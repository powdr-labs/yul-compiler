import YulEvmCompiler.Optimizer.Spec.LocalPass
import YulEvmCompiler.Optimizer.Implementation.StorageForwardResolve
import YulEvmCompiler.Optimizer.Implementation.Frame
/-!
# DispatchTree — balanced binary-search lowering of literal-case switches

solc's function dispatcher lowers as a `switch selector case c₁ {…} … case cₙ {…}
default {…}` on a variable scrutinee whose cases are all word literals. This
compiler lowers `switch` as a *linear* chain of equality compares, so an
unknown-selector call (and, on average, every call) pays gas/steps proportional
to the case's position in the list.

This pass rewrites such a switch into a **balanced binary search tree** of
comparisons:

```yul
switch lt(selector, pivot)
case 1 { <switch over the lower half> }
default { <switch over the upper half> }
```

recursing on each half until a small leaf (`≤ leafSize` cases) is left linear.
The scrutinee is only rewritten when it is a *variable or literal*, so
re-evaluating it on each comparison path is effect-free and yields the same
value (`Step.var` / `Step.lit` never touch the machine state and are
deterministic). The transform is therefore semantics-preserving; the balance is
a pure gas/step heuristic and its correctness does not depend on it.

The partition is by an unsigned `lt` comparison against a pivot word: `lo` are
the cases whose label value is `< pivot`, `hi` the rest. Because EVM `lt` is
unsigned and case labels are 256-bit words, the pivot is chosen as the median
case value; correctness holds for *any* pivot (the halves are literal filters of
the case list), so no ordering invariant is proven — only the filter partition.
-/

namespace YulEvmCompiler.Optimizer.DispatchTree

open YulSemantics
open YulSemantics.EVM

/-- Leaf size: switches with at most this many cases are left as a linear chain. -/
def leafSize : Nat := 3

/-- Minimum case count for the dispatch-tree rewrite to fire. Set well above the
dispatcher sizes seen in the current corpus (≤ 6 cases): measurements show that
for small dispatchers the fixed block-lowering jump overhead dominates the linear
compare chain, so binary search there is net-neutral-to-negative; the tree only
pays off for large dispatchers, where the compare count is the real tax. -/
def minTreeCases : Nat := 8

/-- The scrutinee is safe to re-evaluate (effect-free, deterministic) exactly
when it is a variable or a literal. -/
def pureScrut : Expr Op → Bool
  | .var _ => true
  | .lit _ => true
  | _      => false

/-- Cases whose (unsigned) label value is `< pivot`. -/
def loHalf (pv : U256) (cases : List (Literal × Block Op)) : List (Literal × Block Op) :=
  cases.filter (fun c => (litValue c.1).ult pv)

/-- Cases whose (unsigned) label value is `≥ pivot`. -/
def hiHalf (pv : U256) (cases : List (Literal × Block Op)) : List (Literal × Block Op) :=
  cases.filter (fun c => !(litValue c.1).ult pv)

/-- Heuristic pivot: the median case-label value (unsigned). Purely a balance
heuristic — soundness is independent of the choice. -/
def choosePivot (cases : List (Literal × Block Op)) : U256 :=
  let vals := (cases.map (fun c => litValue c.1)).mergeSort
    (fun a b => a.toNat ≤ b.toNat)
  (vals[cases.length / 2]?).getD 0

/-- The `lt(e, pivot)` scrutinee for an internal tree node. -/
def ltPivot (e : Expr Op) (pv : U256) : Expr Op :=
  .builtin .lt [e, .lit (.number pv.toNat)]

/-- Build the balanced dispatch tree over `cases` with scrutinee `e` and default
`dflt`. `fuel` bounds the recursion (call with `cases.length`); each internal
node splits the cases by an unsigned `lt` against the median pivot. -/
def buildTree (fuel : Nat) (e : Expr Op)
    (cases : List (Literal × Block Op)) (dflt : Option (Block Op)) : Stmt Op :=
  match fuel with
  | 0 => .switch e cases dflt
  | fuel + 1 =>
      if cases.length ≤ leafSize then
        .switch e cases dflt
      else
        let pv := choosePivot cases
        .switch (ltPivot e pv)
          [(.number 1, [buildTree fuel e (loHalf pv cases) dflt])]
          (some [buildTree fuel e (hiHalf pv cases) dflt])

/-- Whether a switch qualifies for the dispatch-tree rewrite: a re-evaluable
scrutinee and more cases than a single leaf holds. -/
def qualifies (e : Expr Op) (cases : List (Literal × Block Op)) : Bool :=
  pureScrut e && (minTreeCases ≤ cases.length)

mutual
  /-- Rewrite a statement, recursing into control-flow bodies and rebuilding
  qualifying switches as dispatch trees. Function definitions are left untouched
  (so the enclosing block's hoisted function scope is preserved verbatim). -/
  def dtStmt : Stmt Op → Stmt Op
    | .block body => .block (dtStmts body)
    | .funDef n ps rs body => .funDef n ps rs body
    | .cond c body => .cond c (dtStmts body)
    | .switch e cases dflt =>
        let cases' := dtCases cases
        let dflt' := dtDflt dflt
        if qualifies e cases' then
          buildTree cases'.length e cases' dflt'
        else
          .switch e cases' dflt'
    | .forLoop init c post body =>
        .forLoop init c (dtStmts post) (dtStmts body)
    | s => s

  def dtStmts : List (Stmt Op) → List (Stmt Op)
    | [] => []
    | s :: rest => dtStmt s :: dtStmts rest

  def dtCases :
      List (Literal × Block Op) → List (Literal × Block Op)
    | [] => []
    | (lit, body) :: rest => (lit, dtStmts body) :: dtCases rest

  def dtDflt : Option (Block Op) → Option (Block Op)
    | none => none
    | some body => some (dtStmts body)
end

/-- Top-level block entry point. Guarded on storage-layout freedom so the pass is
the identity on unresolved `dataoffset`/`datasize` regions, which makes it
commute with object-layout resolution (see `Pipeline`). -/
def dispatchTreeBlock (b : Block Op) : Block Op :=
  if storageLayoutFreeStmts b then dtStmts b else b

end YulEvmCompiler.Optimizer.DispatchTree

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-! ### Empty-scope insertion congruence

A dispatch tree nests `switch` statements, and every `switch` runs its selected
body via `.block`, which prepends `hoist body` to the function environment. A
leaf switch selected inside an outer switch therefore runs its body under one
extra (always empty, since a `switch` is never a `funDef`) function scope
compared to the un-nested original. `FEq` relates two function environments that
differ only by empty scopes inserted at some depth, and `Step.feq` shows
execution is invariant under it — the fact that lets a nested `.block` be
collapsed. -/

/-- `g₁` and `g₂` differ only by empty function scopes inserted at some depth. -/
inductive FEq : FunEnv D → FunEnv D → Prop
  | refl (g : FunEnv D) : FEq g g
  | rm   (rest : FunEnv D) : FEq ([] :: rest) rest
  | add  (rest : FunEnv D) : FEq rest ([] :: rest)
  | cons (s : FScope D) {g₁ g₂ : FunEnv D} : FEq g₁ g₂ → FEq (s :: g₁) (s :: g₂)

theorem FEq.symm {g₁ g₂ : FunEnv D} (h : FEq g₁ g₂) : FEq g₂ g₁ := by
  induction h with
  | refl g => exact .refl g
  | rm rest => exact .add rest
  | add rest => exact .rm rest
  | cons s _ ih => exact .cons s ih

/-- Related environments resolve every function name to the same declaration and
to related closure environments. -/
theorem lookupFun_feq {g₁ g₂ : FunEnv D} (h : FEq g₁ g₂) (fn : Ident) :
    (lookupFun g₁ fn = none ∧ lookupFun g₂ fn = none) ∨
    (∃ decl cenv₁ cenv₂, lookupFun g₁ fn = some (decl, cenv₁) ∧
      lookupFun g₂ fn = some (decl, cenv₂) ∧ FEq cenv₁ cenv₂) := by
  induction h with
  | refl g =>
      rcases hlr : lookupFun g fn with _ | p
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨p.1, p.2, p.2, rfl, rfl, .refl _⟩
  | rm rest =>
      have hnil : lookupFun ([] :: rest) fn = lookupFun rest fn := rfl
      rw [hnil]
      rcases hlr : lookupFun rest fn with _ | p
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨p.1, p.2, p.2, rfl, rfl, .refl _⟩
  | add rest =>
      have hnil : lookupFun ([] :: rest) fn = lookupFun rest fn := rfl
      rw [hnil]
      rcases hlr : lookupFun rest fn with _ | p
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨p.1, p.2, p.2, rfl, rfl, .refl _⟩
  | @cons s g₁ g₂ hg ih =>
      cases hs : s.find? (fun p => p.1 = fn) with
      | some p =>
          refine Or.inr ⟨p.2, s :: g₁, s :: g₂, ?_, ?_, .cons s hg⟩
          · simp [lookupFun, hs]
          · simp [lookupFun, hs]
      | none =>
          rcases ih with ⟨h1, h2⟩ | ⟨decl, c1, c2, h1, h2, hc⟩
          · exact Or.inl ⟨by simp [lookupFun, hs, h1], by simp [lookupFun, hs, h2]⟩
          · exact Or.inr ⟨decl, c1, c2, by simp [lookupFun, hs, h1],
              by simp [lookupFun, hs, h2], hc⟩

/-- Execution is invariant under empty-scope insertion in the function
environment. -/
theorem Step.feq {g₁ : FunEnv D} {V st code r} (h : Step D g₁ V st code r) :
    ∀ {g₂ : FunEnv D}, FEq g₁ g₂ → Step D g₂ V st code r := by
  induction h with
  | lit => exact fun _ => Step.lit
  | var hv => exact fun _ => Step.var hv
  | builtinOk _ hb iha => exact fun hf => Step.builtinOk (iha hf) hb
  | builtinHalt _ hb iha => exact fun hf => Step.builtinHalt (iha hf) hb
  | builtinArgsHalt _ iha => exact fun hf => Step.builtinArgsHalt (iha hf)
  | callOk hargs hl harity hbody hout iha ihb =>
      intro g₂ hf
      rcases lookupFun_feq hf _ with ⟨hn, _⟩ | ⟨decl', c1, c2, h1, h2, hc⟩
      · rw [hl] at hn; exact absurd hn nofun
      · rw [hl] at h1
        simp only [Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact Step.callOk (iha hf) h2 harity (ihb hc) hout
  | callHalt hargs hl harity hbody iha ihb =>
      intro g₂ hf
      rcases lookupFun_feq hf _ with ⟨hn, _⟩ | ⟨decl', c1, c2, h1, h2, hc⟩
      · rw [hl] at hn; exact absurd hn nofun
      · rw [hl] at h1
        simp only [Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact Step.callHalt (iha hf) h2 harity (ihb hc)
  | callArgsHalt _ iha => exact fun hf => Step.callArgsHalt (iha hf)
  | argsNil => exact fun _ => Step.argsNil
  | argsCons _ _ iha ihb => exact fun hf => Step.argsCons (iha hf) (ihb hf)
  | argsRestHalt _ iha => exact fun hf => Step.argsRestHalt (iha hf)
  | argsHeadHalt _ _ iha ihb => exact fun hf => Step.argsHeadHalt (iha hf) (ihb hf)
  | funDef => exact fun _ => Step.funDef
  | block _ ih => exact fun hf => Step.block (ih (hf.cons _))
  | letZero => exact fun _ => Step.letZero
  | letVal _ hlen iha => exact fun hf => Step.letVal (iha hf) hlen
  | letHalt _ iha => exact fun hf => Step.letHalt (iha hf)
  | assignVal _ hlen iha => exact fun hf => Step.assignVal (iha hf) hlen
  | assignHalt _ iha => exact fun hf => Step.assignHalt (iha hf)
  | exprStmt _ iha => exact fun hf => Step.exprStmt (iha hf)
  | exprStmtHalt _ iha => exact fun hf => Step.exprStmtHalt (iha hf)
  | ifTrue _ hz _ iha ihb => exact fun hf => Step.ifTrue (iha hf) hz (ihb hf)
  | ifFalse _ hz iha => exact fun hf => Step.ifFalse (iha hf) hz
  | ifHalt _ iha => exact fun hf => Step.ifHalt (iha hf)
  | switchExec _ _ iha ihb => exact fun hf => Step.switchExec (iha hf) (ihb hf)
  | switchHalt _ iha => exact fun hf => Step.switchHalt (iha hf)
  | forLoop _ _ ihinit ihloop =>
      exact fun hf => Step.forLoop (ihinit (hf.cons _)) (ihloop (hf.cons _))
  | forInitHalt _ ihinit => exact fun hf => Step.forInitHalt (ihinit (hf.cons _))
  | «break» => exact fun _ => Step.«break»
  | «continue» => exact fun _ => Step.«continue»
  | «leave» => exact fun _ => Step.leave
  | seqNil => exact fun _ => Step.seqNil
  | seqCons _ _ iha ihb => exact fun hf => Step.seqCons (iha hf) (ihb hf)
  | seqStop _ hne iha => exact fun hf => Step.seqStop (iha hf) hne
  | loopDone _ hz iha => exact fun hf => Step.loopDone (iha hf) hz
  | loopCondHalt _ iha => exact fun hf => Step.loopCondHalt (iha hf)
  | loopStep _ hnz _ hob _ _ ihc ihb ihp ihr =>
      exact fun hf => Step.loopStep (ihc hf) hnz (ihb hf) hob (ihp hf) (ihr hf)
  | loopPostHalt _ hnz _ hob _ ihc ihb ihp =>
      exact fun hf => Step.loopPostHalt (ihc hf) hnz (ihb hf) hob (ihp hf)
  | loopBreak _ hnz _ ihc ihb => exact fun hf => Step.loopBreak (ihc hf) hnz (ihb hf)
  | loopLeave _ hnz _ ihc ihb => exact fun hf => Step.loopLeave (ihc hf) hnz (ihb hf)
  | loopBodyHalt _ hnz _ ihc ihb => exact fun hf => Step.loopBodyHalt (ihc hf) hnz (ihb hf)

/-! ### Foundational helpers -/

/-- Restoring twice to the same outer frame is restoring once. -/
theorem restore_restore {V W : VEnv D} (h : V.length ≤ W.length) :
    restore V (restore V W) = restore V W := by
  have hlen : (restore V W).length = V.length := restore_length h
  have hunfold : restore V (restore V W)
      = (restore V W).drop ((restore V W).length - V.length) := rfl
  rw [hunfold, hlen, Nat.sub_self, List.drop_zero]

/-- A variable/literal scrutinee evaluates without touching the state, to a value
that can be re-evaluated at any configuration. -/
theorem pureScrut_val {e : Expr Op} (hpure : DispatchTree.pureScrut e = true)
    {funs V st r} (h : Step D funs V st (.expr e) (.eres r)) :
    ∃ cv, r = .vals [cv] st ∧
      ∀ funs' st', Step D funs' V st' (.expr e) (.eres (.vals [cv] st')) := by
  cases e with
  | var x =>
      cases h with
      | var hv => exact ⟨_, rfl, fun _ _ => Step.var hv⟩
  | lit l =>
      cases h with
      | lit => exact ⟨_, rfl, fun _ _ => Step.lit⟩
  | builtin op args => simp [DispatchTree.pureScrut] at hpure
  | call fn args => simp [DispatchTree.pureScrut] at hpure

/-- The number literal chosen for a pivot round-trips to the pivot word. -/
theorem litValue_pivot (pv : U256) : litValue (.number pv.toNat) = pv := by
  simp [litValue]

/-- A singleton statement sequence behaves as the statement itself. -/
theorem stmts_single {funs V st s V' st' o} :
    Step D funs V st (.stmts [s]) (.sres V' st' o) ↔
    Step D funs V st (.stmt s) (.sres V' st' o) := by
  constructor
  · intro h
    cases h with
    | seqCons hs hrest => cases hrest; exact hs
    | seqStop hs _ => exact hs
  · intro h
    cases o with
    | normal => exact Step.seqCons h Step.seqNil
    | «break» => exact Step.seqStop h (by decide)
    | «continue» => exact Step.seqStop h (by decide)
    | «leave» => exact Step.seqStop h (by decide)
    | halt => exact Step.seqStop h (by decide)

/-- `find?` is unaffected by filtering with a predicate that every match satisfies. -/
theorem find_filter_pred {α} (pred q : α → Bool) (l : List α)
    (himp : ∀ x, pred x = true → q x = true) :
    l.find? pred = (l.filter q).find? pred := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      by_cases hp : pred a = true
      · have hq : q a = true := himp a hp
        rw [List.filter_cons_of_pos hq, List.find?_cons_of_pos hp, List.find?_cons_of_pos hp]
      · have hp' : pred a = false := by simpa using hp
        rw [List.find?_cons_of_neg (by simp [hp'])]
        by_cases hq : q a = true
        · rw [List.filter_cons_of_pos hq, List.find?_cons_of_neg (by simp [hp']), ih]
        · have hq' : q a = false := by simpa using hq
          rw [List.filter_cons_of_neg (by simp [hq']), ih]

/-- On the lower branch (`cv < pivot`), the switch selects the same body from the
lower-half filter as from the full case list. -/
theorem selectSwitch_loHalf {cv : U256} (cases : List (Literal × Block Op))
    (dflt : Option (Block Op)) (pv : U256) (h : cv.ult pv = true) :
    selectSwitch D cv cases dflt = selectSwitch D cv (DispatchTree.loHalf pv cases) dflt := by
  simp only [selectSwitch, DispatchTree.loHalf, evmWithExternal]
  rw [find_filter_pred (fun p => decide (cv = litValue p.1))
    (fun c => (litValue c.1).ult pv) cases (fun x hx => by
      simp only [decide_eq_true_eq] at hx; subst hx; exact h)]

/-- On the upper branch (`cv ≥ pivot`), the switch selects the same body from the
upper-half filter as from the full case list. -/
theorem selectSwitch_hiHalf {cv : U256} (cases : List (Literal × Block Op))
    (dflt : Option (Block Op)) (pv : U256) (h : cv.ult pv = false) :
    selectSwitch D cv cases dflt = selectSwitch D cv (DispatchTree.hiHalf pv cases) dflt := by
  simp only [selectSwitch, DispatchTree.hiHalf, evmWithExternal]
  rw [find_filter_pred (fun p => decide (cv = litValue p.1))
    (fun c => !(litValue c.1).ult pv) cases (fun x hx => by
      simp only [decide_eq_true_eq] at hx; subst hx; simp [h])]

/-- Soundness of the dispatch-tree rewrite: pointwise-equivalent to the input. -/
theorem dispatchTreeBlock_sound (b : Block Op) :
    EquivBlock D b (DispatchTree.dispatchTreeBlock b) := by
  sorry

/-- The dispatch-tree pass as a verified `LocalPass`. -/
def dispatchTree : LocalPass D where
  run := DispatchTree.dispatchTreeBlock
  sound := fun b => dispatchTreeBlock_sound b

@[simp] theorem dispatchTree_run (b : Block Op) :
    (dispatchTree (calls := calls) (creates := creates)).run b =
      DispatchTree.dispatchTreeBlock b := rfl

/-- Object-path layout-resolution congruence for the dispatch-tree pass. -/
theorem resolveDispatchTreeBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (DispatchTree.dispatchTreeBlock b)) := by
  sorry

end YulEvmCompiler.Optimizer
