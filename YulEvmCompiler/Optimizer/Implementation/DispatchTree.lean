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

/-- A variable/literal scrutinee evaluates without touching the state, and its
value can be re-evaluated at any configuration. -/
theorem pureScrut_val {e : Expr Op} (hpure : DispatchTree.pureScrut e = true)
    {funs V st v st'} (h : Step D funs V st (.expr e) (.eres (.vals [v] st'))) :
    st' = st ∧ ∀ funs' st'', Step D funs' V st'' (.expr e) (.eres (.vals [v] st'')) := by
  cases e with
  | var x =>
      cases h with
      | var hv => exact ⟨rfl, fun _ _ => Step.var hv⟩
  | lit l =>
      cases h with
      | lit => exact ⟨rfl, fun _ _ => Step.lit⟩
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

/-! ### The `lt(e, pivot)` scrutinee -/

/-- Constructing the pivot comparison: it evaluates to `1`/`0` according to
`cv <ᵤ pivot`, leaving the state untouched. -/
theorem ltPivot_eval {e : Expr Op} {cv : U256} {funs V st} (pv : U256)
    (hcv : ∀ funs' st', Step D funs' V st' (.expr e) (.eres (.vals [cv] st'))) :
    Step D funs V st (.expr (DispatchTree.ltPivot e pv))
      (.eres (.vals [b2w (cv.ult pv)] st)) := by
  unfold DispatchTree.ltPivot
  refine Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (hcv funs st)) ?_
  show stepOp Op.lt [cv, litValue (.number pv.toNat)] st = some (.ok [b2w (cv.ult pv)] st)
  rw [litValue_pivot]; rfl

/-- Inverting the pivot comparison: a `lt(e, pivot)` value comes from `e`
evaluating to some `cv` (re-evaluable, state-preserving) with the value
`b2w (cv <ᵤ pivot)`. -/
theorem ltPivot_eval_inv {e : Expr Op} (hpure : DispatchTree.pureScrut e = true)
    {pv : U256} {funs V st r} (h : Step D funs V st (.expr (DispatchTree.ltPivot e pv)) (.eres r)) :
    ∃ cv, (∀ funs' st', Step D funs' V st' (.expr e) (.eres (.vals [cv] st'))) ∧
      r = .vals [b2w (cv.ult pv)] st := by
  unfold DispatchTree.ltPivot at h
  cases h with
  | @builtinOk _ _ st _ _ argvals st1 rets st2 hargs hb =>
      cases hargs with
      | @argsCons _ _ _ _ _ _ _ v _ hrest hhead =>
          cases hrest with
          | argsCons hnil hpv =>
              cases hnil; cases hpv
              obtain ⟨hst, hre⟩ := pureScrut_val hpure hhead
              subst hst
              refine ⟨v, hre, ?_⟩
              have hbb : stepOp Op.lt [v, litValue (.number pv.toNat)] st1
                  = some (.ok rets st2) := hb
              rw [litValue_pivot] at hbb
              simp only [stepOp, bin, Option.some.injEq, BuiltinResult.ok.injEq] at hbb
              obtain ⟨hr, hs⟩ := hbb
              rw [← hr, ← hs]
  | @builtinHalt _ _ st _ _ argvals st1 st2 hargs hb =>
      cases hargs with
      | argsCons hrest hhead =>
          cases hrest with
          | argsCons hnil hpv =>
              cases hnil; cases hpv
              obtain ⟨hst, _⟩ := pureScrut_val hpure hhead
              subst hst
              have hbb : stepOp Op.lt [_, litValue (.number pv.toNat)] st1
                  = some (.halt st2) := hb
              simp [stepOp, bin] at hbb
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsRestHalt hrest =>
          cases hrest with
          | argsRestHalt hnil => cases hnil
          | argsHeadHalt hnil hpv => cases hnil; cases hpv
      | argsHeadHalt hrest hhead =>
          cases e with
          | var x => cases hhead
          | lit l => cases hhead
          | builtin _ _ => simp [DispatchTree.pureScrut] at hpure
          | call _ _ => simp [DispatchTree.pureScrut] at hpure

/-- A variable/literal scrutinee is deterministic across configurations. -/
theorem pureScrut_det {e : Expr Op} (hpure : DispatchTree.pureScrut e = true)
    {funs V st a sta funs' st' b stb}
    (ha : Step D funs V st (.expr e) (.eres (.vals [a] sta)))
    (hb : Step D funs' V st' (.expr e) (.eres (.vals [b] stb))) : a = b := by
  cases e with
  | var x =>
      cases ha with
      | var hva => cases hb with | var hvb => rw [hva] at hvb; exact Option.some.inj hvb
  | lit l => cases ha with | lit => cases hb with | lit => rfl
  | builtin _ _ => simp [DispatchTree.pureScrut] at hpure
  | call _ _ => simp [DispatchTree.pureScrut] at hpure

/-! ### Collapsing a nested leaf switch

The heart of the tree soundness: an outer switch selects the singleton block
`[switch e cs d]`, running it as `.block [switch e cs d]`; this is equivalent to
running the switch's own selected body `.block (selectSwitch cv cs d)` directly.
The extra `.block` layer prepends an empty function scope (`Step.feq`) and an
extra `restore` (`restore_restore`); both are transparent. -/
theorem block_singleton_switch {e : Expr Op} (hpure : DispatchTree.pureScrut e = true)
    {cv : U256} {cs : List (Literal × Block Op)} {d : Option (Block Op)}
    {funs V st V' st' o}
    (hcv : ∀ funs' st'', Step D funs' V st'' (.expr e) (.eres (.vals [cv] st''))) :
    Step D funs V st (.stmt (.block [.switch e cs d])) (.sres V' st' o) ↔
    Step D funs V st (.stmt (.block (selectSwitch D cv cs d))) (.sres V' st' o) := by
  constructor
  · intro h
    cases h with
    | block hb =>
        have hb2 := (Step.feq hb) (FEq.rm funs)
        rw [stmts_single] at hb2
        cases hb2 with
        | @switchExec _ _ _ _ _ _ cv2 st1 _ _ _ hc hbody =>
            obtain ⟨hst1, _⟩ := pureScrut_val hpure hc
            subst st1
            have hcveq := pureScrut_det hpure hc (hcv funs st)
            subst cv2
            cases hbody with
            | block hbb =>
                have hlen := venvLen_mono hbb rfl
                rw [restore_restore hlen]
                exact Step.block hbb
        | switchHalt hc =>
            cases e with
            | var x => cases hc
            | lit l => cases hc
            | builtin _ _ => simp [DispatchTree.pureScrut] at hpure
            | call _ _ => simp [DispatchTree.pureScrut] at hpure
  · intro h
    cases h with
    | @block _ _ _ _ Vb _ _ hbb =>
        have hlen := venvLen_mono hbb rfl
        have hsw : Step D funs V st (.stmt (.switch e cs d))
            (.sres (restore V Vb) st' o) := Step.switchExec (hcv funs st) (Step.block hbb)
        have hseq : Step D (hoist D [.switch e cs d] :: funs) V st
            (.stmts [.switch e cs d]) (.sres (restore V Vb) st' o) :=
          (Step.feq (stmts_single.mpr hsw)) (FEq.add funs)
        have hfin := Step.block hseq
        rw [restore_restore hlen] at hfin
        exact hfin

/-- The outer node's `case 1` fires exactly when `lt` returned true. -/
theorem selectSwitch_one (B_lo B_hi : Block Op) :
    selectSwitch D (b2w true) [(.number 1, B_lo)] (some B_hi) = B_lo := by
  simp [selectSwitch, b2w, litValue]

/-- Otherwise the node falls to its default (the upper half). -/
theorem selectSwitch_zero (B_lo B_hi : Block Op) :
    selectSwitch D (b2w false) [(.number 1, B_lo)] (some B_hi) = B_hi := by
  simp [selectSwitch, b2w, litValue]

/-! ### One split step -/

/-- The core equivalence: a switch on a pure scrutinee equals the two-way split
`switch lt(e, pivot) case 1 {switch over lower half} default {switch over upper
half}`. Holds for **any** pivot — the halves are literal filters of the case
list. -/
theorem split_equiv (e : Expr Op) (hpure : DispatchTree.pureScrut e = true)
    (cases : List (Literal × Block Op)) (dflt : Option (Block Op)) (pv : U256) :
    EquivStmt D (.switch e cases dflt)
      (.switch (DispatchTree.ltPivot e pv)
        [(.number 1, [.switch e (DispatchTree.loHalf pv cases) dflt])]
        (some [.switch e (DispatchTree.hiHalf pv cases) dflt])) := by
  intro funs V st V'' st'' o
  constructor
  · intro h
    cases h with
    | @switchExec _ _ _ _ _ _ cv st1 _ _ _ hc hbody =>
        obtain ⟨hst1, hre⟩ := pureScrut_val hpure hc
        subst st1
        refine Step.switchExec (ltPivot_eval pv hre) ?_
        by_cases hlt : cv.ult pv = true
        · rw [selectSwitch_loHalf cases dflt pv hlt] at hbody
          rw [hlt, selectSwitch_one]
          exact (block_singleton_switch hpure hre).mpr hbody
        · have hlt' : cv.ult pv = false := by simpa using hlt
          rw [selectSwitch_hiHalf cases dflt pv hlt'] at hbody
          rw [hlt', selectSwitch_zero]
          exact (block_singleton_switch hpure hre).mpr hbody
    | switchHalt hc =>
        cases e with
        | var x => cases hc
        | lit l => cases hc
        | builtin _ _ => simp [DispatchTree.pureScrut] at hpure
        | call _ _ => simp [DispatchTree.pureScrut] at hpure
  · intro h
    cases h with
    | @switchExec _ _ _ _ _ _ ltv st1 _ _ _ hc hbody =>
        obtain ⟨cv, hre, hval⟩ := ltPivot_eval_inv hpure hc
        injection hval with hlv hs
        injection hlv with hlv
        subst st1; subst ltv
        refine Step.switchExec (hre funs st) ?_
        by_cases hlt : cv.ult pv = true
        · rw [hlt, selectSwitch_one] at hbody
          rw [selectSwitch_loHalf cases dflt pv hlt]
          exact (block_singleton_switch hpure hre).mp hbody
        · have hlt' : cv.ult pv = false := by simpa using hlt
          rw [hlt', selectSwitch_zero] at hbody
          rw [selectSwitch_hiHalf cases dflt pv hlt']
          exact (block_singleton_switch hpure hre).mp hbody
    | switchHalt hc =>
        obtain ⟨cv, _, hval⟩ := ltPivot_eval_inv hpure hc
        exact absurd hval (by simp)

/-- The built tree is always a `switch`, so a singleton block containing it
hoists no functions. -/
theorem buildTree_hoist (fuel : Nat) (e : Expr Op)
    (cases : List (Literal × Block Op)) (dflt : Option (Block Op)) :
    hoist D [DispatchTree.buildTree fuel e cases dflt] = [] := by
  cases fuel with
  | zero => rfl
  | succ n => unfold DispatchTree.buildTree; split <;> rfl

/-- The dispatch tree is equivalent to the linear switch it lowers. -/
theorem buildTree_equiv (fuel : Nat) (e : Expr Op)
    (hpure : DispatchTree.pureScrut e = true)
    (cases : List (Literal × Block Op)) (dflt : Option (Block Op)) :
    EquivStmt D (DispatchTree.buildTree fuel e cases dflt) (.switch e cases dflt) := by
  induction fuel generalizing cases with
  | zero => exact EquivStmt.refl _
  | succ n ih =>
      unfold DispatchTree.buildTree
      split
      · exact EquivStmt.refl _
      · refine EquivStmt.trans ?_
          (split_equiv e hpure cases dflt (DispatchTree.choosePivot cases)).symm
        refine EquivStmt.switch_congr (EquivExpr.refl _)
          (List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil) ?_
        · exact EquivBlock.of_forall₂ (List.Forall₂.cons (ih _) List.Forall₂.nil)
            (by rw [buildTree_hoist]; rfl)
        · simp only [Option.getD_some]
          exact EquivBlock.of_forall₂ (List.Forall₂.cons (ih _) List.Forall₂.nil)
            (by rw [buildTree_hoist]; rfl)

/-! ### Structural lifting -/

/-- `hoist` distributes over a cons. -/
theorem hoist_cons (a : Stmt Op) (l : Block Op) :
    hoist D (a :: l) = hoist D [a] ++ hoist D l := by
  cases a <;> simp [hoist]

/-- Rewriting a single statement preserves its hoisted function contribution
(function definitions are left verbatim; every other statement stays a
non-`funDef`). -/
theorem dtStmt_hoistEntry (s : Stmt Op) :
    hoist D [DispatchTree.dtStmt s] = hoist D [s] := by
  cases s with
  | «switch» e cases dflt =>
      show hoist D [DispatchTree.dtStmt (.switch e cases dflt)] = []
      simp only [DispatchTree.dtStmt]
      split
      · exact buildTree_hoist _ _ _ _
      · rfl
  | _ => rfl

/-- The rewrite preserves the block's hoisted function scope. -/
theorem dtStmts_hoist (ss : List (Stmt Op)) :
    hoist D (DispatchTree.dtStmts ss) = hoist D ss := by
  induction ss with
  | nil => rfl
  | cons s rest ih =>
      show hoist D (DispatchTree.dtStmt s :: DispatchTree.dtStmts rest) = hoist D (s :: rest)
      rw [hoist_cons, dtStmt_hoistEntry, ih, ← hoist_cons]

mutual
  /-- Each statement is equivalent to its rewrite. -/
  theorem dtStmt_equiv (s : Stmt Op) : EquivStmt D s (DispatchTree.dtStmt s) := by
    cases s with
    | block body =>
        exact EquivBlock.of_stmts (EquivStmts.of_forall₂ (dtStmts_forall2 body))
          (dtStmts_hoist body).symm
    | funDef n ps rs body => exact EquivStmt.refl _
    | cond c body =>
        exact EquivStmt.cond_congr (EquivExpr.refl _)
          (EquivBlock.of_stmts (EquivStmts.of_forall₂ (dtStmts_forall2 body))
            (dtStmts_hoist body).symm)
    | «switch» e cases dflt =>
        simp only [DispatchTree.dtStmt]
        split
        · rename_i hq
          have hpure : DispatchTree.pureScrut e = true := by
            simp only [DispatchTree.qualifies, Bool.and_eq_true] at hq; exact hq.1
          exact EquivStmt.trans
            (EquivStmt.switch_congr (EquivExpr.refl _) (dtCases_forall2 cases)
              (dtDflt_equiv dflt))
            (buildTree_equiv _ e hpure (DispatchTree.dtCases cases)
              (DispatchTree.dtDflt dflt)).symm
        · exact EquivStmt.switch_congr (EquivExpr.refl _) (dtCases_forall2 cases)
            (dtDflt_equiv dflt)
    | forLoop init c post body =>
        exact EquivStmt.forLoop_congr _ (EquivExpr.refl _)
          (EquivBlock.of_stmts (EquivStmts.of_forall₂ (dtStmts_forall2 post))
            (dtStmts_hoist post).symm)
          (EquivBlock.of_stmts (EquivStmts.of_forall₂ (dtStmts_forall2 body))
            (dtStmts_hoist body).symm)
    | letDecl _ _ => exact EquivStmt.refl _
    | assign _ _ => exact EquivStmt.refl _
    | exprStmt _ => exact EquivStmt.refl _
    | «break» => exact EquivStmt.refl _
    | «continue» => exact EquivStmt.refl _
    | «leave» => exact EquivStmt.refl _

  /-- Statement sequences are element-wise equivalent to their rewrite. -/
  theorem dtStmts_forall2 (ss : List (Stmt Op)) :
      List.Forall₂ (EquivStmt D) ss (DispatchTree.dtStmts ss) := by
    cases ss with
    | nil => exact List.Forall₂.nil
    | cons s rest => exact List.Forall₂.cons (dtStmt_equiv s) (dtStmts_forall2 rest)

  /-- Switch cases are pairwise equivalent (equal labels, equivalent bodies). -/
  theorem dtCases_forall2 (cs : List (Literal × Block Op)) :
      List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2) cs
        (DispatchTree.dtCases cs) := by
    cases cs with
    | nil => exact List.Forall₂.nil
    | cons p rest =>
        obtain ⟨lit, body⟩ := p
        exact List.Forall₂.cons ⟨rfl, EquivBlock.of_stmts
          (EquivStmts.of_forall₂ (dtStmts_forall2 body)) (dtStmts_hoist body).symm⟩
          (dtCases_forall2 rest)

  /-- The default body is equivalent to its rewrite. -/
  theorem dtDflt_equiv (d : Option (Block Op)) :
      EquivBlock D (d.getD []) ((DispatchTree.dtDflt d).getD []) := by
    cases d with
    | none => exact EquivBlock.refl _
    | some body =>
        exact EquivBlock.of_stmts (EquivStmts.of_forall₂ (dtStmts_forall2 body))
          (dtStmts_hoist body).symm
end

/-- Soundness of the dispatch-tree rewrite: pointwise-equivalent to the input. -/
theorem dispatchTreeBlock_sound (b : Block Op) :
    EquivBlock D b (DispatchTree.dispatchTreeBlock b) := by
  unfold DispatchTree.dispatchTreeBlock
  split
  · exact EquivBlock.of_stmts (EquivStmts.of_forall₂ (dtStmts_forall2 b))
      (dtStmts_hoist b).symm
  · exact @EquivBlock.refl (evmWithExternal calls creates) _ b

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
