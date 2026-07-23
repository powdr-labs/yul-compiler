import YulSemantics.Equiv
import YulEvmCompiler.Optimizer.Spec.Pass
import YulEvmCompiler.Optimizer.Implementation.EmptyScope
import YulEvmCompiler.Optimizer.Implementation.Frame

set_option warningAsError true

/-!
# YulEvmCompiler.Optimizer.Implementation.HoistForInit

A single verified pass: **pull the `init` block out of a `for` loop**.

```
for { init } c { post } { body }   ⟿   { init  for {} c { post } { body } }
```

The transform fires only when `init` is a straight-line list of
`let`/`assign`/`exprStmt` statements (`SimpleInit`) — the shape solc emits
(`let i := 0`). That guarantees `init` can only finish `normal` or `halt`, never
`break`/`continue`/`leave` (which the `for` rule does not admit from `init`, so
lifting `init` into the enclosing block would otherwise change behaviour on a
`leave`-in-`init` program). `init` itself is left untouched; `post`/`body`
(and nested `block`/`cond`/`switch`) are recursed into. Function *bodies* are
left unchanged, so the enclosing block's hoisted function scope is preserved and
plain `EquivBlock.of_stmts` suffices (no `FunCongr`).

Soundness is the strong `EquivBlock` `Pass` tier. The one subtlety is that the
residual `for {}` still hoists an (empty) function scope, so the loop runs under
one extra `[]` scope; `EmptyScope.Step.emptyExt_congr(')` bridges it.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-! ### Generic sequence-append lemmas (local copies) -/

theorem hfi_append_normal {funs : FunEnv D} {pre suf : List (Stmt D.Op)} {V st V1 st1 Vb st' o}
    (hpre : Step D funs V st (.stmts pre) (.sres V1 st1 .normal))
    (hsuf : Step D funs V1 st1 (.stmts suf) (.sres Vb st' o)) :
    Step D funs V st (.stmts (pre ++ suf)) (.sres Vb st' o) := by
  induction pre generalizing V st with
  | nil => cases hpre with | seqNil => exact hsuf
  | cons s pre' ih =>
      cases hpre with
      | seqCons hs hpre' => exact Step.seqCons hs (ih hpre')
      | seqStop _ hne => exact absurd rfl hne

theorem hfi_append_early {funs : FunEnv D} {pre suf : List (Stmt D.Op)} {V st Vb st' o}
    (hpre : Step D funs V st (.stmts pre) (.sres Vb st' o)) (hne : o ≠ .normal) :
    Step D funs V st (.stmts (pre ++ suf)) (.sres Vb st' o) := by
  induction pre generalizing V st with
  | nil => cases hpre with | seqNil => exact absurd rfl hne
  | cons s pre' ih =>
      cases hpre with
      | seqCons hs hpre' => exact Step.seqCons hs (ih hpre')
      | seqStop hs hne' => exact Step.seqStop hs hne'

theorem hfi_append_fwd {funs : FunEnv D} {pre suf : List (Stmt D.Op)} {V st Vb st' o}
    (h : Step D funs V st (.stmts (pre ++ suf)) (.sres Vb st' o)) :
    (∃ V1 st1, Step D funs V st (.stmts pre) (.sres V1 st1 .normal) ∧
       Step D funs V1 st1 (.stmts suf) (.sres Vb st' o)) ∨
    (o ≠ .normal ∧ Step D funs V st (.stmts pre) (.sres Vb st' o)) := by
  induction pre generalizing V st with
  | nil => exact Or.inl ⟨V, st, Step.seqNil, h⟩
  | cons s pre' ih =>
      rw [List.cons_append] at h
      cases h with
      | seqCons hs htail =>
          rcases ih htail with ⟨V1, st1, hpre', hsuf⟩ | ⟨hne, hpre'⟩
          · exact Or.inl ⟨V1, st1, Step.seqCons hs hpre', hsuf⟩
          · exact Or.inr ⟨hne, Step.seqCons hs hpre'⟩
      | seqStop hs hne => exact Or.inr ⟨hne, Step.seqStop hs hne⟩

theorem hfi_singleton {funs : FunEnv D} {s} {V st V' st' o}
    (h : Step D funs V st (.stmt s) (.sres V' st' o)) :
    Step D funs V st (.stmts [s]) (.sres V' st' o) := by
  by_cases ho : o = .normal
  · subst ho; exact Step.seqCons h Step.seqNil
  · exact Step.seqStop h ho

theorem hfi_singleton_inv {funs : FunEnv D} {s} {V st V' st' o}
    (h : Step D funs V st (.stmts [s]) (.sres V' st' o)) :
    Step D funs V st (.stmt s) (.sres V' st' o) := by
  cases h with
  | seqCons hs htail => cases htail with | seqNil => exact hs
  | seqStop hs _ => exact hs

/-! ### `restore` composition and hoist over the appended `for {}` -/

theorem hfi_restore_restore {V Vinit Vend : VEnv D}
    (h1 : V.length ≤ Vinit.length) (h2 : Vinit.length ≤ Vend.length) :
    restore V (restore Vinit Vend) = restore V Vend := by
  have hlen : (restore Vinit Vend).length = Vinit.length := restore_length h2
  have e1 : restore V (restore Vinit Vend)
      = (restore Vinit Vend).drop ((restore Vinit Vend).length - V.length) := rfl
  have e2 : restore Vinit Vend = Vend.drop (Vend.length - Vinit.length) := rfl
  have e3 : restore V Vend = Vend.drop (Vend.length - V.length) := rfl
  rw [e1, hlen, e2, List.drop_drop, e3]
  congr 1
  omega

omit [DecidableEq D.Value] in
theorem hfi_hoist_append (init : List (Stmt D.Op)) (c : Expr D.Op) (post body : Block D.Op) :
    hoist D (init ++ [.forLoop [] c post body]) = hoist D init := by
  simp only [hoist, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
    List.append_nil]

/-! ### The `SimpleInit` guard and its outcome consequence -/

/-- A statement whose only possible outcomes are `normal`/`halt`. -/
def simpleInitStmt : Stmt D.Op → Bool
  | .letDecl _ _ => true
  | .assign _ _ => true
  | .exprStmt _ => true
  | _ => false

/-- `init` is a straight-line list of declarations/assignments/expression
statements — the shape solc emits for a `for` initializer. -/
def SimpleInit (init : List (Stmt D.Op)) : Bool := init.all simpleInitStmt

theorem simpleStmt_outcome {s : Stmt D.Op} (hs : simpleInitStmt (D := D) s = true)
    {funs : FunEnv D} {V st V' st' o} (h : Step D funs V st (.stmt s) (.sres V' st' o)) :
    o = .normal ∨ o = .halt := by
  cases s with
  | letDecl vars val =>
      cases h with
      | letZero => exact Or.inl rfl
      | letVal _ _ => exact Or.inl rfl
      | letHalt _ => exact Or.inr rfl
  | assign vars e =>
      cases h with
      | assignVal _ _ => exact Or.inl rfl
      | assignHalt _ => exact Or.inr rfl
  | exprStmt e =>
      cases h with
      | exprStmt _ => exact Or.inl rfl
      | exprStmtHalt _ => exact Or.inr rfl
  | block b => simp [simpleInitStmt] at hs
  | funDef n ps rs b => simp [simpleInitStmt] at hs
  | cond cc b => simp [simpleInitStmt] at hs
  | switch cc cs d => simp [simpleInitStmt] at hs
  | forLoop i cc p b => simp [simpleInitStmt] at hs
  | «break» => simp [simpleInitStmt] at hs
  | «continue» => simp [simpleInitStmt] at hs
  | leave => simp [simpleInitStmt] at hs

theorem simpleInit_outcome {init : List (Stmt D.Op)} (hsimple : SimpleInit (D := D) init = true)
    {funs : FunEnv D} {V st V' st' o} (h : Step D funs V st (.stmts init) (.sres V' st' o)) :
    o = .normal ∨ o = .halt := by
  induction init generalizing V st with
  | nil => cases h with | seqNil => exact Or.inl rfl
  | cons s rest ih =>
      simp only [SimpleInit, List.all_cons, Bool.and_eq_true] at hsimple
      obtain ⟨hhead, htail⟩ := hsimple
      cases h with
      | seqCons _ hrest => exact ih (by simp [SimpleInit, htail]) hrest
      | seqStop hs hne => exact simpleStmt_outcome hhead hs

/-! ### The core statement equivalence -/

/-- Pulling a `SimpleInit` `init` out of a `for` loop into an enclosing block is
semantics-preserving. `post`/`body` are arbitrary (already-transformed) blocks. -/
theorem hoistForInit_core {init : List (Stmt D.Op)} (c : Expr D.Op) (post body : Block D.Op)
    (hsimple : SimpleInit (D := D) init = true) :
    EquivStmt D (.forLoop init c post body) (.block (init ++ [.forLoop [] c post body])) := by
  intro funs V st Vres st' o
  constructor
  · -- forward: for-loop ⟹ block
    intro h
    cases h with
    | @forLoop _ _ _ _ _ _ _ Vinit _ Vend _ _ hinit hloop =>
        have hkey : restore V (restore Vinit Vend) = restore V Vend :=
          hfi_restore_restore (venvLen_mono hinit rfl) (venvLen_mono hloop rfl)
        have hinner : Step D (hoist D init :: funs) V st
            (.stmts (init ++ [Stmt.forLoop [] c post body]))
            (.sres (restore Vinit Vend) st' o) := by
          refine hfi_append_normal hinit (hfi_singleton ?_)
          exact Step.forLoop Step.seqNil
            (Step.emptyExt_congr hloop (EmptyExt.head (hoist D init :: funs)))
        have hblk := Step.block (by rw [hfi_hoist_append]; exact hinner)
        rw [hkey] at hblk
        exact hblk
    | @forInitHalt _ _ _ _ _ _ _ Vinit _ hinit =>
        have hinner : Step D (hoist D init :: funs) V st
            (.stmts (init ++ [Stmt.forLoop [] c post body]))
            (.sres Vinit st' .halt) :=
          hfi_append_early hinit (by decide)
        exact Step.block (by rw [hfi_hoist_append]; exact hinner)
  · -- backward: block ⟹ for-loop
    intro h
    cases h with
    | @block _ _ _ _ Vb _ _ hb =>
        rw [hfi_hoist_append] at hb
        rcases hfi_append_fwd hb with ⟨V1, st1, hinit, hsuf⟩ | ⟨hne, hinit⟩
        · have hfl0 := hfi_singleton_inv hsuf
          cases hfl0 with
          | @forLoop _ _ _ _ _ _ _ _ _ Vend' _ _ hinit0 hloop0 =>
              cases hinit0 with
              | seqNil =>
                  have hloopH := Step.emptyExt_congr' hloop0 (EmptyExt.head (hoist D init :: funs))
                  have hkey : restore V (restore V1 Vend') = restore V Vend' :=
                    hfi_restore_restore (venvLen_mono hinit rfl) (venvLen_mono hloopH rfl)
                  rw [hkey]
                  exact Step.forLoop hinit hloopH
          | @forInitHalt _ _ _ _ _ _ _ _ _ hinit0 => cases hinit0
        · have ho : o = .halt := by
            rcases simpleInit_outcome hsimple hinit with h1 | h1
            · exact absurd h1 hne
            · exact h1
          subst ho
          exact Step.forInitHalt hinit

/-! ### The transform -/

mutual

/-- Pull the `init` out of every `SimpleInit` `for` loop, recursing into
`post`/`body`, `block`/`cond`/`switch`. `funDef` bodies and `init` are left
unchanged. -/
def hoistInitStmt : Stmt D.Op → Stmt D.Op
  | .forLoop init c post body =>
      if SimpleInit init
      then .block (init ++ [.forLoop [] c (hoistInitStmts post) (hoistInitStmts body)])
      else .forLoop init c (hoistInitStmts post) (hoistInitStmts body)
  | .block b => .block (hoistInitStmts b)
  | .cond c b => .cond c (hoistInitStmts b)
  | .switch c cases dflt => .switch c (hoistInitCases cases) (hoistInitDflt dflt)
  | .funDef n ps rs b => .funDef n ps rs b
  | .letDecl vars val => .letDecl vars val
  | .assign vars e => .assign vars e
  | .exprStmt e => .exprStmt e
  | .break => .break
  | .continue => .continue
  | .leave => .leave

def hoistInitStmts : List (Stmt D.Op) → List (Stmt D.Op)
  | [] => []
  | s :: rest => hoistInitStmt s :: hoistInitStmts rest

def hoistInitCases : List (Literal × Block D.Op) → List (Literal × Block D.Op)
  | [] => []
  | (l, b) :: rest => (l, hoistInitStmts b) :: hoistInitCases rest

def hoistInitDflt : Option (Block D.Op) → Option (Block D.Op)
  | none => none
  | some b => some (hoistInitStmts b)

end

/-! ### The transform preserves the hoisted function scope -/

omit [DecidableEq D.Value] in
theorem hoist_cons (x : Stmt D.Op) (l : List (Stmt D.Op)) :
    hoist D (x :: l) = hoist D [x] ++ hoist D l := by
  cases x <;> rfl

omit [DecidableEq D.Value] in
theorem hoistInitStmt_hoistEq (s : Stmt D.Op) :
    hoist D [hoistInitStmt s] = hoist D [s] := by
  cases s with
  | forLoop i cc p bd => simp only [hoistInitStmt]; split <;> rfl
  | funDef n ps rs bd => simp only [hoistInitStmt]
  | block bd => simp only [hoistInitStmt]; rfl
  | cond cc bd => simp only [hoistInitStmt]; rfl
  | switch cc cs d => simp only [hoistInitStmt]; rfl
  | letDecl vars val => simp only [hoistInitStmt]
  | assign vars e => simp only [hoistInitStmt]
  | exprStmt e => simp only [hoistInitStmt]
  | «break» => simp only [hoistInitStmt]
  | «continue» => simp only [hoistInitStmt]
  | leave => simp only [hoistInitStmt]

omit [DecidableEq D.Value] in
theorem hoist_hoistInitStmts (b : List (Stmt D.Op)) :
    hoist D (hoistInitStmts b) = hoist D b := by
  induction b with
  | nil => rfl
  | cons s rest ih =>
      show hoist D (hoistInitStmt s :: hoistInitStmts rest) = hoist D (s :: rest)
      rw [hoist_cons, hoist_cons (D := D) s rest, hoistInitStmt_hoistEq, ih]

/-! ### Soundness -/

mutual

theorem hoistInitStmt_equiv : ∀ s : Stmt D.Op, EquivStmt D s (hoistInitStmt s)
  | .forLoop init c post body => by
      have hpost : EquivBlock D post (hoistInitStmts post) :=
        EquivBlock.of_stmts (EquivStmts.of_forall₂ (hoistInitStmts_forall2 post))
          (hoist_hoistInitStmts post).symm
      have hbody : EquivBlock D body (hoistInitStmts body) :=
        EquivBlock.of_stmts (EquivStmts.of_forall₂ (hoistInitStmts_forall2 body))
          (hoist_hoistInitStmts body).symm
      simp only [hoistInitStmt]
      split
      · rename_i hsimple
        exact (EquivStmt.forLoop_congr init (EquivExpr.refl c) hpost hbody).trans
          (hoistForInit_core c (hoistInitStmts post) (hoistInitStmts body) hsimple)
      · exact EquivStmt.forLoop_congr init (EquivExpr.refl c) hpost hbody
  | .block b =>
      EquivBlock.of_stmts (EquivStmts.of_forall₂ (hoistInitStmts_forall2 b))
        (hoist_hoistInitStmts b).symm
  | .cond c b =>
      EquivStmt.cond_congr (EquivExpr.refl c)
        (EquivBlock.of_stmts (EquivStmts.of_forall₂ (hoistInitStmts_forall2 b))
          (hoist_hoistInitStmts b).symm)
  | .switch c cases dflt => by
      have hsw : EquivStmt D (.switch c cases dflt)
          (.switch c (hoistInitCases cases) (hoistInitDflt dflt)) := by
        apply EquivStmt.switch_congr (EquivExpr.refl c) (hoistInitCases_forall2 cases)
        cases dflt with
        | none => exact EquivBlock.refl _
        | some b =>
            exact EquivBlock.of_stmts (EquivStmts.of_forall₂ (hoistInitStmts_forall2 b))
              (hoist_hoistInitStmts b).symm
      simpa only [hoistInitStmt] using hsw
  | .funDef n ps rs b => by simp only [hoistInitStmt]; exact EquivStmt.refl _
  | .letDecl vars val => by simp only [hoistInitStmt]; exact EquivStmt.refl _
  | .assign vars e => by simp only [hoistInitStmt]; exact EquivStmt.refl _
  | .exprStmt e => by simp only [hoistInitStmt]; exact EquivStmt.refl _
  | .break => by simp only [hoistInitStmt]; exact EquivStmt.refl _
  | .continue => by simp only [hoistInitStmt]; exact EquivStmt.refl _
  | .leave => by simp only [hoistInitStmt]; exact EquivStmt.refl _

theorem hoistInitStmts_forall2 : ∀ ss : List (Stmt D.Op),
    List.Forall₂ (EquivStmt D) ss (hoistInitStmts ss)
  | [] => .nil
  | s :: rest => .cons (hoistInitStmt_equiv s) (hoistInitStmts_forall2 rest)

theorem hoistInitCases_forall2 : ∀ cs : List (Literal × Block D.Op),
    List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2) cs (hoistInitCases cs)
  | [] => .nil
  | (_, b) :: rest =>
      .cons ⟨rfl, EquivBlock.of_stmts (EquivStmts.of_forall₂ (hoistInitStmts_forall2 b))
        (hoist_hoistInitStmts b).symm⟩ (hoistInitCases_forall2 rest)

end

/-- A block is equivalent to its transform. -/
theorem hoistForInit_blockEquiv (b : List (Stmt D.Op)) : EquivBlock D b (hoistInitStmts b) :=
  EquivBlock.of_stmts (EquivStmts.of_forall₂ (hoistInitStmts_forall2 b))
    (hoist_hoistInitStmts b).symm

/-- The **hoist-for-init pass**: pull a `SimpleInit` initializer out of every
`for` loop, bundled with its soundness proof. -/
def hoistForInit : Pass D where
  run := hoistInitStmts
  sound := hoistForInit_blockEquiv



