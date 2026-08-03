import YulEvmCompiler.Optimizer.Implementation.InlineCallsCarry
import YulEvmCompiler.Optimizer.Implementation.InlineCallsSound
import YulEvmCompiler.Optimizer.Implementation.FunCongr
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
/-!
# YulEvmCompiler.Optimizer.Implementation.InlineCallsCarrySound

Soundness of the call-carrying inliner (`InlineCallsCarry.lean`).

The architecture mirrors `InlineCallsSound`, with one change concentrated in
the callee-body transfer at an inline site. `InlineCalls` bodies are call-free,
so `scoped_transfer` moves the body's execution to *any* function environment
(it never consults `funs`). Carry bodies bear calls: the transplanted copy runs
its inner calls under the caller's function environment at the site, whereas the
original runs them under the callee's defining scope `cenv`. Two facts bridge
the gap:

* **`carry_transfer`** — the analog of `scoped_transfer` that *permits* calls.
  It transfers execution to any function environment that **agrees** with the
  original on the code's (syntactic) call names, and simultaneously weakens the
  variable environment by an inert suffix. Agreement is exactly what the
  no-shadowing gate (`carrySurvives`) guarantees between the callee's defining
  scope and the rewrite site.
* **`Step.funs_congr`** (`FunCongr.lean`) — the semantic function-environment
  congruence: once the body runs under the *source* site environment, it runs
  under the *transformed* site environment with the same result, because the
  two environments' functions have `EquivBlock`-equivalent bodies.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### Carry-scoped per-class checks (calls permitted) -/

/-- Per-class carry check for the transfer induction. -/
def carryArgs (bound : List Ident) : List (Expr Op) → Bool
  | [] => true
  | e :: rest => carryExpr bound e && carryArgs bound rest

/-- Per-class carry check for the transfer induction. -/
def carryCode (bound : List Ident) : Code Op → Bool
  | .expr e => carryExpr bound e
  | .args es => carryArgs bound es
  | .stmt s => (carryStmt bound s).isSome
  | .stmts ss => carryStmts bound ss
  | .loop _ _ _ => false

/-- The binding context the carry checker leaves after one statement. -/
def carryPostBound (bound : List Ident) : Code Op → List Ident
  | .stmt s => (carryStmt bound s).getD bound
  | _ => []

/-! ### Call-name collection per class (for the function-agreement side) -/

/-- The syntactic call names of a code class. -/
def carryCallNames : Code Op → List Ident
  | .expr e => exprCallNames e
  | .args es => argsCallNames es
  | .stmt s => stmtCallNames s
  | .stmts ss => stmtsCallNames ss
  | .loop _ _ _ => []

/-- Two function environments **agree** on a set of names when each resolves
identically under both. -/
def FunsAgree (funs₁ funs₂ : FunEnv D) (names : List Ident) : Prop :=
  ∀ g ∈ names, lookupFun funs₁ g = lookupFun funs₂ g

theorem FunsAgree.mono {funs₁ funs₂ : FunEnv D} {a b : List Ident}
    (h : FunsAgree (calls := calls) (creates := creates) funs₁ funs₂ b)
    (hsub : ∀ x ∈ a, x ∈ b) :
    FunsAgree (calls := calls) (creates := creates) funs₁ funs₂ a :=
  fun g hg => h g (hsub g hg)

/-- Agreement lifts through a common prepended **empty** scope (the only kind a
carry body introduces, since it has no `funDef`s): the empty scope resolves
nothing, so both sides recurse to the agreeing tails. -/
theorem FunsAgree.cons_nil {funs₁ funs₂ : FunEnv D} {names : List Ident}
    (h : FunsAgree (calls := calls) (creates := creates) funs₁ funs₂ names) :
    FunsAgree (calls := calls) (creates := creates) ([] :: funs₁) ([] :: funs₂) names := by
  intro g hg
  have e1 : lookupFun (([] : FScope D) :: funs₁) g = lookupFun funs₁ g := rfl
  have e2 : lookupFun (([] : FScope D) :: funs₂) g = lookupFun funs₂ g := rfl
  rw [e1, e2]; exact h g hg

/-- A carry-checked body has no top-level `funDef`, so it hoists nothing. -/
theorem carryStmts_hoist_nil {bound : List Ident} :
    ∀ {body : List (Stmt Op)}, carryStmts bound body = true → hoist D body = [] := by
  intro body
  induction body generalizing bound with
  | nil => intro _; rfl
  | cons s rest ih =>
      intro h
      unfold carryStmts at h
      cases hs : carryStmt bound s with
      | none => rw [hs] at h; exact absurd h (by simp)
      | some bound' =>
          rw [hs] at h
          cases s with
          | funDef n ps rs b => simp [carryStmt] at hs
          | block b => exact ih h
          | letDecl xs v => exact ih h
          | assign xs e => exact ih h
          | exprStmt e => exact ih h
          | cond c b => exact ih h
          | «switch» c cs d => exact ih h
          | forLoop i c p b => simp [carryStmt] at hs
          | «break» => simp [carryStmt] at hs
          | «continue» => simp [carryStmt] at hs
          | «leave» => simp [carryStmt] at hs

/-! ### Carry-scoped inversions -/

/-- Bound reads make an argument list carry-scoped (no call restriction). -/
theorem carryArgs_of_varsBound {bound : List Ident} {args : List (Expr Op)}
    (hv : (varsList args).all bound.contains = true) : carryArgs bound args = true := by
  induction args with
  | nil => rfl
  | cons e rest ih =>
      rw [show varsList (e :: rest) = exprVars e ++ varsList rest from rfl,
        List.all_append, Bool.and_eq_true] at hv
      unfold carryArgs
      rw [Bool.and_eq_true]
      exact ⟨by unfold carryExpr; exact hv.1, ih hv.2⟩

/-- A carry-scoped builtin's arguments are carry-scoped. -/
theorem carryExpr_builtin_args {bound : List Ident} {op : Op} {args : List (Expr Op)}
    (h : carryExpr bound (.builtin op args) = true) : carryArgs bound args = true := by
  unfold carryExpr at h
  exact carryArgs_of_varsBound (by simpa [exprVars] using h)

/-- A carry-scoped call's arguments are carry-scoped. -/
theorem carryExpr_call_args {bound : List Ident} {f : Ident} {args : List (Expr Op)}
    (h : carryExpr bound (.call f args) = true) : carryArgs bound args = true := by
  unfold carryExpr at h
  exact carryArgs_of_varsBound (by simpa [exprVars] using h)

/-- Split a carry sequence at its head. -/
theorem carryStmts_cons_inv {bound : List Ident} {s : Stmt Op} {rest : List (Stmt Op)}
    (h : carryStmts bound (s :: rest) = true) :
    ∃ bound₁, carryStmt bound s = some bound₁ ∧ carryStmts bound₁ rest = true := by
  unfold carryStmts at h
  split at h
  · next bound₁ heq => exact ⟨bound₁, heq, h⟩
  · cases h

/-- The selected switch block of carry-scoped cases/default is carry-scoped. -/
theorem carry_selectSwitch {bound : List Ident} {cv : U256}
    {cases : List (Literal × Block Op)} {dflt : Option (Block Op)}
    (hc : carryCases bound cases = true) (hd : carryDflt bound dflt = true) :
    carryStmts bound (selectSwitch D cv cases dflt) = true := by
  induction cases with
  | nil =>
      unfold selectSwitch
      simp only [List.find?_nil]
      cases dflt with
      | none => rfl
      | some b => exact hd
  | cons hd' rest ih =>
      rcases hd' with ⟨l, b⟩
      unfold carryCases at hc
      rw [Bool.and_eq_true] at hc
      by_cases hcv : cv = (evmWithExternal calls creates).litValue l
      · rw [selectSwitch, List.find?_cons_of_pos (by simp [hcv])]
        exact hc.1
      · rw [selectSwitch, List.find?_cons_of_neg (by simp [hcv])]
        have := ih hc.2
        rw [selectSwitch] at this
        exact this

/-- Call names of the selected switch block sit inside the cases'/default's. -/
theorem selectSwitch_callNames_sub {cv : U256}
    {cases : List (Literal × Block Op)} {dflt : Option (Block Op)} :
    ∀ g ∈ stmtsCallNames (selectSwitch D cv cases dflt),
      g ∈ casesCallNames cases ++ dfltCallNames dflt := by
  intro g hg
  induction cases with
  | nil =>
      simp only [selectSwitch, List.find?_nil] at hg
      cases dflt with
      | none => simp [stmtsCallNames] at hg
      | some b =>
          refine List.mem_append.mpr (Or.inr ?_)
          simpa [dfltCallNames] using hg
  | cons hd' rest ih =>
      rcases hd' with ⟨l, b⟩
      by_cases hcv : cv = (evmWithExternal calls creates).litValue l
      · rw [selectSwitch, List.find?_cons_of_pos (by simp [hcv])] at hg
        refine List.mem_append.mpr (Or.inl ?_)
        show g ∈ stmtsCallNames b ++ casesCallNames rest
        exact List.mem_append.mpr (Or.inl hg)
      · rw [selectSwitch, List.find?_cons_of_neg (by simp [hcv])] at hg
        have := ih (by rw [selectSwitch]; exact hg)
        rcases List.mem_append.mp this with h | h
        · exact List.mem_append.mpr (Or.inl (by
            show g ∈ stmtsCallNames b ++ casesCallNames rest
            exact List.mem_append.mpr (Or.inr h)))
        · exact List.mem_append.mpr (Or.inr h)
