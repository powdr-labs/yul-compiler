import YulEvmCompiler.Optimizer.Core.Equiv
import YulSemantics.Syntax
import YulSemantics.Observation
set_option warningAsError true

/-!
# YulEvmCompiler.Optimizer.Core.RewriteExamples

Sample **local rewrites** for the EVM dialect, proven as semantic equivalences and lifted through
the congruence lemmas of `YulSemantics.Equiv` — validating that the equivalence/congruence framework
can carry an optimizer's proof obligations:

* constant folding: `add(2, 3) ≈ 5`;
* algebraic identity: `add(x, 0) ≈ x` (for a variable `x`);
* a lifted statement rewrite: `sstore(0, add(x, 0)) ≈ sstore(0, x)` via congruence.

Note the shape of the identity: it is stated for a *variable* argument, not an arbitrary
expression. `add(e, 0) ≈ e` is **false** for arbitrary `e` — if `e` is a call returning two
values, the left side is stuck while the right is not. The general version needs a "single-valued
expression" premise; rewrites on variables/literals (what an optimizer's value-numbering pass
produces) avoid it.
-/

namespace YulSemantics.Rewrites

open YulSemantics EVM

/-! ### Inversion helpers for two-element EVM argument lists -/

/-- Two literal arguments always evaluate to their values, unchanged state. -/
private theorem two_lits_inv {funs V st l₁ l₂ r}
    (h : EvalArgs EVM.evm funs V st [.lit l₁, .lit l₂] r) :
    r = .vals [EVM.litValue l₁, EVM.litValue l₂] st := by
  cases h with
  | argsCons h₁ h₂ =>
      cases h₂ with
      | lit =>
          cases h₁ with
          | argsCons h₃ h₄ =>
              cases h₄ with
              | lit => cases h₃ with | argsNil => rfl
  | argsRestHalt h₁ =>
      cases h₁ with
      | argsRestHalt h₃ => cases h₃
      | argsHeadHalt h₃ h₄ => cases h₄
  | argsHeadHalt h₁ h₂ => cases h₂

/-- A variable and a literal always evaluate to the variable's value and the literal, unchanged
state. -/
private theorem var_lit_inv {funs V st x l r}
    (h : EvalArgs EVM.evm funs V st [.var x, .lit l] r) :
    ∃ v, VEnv.get V x = some v ∧ r = .vals [v, EVM.litValue l] st := by
  cases h with
  | argsCons h₁ h₂ =>
      cases h₂ with
      | var hv =>
          cases h₁ with
          | argsCons h₃ h₄ =>
              cases h₄ with
              | lit => cases h₃ with | argsNil => exact ⟨_, hv, rfl⟩
  | argsRestHalt h₁ =>
      cases h₁ with
      | argsRestHalt h₃ => cases h₃
      | argsHeadHalt h₃ h₄ => cases h₄
  | argsHeadHalt h₁ h₂ => cases h₂

/-! ### Constant folding: `add(2, 3) ≈ 5` -/

theorem fold_add_2_3 :
    EquivExpr EVM.evm (.builtin .add [.lit (.number 2), .lit (.number 3)]) (.lit (.number 5)) := by
  have hval : EVM.litValue (.number 2) + EVM.litValue (.number 3) = EVM.litValue (.number 5) := by
    decide
  intro funs V st r
  constructor
  · intro h
    cases h with
    | builtinOk ha hb =>
        have hr := two_lits_inv ha
        injection hr with h1 h2; subst h1; subst h2
        simp [EVM.stepOp, EVM.bin] at hb
        obtain ⟨rfl, rfl⟩ := hb
        rw [hval]
        exact Step.lit
    | builtinHalt ha hb =>
        have hr := two_lits_inv ha
        injection hr with h1 h2; subst h1; subst h2
        simp [EVM.stepOp, EVM.bin] at hb
    | builtinArgsHalt ha =>
        have hr := two_lits_inv ha
        simp at hr
  · intro h
    cases h with
    | lit =>
        refine Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) ?_
        simp [EVM.stepOp, EVM.bin, hval]

/-! ### Algebraic identity: `add(x, 0) ≈ x` -/

theorem add_zero (x : Ident) :
    EquivExpr EVM.evm (.builtin .add [.var x, .lit (.number 0)]) (.var x) := by
  have hz : ∀ v : EVM.U256, v + EVM.litValue (.number 0) = v := fun v => by
    have h0 : EVM.litValue (.number 0) = 0 := by decide
    rw [h0]; exact BitVec.add_zero v
  intro funs V st r
  constructor
  · intro h
    cases h with
    | builtinOk ha hb =>
        obtain ⟨v, hv, hr⟩ := var_lit_inv ha
        injection hr with h1 h2; subst h1; subst h2
        simp [EVM.stepOp, EVM.bin] at hb
        obtain ⟨rfl, rfl⟩ := hb
        rw [hz]
        exact Step.var hv
    | builtinHalt ha hb =>
        obtain ⟨v, hv, hr⟩ := var_lit_inv ha
        injection hr with h1 h2; subst h1; subst h2
        simp [EVM.stepOp, EVM.bin] at hb
    | builtinArgsHalt ha =>
        obtain ⟨v, hv, hr⟩ := var_lit_inv ha
        simp at hr
  · intro h
    cases h with
    | var hv =>
        refine Step.builtinOk
          (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var hv)) ?_
        simp [EVM.stepOp, EVM.bin, hz]

/-! ### Lifting through congruence: a statement-level rewrite -/

/-- The identity lifted into a statement: `sstore(0, add(x, 0)) ≈ sstore(0, x)`. Assembled purely
from the congruence lemmas plus the local rewrite. -/
theorem sstore_add_zero (x : Ident) :
    EquivStmt EVM.evm
      (.exprStmt (.builtin .sstore [.lit (.number 0), .builtin .add [.var x, .lit (.number 0)]]))
      (.exprStmt (.builtin .sstore [.lit (.number 0), .var x])) :=
  EquivStmt.exprStmt_congr
    (EquivExpr.builtin_congr EVM.Op.sstore
      (EquivArgs.of_forall₂ (D := EVM.evm) (.cons (EquivExpr.refl _) (.cons (add_zero x) .nil))))

/-- The same rewrite at the whole-program level, written in concrete syntax (the `x` here is the
Yul identifier `"x"`). The `hoist` side condition is `rfl` — the rewrite touches no function
definitions. -/
example :
    EquivBlock EVM.evm (yul% { sstore(0, add(x, 0)) }) (yul% { sstore(0, x) }) :=
  EquivBlock.of_forall₂ (.cons (sstore_add_zero "x") .nil) rfl

end YulSemantics.Rewrites

/-! ## The dead-store payoff, at the observation boundary

Moved (with the sample rewrites above, both verbatim from yul-semantics at rev `d557aac`)
because dead-effect reasoning belongs to the optimizer: `RunCommitted` — the frame-boundary
observation this is stated against — stays in the semantics. -/

namespace YulSemantics

open EVM
/-! ### Payoff: a dead `sstore` before a `revert` is observationally invisible -/

/-- `{ sstore(0, 1); revert(0, 0) }` — a storage write immediately shadowed by a revert. -/
def deadStoreRevert : Block EVM.Op :=
  [ .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)]),
    .exprStmt (.builtin .revert [.lit (.number 0), .lit (.number 0)]) ]

/-- `{ revert(0, 0) }` — the bare revert. -/
def bareRevert : Block EVM.Op :=
  [ .exprStmt (.builtin .revert [.lit (.number 0), .lit (.number 0)]) ]

/-- The dead-store program runs (raw, exact-state) to a `revert` halt, and its committed observation
rolls every effect back to `st0` with only the `revert` marker set. The raw result state — left
implicit — still carries `storage[0] = 1`; `committedState` is what discards it. -/
private theorem run_dead (st0 : EvmState) (hstatic : st0.env.static = false) :
    ∃ st', Run EVM.evm deadStoreRevert st0 [] st' .halt ∧
      committedState st0 st' = { st0 with halted := some (.revert, []) } := by
  -- With a non-static frame the guarded `sstore` takes its write branch; pin its result state
  -- explicitly so the run's final state stays concrete.
  have hss : evm.Builtin .sstore [evm.litValue (.number 0), evm.litValue (.number 1)] st0
      (.ok [] { st0 with
        storage := upd st0.storage (evm.litValue (.number 0)) (evm.litValue (.number 1)),
        env := { st0.env with
          storageOf := updAccount st0.env.storageOf st0.env.address
            (evm.litValue (.number 0)) (evm.litValue (.number 1)) } }) := by
    show stepOp .sstore _ st0 = some _
    simp [stepOp, guardStatic, hstatic]
  have hrun : Run EVM.evm deadStoreRevert st0 [] _ .halt :=
    Step.block (D := EVM.evm) (Step.seqCons
      (Step.exprStmt (Step.builtinOk
        (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) hss))
      (Step.seqStop
        (Step.exprStmtHalt (Step.builtinHalt
          (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) rfl))
        (by decide)))
  exact ⟨_, hrun, rfl⟩

/-- The bare revert runs to the same committed observation from `st0`. -/
private theorem run_bare (st0 : EvmState) :
    ∃ st', Run EVM.evm bareRevert st0 [] st' .halt ∧
      committedState st0 st' = { st0 with halted := some (.revert, []) } := by
  have hrun : Run EVM.evm bareRevert st0 [] _ .halt :=
    Step.block (D := EVM.evm) (Step.seqStop
      (Step.exprStmtHalt (Step.builtinHalt
        (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) rfl))
      (by decide))
  exact ⟨_, hrun, rfl⟩

/-- Both programs observe the same canonical committed state: `st0` with only the `revert` marker
set (all world changes discarded, no return data). -/
theorem deadStoreRevert_committed (st0 : EvmState) (hstatic : st0.env.static = false) :
    RunCommitted deadStoreRevert st0 [] { st0 with halted := some (.revert, []) } .halt := by
  obtain ⟨st', hrun, heq⟩ := run_dead st0 hstatic
  exact ⟨st', hrun, heq.symm⟩

theorem bareRevert_committed (st0 : EvmState) :
    RunCommitted bareRevert st0 [] { st0 with halted := some (.revert, []) } .halt := by
  obtain ⟨st', hrun, heq⟩ := run_bare st0
  exact ⟨st', hrun, heq.symm⟩

/-- **The general theorem.** From every *non-static* initial state `st0`, the dead-store program and
the bare revert have identical observed (committed) runs. In particular the shadowed `sstore(0, 1)`
is invisible at the frame boundary — the raw exact-state relations (`EquivBlock`, which compare the
full `Step` state) cannot prove this, because they see the un-rolled-back storage write. Proven
relationally via whole-program determinism (`EVM.run_det`), quantified over all non-static `st0`.

The `st0.env.static = false` hypothesis is essential and faithful: under a `STATICCALL` context the
two programs genuinely differ — `sstore` itself halts with `.staticViolation` (exceptional), so the
dead-store program observes a `.staticViolation` halt while the bare revert observes `.revert`. -/
theorem deadStore_revert_obs_eq (st0 : EvmState) (hstatic : st0.env.static = false)
    (V' : VEnv EVM.evm) (stObs : EvmState) (o : Outcome) :
    RunCommitted deadStoreRevert st0 V' stObs o ↔ RunCommitted bareRevert st0 V' stObs o := by
  obtain ⟨sd, hd, hde⟩ := run_dead st0 hstatic
  obtain ⟨sb, hb, hbe⟩ := run_bare st0
  constructor
  · rintro ⟨st', hrun, rfl⟩
    obtain ⟨rfl, rfl, rfl⟩ := EVM.run_det hrun hd
    exact ⟨sb, hb, by rw [hde, hbe]⟩
  · rintro ⟨st', hrun, rfl⟩
    obtain ⟨rfl, rfl, rfl⟩ := EVM.run_det hrun hb
    exact ⟨sd, hd, by rw [hbe, hde]⟩

/-! ### Concrete demonstration

The raw run keeps the dead write (`storage[0] = 1`); the committed observation rolls it back
(`storage[0] = 0`, as in the initial state). -/

example :
    ∃ st', Run EVM.evm deadStoreRevert EvmState.init [] st' .halt ∧
      st'.storage 0 = 1 ∧
      (committedState EvmState.init st').storage 0 = 0 := by
  have hrun : Run EVM.evm deadStoreRevert EvmState.init [] _ .halt :=
    Step.block (D := EVM.evm) (Step.seqCons
      (Step.exprStmt (Step.builtinOk
        (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) rfl))
      (Step.seqStop
        (Step.exprStmtHalt (Step.builtinHalt
          (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) rfl))
        (by decide)))
  exact ⟨_, hrun, by decide, by decide⟩

end YulSemantics
