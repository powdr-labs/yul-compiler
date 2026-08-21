import YulEvmCompiler.Correctness
import YulSemantics.Contract

set_option warningAsError true

/-!
# Transporting relational Yul contracts through compilation

The core compiler theorem consumes one exact source `Run`.  This module lifts it to the
proof-facing `YulSemantics.RunContract` API: clients supply an arbitrary source pre/postcondition
and receive both that source postcondition and the matching target execution, without exposing the
constructed source final state outside this boundary.
-/

namespace YulEvmCompiler

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics (Outcome RunContract VEnv)
open YulSemantics.EVM (EvmState Op evmWithExternal)

variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates model.gas

/-- The target execution guarantee produced by `compile_correct`, packaged as a relation between
the source initial/final states and outcome.  Keeping the gas bound existential makes the relation
usable by functional proofs that deliberately do not account for gas. -/
def CompiledRun (is : List Instr) (sourceInitial sourceFinal : EvmState)
    (outcome : Outcome) : Prop :=
  ∃ bound : Nat, ∀ targetInitial : State,
    FrameOK (assemble is) targetInitial →
    StateMatch sourceInitial targetInitial →
    targetInitial.pc = UInt256.ofNat 0 →
    targetInitial.stack = [] →
    bound ≤ targetInitial.gasAvailable →
    ∃ targetFinal, Steps targetInitial targetFinal ∧
      targetFinal.callStack = [] ∧
      StateMatch sourceFinal targetFinal ∧
      ((outcome = .normal ∧ targetFinal.halt = .Success ∧ targetFinal.hReturn = .empty) ∨
       (outcome = .halt ∧ HaltedMatch sourceFinal targetFinal))

/-- Transport an arbitrary relational source contract to the compiled EVM program.  The result
retains the caller's source postcondition alongside the target run relation; it never asks the
caller to state an equality with a fully expanded source or target final state. -/
theorem compile_runContract (hexternal : ExternalsRealized model)
    {program : YulSemantics.Block Op} {is : List Instr}
    {pre : EvmState → Prop}
    {post : EvmState → VEnv yulD → EvmState → Outcome → Prop}
    (hcompile : compile program imm = some is)
    (hcontract : RunContract (D := yulD) program pre post)
    {sourceInitial : EvmState} (hpre : pre sourceInitial)
    (himm : ∀ key,
      imm key = sourceInitial.env.immutable (YulSemantics.EVM.litValue (.string key))) :
    ∃ finalEnv sourceFinal outcome,
      post sourceInitial finalEnv sourceFinal outcome ∧
      CompiledRun is sourceInitial sourceFinal outcome := by
  obtain ⟨finalEnv, sourceFinal, outcome, hrun, hpost⟩ := hcontract sourceInitial hpre
  obtain ⟨bound, htarget⟩ := compile_correct hexternal hcompile himm hrun
  exact ⟨finalEnv, sourceFinal, outcome, hpost, bound, htarget⟩

/-- Result-level form of `CompiledRun`, corresponding to `compile_correct_eval`. -/
def CompiledEval (is : List Instr) (sourceInitial sourceFinal : EvmState)
    (outcome : Outcome) : Prop :=
  ∃ bound : Nat, ∀ targetInitial : State,
    FrameOK (assemble is) targetInitial →
    StateMatch sourceInitial targetInitial →
    targetInitial.pc = UInt256.ofNat 0 →
    targetInitial.stack = [] →
    bound ≤ targetInitial.gasAvailable →
    (outcome = .normal → Eval targetInitial .success) ∧
    (outcome = .halt → ∃ haltKind,
      sourceFinal.halted = some haltKind ∧ Eval targetInitial (resultOf haltKind))

/-- Transport a source contract directly to the target result-level `Eval` relation. -/
theorem compile_runContract_eval (hexternal : ExternalsRealized model)
    {program : YulSemantics.Block Op} {is : List Instr}
    {pre : EvmState → Prop}
    {post : EvmState → VEnv yulD → EvmState → Outcome → Prop}
    (hcompile : compile program imm = some is)
    (hcontract : RunContract (D := yulD) program pre post)
    {sourceInitial : EvmState} (hpre : pre sourceInitial)
    (himm : ∀ key,
      imm key = sourceInitial.env.immutable (YulSemantics.EVM.litValue (.string key))) :
    ∃ finalEnv sourceFinal outcome,
      post sourceInitial finalEnv sourceFinal outcome ∧
      CompiledEval is sourceInitial sourceFinal outcome := by
  obtain ⟨finalEnv, sourceFinal, outcome, hrun, hpost⟩ := hcontract sourceInitial hpre
  obtain ⟨bound, htarget⟩ := compile_correct_eval hexternal hcompile himm hrun
  exact ⟨finalEnv, sourceFinal, outcome, hpost, bound, htarget⟩

end YulEvmCompiler
