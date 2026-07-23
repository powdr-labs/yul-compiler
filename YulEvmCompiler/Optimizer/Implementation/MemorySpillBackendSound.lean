import YulEvmCompiler.Optimizer.Implementation.MemorySpillObjectSound
import YulEvmCompiler.Correctness
import YulEvmCompiler.ObjectCompile
set_option warningAsError true
/-!
# Backend composition for verified memory spilling

This module connects the plan/block semantic layer to the ordinary verified
Yul backend.  `StateMatch` is intentionally stated for the emitted target-Yul
final state.  The guarded source final state is related only observationally,
through `ScratchRel.runObservables_eq` (or exact equality on a fallback node).
-/

namespace YulEvmCompiler.Optimizer.MemorySpillBackendSound

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open MemorySpill
open MemorySpillSelect
open MemorySpillObjectSound

variable [model : ExternalModel]

local notation "D" => evmWithExternal model.calls model.creates
local notation "G" => guardedEvm model.calls model.creates

omit model in
theorem PlannedFinalRel.runObservables_eq
    {plan : MemorySpillSelect.ObjectPlan}
    {sourceEnv targetEnv : WordEnv} {sourceFinal targetFinal initial : EvmState}
    (hrel : PlannedFinalRel plan sourceEnv sourceFinal targetEnv targetFinal) :
    runObservables initial sourceFinal = runObservables initial targetFinal := by
  cases plan with
  | mk code children =>
      cases code with
      | none =>
          rcases hrel with ⟨_, rfl⟩
          rfl
      | some result =>
          exact ScratchRel.runObservables_eq hrel
/-- Compile one successful spill result after resolving object-layout
references.  The backend matches the emitted target-Yul state; the source
state may differ in the reserved spill interval but has the same committed
observable result. -/
theorem compile_spilled_correct
    (hexternal : ExternalsRealized model)
    {L : EVM.Layout} {raw : Block Op} {result : Result}
    {guards : List Nat} {instructions : List Instr}
    (hspillSound : SpillNodeRunSound
      (calls := model.calls) (creates := model.creates) L)
    (hfacts : SpillFacts raw result guards)
    (hguarded : GuardedExternals model.calls model.creates
      result.base result.reserved)
    (hcomp : compile (resolveForLayoutStmts L result.block) =
      some instructions)
    {sourceEnv : WordEnv} {sourceFinal : EvmState} {out : Outcome}
    (hsource : Run (G result.base result.reserved)
      (resolveForLayoutStmts L
        (resolveMemoryGuardStmts result.base result.reserved raw))
      L.initState sourceEnv sourceFinal out) :
    ∃ targetEnv targetFinal,
      Run D (resolveForLayoutStmts L result.block)
        L.initState targetEnv targetFinal out ∧
      ScratchRel result.base result.reserved sourceFinal targetFinal ∧
      runObservables L.initState sourceFinal =
        runObservables L.initState targetFinal ∧
      ∃ bound : Nat, ∀ s0 : State,
        FrameOK (assemble instructions) s0 →
        StateMatch L.initState s0 →
        s0.pc = UInt256.ofNat 0 → s0.stack = [] →
        bound ≤ s0.gasAvailable →
        ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧
          StateMatch targetFinal s' ∧
          ((out = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
           (out = .halt ∧ HaltedMatch targetFinal s')) := by
  obtain ⟨targetEnv, targetFinal, htarget, hscratch⟩ :=
    hspillSound hfacts hguarded hsource
  have hobs : runObservables L.initState sourceFinal =
      runObservables L.initState targetFinal :=
    ScratchRel.runObservables_eq hscratch
  obtain ⟨bound, hbackend⟩ := compile_correct hexternal hcomp htarget
  exact ⟨targetEnv, targetFinal, htarget, hscratch, hobs, bound, hbackend⟩

/-- Generic object backend composition for an already established plan-node
run transformer.  This form is useful independently of the production object
constructor and exposes the emitted target-Yul final state explicitly. -/
theorem compileObject_planned_correct
    (hexternal : ExternalsRealized model)
    {L : EVM.Layout} {raw output : Object Op}
    {plan : MemorySpillSelect.ObjectPlan}
    (hplanSound : PlannedNodeRunSound
      (calls := model.calls) (creates := model.creates) L raw output plan)
    (hcomp : compileObject output = some L)
    {sourceEnv : WordEnv} {sourceFinal : EvmState} {out : Outcome}
    (hsource : PlannedTopRun (calls := model.calls) (creates := model.creates)
      L raw plan sourceEnv sourceFinal out) :
    ∃ targetEnv targetFinal,
      RunResolvedObject output L targetEnv targetFinal out ∧
      PlannedFinalRel plan sourceEnv sourceFinal targetEnv targetFinal ∧
      runObservables L.initState sourceFinal =
        runObservables L.initState targetFinal ∧
      ∃ bound : Nat, ∀ s0 : State,
        FrameOK (mkCode L.code) s0 → StateMatch L.initState s0 →
        s0.pc = UInt256.ofNat 0 → s0.stack = [] →
        bound ≤ s0.gasAvailable →
        ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧
          StateMatch targetFinal s' ∧
          ((out = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
           (out = .halt ∧ HaltedMatch targetFinal s')) := by
  obtain ⟨targetEnv, targetFinal, htarget, hfinal⟩ := hplanSound hsource
  have hobs := PlannedFinalRel.runObservables_eq
    (initial := L.initState) hfinal
  obtain ⟨bound, hbackend⟩ := compileObject_correct hexternal hcomp htarget
  exact ⟨targetEnv, targetFinal, htarget, hfinal, hobs, bound, hbackend⟩

/-- Final parameterized production composition.  Object recursion, fallback
pipeline preservation, Yul-to-EVM compilation, outcome discipline, and
observable source/target agreement are all discharged here; ControlSound only
has to provide `SpillNodeRunSound`. -/
theorem compileObject_memorySpill_correct
    (hexternal : ExternalsRealized model)
    {raw output : Object Op} {plan : MemorySpillSelect.ObjectPlan}
    {selected : Nat} {L : EVM.Layout}
    (hbuild : spillObjectWithFallback raw
      (optimizerPipelineObject (calls := model.calls) (creates := model.creates)
        (eraseMemoryGuardObject raw)) =
        some { «object» := output, plan := plan, selected := selected })
    (hspillSound : SpillNodeRunSound
      (calls := model.calls) (creates := model.creates) L)
    (hcomp : compileObject output = some L)
    {sourceEnv : WordEnv} {sourceFinal : EvmState} {out : Outcome}
    (hsource : PlannedTopRun (calls := model.calls) (creates := model.creates)
      L raw plan sourceEnv sourceFinal out) :
    ∃ targetEnv targetFinal,
      RunResolvedObject output L targetEnv targetFinal out ∧
      PlannedFinalRel plan sourceEnv sourceFinal targetEnv targetFinal ∧
      runObservables L.initState sourceFinal =
        runObservables L.initState targetFinal ∧
      ∃ bound : Nat, ∀ s0 : State,
        FrameOK (mkCode L.code) s0 → StateMatch L.initState s0 →
        s0.pc = UInt256.ofNat 0 → s0.stack = [] →
        bound ≤ s0.gasAvailable →
        ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧
          StateMatch targetFinal s' ∧
          ((out = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
           (out = .halt ∧ HaltedMatch targetFinal s')) := by
  exact compileObject_planned_correct hexternal
    (spillObjectWithErasedPipelineFallback_top_run hbuild hspillSound)
    hcomp hsource

end YulEvmCompiler.Optimizer.MemorySpillBackendSound
