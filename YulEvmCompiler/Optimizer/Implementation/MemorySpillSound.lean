import YulEvmCompiler.Optimizer.Implementation.MemorySpillStmtStepSound
import YulEvmCompiler.Optimizer.Implementation.MemorySpillBackendSound
set_option warningAsError true
/-!
# End-to-end semantic soundness of guarded memory spilling

This module instantiates the block-level callback used by the object and EVM
backend composition.  The structural simulation is applied at the synthetic
root frame; the resulting target state may differ from the guarded source only
inside the compiler-owned scratch interval.
-/

namespace YulEvmCompiler.Optimizer.MemorySpillSound

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open MemorySpill
open MemorySpillSelect
open MemorySpillStateSound
open MemorySpillRewriteSound
open MemorySpillOriginSound
open MemorySpillControlSound
open MemorySpillStepSound
open MemorySpillStmtStepSound
open MemorySpillObjectSound
open MemorySpillBackendSound

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-- Direct block-root simulation, before any object-layout resolution. -/
theorem spillBlockRunSound {raw : Block Op} {result : Result}
    {guards : List Nat}
    (hfacts : SpillFacts raw result guards)
    (hexternals : GuardedExternals calls creates result.base result.reserved)
    {initial : EvmState} {sourceEnv : MemorySpillObjectSound.WordEnv}
    {sourceFinal : EvmState}
    {out : Outcome}
    (hsource : Run (guardedEvm calls creates result.base result.reserved)
      (resolveMemoryGuardStmts result.base result.reserved raw)
      initial sourceEnv sourceFinal out) :
    ∃ targetEnv targetFinal,
      Run D result.block initial targetEnv targetFinal out ∧
      ScratchRel result.base result.reserved sourceFinal targetFinal := by
  let policyRoot :=
    resolveMemoryGuardStmts result.base result.reserved raw
  let rootFrame : MemorySpillSelect.Frame :=
    { owner := none, params := [], returns := [], body := policyRoot }
  have hctx0 := ControlStepContext.rootInitial
    (raw := raw) (result := result) hfacts .identity
  have hctx := hctx0.asBlockStmt
  have hrel := ControlLiveRel.rootInitial hfacts initial
  have hcovered : FunsCovered
      (guardedEvm calls creates result.base result.reserved)
      (fun body => body)
      ((frames policyRoot).map ((.identity : OriginMode).execFrame)) [] :=
    FunsCovered.nil _ _ _
  have hrootMem : rootFrame ∈ frames policyRoot := by
    simp [rootFrame, frames]
  have hcutoff : frameCutoff result.base result.layout
      (frameInfo result.selection
        ((frames policyRoot).filterMap (·.owner)) rootFrame) ≤ result.reserved :=
    SpillFacts.frameCutoff_le_reserved hfacts hrootMem
  have hsim := step_sim hfacts hexternals .identity hsource
    hctx hrel hcovered rfl hcutoff
  obtain ⟨targetResult, htarget, hresult, _habove⟩ := hsim
  cases targetResult with
  | eres targetExprResult =>
      simp [ResultControlRel] at hresult
  | sres targetEnv targetFinal targetOutcome =>
      rcases hresult with
        ⟨finalLive, houtcome, hcontrol, _horigin, _hexitBound,
          _hexitSignature, _hleave, _hblock, _hnormal⟩
      subst targetOutcome
      refine ⟨targetEnv, targetFinal, ?_, hcontrol.liveRel.frameRel.scratch⟩
      have htarget' : ExecStmts D [] [] initial
          [.block (rewriteStmts result.layout.slots none [] policyRoot)]
          targetEnv targetFinal out := by
        simpa [policyRoot, rootFrame, rewriteCode, spillFuns,
          copyBackReturns, rewriteStmt] using htarget
      have hstmt := execStmt_of_singleton htarget'
      simpa [Run, policyRoot, rootFrame, rewriteCode, hfacts.block_eq] using hstmt

/-- The concrete block transformer required by object-plan composition. -/
theorem spillNodeRunSound (L : EVM.Layout) :
    SpillNodeRunSound (calls := calls) (creates := creates) L := by
  intro raw result guards sourceEnv sourceFinal out hfacts hexternals hsource
  let policyRoot :=
    resolveMemoryGuardStmts result.base result.reserved raw
  let rootFrame : MemorySpillSelect.Frame :=
    { owner := none, params := [], returns := [], body := policyRoot }
  have hctx0 := ControlStepContext.rootInitial
    (raw := raw) (result := result) hfacts (.object L)
  have hctx := hctx0.asBlockStmt
  have hrel := ControlLiveRel.rootInitial hfacts L.initState
  have hcovered : FunsCovered
      (guardedEvm calls creates result.base result.reserved)
      (fun body => body)
      ((frames policyRoot).map ((.object L : OriginMode).execFrame)) [] :=
    FunsCovered.nil _ _ _
  have hrootMem : rootFrame ∈ frames policyRoot := by
    simp [rootFrame, frames]
  have hcutoff : frameCutoff result.base result.layout
      (frameInfo result.selection
        ((frames policyRoot).filterMap (·.owner)) rootFrame) ≤ result.reserved :=
    SpillFacts.frameCutoff_le_reserved hfacts hrootMem
  have hsim := step_sim hfacts hexternals (.object L) hsource
    hctx hrel hcovered rfl hcutoff
  obtain ⟨targetResult, htarget, hresult, _habove⟩ := hsim
  cases targetResult with
  | eres targetExprResult =>
      simp [ResultControlRel] at hresult
  | sres targetEnv targetFinal targetOutcome =>
      rcases hresult with
        ⟨finalLive, houtcome, hcontrol, _horigin, _hexitBound,
          _hexitSignature, _hleave, _hblock, _hnormal⟩
      subst targetOutcome
      refine ⟨targetEnv, targetFinal, ?_, hcontrol.liveRel.frameRel.scratch⟩
      have htarget' : ExecStmts D [] [] L.initState
          [.block (rewriteStmts result.layout.slots none []
            (resolveForLayoutStmts L policyRoot))]
          targetEnv targetFinal out := by
        simpa [policyRoot, rootFrame, rewriteCode, spillFuns,
          copyBackReturns, rewriteStmt] using htarget
      have hstmt := execStmt_of_singleton htarget'
      simpa [Run, policyRoot, rootFrame, rewriteCode, hfacts.block_eq,
        resolveForLayout_rewriteStmts] using hstmt

variable [model : ExternalModel]

/-- Concrete one-block backend theorem with the spill callback discharged. -/
theorem compile_spilled_correct
    (hexternal : ExternalsRealized model)
    {L : EVM.Layout} {raw : Block Op} {result : Result}
    {guards : List Nat} {instructions : List Instr}
    (hfacts : SpillFacts raw result guards)
    (hguarded : GuardedExternals model.calls model.creates
      result.base result.reserved)
    (hcomp : compile (resolveForLayoutStmts L result.block) =
      some instructions)
    {sourceEnv : MemorySpillObjectSound.WordEnv}
    {sourceFinal : EvmState} {out : Outcome}
    (hsource : Run
      (guardedEvm model.calls model.creates result.base result.reserved)
      (resolveForLayoutStmts L
        (resolveMemoryGuardStmts result.base result.reserved raw))
      L.initState sourceEnv sourceFinal out) :
    ∃ targetEnv targetFinal,
      Run (evmWithExternal model.calls model.creates)
        (resolveForLayoutStmts L result.block)
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
           (out = .halt ∧ HaltedMatch targetFinal s')) :=
  MemorySpillBackendSound.compile_spilled_correct hexternal
    (spillNodeRunSound (calls := model.calls) (creates := model.creates) L)
    hfacts hguarded hcomp hsource

/-- Direct production block-root composition from a successful spill choice
through ordinary Yul compilation and the verified EVM backend. -/
theorem compile_memorySpill_correct
    (hexternal : ExternalsRealized model)
    {raw : Block Op} {result : Result} {instructions : List Instr}
    (hspill : spillBlock? raw = some result)
    (hguarded : GuardedExternals model.calls model.creates
      result.base result.reserved)
    (hcomp : compile result.block = some instructions)
    {initial sourceFinal : EvmState}
    {sourceEnv : MemorySpillObjectSound.WordEnv} {out : Outcome}
    (hsource : Run
      (guardedEvm model.calls model.creates result.base result.reserved)
      (resolveMemoryGuardStmts result.base result.reserved raw)
      initial sourceEnv sourceFinal out) :
    ∃ targetEnv targetFinal,
      Run (evmWithExternal model.calls model.creates) result.block
        initial targetEnv targetFinal out ∧
      ScratchRel result.base result.reserved sourceFinal targetFinal ∧
      runObservables initial sourceFinal = runObservables initial targetFinal ∧
      ∃ bound : Nat, ∀ s0 : State,
        FrameOK (assemble instructions) s0 →
        StateMatch initial s0 →
        s0.pc = UInt256.ofNat 0 → s0.stack = [] →
        bound ≤ s0.gasAvailable →
        ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧
          StateMatch targetFinal s' ∧
          ((out = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
           (out = .halt ∧ HaltedMatch targetFinal s')) := by
  obtain ⟨guards, hfacts⟩ := spillBlock_facts hspill
  obtain ⟨targetEnv, targetFinal, htarget, hscratch⟩ :=
    spillBlockRunSound (calls := model.calls) (creates := model.creates)
      hfacts hguarded hsource
  have hobs : runObservables initial sourceFinal =
      runObservables initial targetFinal :=
    ScratchRel.runObservables_eq hscratch
  obtain ⟨bound, hbackend⟩ := compile_correct hexternal hcomp htarget
  exact ⟨targetEnv, targetFinal, htarget, hscratch, hobs, bound, hbackend⟩

/-- Concrete production object theorem with recursive spill/fallback soundness
and the block simulation callback both discharged. -/
theorem compileObject_memorySpill_correct
    (hexternal : ExternalsRealized model)
    {raw output : Object Op} {plan : MemorySpillSelect.ObjectPlan}
    {selected : Nat} {L : EVM.Layout}
    (hbuild : spillObjectWithFallback raw
      (optimizerPipelineObject (calls := model.calls) (creates := model.creates)
        (eraseMemoryGuardObject raw)) =
        some { «object» := output, plan := plan, selected := selected })
    (hcomp : compileObject output = some L)
    {sourceEnv : MemorySpillObjectSound.WordEnv}
    {sourceFinal : EvmState} {out : Outcome}
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
           (out = .halt ∧ HaltedMatch targetFinal s')) :=
  MemorySpillBackendSound.compileObject_memorySpill_correct hexternal hbuild
    (spillNodeRunSound (calls := model.calls) (creates := model.creates) L)
    hcomp hsource

end YulEvmCompiler.Optimizer.MemorySpillSound
