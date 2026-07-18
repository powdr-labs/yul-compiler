import YulEvmCompiler.Optimizer.Implementation.InlineIdentityResolve
import YulEvmCompiler.Optimizer.Implementation.ObjectPass
set_option warningAsError true
/-!
# Production optimizer pipeline

The production pipeline simplifies expressions, applies scoped zero absorption,
inlines exact identity helpers, then repeats simplification and absorption.
-/

namespace YulEvmCompiler.Optimizer

open EvmSemantics EvmSemantics.EVM
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-- Verified production pipeline, applied left-to-right. -/
def identityPipeline : Pass D :=
  Pass.ofList [simplify, inlineIdentityPass, simplify]

@[simp] theorem identityPipeline_run (b : Block Op) :
    (identityPipeline (calls := calls) (creates := creates)).run b =
      absorbZeroStmts []
        (simplifyStmts
          (inlineIdentityBlock (calls := calls) (creates := creates)
            ([] : FunEnv D) (absorbZeroStmts [] (simplifyStmts b)))) := rfl

/-- Resolution congruence for the complete five-stage pipeline. -/
theorem resolveIdentityPipelineBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L
        ((identityPipeline (calls := calls) (creates := creates)).run b)) := by
  have hs₀ := resolveSimplifyBlock_equiv (calls := calls) (creates := creates) L b
  have ha₀ := resolveAbsorbZeroBlock_equiv (calls := calls) (creates := creates) L
    (simplifyStmts b)
  have hi := (inlineIdentityPass (calls := calls) (creates := creates)).sound
    (resolveForLayoutStmts L (absorbZeroStmts [] (simplifyStmts b)))
  change EquivBlock D (resolveForLayoutStmts L (absorbZeroStmts [] (simplifyStmts b)))
    (inlineIdentityBlock (calls := calls) (creates := creates) ([] : FunEnv D)
      (resolveForLayoutStmts L (absorbZeroStmts [] (simplifyStmts b)))) at hi
  rw [← resolve_inlineIdentityBlock_nil L (absorbZeroStmts [] (simplifyStmts b))] at hi
  have hs₁ := resolveSimplifyBlock_equiv (calls := calls) (creates := creates) L
    (inlineIdentityBlock (calls := calls) (creates := creates)
      ([] : FunEnv D) (absorbZeroStmts [] (simplifyStmts b)))
  have ha₁ := resolveAbsorbZeroBlock_equiv (calls := calls) (creates := creates) L
    (simplifyStmts
      (inlineIdentityBlock (calls := calls) (creates := creates)
        ([] : FunEnv D) (absorbZeroStmts [] (simplifyStmts b))))
  simpa using hs₀.trans (ha₀.trans (hi.trans (hs₁.trans ha₁)))

mutual
  /-- Run the verified pipeline on every object code block. -/
  def identityPipelineObject : Object Op → Object Op
    | .mk name code subs segs =>
        .mk name
          ((identityPipeline (calls := calls) (creates := creates)).run code)
          (identityPipelineObjects subs) segs

  /-- Run the verified pipeline on every object in a list. -/
  def identityPipelineObjects : List (Object Op) → List (Object Op)
    | [] => []
    | o :: rest => identityPipelineObject o :: identityPipelineObjects rest
end

@[simp] theorem identityPipelineObject_codeBlock (o : Object Op) :
    (identityPipelineObject (calls := calls) (creates := creates) o).codeBlock =
      (identityPipeline (calls := calls) (creates := creates)).run o.codeBlock := by
  cases o
  rfl

/-- The recursively optimized artifact is covered directly by the verified
object compiler theorem. -/
theorem identityPipelineObject_compileObject_correct
    [model : ExternalModel] (hexternal : ExternalsRealized model)
    {o : Object Op} {L : Layout}
    (hcomp : compileObject
      (identityPipelineObject (calls := model.calls) (creates := model.creates) o) = some L)
    {V : VEnv (evmWithExternal model.calls model.creates)}
    {yst : EvmState} {out : Outcome}
    (hrun : RunResolvedObject
      (identityPipelineObject (calls := model.calls) (creates := model.creates) o)
      L V yst out) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (mkCode L.code) s0 → StateMatch L.initState s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst s' ∧
        ((out = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (out = .halt ∧ HaltedMatch yst s')) :=
  compileObject_correct hexternal hcomp hrun

/-- Every object's own code block is pointwise equivalent to its source block. -/
theorem identityPipelineObject_topEquiv (o : Object Op) :
    EquivBlock D o.codeBlock
      (identityPipelineObject (calls := calls) (creates := creates) o).codeBlock := by
  rw [identityPipelineObject_codeBlock]
  exact (identityPipeline (calls := calls) (creates := creates)).sound o.codeBlock

/-- End-to-end correctness for the recursively optimized object tree, relative
to the original object's resolved execution under the optimized layout. -/
theorem identityPipelineObject_correct
    [model : ExternalModel] (hexternal : ExternalsRealized model)
    {o : Object Op} {L : Layout}
    (hcomp : compileObject
      (identityPipelineObject (calls := model.calls) (creates := model.creates) o) = some L)
    {V : VEnv (evmWithExternal model.calls model.creates)}
    {yst : EvmState} {out : Outcome}
    (hrun : RunResolvedObject o L V yst out) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (mkCode L.code) s0 → StateMatch L.initState s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst s' ∧
        ((out = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (out = .halt ∧ HaltedMatch yst s')) := by
  have hb := resolveIdentityPipelineBlock_equiv
    (calls := model.calls) (creates := model.creates) L o.codeBlock
  have hrun' : RunResolvedObject
      (identityPipelineObject (calls := model.calls) (creates := model.creates) o)
      L V yst out := by
    show Run (evmWithExternal model.calls model.creates)
      (resolveForLayoutStmts L
        (identityPipelineObject (calls := model.calls) (creates := model.creates) o).codeBlock)
      L.initState V yst out
    rw [identityPipelineObject_codeBlock]
    exact hb.run_iff.mp hrun
  exact compileObject_correct hexternal hcomp hrun'

end YulEvmCompiler.Optimizer
