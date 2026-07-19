import YulEvmCompiler.Optimizer.Implementation.InlineHelpersResolve
import YulEvmCompiler.Optimizer.Implementation.PropagateResolve
import YulEvmCompiler.Optimizer.Implementation.DeadLitsResolve
import YulEvmCompiler.Optimizer.Implementation.ObjectPass
set_option warningAsError true
/-!
# Production optimizer pipeline

The production pipeline simplifies expressions, propagates known bindings
(`Propagate`: constant + copy propagation with binding-preserving
substitution), inlines pure expression-body helpers through the Core boundary,
and simplifies again — the trailing round folds what substitution and inlining
exposed and removes the arity-preserving `add(e, 0)` fence where its removal is
proved.

Stage order differs by path, deliberately:

* **block path** (`optimizerPipeline`): `simplify → propagate → inline(litOK)
  → simplify`. Propagation runs *before* the inliner because the block-path
  inliner accepts literal arguments (`litOK := true`) — substituted constants
  make more call sites flat and inlinable.
* **object path** (`objectPipeline`): `simplify → inline(var-only) → propagate
  → simplify`. The object-path inliner is variable-only (`litOK := false`, the
  resolution-stable mode), so propagation runs *after* it — running first
  would turn variable arguments into literals and starve it. `Propagate`
  itself needs no restricted object mode: its soundness is proven for a
  relation closed under layout resolution (`PropagateResolve`), so the
  whole-tree object correctness theorem composes with the full pass.
-/

namespace YulEvmCompiler.Optimizer

open EvmSemantics EvmSemantics.EVM
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-- Verified production pipeline for top-level blocks, applied left-to-right.
The final `deadLits` prunes the literal bindings the earlier stages made dead. -/
def optimizerPipeline : Pass D :=
  Pass.ofList [simplify, propagate, inlineHelpersPass true, simplify, deadLits]

@[simp] theorem optimizerPipeline_run (b : Block Op) :
    (optimizerPipeline (calls := calls) (creates := creates)).run b =
      dlStmts (simplifyStmts
        (inlineHelpersBlock (calls := calls) (creates := creates) true
          ([] : FunEnv D) (propStmts [] (simplifyStmts b)).1)) := rfl

/-- Verified pipeline for object code blocks: the inliner runs in its
resolution-stable mode, before propagation; `deadLits` prunes last. -/
def objectPipeline : Pass D :=
  Pass.ofList [simplify, inlineHelpersPass false, propagate, simplify, deadLits]

@[simp] theorem objectPipeline_run (b : Block Op) :
    (objectPipeline (calls := calls) (creates := creates)).run b =
      dlStmts (simplifyStmts
        (propStmts []
          (inlineHelpersBlock (calls := calls) (creates := creates) false
            ([] : FunEnv D) (simplifyStmts b))).1) := rfl

/-- Resolution congruence for the complete five-stage object pipeline. -/
theorem resolveObjectPipelineBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L
        ((objectPipeline (calls := calls) (creates := creates)).run b)) := by
  have hs₀ := resolveSimplifyBlock_equiv (calls := calls) (creates := creates) L b
  have hi := (inlineHelpersPass (calls := calls) (creates := creates) false).sound
    (resolveForLayoutStmts L (simplifyStmts b))
  change EquivBlock D (resolveForLayoutStmts L (simplifyStmts b))
    (inlineHelpersBlock (calls := calls) (creates := creates) false ([] : FunEnv D)
      (resolveForLayoutStmts L (simplifyStmts b))) at hi
  rw [← resolve_inlineHelpersBlock_nil L (simplifyStmts b)] at hi
  have hp := resolvePropagateBlock_equiv (calls := calls) (creates := creates) L
    (inlineHelpersBlock (calls := calls) (creates := creates) false
      ([] : FunEnv D) (simplifyStmts b))
  have hs₁ := resolveSimplifyBlock_equiv (calls := calls) (creates := creates) L
    (propStmts []
      (inlineHelpersBlock (calls := calls) (creates := creates) false
        ([] : FunEnv D) (simplifyStmts b))).1
  simp only [propagateBlock] at hp
  have hd := resolveDeadLitsBlock_equiv (calls := calls) (creates := creates) L
    (simplifyStmts
      (propStmts []
        (inlineHelpersBlock (calls := calls) (creates := creates) false
          ([] : FunEnv D) (simplifyStmts b))).1)
  simpa using ((hs₀.trans (hi.trans hp)).trans hs₁).trans hd

mutual
  /-- Run the verified object pipeline on every object code block. -/
  def optimizerPipelineObject : Object Op → Object Op
    | .mk name code subs segs =>
        .mk name
          ((objectPipeline (calls := calls) (creates := creates)).run code)
          (optimizerPipelineObjects subs) segs

  /-- Run the verified object pipeline on every object in a list. -/
  def optimizerPipelineObjects : List (Object Op) → List (Object Op)
    | [] => []
    | o :: rest => optimizerPipelineObject o :: optimizerPipelineObjects rest
end

@[simp] theorem optimizerPipelineObject_codeBlock (o : Object Op) :
    (optimizerPipelineObject (calls := calls) (creates := creates) o).codeBlock =
      (objectPipeline (calls := calls) (creates := creates)).run o.codeBlock := by
  cases o
  rfl

/-- The recursively optimized artifact is covered directly by the verified
object compiler theorem. -/
theorem optimizerPipelineObject_compileObject_correct
    [model : ExternalModel] (hexternal : ExternalsRealized model)
    {o : Object Op} {L : Layout}
    (hcomp : compileObject
      (optimizerPipelineObject (calls := model.calls) (creates := model.creates) o)
        = some L)
    {V : VEnv (evmWithExternal model.calls model.creates)}
    {yst : EvmState} {out : Outcome}
    (hrun : RunResolvedObject
      (optimizerPipelineObject (calls := model.calls) (creates := model.creates) o)
      L V yst out) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (mkCode L.code) s0 → StateMatch L.initState s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst s' ∧
        ((out = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (out = .halt ∧ HaltedMatch yst s')) :=
  compileObject_correct hexternal hcomp hrun

/-- Every object's own code block is pointwise equivalent to its source block. -/
theorem optimizerPipelineObject_topEquiv (o : Object Op) :
    EquivBlock D o.codeBlock
      (optimizerPipelineObject (calls := calls) (creates := creates) o).codeBlock := by
  rw [optimizerPipelineObject_codeBlock]
  exact (objectPipeline (calls := calls) (creates := creates)).sound o.codeBlock

/-- End-to-end correctness for the recursively optimized object tree, relative
to the original object's resolved execution under the optimized layout. -/
theorem optimizerPipelineObject_correct
    [model : ExternalModel] (hexternal : ExternalsRealized model)
    {o : Object Op} {L : Layout}
    (hcomp : compileObject
      (optimizerPipelineObject (calls := model.calls) (creates := model.creates) o)
        = some L)
    {V : VEnv (evmWithExternal model.calls model.creates)}
    {yst : EvmState} {out : Outcome}
    (hrun : RunResolvedObject o L V yst out) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (mkCode L.code) s0 → StateMatch L.initState s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst s' ∧
        ((out = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (out = .halt ∧ HaltedMatch yst s')) := by
  have hb := resolveObjectPipelineBlock_equiv
    (calls := model.calls) (creates := model.creates) L o.codeBlock
  have hrun' : RunResolvedObject
      (optimizerPipelineObject (calls := model.calls) (creates := model.creates) o)
      L V yst out := by
    show Run (evmWithExternal model.calls model.creates)
      (resolveForLayoutStmts L
        (optimizerPipelineObject (calls := model.calls)
          (creates := model.creates) o).codeBlock)
      L.initState V yst out
    rw [optimizerPipelineObject_codeBlock]
    exact hb.run_iff.mp hrun
  exact compileObject_correct hexternal hcomp hrun'

end YulEvmCompiler.Optimizer
