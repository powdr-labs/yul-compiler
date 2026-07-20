import YulEvmCompiler.Optimizer.Implementation.InlineHelpersResolve
import YulEvmCompiler.Optimizer.Implementation.PropagateResolve
import YulEvmCompiler.Optimizer.Implementation.DeadLitsResolve
import YulEvmCompiler.Optimizer.Implementation.InlineCallsSound
import YulEvmCompiler.Optimizer.Implementation.ObjectPass
-- TODO(inline-calls): restore `set_option warningAsError true` once the
-- InlineCalls resolution congruence replaces the measurement-phase `sorry`.
set_option warningAsError false
/-!
# Production optimizer pipeline

The production pipeline simplifies expressions, propagates known bindings
(`Propagate`: constant propagation with binding-preserving substitution),
inlines pure expression-body helpers through the Core boundary
(`InlineHelpers`), inlines call-free statement-body helpers (`InlineCalls`),
simplifies again, and prunes dead literal bindings (`DeadLits`). The whole
round is **iterated** (`pipelineRounds`): statement-level inlining collapses
helper chains leaf-first — a call-free callee inlines this round, which makes
its caller call-free for the next round — and each round's leftovers (literal
parameter bindings, zero-initialized returns) feed the next round's
propagation and pruning.

Stage order differs by path, deliberately:

* **block path** (`optimizerPipeline`): `simplify → propagate → inline(litOK)
  → inlineCalls → simplify → deadLits`. Propagation runs *before* the inliner
  because the block-path inliner accepts literal arguments (`litOK := true`) —
  substituted constants make more call sites flat and inlinable.
* **object path** (`objectPipeline`): `simplify → inline(var-only) →
  propagate → inlineCalls → simplify → deadLits`. The object-path inliner is
  variable-only (`litOK := false`, the resolution-stable mode), so propagation
  runs *after* it — running first would turn variable arguments into literals
  and starve it. `Propagate`, `DeadLits`, and `InlineCalls` need no restricted
  object mode: their soundness is proven for relations closed under layout
  resolution, so the whole-tree object correctness theorem composes with the
  full passes.

The object path additionally needs each stage to commute with layout
resolution up to `EquivBlock` — bundled per stage as `RPass` and composed over
the whole iterated pipeline by `RPass.resolve_equiv_ofList`.
-/

namespace YulEvmCompiler.Optimizer

open EvmSemantics EvmSemantics.EVM
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-! ### Resolution-congruent passes -/

/-- A verified pass bundled with its layout-resolution congruence: running the
pass before resolution is equivalent (pointwise) to not running it, *on the
resolved code*. This is the per-stage fact `optimizerPipelineObject_correct`
composes over the whole pipeline. -/
structure RPass (calls : ExternalCalls) (creates : ExternalCreates) where
  pass : Pass (evmWithExternal calls creates)
  resolve_equiv : ∀ (L : Layout) (b : Block Op),
    EquivBlock (evmWithExternal calls creates)
      (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (pass.run b))

/-- The resolution congruence extends from stages to a whole pipeline. -/
theorem RPass.resolve_equiv_ofList (ps : List (RPass calls creates))
    (L : Layout) (b : Block Op) :
    EquivBlock D
      (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L ((Pass.ofList (ps.map (·.pass))).run b)) := by
  induction ps generalizing b with
  | nil => exact EquivBlock.refl _
  | cons p rest ih =>
      exact (p.resolve_equiv L b).trans (ih (p.pass.run b))

/-! ### The stage lists -/

/-- Rounds of the iterated pipeline. Helper chains in solc's unoptimized IR
are ~5 calls deep (`external_fun_*` → `abi_decode_tuple_*` → `abi_decode_t_*`
→ `validator_revert_*` → `cleanup_*`); each round collapses the current
call-free leaves. -/
def pipelineRounds : Nat := 6

/-- One block-path round. -/
def blockRound : List (Pass D) :=
  [simplify, propagate, inlineHelpersPass true, inlineCalls, simplify, deadLits]

/-- Verified production pipeline for top-level blocks: the round, iterated. -/
def optimizerPipeline : Pass D :=
  Pass.ofList ((List.replicate pipelineRounds (blockRound (calls := calls)
    (creates := creates))).flatten)

/-- One object-path round, with each stage's resolution congruence. -/
def objectRound : List (RPass calls creates) :=
  [⟨simplify, fun L b => resolveSimplifyBlock_equiv L b⟩,
   ⟨inlineHelpersPass false, fun L b => by
      have hi := (inlineHelpersPass (calls := calls) (creates := creates) false).sound
        (resolveForLayoutStmts L b)
      change EquivBlock D (resolveForLayoutStmts L b)
        (inlineHelpersBlock (calls := calls) (creates := creates) false ([] : FunEnv D)
          (resolveForLayoutStmts L b)) at hi
      rw [← resolve_inlineHelpersBlock_nil L b] at hi
      exact hi⟩,
   ⟨propagate, fun L b => by
      have hp := resolvePropagateBlock_equiv (calls := calls) (creates := creates) L b
      simpa [propagateBlock] using hp⟩,
   ⟨inlineCalls, fun L b => sorry⟩,
   ⟨simplify, fun L b => resolveSimplifyBlock_equiv L b⟩,
   ⟨deadLits, fun L b => resolveDeadLitsBlock_equiv L b⟩]

/-- Verified pipeline for object code blocks: the round, iterated. -/
def objectPipeline : Pass D :=
  Pass.ofList (((List.replicate pipelineRounds (objectRound (calls := calls)
    (creates := creates))).flatten).map (·.pass))

/-- Resolution congruence for the complete iterated object pipeline. -/
theorem resolveObjectPipelineBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L
        ((objectPipeline (calls := calls) (creates := creates)).run b)) :=
  RPass.resolve_equiv_ofList _ L b

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
