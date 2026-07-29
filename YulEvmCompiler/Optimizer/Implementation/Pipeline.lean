import YulEvmCompiler.Optimizer.Implementation.InlineHelpersResolve
import YulEvmCompiler.Optimizer.Implementation.PropagateResolve
import YulEvmCompiler.Optimizer.Implementation.DeadLitsResolve
import YulEvmCompiler.Optimizer.Implementation.InlineCallsResolve
import YulEvmCompiler.Optimizer.Implementation.DeadPureResolve
import YulEvmCompiler.Optimizer.Implementation.DeadResultsResolve
import YulEvmCompiler.Optimizer.Implementation.FreshenCallsResolve
import YulEvmCompiler.Optimizer.Implementation.HoistCallsResolve
import YulEvmCompiler.Optimizer.Implementation.StorageForwardResolve
import YulEvmCompiler.Optimizer.Implementation.CoalesceCopiesResolve
import YulEvmCompiler.Optimizer.Implementation.RejoinPairs
import YulEvmCompiler.Optimizer.Implementation.DispatchTree
import YulEvmCompiler.Optimizer.Implementation.StructurePasses
import YulEvmCompiler.Optimizer.Implementation.ObjectPass
import YulEvmCompiler.Optimizer.Implementation.Normalization.Normalize
set_option warningAsError true
/-!
# Production optimizer pipeline

The production pipeline simplifies expressions (constant folding, neutral
identities including the open-operand forms), propagates known bindings
(`Propagate`: constant propagation plus depth-gated copy propagation, both
binding-preserving), inlines pure expression-body helpers through the Core
boundary (`InlineHelpers`), hoists direct unary nested calls and freshens
result sites before inlining call-free statement-body helpers (`HoistCalls`,
`FreshenCalls`, `InlineCalls`), forwards cheap values written to literal storage
slots through later loads (`StorageForward`), simplifies again, prunes dead pure
bindings and self-assignments (`DeadPure`, subsuming the earlier `DeadLits`),
and removes
unused result slots together with adjacent total, state-preserving readback
regions (`DeadResults`). The whole round is **iterated** (`pipelineRounds`): statement-level inlining collapses
helper chains leaf-first — a call-free callee inlines this round, which makes
its caller call-free for the next round — and each round's leftovers
(parameter/result copy bindings, zero-initialized returns) feed the next
round's propagation and pruning, which in turn shrink helper bodies back
under the inlining guards.

Stage order differs by path, deliberately:

* **block path** (`optimizerPipeline`): `simplify → propagate → inline(litOK)
  → hoistCalls → freshenCalls → inlineCalls → storageForward → simplify
  → deadPure → deadResults`.
  Propagation runs *before* the inliner
  because the block-path inliner accepts literal arguments (`litOK := true`) —
  substituted constants make more call sites flat and inlinable.
* **object path** (`objectPipeline`): `simplify → inline(var-only) →
  propagate → hoistCalls → freshenCalls → inlineCalls → storageForward →
  simplify → deadPure → deadResults`. The object-path inliner is
  variable-only (`litOK := false`, the resolution-stable mode), so propagation
  runs *after* it — running first would turn variable arguments into literals
  and starve it. `Propagate`, `DeadPure`, and `InlineCalls` need no restricted
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
  pass : LocalPass (evmWithExternal calls creates)
  resolve_equiv : ∀ (L : Layout) (b : Block Op),
    EquivBlock (evmWithExternal calls creates)
      (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (pass.run b))

/-- The resolution congruence extends from stages to a whole pipeline. -/
theorem RPass.resolve_equiv_ofList (ps : List (RPass calls creates))
    (L : Layout) (b : Block Op) :
    EquivBlock D
      (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L ((LocalPass.ofList (ps.map (·.pass))).run b)) := by
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

/-- One block-path round. `coalesceCopies` collapses the statement inliner's
adjacent copy chains (`let a := p; let b := a; …`) right before the dead-code
stages: the merged binders shrink helper bodies below the `liveMax` gates that
pace copy propagation and `InlineCalls`, and never deepen a stack read.
`deadResults` removes at most one dead result region per statement sequence
per invocation, and the scoped fact export turns whole groups of adjacent
readback regions dead within a single round — so the stage runs three times,
draining up to three regions per sequence per round instead of spending a
full round on each. -/
def blockRound : List (LocalPass D) :=
  [simplify, dispatchTree, propagate, inlineHelpersPass true, hoistCalls, freshenCalls, inlineCalls,
   flatten, fuseDeclAssign,
   storageForward, simplify, coalesceCopies, reuseValues, rejoinPairs, deadPure,
   deadResults, deadResults, deadResults, pruneDefs]

/-- The block-path round without `rejoinPairs`. Rejoining merges the bindings
the smart stack layout would otherwise re-slot, which can defeat the layout
rescue on stack-frontier objects (measured: `PoolLiquidity`); the compile
fallback chain therefore also retries the full pipeline without it. -/
def blockRoundNoRejoin : List (LocalPass D) :=
  [simplify, dispatchTree, propagate, inlineHelpersPass true, hoistCalls, freshenCalls, inlineCalls,
   flatten, fuseDeclAssign,
   storageForward, simplify, coalesceCopies, reuseValues, deadPure,
   deadResults, deadResults, deadResults, pruneDefs]

/-- Verified block pipeline at an explicit round count. Iterated inlining can
push a caller's live locals past the backend's `DUP16`/`SWAP16` reach; fewer
rounds keep frames shallower, so `compileSource` retries a **light**
(one-round) pipeline before giving up on optimization entirely. -/
def optimizerPipelineRounds (n : Nat) : LocalPass D :=
  LocalPass.ofList ((List.replicate n (blockRound (calls := calls)
    (creates := creates))).flatten)

/-- Verified production pipeline for top-level blocks: the round, iterated. -/
def optimizerPipeline : LocalPass D :=
  optimizerPipelineRounds pipelineRounds

/-- The light (one-round) block pipeline, the middle compile fallback. -/
def optimizerPipelineLight : LocalPass D :=
  optimizerPipelineRounds 1

/-- The full block pipeline without `rejoinPairs` (see `blockRoundNoRejoin`). -/
def optimizerPipelineNoRejoin : LocalPass D :=
  LocalPass.ofList ((List.replicate pipelineRounds (blockRoundNoRejoin (calls := calls)
    (creates := creates))).flatten)

/-- Object-path helper inlining with the *literal-admitting* classification,
guarded by whole-block layout-freedom on input **and** output (the
`Flatten`/`FuseDeclAssign`/`ReuseValues` recipe): when the guard holds,
resolution is the identity on both sides and the congruence is the pass's own
soundness. When it fails — a constructor block carrying `dataoffset`/
`datasize`/string hooks — fall back to the resolution-stable
`litOK := false` classification with its syntactic commutation, exactly the
previous behavior. Deployed-object runtime code is essentially always
layout-free, so the cleanup-mask helpers (`and(x, 0xffff…)` and friends) that
`litOK := false` excludes finally inline on the object path. -/
def inlineHelpersObjBlock (b : Block Op) : Block Op :=
  if storageLayoutFreeStmts b then
    if storageLayoutFreeStmts (inlineHelpersBlock (calls := calls)
        (creates := creates) true ([] : FunEnv D) b) then
      inlineHelpersBlock (calls := calls) (creates := creates) true
        ([] : FunEnv D) b
    else inlineHelpersBlock (calls := calls) (creates := creates) false
      ([] : FunEnv D) b
  else inlineHelpersBlock (calls := calls) (creates := creates) false
    ([] : FunEnv D) b

/-- The guarded object-path helper inliner is a verified pass: every branch
returns `inlineHelpersBlock` at some `litOK`, whose soundness is
classification-mode-independent. -/
def inlineHelpersObj : LocalPass D where
  run := inlineHelpersObjBlock
  sound b := by
    unfold inlineHelpersObjBlock
    split
    · split
      · exact inlineHelpersBlock_equiv b
      · exact inlineHelpersBlock_equiv b
    · exact inlineHelpersBlock_equiv b

/-- Resolution congruence for the guarded object-path helper inliner. -/
theorem resolveInlineHelpersObjBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (inlineHelpersObjBlock (calls := calls)
        (creates := creates) b)) := by
  have hfalse : EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (inlineHelpersBlock (calls := calls)
        (creates := creates) false ([] : FunEnv D) b)) := by
    have hi := (inlineHelpersPass (calls := calls) (creates := creates) false).sound
      (resolveForLayoutStmts L b)
    change EquivBlock D (resolveForLayoutStmts L b)
      (inlineHelpersBlock (calls := calls) (creates := creates) false ([] : FunEnv D)
        (resolveForLayoutStmts L b)) at hi
    rw [← resolve_inlineHelpersBlock_nil L b] at hi
    exact hi
  unfold inlineHelpersObjBlock
  split
  · split
    · next h1 h2 =>
        rw [resolve_storageLayoutFreeStmts L b h1,
          resolve_storageLayoutFreeStmts L _ h2]
        exact inlineHelpersBlock_equiv b
    · exact hfalse
  · exact hfalse

/-- One object-path round, with each stage's resolution congruence. -/
def objectRound : List (RPass calls creates) :=
  [⟨simplify, fun L b => resolveSimplifyBlock_equiv L b⟩,
   ⟨dispatchTree, fun L b => resolveDispatchTreeBlock_equiv L b⟩,
   ⟨inlineHelpersObj, fun L b => resolveInlineHelpersObjBlock_equiv L b⟩,
   ⟨propagate, fun L b => by
      have hp := resolvePropagateBlock_equiv (calls := calls) (creates := creates) L b
      simpa [propagateBlock] using hp⟩,
   ⟨hoistCalls, fun L b => resolveHoistCallsBlock_equiv L b⟩,
   ⟨freshenCalls, fun L b => resolveFreshenCallsBlock_equiv L b⟩,
   ⟨inlineCalls, fun L b => resolveInlineCallsBlock_equiv L b⟩,
   ⟨flatten, fun L b => resolveFlattenBlock_equiv L b⟩,
   ⟨fuseDeclAssign, fun L b => resolveFuseDeclAssignBlock_equiv L b⟩,
   ⟨storageForward, fun L b => resolveStorageForwardBlock_equiv L b⟩,
   ⟨simplify, fun L b => resolveSimplifyBlock_equiv L b⟩,
   ⟨coalesceCopies, fun L b => resolveCoalesceCopiesBlock_equiv L b⟩,
   ⟨reuseValues, fun L b => resolveReuseValuesBlock_equiv L b⟩,
   ⟨rejoinPairs, fun L b => resolveRejoinPairsBlock_equiv L b⟩,
   ⟨deadPure, fun L b => resolveDeadPureBlock_equiv L b⟩,
   ⟨deadResults, fun L b => resolveDeadResultsBlock_equiv L b⟩,
   ⟨deadResults, fun L b => resolveDeadResultsBlock_equiv L b⟩,
   ⟨deadResults, fun L b => resolveDeadResultsBlock_equiv L b⟩,
   ⟨pruneDefs, fun L b => resolvePruneDefsBlock_equiv L b⟩]

/-- The object-path round without `rejoinPairs` (see `blockRoundNoRejoin`). -/
def objectRoundNoRejoin : List (RPass calls creates) :=
  [⟨simplify, fun L b => resolveSimplifyBlock_equiv L b⟩,
   ⟨dispatchTree, fun L b => resolveDispatchTreeBlock_equiv L b⟩,
   ⟨inlineHelpersObj, fun L b => resolveInlineHelpersObjBlock_equiv L b⟩,
   ⟨propagate, fun L b => by
      have hp := resolvePropagateBlock_equiv (calls := calls) (creates := creates) L b
      simpa [propagateBlock] using hp⟩,
   ⟨hoistCalls, fun L b => resolveHoistCallsBlock_equiv L b⟩,
   ⟨freshenCalls, fun L b => resolveFreshenCallsBlock_equiv L b⟩,
   ⟨inlineCalls, fun L b => resolveInlineCallsBlock_equiv L b⟩,
   ⟨flatten, fun L b => resolveFlattenBlock_equiv L b⟩,
   ⟨fuseDeclAssign, fun L b => resolveFuseDeclAssignBlock_equiv L b⟩,
   ⟨storageForward, fun L b => resolveStorageForwardBlock_equiv L b⟩,
   ⟨simplify, fun L b => resolveSimplifyBlock_equiv L b⟩,
   ⟨coalesceCopies, fun L b => resolveCoalesceCopiesBlock_equiv L b⟩,
   ⟨reuseValues, fun L b => resolveReuseValuesBlock_equiv L b⟩,
   ⟨deadPure, fun L b => resolveDeadPureBlock_equiv L b⟩,
   ⟨deadResults, fun L b => resolveDeadResultsBlock_equiv L b⟩,
   ⟨deadResults, fun L b => resolveDeadResultsBlock_equiv L b⟩,
   ⟨deadResults, fun L b => resolveDeadResultsBlock_equiv L b⟩,
   ⟨pruneDefs, fun L b => resolvePruneDefsBlock_equiv L b⟩]

/-- Verified object pipeline at an explicit round count (see
`optimizerPipelineRounds` for why the count varies). -/
def objectPipelineRounds (n : Nat) : LocalPass D :=
  LocalPass.ofList (((List.replicate n (objectRound (calls := calls)
    (creates := creates))).flatten).map (·.pass))

/-- Verified pipeline for object code blocks: the round, iterated. -/
def objectPipeline : LocalPass D :=
  objectPipelineRounds pipelineRounds

/-- Resolution congruence for the iterated object pipeline, any round count. -/
theorem resolveObjectPipelineRoundsBlock_equiv (n : Nat) (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L
        ((objectPipelineRounds (calls := calls) (creates := creates) n).run b)) :=
  RPass.resolve_equiv_ofList _ L b

/-- Resolution congruence for the complete iterated object pipeline. -/
theorem resolveObjectPipelineBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L
        ((objectPipeline (calls := calls) (creates := creates)).run b)) :=
  RPass.resolve_equiv_ofList _ L b

mutual
  /-- Run the verified object pipeline (at a round count) on every object
  code block. -/
  def optimizerPipelineObjectRounds (n : Nat) : Object Op → Object Op
    | .mk name code subs segs =>
        .mk name
          ((objectPipelineRounds (calls := calls) (creates := creates) n).run code)
          (optimizerPipelineObjectsRounds n subs) segs

  /-- Run the verified object pipeline on every object in a list. -/
  def optimizerPipelineObjectsRounds (n : Nat) : List (Object Op) → List (Object Op)
    | [] => []
    | o :: rest =>
        optimizerPipelineObjectRounds n o :: optimizerPipelineObjectsRounds n rest
end

/-- Run the verified object pipeline on every object code block. -/
def optimizerPipelineObject : Object Op → Object Op :=
  optimizerPipelineObjectRounds (calls := calls) (creates := creates)
    pipelineRounds

/-- The light (one-round) whole-tree optimizer, the middle compile fallback. -/
def optimizerPipelineObjectLight : Object Op → Object Op :=
  optimizerPipelineObjectRounds (calls := calls) (creates := creates) 1

/-- The full object pipeline without `rejoinPairs`, as a stage list. -/
def objectPipelineNoRejoin : LocalPass D :=
  LocalPass.ofList (((List.replicate pipelineRounds (objectRoundNoRejoin (calls := calls)
    (creates := creates))).flatten).map (·.pass))

/-- Resolution congruence for the no-rejoin object pipeline. -/
theorem resolveObjectPipelineNoRejoinBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L
        ((objectPipelineNoRejoin (calls := calls) (creates := creates)).run b)) :=
  RPass.resolve_equiv_ofList _ L b

mutual
  /-- Run the no-rejoin object pipeline on every object code block. -/
  def optimizerPipelineObjectNoRejoin : Object Op → Object Op
    | .mk name code subs segs =>
        .mk name
          ((objectPipelineNoRejoin (calls := calls) (creates := creates)).run code)
          (optimizerPipelineObjectsNoRejoin subs) segs

  def optimizerPipelineObjectsNoRejoin : List (Object Op) → List (Object Op)
    | [] => []
    | o :: rest =>
        optimizerPipelineObjectNoRejoin o :: optimizerPipelineObjectsNoRejoin rest
end

set_option maxRecDepth 4096 in
@[simp] theorem optimizerPipelineObjectRounds_codeBlock (n : Nat) (o : Object Op) :
    (optimizerPipelineObjectRounds (calls := calls) (creates := creates) n o).codeBlock =
      (objectPipelineRounds (calls := calls) (creates := creates) n).run o.codeBlock := by
  cases o
  rfl

set_option maxRecDepth 4096 in
@[simp] theorem optimizerPipelineObject_codeBlock (o : Object Op) :
    (optimizerPipelineObject (calls := calls) (creates := creates) o).codeBlock =
      (objectPipeline (calls := calls) (creates := creates)).run o.codeBlock := by
  cases o
  rfl

/-- The recursively optimized artifact (any round count) is covered directly
by the verified object compiler theorem. -/
theorem optimizerPipelineObjectRounds_compileObject_correct
    [model : ExternalModel] (hexternal : ExternalsRealized model) (n : Nat)
    {o : Object Op} {L : Layout}
    (hcomp : compileObject
      (optimizerPipelineObjectRounds (calls := model.calls) (creates := model.creates) n o)
        = some L)
    {V : VEnv (evmWithExternal model.calls model.creates)}
    {yst : EvmState} {out : Outcome}
    (hrun : RunResolvedObject
      (optimizerPipelineObjectRounds (calls := model.calls) (creates := model.creates) n o)
      L V yst out) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (mkCode L.code) s0 → StateMatch L.initState s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst s' ∧
        ((out = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (out = .halt ∧ HaltedMatch yst s')) :=
  compileObject_correct hexternal hcomp hrun

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

/-- Every object's own code block is pointwise equivalent to its source block
(any round count). -/
theorem optimizerPipelineObjectRounds_topEquiv (n : Nat) (o : Object Op) :
    EquivBlock D o.codeBlock
      (optimizerPipelineObjectRounds (calls := calls) (creates := creates) n o).codeBlock := by
  rw [optimizerPipelineObjectRounds_codeBlock]
  exact (objectPipelineRounds (calls := calls) (creates := creates) n).sound o.codeBlock

/-- Every object's own code block is pointwise equivalent to its source block. -/
theorem optimizerPipelineObject_topEquiv (o : Object Op) :
    EquivBlock D o.codeBlock
      (optimizerPipelineObject (calls := calls) (creates := creates) o).codeBlock :=
  optimizerPipelineObjectRounds_topEquiv pipelineRounds o

/-- End-to-end correctness for the recursively optimized object tree (any
round count), relative to the original object's resolved execution under the
optimized layout. -/
theorem optimizerPipelineObjectRounds_correct
    [model : ExternalModel] (hexternal : ExternalsRealized model) (n : Nat)
    {o : Object Op} {L : Layout}
    (hcomp : compileObject
      (optimizerPipelineObjectRounds (calls := model.calls) (creates := model.creates) n o)
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
  have hb := resolveObjectPipelineRoundsBlock_equiv
    (calls := model.calls) (creates := model.creates) n L o.codeBlock
  have hrun' : RunResolvedObject
      (optimizerPipelineObjectRounds (calls := model.calls) (creates := model.creates) n o)
      L V yst out := by
    show Run (evmWithExternal model.calls model.creates)
      (resolveForLayoutStmts L
        (optimizerPipelineObjectRounds (calls := model.calls)
          (creates := model.creates) n o).codeBlock)
      L.initState V yst out
    rw [optimizerPipelineObjectRounds_codeBlock]
    exact hb.run_iff.mp hrun
  exact compileObject_correct hexternal hcomp hrun'

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
         (out = .halt ∧ HaltedMatch yst s')) :=
  optimizerPipelineObjectRounds_correct hexternal pipelineRounds hcomp hrun

/-! ### Normalization as the first pipeline step

`compileSource` runs the full normalization front-end (`Normalize.normalize` /
`Normalize.normalizeObject`, see `Normalization/Normalize.lean`) — disambiguate
every declared name, then hoist every function definition to the root —
**before** the optimizer pipeline. Both steps guard on a decidable check
(`Disambiguate/Decide.lean`'s `sourceValidB` for disambiguation, `hoistGuard` for
hoisting) and are the identity off their domains, so normalization is now an
**unconditionally**-sound `GlobalPass`: the composed guarantees below carry no
`SourceValid` hypothesis. On any valid source program (which the parser's
validator guarantees) both guards fire, so normalization is active, not a
no-op. -/

/-- **Normalize-then-optimize preserves whole-program behaviour** (block path),
for **every** block: normalization is now an unconditionally-sound guarded pass
(`Normalize.normalize_runEquivBlock`), so no `SourceValid` hypothesis survives. -/
theorem normalize_optimizerPipelineRounds_runEquiv (n : Nat) (b : Block Op) :
    RunEquivBlock D b
      ((optimizerPipelineRounds (calls := calls) (creates := creates) n).run
        (@Normalize.normalize (evmWithExternal calls creates) b)) :=
  (@Normalize.normalize_runEquivBlock (evmWithExternal calls creates) _ b).trans
    (RunEquivBlock.of_equivBlock
      ((optimizerPipelineRounds (calls := calls) (creates := creates) n).sound
        (@Normalize.normalize (evmWithExternal calls creates) b)))

/-- **Normalize-then-optimize preserves whole-program behaviour** (object path,
at the top code block — the `RunObject`/`RunResolvedObject` interface), for
**every** object tree. -/
theorem normalize_optimizerPipelineObjectRounds_topRunEquiv (n : Nat) (o : Object Op) :
    RunEquivBlock D o.codeBlock
      (optimizerPipelineObjectRounds (calls := calls) (creates := creates) n
        (@Normalize.normalizeObject (evmWithExternal calls creates) _ o)).codeBlock :=
  (@Normalize.normalizeObject_topRunEquiv (evmWithExternal calls creates) _ o).trans
    (RunEquivBlock.of_equivBlock
      (optimizerPipelineObjectRounds_topEquiv n (@Normalize.normalizeObject (evmWithExternal calls creates) _ o)))

end YulEvmCompiler.Optimizer
