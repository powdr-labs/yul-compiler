import YulEvmCompiler.Optimizer.Implementation.StackLayoutSound
import YulEvmCompiler.ObjectCompile
set_option warningAsError true
/-!
# Smart stack layout on object trees

`stackLayoutObject` applies the verified block pass independently to every
deploy/runtime code block while preserving names, child structure, and data.
This module records both sides of the object guarantee: each transformed block
is pointwise equivalent to its source, and an emitted transformed artifact is
covered by the ordinary full object-execution simulation.
-/

namespace YulEvmCompiler.Optimizer

open EvmSemantics EvmSemantics.EVM
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

@[simp] theorem stackLayoutObject_codeBlock (o : Object Op) :
    (stackLayoutObject o).codeBlock = stackLayoutBlock o.codeBlock := by
  cases o
  rfl

/-- Every code block rewritten by `stackLayoutObject` is covered by the strong
pointwise `Pass` equivalence. -/
theorem stackLayoutObject_topEquiv (o : Object Op) :
    EquivBlock D o.codeBlock (stackLayoutObject o).codeBlock := by
  rw [stackLayoutObject_codeBlock]
  exact (stackLayout (calls := calls) (creates := creates)).sound o.codeBlock

/-- The recursively laid-out artifact is covered by the full object compiler
simulation, including emitted layout, payloads, and target state. -/
theorem stackLayoutObject_compileObject_correct
    [model : ExternalModel] (hexternal : ExternalsRealized model)
    {o : Object Op} {L : Layout}
    (hcomp : compileObject (stackLayoutObject o) = some L)
    {V : VEnv (evmWithExternal model.calls model.creates)}
    {yst : EvmState} {out : Outcome}
    (hrun : RunResolvedObject (stackLayoutObject o) L V yst out) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (mkCode L.code) s0 → StateMatch L.initState s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst s' ∧
        ((out = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (out = .halt ∧ HaltedMatch yst s')) :=
  compileObject_correct hexternal hcomp hrun

end YulEvmCompiler.Optimizer
