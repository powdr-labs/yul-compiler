import YulEvmCompiler.Correctness
import YulEvmCompiler.Optimizer.Spec.Pass
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Backend

The payoff of the optimizer specification: a **sound pass composes with the
verified backend**. `Pass.optimize_then_compile_correct` shows that compiling the
*optimized* program with the (proved) Yul→EVM compiler correctly simulates the
*original* program's Yul semantics — so running any `Optimizer.Pass` in front of
`compile` never invalidates `compile_correct`.

The proof is exactly the composition `AGENTS.md` prescribes for a source-to-source
pass: transport the source run across the pass's soundness
(`Pass.run_optimized`), then feed it to `compile_correct`. No backend proof is
re-opened; the optimizer's obligation and the compiler's theorem meet at the
`YulSemantics.Run` interface.
-/

namespace YulEvmCompiler.Optimizer

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM (U256 EvmState Op evmWithExternal)
open YulSemantics (Outcome VEnv Run Block)

variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates

/-- **A sound optimizer pass is safe in front of the verified backend.** If `P`
is any verified `Pass`, the compiler accepts the optimized program
`P.run prog`, and the Yul semantics runs the *original* `prog` from `yst0` to
`yst'` with outcome `o`, then the bytecode compiled from `P.run prog` reproduces
that behavior on the EVM: from every matching initial state with enough gas it
reaches a final state matching `yst'`, with the same halt/return discipline as
`compile_correct`.

This is `compile_correct` precomposed with the pass's semantics preservation —
the end-to-end statement that optimizing before compiling is correct. -/
theorem Pass.optimize_then_compile_correct
    (P : Pass yulD) (hexternal : ExternalsRealized model)
    {prog : Block Op} {is : List Instr}
    (hcomp : compile (P.run prog) = some is)
    {yst0 : EvmState} {V' : VEnv yulD} {yst' : EvmState} {o : Outcome}
    (hrun : Run yulD prog yst0 V' yst' o) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (assemble is) s0 → StateMatch yst0 s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst' s' ∧
        ((o = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (o = .halt ∧ HaltedMatch yst' s')) :=
  compile_correct hexternal hcomp (P.run_optimized hrun)

end YulEvmCompiler.Optimizer
