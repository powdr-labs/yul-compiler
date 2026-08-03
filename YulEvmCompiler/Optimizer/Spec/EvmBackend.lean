import YulEvmCompiler.Correctness
import YulEvmCompiler.Optimizer.Spec.LocalPass
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Spec.EvmBackend

The **generalized backend contract**: what it means for *any* compilation
path from Yul to EVM bytecode to be correct — stated once, in exactly the
vocabulary of `compile_correct` (`Run`, `StateMatch`, `FrameOK`, `Steps`,
`HaltedMatch`), so that

* the classic labeled-assembly backend (`compile`) is one instance
  (`EvmBackend.classic` — its `correct` field *is* `compile_correct`);
* the SSA-CFG backend (`SsaCfg.compileViaSsa`, see
  `YulEvmCompiler/SsaCfg/`) is a second instance; and
* the verified Yul→Yul optimizer pipeline composes in front of **either**
  (`LocalPass.optimize_then_backend_correct`), generalizing
  `LocalPass.optimize_then_compile_correct` without touching it.

This is the spec change that admits intermediate dialects: an optimizer
stage no longer has to be Yul→Yul — anything that *ends* in EVM bytecode
satisfying `EvmBackend.Correct` composes with the rest of the framework.
The intermediate representation itself (its syntax, semantics, and passes)
stays out of the audited surface: the contract quantifies only over the two
pinned semantics, exactly like `compile_correct`.
-/

namespace YulEvmCompiler.Optimizer

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM (U256 EvmState Op evmWithExternal)
open YulSemantics (Outcome VEnv Run)

/-- **Backend correctness**, the statement shape of `compile_correct`
abstracted over the compilation function: for every external model whose
call/create responses are realized, every accepted program, and every source
run, the emitted bytecode simulates the run from every matching initial
state with enough gas. -/
def EvmBackend.Correct
    (compileFn : YulSemantics.Block Op → Option (List Instr)) : Prop :=
  ∀ (model : ExternalModel), ExternalsRealized model →
    ∀ {prog : YulSemantics.Block Op} {is : List Instr},
      compileFn prog = some is →
      ∀ {yst0 : EvmState}
        {V' : VEnv (evmWithExternal model.calls model.creates)}
        {yst' : EvmState} {o : Outcome},
        Run (evmWithExternal model.calls model.creates) prog yst0 V' yst' o →
        ∃ b : Nat, ∀ s0 : State,
          FrameOK (assemble is) s0 → StateMatch yst0 s0 →
          s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
          ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst' s' ∧
            ((o = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
             (o = .halt ∧ HaltedMatch yst' s'))

/-- A **verified EVM backend**: a compilation function bundled with its
correctness proof. Possessing an `EvmBackend` is possessing a verified
compiler — the same by-construction discipline as `Optimizer.LocalPass`. -/
structure EvmBackend where
  /-- The compilation function (`Option`-valued: rejection, never
  miscompilation). -/
  compile : YulSemantics.Block Op → Option (List Instr)
  /-- The proof obligation: the `compile_correct` statement shape. -/
  correct : EvmBackend.Correct compile

/-- The classic labeled-assembly backend as an `EvmBackend`: the `correct`
field is exactly `compile_correct`. -/
def EvmBackend.classic : EvmBackend where
  compile := YulEvmCompiler.compile
  correct := by
    intro model hext prog is hcomp yst0 V' yst' o hrun
    exact compile_correct hext hcomp hrun

section Compose

variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates

/-- **A sound Yul→Yul pass is safe in front of any verified backend** — the
generalization of `LocalPass.optimize_then_compile_correct` from the classic
backend to every `EvmBackend`. The proof is the same composition at the
`Run` interface: transport the source run across the pass's soundness, then
apply the backend's own correctness. -/
theorem LocalPass.optimize_then_backend_correct
    (B : EvmBackend) (P : LocalPass yulD) (hexternal : ExternalsRealized model)
    {prog : YulSemantics.Block Op} {is : List Instr}
    (hcomp : B.compile (P.run prog) = some is)
    {yst0 : EvmState} {V' : VEnv yulD} {yst' : EvmState} {o : Outcome}
    (hrun : Run yulD prog yst0 V' yst' o) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (assemble is) s0 → StateMatch yst0 s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst' s' ∧
        ((o = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (o = .halt ∧ HaltedMatch yst' s')) :=
  B.correct model hexternal hcomp (P.run_optimized hrun)

end Compose

end YulEvmCompiler.Optimizer
