import Challenge.Sha256.Statement
set_option warningAsError true
/-!
# From a Yul-level obligation to the challenge statement

The point of a verified compiler in a challenge like this one: **nobody has
to reason about bytecode.** This module proves that for any program our
compiler accepts, `Challenge.Sha256.Correct` of the emitted bytecode follows
from two facts about the *Yul source* alone —

* `ComputesDigest prog` — the Yul program, run from a fresh state, halts by
  returning the digest of its calldata (the functional obligation; the real
  work, decomposed in `Challenge/README.md`);
* `AbstractsFrame code` — the canonical EVM frame is matched by some
  yul-semantics state with the same calldata and empty memory (pure
  plumbing: build the source-level state from the target one).

Everything between those and executable bytecode — code generation, the
labeled-assembly layer, the calling convention, byte layout, gas, decoding —
is already proved in this repository and is consumed here as
`compile_correct_eval`.

Both hypotheses are ordinary `Prop`s, so this module carries no unfinished
proof of its own; what is open is *inhabiting* them, which is the challenge.
-/

namespace Challenge.Sha256

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics (Block Run VEnv)
open YulSemantics.EVM (EvmState Op evmWithExternal ExternalCalls ExternalCreates)
open YulEvmCompiler

/-- The closed-world model: the reference implementation makes no external
calls and creates no contracts, so the open-world relations are empty and
`ExternalsRealized.none` discharges the compiler theorem's side condition. -/
@[reducible] def localModel : ExternalModel :=
  { calls := ExternalCalls.none, creates := ExternalCreates.none }

/-- The gas-free source dialect the obligation is stated against. -/
abbrev localDialect := evmWithExternal ExternalCalls.none ExternalCreates.none

/-- **Obligation A** (plumbing). Every canonical frame for `code` is matched
by a yul-semantics state that has the same calldata, empty memory, and has
not halted. One state serves every gas level, because `StateMatch` does not
mention gas. -/
def AbstractsFrame (code : ByteArray) : Prop :=
  ∀ calldata : ByteArray, ∃ yst : EvmState,
    (∀ g : Nat, StateMatch yst (frame code calldata g)) ∧
    yst.memory = (fun _ => 0) ∧
    yst.env.calldata = calldata.toList ∧
    yst.halted = none

/-- **Obligation Y** (the functional obligation). From any fresh
yul-semantics state, `prog` halts via `return` with exactly the SHA-256
digest of the state's calldata.

This is the whole mathematical content of a submission: it says the Yul
program *is* SHA-256, against the same `Crypto.Sha256.hash` the `0x02`
precompile computes. -/
def ComputesDigest (prog : Block Op) : Prop :=
  ∀ yst : EvmState, yst.memory = (fun _ => 0) → yst.halted = none →
    ∃ (V : VEnv localDialect) (yst' : EvmState),
      Run localDialect prog yst V yst' .halt ∧
        yst'.halted = some (.ret, digestOf yst.env.calldata)

/-- **The reduction.** A compiler-accepted Yul program that computes the
digest yields bytecode satisfying the challenge statement. No step of this
proof mentions an opcode: the bytecode-level work is `compile_correct_eval`.

`hsize` is the trivial code-size side condition (`FrameOK.codeSmall`); for a
concrete submission it is `by decide` on the emitted length. -/
theorem correct_of_computesDigest {prog : Block Op} {is : List Instr}
    (hcomp : compile prog = some is)
    (hsize : (assemble is).size < 2 ^ 256)
    (habs : AbstractsFrame (assemble is))
    (hyul : ComputesDigest prog) :
    Correct (assemble is) := by
  intro calldata
  obtain ⟨yst, hmatch, hmem, hcd, hhalted⟩ := habs calldata
  obtain ⟨V, yst', hrun, hres⟩ := hyul yst hmem hhalted
  obtain ⟨b, H⟩ :=
    compile_correct_eval (model := localModel) ExternalsRealized.none hcomp hrun
  refine ⟨b, fun g hg => ?_⟩
  obtain ⟨-, hhalt⟩ :=
    H (frame (assemble is) calldata g) (frame_frameOK hsize) (hmatch g)
      (frame_pc _ _ _) (frame_stack _ _ _) (by rw [frame_gas]; exact hg)
  obtain ⟨hk, hyk, heval⟩ := hhalt rfl
  rw [hres] at hyk
  cases hyk
  simpa [resultOf, digestOf, hcd, mkCode_toList, spec] using heval

end Challenge.Sha256
