import YulEvmCompiler.Correctness

/-!
# Checks

CI meta-checks for the project's headline guarantee. These are **not** part of
the `YulEvmCompiler` library; CI type-checks this file separately
(`lake env lean Checks.lean`).

Each `#guard_msgs in #print axioms …` pins the *exact* axiom set of a main
correctness theorem. If a `sorry` (which shows up as `sorryAx`) or any new
axiom ever slips into the proof — directly or through a dependency edit — the
printed message changes, `#guard_msgs` reports a mismatch, and elaboration
fails. So this file failing to compile is a hard signal that the compiler is
no longer proved correct on the terms recorded here.

The expected set is Lean's three standard classical-mathematics axioms
(`propext`, `Classical.choice`, `Quot.sound`) — the same ones Mathlib itself
depends on, and notably *not* `sorryAx` — **plus** the three
`YulEvmCompiler.Assumed.*` axioms. The latter are `ByteArray` reduction facts
about evm-semantics' total `writeBytes` / `natToBytesPadded` (needed for the
verified `MSTORE`); they are provable and slated to move upstream into
`EvmSemantics` (see `notes/writeBytes-lemmas.md`), at which point they drop
out of this list. Their presence is the honest statement "the compiler is
correct, modulo these pending-upstream byte-array lemmas". -/

/-- info: 'YulEvmCompiler.compile_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 YulEvmCompiler.Assumed.natToBytesPadded_getElem?_getD,
 YulEvmCompiler.Assumed.natToBytesPadded_size,
 YulEvmCompiler.Assumed.writeBytes_getElem?_getD] -/
#guard_msgs in
#print axioms YulEvmCompiler.compile_correct

/-- info: 'YulEvmCompiler.compile_correct_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 YulEvmCompiler.Assumed.natToBytesPadded_getElem?_getD,
 YulEvmCompiler.Assumed.natToBytesPadded_size,
 YulEvmCompiler.Assumed.writeBytes_getElem?_getD] -/
#guard_msgs in
#print axioms YulEvmCompiler.compile_correct_eval
