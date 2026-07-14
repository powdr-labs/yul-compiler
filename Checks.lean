import YulEvmCompiler.Correctness
import YulEvmCompiler.ObjectCompile
import YulParser

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

The expected set is exactly Lean's three standard classical-mathematics axioms
(`propext`, `Classical.choice`, `Quot.sound`) — the same ones Mathlib itself
depends on, and notably *not* `sorryAx`. There are no project-specific axioms:
the `ByteArray` reduction facts about evm-semantics' `writeBytes` and
`natToBytesPadded` that `MSTORE` needs are all genuine theorems — `writeBytes`
upstream as `EvmSemantics.MachineState.writeBytes_getElem?_getD`, and the two
`natToBytesPadded` facts proved locally in `YulEvmCompiler.BytesLemmas`. So the
footprint below is the strongest honest statement: the compiler is correct
modulo only the standard classical axioms. -/

/-- info: 'YulEvmCompiler.compile_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms YulEvmCompiler.compile_correct

/-- info: 'YulEvmCompiler.compile_correct_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms YulEvmCompiler.compile_correct_eval

/-- info: 'YulEvmCompiler.compile_correct_withPayload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms YulEvmCompiler.compile_correct_withPayload

/-- info: 'YulEvmCompiler.compileObject_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms YulEvmCompiler.compileObject_correct

/-- info: 'YulEvmCompiler.compileObject_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms YulEvmCompiler.compileObject_consistent

/-- info: 'YulEvmCompiler.compiled_constructor_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms YulEvmCompiler.compiled_constructor_returns

/-- info: 'YulParser.parse_canon_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms YulParser.parse_canon_block

/-- info: 'YulParser.parse_canon_obj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms YulParser.parse_canon_obj
