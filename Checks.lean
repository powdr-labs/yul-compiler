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
no longer unconditionally proved correct.

The expected set is Lean's three standard classical-mathematics axioms
(`propext`, `Classical.choice`, `Quot.sound`) — the same ones Mathlib itself
depends on, and notably *not* `sorryAx`. -/

/-- info: 'YulEvmCompiler.compile_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms YulEvmCompiler.compile_correct

/-- info: 'YulEvmCompiler.compile_correct_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms YulEvmCompiler.compile_correct_eval
