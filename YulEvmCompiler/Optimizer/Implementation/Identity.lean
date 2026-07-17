import YulEvmCompiler.Optimizer.Spec.Pass

/-!
# YulEvmCompiler.Optimizer.Implementation.Identity

The **identity optimizer pass** — the first concrete inhabitant of
`Optimizer.Pass`, living under `Optimizer/Implementation/` alongside future real
passes. It returns its input Yul program unchanged and proves the semantics are
equivalent, so it validates that the spec (`Optimizer/Spec/Pass.lean`) is
inhabited by a concrete pass and that its obligation `Sound` is dischargeable.

Nothing here is part of the audited surface: as `Spec/Pass.lean` explains, any
value of `Pass` is sound by construction, so a reader who trusts the spec need not
read this file. Concretely, `identity` is the do-nothing pass `Pass.id`, whose
soundness is reflexivity of `EquivBlock`; a real pass replaces `run` with an
actual transformation and `sound` with a real equivalence proof, following the
same shape.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-- The **identity pass**: returns the input program unchanged. Sound by
reflexivity of semantic equivalence. It is definitionally the spec's neutral
element `Pass.id`; kept as a named implementation because it is the canonical
"first pass" and the base case of any pipeline (`Pass.ofList []`). -/
def identity : Pass D := Pass.id

@[simp] theorem identity_run (b : Block D.Op) : (identity (D := D)).run b = b := rfl

theorem identity_eq_id : (identity : Pass D) = Pass.id := rfl

/-- The identity pass changes no whole-program behavior: its `Run` results are
exactly those of the input program. -/
theorem identity_preservesRun (b : Block D.Op) (hb : WellScoped b) {st0 V' st' o} :
    Run D b st0 V' st' o ↔ Run D ((identity (D := D)).run b) st0 V' st' o :=
  (identity (D := D)).preservesRun b hb

end YulEvmCompiler.Optimizer
