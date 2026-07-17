import YulSemantics.Equiv

/-!
# YulEvmCompiler.Optimizer.Pass

The specification a **Yul→Yul optimizer pass** must satisfy to be admitted in
front of the verified backend: a total source-to-source transformation together
with a machine-checked proof that it preserves the program's meaning. This is
the foundation the repository's future optimization research stands on — every
concrete pass is a value of the `Pass` structure defined here, so *possessing*
one is possessing a verified optimizer.

## What "correct and sound" means, formally

A pass is a total function `run : Block D.Op → Block D.Op` on Yul programs
(top-level blocks over the built-in operation type of a dialect `D`). It is
**sound** when its output is *semantically equivalent* to its input:

```
Sound D run  :=  ∀ b, EquivBlock D b (run b)
```

`EquivBlock` (from `YulSemantics.Equiv`) is *pointwise* big-step equivalence: the
two blocks yield the **same** results — final variable environment `V'`, final
machine state `st'` (hence identical halt payloads, which live in the state), and
control-flow outcome `o` (`normal`/`break`/`continue`/`leave`/`halt`) — from
**every** function environment, variable environment, and initial state. It is
strictly stronger than observational equivalence, which is exactly what makes it
the right notion for an optimizer: a sound replacement is undetectable in *any*
context, so passes compose (`Pass.comp`) and local rewrites lift through the
syntax congruences of `YulSemantics.Equiv`.

Soundness is precisely the obligation `AGENTS.md` requires of a source-to-source
pass — a theorem "relating its input and output under `YulSemantics.Run`
(including halt payloads, environments, and all outcomes it can encounter)" — and
more: it holds at every sub-configuration, not only at the top-level `Run`. The
top-level consequence — that a pass changes no observable whole-program behavior
— is recovered by `Pass.preservesRun`, and its composition with the verified
backend by `Optimizer.Pass.optimize_then_compile_correct` (see `Backend.lean`).

## Algebra of passes

Passes are closed under composition: `Pass.comp` runs one after another and
discharges soundness by transitivity. With the identity pass
(`Optimizer.identity`, in `Identity.lean`) as unit, this makes a sound
optimization *pipeline* just another sound `Pass` — so a research loop can grow
the pipeline one proved pass at a time and inherit end-to-end soundness for free.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-- **Soundness** of a source-to-source transform: its output is pointwise
semantically equivalent to its input — at every function/variable environment
and initial state, and for every control-flow outcome and resulting state. This
is the sole proof obligation for admitting a Yul→Yul pass in front of the
verified backend. -/
def Sound (D : Dialect) [DecidableEq D.Value] (run : Block D.Op → Block D.Op) : Prop :=
  ∀ b, EquivBlock D b (run b)

/-- A **verified optimizer pass**: a total Yul→Yul transformation bundled with a
proof that it preserves program semantics. A value of this type *is* a sound
optimizer; there is no way to construct one without discharging `Sound`. -/
structure Pass (D : Dialect) [DecidableEq D.Value] where
  /-- The source-to-source transformation on top-level blocks. -/
  run : Block D.Op → Block D.Op
  /-- Proof obligation: the transformation is semantics-preserving (`Sound`). -/
  sound : Sound D run

namespace Pass

/-- The whole-program behavioral guarantee: a sound pass leaves every `Run`
result unchanged — same final environment, final state, and outcome, from every
initial state. Combined with determinism (`YulSemantics.Run.det`), this means the
optimized program has the *same unique* result as the original. -/
theorem preservesRun (P : Pass D) (b : Block D.Op) {st0 V' st' o} :
    Run D b st0 V' st' o ↔ Run D (P.run b) st0 V' st' o :=
  (P.sound b).run_iff

/-- Transport a run of the original program to a run of the optimized program. -/
theorem run_optimized (P : Pass D) {b : Block D.Op} {st0 V' st' o}
    (h : Run D b st0 V' st' o) : Run D (P.run b) st0 V' st' o :=
  (P.preservesRun b).mp h

/-- Transport a run of the optimized program back to a run of the original. -/
theorem run_original (P : Pass D) {b : Block D.Op} {st0 V' st' o}
    (h : Run D (P.run b) st0 V' st' o) : Run D b st0 V' st' o :=
  (P.preservesRun b).mpr h

/-- **Composition of passes.** `comp P Q` runs `Q` first and then `P`
(`run = P.run ∘ Q.run`); it is sound by transitivity of `EquivBlock`. A verified
pipeline is therefore itself a single verified `Pass`. -/
def comp (P Q : Pass D) : Pass D where
  run := fun b => P.run (Q.run b)
  sound := fun b => (Q.sound b).trans (P.sound (Q.run b))

@[simp] theorem comp_run (P Q : Pass D) (b : Block D.Op) :
    (comp P Q).run b = P.run (Q.run b) := rfl

end Pass

end YulEvmCompiler.Optimizer
