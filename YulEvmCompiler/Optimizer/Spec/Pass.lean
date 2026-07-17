import YulSemantics.Equiv
import YulEvmCompiler.Optimizer.Spec.Scoped

/-!
# YulEvmCompiler.Optimizer.Spec.Pass

The **stable specification** a Yul→Yul optimizer pass must satisfy. This module is
the contract: it defines what "correct and sound" means for a pass and fixes the
single proof obligation. Once agreed, it is not meant to change — every concrete
pass under `Optimizer/Implementation/` is a value of the `Pass` structure defined
here, and an auditor who trusts this file need not read any pass's proof.

## What "correct and sound" means, formally

A pass is a total function `run : Block D.Op → Block D.Op` on Yul programs
(top-level blocks over the built-in operation type of a dialect `D`). It is
**sound** when its output is *semantically equivalent* to its input:

```
Sound D run  :=  ∀ b, EquivBlock D b (run b)
```

`EquivBlock` (from the pinned `YulSemantics.Equiv`) is *pointwise* big-step
equivalence: the two blocks yield the **same** results — final variable
environment `V'`, final machine state `st'` (hence identical halt payloads, which
live in the state), and control-flow outcome `o`
(`normal`/`break`/`continue`/`leave`/`halt`) — from **every** function
environment, variable environment, and initial state. It is strictly stronger
than observational equivalence, which is exactly the point: a sound replacement is
undetectable in *any* context, so passes compose (`Pass.comp`) and local rewrites
lift through the syntax congruences of `YulSemantics.Equiv`.

Soundness is precisely the obligation `AGENTS.md` requires of a source-to-source
pass — a theorem "relating its input and output under `YulSemantics.Run`
(including halt payloads, environments, and all outcomes it can encounter)" — and
more: it holds at every sub-configuration, not only at the top-level `Run`. The
top-level consequence — that a pass changes no observable whole-program behavior —
is `Pass.preservesRun`; its composition with the verified backend is
`Optimizer.Pass.optimize_then_compile_correct` (see `Spec/Backend.lean`).

## Why implementations need no separate audit

The `Pass` structure bundles a transform with its `Sound` proof, so *possessing* a
`Pass` value is possessing a verified optimizer — there is no way to build one
without discharging the obligation. Consequently the audited surface only ever
needs this spec (`Pass`, `Sound`) and its guarantees; a concrete pass in
`Optimizer/Implementation/` is trusted the moment it type-checks as a `Pass`, and
its internal proof is not part of what an auditor must read.

## Algebra of passes

Passes are closed under composition (`Pass.comp`, sound by transitivity of
`EquivBlock`) with the do-nothing pass (`Pass.id`, sound by reflexivity) as unit.
A whole optimization *pipeline* is therefore itself a single sound `Pass`
(`Pass.ofList`) — so a research loop can grow the pipeline one proved pass at a
time and inherit end-to-end soundness for free.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-- **Soundness** of a source-to-source transform: its output is pointwise
semantically equivalent to its input — at every function/variable environment and
initial state, and for every control-flow outcome and resulting state. This is the
sole proof obligation for admitting a Yul→Yul pass in front of the verified
backend. -/
def Sound (D : Dialect) [DecidableEq D.Value] (run : Block D.Op → Block D.Op) : Prop :=
  ∀ b, WellScoped b → EquivBlock D b (run b)

/-- A **verified optimizer pass**: a total Yul→Yul transformation bundled with a
proof that it preserves program semantics on **well-scoped** input, and a proof
that it preserves well-scopedness (so passes compose). A value of this type *is* a
sound optimizer; there is no way to construct one without discharging `Sound`.

The well-scopedness precondition is what makes aggressive binding-removal (dead
`let`, copy-propagation) sound — see `Spec/Scoped.lean`. It costs no real
coverage: every program the frontend/`solc` emits is well-scoped. The `scoped`
field keeps the class closed under composition (`comp`/`ofList`). -/
structure Pass (D : Dialect) [DecidableEq D.Value] where
  /-- The source-to-source transformation on top-level blocks. -/
  run : Block D.Op → Block D.Op
  /-- Proof obligation: the transformation is semantics-preserving on well-scoped
  input (`Sound`). -/
  sound : Sound D run
  /-- Proof obligation: the transformation maps well-scoped programs to
  well-scoped programs, so passes compose. -/
  preservesScoped : ∀ b, WellScoped b → WellScoped (run b)

namespace Pass

/-- The whole-program behavioral guarantee: a sound pass leaves every `Run` result
unchanged — same final environment, final state, and outcome, from every initial
state. Combined with determinism (`YulSemantics.Run.det`), this means the optimized
program has the *same unique* result as the original. -/
theorem preservesRun (P : Pass D) (b : Block D.Op) (hb : WellScoped b) {st0 V' st' o} :
    Run D b st0 V' st' o ↔ Run D (P.run b) st0 V' st' o :=
  (P.sound b hb).run_iff

/-- Transport a run of the original program to a run of the optimized program. -/
theorem run_optimized (P : Pass D) {b : Block D.Op} (hb : WellScoped b) {st0 V' st' o}
    (h : Run D b st0 V' st' o) : Run D (P.run b) st0 V' st' o :=
  (P.preservesRun b hb).mp h

/-- Transport a run of the optimized program back to a run of the original. -/
theorem run_original (P : Pass D) {b : Block D.Op} (hb : WellScoped b) {st0 V' st' o}
    (h : Run D (P.run b) st0 V' st' o) : Run D b st0 V' st' o :=
  (P.preservesRun b hb).mpr h

/-- The **do-nothing pass**: returns its input unchanged, sound by reflexivity of
semantic equivalence. It is the neutral element of `comp` and the seed of `ofList`.
(The user-facing *identity optimizer pass* is this, packaged as a concrete
implementation in `Optimizer/Implementation/Identity.lean`.) -/
def id : Pass D where
  run := fun b => b
  sound := fun b _ => EquivBlock.refl b
  preservesScoped := fun _ h => h

@[simp] theorem id_run (b : Block D.Op) : (id (D := D)).run b = b := rfl

/-- **Composition of passes.** `comp P Q` runs `Q` first and then `P`
(`run = P.run ∘ Q.run`); it is sound by transitivity of `EquivBlock`. A verified
pipeline is therefore itself a single verified `Pass`. -/
def comp (P Q : Pass D) : Pass D where
  run := fun b => P.run (Q.run b)
  sound := fun b hb => (Q.sound b hb).trans (P.sound (Q.run b) (Q.preservesScoped b hb))
  preservesScoped := fun b hb => P.preservesScoped (Q.run b) (Q.preservesScoped b hb)

@[simp] theorem comp_run (P Q : Pass D) (b : Block D.Op) :
    (comp P Q).run b = P.run (Q.run b) := rfl

@[simp] theorem comp_id_left (P : Pass D) : (comp id P).run = P.run := rfl
@[simp] theorem comp_id_right (P : Pass D) : (comp P id).run = P.run := rfl
theorem comp_assoc (P Q R : Pass D) :
    (comp (comp P Q) R).run = (comp P (comp Q R)).run := rfl

/-! ### Pipelines: a list of passes is a pass -/

/-- Fold a list of passes into a single pass, applied **left to right** (the head
runs first), seeded by `id`. The result is a `Pass`, so an entire optimization
pipeline carries one soundness proof assembled from its stages'. -/
def ofList (ps : List (Pass D)) : Pass D :=
  ps.foldr (fun p acc => comp acc p) id

@[simp] theorem ofList_nil : ofList ([] : List (Pass D)) = id := rfl
@[simp] theorem ofList_cons (p : Pass D) (ps : List (Pass D)) :
    ofList (p :: ps) = comp (ofList ps) p := rfl

/-- The pipeline's whole-program behavior matches the source program's — the
end-to-end soundness of a composed optimizer, for free. -/
theorem ofList_preservesRun (ps : List (Pass D)) (b : Block D.Op) (hb : WellScoped b)
    {st0 V' st' o} :
    Run D b st0 V' st' o ↔ Run D ((ofList ps).run b) st0 V' st' o :=
  (ofList ps).preservesRun b hb

end Pass

end YulEvmCompiler.Optimizer
