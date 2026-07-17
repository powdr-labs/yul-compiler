import YulEvmCompiler.Optimizer.Pass

/-!
# YulEvmCompiler.Optimizer.Identity

The **identity optimizer pass**: the first inhabitant of `Optimizer.Pass`. It
returns its input Yul program unchanged and proves the semantics are equivalent,
so it validates that the `Pass` specification (`Pass.lean`) is inhabited and that
its proof obligation `Sound` is dischargeable.

Because the transform is literally the identity function, soundness is
reflexivity of `EquivBlock` — the honest proof that "returning the input"
preserves meaning. The identity pass is also the **unit** of pass composition
(`Pass.comp`), which makes it the natural seed for a research pipeline: `ofList`
folds a list of proved passes into one proved pass, starting from `identity`.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-- The **identity pass**: returns the input program unchanged. Sound by
reflexivity of semantic equivalence (`EquivBlock.refl`). -/
def identity : Pass D where
  run := fun b => b
  sound := fun b => EquivBlock.refl b

@[simp] theorem identity_run (b : Block D.Op) : (identity (D := D)).run b = b := rfl

/-- The identity pass changes no whole-program behavior: its `Run` results are
exactly those of the input program. (A direct corollary of `Pass.preservesRun`,
recorded here as the headline guarantee of this concrete pass.) -/
theorem identity_preservesRun (b : Block D.Op) {st0 V' st' o} :
    Run D b st0 V' st' o ↔ Run D ((identity (D := D)).run b) st0 V' st' o :=
  (identity (D := D)).preservesRun b

/-! ### The identity pass is the unit of composition -/

@[simp] theorem comp_identity_left (P : Pass D) :
    (Pass.comp identity P).run = P.run := rfl

@[simp] theorem comp_identity_right (P : Pass D) :
    (Pass.comp P identity).run = P.run := rfl

/-! ### Pipelines: a list of passes is a pass -/

/-- Fold a list of passes into a single pass, applied **left to right** (the head
runs first), seeded by `identity`. The result is a `Pass`, so an entire
optimization pipeline carries one soundness proof assembled from its stages'. -/
def ofList (ps : List (Pass D)) : Pass D :=
  ps.foldr (fun p acc => Pass.comp acc p) identity

@[simp] theorem ofList_nil : ofList ([] : List (Pass D)) = identity := rfl

@[simp] theorem ofList_cons (p : Pass D) (ps : List (Pass D)) :
    ofList (p :: ps) = Pass.comp (ofList ps) p := rfl

/-- The pipeline's whole-program behavior matches the source program's — the
end-to-end soundness of a composed optimizer, for free. -/
theorem ofList_preservesRun (ps : List (Pass D)) (b : Block D.Op) {st0 V' st' o} :
    Run D b st0 V' st' o ↔ Run D ((ofList ps).run b) st0 V' st' o :=
  (ofList ps).preservesRun b

end YulEvmCompiler.Optimizer
