import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate.Pass
import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate.NormalForm
import YulEvmCompiler.Optimizer.Implementation.Normalization.HoistFunDefsPass
set_option warningAsError true
/-!
# The full normalization pass: disambiguate, then hoist

`Normalize.normalize` is the single **normalization front-end** the compiler runs
before the optimizer proper. It chains the landed normalization steps in the
order their preconditions demand:

1. **Disambiguate** (`disambiguate`, `Disambiguate/`) — rename every declared
   variable and function so no name is declared twice
   (`NormalForm.UniqueNames`). Semantics-preserving for valid source programs
   (`SourceValid`, an *assumed* precondition — see `Disambiguate/Pass.lean`).
2. **Hoist functions** (`hoistBlock` / `hoistFunDefsPass`, `HoistFunDefs*`) — lift
   every function definition to the root block with a definition-free body
   (`NormalForm.FunctionsHoisted`). Hoisting is only sound when function names are
   globally unique *and* the program is well scoped, so it must run **after**
   disambiguation; the pass guards on a decidable check and is unconditionally
   sound (`GlobalPass`).

Running disambiguation first is exactly what makes the guarded hoister fire: on
its uniquely-named, well-scoped output the `hoistGuard` holds, so `hoistBlock`
really does hoist rather than fall back to the identity.

The result is that the pipeline **starts** with one normalization pass whose
output is disambiguated and function-hoisted; subsequent optimizer stages may
assume that shape (and are expected to preserve it — the per-stage preservation
obligations, and the remaining `NormalForm` fields established by the not-yet-
landed ANF / for-init / flatten passes, are the follow-up tracked in
`NormalForm.lean` and `Optimizer/IDEAS.md`).

## Soundness

`normalize` is semantics-preserving under the same `SourceValid` hypotheses the
disambiguator owes (hoisting adds none — it is unconditional):
`sourceValid_normalize_runEquivBlock` (block) and `normalizeObject_objEquiv`
(whole object tree). These are the facts `Pipeline.lean` composes with the
verified optimizer to state whole-program correctness of the composite.
-/

namespace YulEvmCompiler.Optimizer.Normalize

open YulSemantics
open YulEvmCompiler.Optimizer (RunEquivBlock ObjEquiv guardedBlock)
open YulEvmCompiler.Optimizer.Normalization
  (hoistBlock hoistGuard hoistGuard_sound liftFunDefs liftFunDefs_run_equiv hoistFunDefsPass)

variable {D : Dialect} [DecidableEq D.Value]

/-! ### Block-level soundness of the guarded hoister -/

/-- **The guarded function hoister preserves whole-program behaviour**, at the
block level and unconditionally: where its guard fires the rewrite is
`liftFunDefs` (sound by `liftFunDefs_run_equiv`, whose hypotheses the guard
decides), and elsewhere it is the identity. This is the block-level companion of
`hoistFunDefsPass.sound`. -/
theorem hoistBlock_runEquiv (b : Block D.Op) :
    RunEquivBlock D b (hoistBlock b) := by
  simp only [hoistBlock, guardedBlock]
  by_cases hb : hoistGuard b = true
  · rw [if_pos hb]
    intro st0 V' st' o
    exact liftFunDefs_run_equiv (hoistGuard_sound hb).1 (hoistGuard_sound hb).2
  · rw [if_neg hb]; exact RunEquivBlock.refl b

/-! ### The transform -/

/-- **Full normalization of a block**: disambiguate, then hoist every function
definition to the top. -/
def normalize (b : Block D.Op) : Block D.Op := hoistBlock (disambiguate b)

/-- **Full normalization of an object tree**: disambiguate then hoist every code
block (each object — the deploy artifact and every nested runtime — is its own
root). -/
def normalizeObject (o : Object D.Op) : Object D.Op :=
  (hoistFunDefsPass (D := D)).run (disambiguateObject o)

@[simp] theorem normalizeObject_codeBlock (o : Object D.Op) :
    (normalizeObject o).codeBlock = normalize o.codeBlock := by
  cases o; rfl

/-! ### Conditional soundness (block) -/

/-- **Full normalization preserves whole-program behaviour** on a valid source
block: `b` and `normalize b` run identically from the top-of-execution
interface. The `SourceValid` hypothesis is the disambiguator's — hoisting is
unconditional. -/
theorem sourceValid_normalize_runEquivBlock {b : Block D.Op} (h : SourceValid b) :
    RunEquivBlock D b (normalize b) :=
  (sourceValid_runEquivBlock h).trans (hoistBlock_runEquiv (disambiguate b))

/-! ### Conditional soundness (object tree) -/

/-- **Whole-tree normalization preserves whole-program behaviour** on a valid
source tree. -/
theorem normalizeObject_objEquiv (o : Object D.Op) (h : SourceValidObj o) :
    ObjEquiv D o (normalizeObject o) :=
  (disambiguateObject_objEquiv o h).trans ((hoistFunDefsPass (D := D)).sound (disambiguateObject o))

/-- The operative consequence at the object boundary (`RunObject`/
`RunResolvedObject` depend only on the top code block): validity of the **top**
block alone preserves the tree's top-level behaviour. -/
theorem normalizeObject_topRunEquiv {o : Object D.Op} (h : SourceValid o.codeBlock) :
    RunEquivBlock D o.codeBlock (normalizeObject o).codeBlock := by
  rw [normalizeObject_codeBlock]
  exact sourceValid_normalize_runEquivBlock h

end YulEvmCompiler.Optimizer.Normalize
