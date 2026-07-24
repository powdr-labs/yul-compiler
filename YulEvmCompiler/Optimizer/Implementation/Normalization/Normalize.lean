import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate.Pass
import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate.NormalForm
import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate.Decide
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
   (`SourceValid`); the transform **guards** on the decidable mirror
   `sourceValidB` (`Disambiguate/Decide.lean`, sound by `sourceValidB_sound`) and
   is the identity elsewhere, so it is **unconditionally** sound — the
   `hoistFunDefsPass` pattern.
2. **Hoist functions** (`hoistBlock` / `hoistFunDefsPass`, `HoistFunDefs*`) — lift
   every function definition to the root block with a definition-free body
   (`NormalForm.FunctionsHoisted`). Hoisting is only sound when function names are
   globally unique *and* the program is well scoped, so it must run **after**
   disambiguation; the pass guards on a decidable check and is unconditionally
   sound (`GlobalPass`).

Both steps guard, so `normalize`/`normalizePass` are **unconditionally**
semantics-preserving `GlobalPass`es — no `SourceValid` hypothesis survives to the
composed pipeline. On any valid source program (which the parser's validator
guarantees) both guards fire, so normalization really does disambiguate and hoist
rather than fall back to the identity.

The result is that the pipeline **starts** with one normalization pass whose
output is disambiguated and function-hoisted; subsequent optimizer stages may
assume that shape (and are expected to preserve it — the per-stage preservation
obligations, and the remaining `NormalForm` fields established by the not-yet-
landed ANF / for-init / flatten passes, are the follow-up tracked in
`NormalForm.lean` and `Optimizer/IDEAS.md`).

## Soundness

`normalize_runEquivBlock` (block) and `normalizePass` (whole object tree, via its
`GlobalPass.sound` field) are unconditional. These are the facts `Pipeline.lean`
composes with the verified optimizer to state whole-program correctness of the
composite.
-/

namespace YulEvmCompiler.Optimizer.Normalize

open YulSemantics
open YulEvmCompiler.Optimizer (RunEquivBlock ObjEquiv guardedBlock GlobalPass mapObjCode)
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

/-! ### The guarded disambiguator -/

/-- Disambiguation, **guarded** on the decidable source-validity mirror: rename
where `sourceValidB` holds (its soundness theorem then applies), identity
otherwise. -/
def disambiguateGuarded (b : Block D.Op) : Block D.Op := guardedBlock sourceValidB disambiguate b

/-- **The guarded disambiguator preserves whole-program behaviour**,
unconditionally. Where the guard fires, `sourceValidB_sound` supplies the
`SourceValid` hypothesis of `sourceValid_runEquivBlock`; elsewhere it is the
identity. -/
theorem disambiguateGuarded_runEquiv (b : Block D.Op) :
    RunEquivBlock D b (disambiguateGuarded b) := by
  simp only [disambiguateGuarded, guardedBlock]
  by_cases hb : sourceValidB b = true
  · rw [if_pos hb]; exact sourceValid_runEquivBlock (sourceValidB_sound hb)
  · rw [if_neg hb]; exact RunEquivBlock.refl b

/-- Disambiguation as an **unconditionally sound** whole-tree `GlobalPass`. -/
def disambiguatePass : GlobalPass D :=
  GlobalPass.ofGuardedBlock sourceValidB disambiguate
    (fun _ hg => sourceValid_runEquivBlock (sourceValidB_sound hg))

/-! ### The transform -/

/-- **Full normalization of a block**: (guarded) disambiguate, then hoist every
function definition to the top. -/
def normalize (b : Block D.Op) : Block D.Op := hoistBlock (disambiguateGuarded b)

/-- Full normalization as an **unconditionally sound** whole-tree `GlobalPass`:
disambiguate then hoist every code block (each object — the deploy artifact and
every nested runtime — is its own root). -/
def normalizePass : GlobalPass D := GlobalPass.comp hoistFunDefsPass disambiguatePass

/-- **Full normalization of an object tree.** -/
def normalizeObject (o : Object D.Op) : Object D.Op := normalizePass.run o

@[simp] theorem normalizeObject_codeBlock (o : Object D.Op) :
    (normalizeObject o).codeBlock = normalize o.codeBlock := by
  cases o; rfl

/-! ### Unconditional soundness (block) -/

/-- **Full normalization preserves whole-program behaviour** on every block: `b`
and `normalize b` run identically from the top-of-execution interface. Both steps
guard, so no source-validity hypothesis is needed. -/
theorem normalize_runEquivBlock (b : Block D.Op) :
    RunEquivBlock D b (normalize b) :=
  (disambiguateGuarded_runEquiv b).trans (hoistBlock_runEquiv (disambiguateGuarded b))

/-! ### Unconditional soundness (object tree) -/

/-- **Whole-tree normalization preserves whole-program behaviour**, on every
object tree — it is the `GlobalPass.sound` field of `normalizePass`. -/
theorem normalizeObject_objEquiv (o : Object D.Op) :
    ObjEquiv D o (normalizeObject o) :=
  normalizePass.sound o

/-- The operative consequence at the object boundary (`RunObject`/
`RunResolvedObject` depend only on the top code block). -/
theorem normalizeObject_topRunEquiv (o : Object D.Op) :
    RunEquivBlock D o.codeBlock (normalizeObject o).codeBlock := by
  rw [normalizeObject_codeBlock]
  exact normalize_runEquivBlock _

end YulEvmCompiler.Optimizer.Normalize
