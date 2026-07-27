import YulEvmCompiler.Optimizer.Implementation.Flatten
import YulEvmCompiler.Optimizer.Implementation.FlattenSound
import YulEvmCompiler.Optimizer.Implementation.FuseDeclAssignSound
import YulEvmCompiler.Optimizer.Implementation.ReuseValues
import YulEvmCompiler.Optimizer.Implementation.ReuseValuesSound
import YulEvmCompiler.Optimizer.Implementation.PruneDefsResolve
import YulEvmCompiler.Optimizer.Implementation.ResolveCongr
import YulEvmCompiler.Optimizer.Implementation.RejoinPairs
set_option warningAsError true
/-!
# Pass values for the structural cleanup family

`LocalPass`/resolution-congruence bundles for `Flatten`, `FuseDeclAssign`,
`ReuseValues`, and `PruneDefs`.

`PruneDefs` is fully proved (`PruneDefsSound`/`PruneDefsResolve`).  The other
three passes are guarded by whole-block layout-freedom on **both input and
output** (post-checked, falling back to the input), so their object-path
congruences reduce to their block soundness via `resolve_storageLayoutFreeStmts`
— resolution is the identity on both sides.  All four block-soundness
theorems are fully proved:

* `flattenBlock_sound` — the splice frame argument (`FlattenSound`) plus a
  block-local fresh-binder alpha conversion;
* `fuseDeclAssignBlock_sound` — the binding-sink env-reorder transport
  (`FuseDeclAssignSound`);
* `reuseValuesBlock_sound` — the `StorageForward`-style cache-validity
  simulation extended with content-keyed keccak and memory-cell facts
  (`ReuseValuesSound`).
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-! ### The block-soundness theorems -/

/-- Block soundness of flattening (fully proved). -/
theorem flattenBlock_sound (b : Block Op) :
    EquivBlock D b (Flatten.flattenBlock b) :=
  Flatten.flattenBlock_equiv b

/-- Block soundness of declare-then-assign fusion (fully proved). -/
theorem fuseDeclAssignBlock_sound (b : Block Op) :
    EquivBlock D b (FuseDeclAssign.fuseDeclAssignBlock b) :=
  FuseDeclAssign.fuseDeclAssignBlock_equiv b

/-- Block soundness of available-value reuse (fully proved). -/
theorem reuseValuesBlock_sound (b : Block Op) :
    EquivBlock D b (ReuseValues.reuseValuesBlock b) :=
  ReuseValues.reuseValuesBlock_equiv b

/-! ### The pass values -/

def flatten : LocalPass D where
  run := Flatten.flattenBlock
  sound := fun b => flattenBlock_sound b

def fuseDeclAssign : LocalPass D where
  run := FuseDeclAssign.fuseDeclAssignBlock
  sound := fun b => fuseDeclAssignBlock_sound b

def reuseValues : LocalPass D where
  run := ReuseValues.reuseValuesBlock
  sound := fun b => reuseValuesBlock_sound b

/-- Unreachable-definition pruning as a verified pass (fully proved). -/
def pruneDefs : LocalPass D where
  run := PruneDefs.pruneDefsBlock
  sound := fun b => PruneDefs.pruneDefsBlock_sound b

/-! ### Object-path congruences

For the guarded passes, either the pass fired — then input and output are both
layout-free, resolution is the identity on both, and the congruence *is* the
soundness theorem — or it declined and the two sides are equal. -/

/-- Object-path congruence for `flatten`. -/
theorem resolveFlattenBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (Flatten.flattenBlock b)) := by
  have hsound := flattenBlock_sound (calls := calls) (creates := creates) b
  unfold Flatten.flattenBlock at hsound ⊢
  by_cases h1 : storageLayoutFreeStmts b
  · rw [if_pos h1] at hsound ⊢
    by_cases h2 : storageLayoutFreeStmts (Flatten.flattenCore b)
    · simp only [if_pos h2] at hsound ⊢
      rw [resolve_storageLayoutFreeStmts L b h1,
        resolve_storageLayoutFreeStmts L _ h2]
      exact hsound
    · simp only [if_neg h2] at hsound ⊢
      exact EquivBlock.refl _
  · rw [if_neg h1]
    exact EquivBlock.refl _

/-- Object-path congruence for `fuseDeclAssign`. -/
theorem resolveFuseDeclAssignBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (FuseDeclAssign.fuseDeclAssignBlock b)) := by
  have hsound := fuseDeclAssignBlock_sound (calls := calls) (creates := creates) b
  unfold FuseDeclAssign.fuseDeclAssignBlock at hsound ⊢
  by_cases h1 : storageLayoutFreeStmts b
  · rw [if_pos h1] at hsound ⊢
    by_cases h2 : storageLayoutFreeStmts (FuseDeclAssign.fdStmts b)
    · simp only [if_pos h2] at hsound ⊢
      rw [resolve_storageLayoutFreeStmts L b h1,
        resolve_storageLayoutFreeStmts L _ h2]
      exact hsound
    · simp only [if_neg h2] at hsound ⊢
      exact EquivBlock.refl _
  · rw [if_neg h1]
    exact EquivBlock.refl _

/-- Object-path congruence for `reuseValues`. -/
theorem resolveReuseValuesBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (ReuseValues.reuseValuesBlock b)) := by
  have hsound := reuseValuesBlock_sound (calls := calls) (creates := creates) b
  unfold ReuseValues.reuseValuesBlock at hsound ⊢
  by_cases h1 : storageLayoutFreeStmts b
  · rw [if_pos h1] at hsound ⊢
    by_cases h2 : storageLayoutFreeStmts
        (ReuseValues.reuseValuesShallowBlock (ReuseValues.rvFunStmts b))
    · simp only [if_pos h2] at hsound ⊢
      rw [resolve_storageLayoutFreeStmts L b h1,
        resolve_storageLayoutFreeStmts L _ h2]
      exact hsound
    · simp only [if_neg h2] at hsound ⊢
      exact EquivBlock.refl _
  · rw [if_neg h1]
    exact EquivBlock.refl _

/-- Object-path congruence for `pruneDefs` (fully proved). -/
theorem resolvePruneDefsBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (PruneDefs.pruneDefsBlock b)) := by
  rw [PruneDefs.resolve_pruneDefsBlock]
  exact PruneDefs.pruneDefsBlock_sound (resolveForLayoutStmts L b)

end YulEvmCompiler.Optimizer
