import YulEvmCompiler.Optimizer.Implementation.DeadStore.DeadStore
import YulEvmCompiler.Optimizer.Implementation.StorageForwardResolve
/-!
# YulEvmCompiler.Optimizer.Implementation.DeadStore.Resolve

Layout-resolution congruence for dead-store elimination — the per-stage fact the
**object path** needs (`optimizerPipelineObject_correct` composes it over the
whole tree via `RPass`).

Object-layout resolution (`resolveForLayoutStmts`) rewrites the object-data ops
(`dataoffset`/`datasize`/`datacopy`) into layout constants, which can change a
key's shape and hence a dead-store decision. Rather than reason about that
interaction, we follow `StorageForward`: the object-path pass acts **only on
layout-free blocks** (`storageLayoutFreeStmts`), on which resolution is the
identity, so running the pass then resolving equals resolving then (not) running
it. On any block containing a data op the pass is the identity. Runtime code
blocks (the DSE hot path) are layout-free; deploy code with `datacopy` is left
to the backend unchanged.

Everything here is proved outright; the object-path soundness rests only on the
one remaining semantic obligation `deadAt_sound`.
-/

namespace YulEvmCompiler.Optimizer.DeadStore

open YulSemantics YulSemantics.EVM
open YulEvmCompiler

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-! ### Dead-store elimination preserves layout-freeness -/

mutual
theorem dseStmt_layoutFree (R : Region) :
    ∀ s : Stmt Op, storageLayoutFreeStmt s = true → storageLayoutFreeStmt (dseStmt R s) = true
  | .block body, h => by
      rw [dseStmt]; simp only [storageLayoutFreeStmt] at h ⊢
      exact dseStmts_layoutFree R body h
  | .cond c body, h => by
      rw [dseStmt]; simp only [storageLayoutFreeStmt, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, dseStmts_layoutFree R body h.2⟩
  | .switch c cases dflt, h => by
      rw [dseStmt]; simp only [storageLayoutFreeStmt, Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1.1, dseCases_layoutFree R cases h.1.2⟩, dseDflt_layoutFree R dflt h.2⟩
  | .forLoop init c post body, h => by
      rw [dseStmt]; simp only [storageLayoutFreeStmt, Bool.and_eq_true] at h ⊢
      exact ⟨⟨⟨h.1.1.1, h.1.1.2⟩, dseStmts_layoutFree R post h.1.2⟩,
        dseStmts_layoutFree R body h.2⟩
  | .funDef _ _ _ _, h => h
  | .letDecl _ _, h => h
  | .assign _ _, h => h
  | .exprStmt _, h => h
  | .break, h => h
  | .continue, h => h
  | .leave, h => h
theorem dseStmts_layoutFree (R : Region) :
    ∀ ss : List (Stmt Op), storageLayoutFreeStmts ss = true →
      storageLayoutFreeStmts (dseStmts R ss) = true
  | [], h => h
  | s :: rest, h => by
      simp only [storageLayoutFreeStmts, Bool.and_eq_true] at h
      simp only [dseStmts]
      split
      · split
        · exact dseStmts_layoutFree R rest h.2
        · simp only [storageLayoutFreeStmts, Bool.and_eq_true]
          exact ⟨dseStmt_layoutFree R s h.1, dseStmts_layoutFree R rest h.2⟩
      · simp only [storageLayoutFreeStmts, Bool.and_eq_true]
        exact ⟨dseStmt_layoutFree R s h.1, dseStmts_layoutFree R rest h.2⟩
theorem dseCases_layoutFree (R : Region) :
    ∀ cases : List (Literal × List (Stmt Op)), storageLayoutFreeCases cases = true →
      storageLayoutFreeCases (dseCases R cases) = true
  | [], h => h
  | (_, b) :: rest, h => by
      simp only [storageLayoutFreeCases, Bool.and_eq_true] at h
      rw [dseCases]; simp only [storageLayoutFreeCases, Bool.and_eq_true]
      exact ⟨dseStmts_layoutFree R b h.1, dseCases_layoutFree R rest h.2⟩
theorem dseDflt_layoutFree (R : Region) :
    ∀ dflt : Option (List (Stmt Op)), storageLayoutFreeDflt dflt = true →
      storageLayoutFreeDflt (dseDflt R dflt) = true
  | none, h => h
  | some b, h => by
      rw [dseDflt]; simp only [storageLayoutFreeDflt] at h ⊢
      exact dseStmts_layoutFree R b h
end

theorem deadStoreBlock_layoutFree (b : Block Op) (h : storageLayoutFreeStmts b = true) :
    storageLayoutFreeStmts (deadStoreBlock b) = true := by
  unfold deadStoreBlock
  exact dseStmts_layoutFree .memory _
    (dseStmts_layoutFree .transient _ (dseStmts_layoutFree .storage b h))

/-! ### The object-path pass: guarded to layout-free blocks -/

/-- Dead-store elimination for the object path: acts only on layout-free blocks
(the identity elsewhere), so it commutes with object-layout resolution. -/
def deadStoreObjBlock (b : Block Op) : Block Op :=
  if storageLayoutFreeStmts b then deadStoreBlock b else b

theorem deadStoreObjBlock_sound : Sound D deadStoreObjBlock := by
  intro b
  unfold deadStoreObjBlock
  by_cases h : storageLayoutFreeStmts b = true
  · rw [if_pos h]; exact (deadStore (calls := calls) (creates := creates)).sound b
  · rw [if_neg h]; exact EquivBlock.refl b

/-- The object-path dead-store pass, as a verified `Pass`. -/
def deadStoreObj : Pass D where
  run := deadStoreObjBlock
  sound := deadStoreObjBlock_sound

@[simp] theorem deadStoreObj_run (b : Block Op) :
    (deadStoreObj (calls := calls) (creates := creates)).run b = deadStoreObjBlock b := rfl

/-- **Resolution congruence.** Running the (guarded) dead-store pass before layout
resolution agrees pointwise with not running it, on the resolved code — the exact
shape the object pipeline's `RPass` expects. -/
theorem resolveDeadStoreObj_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L ((deadStoreObj (calls := calls) (creates := creates)).run b)) := by
  show EquivBlock D (resolveForLayoutStmts L b) (resolveForLayoutStmts L (deadStoreObjBlock b))
  unfold deadStoreObjBlock
  by_cases h : storageLayoutFreeStmts b = true
  · rw [if_pos h, resolve_storageLayoutFreeStmts L b h,
        resolve_storageLayoutFreeStmts L (deadStoreBlock b) (deadStoreBlock_layoutFree b h)]
    exact (deadStore (calls := calls) (creates := creates)).sound b
  · rw [if_neg h]; exact EquivBlock.refl _

end YulEvmCompiler.Optimizer.DeadStore
