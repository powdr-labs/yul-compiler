import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate
import YulSemantics.Equiv
/-!
# Semantic soundness of name disambiguation — foundations

Goal: `EquivBlock D b (disambiguate b)` for well-formed `b`. Disambiguation
renames only *declared* (bound) names, and every declaration in a block is
dropped from the variable environment on block exit (`restore`) — so the renaming
is invisible in the observable result. Proving it, however, needs a bisimulation
that carries a *renaming* through the big-step judgment (`Step`).

This file builds the reusable variable-environment layer: `renVEnv σ V` renames a
variable environment's keys by `σ`, and the transport lemmas show the semantic
helpers (`get`, `set`, `setMany`, `bindZeros`, `restore`) commute with an
*injective* key-renaming. Injectivity is the semantic content of Yul's
no-shadowing rule (in-scope names are distinct) together with disambiguation's
globally-fresh, capture-avoiding `dsName`s.

The function-environment side and the `Step` induction proper build on top.
-/

namespace YulEvmCompiler.Optimizer.Normalize

open YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-! ### Renaming a variable environment -/

/-- `renVEnv σ V` is `V` with every key renamed by `σ` (values untouched). -/
def renVEnv (σ : Ident → Ident) (V : VEnv D) : VEnv D := V.map (fun p => (σ p.1, p.2))

@[simp] theorem renVEnv_nil (σ : Ident → Ident) : renVEnv σ ([] : VEnv D) = [] := rfl

@[simp] theorem renVEnv_cons (σ : Ident → Ident) (x : Ident) (v : D.Value) (V : VEnv D) :
    renVEnv σ ((x, v) :: V) = (σ x, v) :: renVEnv σ V := rfl

@[simp] theorem renVEnv_length (σ : Ident → Ident) (V : VEnv D) :
    (renVEnv σ V).length = V.length := by simp [renVEnv]

@[simp] theorem renVEnv_append (σ : Ident → Ident) (V W : VEnv D) :
    renVEnv σ (V ++ W) = renVEnv σ V ++ renVEnv σ W := by simp [renVEnv]

/-- Keys of a renamed environment are the σ-images of the keys. -/
theorem renVEnv_keys (σ : Ident → Ident) (V : VEnv D) :
    (renVEnv σ V).map Prod.fst = (V.map Prod.fst).map σ := by
  simp [renVEnv, List.map_map, Function.comp]

/-! ### `get` transport

For a *specific* looked-up name `x`, `get` needs only that `σ` does not merge any
other in-scope key onto `σ x` — captured by `hne : ∀ y ∈ keys, σ y = σ x → y = x`. -/

theorem renVEnv_get (σ : Ident → Ident) (V : VEnv D) (x : Ident)
    (hne : ∀ p ∈ V, σ p.1 = σ x → p.1 = x) :
    VEnv.get (renVEnv σ V) (σ x) = VEnv.get V x := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      simp only [renVEnv_cons, VEnv.get, List.find?_cons]
      by_cases hyx : y = x
      · subst hyx; simp
      · have hσ : ¬ (σ y = σ x) := fun h => hyx (hne (y, w) (List.mem_cons_self ..) h)
        simp only [hyx, hσ, decide_false, cond_false]
        exact ih (fun p hp => hne p (List.mem_cons_of_mem _ hp))
/-! ### `set` transport (same per-name no-merge condition as `get`) -/

theorem renVEnv_set (σ : Ident → Ident) (V : VEnv D) (x : Ident) (v : D.Value)
    (hne : ∀ p ∈ V, σ p.1 = σ x → p.1 = x) :
    VEnv.set (renVEnv σ V) (σ x) v = renVEnv σ (VEnv.set V x v) := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      simp only [renVEnv_cons, VEnv.set]
      by_cases hyx : y = x
      · subst hyx; simp
      · have hσ : ¬ (σ y = σ x) := fun h => hyx (hne (y, w) (List.mem_cons_self ..) h)
        rw [if_neg hyx, if_neg hσ, renVEnv_cons,
          ih (fun p hp => hne p (List.mem_cons_of_mem _ hp))]

/-! ### `bindZeros` and `restore` transport (unconditional) -/

@[simp] theorem renVEnv_bindZeros (σ : Ident → Ident) (xs : List Ident) :
    renVEnv σ (bindZeros D xs) = bindZeros D (xs.map σ) := by
  simp [renVEnv, bindZeros, List.map_map, Function.comp]

theorem renVEnv_restore (σ : Ident → Ident) (V W : VEnv D) :
    renVEnv σ (restore V W) = restore (renVEnv σ V) (renVEnv σ W) := by
  simp only [restore, renVEnv, List.map_drop, List.length_map]

/-! ### `setMany` transport (under a genuinely injective renaming) -/

theorem VEnv.setMany_cons (V : VEnv D) (x : Ident) (v : D.Value)
    (xs : List Ident) (vs : List D.Value) :
    VEnv.setMany V (x :: xs) (v :: vs) = VEnv.setMany (VEnv.set V x v) xs vs := by
  simp [VEnv.setMany, List.zip_cons_cons, List.foldl_cons]

theorem renVEnv_setMany (σ : Ident → Ident) (hinj : Function.Injective σ) :
    ∀ (vars : List Ident) (vals : List D.Value) (V : VEnv D),
      VEnv.setMany (renVEnv σ V) (vars.map σ) vals = renVEnv σ (VEnv.setMany V vars vals) := by
  intro vars
  induction vars with
  | nil => intro vals V; simp [VEnv.setMany]
  | cons x xs ih =>
      intro vals V
      cases vals with
      | nil => simp [VEnv.setMany]
      | cons v vs =>
          rw [List.map_cons, VEnv.setMany_cons, VEnv.setMany_cons,
            renVEnv_set σ V x v (fun _ _ h => hinj h), ih vs (VEnv.set V x v)]
