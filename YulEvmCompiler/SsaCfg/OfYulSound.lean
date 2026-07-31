import YulEvmCompiler.SsaCfg.Sem
import YulEvmCompiler.SsaCfg.OfYul
import YulSemantics.BigStep
/-!
# YulEvmCompiler.SsaCfg.OfYulSound

**Construction soundness** for the `yul-ssa-cfg` dialect: every terminating
source derivation over a program the construction accepts is matched by an
SSA-CFG execution (`ofBlock_sound'`, the statement `Correctness.ofBlock_sound`
currently `sorry`s).

This file is the bottom-up half of that proof: the reusable infrastructure is
proved outright, the top-level plumbing is proved outright, and the remaining
holes are the statement-class simulation induction and the builder-state
monotonicity facts it consumes (each `sorry` carries the exact obligation).
-/

namespace YulEvmCompiler.SsaCfg

open YulSemantics (Ident Literal Expr Stmt VEnv Outcome)
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal evmWithExternal)

/-! ## `List.Forall₂` helpers

Self-contained so this file does not depend on which `Mathlib.Data.List`
modules happen to be transitively imported. -/

namespace Forall2

variable {α β : Type} {r s : α → β → Prop}

theorem imp (h : ∀ a b, r a b → s a b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ r l₁ l₂ → List.Forall₂ s l₁ l₂ := by
  intro l₁ l₂ hr
  induction hr with
  | nil => exact .nil
  | cons hh ht ih => exact .cons (h _ _ hh) ih

theorem length_eq : ∀ {l₁ : List α} {l₂ : List β},
    List.Forall₂ r l₁ l₂ → l₁.length = l₂.length := by
  intro l₁ l₂ hr
  induction hr with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem append : ∀ {a : List α} {b : List β} {c : List α} {d : List β},
    List.Forall₂ r a b → List.Forall₂ r c d → List.Forall₂ r (a ++ c) (b ++ d) := by
  intro a b c d hab hcd
  induction hab with
  | nil => simpa using hcd
  | cons hh _ ih => exact .cons hh ih

theorem drop : ∀ (n : Nat) {a : List α} {b : List β},
    List.Forall₂ r a b → List.Forall₂ r (a.drop n) (b.drop n) := by
  intro n
  induction n with
  | zero => intro a b h; simpa using h
  | succ n ih =>
    intro a b h
    cases h with
    | nil => simp
    | cons hh ht => simpa using ih ht

end Forall2

/-! ## Register files

The single-assignment payoff, packaged as a preorder on register files: the
construction only ever `set`s ids it has just allocated, so every step of the
translation *extends* the register file and every fact `R x = some v`
survives (`Regs.Le`). -/

namespace Regs

/-- `Le R R'`: `R'` agrees with `R` wherever `R` is defined. -/
def Le (R R' : Regs) : Prop := ∀ x v, R x = some v → R' x = some v

theorem Le.rfl (R : Regs) : Le R R := fun _ _ h => h

theorem Le.trans {R₁ R₂ R₃ : Regs} (h₁ : Le R₁ R₂) (h₂ : Le R₂ R₃) : Le R₁ R₃ :=
  fun x v h => h₂ x v (h₁ x v h)

/-- Binding a *fresh* id extends the register file. -/
theorem Le.set {R : Regs} {x : ValId} (v : U256) (hfresh : R x = none) :
    Le R (R.set x v) := by
  intro y w hy
  by_cases hxy : y = x
  · exact absurd (hxy ▸ hy) (by rw [hfresh]; simp)
  · rw [set_other R v hxy]; exact hy

/-! ### `getMany` -/

theorem getMany_eq_some_iff {R : Regs} {xs : List ValId} {vs : List U256} :
    R.getMany xs = some vs ↔ List.Forall₂ (fun x v => R x = some v) xs vs := by
  constructor
  · induction xs generalizing vs with
    | nil => intro h; rw [getMany_nil] at h; cases h; exact .nil
    | cons x xs ih =>
      intro h
      rw [getMany_cons] at h
      cases hx : R x with
      | none => rw [hx] at h; simp at h
      | some v =>
        rw [hx] at h
        simp only [Option.bind_some] at h
        cases hxs : R.getMany xs with
        | none => rw [hxs] at h; simp at h
        | some ws =>
          rw [hxs] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          exact .cons hx (ih hxs)
  · intro h
    induction h with
    | nil => rfl
    | cons hh ht ih => rw [getMany_cons, hh, ih]; simp

/-- `getMany` only looks at the listed ids, so every extension agrees. -/
theorem getMany_mono {R R' : Regs} (h : Le R R') {xs : List ValId}
    {vs : List U256} (hg : R.getMany xs = some vs) : R'.getMany xs = some vs := by
  rw [getMany_eq_some_iff] at hg ⊢
  exact Forall2.imp (fun x v hxv => h x v hxv) hg

theorem getMany_append {R : Regs} {xs ys : List ValId} {vs ws : List U256}
    (hx : R.getMany xs = some vs) (hy : R.getMany ys = some ws) :
    R.getMany (xs ++ ys) = some (vs ++ ws) := by
  rw [getMany_eq_some_iff] at hx hy ⊢
  exact Forall2.append hx hy

theorem getMany_length {R : Regs} {xs : List ValId} {vs : List U256}
    (h : R.getMany xs = some vs) : xs.length = vs.length :=
  Forall2.length_eq (getMany_eq_some_iff.mp h)

/-! ### `setMany` -/

@[simp] theorem setMany_nil (R : Regs) (vs : List U256) : R.setMany [] vs = R := rfl

@[simp] theorem setMany_nil_right (R : Regs) (xs : List ValId) :
    R.setMany xs [] = R := by
  cases xs <;> rfl

theorem setMany_cons (R : Regs) (x : ValId) (xs : List ValId) (v : U256)
    (vs : List U256) :
    R.setMany (x :: xs) (v :: vs) = (R.set x v).setMany xs vs := by
  simp only [setMany, List.zip_cons_cons, List.foldl_cons]

/-- Ids outside the bound list are untouched. -/
theorem setMany_other : ∀ {xs : List ValId} {vs : List U256} {R : Regs} {y : ValId},
    y ∉ xs → (R.setMany xs vs) y = R y := by
  intro xs
  induction xs with
  | nil => intro vs R y _; rfl
  | cons x xs ih =>
    intro vs R y hy
    cases vs with
    | nil => rfl
    | cons v vs =>
      have hyx : y ≠ x := fun h => hy (by rw [h]; exact List.mem_cons_self ..)
      have hyxs : y ∉ xs := fun h => hy (List.mem_cons_of_mem _ h)
      rw [setMany_cons, ih hyxs, set_other R v hyx]

/-- Binding a list of pairwise-distinct fresh ids extends the register file. -/
theorem Le.setMany : ∀ {xs : List ValId} {vs : List U256} {R : Regs},
    xs.Nodup → (∀ x ∈ xs, R x = none) → Le R (R.setMany xs vs) := by
  intro xs
  induction xs with
  | nil => intro vs R _ _; exact Le.rfl _
  | cons x xs ih =>
    intro vs R hnd hfresh
    cases vs with
    | nil => exact Le.rfl _
    | cons v vs =>
      have hxni : x ∉ xs := (List.nodup_cons.mp hnd).1
      have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
      rw [setMany_cons]
      refine Le.trans (Le.set v (hfresh x (List.mem_cons_self ..))) (ih hnd' ?_)
      intro y hy
      have hyx : y ≠ x := fun h => hxni (h ▸ hy)
      rw [set_other R v hyx]
      exact hfresh y (List.mem_cons_of_mem _ hy)

/-- Reading back a freshly bound parameter list. -/
theorem getMany_setMany_self : ∀ {xs : List ValId} {vs : List U256} {R : Regs},
    xs.Nodup → xs.length = vs.length → (R.setMany xs vs).getMany xs = some vs := by
  intro xs
  induction xs with
  | nil =>
    intro vs R _ hlen
    cases vs with
    | nil => rfl
    | cons _ _ => exact absurd hlen (by simp)
  | cons x xs ih =>
    intro vs R hnd hlen
    cases vs with
    | nil => exact absurd hlen (by simp)
    | cons v vs =>
      have hxni : x ∉ xs := (List.nodup_cons.mp hnd).1
      have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
      rw [setMany_cons, getMany_cons, setMany_other hxni, set_same,
        ih hnd' (by simpa using hlen)]
      simp

end Regs

end YulEvmCompiler.SsaCfg
