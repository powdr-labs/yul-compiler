import YulEvmCompiler.SsaCfg.Spec.Sem
import YulEvmCompiler.SsaCfg.Implementation.OfYul
import YulSemantics.BigStep
/-!
# YulEvmCompiler.SsaCfg.Implementation.OfYulSound

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

/-- An all-or-nothing `mapM` succeeds exactly when it succeeds pointwise. Used
for both `Regs.getMany` (`mapM R`) and `edgeArgs` (`mapM env.get`). -/
theorem mapM_eq_some_iff {f : α → Option β} :
    ∀ {xs : List α} {ys : List β},
      xs.mapM f = some ys ↔ List.Forall₂ (fun x y => f x = some y) xs ys := by
  intro xs ys
  constructor
  · induction xs generalizing ys with
    | nil => intro h; simp only [List.mapM_nil, Option.pure_def] at h
             cases h; exact .nil
    | cons x xs ih =>
      intro h
      rw [List.mapM_cons] at h
      cases hx : f x with
      | none => rw [hx] at h; simp at h
      | some y =>
        rw [hx] at h
        cases hxs : xs.mapM f with
        | none => rw [hxs] at h; simp at h
        | some ws =>
          rw [hxs] at h
          obtain rfl : ys = y :: ws := by simpa using h.symm
          exact .cons hx (ih hxs)
  · intro h
    induction h with
    | nil => rfl
    | cons hh _ ih => rw [List.mapM_cons, hh, ih]; simp

theorem refl {r : α → α → Prop} (h : ∀ a, r a a) : ∀ l : List α, List.Forall₂ r l l := by
  intro l
  induction l with
  | nil => exact .nil
  | cons a l ih => exact .cons (h a) ih

theorem trans' {γ : Type} {r : α → β → Prop} {t : β → γ → Prop} {u : α → γ → Prop}
    (hc : ∀ a b c, r a b → t b c → u a c) :
    ∀ {l₁ : List α} {l₂ : List β} {l₃ : List γ},
      List.Forall₂ r l₁ l₂ → List.Forall₂ t l₂ l₃ → List.Forall₂ u l₁ l₃ := by
  intro l₁ l₂ l₃ h₁ h₂
  induction h₁ generalizing l₃ with
  | nil => cases h₂; exact .nil
  | cons hh ht ih =>
    cases h₂ with
    | cons hh2 ht2 => exact .cons (hc _ _ _ hh hh2) (ih ht2)

theorem imp_mem {r s : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ r l₁ l₂ →
      (∀ a ∈ l₁, ∀ b, r a b → s a b) → List.Forall₂ s l₁ l₂ := by
  intro l₁ l₂ h
  induction h with
  | nil => intro _; exact .nil
  | @cons a b l₁' l₂' hh _ ih =>
    intro hs
    exact .cons (hs a (List.mem_cons_self ..) b hh)
      (ih (fun y hy c hc => hs y (List.mem_cons_of_mem _ hy) c hc))

end Forall2

theorem lt_size_of_getElem? {α : Type} {a : Array α} {i : Nat} {x : α}
    (h : a[i]? = some x) : i < a.size := by
  by_contra hc
  rw [Array.getElem?_eq_none (by omega)] at h
  exact absurd h (by simp)

/-! ## Register files

The single-assignment payoff, packaged as a preorder on register files: the
construction only ever `set`s ids it has just allocated, so every step of the
translation *extends* the register file and every fact `R x = some v`
survives (`Regs.Le`). -/

namespace Regs

/-- `Le R R'`: `R'` agrees with `R` wherever `R` is defined. -/
def Le (R R' : Regs) : Prop := ∀ x v, R x = some v → R' x = some v

/-- `BelowEq n R R'`: a translated fragment has not written any register
strictly below its entry `nextVal` watermark `n`.  Unlike `Le`, this also
preserves registers that were unbound at entry; reserved join parameters rely
on exactly that negative information. -/
def BelowEq (n : Nat) (R R' : Regs) : Prop := ∀ i, i < n → R' i = R i

theorem BelowEq.rfl (n : Nat) (R : Regs) : BelowEq n R R :=
  fun _ _ => Eq.refl _

theorem BelowEq.trans {n : Nat} {R₁ R₂ R₃ : Regs}
    (h₁ : BelowEq n R₁ R₂) (h₂ : BelowEq n R₂ R₃) :
    BelowEq n R₁ R₃ := fun i hi => (h₂ i hi).trans (h₁ i hi)

theorem BelowEq.mono {n m : Nat} {R R' : Regs} (h : BelowEq m R R')
    (hnm : n ≤ m) : BelowEq n R R' :=
  fun i hi => h i (Nat.lt_of_lt_of_le hi hnm)

theorem BelowEq.set {n : Nat} {R : Regs} {x : ValId} (v : U256)
    (hnx : n ≤ x) : BelowEq n R (R.set x v) := by
  intro i hi
  rw [set_other R v (Nat.ne_of_lt (Nat.lt_of_lt_of_le hi hnx))]

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

/-- Applying the same binding to two related register files preserves the
extension relation. -/
theorem Le.setBoth {R R' : Regs} (h : Le R R') (x : ValId) (v : U256) :
    Le (R.set x v) (R'.set x v) := by
  intro y w hy
  by_cases hyx : y = x
  · subst y
    simpa using hy
  · rw [set_other R' v hyx]
    rw [set_other R v hyx] at hy
    exact h y w hy

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

theorem set_set (R : Regs) (x : ValId) (v w : U256) :
    (R.set x v).set x w = R.set x w := by
  funext y
  by_cases h : y = x
  · subst y; simp
  · rw [set_other, set_other, set_other] <;> exact h

theorem set_comm (R : Regs) {x y : ValId} (hxy : x ≠ y) (v w : U256) :
    (R.set x v).set y w = (R.set y w).set x v := by
  funext z
  by_cases hzx : z = x
  · subst z
    rw [set_other _ _ hxy, set_same, set_same]
  · by_cases hzy : z = y
    · subst z
      rw [set_same, set_other _ _ (Ne.symm hxy), set_same]
    · rw [set_other _ _ hzy, set_other _ _ hzx,
        set_other _ _ hzx, set_other _ _ hzy]

theorem setMany_comm (R : Regs) {x : ValId} {xs : List ValId}
    (hx : x ∉ xs) (v : U256) (vs : List U256) :
    (R.set x v).setMany xs vs = (R.setMany xs vs).set x v := by
  induction xs generalizing R vs with
  | nil => simp
  | cons y ys ih =>
    cases vs with
    | nil => simp
    | cons w ws =>
      have hxy : x ≠ y := fun h => hx (h ▸ List.mem_cons_self ..)
      have hxn : x ∉ ys := fun h => hx (List.mem_cons_of_mem _ h)
      rw [setMany_cons, setMany_cons, set_comm _ hxy, ih _ hxn]

theorem setMany_overwrite (R : Regs) {xs : List ValId} {vs ws : List U256}
    (hnd : xs.Nodup) (hlv : xs.length = vs.length)
    (hlw : xs.length = ws.length) :
    (R.setMany xs vs).setMany xs ws = R.setMany xs ws := by
  induction xs generalizing R vs ws with
  | nil => simp
  | cons x xs ih =>
    cases vs with
    | nil => simp at hlv
    | cons v vs =>
      cases ws with
      | nil => simp at hlw
      | cons w ws =>
        have hx : x ∉ xs := (List.nodup_cons.mp hnd).1
        have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
        have hlv' : xs.length = vs.length := by simpa using hlv
        have hlw' : xs.length = ws.length := by simpa using hlw
        calc
          ((R.setMany (x :: xs) (v :: vs)).setMany (x :: xs) (w :: ws)) =
              (((R.set x v).setMany xs vs).set x w).setMany xs ws := by
                rw [setMany_cons, setMany_cons]
          _ = (((R.set x v).set x w).setMany xs vs).setMany xs ws := by
                rw [setMany_comm (R.set x v) hx]
          _ = ((R.set x w).setMany xs vs).setMany xs ws := by rw [set_set]
          _ = (R.set x w).setMany xs ws := ih _ hnd' hlv' hlw'
          _ = R.setMany (x :: xs) (w :: ws) := by rw [setMany_cons]

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

theorem BelowEq.setMany {n : Nat} {R : Regs} {xs : List ValId}
    {vs : List U256} (hxs : ∀ x ∈ xs, n ≤ x) :
    BelowEq n R (R.setMany xs vs) := by
  intro i hi
  rw [setMany_other]
  intro himem
  exact absurd (Nat.lt_of_lt_of_le hi (hxs i himem)) (Nat.lt_irrefl i)

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

/-- Applying the same list of bindings to related files preserves the
extension relation. -/
theorem Le.setManyBoth : ∀ {xs : List ValId} {vs : List U256} {R R' : Regs},
    Le R R' → Le (R.setMany xs vs) (R'.setMany xs vs) := by
  intro xs
  induction xs with
  | nil => intro vs R R' h; simpa using h
  | cons x xs ih =>
    intro vs R R' h
    cases vs with
    | nil => simpa using h
    | cons v vs =>
      rw [setMany_cons, setMany_cons]
      exact ih (h.setBoth x v)

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

/-- Every id of a freshly zero-initialised block reads back `0`. -/
theorem setMany_replicate_mem : ∀ {xs : List ValId} {R : Regs},
    xs.Nodup → ∀ i ∈ xs,
      (R.setMany xs (List.replicate xs.length (0 : U256))) i = some 0 := by
  intro xs
  induction xs with
  | nil => intro R _ i hi; exact absurd hi (by simp)
  | cons x xs ih =>
    intro R hnd i hi
    have hxni : x ∉ xs := (List.nodup_cons.mp hnd).1
    rw [List.length_cons, List.replicate_succ, setMany_cons]
    rcases List.mem_cons.mp hi with rfl | hmem
    · rw [setMany_other hxni, set_same]
    · exact ih (List.nodup_cons.mp hnd).2 i hmem

end Regs

/-! ## `VMap` scoping lemmas

`VMap` is definitionally the `VEnv` discipline with `ValId`s in place of
values, so each `VEnv` operation has a `VMap` twin; these are the shape
lemmas both sides need. -/

namespace VMap

@[simp] theorem get_nil (x : Ident) : VMap.get [] x = none := rfl

theorem get_cons (p : Ident × ValId) (m : VMap) (x : Ident) :
    VMap.get (p :: m) x = if p.1 = x then some p.2 else VMap.get m x := by
  unfold VMap.get
  rw [List.find?_cons]
  by_cases h : p.1 = x <;> simp [h]

@[simp] theorem setMany_nil (m : VMap) (is : List ValId) : m.setMany [] is = m := rfl

@[simp] theorem setMany_nil_right (m : VMap) (xs : List Ident) :
    m.setMany xs [] = m := by cases xs <;> rfl

theorem setMany_cons (m : VMap) (x : Ident) (xs : List Ident) (i : ValId)
    (is : List ValId) : m.setMany (x :: xs) (i :: is) = (m.set x i).setMany xs is := by
  simp only [setMany, List.zip_cons_cons, List.foldl_cons]

theorem set_set (m : VMap) (x : Ident) (i j : ValId) :
    (m.set x i).set x j = m.set x j := by
  induction m with
  | nil => rfl
  | cons p m ih =>
    by_cases h : p.1 = x
    · simp [VMap.set, h]
    · simp [VMap.set, h, ih]

theorem set_comm (m : VMap) {x y : Ident} (hxy : x ≠ y) (i j : ValId) :
    (m.set x i).set y j = (m.set y j).set x i := by
  induction m with
  | nil => rfl
  | cons p m ih =>
    by_cases hx : p.1 = x
    · have hy : p.1 ≠ y := fun h => hxy (hx.symm.trans h)
      simp [VMap.set, hx, hy, hxy]
    · by_cases hy : p.1 = y
      · simp [VMap.set, hx, hy, hxy, Ne.symm hxy]
      · simp [VMap.set, hx, hy, ih]

theorem setMany_comm (m : VMap) {x : Ident} {xs : List Ident}
    (hx : x ∉ xs) (i : ValId) (is : List ValId) :
    (m.set x i).setMany xs is = (m.setMany xs is).set x i := by
  induction xs generalizing m is with
  | nil => simp
  | cons y ys ih =>
    cases is with
    | nil => simp
    | cons j js =>
      have hxy : x ≠ y := fun h => hx (h ▸ List.mem_cons_self ..)
      have hxn : x ∉ ys := fun h => hx (List.mem_cons_of_mem _ h)
      rw [setMany_cons, setMany_cons, set_comm _ hxy, ih _ hxn]

theorem setMany_overwrite (m : VMap) {xs : List Ident} {is js : List ValId}
    (hnd : xs.Nodup) (hli : xs.length = is.length)
    (hlj : xs.length = js.length) :
    (m.setMany xs is).setMany xs js = m.setMany xs js := by
  induction xs generalizing m is js with
  | nil => simp
  | cons x xs ih =>
    cases is with
    | nil => simp at hli
    | cons i is =>
      cases js with
      | nil => simp at hlj
      | cons j js =>
        have hx : x ∉ xs := (List.nodup_cons.mp hnd).1
        have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
        have hli' : xs.length = is.length := by simpa using hli
        have hlj' : xs.length = js.length := by simpa using hlj
        calc
          ((m.setMany (x :: xs) (i :: is)).setMany (x :: xs) (j :: js)) =
              (((m.set x i).setMany xs is).set x j).setMany xs js := by
                rw [setMany_cons, setMany_cons]
          _ = (((m.set x i).set x j).setMany xs is).setMany xs js := by
                rw [setMany_comm (m.set x i) hx]
          _ = ((m.set x j).setMany xs is).setMany xs js := by rw [set_set]
          _ = (m.set x j).setMany xs js := ih _ hnd' hli' hlj'
          _ = m.setMany (x :: xs) (j :: js) := by rw [setMany_cons]

theorem length_set : ∀ (m : VMap) (x : Ident) (i : ValId), (m.set x i).length = m.length := by
  intro m x i
  induction m with
  | nil => rfl
  | cons p m ih =>
    by_cases h : p.1 = x
    · simp [VMap.set, h]
    · simp [VMap.set, h, ih]

theorem length_setMany : ∀ {xs : List Ident} {is : List ValId} {m : VMap},
    (m.setMany xs is).length = m.length := by
  intro xs
  induction xs with
  | nil => intro is m; rfl
  | cons x xs ih =>
    intro is m
    cases is with
    | nil => rfl
    | cons i is => rw [setMany_cons, ih, length_set]

/-- The construction's visible-variable invariant: every currently visible
name occurs exactly once.  `trStmt` preserves this by rejecting shadowing. -/
def Unique (m : VMap) : Prop := (m.map Prod.fst).Nodup

@[simp] theorem unique_nil : Unique ([] : VMap) := by simp [Unique]

theorem eraseDups_names_eq_self {m : VMap} (h : m.Unique) :
    (m.map Prod.fst).eraseDups = m.map Prod.fst := by
  have aux : ∀ l : List Ident, l.Nodup → l.eraseDups = l := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.eraseDups_cons]
      have hn := List.nodup_cons.mp hl
      have hf : l.filter (fun b => !b == a) = l := by
        apply List.filter_eq_self.mpr
        intro b hb
        change (!(b == a)) = true
        rw [Bool.not_eq_true']
        exact beq_eq_false_iff_ne.mpr (fun he => hn.1 (he ▸ hb))
      rw [hf, ih hn.2]
  exact aux _ h

theorem names_set : ∀ (m : VMap) (x : Ident) (i : ValId),
    (m.set x i).map Prod.fst = m.map Prod.fst := by
  intro m x i
  induction m with
  | nil => rfl
  | cons p m ih =>
    by_cases h : p.1 = x
    · simp [VMap.set, h]
    · simp [VMap.set, h, ih]

theorem names_setMany : ∀ (m : VMap) (xs : List Ident) (is : List ValId),
    (m.setMany xs is).map Prod.fst = m.map Prod.fst := by
  intro m xs
  induction xs generalizing m with
  | nil => intro is; rfl
  | cons x xs ih =>
    intro is
    cases is with
    | nil => rfl
    | cons i is => rw [setMany_cons, ih, names_set]

theorem Unique.setMany {m : VMap} (h : m.Unique) (xs : List Ident)
    (is : List ValId) : (m.setMany xs is).Unique := by
  rw [Unique, names_setMany]
  exact h

theorem Unique.drop {m : VMap} (h : m.Unique) (n : Nat) : Unique (m.drop n) := by
  rw [Unique, List.map_drop]
  exact List.Pairwise.drop h

/-- Prepending a declaration group preserves uniqueness when the construction's
two declaration gates (no visible collision, no duplicate in the group) pass. -/
theorem Unique.zip_append {m : VMap} {vars : List Ident} {ids : List ValId}
    (hm : m.Unique) (hv : vars.Nodup) (hdis : ∀ x ∈ vars, m.mem x = false)
    (hlen : vars.length = ids.length) : Unique (vars.zip ids ++ m) := by
  rw [Unique, List.map_append, List.map_fst_zip]
  · exact List.Nodup.append hv hm (by
      intro x hxv hxm
      have : m.mem x = true := by
        simp only [VMap.mem, List.any_eq_true]
        obtain ⟨p, hp, he⟩ := List.mem_map.mp hxm
        exact ⟨p, hp, by simpa using he⟩
      rw [hdis x hxv] at this
      cases this)
  · omega

/-- `get` succeeds exactly on the visible names (`mem`, the no-shadowing gate). -/
theorem get_isSome_iff_mem (m : VMap) (x : Ident) :
    (VMap.get m x).isSome = m.mem x := by
  simp only [VMap.mem]
  induction m with
  | nil => rfl
  | cons p m ih =>
    rw [get_cons, List.any_cons]
    by_cases h : p.1 = x
    · simp [h]
    · simpa [h] using ih

theorem exists_get_of_mem {m : VMap} {x : Ident} (h : m.mem x = true) :
    ∃ i, VMap.get m x = some i := by
  have := get_isSome_iff_mem m x
  rw [h] at this
  exact Option.isSome_iff_exists.mp this

end VMap

namespace VEnv

open YulSemantics (VEnv)

variable {D : YulSemantics.Dialect}

theorem get_cons (p : Ident × D.Value) (V : VEnv D) (x : Ident) :
    YulSemantics.VEnv.get (p :: V) x
      = if p.1 = x then some p.2 else YulSemantics.VEnv.get V x := by
  unfold YulSemantics.VEnv.get
  rw [List.find?_cons]
  by_cases h : p.1 = x <;> simp [h]

@[simp] theorem setMany_nil (V : VEnv D) (vs : List D.Value) :
    YulSemantics.VEnv.setMany V [] vs = V := rfl

@[simp] theorem setMany_nil_right (V : VEnv D) (xs : List Ident) :
    YulSemantics.VEnv.setMany V xs [] = V := by cases xs <;> rfl

theorem setMany_cons (V : VEnv D) (x : Ident) (xs : List Ident) (v : D.Value)
    (vs : List D.Value) :
    YulSemantics.VEnv.setMany V (x :: xs) (v :: vs)
      = YulSemantics.VEnv.setMany (YulSemantics.VEnv.set V x v) xs vs := by
  simp only [YulSemantics.VEnv.setMany, List.zip_cons_cons, List.foldl_cons]

theorem set_set (V : VEnv D) (x : Ident) (v w : D.Value) :
    YulSemantics.VEnv.set (YulSemantics.VEnv.set V x v) x w =
      YulSemantics.VEnv.set V x w := by
  induction V with
  | nil => rfl
  | cons p V ih =>
    by_cases h : p.1 = x
    · simp [YulSemantics.VEnv.set, h]
    · simp [YulSemantics.VEnv.set, h, ih]

theorem set_comm (V : VEnv D) {x y : Ident} (hxy : x ≠ y)
    (v w : D.Value) :
    YulSemantics.VEnv.set (YulSemantics.VEnv.set V x v) y w =
      YulSemantics.VEnv.set (YulSemantics.VEnv.set V y w) x v := by
  induction V with
  | nil => rfl
  | cons p V ih =>
    by_cases hx : p.1 = x
    · have hy : p.1 ≠ y := fun h => hxy (hx.symm.trans h)
      simp [YulSemantics.VEnv.set, hx, hy, hxy]
    · by_cases hy : p.1 = y
      · simp [YulSemantics.VEnv.set, hx, hy, hxy, Ne.symm hxy]
      · simp [YulSemantics.VEnv.set, hx, hy, ih]

theorem setMany_comm (V : VEnv D) {x : Ident} {xs : List Ident}
    (hx : x ∉ xs) (v : D.Value) (vs : List D.Value) :
    YulSemantics.VEnv.setMany (YulSemantics.VEnv.set V x v) xs vs =
      YulSemantics.VEnv.set (YulSemantics.VEnv.setMany V xs vs) x v := by
  induction xs generalizing V vs with
  | nil => simp
  | cons y ys ih =>
    cases vs with
    | nil => simp
    | cons w ws =>
      have hxy : x ≠ y := fun h => hx (h ▸ List.mem_cons_self ..)
      have hxn : x ∉ ys := fun h => hx (List.mem_cons_of_mem _ h)
      rw [setMany_cons, setMany_cons, set_comm _ hxy, ih _ hxn]

theorem setMany_overwrite (V : VEnv D) {xs : List Ident}
    {vs ws : List D.Value} (hnd : xs.Nodup) (hlv : xs.length = vs.length)
    (hlw : xs.length = ws.length) :
    YulSemantics.VEnv.setMany (YulSemantics.VEnv.setMany V xs vs) xs ws =
      YulSemantics.VEnv.setMany V xs ws := by
  induction xs generalizing V vs ws with
  | nil => simp
  | cons x xs ih =>
    cases vs with
    | nil => simp at hlv
    | cons v vs =>
      cases ws with
      | nil => simp at hlw
      | cons w ws =>
        have hx : x ∉ xs := (List.nodup_cons.mp hnd).1
        have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
        have hlv' : xs.length = vs.length := by simpa using hlv
        have hlw' : xs.length = ws.length := by simpa using hlw
        calc
          YulSemantics.VEnv.setMany
              (YulSemantics.VEnv.setMany V (x :: xs) (v :: vs))
              (x :: xs) (w :: ws) =
              YulSemantics.VEnv.setMany
                (YulSemantics.VEnv.set
                  (YulSemantics.VEnv.setMany
                    (YulSemantics.VEnv.set V x v) xs vs) x w) xs ws := by
                    rw [setMany_cons, setMany_cons]
          _ = YulSemantics.VEnv.setMany
                (YulSemantics.VEnv.setMany
                  (YulSemantics.VEnv.set
                    (YulSemantics.VEnv.set V x v) x w) xs vs) xs ws := by
                  rw [setMany_comm (YulSemantics.VEnv.set V x v) hx]
          _ = YulSemantics.VEnv.setMany
                (YulSemantics.VEnv.setMany
                  (YulSemantics.VEnv.set V x w) xs vs) xs ws := by rw [set_set]
          _ = YulSemantics.VEnv.setMany
                (YulSemantics.VEnv.set V x w) xs ws := ih _ hnd' hlv' hlw'
          _ = YulSemantics.VEnv.setMany V (x :: xs) (w :: ws) := by
                rw [setMany_cons]

/-! ### Names, in-place update, and scope exit

The structural facts behind the `modStmts` analysis: execution only *prepends*
to the environment and updates existing bindings *in place*, so the name list of
the visible prefix never changes and `restore` really does undo a scope. -/

/-- The names bound by an environment, innermost first. -/
def names (V : VEnv D) : List Ident := V.map Prod.fst

@[simp] theorem names_nil : names ([] : VEnv D) = [] := rfl

@[simp] theorem names_cons (p : Ident × D.Value) (V : VEnv D) :
    names (p :: V) = p.1 :: names V := rfl

@[simp] theorem length_names (V : VEnv D) : (names V).length = V.length := by
  simp [names]

theorem names_append (A B : VEnv D) : names (A ++ B) = names A ++ names B := by
  simp [names]

theorem names_set : ∀ (V : VEnv D) (x : Ident) (v : D.Value),
    names (YulSemantics.VEnv.set V x v) = names V := by
  intro V
  induction V with
  | nil => intro x v; rfl
  | cons p V ih =>
    intro x v
    obtain ⟨pn, pv⟩ := p
    rw [YulSemantics.VEnv.set]
    by_cases h : pn = x
    · rw [if_pos h, names_cons, names_cons, h]
    · rw [if_neg h, names_cons, names_cons, ih]

theorem length_set (V : VEnv D) (x : Ident) (v : D.Value) :
    (YulSemantics.VEnv.set V x v).length = V.length := by
  rw [← length_names, ← length_names, names_set]

theorem names_setMany : ∀ {xs : List Ident} {vs : List D.Value} {V : VEnv D},
    names (YulSemantics.VEnv.setMany V xs vs) = names V := by
  intro xs
  induction xs with
  | nil => intro vs V; rfl
  | cons x xs ih =>
    intro vs V
    cases vs with
    | nil => rfl
    | cons v vs => rw [setMany_cons, ih, names_set]

theorem length_setMany {xs : List Ident} {vs : List D.Value} {V : VEnv D} :
    (YulSemantics.VEnv.setMany V xs vs).length = V.length := by
  rw [← length_names, ← length_names, names_setMany]

/-- `set` updates the *innermost* binding, so any other name reads back
unchanged. -/
theorem get_set_ne : ∀ (V : VEnv D) {x y : Ident} (v : D.Value), y ≠ x →
    YulSemantics.VEnv.get (YulSemantics.VEnv.set V x v) y
      = YulSemantics.VEnv.get V y := by
  intro V
  induction V with
  | nil => intro x y v _; rfl
  | cons p V ih =>
    intro x y v h
    obtain ⟨pn, pv⟩ := p
    rw [YulSemantics.VEnv.set]
    by_cases hp : pn = x
    · rw [if_pos hp, get_cons, get_cons]
      simp only []
      rw [if_neg (by simpa using Ne.symm h), if_neg (by rw [hp]; exact Ne.symm h)]
    · rw [if_neg hp, get_cons, get_cons]
      by_cases hq : pn = y
      · rw [if_pos hq, if_pos hq]
      · rw [if_neg hq, if_neg hq, ih v h]

theorem get_setMany_not_mem : ∀ {xs : List Ident} {vs : List D.Value}
    {V : VEnv D} {y : Ident}, y ∉ xs →
    YulSemantics.VEnv.get (YulSemantics.VEnv.setMany V xs vs) y
      = YulSemantics.VEnv.get V y := by
  intro xs
  induction xs with
  | nil => intro vs V y _; rfl
  | cons x xs ih =>
    intro vs V y hy
    cases vs with
    | nil => rfl
    | cons v vs =>
      have hyx : y ≠ x := fun hh => hy (by rw [hh]; exact List.mem_cons_self ..)
      rw [setMany_cons, ih (fun hh => hy (List.mem_cons_of_mem _ hh)),
        get_set_ne V v hyx]

/-- Updating a bound name makes its visible value the supplied one. -/
theorem get_set_of_mem : ∀ (V : VEnv D) (x : Ident) (v : D.Value),
    x ∈ names V → YulSemantics.VEnv.get (YulSemantics.VEnv.set V x v) x = some v := by
  intro V
  induction V with
  | nil => intro x v hx; simp at hx
  | cons p V ih =>
    intro x v hx
    obtain ⟨pn, pv⟩ := p
    rw [YulSemantics.VEnv.set]
    by_cases h : pn = x
    · subst pn; simp [get_cons]
    · rw [if_neg h, get_cons]
      simp only [Prod.fst]
      rw [if_neg h]
      exact ih x v (by
        rcases List.mem_cons.mp hx with he | he
        · exact absurd he.symm h
        · exact he)

/-- Applying the same complete, duplicate-free update list gives the same
visible value at every updated name, independently of the old values. -/
theorem get_setMany_congr_of_mem : ∀ {xs : List Ident} {vs : List D.Value}
    {V W : VEnv D} {x : Ident}, xs.length = vs.length → x ∈ xs →
    x ∈ names V → x ∈ names W →
    YulSemantics.VEnv.get (YulSemantics.VEnv.setMany V xs vs) x =
      YulSemantics.VEnv.get (YulSemantics.VEnv.setMany W xs vs) x := by
  intro xs
  induction xs with
  | nil => intro vs V W x _ hx _ _; exact absurd hx (by simp)
  | cons y ys ih =>
    intro vs V W x hlen hx hV hW
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      rw [setMany_cons, setMany_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · by_cases hy : x ∈ ys
        · exact ih (by simpa using hlen) hy
            (by rw [names_set]; exact hV) (by rw [names_set]; exact hW)
        · rw [get_setMany_not_mem hy, get_setMany_not_mem hy,
            get_set_of_mem V x v hV, get_set_of_mem W x v hW]
      · exact ih (by simpa using hlen) hx
          (by rw [names_set]; exact hV) (by rw [names_set]; exact hW)

/-- Environments with the same duplicate-free name spine are equal once every
visible lookup agrees. -/
theorem eq_of_names_get : ∀ {V W : VEnv D}, (names V).Nodup → names V = names W →
    (∀ x ∈ names V, YulSemantics.VEnv.get V x = YulSemantics.VEnv.get W x) →
    V = W := by
  intro V
  induction V with
  | nil =>
    intro W _ hn _
    cases W with
    | nil => rfl
    | cons q W => simp [names] at hn
  | cons p V ih =>
    intro W hnd hn hg
    cases W with
    | nil => simp [names] at hn
    | cons q W =>
      obtain ⟨pn, pv⟩ := p
      obtain ⟨qn, qv⟩ := q
      simp only [names_cons, List.cons.injEq] at hn
      obtain ⟨rfl, hn⟩ := hn
      have hpv : pv = qv := by
        have hh := hg pn (by simp)
        rw [get_cons, get_cons, if_pos rfl, if_pos rfl] at hh
        exact Option.some.inj hh
      subst qv
      congr 1
      exact ih (List.nodup_cons.mp hnd).2 hn (by
        intro x hx
        have hne : pn ≠ x := fun he => (List.nodup_cons.mp hnd).1 (he ▸ hx)
        have hh := hg x (List.mem_cons_of_mem _ hx)
        simpa [get_cons, hne] using hh)

/-- Lookup skips a prefix that does not bind the name. -/
theorem get_append_of_not_mem : ∀ {A : VEnv D} {B : VEnv D} {x : Ident},
    x ∉ names A →
    YulSemantics.VEnv.get (A ++ B) x = YulSemantics.VEnv.get B x := by
  intro A
  induction A with
  | nil => intro B x _; rfl
  | cons p A ih =>
    intro B x hx
    rw [List.cons_append, get_cons,
      if_neg (fun hh => hx (by rw [names_cons, hh]; exact List.mem_cons_self ..))]
    exact ih (fun hh => hx (List.mem_cons_of_mem _ hh))

/-- `set` only ever changes a position whose name is the one being set. -/
theorem set_positional : ∀ (V : VEnv D) (x : Ident) (v : D.Value),
    List.Forall₂ (fun (p q : Ident × D.Value) => p.1 = q.1 ∧ (q.2 = p.2 ∨ p.1 = x))
      V (YulSemantics.VEnv.set V x v) := by
  intro V
  induction V with
  | nil => intro x v; exact .nil
  | cons p V ih =>
    intro x v
    obtain ⟨pn, pv⟩ := p
    rw [YulSemantics.VEnv.set]
    by_cases h : pn = x
    · exact (if_pos h) ▸ List.Forall₂.cons ⟨h, Or.inr h⟩
        (Forall2.refl (fun _ => ⟨rfl, Or.inl rfl⟩) V)
    · exact (if_neg h) ▸ List.Forall₂.cons ⟨rfl, Or.inl rfl⟩ (ih x v)

/-- If the name being set is bound in the first `k` entries, `set` updates *that*
binding and leaves everything past `k` alone. -/
theorem set_drop_of_mem_take : ∀ (V : VEnv D) (x : Ident) (v : D.Value) (k : Nat),
    x ∈ names (V.take k) →
    (YulSemantics.VEnv.set V x v).drop k = V.drop k := by
  intro V
  induction V with
  | nil => intro x v k hx; simp at hx
  | cons p V ih =>
    intro x v k hx
    cases k with
    | zero => simp at hx
    | succ k =>
      obtain ⟨pn, pv⟩ := p
      rw [List.take_succ_cons, names_cons] at hx
      rw [YulSemantics.VEnv.set]
      by_cases h : pn = x
      · rw [if_pos h]; simp
      · rw [if_neg h]
        rw [List.drop_succ_cons, List.drop_succ_cons]
        exact ih x v k (by
          rcases List.mem_cons.mp hx with rfl | hm
          · exact absurd rfl h
          · exact hm)

/-- Re-setting a binding to the value it already holds is a no-op. -/
theorem set_get_self : ∀ {V : VEnv D} {x : Ident} {v : D.Value},
    YulSemantics.VEnv.get V x = some v → YulSemantics.VEnv.set V x v = V := by
  intro V
  induction V with
  | nil => intro x v _; rfl
  | cons p V ih =>
    intro x v hg
    obtain ⟨pn, pv⟩ := p
    rw [get_cons] at hg
    rw [YulSemantics.VEnv.set]
    by_cases h : pn = x
    · rw [if_pos h] at hg ⊢
      obtain rfl : pv = v := Option.some.inj hg
      rw [h]
    · rw [if_neg h] at hg ⊢
      rw [ih hg]

/-- Assigning a list of variables their current values is a no-op — the
`if`-false and loop-exit edges pass exactly these. -/
theorem setMany_self {V : VEnv D} : ∀ {xs : List Ident} {vs : List D.Value},
    List.Forall₂ (fun x v => YulSemantics.VEnv.get V x = some v) xs vs →
    YulSemantics.VEnv.setMany V xs vs = V := by
  intro xs
  induction xs with
  | nil => intro vs _; rfl
  | cons x xs ih =>
    intro vs h
    cases h with
    | @cons v vs' _ _ hh ht =>
      rw [setMany_cons, set_get_self hh]
      exact ih ht

/-! ### `restore` -/

theorem restore_def (V Vb : VEnv D) :
    YulSemantics.restore V Vb = Vb.drop (Vb.length - V.length) := rfl

theorem length_restore {V Vb : VEnv D} (h : V.length ≤ Vb.length) :
    (YulSemantics.restore V Vb).length = V.length := by
  rw [restore_def, List.length_drop]; omega

@[simp] theorem restore_self (V : VEnv D) : YulSemantics.restore V V = V := by
  rw [restore_def]; simp

theorem restore_of_length_eq {V Vb : VEnv D} (h : V.length = Vb.length) :
    YulSemantics.restore V Vb = Vb := by
  rw [restore_def, h]; simp

theorem restore_append (W V : VEnv D) :
    YulSemantics.restore V (W ++ V) = V := by
  rw [restore_def]
  simp

/-- Scope exit composes: restoring past two nested scopes is restoring past
the outer one. -/
theorem restore_trans {V V₁ V₂ : VEnv D} (h₁ : V.length ≤ V₁.length)
    (h₂ : V₁.length ≤ V₂.length) :
    YulSemantics.restore V V₂
      = YulSemantics.restore V (YulSemantics.restore V₁ V₂) := by
  rw [restore_def V V₂, restore_def V (YulSemantics.restore V₁ V₂),
    length_restore h₂, restore_def V₁ V₂, List.drop_drop]
  congr 1
  omega

end VEnv

section Correspondence

variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates

/-! ## The environment invariant

`EnvOK env V R`: the construction-time map `env` and the runtime environment
`V` bind the same names in the same order, and every `ValId` `env` records
holds the value `V` records. This is the invariant that makes `VMap.get`
(construction) and `VEnv.get` (semantics) interchangeable. -/

/-- The construction-time environment mirrors the runtime one through `R`. -/
def EnvOK (env : VMap) (V : VEnv yulD) (R : Regs) : Prop :=
  List.Forall₂ (fun (p : Ident × ValId) (q : Ident × U256) =>
    p.1 = q.1 ∧ R p.2 = some q.2) env V

namespace EnvOK

/-- `EnvOK` preserves the complete visible-name spine. -/
theorem names {env : VMap} {V : VEnv yulD} {R : Regs}
    (h : EnvOK env V R) : env.map Prod.fst = VEnv.names V := by
  induction h with
  | nil => rfl
  | @cons p q env V hpq _ ih =>
    change p.1 :: env.map Prod.fst = q.1 :: VEnv.names V
    rw [hpq.1, ih]

theorem unique_names {env : VMap} {V : VEnv yulD} {R : Regs}
    (h : EnvOK env V R) (hu : env.Unique) : (VEnv.names V).Nodup := by
  rw [← h.names]
  exact hu

theorem length {env : VMap} {V : VEnv yulD} {R : Regs} (h : EnvOK env V R) :
    env.length = V.length :=
  Forall2.length_eq h

/-- Register-file extension preserves the invariant — the single-assignment
payoff: nothing the construction does later can invalidate a binding. -/
theorem mono {env : VMap} {V : VEnv yulD} {R R' : Regs} (h : EnvOK env V R)
    (hle : Regs.Le R R') : EnvOK env V R' :=
  Forall2.imp (fun _ _ hpq => ⟨hpq.1, hle _ _ hpq.2⟩) h

theorem nil : EnvOK ([] : VMap) ([] : VEnv yulD) R := List.Forall₂.nil

theorem cons {x : Ident} {i : ValId} {v : U256} {env : VMap} {V : VEnv yulD}
    {R : Regs} (hv : R i = some v) (h : EnvOK env V R) :
    EnvOK ((x, i) :: env) ((x, v) :: V) R :=
  List.Forall₂.cons ⟨rfl, hv⟩ h

theorem append {env₁ env₂ : VMap} {V₁ V₂ : VEnv yulD} {R : Regs}
    (h₁ : EnvOK env₁ V₁ R) (h₂ : EnvOK env₂ V₂ R) :
    EnvOK (env₁ ++ env₂) (V₁ ++ V₂) R :=
  Forall2.append h₁ h₂

theorem drop {env : VMap} {V : VEnv yulD} {R : Regs} (n : Nat)
    (h : EnvOK env V R) : EnvOK (env.drop n) (V.drop n) R :=
  Forall2.drop n h

/-- Scope exit agrees: the construction's `drop` is the semantics' `restore`. -/
theorem restore {env : VMap} {V : VEnv yulD} {R : Regs} {env₀ : VMap}
    {V₀ : VEnv yulD} (h : EnvOK env V R) (h₀ : env₀.length = V₀.length) :
    EnvOK (env.drop (env.length - env₀.length))
      (YulSemantics.restore V₀ V) R := by
  have hlen : env.length = V.length := h.length
  rw [YulSemantics.restore, ← hlen, ← h₀]
  exact h.drop _

/-- A successful construction-time lookup is matched by the semantics. -/
theorem get {env : VMap} {V : VEnv yulD} {R : Regs} (h : EnvOK env V R)
    {x : Ident} {i : ValId} (hget : VMap.get env x = some i) :
    ∃ v, YulSemantics.VEnv.get V x = some v ∧ R i = some v := by
  induction h with
  | nil => exact absurd hget (by simp)
  | @cons p q env' V' hpq _ ih =>
    rw [VMap.get_cons] at hget
    rw [VEnv.get_cons, ← hpq.1]
    by_cases hx : p.1 = x
    · rw [if_pos hx] at hget ⊢
      obtain rfl := Option.some.inj hget
      exact ⟨q.2, rfl, hpq.2⟩
    · rw [if_neg hx] at hget ⊢
      exact ih hget

/-- …and conversely: whatever the semantics can read, the construction found. -/
theorem get_rev {env : VMap} {V : VEnv yulD} {R : Regs} (h : EnvOK env V R)
    {x : Ident} {v : U256} (hget : YulSemantics.VEnv.get V x = some v) :
    ∃ i, VMap.get env x = some i ∧ R i = some v := by
  induction h with
  | nil => exact absurd hget (by simp [YulSemantics.VEnv.get])
  | @cons p q env' V' hpq _ ih =>
    rw [VEnv.get_cons, ← hpq.1] at hget
    rw [VMap.get_cons]
    by_cases hx : p.1 = x
    · rw [if_pos hx] at hget ⊢
      obtain rfl := Option.some.inj hget
      exact ⟨p.2, rfl, hpq.2⟩
    · rw [if_neg hx] at hget ⊢
      exact ih hget

/-- In-place update: the construction's `VMap.set` tracks `VEnv.set`. -/
theorem set {env : VMap} {V : VEnv yulD} {R : Regs} (h : EnvOK env V R)
    {x : Ident} {i : ValId} {v : U256} (hv : R i = some v) :
    EnvOK (env.set x i) (YulSemantics.VEnv.set V x v) R := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons p q env' V' hpq htl ih =>
    obtain ⟨py, pi⟩ := p
    obtain ⟨qy, qv⟩ := q
    obtain ⟨rfl, hqv⟩ := hpq
    rw [VMap.set, YulSemantics.VEnv.set]
    by_cases hx : py = x
    · rw [if_pos hx, if_pos hx]
      exact List.Forall₂.cons ⟨rfl, hv⟩ htl
    · rw [if_neg hx, if_neg hx]
      exact List.Forall₂.cons ⟨rfl, hqv⟩ ih

/-- Multi-assignment: `VMap.setMany` tracks `VEnv.setMany` pointwise. -/
theorem setMany {R : Regs} : ∀ {xs : List Ident} {is : List ValId} {vs : List U256}
    {env : VMap} {V : VEnv yulD}, EnvOK env V R →
    List.Forall₂ (fun i v => R i = some v) is vs →
    EnvOK (env.setMany xs is) (YulSemantics.VEnv.setMany V xs vs) R := by
  intro xs
  induction xs with
  | nil => intro is vs env V h _; exact h
  | cons x xs ih =>
    intro is vs env V h hiv
    cases hiv with
    | nil => rw [VMap.setMany_nil_right, VEnv.setMany_nil_right]; exact h
    | @cons i v is' vs' hh ht =>
      rw [VMap.setMany_cons, VEnv.setMany_cons]
      exact ih (h.set hh) ht

/-- A freshly built `zip` of names to just-defined ids. -/
theorem zip {R : Regs} : ∀ {xs : List Ident} {is : List ValId} {vs : List U256},
    List.Forall₂ (fun i v => R i = some v) is vs → xs.length = is.length →
    EnvOK (xs.zip is) (xs.zip vs) R := by
  intro xs
  induction xs with
  | nil => intro is vs _ _; exact List.Forall₂.nil
  | cons x xs ih =>
    intro is vs hiv hlen
    cases hiv with
    | nil => exact absurd hlen (by simp)
    | @cons i v is' vs' hh ht =>
      simp only [List.zip_cons_cons]
      exact List.Forall₂.cons ⟨rfl, hh⟩ (ih ht (by simpa using hlen))

/-- The `let`-without-value / return-variable case: ids bound to zero mirror
`bindZeros`. -/
theorem zip_bindZeros {R : Regs} : ∀ {xs : List Ident} {is : List ValId},
    xs.length = is.length → (∀ i ∈ is, R i = some 0) →
    EnvOK (xs.zip is) (YulSemantics.bindZeros yulD xs) R := by
  intro xs
  induction xs with
  | nil => intro is _ _; exact List.Forall₂.nil
  | cons x xs ih =>
    intro is hlen hz
    cases is with
    | nil => exact absurd hlen (by simp)
    | cons i is =>
      simp only [List.zip_cons_cons, YulSemantics.bindZeros, List.map_cons]
      exact List.Forall₂.cons ⟨rfl, hz i (List.mem_cons_self ..)⟩
        (ih (by simpa using hlen) (fun j hj => hz j (List.mem_cons_of_mem _ hj)))

/-- Pointwise version of `edgeArgs`' payoff. -/
theorem edge_vals {env : VMap} {V : VEnv yulD} {R : Regs} (henv : EnvOK env V R) :
    ∀ {xs : List Ident} {ids : List ValId},
      List.Forall₂ (fun x i => VMap.get env x = some i) xs ids →
      ∃ vals, R.getMany ids = some vals
        ∧ List.Forall₂ (fun x v => YulSemantics.VEnv.get V x = some v) xs vals := by
  intro xs ids h
  induction h with
  | nil => exact ⟨[], rfl, .nil⟩
  | @cons x i xs' ids' hh _ ih =>
    obtain ⟨v, hv, hRi⟩ := henv.get hh
    obtain ⟨vals, hvals, hf⟩ := ih
    exact ⟨v :: vals, by rw [Regs.getMany_cons, hRi, hvals]; simp, .cons hv hf⟩

end EnvOK

end Correspondence

/-! ## Inverting the construction monad

`M = StateT BState Option`; a successful run of a `do` block decomposes into
successful runs of its steps, exactly as `compileProgramAsm_inv` decomposes the
classic backend's `Option` pipeline. Everything in this section is by
definitional unfolding. -/

namespace M

theorem bind_eq {α β} (x : M α) (f : α → M β) (s : BState) :
    (x >>= f) s = (x s).bind (fun p => f p.1 p.2) := rfl

/-- The workhorse: invert one `do`-step. -/
theorem bind_inv {α β} {x : M α} {f : α → M β} {s : BState} {r : β × BState}
    (h : (x >>= f) s = some r) :
    ∃ (a : α) (s₁ : BState), x s = some (a, s₁) ∧ f a s₁ = some r := by
  rw [bind_eq] at h
  cases hx : x s with
  | none => rw [hx] at h; exact absurd h (by simp)
  | some p =>
    rw [hx] at h
    simp only [Option.bind_some] at h
    exact ⟨p.1, p.2, rfl, h⟩

@[simp] theorem pure_apply {α} (a : α) (s : BState) :
    (pure a : M α) s = some (a, s) := rfl

theorem pure_inv {α} {a a' : α} {s s' : BState} (h : (pure a : M α) s = some (a', s')) :
    a' = a ∧ s' = s := by
  rw [pure_apply] at h
  have h' := Option.some.inj h
  exact ⟨(congrArg Prod.fst h').symm, (congrArg Prod.snd h').symm⟩

@[simp] theorem reject_apply {α} (s : BState) : (reject : M α) s = none := rfl

theorem reject_inv {α} {s : BState} {r : α × BState} (h : (reject : M α) s = some r) :
    False := by simp at h

theorem liftO_inv {α} {o : Option α} {s : BState} {a : α} {s' : BState}
    (h : (liftO o : M α) s = some (a, s')) : o = some a ∧ s' = s := by
  cases o with
  | none => exact absurd h (by simp [liftO])
  | some b =>
    have h' : (b, s) = (a, s') := Option.some.inj h
    have h1 : b = a := congrArg Prod.fst h'
    have h2 : s = s' := congrArg Prod.snd h'
    exact ⟨by rw [h1], h2.symm⟩

/-- Invert the `if <bad> then reject else k` gate the construction uses for
its rejections (shadowing, duplicate names, missing loop/function context). -/
theorem ite_reject_inv {α} {c : Prop} [Decidable c] {k : M α} {s : BState}
    {r : α × BState} (h : (if c then (reject : M α) else k) s = some r) :
    ¬ c ∧ k s = some r := by
  by_cases hc : c
  · rw [if_pos hc] at h; exact absurd h (by simp)
  · exact ⟨hc, by rw [if_neg hc] at h; exact h⟩

/-! ### The primitives -/

@[simp] theorem freshVal_apply (s : BState) :
    freshVal s = some (s.fn.nextVal,
      { s with fn := { s.fn with nextVal := s.fn.nextVal + 1 } }) := rfl

@[simp] theorem emit_apply (i : Instr) (s : BState) :
    emit i s = some ((), { s with fn := { s.fn with cur := i :: s.fn.cur } }) := rfl

@[simp] theorem newBlock_apply (params : List ValId) (s : BState) :
    newBlock params s = some (s.fn.blocks.size,
      { s with fn := { s.fn with
          blocks := s.fn.blocks.push ⟨params, [], .ret []⟩ } }) := rfl

@[simp] theorem moveTo_apply (b : BlockId) (s : BState) :
    moveTo b s = some ((), { s with fn := { s.fn with curId := b, cur := [] } }) := rfl

@[simp] theorem getFn_apply (s : BState) : getFn s = some (s.fn, s) := rfl

@[simp] theorem setFn_apply (fn : FnState) (s : BState) :
    setFn fn s = some ((), { s with fn }) := rfl

@[simp] theorem allocFunc_apply (s : BState) :
    allocFunc s = some (s.funcs.size, { s with funcs := s.funcs.push none }) := rfl

theorem sealCur_inv {t : Term} {s s' : BState} {u : Unit}
    (h : sealCur t s = some (u, s')) :
    ∃ b, s.fn.blocks[s.fn.curId]? = some b
      ∧ s' = { s with fn := { s.fn with
          blocks := s.fn.blocks.set! s.fn.curId ⟨b.params, s.fn.cur.reverse, t⟩,
          cur := [] } } := by
  rw [sealCur] at h
  cases hb : s.fn.blocks[s.fn.curId]? with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some b =>
    rw [hb] at h
    exact ⟨b, rfl, (congrArg Prod.snd (Option.some.inj h)).symm⟩

theorem fillFunc_inv {fid : FuncId} {f : Func} {s s' : BState} {u : Unit}
    (h : fillFunc fid f s = some (u, s')) :
    ∃ hlt : fid < s.funcs.size,
      s' = { s with funcs := s.funcs.set fid (some f) hlt } := by
  rw [fillFunc] at h
  by_cases hlt : fid < s.funcs.size
  · rw [dif_pos hlt] at h
    exact ⟨hlt, (congrArg Prod.snd (Option.some.inj h)).symm⟩
  · rw [dif_neg hlt] at h; exact absurd h (by simp)

theorem edgeArgs_inv {env : VMap} {xs : List Ident} {s s' : BState}
    {ids : List ValId} (h : edgeArgs env xs s = some (ids, s')) :
    xs.mapM env.get = some ids ∧ s' = s :=
  liftO_inv h

/-! ### Fresh-value allocation

The construction's parameter/return-value allocation is `mapM freshVal`, which
returns exactly the next `n` ids. This is the freshness engine: the ids are an
interval above the old `nextVal` and below the new one, hence pairwise
distinct and absent from any register file built from earlier ids. -/

theorem mapM_freshVal {α} : ∀ (xs : List α) (s : BState),
    (xs.mapM (fun _ => freshVal)) s
      = some (List.range' s.fn.nextVal xs.length,
          { s with fn := { s.fn with
              nextVal := s.fn.nextVal + xs.length } }) := by
  intro xs
  induction xs with
  | nil => intro s; rfl
  | cons x xs ih =>
    intro s
    have hn : s.fn.nextVal + 1 + xs.length = s.fn.nextVal + (xs.length + 1) :=
      Nat.add_right_comm _ _ _
    rw [List.mapM_cons, bind_eq, freshVal_apply]
    simp only [Option.bind_some]
    rw [bind_eq, ih]
    simp only [Option.bind_some, pure_apply, List.length_cons, List.range'_succ, hn]

theorem mapM_freshVal_length {α} {xs : List α} {s s' : BState} {ids : List ValId}
    (h : (xs.mapM (fun _ => freshVal)) s = some (ids, s')) :
    ids.length = xs.length ∧ ids = List.range' s.fn.nextVal xs.length
      ∧ s' = { s with fn := { s.fn with nextVal := s.fn.nextVal + xs.length } } := by
  rw [mapM_freshVal] at h
  have h' := Option.some.inj h
  obtain ⟨rfl, rfl⟩ : ids = List.range' s.fn.nextVal xs.length
      ∧ s' = { s with fn := { s.fn with nextVal := s.fn.nextVal + xs.length } } :=
    ⟨(congrArg Prod.fst h').symm, (congrArg Prod.snd h').symm⟩
  exact ⟨by simp, rfl, rfl⟩

theorem nodup_range' (k n : Nat) : (List.range' k n).Nodup := List.nodup_range'

theorem mem_range'_bounds {k n i : Nat} (h : i ∈ List.range' k n) : k ≤ i ∧ i < k + n := by
  rw [List.mem_range'_1] at h
  exact h

theorem some_pair_inj {α : Type} {a b : α} {s t : BState}
    (h : (some (a, s) : Option (α × BState)) = some (b, t)) : a = b ∧ s = t :=
  ⟨congrArg Prod.fst (Option.some.inj h), congrArg Prod.snd (Option.some.inj h)⟩

/-- Invert `do let a ← x; pure (f a)`, which the elaborator compiles to a
`Functor.map` rather than a `bind`. -/
theorem map_inv {α β : Type} {f : α → β} {x : M α} {s : BState} {b : β}
    {s' : BState} (h : (f <$> x) s = some (b, s')) :
    ∃ a, x s = some (a, s') ∧ b = f a := by
  have h' : (x s).bind (fun p => some (f p.1, p.2)) = some (b, s') := h
  cases hx : x s with
  | none => rw [hx] at h'; exact absurd h' (by simp)
  | some p =>
    rw [hx] at h'
    simp only [Option.bind_some] at h'
    obtain ⟨rfl, rfl⟩ := some_pair_inj h'
    exact ⟨p.1, rfl, rfl⟩

/-- Invert the `if <ok> then k else reject` form (`trExprN`'s arity gate). -/
theorem ite_reject_inv' {α : Type} {c : Prop} [Decidable c] {k : M α}
    {s : BState} {r : α × BState}
    (h : (if c then k else (reject : M α)) s = some r) : c ∧ k s = some r := by
  by_cases hc : c
  · exact ⟨hc, by rw [if_pos hc] at h; exact h⟩
  · rw [if_neg hc] at h; exact absurd h (by simp)

end M

/-! ## Freshness: the builder only allocates

`Grows s s'` records everything an *expression*-level translation step can do to
the builder state: raise `nextVal` and prepend to the current block's pending
instruction list. Nothing already written moves, and every id an expression
defines is at least the incoming `nextVal` — which is what makes `Regs.Le` (and
hence `EnvOK.mono`) available at every step. -/

/-- The builder state grew: `nextVal` rose, instructions were prepended to the
current block, and nothing else changed. -/
structure Grows (s s' : BState) : Prop where
  nextVal : s.fn.nextVal ≤ s'.fn.nextVal
  blocks : s.fn.blocks = s'.fn.blocks
  curId : s.fn.curId = s'.fn.curId
  funcs : s.funcs = s'.funcs
  cur : ∃ Δ, s'.fn.cur = Δ ++ s.fn.cur

namespace Grows

theorem rfl' (s : BState) : Grows s s := ⟨Nat.le_refl _, rfl, rfl, rfl, ⟨[], rfl⟩⟩

theorem trans {s₁ s₂ s₃ : BState} (h₁ : Grows s₁ s₂) (h₂ : Grows s₂ s₃) :
    Grows s₁ s₃ := by
  obtain ⟨Δ₁, e₁⟩ := h₁.cur
  obtain ⟨Δ₂, e₂⟩ := h₂.cur
  exact ⟨Nat.le_trans h₁.nextVal h₂.nextVal, h₁.blocks.trans h₂.blocks,
    h₁.curId.trans h₂.curId, h₁.funcs.trans h₂.funcs,
    ⟨Δ₂ ++ Δ₁, by rw [e₂, e₁, List.append_assoc]⟩⟩

theorem of_freshVal {s s' : BState} {v : ValId}
    (h : SsaCfg.freshVal s = some (v, s')) : Grows s s' := by
  rw [M.freshVal_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact ⟨Nat.le_succ _, rfl, rfl, rfl, ⟨[], rfl⟩⟩

/-- The allocated id is exactly the old `nextVal`, and the new one is one more:
the fact that makes a freshly allocated id provably absent from any register
file built from earlier ids. -/
theorem freshVal_spec {s s' : BState} {v : ValId}
    (h : SsaCfg.freshVal s = some (v, s')) :
    v = s.fn.nextVal ∧ s'.fn.nextVal = s.fn.nextVal + 1 := by
  rw [M.freshVal_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact ⟨rfl, rfl⟩

theorem of_emit {i : Instr} {s s' : BState} {u : Unit}
    (h : SsaCfg.emit i s = some (u, s')) : Grows s s' := by
  rw [M.emit_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact ⟨Nat.le_refl _, rfl, rfl, rfl, ⟨[i], rfl⟩⟩

theorem of_liftO {α : Type} {o : Option α} {a : α} {s s' : BState}
    (h : (SsaCfg.liftO o : M α) s = some (a, s')) : Grows s s' := by
  obtain ⟨-, rfl⟩ := M.liftO_inv h
  exact rfl' _

theorem of_pure {α : Type} {a b : α} {s s' : BState}
    (h : (pure a : M α) s = some (b, s')) : Grows s s' := by
  obtain ⟨-, rfl⟩ := M.pure_inv h
  exact rfl' _

/-- `mapM freshVal` grows. -/
theorem of_mapM_freshVal {α : Type} {xs : List α} {s s' : BState}
    {ids : List ValId}
    (h : (xs.mapM (fun _ => SsaCfg.freshVal)) s = some (ids, s')) :
    Grows s s' := by
  obtain ⟨-, -, rfl⟩ := M.mapM_freshVal_length h
  exact ⟨by simp, rfl, rfl, rfl, ⟨[], rfl⟩⟩

end Grows

/-- The finished function *completes* a builder state — the placement invariant
the induction carries.

* `sealed`: every block the builder has laid down other than the one it is
  currently filling is already final. This holds at every `trStmt`/`trStmts`/
  `trScope` boundary: the construction always seals the block it is leaving
  before `moveTo`, and the only block it reserves without immediately sealing is
  the join/exit block it makes current on the way out.
* `params`: **every** reserved block keeps its parameter list, current or not.
  This is the strengthening the `cond`/`switch`/`forLoop` cases need, where a
  join/exit block is reserved *before* the blocks that jump to it are sealed —
  the edge-argument arity premises of `Exec.jump`/`Exec.branch*` are about the
  finished block, but the construction only ever sees the reserved one.
* `size`: the block array only grows. -/
structure Completes (f : Func) (fn : FnState)
    (joins : List BlockId := []) : Prop where
  sealed : ∀ (i : Nat) (b : Block), i ∉ joins → i ≠ fn.curId → fn.blocks[i]? = some b
      → f.blocks[i]? = some b
  params : ∀ (i : Nat) (b : Block), fn.blocks[i]? = some b
      → ∃ bf, f.blocks[i]? = some bf ∧ bf.params = b.params
  size : fn.blocks.size ≤ f.blocks.size

/-- The weak form the `SOut` leaves consume. -/
def Extends (f : Func) (fn : FnState) : Prop :=
  (∀ (i : Nat) (b : Block), i ≠ fn.curId → fn.blocks[i]? = some b
      → f.blocks[i]? = some b)
  ∧ (∀ b : Block, fn.blocks[fn.curId]? = some b
      → ∃ bf, f.blocks[fn.curId]? = some bf ∧ bf.params = b.params)

theorem Completes.toExtends {f : Func} {fn : FnState} (h : Completes f fn) :
    Extends f fn :=
  ⟨fun i b hne hb => h.sealed i b (by simp) hne hb,
    fun b hb => h.params _ b hb⟩

theorem Completes.protect {f : Func} {fn : FnState} {joins : List BlockId}
    (h : Completes f fn joins) (joinId : BlockId) :
    Completes f fn (joinId :: joins) := by
  refine ⟨?_, h.params, h.size⟩
  intro i b hnot hne hb
  exact h.sealed i b (fun hi => hnot (by simp [hi])) hne hb

/-- Backward completion transfer across the one non-fresh move structured
control performs: returning to a protected enclosing join.  `moveTo` changes
only `curId`/`cur`; if the output-current block is encountered while proving
the input's sealed field, it is the protected target and the non-membership
premise rules that case out. -/
theorem Completes.of_moveTo_protected {f : Func} {s s' : BState}
    {joinId : BlockId} {u : Unit} {joins : List BlockId}
    (hmem : joinId ∈ joins) (hmv : moveTo joinId s = some (u, s'))
    (h : Completes f s'.fn joins) : Completes f s.fn joins := by
  rw [M.moveTo_apply] at hmv
  obtain ⟨-, rfl⟩ := M.some_pair_inj hmv
  refine ⟨?_, h.params, h.size⟩
  intro i b hnot hne hb
  exact h.sealed i b hnot (fun hi => hnot (hi ▸ hmem)) hb

/-- Blocks protected by an enclosing structured construct were all reserved
before the fragment starts, and none is the fragment's current block.  The
first fact makes the property stable when the fragment moves to a fresh block;
the second licenses exact-block uses of `Completes.sealed` for the block the
fragment is currently filling. -/
structure ProtectedAt (joins : List BlockId) (fn : FnState) : Prop where
  below : ∀ i ∈ joins, i < fn.blocks.size
  away : fn.curId ∉ joins

namespace ProtectedAt

theorem nil (fn : FnState) : ProtectedAt [] fn := ⟨by simp, by simp⟩

end ProtectedAt

/-! ### Statement-class monotonicity

Statements do more than expressions: they reserve blocks, seal them, move the
current block, and fill function slots. `SGrowsAt N` is what survives, relative
to a *base* block count `N` (in use, the block count at the start of the
fragment):

* nothing shrinks (`nextVal`, `size`, `funcsSize`);
* **no block's parameter list ever changes** (`params`) — this is what feeds
  the `params` field of `Completes`;
* the only pre-existing block a fragment can disturb is the one it starts on
  (`keep`), because every other block it seals it reserved itself;
* correspondingly the current block either does not move or moves to a block
  reserved at or after `N` (`curId`).

The last two fields are exactly what makes the relation composable: `keep` for
the second half applies because `curId` for the first half puts the moved-to
block out of range. -/
structure SGrowsAt (N : Nat) (s s' : BState) : Prop where
  nextVal : s.fn.nextVal ≤ s'.fn.nextVal
  size : s.fn.blocks.size ≤ s'.fn.blocks.size
  funcsSize : s.funcs.size ≤ s'.funcs.size
  params : ∀ (i : Nat) (b : Block), s.fn.blocks[i]? = some b →
    ∃ b', s'.fn.blocks[i]? = some b' ∧ b'.params = b.params
  keep : ∀ (i : Nat) (b : Block), i < N → i ≠ s.fn.curId →
    s.fn.blocks[i]? = some b → s'.fn.blocks[i]? = some b
  curId : s'.fn.curId = s.fn.curId ∨ N ≤ s'.fn.curId

/-- Function slots are only ever appended and filled; nothing is ever removed.
Weak enough to survive `trFunc`'s `setFn` save/restore, which is why it is
tracked separately. -/
def FGrows (s s' : BState) : Prop := s.funcs.size ≤ s'.funcs.size

/-- Content half of function-table growth.  Reserved `none` slots may be
refined to a function, but an already-filled slot keeps the same function.
This is the pointwise prefix order needed to transport a local `trFunc`
result into the completed top-level table. -/
def FContents (s s' : BState) : Prop :=
  ∀ (i : Nat) (g : Func), s.funcs[i]? = some (some g) →
    s'.funcs[i]? = some (some g)

/-- Size growth together with preservation of every filled entry. -/
def FRefines (s s' : BState) : Prop := FGrows s s' ∧ FContents s s'

/-- Exact ownership of the function slots which are still pending in a local
builder state.  `owned` is not a list of function *names*: it is the
duplicate-free list of the concrete array indices whose reservations this
translation still has to discharge.  This index-level formulation is what
prevents two equal hoisted names from silently sharing one reservation.

The filled-prefix clause connects the local table to the one fixed completed
table used by the construction simulation.  Slots not allocated yet are
deliberately unconstrained. -/
structure FOwned (owned : List FuncId) (s done : BState) : Prop where
  nodup : owned.Nodup
  pending : ∀ i : FuncId, i ∈ owned ↔ s.funcs[i]? = some none
  filled : FContents s done

namespace FGrows

theorem rfl' (s : BState) : FGrows s s := Nat.le_refl _

theorem trans {s₁ s₂ s₃ : BState} (h₁ : FGrows s₁ s₂) (h₂ : FGrows s₂ s₃) :
    FGrows s₁ s₃ := Nat.le_trans h₁ h₂

theorem of_fnOnly {s s' : BState} (h : s.funcs = s'.funcs) : FGrows s s' := by
  rw [FGrows, h]

theorem of_getFn {s s' : BState} {fn : FnState} (h : getFn s = some (fn, s')) :
    FGrows s s' := by
  rw [M.getFn_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact rfl' _

theorem of_setFn {fn : FnState} {s s' : BState} {u : Unit}
    (h : setFn fn s = some (u, s')) : FGrows s s' := by
  rw [M.setFn_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact of_fnOnly rfl

end FGrows

namespace FContents

theorem rfl' (s : BState) : FContents s s := fun _ _ h => h

theorem trans {s₁ s₂ s₃ : BState} (h₁ : FContents s₁ s₂)
    (h₂ : FContents s₂ s₃) : FContents s₁ s₃ :=
  fun i g hi => h₂ i g (h₁ i g hi)

theorem of_funcs_eq {s s' : BState} (h : s.funcs = s'.funcs) :
    FContents s s' := by
  intro i g hi
  rwa [← h]

theorem of_getFn {s s' : BState} {fn : FnState}
    (h : getFn s = some (fn, s')) : FContents s s' := by
  rw [M.getFn_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact rfl' _

theorem of_setFn {fn : FnState} {s s' : BState} {u : Unit}
    (h : setFn fn s = some (u, s')) : FContents s s' := by
  rw [M.setFn_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact of_funcs_eq rfl

theorem of_allocFunc {s s' : BState} {fid : FuncId}
    (h : allocFunc s = some (fid, s')) : FContents s s' := by
  rw [M.allocFunc_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  intro i g hi
  have hlt := lt_size_of_getElem? hi
  rw [Array.getElem?_push, if_neg (by omega : ¬ i = s.funcs.size)]
  exact hi

/-- Filling a genuinely reserved slot preserves every function that was
already present.  The `allocScope`/`trStmts` singleton recovery establishes
the `none` premise for the particular slot selected by `FMap.get`. -/
theorem of_fillFunc_empty {fid : FuncId} {g : Func} {s s' : BState}
    {u : Unit} (hempty : s.funcs[fid]? = some none)
    (h : fillFunc fid g s = some (u, s')) : FContents s s' := by
  obtain ⟨hlt, rfl⟩ := M.fillFunc_inv h
  intro i g' hi
  have hne : i ≠ fid := by
    intro heq
    subst i
    have hbad : some g' = none := Option.some.inj (hi.symm.trans hempty)
    cases hbad
  rw [Array.getElem?_set (h := hlt), if_neg (Ne.symm hne)]
  exact hi

theorem of_grows {s s' : BState} (h : Grows s s') : FContents s s' :=
  of_funcs_eq h.funcs

end FContents

namespace FOwned

theorem of_funcs_eq {owned : List FuncId} {s s' done : BState}
    (hfuncs : s.funcs = s'.funcs) (h : FOwned owned s' done) :
    FOwned owned s done := by
  refine ⟨h.nodup, ?_, ?_⟩
  · intro i
    rw [h.pending, hfuncs]
  · exact FContents.trans (FContents.of_funcs_eq hfuncs) h.filled

theorem rfl_of_no_pending {s : BState}
    (h : ∀ i : FuncId, s.funcs[i]? ≠ some none) : FOwned [] s s := by
  refine ⟨List.nodup_nil, ?_, FContents.rfl' s⟩
  intro i
  simp only [List.not_mem_nil, false_iff]
  exact h i

/-- Reserving a slot adds precisely its fresh array index to the ownership
budget. -/
theorem of_allocFunc {owned : List FuncId} {s s' done : BState}
    {fid : FuncId} (ho : FOwned owned s done)
    (h : allocFunc s = some (fid, s')) : FOwned (owned ++ [fid]) s' done := by
  rw [M.allocFunc_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  have hnot : s.funcs.size ∉ owned := by
    intro hm
    have := (ho.pending s.funcs.size).mp hm
    simpa using this
  refine ⟨ho.nodup.append (by simp) (by simpa), ?_, ?_⟩
  · intro i
    rw [List.mem_append, List.mem_singleton, Array.getElem?_push]
    by_cases hi : i = s.funcs.size
    · subst i
      simp [hnot]
    · simp [hi, ho.pending]
  · intro i g hi
    rw [Array.getElem?_push] at hi
    by_cases hieq : i = s.funcs.size
    · rw [if_pos hieq] at hi
      cases Option.some.inj hi
    · rw [if_neg hieq] at hi
      exact ho.filled i g hi

/-- Reserving all declarations of a scope appends exactly the function ids
recorded in the resulting scope map to the pending-slot budget. -/
theorem of_allocScope {owned : List FuncId} {ss : List (Stmt Op)}
    {s s' done : BState} {scope : List (Ident × FuncId)}
    (ho : FOwned owned s done)
    (h : allocScope ss s = some (scope, s')) :
    FOwned (owned ++ scope.map Prod.snd) s' done := by
  rw [allocScope] at h
  have fold : ∀ (l : List (Stmt Op)) (acc : List (Ident × FuncId))
      (s₀ s₁ : BState) (out : List (Ident × FuncId))
      (base : List FuncId),
      FOwned (owned ++ base) s₀ done →
      acc.map Prod.snd = base →
      (l.foldlM (init := acc) fun acc (st : Stmt Op) =>
        match st with
        | Stmt.funDef n _ _ _ => do
            let fid ← allocFunc
            pure (acc ++ [(n, fid)])
        | _ => pure acc) s₀ = some (out, s₁) →
      FOwned (owned ++ out.map Prod.snd) s₁ done := by
    intro l
    induction l with
    | nil =>
        intro acc s₀ s₁ out base hown hacc hl
        obtain ⟨rfl, rfl⟩ := M.pure_inv hl
        simpa [hacc] using hown
    | cons st rest ih =>
        intro acc s₀ s₁ out base hown hacc hl
        rw [List.foldlM_cons] at hl
        obtain ⟨acc', t, hst, hrest⟩ := M.bind_inv hl
        cases st with
        | funDef n ps rs body =>
            obtain ⟨fid, u, ha, hp⟩ := M.bind_inv hst
            obtain ⟨rfl, rfl⟩ := M.pure_inv hp
            have halloc := FOwned.of_allocFunc hown ha
            apply ih (acc ++ [(n, fid)]) t s₁ out (base ++ [fid])
            · simpa [List.append_assoc] using halloc
            · simp [hacc]
            · exact hrest
        | block body | letDecl vars val | assign vars e | cond e body
        | forLoop init e post body | «break» | «continue» | leave
        | switch e cases dflt | exprStmt e =>
            have heq := M.pure_inv hst
            rw [heq.1, heq.2] at hrest
            exact ih acc s₀ s₁ out base hown hacc hrest
  exact fold ss [] s s' scope [] (by simpa using ho) rfl h

/-- Backwards form of allocation: the newly appended owned reservation is
removed when reconstructing the caller state. -/
theorem back_allocFunc {owned : List FuncId} {s s' done : BState}
    {fid : FuncId} (h : allocFunc s = some (fid, s'))
    (ho : FOwned (owned ++ [fid]) s' done) : FOwned owned s done := by
  rw [M.allocFunc_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  have hnd : owned.Nodup := (ho.nodup.of_append_left)
  have hnot : s.funcs.size ∉ owned := by
    have hd := (List.nodup_append'.mp ho.nodup).2.2
    exact fun hm => (List.disjoint_left.mp hd) hm (by simp)
  refine ⟨hnd, ?_, ?_⟩
  · intro i
    by_cases hi : i = s.funcs.size
    · subst i
      simp [hnot]
    · have hp := ho.pending i
      simpa [Array.getElem?_push, hi] using hp
  · intro i g hi
    apply ho.filled i g
    rw [Array.getElem?_push, if_neg]
    · exact hi
    · intro heq
      subst i
      simpa using hi

/-- Backwards form of whole-scope allocation: remove precisely the reservation
suffix recorded by the generated scope map. -/
theorem back_allocScope {owned : List FuncId} {ss : List (Stmt Op)}
    {s s' done : BState} {scope : List (Ident × FuncId)}
    (h : allocScope ss s = some (scope, s'))
    (ho : FOwned (owned ++ scope.map Prod.snd) s' done) :
    FOwned owned s done := by
  rw [allocScope] at h
  have fold : ∀ (l : List (Stmt Op)) (acc : List (Ident × FuncId))
      (s₀ s₁ : BState) (out : List (Ident × FuncId)),
      (l.foldlM (init := acc) fun acc (st : Stmt Op) =>
        match st with
        | Stmt.funDef n _ _ _ => do
            let fid ← allocFunc
            pure (acc ++ [(n, fid)])
        | _ => pure acc) s₀ = some (out, s₁) →
      FOwned (owned ++ out.map Prod.snd) s₁ done →
      FOwned (owned ++ acc.map Prod.snd) s₀ done := by
    intro l
    induction l with
    | nil =>
        intro acc s₀ s₁ out hl hown
        obtain ⟨rfl, rfl⟩ := M.pure_inv hl
        exact hown
    | cons st rest ih =>
        intro acc s₀ s₁ out hl hown
        rw [List.foldlM_cons] at hl
        obtain ⟨acc', t, hst, hrest⟩ := M.bind_inv hl
        have hmid := ih acc' t s₁ out hrest hown
        cases st with
        | funDef n ps rs body =>
            obtain ⟨fid, u, ha, hp⟩ := M.bind_inv hst
            obtain ⟨rfl, rfl⟩ := M.pure_inv hp
            have hback := FOwned.back_allocFunc
              (owned := owned ++ acc.map Prod.snd) ha (by
              simpa [List.map_append, List.append_assoc] using hmid)
            simpa using hback
        | block body | letDecl vars val | assign vars e | cond e body
        | forLoop init e post body | «break» | «continue» | leave
        | switch e cases dflt | exprStmt e =>
            have heq := M.pure_inv hst
            simpa [heq.1, heq.2] using hmid
  simpa using fold ss [] s s' scope h ho

/-- Filling an owned empty slot consumes exactly that index.  The theorem is
stated backwards because a completed suffix tells us both that the output slot
contains `g` and that it agrees with `done`; reconstructing the input then
restores `fid` to the pending budget. -/
theorem back_fillFunc {owned : List FuncId} {fid : FuncId} {g : Func}
    {s s' done : BState} {u : Unit}
    (hempty : s.funcs[fid]? = some none)
    (h : fillFunc fid g s = some (u, s'))
    (ho : FOwned owned s' done) : FOwned (fid :: owned) s done := by
  have hfill := h
  obtain ⟨hlt, rfl⟩ := M.fillFunc_inv h
  have hslot : ({ s with funcs := s.funcs.set fid (some g) hlt }).funcs[fid]?
      = some (some g) := by simp
  have hnot : fid ∉ owned := by
    intro hm
    have hp := (ho.pending fid).mp hm
    rw [hslot] at hp
    cases Option.some.inj hp
  refine ⟨List.nodup_cons.mpr ⟨hnot, ho.nodup⟩, ?_, ?_⟩
  · intro i
    by_cases hi : i = fid
    · subst i
      simp [hempty]
    · have hp := ho.pending i
      rw [Array.getElem?_set (h := hlt), if_neg (Ne.symm hi)] at hp
      simpa [hi] using hp
  · exact FContents.trans (FContents.of_fillFunc_empty hempty hfill) ho.filled

end FOwned

namespace FRefines

theorem rfl' (s : BState) : FRefines s s := ⟨FGrows.rfl' s, FContents.rfl' s⟩

theorem trans {s₁ s₂ s₃ : BState} (h₁ : FRefines s₁ s₂)
    (h₂ : FRefines s₂ s₃) : FRefines s₁ s₃ :=
  ⟨FGrows.trans h₁.1 h₂.1, FContents.trans h₁.2 h₂.2⟩

theorem of_grows {s s' : BState} (h : Grows s s') : FRefines s s' :=
  ⟨FGrows.of_fnOnly h.funcs, FContents.of_grows h⟩

end FRefines

/-! ### Function-table prefix frames

`trFunc` may recursively allocate and fill nested functions while an enclosing
scope still has reserved `none` slots.  Size growth alone does not say that
those caller-owned slots survived.  `FPrefix N s s'` records the stronger
frame fact: every slot below the allocation watermark `N` is byte-for-byte
unchanged (including a pending `none`). -/

def FPrefix (N : Nat) (s s' : BState) : Prop :=
  ∀ i : FuncId, i < N → s'.funcs[i]? = s.funcs[i]?

namespace FPrefix

theorem rfl' (N : Nat) (s : BState) : FPrefix N s s := fun _ _ => rfl

theorem trans {N : Nat} {s₀ s₁ s₂ : BState}
    (h₀₁ : FPrefix N s₀ s₁) (h₁₂ : FPrefix N s₁ s₂) :
    FPrefix N s₀ s₂ := by
  intro i hi
  exact (h₁₂ i hi).trans (h₀₁ i hi)

/-- A theorem at a larger watermark implies one at every smaller watermark. -/
theorem mono {N N' : Nat} (hN : N' ≤ N) {s s' : BState}
    (h : FPrefix N s s') : FPrefix N' s s' :=
  fun i hi => h i (Nat.lt_of_lt_of_le hi hN)

theorem size {N : Nat} {s s' : BState} (h : FPrefix N s s')
    (hN : N ≤ s.funcs.size) : N ≤ s'.funcs.size := by
  cases N with
  | zero => exact Nat.zero_le _
  | succ n =>
      by_contra hn
      have hinLt : n < s.funcs.size := Nat.lt_of_succ_le hN
      have houtLe : s'.funcs.size ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_not_ge hn)
      have hin := Array.getElem?_eq_getElem (xs := s.funcs) (i := n) hinLt
      have hout := Array.getElem?_eq_none (xs := s'.funcs) (i := n) houtLe
      have heq := h n (Nat.lt_succ_self n)
      rw [hout, hin] at heq
      cases heq

theorem of_funcs_eq {N : Nat} {s s' : BState} (h : s'.funcs = s.funcs) :
    FPrefix N s s' := by
  intro i hi
  rw [h]

theorem of_grows {N : Nat} {s s' : BState} (h : Grows s s') :
    FPrefix N s s' := of_funcs_eq h.funcs.symm

theorem of_allocFunc {N : Nat} {s s' : BState} {fid : FuncId}
    (hN : N ≤ s.funcs.size) (h : allocFunc s = some (fid, s')) :
    FPrefix N s s' := by
  rw [M.allocFunc_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  intro i hi
  rw [Array.getElem?_push, if_neg
    (Nat.ne_of_lt (Nat.lt_of_lt_of_le hi hN))]

theorem of_fillFunc {N : Nat} {s s' : BState} {fid : FuncId} {g : Func}
    {u : Unit} (hfid : N ≤ fid) (h : fillFunc fid g s = some (u, s')) :
    FPrefix N s s' := by
  obtain ⟨hlt, rfl⟩ := M.fillFunc_inv h
  intro i hi
  rw [Array.getElem?_set (h := hlt), if_neg
    (Nat.ne_of_gt (Nat.lt_of_lt_of_le hi hfid))]

theorem of_getFn {N : Nat} {s s' : BState} {fn : FnState}
    (h : getFn s = some (fn, s')) : FPrefix N s s' := by
  rw [M.getFn_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact rfl' _ _

theorem of_setFn {N : Nat} {s s' : BState} {fn : FnState} {u : Unit}
    (h : setFn fn s = some (u, s')) : FPrefix N s s' := by
  rw [M.setFn_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact rfl' _ _

theorem of_newBlock {N : Nat} {s s' : BState} {ps : List ValId}
    {bid : BlockId} (h : newBlock ps s = some (bid, s')) : FPrefix N s s' := by
  rw [M.newBlock_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact rfl' _ _

theorem of_moveTo {N : Nat} {s s' : BState} {bid : BlockId} {u : Unit}
    (h : moveTo bid s = some (u, s')) : FPrefix N s s' := by
  rw [M.moveTo_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact rfl' _ _

theorem of_sealCur {N : Nat} {s s' : BState} {t : Term} {u : Unit}
    (h : sealCur t s = some (u, s')) : FPrefix N s s' := by
  obtain ⟨b, hb, rfl⟩ := M.sealCur_inv h
  exact rfl' _ _

theorem of_liftO {N : Nat} {α : Type} {o : Option α} {a : α}
    {s s' : BState} (h : (liftO o : M α) s = some (a, s')) :
    FPrefix N s s' := by
  obtain ⟨-, rfl⟩ := M.liftO_inv h
  exact rfl' _ _

theorem of_pure {N : Nat} {α : Type} {a b : α} {s s' : BState}
    (h : (pure a : M α) s = some (b, s')) : FPrefix N s s' := by
  obtain ⟨-, rfl⟩ := M.pure_inv h
  exact rfl' _ _

theorem of_edgeArgs {N : Nat} {env : VMap} {xs : List Ident}
    {s s' : BState} {ids : List ValId}
    (h : edgeArgs env xs s = some (ids, s')) : FPrefix N s s' :=
  of_liftO h

end FPrefix

namespace FOwned

/-- Ownership budgets are extensional up to permutation; their list order is
only a convenient way to state duplicate-freedom. -/
theorem perm {owned owned' : List FuncId} {s done : BState}
    (hp : owned.Perm owned') (ho : FOwned owned s done) :
    FOwned owned' s done := by
  refine ⟨hp.nodup ho.nodup, ?_, ho.filled⟩
  intro i
  rw [← hp.mem_iff, ho.pending]

/-- Pull ownership backward across a closed nested translation which frames
the caller's whole input table.  The explicit bound says that `owned` really
belongs to the caller rather than to slots freshly allocated by the nested
translation; this is the small side condition the simulation motive must
thread together with `FOwned`. -/
theorem back_fprefix {owned : List FuncId} {s s' done : BState}
    (hp : FPrefix s.funcs.size s s')
    (hbound : ∀ i : FuncId, i ∈ owned → i < s.funcs.size)
    (ho : FOwned owned s' done) : FOwned owned s done := by
  refine ⟨ho.nodup, ?_, ?_⟩
  · intro i
    constructor
    · intro hi
      rw [← hp i (hbound i hi)]
      exact (ho.pending i).mp hi
    · intro hi
      have hlt : i < s.funcs.size := lt_size_of_getElem? hi
      apply (ho.pending i).mpr
      rwa [hp i hlt]
  · intro i g hi
    have hlt : i < s.funcs.size := lt_size_of_getElem? hi
    apply ho.filled i g
    rwa [hp i hlt]

end FOwned

namespace SGrowsAt

theorem toFGrows {N : Nat} {s s' : BState} (h : SGrowsAt N s s') : FGrows s s' :=
  h.funcsSize

/-- A larger base is a stronger statement. -/
theorem mono {N N' : Nat} (hle : N' ≤ N) {s s' : BState} (h : SGrowsAt N s s') :
    SGrowsAt N' s s' :=
  ⟨h.nextVal, h.size, h.funcsSize, h.params,
    fun i b hi hne hb => h.keep i b (Nat.lt_of_lt_of_le hi hle) hne hb,
    h.curId.imp id (fun hh => Nat.le_trans hle hh)⟩

theorem rfl' (N : Nat) (s : BState) : SGrowsAt N s s :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, fun _ b hb => ⟨b, hb, rfl⟩,
    fun _ _ _ _ hb => hb, Or.inl rfl⟩

theorem trans {N : Nat} {s₁ s₂ s₃ : BState} (h₁ : SGrowsAt N s₁ s₂)
    (h₂ : SGrowsAt N s₂ s₃) : SGrowsAt N s₁ s₃ := by
  refine ⟨Nat.le_trans h₁.nextVal h₂.nextVal, Nat.le_trans h₁.size h₂.size,
    Nat.le_trans h₁.funcsSize h₂.funcsSize, ?_, ?_, ?_⟩
  · intro i b hb
    obtain ⟨b', hb', hp'⟩ := h₁.params i b hb
    obtain ⟨b'', hb'', hp''⟩ := h₂.params i b' hb'
    exact ⟨b'', hb'', hp''.trans hp'⟩
  · intro i b hi hne hb
    have hne2 : i ≠ s₂.fn.curId := by
      rcases h₁.curId with heq | hge
      · rw [heq]; exact hne
      · omega
    exact h₂.keep i b hi hne2 (h₁.keep i b hi hne hb)
  · rcases h₂.curId with heq | hge
    · rw [heq]; exact h₁.curId
    · exact Or.inr hge

/-- From an expression-level step. -/
theorem of_grows {N : Nat} {s s' : BState} (h : Grows s s') : SGrowsAt N s s' :=
  ⟨h.nextVal, by rw [h.blocks], by rw [h.funcs],
    fun i b hb => ⟨b, by rw [← h.blocks]; exact hb, rfl⟩,
    fun _ b _ _ hb => by rw [← h.blocks]; exact hb, Or.inl h.curId.symm⟩

/-- A step that changes nothing but the function table. -/
theorem of_funcsOnly {N : Nat} {s s' : BState} (hfn : s'.fn = s.fn)
    (hf : s.funcs.size ≤ s'.funcs.size) : SGrowsAt N s s' :=
  ⟨by rw [hfn], by rw [hfn], hf,
    fun i b hb => ⟨b, by rw [hfn]; exact hb, rfl⟩,
    fun _ b _ _ hb => by rw [hfn]; exact hb, Or.inl (by rw [hfn])⟩

theorem of_newBlock {N : Nat} {ps : List ValId} {s s' : BState} {bid : BlockId}
    (h : newBlock ps s = some (bid, s')) : SGrowsAt N s s' := by
  rw [M.newBlock_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  refine ⟨Nat.le_refl _, by simp, Nat.le_refl _, ?_, ?_, Or.inl rfl⟩
  · intro i b hb
    have hlt := lt_size_of_getElem? hb
    refine ⟨b, ?_, rfl⟩
    dsimp only
    rw [Array.getElem?_push, if_neg (by omega : ¬ i = s.fn.blocks.size)]
    exact hb
  · intro i b _ _ hb
    have hlt := lt_size_of_getElem? hb
    dsimp only
    rw [Array.getElem?_push, if_neg (by omega : ¬ i = s.fn.blocks.size)]
    exact hb

/-- The reserved block's id is the old block count: every `moveTo` target the
construction produces is at or beyond the fragment's base. -/
theorem newBlock_id {ps : List ValId} {s s' : BState} {bid : BlockId}
    (h : newBlock ps s = some (bid, s')) : bid = s.fn.blocks.size := by
  rw [M.newBlock_apply] at h
  exact (M.some_pair_inj h).1.symm

theorem of_sealCur {N : Nat} {t : Term} {s s' : BState} {u : Unit}
    (h : sealCur t s = some (u, s')) : SGrowsAt N s s' := by
  obtain ⟨b, hb, rfl⟩ := M.sealCur_inv h
  have hlt : s.fn.curId < s.fn.blocks.size := lt_size_of_getElem? hb
  refine ⟨Nat.le_refl _, by simp, Nat.le_refl _, ?_, ?_, Or.inl rfl⟩
  · intro i b' hb'
    by_cases hc : i = s.fn.curId
    · subst hc
      obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
      refine ⟨⟨b'.params, s.fn.cur.reverse, t⟩, ?_, rfl⟩
      dsimp only
      rw [Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_self_of_lt hlt]
    · refine ⟨b', ?_, rfl⟩
      dsimp only
      rw [Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_ne (Ne.symm hc)]
      exact hb'
  · intro i b' _ hne hb'
    dsimp only
    rw [Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (Ne.symm hne)]
    exact hb'

theorem of_moveTo {N : Nat} {bid : BlockId} {s s' : BState} {u : Unit}
    (hbid : N ≤ bid ∨ bid = s.fn.curId) (h : moveTo bid s = some (u, s')) :
    SGrowsAt N s s' := by
  rw [M.moveTo_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
    fun i b hb => ⟨b, hb, rfl⟩, fun _ _ _ _ hb => hb, hbid.symm⟩

theorem of_allocFunc {N : Nat} {s s' : BState} {fid : FuncId}
    (h : allocFunc s = some (fid, s')) : SGrowsAt N s s' := by
  rw [M.allocFunc_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact of_funcsOnly rfl (by simp)

theorem of_fillFunc {N : Nat} {fid : FuncId} {g : Func} {s s' : BState}
    {u : Unit} (h : fillFunc fid g s = some (u, s')) : SGrowsAt N s s' := by
  obtain ⟨hlt, rfl⟩ := M.fillFunc_inv h
  exact of_funcsOnly rfl (by simp)

theorem of_getFn {N : Nat} {s s' : BState} {fn : FnState}
    (h : getFn s = some (fn, s')) : SGrowsAt N s s' := by
  rw [M.getFn_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact rfl' N s

theorem of_liftO {N : Nat} {α : Type} {o : Option α} {a : α} {s s' : BState}
    (h : (liftO o : M α) s = some (a, s')) : SGrowsAt N s s' := by
  obtain ⟨-, rfl⟩ := M.liftO_inv h
  exact rfl' N _

theorem of_pure {N : Nat} {α : Type} {a b : α} {s s' : BState}
    (h : (pure a : M α) s = some (b, s')) : SGrowsAt N s s' := by
  obtain ⟨-, rfl⟩ := M.pure_inv h
  exact rfl' N _

theorem of_edgeArgs {N : Nat} {env : VMap} {xs : List Ident} {s s' : BState}
    {ids : List ValId} (h : edgeArgs env xs s = some (ids, s')) :
    SGrowsAt N s s' := of_liftO h

/-- **The `Completes` transfer.** The placement invariant travels *backwards*
along a fragment: if the finished function completes the state the fragment ends
in, it completes the state it started in. This is the payoff of `keep`/`curId`
— the block the fragment started on is the only pre-existing one it could have
sealed, and it is exempt from `Completes.sealed` at the input state. -/
theorem completes_of {f : Func} {s s' : BState} {joins : List BlockId}
    (h : SGrowsAt s.fn.blocks.size s s') (hc : Completes f s'.fn joins) :
    Completes f s.fn joins := by
  refine ⟨?_, ?_, Nat.le_trans h.size hc.size⟩
  · intro i b hprot hne hb
    have hlt : i < s.fn.blocks.size := lt_size_of_getElem? hb
    have hne2 : i ≠ s'.fn.curId := by
      rcases h.curId with heq | hge
      · rw [heq]; exact hne
      · omega
    exact hc.sealed i b hprot hne2 (h.keep i b hlt hne hb)
  · intro i b hb
    obtain ⟨b', hb', hp'⟩ := h.params i b hb
    obtain ⟨bf, hbf, hpf⟩ := hc.params i b' hb'
    exact ⟨bf, hbf, hpf.trans hp'⟩

end SGrowsAt

namespace ProtectedAt

theorem forward {joins : List BlockId} {s s' : BState}
    (hp : ProtectedAt joins s.fn)
    (hg : SGrowsAt s.fn.blocks.size s s') : ProtectedAt joins s'.fn := by
  refine ⟨fun i hi => Nat.lt_of_lt_of_le (hp.below i hi) hg.size, ?_⟩
  intro hc
  rcases hg.curId with heq | hge
  · exact hp.away (by simpa only [heq] using hc)
  · exact Nat.not_lt_of_ge hge (hp.below _ hc)

end ProtectedAt

namespace FGrows

theorem of_newBlock {ps : List ValId} {s s' : BState} {bid : BlockId}
    (h : newBlock ps s = some (bid, s')) : FGrows s s' :=
  (SGrowsAt.of_newBlock (N := 0) h).funcsSize

theorem of_moveTo {bid : BlockId} {s s' : BState} {u : Unit}
    (h : moveTo bid s = some (u, s')) : FGrows s s' :=
  (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h).funcsSize

theorem of_sealCur {t : Term} {s s' : BState} {u : Unit}
    (h : sealCur t s = some (u, s')) : FGrows s s' :=
  (SGrowsAt.of_sealCur (N := 0) h).funcsSize

theorem of_liftO {α : Type} {o : Option α} {a : α} {s s' : BState}
    (h : (liftO o : M α) s = some (a, s')) : FGrows s s' :=
  (SGrowsAt.of_liftO (N := 0) h).funcsSize

theorem of_pure {α : Type} {a b : α} {s s' : BState}
    (h : (pure a : M α) s = some (b, s')) : FGrows s s' :=
  (SGrowsAt.of_pure (N := 0) h).funcsSize

theorem of_grows {s s' : BState} (h : Grows s s') : FGrows s s' :=
  (SGrowsAt.of_grows (N := 0) h).funcsSize

end FGrows

/-- Statement-class monotonicity at its natural base: the block count the
fragment starts with. -/
def SGrows (s s' : BState) : Prop := SGrowsAt s.fn.blocks.size s s'

namespace SGrows

theorem rfl' (s : BState) : SGrows s s := SGrowsAt.rfl' _ s

/-- Own-base monotonicity is transitive: the second fragment's guarantee is
weakened to the first one's base, which is legitimate because the block array
only grew. -/
theorem trans {s₀ s₁ s₂ : BState} (h₁ : SGrows s₀ s₁) (h₂ : SGrows s₁ s₂) :
    SGrows s₀ s₂ :=
  SGrowsAt.trans h₁ (h₂.mono h₁.size)

theorem of_grows {s s' : BState} (h : Grows s s') : SGrows s s' :=
  SGrowsAt.of_grows h

end SGrows

/-- `mapM` over allocating steps allocates. -/
theorem Grows.of_mapM {α : Type} {g : α → M ValId}
    (hg : ∀ (a : α) (s s' : BState) (v : ValId), g a s = some (v, s') → Grows s s') :
    ∀ (l : List α) (s s' : BState) (vs : List ValId),
      (l.mapM g) s = some (vs, s') → Grows s s' := by
  intro l
  induction l with
  | nil => intro s s' vs h; exact Grows.of_pure h
  | cons a l ih =>
    intro s s' vs h
    rw [List.mapM_cons] at h
    obtain ⟨v, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨vs', s₂, h2, h3⟩ := M.bind_inv h
    exact (hg a s s₁ v h1).trans ((ih s₁ s₂ vs' h2).trans (Grows.of_pure h3))

/-- The zero-initialising allocation `trStmt`/`trFunc` use for `let`-without-value
and for return variables. -/
theorem Grows.of_mapM_constZero {α : Type} {l : List α} {s s' : BState}
    {vs : List ValId}
    (h : (l.mapM (fun _ => do let v ← freshVal; emit (.const v 0); pure v)) s
        = some (vs, s')) : Grows s s' := by
  refine Grows.of_mapM ?_ l s s' vs h
  intro a s₀ s₁ v hv
  obtain ⟨w, s₂, h1, hv⟩ := M.bind_inv hv
  obtain ⟨u, s₃, h2, h3⟩ := M.bind_inv hv
  exact (Grows.of_freshVal h1).trans ((Grows.of_emit h2).trans (Grows.of_pure h3))

/-- The zero-initialising allocation, exactly: the ids are the next `|l|`, and
the emitted instruction block is their `const _ 0`s in order. -/
theorem constZero_apply (s : BState) :
    (do let v ← freshVal; emit (.const v 0); pure v) s
      = some (s.fn.nextVal, { s with fn := { s.fn with
          nextVal := s.fn.nextVal + 1,
          cur := Instr.const s.fn.nextVal 0 :: s.fn.cur } }) := rfl

theorem mapM_constZero_spec {α : Type} : ∀ (l : List α) (s : BState),
    (l.mapM (fun _ => do let v ← freshVal; emit (.const v 0); pure v)) s
      = some (List.range' s.fn.nextVal l.length,
          { s with fn := { s.fn with
              nextVal := s.fn.nextVal + l.length,
              cur := ((List.range' s.fn.nextVal l.length).map
                        (fun v => Instr.const v 0)).reverse ++ s.fn.cur } }) := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons a l ih =>
    intro s
    have hn : s.fn.nextVal + 1 + l.length = s.fn.nextVal + (l.length + 1) :=
      Nat.add_right_comm _ _ _
    rw [List.mapM_cons, M.bind_eq, constZero_apply]
    simp only [Option.bind_some]
    rw [M.bind_eq, ih]
    simp only [Option.bind_some, M.pure_apply, List.length_cons,
      List.range'_succ, List.map_cons, List.reverse_cons, hn]
    simp

/-- **Expression translation only allocates.** -/
theorem trExpr_grows : ∀ (e : Expr Op) (fenv : FMap) (env : VMap) (s s' : BState)
    (i : ValId), trExpr fenv env e s = some (i, s') → Grows s s' := by
  refine trExpr.induct
    (fun e => ∀ (fenv : FMap) (env : VMap) (s s' : BState) (i : ValId),
      trExpr fenv env e s = some (i, s') → Grows s s')
    (fun es => ∀ (fenv : FMap) (env : VMap) (s s' : BState) (ids : List ValId),
      trArgs fenv env es s = some (ids, s') → Grows s s')
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro l fenv env s s' i h
    rw [trExpr] at h
    obtain ⟨v, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    exact (Grows.of_freshVal h1).trans ((Grows.of_emit h2).trans (Grows.of_pure h3))
  · intro x fenv env s s' i h
    rw [trExpr] at h
    exact Grows.of_liftO h
  · intro op args ih fenv env s s' i h
    rw [trExpr] at h
    obtain ⟨as, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨d, s₂, h2, h⟩ := M.bind_inv h
    obtain ⟨u, s₃, h3, h4⟩ := M.bind_inv h
    exact (ih fenv env s s₁ as h1).trans
      ((Grows.of_freshVal h2).trans ((Grows.of_emit h3).trans (Grows.of_pure h4)))
  · intro fn args ih fenv env s s' i h
    rw [trExpr] at h
    obtain ⟨as, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨fid, s₂, h2, h⟩ := M.bind_inv h
    obtain ⟨d, s₃, h3, h⟩ := M.bind_inv h
    obtain ⟨u, s₄, h4, h5⟩ := M.bind_inv h
    exact (ih fenv env s s₁ as h1).trans ((Grows.of_liftO h2).trans
      ((Grows.of_freshVal h3).trans ((Grows.of_emit h4).trans (Grows.of_pure h5))))
  · intro fenv env s s' ids h
    rw [trArgs] at h
    exact Grows.of_pure h
  · intro e rest ihrest ihe fenv env s s' ids h
    rw [trArgs] at h
    obtain ⟨restIds, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨i, s₂, h2, h3⟩ := M.bind_inv h
    exact (ihrest fenv env s s₁ restIds h1).trans
      ((ihe fenv env s₁ s₂ i h2).trans (Grows.of_pure h3))

/-- **Argument-list translation only allocates.** -/
theorem trArgs_grows : ∀ (es : List (Expr Op)) (fenv : FMap) (env : VMap)
    (s s' : BState) (ids : List ValId),
    trArgs fenv env es s = some (ids, s') → Grows s s' := by
  refine trArgs.induct
    (fun e => ∀ (fenv : FMap) (env : VMap) (s s' : BState) (i : ValId),
      trExpr fenv env e s = some (i, s') → Grows s s')
    (fun es => ∀ (fenv : FMap) (env : VMap) (s s' : BState) (ids : List ValId),
      trArgs fenv env es s = some (ids, s') → Grows s s')
    (fun l => trExpr_grows (.lit l)) (fun x => trExpr_grows (.var x))
    (fun op args _ => trExpr_grows (.builtin op args))
    (fun fn args _ => trExpr_grows (.call fn args)) ?_ ?_
  · intro fenv env s s' ids h
    rw [trArgs] at h
    exact Grows.of_pure h
  · intro e rest ihrest ihe fenv env s s' ids h
    rw [trArgs] at h
    obtain ⟨restIds, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨i, s₂, h2, h3⟩ := M.bind_inv h
    exact (ihrest fenv env s s₁ restIds h1).trans
      ((ihe fenv env s₁ s₂ i h2).trans (Grows.of_pure h3))

/-- `foldlM` over steps that only append to the function table. -/
theorem foldlM_funcsOnly {α β : Type} {g : β → α → M β}
    (hg : ∀ (b : β) (a : α) (s s' : BState) (b' : β),
      g b a s = some (b', s') → s'.fn = s.fn ∧ s.funcs.size ≤ s'.funcs.size) :
    ∀ (l : List α) (b : β) (s : BState) (b' : β) (s' : BState),
      (l.foldlM g b) s = some (b', s')
        → s'.fn = s.fn ∧ s.funcs.size ≤ s'.funcs.size := by
  intro l
  induction l with
  | nil =>
    intro b s b' s' h
    obtain ⟨-, rfl⟩ := M.pure_inv h
    exact ⟨rfl, Nat.le_refl _⟩
  | cons a l ih =>
    intro b s b' s' h
    rw [List.foldlM_cons] at h
    obtain ⟨c, s₁, h1, h2⟩ := M.bind_inv h
    obtain ⟨hfn1, hf1⟩ := hg b a s s₁ c h1
    obtain ⟨hfn2, hf2⟩ := ih c s₁ b' s' h2
    exact ⟨hfn2.trans hfn1, Nat.le_trans hf1 hf2⟩

/-- Reserving a scope's function slots touches only the function table. -/
theorem allocScope_funcsOnly {ss : List (Stmt Op)} {s s' : BState}
    {sc : List (Ident × FuncId)} (h : allocScope ss s = some (sc, s')) :
    s'.fn = s.fn ∧ s.funcs.size ≤ s'.funcs.size := by
  rw [allocScope] at h
  refine foldlM_funcsOnly ?_ ss [] s sc s' h
  intro b a s₀ s₁ b' hb
  cases a
  case funDef n ps rs body =>
    obtain ⟨fid, s₂, h1, h2⟩ := M.bind_inv hb
    rw [M.allocFunc_apply] at h1
    obtain ⟨rfl, rfl⟩ := M.some_pair_inj h1
    obtain ⟨-, rfl⟩ := M.pure_inv h2
    exact ⟨rfl, by simp⟩
  all_goals (obtain ⟨-, rfl⟩ := M.pure_inv hb; exact ⟨rfl, Nat.le_refl _⟩)

/-- Reserving a whole scope is genuine function-table refinement: it appends
`none` slots and leaves every already-filled entry untouched. -/
theorem allocScope_frefines {ss : List (Stmt Op)} {s s' : BState}
    {sc : List (Ident × FuncId)} (h : allocScope ss s = some (sc, s')) :
    FRefines s s' := by
  rw [allocScope] at h
  have step : ∀ (acc : List (Ident × FuncId)) (st : Stmt Op)
      (s₀ s₁ : BState) (acc' : List (Ident × FuncId)),
      (match st with
        | Stmt.funDef n _ _ _ => do
            let fid ← allocFunc
            pure (acc ++ [(n, fid)])
        | _ => pure acc) s₀ = some (acc', s₁) → FRefines s₀ s₁ := by
    intro acc st s₀ s₁ acc' hs
    cases st with
    | funDef n ps rs body =>
        obtain ⟨fid, t, ha, hp⟩ := M.bind_inv hs
        obtain ⟨-, rfl⟩ := M.pure_inv hp
        exact ⟨(SGrowsAt.of_allocFunc (N := 0) ha).funcsSize,
          FContents.of_allocFunc ha⟩
    | block body | letDecl vars val | assign vars e | cond e body
    | forLoop init e post body | «break» | «continue» | leave
    | switch e cases dflt | exprStmt e =>
        obtain ⟨-, rfl⟩ := M.pure_inv hs
        exact FRefines.rfl' _
  have fold : ∀ (l : List (Stmt Op)) (init : List (Ident × FuncId))
      (s₀ s₁ : BState) (out : List (Ident × FuncId)),
      (l.foldlM (init := init) fun acc (st : Stmt Op) =>
        match st with
        | Stmt.funDef n _ _ _ => do
            let fid ← allocFunc
            pure (acc ++ [(n, fid)])
        | _ => pure acc) s₀ = some (out, s₁) → FRefines s₀ s₁ := by
    intro l
    induction l with
    | nil =>
        intro init s₀ s₁ out hl
        obtain ⟨-, rfl⟩ := M.pure_inv hl
        exact FRefines.rfl' _
    | cons st rest ih =>
        intro init s₀ s₁ out hl
        rw [List.foldlM_cons] at hl
        obtain ⟨acc, t, hst, hrest⟩ := M.bind_inv hl
        exact (step init st s₀ t acc hst).trans (ih acc t s₁ out hrest)
  exact fold ss [] s s' sc h

/-- `allocScope` appends reservations and therefore preserves the complete
pre-existing function-table prefix, including pending `none` entries. -/
theorem allocScope_fprefix {ss : List (Stmt Op)} {s s' : BState}
    {sc : List (Ident × FuncId)} (h : allocScope ss s = some (sc, s')) :
    FPrefix s.funcs.size s s' := by
  rw [allocScope] at h
  have step : ∀ (acc : List (Ident × FuncId)) (st : Stmt Op)
      (s₀ s₁ : BState) (acc' : List (Ident × FuncId)),
      (match st with
        | Stmt.funDef n _ _ _ => do
            let fid ← allocFunc
            pure (acc ++ [(n, fid)])
        | _ => pure acc) s₀ = some (acc', s₁) →
        FPrefix s₀.funcs.size s₀ s₁ ∧ FGrows s₀ s₁ := by
    intro acc st s₀ s₁ acc' hs
    cases st with
    | funDef n ps rs body =>
        obtain ⟨fid, t, ha, hp⟩ := M.bind_inv hs
        obtain ⟨-, rfl⟩ := M.pure_inv hp
        exact ⟨FPrefix.of_allocFunc (Nat.le_refl _) ha,
          (SGrowsAt.of_allocFunc (N := 0) ha).funcsSize⟩
    | block body | letDecl vars val | assign vars e | cond e body
    | forLoop init e post body | «break» | «continue» | leave
    | switch e cases dflt | exprStmt e =>
        obtain ⟨-, rfl⟩ := M.pure_inv hs
        exact ⟨FPrefix.rfl' _ _, FGrows.rfl' _⟩
  have fold : ∀ (l : List (Stmt Op)) (init : List (Ident × FuncId))
      (s₀ s₁ : BState) (out : List (Ident × FuncId)),
      (l.foldlM (init := init) fun acc (st : Stmt Op) =>
        match st with
        | Stmt.funDef n _ _ _ => do
            let fid ← allocFunc
            pure (acc ++ [(n, fid)])
        | _ => pure acc) s₀ = some (out, s₁) →
        FPrefix s₀.funcs.size s₀ s₁ := by
    intro l
    induction l with
    | nil =>
        intro init s₀ s₁ out hl
        obtain ⟨-, rfl⟩ := M.pure_inv hl
        exact FPrefix.rfl' _ _
    | cons st rest ih =>
        intro init s₀ s₁ out hl
        rw [List.foldlM_cons] at hl
        obtain ⟨acc, t, hst, hrest⟩ := M.bind_inv hl
        have hs := step init st s₀ t acc hst
        exact hs.1.trans ((ih acc t s₁ out hrest).mono hs.2)
  exact fold ss [] s s' sc h

/-- Every `funDef` translated by a statement walk must resolve to a slot at or
above `N`.  This is the side condition under which that walk frames the prefix
below `N`. -/
def FillAbove (N : Nat) (fenv : FMap) (ss : List (Stmt Op)) : Prop :=
  ∀ (n : Ident) (ps rs : List Ident) (body : List (Stmt Op)),
    Stmt.funDef n ps rs body ∈ ss →
    ∀ fid : FuncId, fenv.get n = some fid → N ≤ fid

/-- The scope allocated for `ss` covers every declaration in `ss`, and every
slot selected through that innermost scope is freshly appended after the
input table.  Duplicate names are harmless here: `FMap.get` may select the
first duplicate, but all duplicates satisfy the same lower bound. -/
theorem allocScope_fillAbove {ss : List (Stmt Op)} {s s' : BState}
    {scope : List (Ident × FuncId)}
    (h : allocScope ss s = some (scope, s')) (outer : FMap) :
    FillAbove s.funcs.size (scope :: outer) ss := by
  rw [allocScope] at h
  have fold : ∀ (l : List (Stmt Op)) (init : List (Ident × FuncId))
      (s₀ s₁ : BState) (out : List (Ident × FuncId)) (N : Nat),
      N ≤ s₀.funcs.size →
      (l.foldlM (init := init) fun acc (st : Stmt Op) =>
        match st with
        | Stmt.funDef n _ _ _ => do
            let fid ← allocFunc
            pure (acc ++ [(n, fid)])
        | _ => pure acc) s₀ = some (out, s₁) →
      (∀ p ∈ out, p ∈ init ∨ N ≤ p.2) ∧
      (∀ p ∈ init, p ∈ out) ∧
      (∀ (n : Ident) (ps rs : List Ident) (body : List (Stmt Op)),
        Stmt.funDef n ps rs body ∈ l → ∃ fid, (n, fid) ∈ out) := by
    intro l
    induction l with
    | nil =>
        intro baseAcc s₀ s₁ out N hN hl
        obtain ⟨rfl, rfl⟩ := M.pure_inv hl
        exact ⟨fun p hp => Or.inl hp, fun p hp => hp, by simp⟩
    | cons st rest ih =>
        intro baseAcc s₀ s₁ out N hN hl
        rw [List.foldlM_cons] at hl
        obtain ⟨acc, t, hst, hrest⟩ := M.bind_inv hl
        have nonfun
            (hnf : ∀ (n : Ident) (ps rs : List Ident) (body : List (Stmt Op)),
              Stmt.funDef n ps rs body ≠ st)
            (hpure : (pure baseAcc : M (List (Ident × FuncId))) s₀ =
              some (acc, t)) :
            (∀ p ∈ out, p ∈ baseAcc ∨ N ≤ p.2) ∧
            (∀ p ∈ baseAcc, p ∈ out) ∧
            (∀ (n : Ident) (ps rs : List Ident) (body : List (Stmt Op)),
              Stmt.funDef n ps rs body ∈ st :: rest →
                ∃ fid, (n, fid) ∈ out) := by
          obtain ⟨rfl, rfl⟩ := M.pure_inv hpure
          obtain ⟨hout, hkeep, hcov⟩ :=
            ih acc t s₁ out N hN hrest
          refine ⟨hout, hkeep, ?_⟩
          intro n ps rs body hm
          simp only [List.mem_cons] at hm
          exact hm.elim (fun heq => absurd heq (hnf n ps rs body))
            (hcov n ps rs body)
        cases st with
        | funDef n ps rs body =>
            obtain ⟨fid, u, ha, hp⟩ := M.bind_inv hst
            rw [M.allocFunc_apply] at ha
            obtain ⟨rfl, rfl⟩ := M.some_pair_inj ha
            obtain ⟨rfl, rfl⟩ := M.pure_inv hp
            have ht : N ≤ ({ s₀ with funcs := s₀.funcs.push none }).funcs.size := by
              simpa using Nat.le_trans hN (by simp : s₀.funcs.size ≤ s₀.funcs.size + 1)
            obtain ⟨hout, hkeep, hcov⟩ :=
              ih (baseAcc ++ [(n, s₀.funcs.size)])
                { s₀ with funcs := s₀.funcs.push none } s₁ out N ht hrest
            refine ⟨?_, ?_, ?_⟩
            · intro p hpout
              rcases hout p hpout with hpacc | hpge
              · rw [List.mem_append] at hpacc
                exact hpacc.elim Or.inl (fun hpone => by
                  obtain rfl := List.mem_singleton.mp hpone
                  right
                  exact hN)
              · exact Or.inr hpge
            · intro p hpinit
              exact hkeep p (List.mem_append_left _ hpinit)
            · intro n' ps' rs' body' hm
              simp only [List.mem_cons] at hm
              rcases hm with heq | hm
              · cases heq
                exact ⟨s₀.funcs.size,
                  hkeep _ (by simp)⟩
              · exact hcov n' ps' rs' body' hm
        | block body => exact nonfun (by intros; simp) hst
        | letDecl vars val => exact nonfun (by intros; simp) hst
        | assign vars e => exact nonfun (by intros; simp) hst
        | cond e body => exact nonfun (by intros; simp) hst
        | switch e cases dflt => exact nonfun (by intros; simp) hst
        | forLoop init e post body => exact nonfun (by intros; simp) hst
        | exprStmt e => exact nonfun (by intros; simp) hst
        | «break» => exact nonfun (by intros; simp) hst
        | «continue» => exact nonfun (by intros; simp) hst
        | leave => exact nonfun (by intros; simp) hst
  obtain ⟨habove, _hkeep, hcover⟩ := fold ss [] s s' scope s.funcs.size
    (Nat.le_refl _) h
  intro n ps rs body hmem fid hget
  obtain ⟨fid₀, hfid₀⟩ := hcover n ps rs body hmem
  unfold FMap.get at hget
  cases hfind : scope.find? (·.1 = n) with
  | none =>
      have hall := List.find?_eq_none.mp hfind (n, fid₀) hfid₀
      exfalso
      apply hall
      simp
  | some p =>
      have hp : p ∈ scope := List.mem_of_find?_eq_some hfind
      have hfid : p.2 = fid := by simpa [hfind] using hget
      rw [← hfid]
      exact (habove p hp).elim (by simp) id

theorem allocScope_sgrows {ss : List (Stmt Op)} {s s' : BState}
    {sc : List (Ident × FuncId)} (h : allocScope ss s = some (sc, s')) :
    SGrows s s' :=
  SGrowsAt.of_funcsOnly (allocScope_funcsOnly h).1 (allocScope_funcsOnly h).2

/-- **Statement-level right-hand sides only allocate** (`trExprN` is `trArgs`
plus one `emit` for a user call, and a single `trExpr` otherwise). -/
theorem trExprN_grows {fenv : FMap} {env : VMap} {n : Nat} {e : Expr Op}
    {s s' : BState} {ids : List ValId}
    (h : trExprN fenv env n e s = some (ids, s')) : Grows s s' := by
  cases e with
  | call fn args =>
    rw [trExprN] at h
    obtain ⟨as, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨fid, s₂, h2, h⟩ := M.bind_inv h
    obtain ⟨ds, s₃, h3, h⟩ := M.bind_inv h
    obtain ⟨u, s₄, h4, h5⟩ := M.bind_inv h
    exact (trArgs_grows args fenv env s s₁ as h1).trans ((Grows.of_liftO h2).trans
      ((Grows.of_mapM_freshVal h3).trans
        ((Grows.of_emit h4).trans (Grows.of_pure h5))))
  | lit l =>
    rw [trExprN] at h
    · obtain ⟨-, h⟩ := M.ite_reject_inv' h
      obtain ⟨v, s₁, h1, h2⟩ := M.bind_inv h
      exact (trExpr_grows (.lit l) fenv env s s₁ v h1).trans (Grows.of_pure h2)
    · intro fn' args' hc
      simp at hc
  | var x =>
    rw [trExprN] at h
    · obtain ⟨-, h⟩ := M.ite_reject_inv' h
      obtain ⟨v, s₁, h1, h2⟩ := M.bind_inv h
      exact (trExpr_grows (.var x) fenv env s s₁ v h1).trans (Grows.of_pure h2)
    · intro fn' args' hc
      simp at hc
  | builtin op args =>
    rw [trExprN] at h
    · obtain ⟨-, h⟩ := M.ite_reject_inv' h
      obtain ⟨v, s₁, h1, h2⟩ := M.bind_inv h
      exact (trExpr_grows (.builtin op args) fenv env s s₁ v h1).trans (Grows.of_pure h2)
    · intro fn' args' hc
      simp at hc

section Semantics

variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates

/-! ### The statement-class monotonicity induction

One `trStmt.induct` over the construction's five mutually recursive functions.
Every case is a chain of the `SGrowsAt` primitive lemmas above, at the fixed
base `N = ` the case's incoming block count; sub-fragments are weakened to that
base with `SGrowsAt.mono`. -/

/-- Motive for `trFunc`: the per-function state is saved and restored, so only
the function table moves. -/
def FuncGrows (fenv : FMap) (ps rs : List Ident) (body : List (Stmt Op)) : Prop :=
  ∀ (s : BState) (g : Func) (s' : BState),
    trFunc fenv ps rs body s = some (g, s') → s'.fn = s.fn ∧ FGrows s s'

/-- Motive for `trScope`. -/
def ScopeGrows (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (body : List (Stmt Op)) : Prop :=
  ∀ (s : BState) (r : Option VMap) (s' : BState),
    trScope fenv env lctx rets body s = some (r, s') → SGrows s s'

/-- Motive for `trStmts`. -/
def StmtsGrows (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (d : Bool) (ss : List (Stmt Op)) : Prop :=
  ∀ (s : BState) (r : Option VMap) (s' : BState),
    trStmts fenv env lctx rets d ss s = some (r, s') → SGrows s s'

/-- Motive for `trStmt`. -/
def StmtGrows (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (st : Stmt Op) : Prop :=
  ∀ (s : BState) (r : Option VMap) (s' : BState),
    trStmt fenv env lctx rets st s = some (r, s') → SGrows s s'

/-- Motive for `trCases`. -/
def CasesGrows (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (_sv : ValId) (_X : List Ident)
    (_joinId : BlockId) (cases : List (Literal × List (Stmt Op)))
    (dflt : Option (List (Stmt Op))) : Prop :=
  ∀ (sv : ValId) (X : List Ident) (joinId : BlockId) (s : BState) (u : Unit)
    (s' : BState),
    trCases fenv env lctx rets sv X joinId cases dflt s = some (u, s') →
      SGrows s s'

omit model in
/-- **Statement translation only allocates and seals what it reserved.**

The proof is one `trStmt.induct` over the construction's five mutually
recursive functions. `trScope.induct`, `trStmts.induct`, `trFunc.induct` and
`trCases.induct` have the *same* hypothesis list, so this script instantiates
verbatim at each of them to give `ScopeGrows`/`StmtsGrows`/`FuncGrows`/
`CasesGrows`; only the `refine`'s head and the theorem statement change. -/
theorem trStmt_grows : ∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (st : Stmt Op), StmtGrows fenv env lctx rets st := by
  refine trStmt.induct FuncGrows ScopeGrows StmtsGrows StmtGrows CasesGrows
    ?trFunc ?trScope ?stmtsNil ?stmtsFunDef ?stmtsSkip ?stmtsCons
    ?block ?funDef ?letNoneBad ?letNone ?letSomeBad ?letSome ?assignBad ?assign
    ?cond ?switch ?forLoop ?exprBuiltin ?exprCall ?exprBad
    ?breakNone ?breakSome ?contNone ?contSome ?leaveNone ?leaveSome
    ?casesNilNone ?casesNilSome ?casesCons
  case trFunc =>
    intro fenv ps rs body ih s g s' h
    unfold trFunc at h
    obtain ⟨saved, s1, h1, h⟩ := M.bind_inv h
    have hsv : saved = s.fn := by
      rw [M.getFn_apply] at h1; exact (M.some_pair_inj h1).1.symm
    obtain ⟨u2, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨entry, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨pids, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨rids, s6, h6, h⟩ := M.bind_inv h
    have f1 : FGrows s s2 :=
      FGrows.trans (FGrows.of_getFn h1) (FGrows.of_setFn h2)
    have f2 : FGrows s s4 :=
      FGrows.trans f1 (FGrows.trans (FGrows.of_newBlock h3) (FGrows.of_moveTo h4))
    have f3 : FGrows s s6 :=
      FGrows.trans f2 (FGrows.trans
        (FGrows.of_grows (Grows.of_mapM_freshVal h5))
        (FGrows.of_grows (Grows.of_mapM_constZero h6)))
    -- the closing `getFn; setFn saved; pure` restores the caller's `fn`
    have hfin : ∀ (sk : BState), FGrows s sk →
        (getFn >>= fun done => setFn saved >>= fun _ =>
          (pure { params := pids, nrets := rs.length, entry := entry,
                  blocks := done.blocks } : M Func)) sk = some (g, s') →
        s'.fn = s.fn ∧ FGrows s s' := by
      intro sk hk hh
      obtain ⟨done, sa, ha, hh⟩ := M.bind_inv hh
      rw [M.getFn_apply] at ha
      obtain ⟨-, hd2⟩ := M.some_pair_inj ha
      obtain ⟨ub, sb, hb2, hc2⟩ := M.bind_inv hh
      rw [M.setFn_apply] at hb2
      obtain ⟨-, hb3⟩ := M.some_pair_inj hb2
      obtain ⟨-, hc3⟩ := M.pure_inv hc2
      refine ⟨?_, ?_⟩
      · rw [hc3, ← hb3, hsv]
      · rw [FGrows, hc3, ← hb3]
        exact hd2 ▸ hk
    by_cases hg : (!decide (ps ++ rs).Nodup) = true
    · rw [if_pos hg] at h
      obtain ⟨u7, s7, h7, -⟩ := M.bind_inv h
      exact absurd h7 (by simp [reject])
    · rw [if_neg hg] at h
      obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
      obtain ⟨renv, s8, h8, h⟩ := M.bind_inv h
      have f4 : FGrows s s8 :=
        FGrows.trans f3 (FGrows.trans (FGrows.of_pure h7)
          ((ih pids rids s7 renv s8 h8).funcsSize))
      cases renv with
      | none =>
        obtain ⟨ua, sa, ha, hh⟩ := M.bind_inv h
        exact hfin sa (FGrows.trans f4 (FGrows.of_pure ha)) hh
      | some envEnd =>
        obtain ⟨vals, sa, ha, hh⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb2, hh⟩ := M.bind_inv hh
        exact hfin sb (FGrows.trans f4 (FGrows.trans (FGrows.of_liftO ha)
          (FGrows.of_sealCur hb2))) hh
  case trScope =>
    intro fenv env lctx rets body ih s r s' h
    rw [trScope] at h
    obtain ⟨scope, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨renv, s₂, h2, h3⟩ := M.bind_inv h
    have g1 : SGrows s s₁ := allocScope_sgrows h1
    have g2 : SGrows s₁ s₂ := ih scope s₁ renv s₂ h2
    refine (g1.trans g2).trans ?_
    cases renv with
    | none => exact SGrowsAt.of_pure h3
    | some e => exact SGrowsAt.of_pure h3
    
  case stmtsNil =>
    intro fenv env lctx rets d s r s' h
    rw [trStmts] at h
    exact SGrowsAt.of_pure h
  case stmtsFunDef =>
    intro fenv env lctx rets d n ps rs fbody rest ihf ihr s r s' h
    rw [trStmts] at h
    obtain ⟨fid, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨g, s₂, h2, h⟩ := M.bind_inv h
    obtain ⟨u, s₃, h3, h4⟩ := M.bind_inv h
    obtain ⟨hfn, hfg⟩ := ihf s₁ g s₂ h2
    exact (((SGrows.trans (SGrowsAt.of_liftO h1)
      (SGrowsAt.of_funcsOnly hfn hfg)).trans
        (SGrowsAt.of_fillFunc h3)).trans (ihr s₃ r s' h4))
  case stmtsSkip =>
    intro fenv env lctx rets st rest hnf ih s r s' h
    rw [trStmts] at h
    · split at h
      · exact ih s r s' h
      · rename_i hc; exact absurd rfl hc
    · exact hnf
  case stmtsCons =>
    intro fenv env lctx rets d st rest hnf hd ih4 ih3n ih3t s r s' h
    rw [trStmts] at h
    · rw [if_neg hd] at h
      obtain ⟨renv, s₁, h1, h2⟩ := M.bind_inv h
      have g1 : SGrows s s₁ := ih4 s renv s₁ h1
      cases renv with
      | some env' => exact SGrows.trans g1 (ih3n env' s₁ r s' h2)
      | none => exact SGrows.trans g1 (ih3t s₁ r s' h2)
    · exact hnf
  case block =>
    intro fenv env lctx rets body ih s r s' h
    rw [trStmt] at h
    exact ih s r s' h
  case funDef =>
    intro fenv env lctx rets name ps rs body s r s' h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case letNoneBad =>
    intro fenv env lctx rets vars hgate s r s' h
    rw [trStmt] at h
    rw [if_pos hgate] at h
    obtain ⟨u, s₁, h1, -⟩ := M.bind_inv h
    exact absurd h1 (by simp [reject])
  case letNone =>
    intro fenv env lctx rets vars hgate s r s' h
    rw [trStmt] at h
    rw [if_neg hgate] at h
    obtain ⟨u, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_pure h1)
      (SGrows.trans (SGrows.of_grows (Grows.of_mapM_constZero h2))
        (SGrowsAt.of_pure h3))
  case letSomeBad =>
    intro fenv env lctx rets vars e hgate s r s' h
    rw [trStmt] at h
    rw [if_pos hgate] at h
    obtain ⟨u, s₁, h1, -⟩ := M.bind_inv h
    exact absurd h1 (by simp [reject])
  case letSome =>
    intro fenv env lctx rets vars e hgate s r s' h
    rw [trStmt] at h
    rw [if_neg hgate] at h
    obtain ⟨u, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_pure h1)
      (SGrows.trans (SGrows.of_grows (trExprN_grows h2)) (SGrowsAt.of_pure h3))
  case assignBad =>
    intro fenv env lctx rets vars e hgate s r s' h
    rw [trStmt] at h
    rw [if_pos hgate] at h
    obtain ⟨u, s₁, h1, -⟩ := M.bind_inv h
    exact absurd h1 (by simp [reject])
  case assign =>
    intro fenv env lctx rets vars e hgate s r s' h
    rw [trStmt] at h
    rw [if_neg hgate] at h
    obtain ⟨u, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_pure h1)
      (SGrows.trans (SGrows.of_grows (trExprN_grows h2)) (SGrowsAt.of_pure h3))
  case cond =>
    intro fenv env lctx rets c body ih s r s' h
    rw [trStmt] at h
    obtain ⟨cv, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨xvals, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨bodyId, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨joinParams, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨joinId, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨u6, s6, h6, h⟩ := M.bind_inv h
    obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
    obtain ⟨renv, s8, h8, h⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 :=
      SGrowsAt.of_grows (trExpr_grows c fenv env s s1 cv h1)
    have a2 := a1.trans (SGrowsAt.of_edgeArgs h2)
    have a3 := a2.trans (SGrowsAt.of_newBlock h3)
    have a4 := a3.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h4))
    have a5 := a4.trans (SGrowsAt.of_newBlock h5)
    have a6 := a5.trans (SGrowsAt.of_sealCur h6)
    have hbody : s.fn.blocks.size ≤ bodyId := by
      rw [SGrowsAt.newBlock_id h3]; exact a2.size
    have hjoin : s.fn.blocks.size ≤ joinId := by
      rw [SGrowsAt.newBlock_id h5]; exact a4.size
    have a7 := a6.trans (SGrowsAt.of_moveTo (Or.inl hbody) h7)
    have a8 := a7.trans ((ih s7 renv s8 h8).mono a7.size)
    refine a8.trans ?_
    cases renv with
    | none =>
      obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, hc2⟩ := M.bind_inv h
      exact (SGrowsAt.of_pure ha).trans
        ((SGrowsAt.of_moveTo (Or.inl hjoin) hb2).trans (SGrowsAt.of_pure hc2))
    | some env' =>
      obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
      obtain ⟨uc, sc, hc2, hd2⟩ := M.bind_inv h
      exact (SGrowsAt.of_edgeArgs ha).trans
        ((SGrowsAt.of_sealCur hb2).trans
          ((SGrowsAt.of_moveTo (Or.inl hjoin) hc2).trans (SGrowsAt.of_pure hd2)))
  case switch =>
    intro fenv env lctx rets c cases dflt ih s r s' h
    unfold trStmt at h
    obtain ⟨sv, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨joinParams, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨joinId, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨u5, s5, h5, h6⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 :=
      SGrowsAt.of_grows (trExpr_grows c fenv env s s1 sv h1)
    have a2 := a1.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h2))
    have a3 := a2.trans (SGrowsAt.of_newBlock h3)
    have hjoin : s.fn.blocks.size ≤ joinId := by
      rw [SGrowsAt.newBlock_id h3]; exact a2.size
    have a4 := a3.trans ((ih 0 0 _ _ _ s3 u4 s4 h4).mono a3.size)
    exact (a4.trans (SGrowsAt.of_moveTo (Or.inl hjoin) h5)).trans
      (SGrowsAt.of_pure h6)
  case forLoop =>
    intro fenv env lctx rets init c post body ihInit ihBody ihPost s r s' h
    unfold trStmt at h
    obtain ⟨scope, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨rinit, s2, h2, h⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 := allocScope_sgrows h1
    have a2 := a1.trans ((ihInit scope s1 rinit s2 h2).mono a1.size)
    cases rinit with
    | none => exact a2.trans (SGrowsAt.of_pure h)
    | some envI =>
      obtain ⟨xvals, s3, h3, h⟩ := M.bind_inv h
      obtain ⟨hParams, s4, h4, h⟩ := M.bind_inv h
      obtain ⟨hId, s5, h5, h⟩ := M.bind_inv h
      obtain ⟨exitParams, s6, h6, h⟩ := M.bind_inv h
      obtain ⟨exitId, s7, h7, h⟩ := M.bind_inv h
      obtain ⟨postParams, s8, h8, h⟩ := M.bind_inv h
      obtain ⟨postId, s9, h9, h⟩ := M.bind_inv h
      obtain ⟨u10, s10, h10, h⟩ := M.bind_inv h
      obtain ⟨u11, s11, h11, h⟩ := M.bind_inv h
      obtain ⟨cv, s12, h12, h⟩ := M.bind_inv h
      obtain ⟨bodyId, s13, h13, h⟩ := M.bind_inv h
      obtain ⟨hX, s14, h14, h⟩ := M.bind_inv h
      obtain ⟨u15, s15, h15, h⟩ := M.bind_inv h
      obtain ⟨u16, s16, h16, h⟩ := M.bind_inv h
      obtain ⟨renvB, s17, h17, h⟩ := M.bind_inv h
      have a3 := a2.trans (SGrowsAt.of_edgeArgs h3)
      have a4 := a3.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h4))
      have a5 := a4.trans (SGrowsAt.of_newBlock h5)
      have a6 := a5.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h6))
      have a7 := a6.trans (SGrowsAt.of_newBlock h7)
      have a8 := a7.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h8))
      have a9 := a8.trans (SGrowsAt.of_newBlock h9)
      have a10 := a9.trans (SGrowsAt.of_sealCur h10)
      have hhdr : s.fn.blocks.size ≤ hId := by
        rw [SGrowsAt.newBlock_id h5]; exact a4.size
      have hexit : s.fn.blocks.size ≤ exitId := by
        rw [SGrowsAt.newBlock_id h7]; exact a6.size
      have hpost : s.fn.blocks.size ≤ postId := by
        rw [SGrowsAt.newBlock_id h9]; exact a8.size
      have a11 := a10.trans (SGrowsAt.of_moveTo (Or.inl hhdr) h11)
      have a12 := a11.trans (SGrowsAt.of_grows
        (trExpr_grows c (scope :: fenv) _ s11 s12 cv h12))
      have a13 := a12.trans (SGrowsAt.of_newBlock h13)
      have a14 := a13.trans (SGrowsAt.of_edgeArgs h14)
      have a15 := a14.trans (SGrowsAt.of_sealCur h15)
      have hbody : s.fn.blocks.size ≤ bodyId := by
        rw [SGrowsAt.newBlock_id h13]; exact a12.size
      have a16 := a15.trans (SGrowsAt.of_moveTo (Or.inl hbody) h16)
      have a17 := a16.trans
        ((ihBody scope envI hParams exitId postId s16 renvB s17 h17).mono a16.size)
      -- the `post` scope and the loop exit, under both `if let` branches
      cases renvB with
      | none =>
        obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
        obtain ⟨renvP, sc, hc2, h⟩ := M.bind_inv h
        have b1 := a17.trans (SGrowsAt.of_pure ha)
        have b2 := b1.trans (SGrowsAt.of_moveTo (Or.inl hpost) hb2)
        have b3 := b2.trans
          ((ihPost scope envI postParams sb renvP sc hc2).mono b2.size)
        cases renvP with
        | none =>
          obtain ⟨ud, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, hf⟩ := M.bind_inv h
          exact ((b3.trans (SGrowsAt.of_pure hd)).trans
            (SGrowsAt.of_moveTo (Or.inl hexit) he)).trans (SGrowsAt.of_pure hf)
        | some envP' =>
          obtain ⟨xvP, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, h⟩ := M.bind_inv h
          obtain ⟨uf, sf, hf, hg2⟩ := M.bind_inv h
          exact (((b3.trans (SGrowsAt.of_edgeArgs hd)).trans
            (SGrowsAt.of_sealCur he)).trans
              (SGrowsAt.of_moveTo (Or.inl hexit) hf)).trans (SGrowsAt.of_pure hg2)
      | some envB =>
        obtain ⟨xvB, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ua', sa', ha', h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
        obtain ⟨renvP, sc, hc2, h⟩ := M.bind_inv h
        have b0 := a17.trans (SGrowsAt.of_edgeArgs ha)
        have b1 := b0.trans (SGrowsAt.of_sealCur ha')
        have b2 := b1.trans (SGrowsAt.of_moveTo (Or.inl hpost) hb2)
        have b3 := b2.trans
          ((ihPost scope envI postParams sb renvP sc hc2).mono b2.size)
        cases renvP with
        | none =>
          obtain ⟨ud, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, hf⟩ := M.bind_inv h
          exact ((b3.trans (SGrowsAt.of_pure hd)).trans
            (SGrowsAt.of_moveTo (Or.inl hexit) he)).trans (SGrowsAt.of_pure hf)
        | some envP' =>
          obtain ⟨xvP, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, h⟩ := M.bind_inv h
          obtain ⟨uf, sf, hf, hg2⟩ := M.bind_inv h
          exact (((b3.trans (SGrowsAt.of_edgeArgs hd)).trans
            (SGrowsAt.of_sealCur he)).trans
              (SGrowsAt.of_moveTo (Or.inl hexit) hf)).trans (SGrowsAt.of_pure hg2)
  case exprBuiltin =>
    intro fenv env lctx rets op args s r s' h
    rw [trStmt] at h
    obtain ⟨as, s₁, h1, h⟩ := M.bind_inv h
    refine SGrows.trans (SGrows.of_grows (trArgs_grows args fenv env s s₁ as h1)) ?_
    by_cases hop : isHaltingOp op = true
    · rw [if_pos hop] at h
      obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
      exact SGrows.trans (SGrowsAt.of_sealCur h2) (SGrowsAt.of_pure h3)
    · rw [if_neg hop] at h
      obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
      exact SGrows.trans (SGrows.of_grows (Grows.of_emit h2)) (SGrowsAt.of_pure h3)
  case exprCall =>
    intro fenv env lctx rets fn args s r s' h
    rw [trStmt] at h
    obtain ⟨as, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨fid, s₂, h2, h⟩ := M.bind_inv h
    obtain ⟨u, s₃, h3, h4⟩ := M.bind_inv h
    exact SGrows.trans (SGrows.of_grows (trArgs_grows args fenv env s s₁ as h1))
      (SGrows.trans (SGrowsAt.of_liftO h2)
        (SGrows.trans (SGrows.of_grows (Grows.of_emit h3)) (SGrowsAt.of_pure h4)))
  case exprBad =>
    intro fenv env lctx rets e hnb hnc s r s' h
    rw [trStmt] at h
    · exact absurd h (by simp [reject])
    · exact hnb
    · exact hnc
  case breakNone =>
    intro fenv env rets s r s' h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case breakSome =>
    intro fenv env rets l s r s' h
    rw [trStmt] at h
    obtain ⟨vals, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_edgeArgs h1)
      (SGrows.trans (SGrowsAt.of_sealCur h2) (SGrowsAt.of_pure h3))
  case contNone =>
    intro fenv env rets s r s' h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case contSome =>
    intro fenv env rets l s r s' h
    rw [trStmt] at h
    obtain ⟨vals, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_edgeArgs h1)
      (SGrows.trans (SGrowsAt.of_sealCur h2) (SGrowsAt.of_pure h3))
  case leaveNone =>
    intro fenv env lctx s r s' h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case leaveSome =>
    intro fenv env lctx rs s r s' h
    rw [trStmt] at h
    obtain ⟨vals, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_edgeArgs h1)
      (SGrows.trans (SGrowsAt.of_sealCur h2) (SGrowsAt.of_pure h3))
  case casesNilNone =>
    intro fenv env lctx rets _sv _X _joinId sv X joinId s u s' h
    rw [trCases] at h
    obtain ⟨xvals, s₁, h1, h2⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_edgeArgs h1) (SGrowsAt.of_sealCur h2)
  case casesNilSome =>
    intro fenv env lctx rets _sv _X _joinId dbody ih sv X joinId s u s' h
    rw [trCases] at h
    obtain ⟨renv, s₁, h1, h2⟩ := M.bind_inv h
    refine SGrows.trans (ih s renv s₁ h1) ?_
    cases renv with
    | none => exact SGrowsAt.of_pure h2
    | some env' =>
      obtain ⟨xv, s₂, h3, h4⟩ := M.bind_inv h2
      exact SGrows.trans (SGrowsAt.of_edgeArgs h3) (SGrowsAt.of_sealCur h4)
  case casesCons =>
    intro fenv env lctx rets _sv _X _joinId lit cbody restCases dflt ihc ihr
      sv X joinId s u s' h
    rw [trCases] at h
    obtain ⟨t, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨u2, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨e, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨caseId, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨nextId, s6, h6, h⟩ := M.bind_inv h
    obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
    obtain ⟨u8, s8, h8, h⟩ := M.bind_inv h
    obtain ⟨renv, s9, h9, h⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 :=
      SGrowsAt.of_grows (Grows.of_freshVal h1)
    have a2 := a1.trans (SGrowsAt.of_grows (Grows.of_emit h2))
    have a3 := a2.trans (SGrowsAt.of_grows (Grows.of_freshVal h3))
    have a4 := a3.trans (SGrowsAt.of_grows (Grows.of_emit h4))
    have a5 := a4.trans (SGrowsAt.of_newBlock h5)
    have a6 := a5.trans (SGrowsAt.of_newBlock h6)
    have a7 := a6.trans (SGrowsAt.of_sealCur h7)
    have hcase : s.fn.blocks.size ≤ caseId := by
      rw [SGrowsAt.newBlock_id h5]; exact a4.size
    have hnext : s.fn.blocks.size ≤ nextId := by
      rw [SGrowsAt.newBlock_id h6]; exact a5.size
    have a8 := a7.trans (SGrowsAt.of_moveTo (Or.inl hcase) h8)
    have a9 := a8.trans ((ihc s8 renv s9 h9).mono a8.size)
    refine a9.trans ?_
    cases renv with
    | none =>
      obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, hc2⟩ := M.bind_inv h
      refine (SGrowsAt.of_pure ha).trans
        ((SGrowsAt.of_moveTo (Or.inl hnext) hb2).trans ?_)
      exact ((ihr sv X joinId sb u s' hc2).mono
        (Nat.le_trans (Nat.le_trans a9.size (SGrowsAt.of_pure (N := 0) ha).size)
          (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) hb2).size))
    | some env' =>
      obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
      obtain ⟨uc, sc, hc2, hd2⟩ := M.bind_inv h
      refine (SGrowsAt.of_edgeArgs ha).trans
        ((SGrowsAt.of_sealCur hb2).trans
          ((SGrowsAt.of_moveTo (Or.inl hnext) hc2).trans ?_))
      exact ((ihr sv X joinId sc u s' hd2).mono
        (Nat.le_trans (Nat.le_trans (Nat.le_trans a9.size
          (SGrowsAt.of_edgeArgs (N := 0) ha).size)
            (SGrowsAt.of_sealCur (N := 0) hb2).size)
          (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) hc2).size))

/-! ### Mutual function-table frame induction -/

def FuncFrame (fenv : FMap) (ps rs : List Ident)
    (body : List (Stmt Op)) : Prop :=
  ∀ (N : Nat) (s : BState) (g : Func) (s' : BState),
    N ≤ s.funcs.size → trFunc fenv ps rs body s = some (g, s') →
      FPrefix N s s'

def ScopeFrame (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (body : List (Stmt Op)) : Prop :=
  ∀ (N : Nat) (s : BState) (r : Option VMap) (s' : BState),
    N ≤ s.funcs.size → trScope fenv env lctx rets body s = some (r, s') →
      FPrefix N s s'

def StmtsFrame (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (d : Bool) (ss : List (Stmt Op)) : Prop :=
  ∀ (N : Nat) (s : BState) (r : Option VMap) (s' : BState),
    N ≤ s.funcs.size → FillAbove N fenv ss →
    trStmts fenv env lctx rets d ss s = some (r, s') → FPrefix N s s'

def StmtFrame (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (st : Stmt Op) : Prop :=
  ∀ (N : Nat) (s : BState) (r : Option VMap) (s' : BState),
    N ≤ s.funcs.size → trStmt fenv env lctx rets st s = some (r, s') →
      FPrefix N s s'

def CasesFrame (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (_sv : ValId) (_X : List Ident)
    (_joinId : BlockId) (cases : List (Literal × List (Stmt Op)))
    (dflt : Option (List (Stmt Op))) : Prop :=
  ∀ (sv : ValId) (X : List Ident) (joinId : BlockId) (N : Nat)
    (s : BState) (u : Unit) (s' : BState),
    N ≤ s.funcs.size →
    trCases fenv env lctx rets sv X joinId cases dflt s = some (u, s') →
      FPrefix N s s'

omit model in
theorem FillAbove.mono {N N' : Nat} (hNN' : N ≤ N')
    {fenv : FMap} {ss : List (Stmt Op)} (h : FillAbove N' fenv ss) :
    FillAbove N fenv ss := by
  intro n ps rs body hm fid hget
  exact Nat.le_trans hNN' (h n ps rs body hm fid hget)

omit model in
theorem FillAbove.tail {N : Nat} {fenv : FMap} {st : Stmt Op}
    {rest : List (Stmt Op)} (h : FillAbove N fenv (st :: rest)) :
    FillAbove N fenv rest := by
  intro n ps rs body hm
  exact h n ps rs body (by simp [hm])

omit model in
/-- Companion of `trStmt_grows` at `trScope.induct`: the same 29-case script against the same hypothesis list. The
five induct principles the `mutual` block generates share that list, so the
script instantiates verbatim; only the head and the conclusion change. -/
theorem trScope_grows : ∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (body : List (Stmt Op)),
    ScopeGrows fenv env lctx rets body := by
  refine trScope.induct FuncGrows ScopeGrows StmtsGrows StmtGrows CasesGrows
    ?trFunc ?trScope ?stmtsNil ?stmtsFunDef ?stmtsSkip ?stmtsCons
    ?block ?funDef ?letNoneBad ?letNone ?letSomeBad ?letSome ?assignBad ?assign
    ?cond ?switch ?forLoop ?exprBuiltin ?exprCall ?exprBad
    ?breakNone ?breakSome ?contNone ?contSome ?leaveNone ?leaveSome
    ?casesNilNone ?casesNilSome ?casesCons
  case trFunc =>
    intro fenv ps rs body ih s g s' h
    unfold trFunc at h
    obtain ⟨saved, s1, h1, h⟩ := M.bind_inv h
    have hsv : saved = s.fn := by
      rw [M.getFn_apply] at h1; exact (M.some_pair_inj h1).1.symm
    obtain ⟨u2, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨entry, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨pids, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨rids, s6, h6, h⟩ := M.bind_inv h
    have f1 : FGrows s s2 :=
      FGrows.trans (FGrows.of_getFn h1) (FGrows.of_setFn h2)
    have f2 : FGrows s s4 :=
      FGrows.trans f1 (FGrows.trans (FGrows.of_newBlock h3) (FGrows.of_moveTo h4))
    have f3 : FGrows s s6 :=
      FGrows.trans f2 (FGrows.trans
        (FGrows.of_grows (Grows.of_mapM_freshVal h5))
        (FGrows.of_grows (Grows.of_mapM_constZero h6)))
    -- the closing `getFn; setFn saved; pure` restores the caller's `fn`
    have hfin : ∀ (sk : BState), FGrows s sk →
        (getFn >>= fun done => setFn saved >>= fun _ =>
          (pure { params := pids, nrets := rs.length, entry := entry,
                  blocks := done.blocks } : M Func)) sk = some (g, s') →
        s'.fn = s.fn ∧ FGrows s s' := by
      intro sk hk hh
      obtain ⟨done, sa, ha, hh⟩ := M.bind_inv hh
      rw [M.getFn_apply] at ha
      obtain ⟨-, hd2⟩ := M.some_pair_inj ha
      obtain ⟨ub, sb, hb2, hc2⟩ := M.bind_inv hh
      rw [M.setFn_apply] at hb2
      obtain ⟨-, hb3⟩ := M.some_pair_inj hb2
      obtain ⟨-, hc3⟩ := M.pure_inv hc2
      refine ⟨?_, ?_⟩
      · rw [hc3, ← hb3, hsv]
      · rw [FGrows, hc3, ← hb3]
        exact hd2 ▸ hk
    by_cases hg : (!decide (ps ++ rs).Nodup) = true
    · rw [if_pos hg] at h
      obtain ⟨u7, s7, h7, -⟩ := M.bind_inv h
      exact absurd h7 (by simp [reject])
    · rw [if_neg hg] at h
      obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
      obtain ⟨renv, s8, h8, h⟩ := M.bind_inv h
      have f4 : FGrows s s8 :=
        FGrows.trans f3 (FGrows.trans (FGrows.of_pure h7)
          ((ih pids rids s7 renv s8 h8).funcsSize))
      cases renv with
      | none =>
        obtain ⟨ua, sa, ha, hh⟩ := M.bind_inv h
        exact hfin sa (FGrows.trans f4 (FGrows.of_pure ha)) hh
      | some envEnd =>
        obtain ⟨vals, sa, ha, hh⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb2, hh⟩ := M.bind_inv hh
        exact hfin sb (FGrows.trans f4 (FGrows.trans (FGrows.of_liftO ha)
          (FGrows.of_sealCur hb2))) hh
  case trScope =>
    intro fenv env lctx rets body ih s r s' h
    rw [trScope] at h
    obtain ⟨scope, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨renv, s₂, h2, h3⟩ := M.bind_inv h
    have g1 : SGrows s s₁ := allocScope_sgrows h1
    have g2 : SGrows s₁ s₂ := ih scope s₁ renv s₂ h2
    refine (g1.trans g2).trans ?_
    cases renv with
    | none => exact SGrowsAt.of_pure h3
    | some e => exact SGrowsAt.of_pure h3
    
  case stmtsNil =>
    intro fenv env lctx rets d s r s' h
    rw [trStmts] at h
    exact SGrowsAt.of_pure h
  case stmtsFunDef =>
    intro fenv env lctx rets d n ps rs fbody rest ihf ihr s r s' h
    rw [trStmts] at h
    obtain ⟨fid, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨g, s₂, h2, h⟩ := M.bind_inv h
    obtain ⟨u, s₃, h3, h4⟩ := M.bind_inv h
    obtain ⟨hfn, hfg⟩ := ihf s₁ g s₂ h2
    exact (((SGrows.trans (SGrowsAt.of_liftO h1)
      (SGrowsAt.of_funcsOnly hfn hfg)).trans
        (SGrowsAt.of_fillFunc h3)).trans (ihr s₃ r s' h4))
  case stmtsSkip =>
    intro fenv env lctx rets st rest hnf ih s r s' h
    rw [trStmts] at h
    · split at h
      · exact ih s r s' h
      · rename_i hc; exact absurd rfl hc
    · exact hnf
  case stmtsCons =>
    intro fenv env lctx rets d st rest hnf hd ih4 ih3n ih3t s r s' h
    rw [trStmts] at h
    · rw [if_neg hd] at h
      obtain ⟨renv, s₁, h1, h2⟩ := M.bind_inv h
      have g1 : SGrows s s₁ := ih4 s renv s₁ h1
      cases renv with
      | some env' => exact SGrows.trans g1 (ih3n env' s₁ r s' h2)
      | none => exact SGrows.trans g1 (ih3t s₁ r s' h2)
    · exact hnf
  case block =>
    intro fenv env lctx rets body ih s r s' h
    rw [trStmt] at h
    exact ih s r s' h
  case funDef =>
    intro fenv env lctx rets name ps rs body s r s' h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case letNoneBad =>
    intro fenv env lctx rets vars hgate s r s' h
    rw [trStmt] at h
    rw [if_pos hgate] at h
    obtain ⟨u, s₁, h1, -⟩ := M.bind_inv h
    exact absurd h1 (by simp [reject])
  case letNone =>
    intro fenv env lctx rets vars hgate s r s' h
    rw [trStmt] at h
    rw [if_neg hgate] at h
    obtain ⟨u, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_pure h1)
      (SGrows.trans (SGrows.of_grows (Grows.of_mapM_constZero h2))
        (SGrowsAt.of_pure h3))
  case letSomeBad =>
    intro fenv env lctx rets vars e hgate s r s' h
    rw [trStmt] at h
    rw [if_pos hgate] at h
    obtain ⟨u, s₁, h1, -⟩ := M.bind_inv h
    exact absurd h1 (by simp [reject])
  case letSome =>
    intro fenv env lctx rets vars e hgate s r s' h
    rw [trStmt] at h
    rw [if_neg hgate] at h
    obtain ⟨u, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_pure h1)
      (SGrows.trans (SGrows.of_grows (trExprN_grows h2)) (SGrowsAt.of_pure h3))
  case assignBad =>
    intro fenv env lctx rets vars e hgate s r s' h
    rw [trStmt] at h
    rw [if_pos hgate] at h
    obtain ⟨u, s₁, h1, -⟩ := M.bind_inv h
    exact absurd h1 (by simp [reject])
  case assign =>
    intro fenv env lctx rets vars e hgate s r s' h
    rw [trStmt] at h
    rw [if_neg hgate] at h
    obtain ⟨u, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_pure h1)
      (SGrows.trans (SGrows.of_grows (trExprN_grows h2)) (SGrowsAt.of_pure h3))
  case cond =>
    intro fenv env lctx rets c body ih s r s' h
    rw [trStmt] at h
    obtain ⟨cv, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨xvals, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨bodyId, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨joinParams, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨joinId, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨u6, s6, h6, h⟩ := M.bind_inv h
    obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
    obtain ⟨renv, s8, h8, h⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 :=
      SGrowsAt.of_grows (trExpr_grows c fenv env s s1 cv h1)
    have a2 := a1.trans (SGrowsAt.of_edgeArgs h2)
    have a3 := a2.trans (SGrowsAt.of_newBlock h3)
    have a4 := a3.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h4))
    have a5 := a4.trans (SGrowsAt.of_newBlock h5)
    have a6 := a5.trans (SGrowsAt.of_sealCur h6)
    have hbody : s.fn.blocks.size ≤ bodyId := by
      rw [SGrowsAt.newBlock_id h3]; exact a2.size
    have hjoin : s.fn.blocks.size ≤ joinId := by
      rw [SGrowsAt.newBlock_id h5]; exact a4.size
    have a7 := a6.trans (SGrowsAt.of_moveTo (Or.inl hbody) h7)
    have a8 := a7.trans ((ih s7 renv s8 h8).mono a7.size)
    refine a8.trans ?_
    cases renv with
    | none =>
      obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, hc2⟩ := M.bind_inv h
      exact (SGrowsAt.of_pure ha).trans
        ((SGrowsAt.of_moveTo (Or.inl hjoin) hb2).trans (SGrowsAt.of_pure hc2))
    | some env' =>
      obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
      obtain ⟨uc, sc, hc2, hd2⟩ := M.bind_inv h
      exact (SGrowsAt.of_edgeArgs ha).trans
        ((SGrowsAt.of_sealCur hb2).trans
          ((SGrowsAt.of_moveTo (Or.inl hjoin) hc2).trans (SGrowsAt.of_pure hd2)))
  case switch =>
    intro fenv env lctx rets c cases dflt ih s r s' h
    unfold trStmt at h
    obtain ⟨sv, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨joinParams, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨joinId, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨u5, s5, h5, h6⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 :=
      SGrowsAt.of_grows (trExpr_grows c fenv env s s1 sv h1)
    have a2 := a1.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h2))
    have a3 := a2.trans (SGrowsAt.of_newBlock h3)
    have hjoin : s.fn.blocks.size ≤ joinId := by
      rw [SGrowsAt.newBlock_id h3]; exact a2.size
    have a4 := a3.trans ((ih 0 0 _ _ _ s3 u4 s4 h4).mono a3.size)
    exact (a4.trans (SGrowsAt.of_moveTo (Or.inl hjoin) h5)).trans
      (SGrowsAt.of_pure h6)
  case forLoop =>
    intro fenv env lctx rets init c post body ihInit ihBody ihPost s r s' h
    unfold trStmt at h
    obtain ⟨scope, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨rinit, s2, h2, h⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 := allocScope_sgrows h1
    have a2 := a1.trans ((ihInit scope s1 rinit s2 h2).mono a1.size)
    cases rinit with
    | none => exact a2.trans (SGrowsAt.of_pure h)
    | some envI =>
      obtain ⟨xvals, s3, h3, h⟩ := M.bind_inv h
      obtain ⟨hParams, s4, h4, h⟩ := M.bind_inv h
      obtain ⟨hId, s5, h5, h⟩ := M.bind_inv h
      obtain ⟨exitParams, s6, h6, h⟩ := M.bind_inv h
      obtain ⟨exitId, s7, h7, h⟩ := M.bind_inv h
      obtain ⟨postParams, s8, h8, h⟩ := M.bind_inv h
      obtain ⟨postId, s9, h9, h⟩ := M.bind_inv h
      obtain ⟨u10, s10, h10, h⟩ := M.bind_inv h
      obtain ⟨u11, s11, h11, h⟩ := M.bind_inv h
      obtain ⟨cv, s12, h12, h⟩ := M.bind_inv h
      obtain ⟨bodyId, s13, h13, h⟩ := M.bind_inv h
      obtain ⟨hX, s14, h14, h⟩ := M.bind_inv h
      obtain ⟨u15, s15, h15, h⟩ := M.bind_inv h
      obtain ⟨u16, s16, h16, h⟩ := M.bind_inv h
      obtain ⟨renvB, s17, h17, h⟩ := M.bind_inv h
      have a3 := a2.trans (SGrowsAt.of_edgeArgs h3)
      have a4 := a3.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h4))
      have a5 := a4.trans (SGrowsAt.of_newBlock h5)
      have a6 := a5.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h6))
      have a7 := a6.trans (SGrowsAt.of_newBlock h7)
      have a8 := a7.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h8))
      have a9 := a8.trans (SGrowsAt.of_newBlock h9)
      have a10 := a9.trans (SGrowsAt.of_sealCur h10)
      have hhdr : s.fn.blocks.size ≤ hId := by
        rw [SGrowsAt.newBlock_id h5]; exact a4.size
      have hexit : s.fn.blocks.size ≤ exitId := by
        rw [SGrowsAt.newBlock_id h7]; exact a6.size
      have hpost : s.fn.blocks.size ≤ postId := by
        rw [SGrowsAt.newBlock_id h9]; exact a8.size
      have a11 := a10.trans (SGrowsAt.of_moveTo (Or.inl hhdr) h11)
      have a12 := a11.trans (SGrowsAt.of_grows
        (trExpr_grows c (scope :: fenv) _ s11 s12 cv h12))
      have a13 := a12.trans (SGrowsAt.of_newBlock h13)
      have a14 := a13.trans (SGrowsAt.of_edgeArgs h14)
      have a15 := a14.trans (SGrowsAt.of_sealCur h15)
      have hbody : s.fn.blocks.size ≤ bodyId := by
        rw [SGrowsAt.newBlock_id h13]; exact a12.size
      have a16 := a15.trans (SGrowsAt.of_moveTo (Or.inl hbody) h16)
      have a17 := a16.trans
        ((ihBody scope envI hParams exitId postId s16 renvB s17 h17).mono a16.size)
      -- the `post` scope and the loop exit, under both `if let` branches
      cases renvB with
      | none =>
        obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
        obtain ⟨renvP, sc, hc2, h⟩ := M.bind_inv h
        have b1 := a17.trans (SGrowsAt.of_pure ha)
        have b2 := b1.trans (SGrowsAt.of_moveTo (Or.inl hpost) hb2)
        have b3 := b2.trans
          ((ihPost scope envI postParams sb renvP sc hc2).mono b2.size)
        cases renvP with
        | none =>
          obtain ⟨ud, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, hf⟩ := M.bind_inv h
          exact ((b3.trans (SGrowsAt.of_pure hd)).trans
            (SGrowsAt.of_moveTo (Or.inl hexit) he)).trans (SGrowsAt.of_pure hf)
        | some envP' =>
          obtain ⟨xvP, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, h⟩ := M.bind_inv h
          obtain ⟨uf, sf, hf, hg2⟩ := M.bind_inv h
          exact (((b3.trans (SGrowsAt.of_edgeArgs hd)).trans
            (SGrowsAt.of_sealCur he)).trans
              (SGrowsAt.of_moveTo (Or.inl hexit) hf)).trans (SGrowsAt.of_pure hg2)
      | some envB =>
        obtain ⟨xvB, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ua', sa', ha', h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
        obtain ⟨renvP, sc, hc2, h⟩ := M.bind_inv h
        have b0 := a17.trans (SGrowsAt.of_edgeArgs ha)
        have b1 := b0.trans (SGrowsAt.of_sealCur ha')
        have b2 := b1.trans (SGrowsAt.of_moveTo (Or.inl hpost) hb2)
        have b3 := b2.trans
          ((ihPost scope envI postParams sb renvP sc hc2).mono b2.size)
        cases renvP with
        | none =>
          obtain ⟨ud, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, hf⟩ := M.bind_inv h
          exact ((b3.trans (SGrowsAt.of_pure hd)).trans
            (SGrowsAt.of_moveTo (Or.inl hexit) he)).trans (SGrowsAt.of_pure hf)
        | some envP' =>
          obtain ⟨xvP, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, h⟩ := M.bind_inv h
          obtain ⟨uf, sf, hf, hg2⟩ := M.bind_inv h
          exact (((b3.trans (SGrowsAt.of_edgeArgs hd)).trans
            (SGrowsAt.of_sealCur he)).trans
              (SGrowsAt.of_moveTo (Or.inl hexit) hf)).trans (SGrowsAt.of_pure hg2)
  case exprBuiltin =>
    intro fenv env lctx rets op args s r s' h
    rw [trStmt] at h
    obtain ⟨as, s₁, h1, h⟩ := M.bind_inv h
    refine SGrows.trans (SGrows.of_grows (trArgs_grows args fenv env s s₁ as h1)) ?_
    by_cases hop : isHaltingOp op = true
    · rw [if_pos hop] at h
      obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
      exact SGrows.trans (SGrowsAt.of_sealCur h2) (SGrowsAt.of_pure h3)
    · rw [if_neg hop] at h
      obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
      exact SGrows.trans (SGrows.of_grows (Grows.of_emit h2)) (SGrowsAt.of_pure h3)
  case exprCall =>
    intro fenv env lctx rets fn args s r s' h
    rw [trStmt] at h
    obtain ⟨as, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨fid, s₂, h2, h⟩ := M.bind_inv h
    obtain ⟨u, s₃, h3, h4⟩ := M.bind_inv h
    exact SGrows.trans (SGrows.of_grows (trArgs_grows args fenv env s s₁ as h1))
      (SGrows.trans (SGrowsAt.of_liftO h2)
        (SGrows.trans (SGrows.of_grows (Grows.of_emit h3)) (SGrowsAt.of_pure h4)))
  case exprBad =>
    intro fenv env lctx rets e hnb hnc s r s' h
    rw [trStmt] at h
    · exact absurd h (by simp [reject])
    · exact hnb
    · exact hnc
  case breakNone =>
    intro fenv env rets s r s' h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case breakSome =>
    intro fenv env rets l s r s' h
    rw [trStmt] at h
    obtain ⟨vals, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_edgeArgs h1)
      (SGrows.trans (SGrowsAt.of_sealCur h2) (SGrowsAt.of_pure h3))
  case contNone =>
    intro fenv env rets s r s' h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case contSome =>
    intro fenv env rets l s r s' h
    rw [trStmt] at h
    obtain ⟨vals, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_edgeArgs h1)
      (SGrows.trans (SGrowsAt.of_sealCur h2) (SGrowsAt.of_pure h3))
  case leaveNone =>
    intro fenv env lctx s r s' h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case leaveSome =>
    intro fenv env lctx rs s r s' h
    rw [trStmt] at h
    obtain ⟨vals, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_edgeArgs h1)
      (SGrows.trans (SGrowsAt.of_sealCur h2) (SGrowsAt.of_pure h3))
  case casesNilNone =>
    intro fenv env lctx rets _sv _X _joinId sv X joinId s u s' h
    rw [trCases] at h
    obtain ⟨xvals, s₁, h1, h2⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_edgeArgs h1) (SGrowsAt.of_sealCur h2)
  case casesNilSome =>
    intro fenv env lctx rets _sv _X _joinId dbody ih sv X joinId s u s' h
    rw [trCases] at h
    obtain ⟨renv, s₁, h1, h2⟩ := M.bind_inv h
    refine SGrows.trans (ih s renv s₁ h1) ?_
    cases renv with
    | none => exact SGrowsAt.of_pure h2
    | some env' =>
      obtain ⟨xv, s₂, h3, h4⟩ := M.bind_inv h2
      exact SGrows.trans (SGrowsAt.of_edgeArgs h3) (SGrowsAt.of_sealCur h4)
  case casesCons =>
    intro fenv env lctx rets _sv _X _joinId lit cbody restCases dflt ihc ihr
      sv X joinId s u s' h
    rw [trCases] at h
    obtain ⟨t, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨u2, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨e, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨caseId, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨nextId, s6, h6, h⟩ := M.bind_inv h
    obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
    obtain ⟨u8, s8, h8, h⟩ := M.bind_inv h
    obtain ⟨renv, s9, h9, h⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 :=
      SGrowsAt.of_grows (Grows.of_freshVal h1)
    have a2 := a1.trans (SGrowsAt.of_grows (Grows.of_emit h2))
    have a3 := a2.trans (SGrowsAt.of_grows (Grows.of_freshVal h3))
    have a4 := a3.trans (SGrowsAt.of_grows (Grows.of_emit h4))
    have a5 := a4.trans (SGrowsAt.of_newBlock h5)
    have a6 := a5.trans (SGrowsAt.of_newBlock h6)
    have a7 := a6.trans (SGrowsAt.of_sealCur h7)
    have hcase : s.fn.blocks.size ≤ caseId := by
      rw [SGrowsAt.newBlock_id h5]; exact a4.size
    have hnext : s.fn.blocks.size ≤ nextId := by
      rw [SGrowsAt.newBlock_id h6]; exact a5.size
    have a8 := a7.trans (SGrowsAt.of_moveTo (Or.inl hcase) h8)
    have a9 := a8.trans ((ihc s8 renv s9 h9).mono a8.size)
    refine a9.trans ?_
    cases renv with
    | none =>
      obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, hc2⟩ := M.bind_inv h
      refine (SGrowsAt.of_pure ha).trans
        ((SGrowsAt.of_moveTo (Or.inl hnext) hb2).trans ?_)
      exact ((ihr sv X joinId sb u s' hc2).mono
        (Nat.le_trans (Nat.le_trans a9.size (SGrowsAt.of_pure (N := 0) ha).size)
          (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) hb2).size))
    | some env' =>
      obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
      obtain ⟨uc, sc, hc2, hd2⟩ := M.bind_inv h
      refine (SGrowsAt.of_edgeArgs ha).trans
        ((SGrowsAt.of_sealCur hb2).trans
          ((SGrowsAt.of_moveTo (Or.inl hnext) hc2).trans ?_))
      exact ((ihr sv X joinId sc u s' hd2).mono
        (Nat.le_trans (Nat.le_trans (Nat.le_trans a9.size
          (SGrowsAt.of_edgeArgs (N := 0) ha).size)
            (SGrowsAt.of_sealCur (N := 0) hb2).size)
          (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) hc2).size))

omit model in
/-- Companion of `trStmt_grows` at `trStmts.induct`: the same 29-case script against the same hypothesis list. The
five induct principles the `mutual` block generates share that list, so the
script instantiates verbatim; only the head and the conclusion change. -/
theorem trStmts_grows : ∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (d : Bool) (ss : List (Stmt Op)),
    StmtsGrows fenv env lctx rets d ss := by
  refine trStmts.induct FuncGrows ScopeGrows StmtsGrows StmtGrows CasesGrows
    ?trFunc ?trScope ?stmtsNil ?stmtsFunDef ?stmtsSkip ?stmtsCons
    ?block ?funDef ?letNoneBad ?letNone ?letSomeBad ?letSome ?assignBad ?assign
    ?cond ?switch ?forLoop ?exprBuiltin ?exprCall ?exprBad
    ?breakNone ?breakSome ?contNone ?contSome ?leaveNone ?leaveSome
    ?casesNilNone ?casesNilSome ?casesCons
  case trFunc =>
    intro fenv ps rs body ih s g s' h
    unfold trFunc at h
    obtain ⟨saved, s1, h1, h⟩ := M.bind_inv h
    have hsv : saved = s.fn := by
      rw [M.getFn_apply] at h1; exact (M.some_pair_inj h1).1.symm
    obtain ⟨u2, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨entry, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨pids, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨rids, s6, h6, h⟩ := M.bind_inv h
    have f1 : FGrows s s2 :=
      FGrows.trans (FGrows.of_getFn h1) (FGrows.of_setFn h2)
    have f2 : FGrows s s4 :=
      FGrows.trans f1 (FGrows.trans (FGrows.of_newBlock h3) (FGrows.of_moveTo h4))
    have f3 : FGrows s s6 :=
      FGrows.trans f2 (FGrows.trans
        (FGrows.of_grows (Grows.of_mapM_freshVal h5))
        (FGrows.of_grows (Grows.of_mapM_constZero h6)))
    -- the closing `getFn; setFn saved; pure` restores the caller's `fn`
    have hfin : ∀ (sk : BState), FGrows s sk →
        (getFn >>= fun done => setFn saved >>= fun _ =>
          (pure { params := pids, nrets := rs.length, entry := entry,
                  blocks := done.blocks } : M Func)) sk = some (g, s') →
        s'.fn = s.fn ∧ FGrows s s' := by
      intro sk hk hh
      obtain ⟨done, sa, ha, hh⟩ := M.bind_inv hh
      rw [M.getFn_apply] at ha
      obtain ⟨-, hd2⟩ := M.some_pair_inj ha
      obtain ⟨ub, sb, hb2, hc2⟩ := M.bind_inv hh
      rw [M.setFn_apply] at hb2
      obtain ⟨-, hb3⟩ := M.some_pair_inj hb2
      obtain ⟨-, hc3⟩ := M.pure_inv hc2
      refine ⟨?_, ?_⟩
      · rw [hc3, ← hb3, hsv]
      · rw [FGrows, hc3, ← hb3]
        exact hd2 ▸ hk
    by_cases hg : (!decide (ps ++ rs).Nodup) = true
    · rw [if_pos hg] at h
      obtain ⟨u7, s7, h7, -⟩ := M.bind_inv h
      exact absurd h7 (by simp [reject])
    · rw [if_neg hg] at h
      obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
      obtain ⟨renv, s8, h8, h⟩ := M.bind_inv h
      have f4 : FGrows s s8 :=
        FGrows.trans f3 (FGrows.trans (FGrows.of_pure h7)
          ((ih pids rids s7 renv s8 h8).funcsSize))
      cases renv with
      | none =>
        obtain ⟨ua, sa, ha, hh⟩ := M.bind_inv h
        exact hfin sa (FGrows.trans f4 (FGrows.of_pure ha)) hh
      | some envEnd =>
        obtain ⟨vals, sa, ha, hh⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb2, hh⟩ := M.bind_inv hh
        exact hfin sb (FGrows.trans f4 (FGrows.trans (FGrows.of_liftO ha)
          (FGrows.of_sealCur hb2))) hh
  case trScope =>
    intro fenv env lctx rets body ih s r s' h
    rw [trScope] at h
    obtain ⟨scope, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨renv, s₂, h2, h3⟩ := M.bind_inv h
    have g1 : SGrows s s₁ := allocScope_sgrows h1
    have g2 : SGrows s₁ s₂ := ih scope s₁ renv s₂ h2
    refine (g1.trans g2).trans ?_
    cases renv with
    | none => exact SGrowsAt.of_pure h3
    | some e => exact SGrowsAt.of_pure h3
    
  case stmtsNil =>
    intro fenv env lctx rets d s r s' h
    rw [trStmts] at h
    exact SGrowsAt.of_pure h
  case stmtsFunDef =>
    intro fenv env lctx rets d n ps rs fbody rest ihf ihr s r s' h
    rw [trStmts] at h
    obtain ⟨fid, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨g, s₂, h2, h⟩ := M.bind_inv h
    obtain ⟨u, s₃, h3, h4⟩ := M.bind_inv h
    obtain ⟨hfn, hfg⟩ := ihf s₁ g s₂ h2
    exact (((SGrows.trans (SGrowsAt.of_liftO h1)
      (SGrowsAt.of_funcsOnly hfn hfg)).trans
        (SGrowsAt.of_fillFunc h3)).trans (ihr s₃ r s' h4))
  case stmtsSkip =>
    intro fenv env lctx rets st rest hnf ih s r s' h
    rw [trStmts] at h
    · split at h
      · exact ih s r s' h
      · rename_i hc; exact absurd rfl hc
    · exact hnf
  case stmtsCons =>
    intro fenv env lctx rets d st rest hnf hd ih4 ih3n ih3t s r s' h
    rw [trStmts] at h
    · rw [if_neg hd] at h
      obtain ⟨renv, s₁, h1, h2⟩ := M.bind_inv h
      have g1 : SGrows s s₁ := ih4 s renv s₁ h1
      cases renv with
      | some env' => exact SGrows.trans g1 (ih3n env' s₁ r s' h2)
      | none => exact SGrows.trans g1 (ih3t s₁ r s' h2)
    · exact hnf
  case block =>
    intro fenv env lctx rets body ih s r s' h
    rw [trStmt] at h
    exact ih s r s' h
  case funDef =>
    intro fenv env lctx rets name ps rs body s r s' h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case letNoneBad =>
    intro fenv env lctx rets vars hgate s r s' h
    rw [trStmt] at h
    rw [if_pos hgate] at h
    obtain ⟨u, s₁, h1, -⟩ := M.bind_inv h
    exact absurd h1 (by simp [reject])
  case letNone =>
    intro fenv env lctx rets vars hgate s r s' h
    rw [trStmt] at h
    rw [if_neg hgate] at h
    obtain ⟨u, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_pure h1)
      (SGrows.trans (SGrows.of_grows (Grows.of_mapM_constZero h2))
        (SGrowsAt.of_pure h3))
  case letSomeBad =>
    intro fenv env lctx rets vars e hgate s r s' h
    rw [trStmt] at h
    rw [if_pos hgate] at h
    obtain ⟨u, s₁, h1, -⟩ := M.bind_inv h
    exact absurd h1 (by simp [reject])
  case letSome =>
    intro fenv env lctx rets vars e hgate s r s' h
    rw [trStmt] at h
    rw [if_neg hgate] at h
    obtain ⟨u, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_pure h1)
      (SGrows.trans (SGrows.of_grows (trExprN_grows h2)) (SGrowsAt.of_pure h3))
  case assignBad =>
    intro fenv env lctx rets vars e hgate s r s' h
    rw [trStmt] at h
    rw [if_pos hgate] at h
    obtain ⟨u, s₁, h1, -⟩ := M.bind_inv h
    exact absurd h1 (by simp [reject])
  case assign =>
    intro fenv env lctx rets vars e hgate s r s' h
    rw [trStmt] at h
    rw [if_neg hgate] at h
    obtain ⟨u, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_pure h1)
      (SGrows.trans (SGrows.of_grows (trExprN_grows h2)) (SGrowsAt.of_pure h3))
  case cond =>
    intro fenv env lctx rets c body ih s r s' h
    rw [trStmt] at h
    obtain ⟨cv, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨xvals, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨bodyId, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨joinParams, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨joinId, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨u6, s6, h6, h⟩ := M.bind_inv h
    obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
    obtain ⟨renv, s8, h8, h⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 :=
      SGrowsAt.of_grows (trExpr_grows c fenv env s s1 cv h1)
    have a2 := a1.trans (SGrowsAt.of_edgeArgs h2)
    have a3 := a2.trans (SGrowsAt.of_newBlock h3)
    have a4 := a3.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h4))
    have a5 := a4.trans (SGrowsAt.of_newBlock h5)
    have a6 := a5.trans (SGrowsAt.of_sealCur h6)
    have hbody : s.fn.blocks.size ≤ bodyId := by
      rw [SGrowsAt.newBlock_id h3]; exact a2.size
    have hjoin : s.fn.blocks.size ≤ joinId := by
      rw [SGrowsAt.newBlock_id h5]; exact a4.size
    have a7 := a6.trans (SGrowsAt.of_moveTo (Or.inl hbody) h7)
    have a8 := a7.trans ((ih s7 renv s8 h8).mono a7.size)
    refine a8.trans ?_
    cases renv with
    | none =>
      obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, hc2⟩ := M.bind_inv h
      exact (SGrowsAt.of_pure ha).trans
        ((SGrowsAt.of_moveTo (Or.inl hjoin) hb2).trans (SGrowsAt.of_pure hc2))
    | some env' =>
      obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
      obtain ⟨uc, sc, hc2, hd2⟩ := M.bind_inv h
      exact (SGrowsAt.of_edgeArgs ha).trans
        ((SGrowsAt.of_sealCur hb2).trans
          ((SGrowsAt.of_moveTo (Or.inl hjoin) hc2).trans (SGrowsAt.of_pure hd2)))
  case switch =>
    intro fenv env lctx rets c cases dflt ih s r s' h
    unfold trStmt at h
    obtain ⟨sv, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨joinParams, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨joinId, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨u5, s5, h5, h6⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 :=
      SGrowsAt.of_grows (trExpr_grows c fenv env s s1 sv h1)
    have a2 := a1.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h2))
    have a3 := a2.trans (SGrowsAt.of_newBlock h3)
    have hjoin : s.fn.blocks.size ≤ joinId := by
      rw [SGrowsAt.newBlock_id h3]; exact a2.size
    have a4 := a3.trans ((ih 0 0 _ _ _ s3 u4 s4 h4).mono a3.size)
    exact (a4.trans (SGrowsAt.of_moveTo (Or.inl hjoin) h5)).trans
      (SGrowsAt.of_pure h6)
  case forLoop =>
    intro fenv env lctx rets init c post body ihInit ihBody ihPost s r s' h
    unfold trStmt at h
    obtain ⟨scope, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨rinit, s2, h2, h⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 := allocScope_sgrows h1
    have a2 := a1.trans ((ihInit scope s1 rinit s2 h2).mono a1.size)
    cases rinit with
    | none => exact a2.trans (SGrowsAt.of_pure h)
    | some envI =>
      obtain ⟨xvals, s3, h3, h⟩ := M.bind_inv h
      obtain ⟨hParams, s4, h4, h⟩ := M.bind_inv h
      obtain ⟨hId, s5, h5, h⟩ := M.bind_inv h
      obtain ⟨exitParams, s6, h6, h⟩ := M.bind_inv h
      obtain ⟨exitId, s7, h7, h⟩ := M.bind_inv h
      obtain ⟨postParams, s8, h8, h⟩ := M.bind_inv h
      obtain ⟨postId, s9, h9, h⟩ := M.bind_inv h
      obtain ⟨u10, s10, h10, h⟩ := M.bind_inv h
      obtain ⟨u11, s11, h11, h⟩ := M.bind_inv h
      obtain ⟨cv, s12, h12, h⟩ := M.bind_inv h
      obtain ⟨bodyId, s13, h13, h⟩ := M.bind_inv h
      obtain ⟨hX, s14, h14, h⟩ := M.bind_inv h
      obtain ⟨u15, s15, h15, h⟩ := M.bind_inv h
      obtain ⟨u16, s16, h16, h⟩ := M.bind_inv h
      obtain ⟨renvB, s17, h17, h⟩ := M.bind_inv h
      have a3 := a2.trans (SGrowsAt.of_edgeArgs h3)
      have a4 := a3.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h4))
      have a5 := a4.trans (SGrowsAt.of_newBlock h5)
      have a6 := a5.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h6))
      have a7 := a6.trans (SGrowsAt.of_newBlock h7)
      have a8 := a7.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h8))
      have a9 := a8.trans (SGrowsAt.of_newBlock h9)
      have a10 := a9.trans (SGrowsAt.of_sealCur h10)
      have hhdr : s.fn.blocks.size ≤ hId := by
        rw [SGrowsAt.newBlock_id h5]; exact a4.size
      have hexit : s.fn.blocks.size ≤ exitId := by
        rw [SGrowsAt.newBlock_id h7]; exact a6.size
      have hpost : s.fn.blocks.size ≤ postId := by
        rw [SGrowsAt.newBlock_id h9]; exact a8.size
      have a11 := a10.trans (SGrowsAt.of_moveTo (Or.inl hhdr) h11)
      have a12 := a11.trans (SGrowsAt.of_grows
        (trExpr_grows c (scope :: fenv) _ s11 s12 cv h12))
      have a13 := a12.trans (SGrowsAt.of_newBlock h13)
      have a14 := a13.trans (SGrowsAt.of_edgeArgs h14)
      have a15 := a14.trans (SGrowsAt.of_sealCur h15)
      have hbody : s.fn.blocks.size ≤ bodyId := by
        rw [SGrowsAt.newBlock_id h13]; exact a12.size
      have a16 := a15.trans (SGrowsAt.of_moveTo (Or.inl hbody) h16)
      have a17 := a16.trans
        ((ihBody scope envI hParams exitId postId s16 renvB s17 h17).mono a16.size)
      -- the `post` scope and the loop exit, under both `if let` branches
      cases renvB with
      | none =>
        obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
        obtain ⟨renvP, sc, hc2, h⟩ := M.bind_inv h
        have b1 := a17.trans (SGrowsAt.of_pure ha)
        have b2 := b1.trans (SGrowsAt.of_moveTo (Or.inl hpost) hb2)
        have b3 := b2.trans
          ((ihPost scope envI postParams sb renvP sc hc2).mono b2.size)
        cases renvP with
        | none =>
          obtain ⟨ud, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, hf⟩ := M.bind_inv h
          exact ((b3.trans (SGrowsAt.of_pure hd)).trans
            (SGrowsAt.of_moveTo (Or.inl hexit) he)).trans (SGrowsAt.of_pure hf)
        | some envP' =>
          obtain ⟨xvP, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, h⟩ := M.bind_inv h
          obtain ⟨uf, sf, hf, hg2⟩ := M.bind_inv h
          exact (((b3.trans (SGrowsAt.of_edgeArgs hd)).trans
            (SGrowsAt.of_sealCur he)).trans
              (SGrowsAt.of_moveTo (Or.inl hexit) hf)).trans (SGrowsAt.of_pure hg2)
      | some envB =>
        obtain ⟨xvB, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ua', sa', ha', h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
        obtain ⟨renvP, sc, hc2, h⟩ := M.bind_inv h
        have b0 := a17.trans (SGrowsAt.of_edgeArgs ha)
        have b1 := b0.trans (SGrowsAt.of_sealCur ha')
        have b2 := b1.trans (SGrowsAt.of_moveTo (Or.inl hpost) hb2)
        have b3 := b2.trans
          ((ihPost scope envI postParams sb renvP sc hc2).mono b2.size)
        cases renvP with
        | none =>
          obtain ⟨ud, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, hf⟩ := M.bind_inv h
          exact ((b3.trans (SGrowsAt.of_pure hd)).trans
            (SGrowsAt.of_moveTo (Or.inl hexit) he)).trans (SGrowsAt.of_pure hf)
        | some envP' =>
          obtain ⟨xvP, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, h⟩ := M.bind_inv h
          obtain ⟨uf, sf, hf, hg2⟩ := M.bind_inv h
          exact (((b3.trans (SGrowsAt.of_edgeArgs hd)).trans
            (SGrowsAt.of_sealCur he)).trans
              (SGrowsAt.of_moveTo (Or.inl hexit) hf)).trans (SGrowsAt.of_pure hg2)
  case exprBuiltin =>
    intro fenv env lctx rets op args s r s' h
    rw [trStmt] at h
    obtain ⟨as, s₁, h1, h⟩ := M.bind_inv h
    refine SGrows.trans (SGrows.of_grows (trArgs_grows args fenv env s s₁ as h1)) ?_
    by_cases hop : isHaltingOp op = true
    · rw [if_pos hop] at h
      obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
      exact SGrows.trans (SGrowsAt.of_sealCur h2) (SGrowsAt.of_pure h3)
    · rw [if_neg hop] at h
      obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
      exact SGrows.trans (SGrows.of_grows (Grows.of_emit h2)) (SGrowsAt.of_pure h3)
  case exprCall =>
    intro fenv env lctx rets fn args s r s' h
    rw [trStmt] at h
    obtain ⟨as, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨fid, s₂, h2, h⟩ := M.bind_inv h
    obtain ⟨u, s₃, h3, h4⟩ := M.bind_inv h
    exact SGrows.trans (SGrows.of_grows (trArgs_grows args fenv env s s₁ as h1))
      (SGrows.trans (SGrowsAt.of_liftO h2)
        (SGrows.trans (SGrows.of_grows (Grows.of_emit h3)) (SGrowsAt.of_pure h4)))
  case exprBad =>
    intro fenv env lctx rets e hnb hnc s r s' h
    rw [trStmt] at h
    · exact absurd h (by simp [reject])
    · exact hnb
    · exact hnc
  case breakNone =>
    intro fenv env rets s r s' h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case breakSome =>
    intro fenv env rets l s r s' h
    rw [trStmt] at h
    obtain ⟨vals, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_edgeArgs h1)
      (SGrows.trans (SGrowsAt.of_sealCur h2) (SGrowsAt.of_pure h3))
  case contNone =>
    intro fenv env rets s r s' h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case contSome =>
    intro fenv env rets l s r s' h
    rw [trStmt] at h
    obtain ⟨vals, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_edgeArgs h1)
      (SGrows.trans (SGrowsAt.of_sealCur h2) (SGrowsAt.of_pure h3))
  case leaveNone =>
    intro fenv env lctx s r s' h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case leaveSome =>
    intro fenv env lctx rs s r s' h
    rw [trStmt] at h
    obtain ⟨vals, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_edgeArgs h1)
      (SGrows.trans (SGrowsAt.of_sealCur h2) (SGrowsAt.of_pure h3))
  case casesNilNone =>
    intro fenv env lctx rets _sv _X _joinId sv X joinId s u s' h
    rw [trCases] at h
    obtain ⟨xvals, s₁, h1, h2⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_edgeArgs h1) (SGrowsAt.of_sealCur h2)
  case casesNilSome =>
    intro fenv env lctx rets _sv _X _joinId dbody ih sv X joinId s u s' h
    rw [trCases] at h
    obtain ⟨renv, s₁, h1, h2⟩ := M.bind_inv h
    refine SGrows.trans (ih s renv s₁ h1) ?_
    cases renv with
    | none => exact SGrowsAt.of_pure h2
    | some env' =>
      obtain ⟨xv, s₂, h3, h4⟩ := M.bind_inv h2
      exact SGrows.trans (SGrowsAt.of_edgeArgs h3) (SGrowsAt.of_sealCur h4)
  case casesCons =>
    intro fenv env lctx rets _sv _X _joinId lit cbody restCases dflt ihc ihr
      sv X joinId s u s' h
    rw [trCases] at h
    obtain ⟨t, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨u2, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨e, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨caseId, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨nextId, s6, h6, h⟩ := M.bind_inv h
    obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
    obtain ⟨u8, s8, h8, h⟩ := M.bind_inv h
    obtain ⟨renv, s9, h9, h⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 :=
      SGrowsAt.of_grows (Grows.of_freshVal h1)
    have a2 := a1.trans (SGrowsAt.of_grows (Grows.of_emit h2))
    have a3 := a2.trans (SGrowsAt.of_grows (Grows.of_freshVal h3))
    have a4 := a3.trans (SGrowsAt.of_grows (Grows.of_emit h4))
    have a5 := a4.trans (SGrowsAt.of_newBlock h5)
    have a6 := a5.trans (SGrowsAt.of_newBlock h6)
    have a7 := a6.trans (SGrowsAt.of_sealCur h7)
    have hcase : s.fn.blocks.size ≤ caseId := by
      rw [SGrowsAt.newBlock_id h5]; exact a4.size
    have hnext : s.fn.blocks.size ≤ nextId := by
      rw [SGrowsAt.newBlock_id h6]; exact a5.size
    have a8 := a7.trans (SGrowsAt.of_moveTo (Or.inl hcase) h8)
    have a9 := a8.trans ((ihc s8 renv s9 h9).mono a8.size)
    refine a9.trans ?_
    cases renv with
    | none =>
      obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, hc2⟩ := M.bind_inv h
      refine (SGrowsAt.of_pure ha).trans
        ((SGrowsAt.of_moveTo (Or.inl hnext) hb2).trans ?_)
      exact ((ihr sv X joinId sb u s' hc2).mono
        (Nat.le_trans (Nat.le_trans a9.size (SGrowsAt.of_pure (N := 0) ha).size)
          (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) hb2).size))
    | some env' =>
      obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
      obtain ⟨uc, sc, hc2, hd2⟩ := M.bind_inv h
      refine (SGrowsAt.of_edgeArgs ha).trans
        ((SGrowsAt.of_sealCur hb2).trans
          ((SGrowsAt.of_moveTo (Or.inl hnext) hc2).trans ?_))
      exact ((ihr sv X joinId sc u s' hd2).mono
        (Nat.le_trans (Nat.le_trans (Nat.le_trans a9.size
          (SGrowsAt.of_edgeArgs (N := 0) ha).size)
            (SGrowsAt.of_sealCur (N := 0) hb2).size)
          (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) hc2).size))

omit model in
/-- Companion of `trStmt_grows` at `trCases.induct`: the same 29-case script against the same hypothesis list. The
five induct principles the `mutual` block generates share that list, so the
script instantiates verbatim; only the head and the conclusion change. -/
theorem trCases_grows : ∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (sv : ValId) (X : List Ident) (joinId : BlockId)
    (cs : List (Literal × List (Stmt Op))) (df : Option (List (Stmt Op))),
    CasesGrows fenv env lctx rets sv X joinId cs df := by
  refine trCases.induct FuncGrows ScopeGrows StmtsGrows StmtGrows CasesGrows
    ?trFunc ?trScope ?stmtsNil ?stmtsFunDef ?stmtsSkip ?stmtsCons
    ?block ?funDef ?letNoneBad ?letNone ?letSomeBad ?letSome ?assignBad ?assign
    ?cond ?switch ?forLoop ?exprBuiltin ?exprCall ?exprBad
    ?breakNone ?breakSome ?contNone ?contSome ?leaveNone ?leaveSome
    ?casesNilNone ?casesNilSome ?casesCons
  case trFunc =>
    intro fenv ps rs body ih s g s' h
    unfold trFunc at h
    obtain ⟨saved, s1, h1, h⟩ := M.bind_inv h
    have hsv : saved = s.fn := by
      rw [M.getFn_apply] at h1; exact (M.some_pair_inj h1).1.symm
    obtain ⟨u2, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨entry, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨pids, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨rids, s6, h6, h⟩ := M.bind_inv h
    have f1 : FGrows s s2 :=
      FGrows.trans (FGrows.of_getFn h1) (FGrows.of_setFn h2)
    have f2 : FGrows s s4 :=
      FGrows.trans f1 (FGrows.trans (FGrows.of_newBlock h3) (FGrows.of_moveTo h4))
    have f3 : FGrows s s6 :=
      FGrows.trans f2 (FGrows.trans
        (FGrows.of_grows (Grows.of_mapM_freshVal h5))
        (FGrows.of_grows (Grows.of_mapM_constZero h6)))
    -- the closing `getFn; setFn saved; pure` restores the caller's `fn`
    have hfin : ∀ (sk : BState), FGrows s sk →
        (getFn >>= fun done => setFn saved >>= fun _ =>
          (pure { params := pids, nrets := rs.length, entry := entry,
                  blocks := done.blocks } : M Func)) sk = some (g, s') →
        s'.fn = s.fn ∧ FGrows s s' := by
      intro sk hk hh
      obtain ⟨done, sa, ha, hh⟩ := M.bind_inv hh
      rw [M.getFn_apply] at ha
      obtain ⟨-, hd2⟩ := M.some_pair_inj ha
      obtain ⟨ub, sb, hb2, hc2⟩ := M.bind_inv hh
      rw [M.setFn_apply] at hb2
      obtain ⟨-, hb3⟩ := M.some_pair_inj hb2
      obtain ⟨-, hc3⟩ := M.pure_inv hc2
      refine ⟨?_, ?_⟩
      · rw [hc3, ← hb3, hsv]
      · rw [FGrows, hc3, ← hb3]
        exact hd2 ▸ hk
    by_cases hg : (!decide (ps ++ rs).Nodup) = true
    · rw [if_pos hg] at h
      obtain ⟨u7, s7, h7, -⟩ := M.bind_inv h
      exact absurd h7 (by simp [reject])
    · rw [if_neg hg] at h
      obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
      obtain ⟨renv, s8, h8, h⟩ := M.bind_inv h
      have f4 : FGrows s s8 :=
        FGrows.trans f3 (FGrows.trans (FGrows.of_pure h7)
          ((ih pids rids s7 renv s8 h8).funcsSize))
      cases renv with
      | none =>
        obtain ⟨ua, sa, ha, hh⟩ := M.bind_inv h
        exact hfin sa (FGrows.trans f4 (FGrows.of_pure ha)) hh
      | some envEnd =>
        obtain ⟨vals, sa, ha, hh⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb2, hh⟩ := M.bind_inv hh
        exact hfin sb (FGrows.trans f4 (FGrows.trans (FGrows.of_liftO ha)
          (FGrows.of_sealCur hb2))) hh
  case trScope =>
    intro fenv env lctx rets body ih s r s' h
    rw [trScope] at h
    obtain ⟨scope, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨renv, s₂, h2, h3⟩ := M.bind_inv h
    have g1 : SGrows s s₁ := allocScope_sgrows h1
    have g2 : SGrows s₁ s₂ := ih scope s₁ renv s₂ h2
    refine (g1.trans g2).trans ?_
    cases renv with
    | none => exact SGrowsAt.of_pure h3
    | some e => exact SGrowsAt.of_pure h3
    
  case stmtsNil =>
    intro fenv env lctx rets d s r s' h
    rw [trStmts] at h
    exact SGrowsAt.of_pure h
  case stmtsFunDef =>
    intro fenv env lctx rets d n ps rs fbody rest ihf ihr s r s' h
    rw [trStmts] at h
    obtain ⟨fid, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨g, s₂, h2, h⟩ := M.bind_inv h
    obtain ⟨u, s₃, h3, h4⟩ := M.bind_inv h
    obtain ⟨hfn, hfg⟩ := ihf s₁ g s₂ h2
    exact (((SGrows.trans (SGrowsAt.of_liftO h1)
      (SGrowsAt.of_funcsOnly hfn hfg)).trans
        (SGrowsAt.of_fillFunc h3)).trans (ihr s₃ r s' h4))
  case stmtsSkip =>
    intro fenv env lctx rets st rest hnf ih s r s' h
    rw [trStmts] at h
    · split at h
      · exact ih s r s' h
      · rename_i hc; exact absurd rfl hc
    · exact hnf
  case stmtsCons =>
    intro fenv env lctx rets d st rest hnf hd ih4 ih3n ih3t s r s' h
    rw [trStmts] at h
    · rw [if_neg hd] at h
      obtain ⟨renv, s₁, h1, h2⟩ := M.bind_inv h
      have g1 : SGrows s s₁ := ih4 s renv s₁ h1
      cases renv with
      | some env' => exact SGrows.trans g1 (ih3n env' s₁ r s' h2)
      | none => exact SGrows.trans g1 (ih3t s₁ r s' h2)
    · exact hnf
  case block =>
    intro fenv env lctx rets body ih s r s' h
    rw [trStmt] at h
    exact ih s r s' h
  case funDef =>
    intro fenv env lctx rets name ps rs body s r s' h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case letNoneBad =>
    intro fenv env lctx rets vars hgate s r s' h
    rw [trStmt] at h
    rw [if_pos hgate] at h
    obtain ⟨u, s₁, h1, -⟩ := M.bind_inv h
    exact absurd h1 (by simp [reject])
  case letNone =>
    intro fenv env lctx rets vars hgate s r s' h
    rw [trStmt] at h
    rw [if_neg hgate] at h
    obtain ⟨u, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_pure h1)
      (SGrows.trans (SGrows.of_grows (Grows.of_mapM_constZero h2))
        (SGrowsAt.of_pure h3))
  case letSomeBad =>
    intro fenv env lctx rets vars e hgate s r s' h
    rw [trStmt] at h
    rw [if_pos hgate] at h
    obtain ⟨u, s₁, h1, -⟩ := M.bind_inv h
    exact absurd h1 (by simp [reject])
  case letSome =>
    intro fenv env lctx rets vars e hgate s r s' h
    rw [trStmt] at h
    rw [if_neg hgate] at h
    obtain ⟨u, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_pure h1)
      (SGrows.trans (SGrows.of_grows (trExprN_grows h2)) (SGrowsAt.of_pure h3))
  case assignBad =>
    intro fenv env lctx rets vars e hgate s r s' h
    rw [trStmt] at h
    rw [if_pos hgate] at h
    obtain ⟨u, s₁, h1, -⟩ := M.bind_inv h
    exact absurd h1 (by simp [reject])
  case assign =>
    intro fenv env lctx rets vars e hgate s r s' h
    rw [trStmt] at h
    rw [if_neg hgate] at h
    obtain ⟨u, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_pure h1)
      (SGrows.trans (SGrows.of_grows (trExprN_grows h2)) (SGrowsAt.of_pure h3))
  case cond =>
    intro fenv env lctx rets c body ih s r s' h
    rw [trStmt] at h
    obtain ⟨cv, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨xvals, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨bodyId, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨joinParams, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨joinId, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨u6, s6, h6, h⟩ := M.bind_inv h
    obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
    obtain ⟨renv, s8, h8, h⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 :=
      SGrowsAt.of_grows (trExpr_grows c fenv env s s1 cv h1)
    have a2 := a1.trans (SGrowsAt.of_edgeArgs h2)
    have a3 := a2.trans (SGrowsAt.of_newBlock h3)
    have a4 := a3.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h4))
    have a5 := a4.trans (SGrowsAt.of_newBlock h5)
    have a6 := a5.trans (SGrowsAt.of_sealCur h6)
    have hbody : s.fn.blocks.size ≤ bodyId := by
      rw [SGrowsAt.newBlock_id h3]; exact a2.size
    have hjoin : s.fn.blocks.size ≤ joinId := by
      rw [SGrowsAt.newBlock_id h5]; exact a4.size
    have a7 := a6.trans (SGrowsAt.of_moveTo (Or.inl hbody) h7)
    have a8 := a7.trans ((ih s7 renv s8 h8).mono a7.size)
    refine a8.trans ?_
    cases renv with
    | none =>
      obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, hc2⟩ := M.bind_inv h
      exact (SGrowsAt.of_pure ha).trans
        ((SGrowsAt.of_moveTo (Or.inl hjoin) hb2).trans (SGrowsAt.of_pure hc2))
    | some env' =>
      obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
      obtain ⟨uc, sc, hc2, hd2⟩ := M.bind_inv h
      exact (SGrowsAt.of_edgeArgs ha).trans
        ((SGrowsAt.of_sealCur hb2).trans
          ((SGrowsAt.of_moveTo (Or.inl hjoin) hc2).trans (SGrowsAt.of_pure hd2)))
  case switch =>
    intro fenv env lctx rets c cases dflt ih s r s' h
    unfold trStmt at h
    obtain ⟨sv, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨joinParams, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨joinId, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨u5, s5, h5, h6⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 :=
      SGrowsAt.of_grows (trExpr_grows c fenv env s s1 sv h1)
    have a2 := a1.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h2))
    have a3 := a2.trans (SGrowsAt.of_newBlock h3)
    have hjoin : s.fn.blocks.size ≤ joinId := by
      rw [SGrowsAt.newBlock_id h3]; exact a2.size
    have a4 := a3.trans ((ih 0 0 _ _ _ s3 u4 s4 h4).mono a3.size)
    exact (a4.trans (SGrowsAt.of_moveTo (Or.inl hjoin) h5)).trans
      (SGrowsAt.of_pure h6)
  case forLoop =>
    intro fenv env lctx rets init c post body ihInit ihBody ihPost s r s' h
    unfold trStmt at h
    obtain ⟨scope, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨rinit, s2, h2, h⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 := allocScope_sgrows h1
    have a2 := a1.trans ((ihInit scope s1 rinit s2 h2).mono a1.size)
    cases rinit with
    | none => exact a2.trans (SGrowsAt.of_pure h)
    | some envI =>
      obtain ⟨xvals, s3, h3, h⟩ := M.bind_inv h
      obtain ⟨hParams, s4, h4, h⟩ := M.bind_inv h
      obtain ⟨hId, s5, h5, h⟩ := M.bind_inv h
      obtain ⟨exitParams, s6, h6, h⟩ := M.bind_inv h
      obtain ⟨exitId, s7, h7, h⟩ := M.bind_inv h
      obtain ⟨postParams, s8, h8, h⟩ := M.bind_inv h
      obtain ⟨postId, s9, h9, h⟩ := M.bind_inv h
      obtain ⟨u10, s10, h10, h⟩ := M.bind_inv h
      obtain ⟨u11, s11, h11, h⟩ := M.bind_inv h
      obtain ⟨cv, s12, h12, h⟩ := M.bind_inv h
      obtain ⟨bodyId, s13, h13, h⟩ := M.bind_inv h
      obtain ⟨hX, s14, h14, h⟩ := M.bind_inv h
      obtain ⟨u15, s15, h15, h⟩ := M.bind_inv h
      obtain ⟨u16, s16, h16, h⟩ := M.bind_inv h
      obtain ⟨renvB, s17, h17, h⟩ := M.bind_inv h
      have a3 := a2.trans (SGrowsAt.of_edgeArgs h3)
      have a4 := a3.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h4))
      have a5 := a4.trans (SGrowsAt.of_newBlock h5)
      have a6 := a5.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h6))
      have a7 := a6.trans (SGrowsAt.of_newBlock h7)
      have a8 := a7.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h8))
      have a9 := a8.trans (SGrowsAt.of_newBlock h9)
      have a10 := a9.trans (SGrowsAt.of_sealCur h10)
      have hhdr : s.fn.blocks.size ≤ hId := by
        rw [SGrowsAt.newBlock_id h5]; exact a4.size
      have hexit : s.fn.blocks.size ≤ exitId := by
        rw [SGrowsAt.newBlock_id h7]; exact a6.size
      have hpost : s.fn.blocks.size ≤ postId := by
        rw [SGrowsAt.newBlock_id h9]; exact a8.size
      have a11 := a10.trans (SGrowsAt.of_moveTo (Or.inl hhdr) h11)
      have a12 := a11.trans (SGrowsAt.of_grows
        (trExpr_grows c (scope :: fenv) _ s11 s12 cv h12))
      have a13 := a12.trans (SGrowsAt.of_newBlock h13)
      have a14 := a13.trans (SGrowsAt.of_edgeArgs h14)
      have a15 := a14.trans (SGrowsAt.of_sealCur h15)
      have hbody : s.fn.blocks.size ≤ bodyId := by
        rw [SGrowsAt.newBlock_id h13]; exact a12.size
      have a16 := a15.trans (SGrowsAt.of_moveTo (Or.inl hbody) h16)
      have a17 := a16.trans
        ((ihBody scope envI hParams exitId postId s16 renvB s17 h17).mono a16.size)
      -- the `post` scope and the loop exit, under both `if let` branches
      cases renvB with
      | none =>
        obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
        obtain ⟨renvP, sc, hc2, h⟩ := M.bind_inv h
        have b1 := a17.trans (SGrowsAt.of_pure ha)
        have b2 := b1.trans (SGrowsAt.of_moveTo (Or.inl hpost) hb2)
        have b3 := b2.trans
          ((ihPost scope envI postParams sb renvP sc hc2).mono b2.size)
        cases renvP with
        | none =>
          obtain ⟨ud, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, hf⟩ := M.bind_inv h
          exact ((b3.trans (SGrowsAt.of_pure hd)).trans
            (SGrowsAt.of_moveTo (Or.inl hexit) he)).trans (SGrowsAt.of_pure hf)
        | some envP' =>
          obtain ⟨xvP, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, h⟩ := M.bind_inv h
          obtain ⟨uf, sf, hf, hg2⟩ := M.bind_inv h
          exact (((b3.trans (SGrowsAt.of_edgeArgs hd)).trans
            (SGrowsAt.of_sealCur he)).trans
              (SGrowsAt.of_moveTo (Or.inl hexit) hf)).trans (SGrowsAt.of_pure hg2)
      | some envB =>
        obtain ⟨xvB, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ua', sa', ha', h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
        obtain ⟨renvP, sc, hc2, h⟩ := M.bind_inv h
        have b0 := a17.trans (SGrowsAt.of_edgeArgs ha)
        have b1 := b0.trans (SGrowsAt.of_sealCur ha')
        have b2 := b1.trans (SGrowsAt.of_moveTo (Or.inl hpost) hb2)
        have b3 := b2.trans
          ((ihPost scope envI postParams sb renvP sc hc2).mono b2.size)
        cases renvP with
        | none =>
          obtain ⟨ud, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, hf⟩ := M.bind_inv h
          exact ((b3.trans (SGrowsAt.of_pure hd)).trans
            (SGrowsAt.of_moveTo (Or.inl hexit) he)).trans (SGrowsAt.of_pure hf)
        | some envP' =>
          obtain ⟨xvP, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, h⟩ := M.bind_inv h
          obtain ⟨uf, sf, hf, hg2⟩ := M.bind_inv h
          exact (((b3.trans (SGrowsAt.of_edgeArgs hd)).trans
            (SGrowsAt.of_sealCur he)).trans
              (SGrowsAt.of_moveTo (Or.inl hexit) hf)).trans (SGrowsAt.of_pure hg2)
  case exprBuiltin =>
    intro fenv env lctx rets op args s r s' h
    rw [trStmt] at h
    obtain ⟨as, s₁, h1, h⟩ := M.bind_inv h
    refine SGrows.trans (SGrows.of_grows (trArgs_grows args fenv env s s₁ as h1)) ?_
    by_cases hop : isHaltingOp op = true
    · rw [if_pos hop] at h
      obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
      exact SGrows.trans (SGrowsAt.of_sealCur h2) (SGrowsAt.of_pure h3)
    · rw [if_neg hop] at h
      obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
      exact SGrows.trans (SGrows.of_grows (Grows.of_emit h2)) (SGrowsAt.of_pure h3)
  case exprCall =>
    intro fenv env lctx rets fn args s r s' h
    rw [trStmt] at h
    obtain ⟨as, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨fid, s₂, h2, h⟩ := M.bind_inv h
    obtain ⟨u, s₃, h3, h4⟩ := M.bind_inv h
    exact SGrows.trans (SGrows.of_grows (trArgs_grows args fenv env s s₁ as h1))
      (SGrows.trans (SGrowsAt.of_liftO h2)
        (SGrows.trans (SGrows.of_grows (Grows.of_emit h3)) (SGrowsAt.of_pure h4)))
  case exprBad =>
    intro fenv env lctx rets e hnb hnc s r s' h
    rw [trStmt] at h
    · exact absurd h (by simp [reject])
    · exact hnb
    · exact hnc
  case breakNone =>
    intro fenv env rets s r s' h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case breakSome =>
    intro fenv env rets l s r s' h
    rw [trStmt] at h
    obtain ⟨vals, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_edgeArgs h1)
      (SGrows.trans (SGrowsAt.of_sealCur h2) (SGrowsAt.of_pure h3))
  case contNone =>
    intro fenv env rets s r s' h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case contSome =>
    intro fenv env rets l s r s' h
    rw [trStmt] at h
    obtain ⟨vals, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_edgeArgs h1)
      (SGrows.trans (SGrowsAt.of_sealCur h2) (SGrowsAt.of_pure h3))
  case leaveNone =>
    intro fenv env lctx s r s' h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case leaveSome =>
    intro fenv env lctx rs s r s' h
    rw [trStmt] at h
    obtain ⟨vals, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_edgeArgs h1)
      (SGrows.trans (SGrowsAt.of_sealCur h2) (SGrowsAt.of_pure h3))
  case casesNilNone =>
    intro fenv env lctx rets _sv _X _joinId sv X joinId s u s' h
    rw [trCases] at h
    obtain ⟨xvals, s₁, h1, h2⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_edgeArgs h1) (SGrowsAt.of_sealCur h2)
  case casesNilSome =>
    intro fenv env lctx rets _sv _X _joinId dbody ih sv X joinId s u s' h
    rw [trCases] at h
    obtain ⟨renv, s₁, h1, h2⟩ := M.bind_inv h
    refine SGrows.trans (ih s renv s₁ h1) ?_
    cases renv with
    | none => exact SGrowsAt.of_pure h2
    | some env' =>
      obtain ⟨xv, s₂, h3, h4⟩ := M.bind_inv h2
      exact SGrows.trans (SGrowsAt.of_edgeArgs h3) (SGrowsAt.of_sealCur h4)
  case casesCons =>
    intro fenv env lctx rets _sv _X _joinId lit cbody restCases dflt ihc ihr
      sv X joinId s u s' h
    rw [trCases] at h
    obtain ⟨t, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨u2, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨e, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨caseId, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨nextId, s6, h6, h⟩ := M.bind_inv h
    obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
    obtain ⟨u8, s8, h8, h⟩ := M.bind_inv h
    obtain ⟨renv, s9, h9, h⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 :=
      SGrowsAt.of_grows (Grows.of_freshVal h1)
    have a2 := a1.trans (SGrowsAt.of_grows (Grows.of_emit h2))
    have a3 := a2.trans (SGrowsAt.of_grows (Grows.of_freshVal h3))
    have a4 := a3.trans (SGrowsAt.of_grows (Grows.of_emit h4))
    have a5 := a4.trans (SGrowsAt.of_newBlock h5)
    have a6 := a5.trans (SGrowsAt.of_newBlock h6)
    have a7 := a6.trans (SGrowsAt.of_sealCur h7)
    have hcase : s.fn.blocks.size ≤ caseId := by
      rw [SGrowsAt.newBlock_id h5]; exact a4.size
    have hnext : s.fn.blocks.size ≤ nextId := by
      rw [SGrowsAt.newBlock_id h6]; exact a5.size
    have a8 := a7.trans (SGrowsAt.of_moveTo (Or.inl hcase) h8)
    have a9 := a8.trans ((ihc s8 renv s9 h9).mono a8.size)
    refine a9.trans ?_
    cases renv with
    | none =>
      obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, hc2⟩ := M.bind_inv h
      refine (SGrowsAt.of_pure ha).trans
        ((SGrowsAt.of_moveTo (Or.inl hnext) hb2).trans ?_)
      exact ((ihr sv X joinId sb u s' hc2).mono
        (Nat.le_trans (Nat.le_trans a9.size (SGrowsAt.of_pure (N := 0) ha).size)
          (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) hb2).size))
    | some env' =>
      obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
      obtain ⟨uc, sc, hc2, hd2⟩ := M.bind_inv h
      refine (SGrowsAt.of_edgeArgs ha).trans
        ((SGrowsAt.of_sealCur hb2).trans
          ((SGrowsAt.of_moveTo (Or.inl hnext) hc2).trans ?_))
      exact ((ihr sv X joinId sc u s' hd2).mono
        (Nat.le_trans (Nat.le_trans (Nat.le_trans a9.size
          (SGrowsAt.of_edgeArgs (N := 0) ha).size)
            (SGrowsAt.of_sealCur (N := 0) hb2).size)
          (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) hc2).size))

omit model in
/-- Companion of `trStmt_grows` at `trFunc.induct`: the same 29-case script against the same hypothesis list. The
five induct principles the `mutual` block generates share that list, so the
script instantiates verbatim; only the head and the conclusion change. -/
theorem trFunc_grows : ∀ (fenv : FMap) (ps rs : List Ident) (body : List (Stmt Op)),
    FuncGrows fenv ps rs body := by
  refine trFunc.induct FuncGrows ScopeGrows StmtsGrows StmtGrows CasesGrows
    ?trFunc ?trScope ?stmtsNil ?stmtsFunDef ?stmtsSkip ?stmtsCons
    ?block ?funDef ?letNoneBad ?letNone ?letSomeBad ?letSome ?assignBad ?assign
    ?cond ?switch ?forLoop ?exprBuiltin ?exprCall ?exprBad
    ?breakNone ?breakSome ?contNone ?contSome ?leaveNone ?leaveSome
    ?casesNilNone ?casesNilSome ?casesCons
  case trFunc =>
    intro fenv ps rs body ih s g s' h
    unfold trFunc at h
    obtain ⟨saved, s1, h1, h⟩ := M.bind_inv h
    have hsv : saved = s.fn := by
      rw [M.getFn_apply] at h1; exact (M.some_pair_inj h1).1.symm
    obtain ⟨u2, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨entry, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨pids, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨rids, s6, h6, h⟩ := M.bind_inv h
    have f1 : FGrows s s2 :=
      FGrows.trans (FGrows.of_getFn h1) (FGrows.of_setFn h2)
    have f2 : FGrows s s4 :=
      FGrows.trans f1 (FGrows.trans (FGrows.of_newBlock h3) (FGrows.of_moveTo h4))
    have f3 : FGrows s s6 :=
      FGrows.trans f2 (FGrows.trans
        (FGrows.of_grows (Grows.of_mapM_freshVal h5))
        (FGrows.of_grows (Grows.of_mapM_constZero h6)))
    -- the closing `getFn; setFn saved; pure` restores the caller's `fn`
    have hfin : ∀ (sk : BState), FGrows s sk →
        (getFn >>= fun done => setFn saved >>= fun _ =>
          (pure { params := pids, nrets := rs.length, entry := entry,
                  blocks := done.blocks } : M Func)) sk = some (g, s') →
        s'.fn = s.fn ∧ FGrows s s' := by
      intro sk hk hh
      obtain ⟨done, sa, ha, hh⟩ := M.bind_inv hh
      rw [M.getFn_apply] at ha
      obtain ⟨-, hd2⟩ := M.some_pair_inj ha
      obtain ⟨ub, sb, hb2, hc2⟩ := M.bind_inv hh
      rw [M.setFn_apply] at hb2
      obtain ⟨-, hb3⟩ := M.some_pair_inj hb2
      obtain ⟨-, hc3⟩ := M.pure_inv hc2
      refine ⟨?_, ?_⟩
      · rw [hc3, ← hb3, hsv]
      · rw [FGrows, hc3, ← hb3]
        exact hd2 ▸ hk
    by_cases hg : (!decide (ps ++ rs).Nodup) = true
    · rw [if_pos hg] at h
      obtain ⟨u7, s7, h7, -⟩ := M.bind_inv h
      exact absurd h7 (by simp [reject])
    · rw [if_neg hg] at h
      obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
      obtain ⟨renv, s8, h8, h⟩ := M.bind_inv h
      have f4 : FGrows s s8 :=
        FGrows.trans f3 (FGrows.trans (FGrows.of_pure h7)
          ((ih pids rids s7 renv s8 h8).funcsSize))
      cases renv with
      | none =>
        obtain ⟨ua, sa, ha, hh⟩ := M.bind_inv h
        exact hfin sa (FGrows.trans f4 (FGrows.of_pure ha)) hh
      | some envEnd =>
        obtain ⟨vals, sa, ha, hh⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb2, hh⟩ := M.bind_inv hh
        exact hfin sb (FGrows.trans f4 (FGrows.trans (FGrows.of_liftO ha)
          (FGrows.of_sealCur hb2))) hh
  case trScope =>
    intro fenv env lctx rets body ih s r s' h
    rw [trScope] at h
    obtain ⟨scope, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨renv, s₂, h2, h3⟩ := M.bind_inv h
    have g1 : SGrows s s₁ := allocScope_sgrows h1
    have g2 : SGrows s₁ s₂ := ih scope s₁ renv s₂ h2
    refine (g1.trans g2).trans ?_
    cases renv with
    | none => exact SGrowsAt.of_pure h3
    | some e => exact SGrowsAt.of_pure h3
    
  case stmtsNil =>
    intro fenv env lctx rets d s r s' h
    rw [trStmts] at h
    exact SGrowsAt.of_pure h
  case stmtsFunDef =>
    intro fenv env lctx rets d n ps rs fbody rest ihf ihr s r s' h
    rw [trStmts] at h
    obtain ⟨fid, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨g, s₂, h2, h⟩ := M.bind_inv h
    obtain ⟨u, s₃, h3, h4⟩ := M.bind_inv h
    obtain ⟨hfn, hfg⟩ := ihf s₁ g s₂ h2
    exact (((SGrows.trans (SGrowsAt.of_liftO h1)
      (SGrowsAt.of_funcsOnly hfn hfg)).trans
        (SGrowsAt.of_fillFunc h3)).trans (ihr s₃ r s' h4))
  case stmtsSkip =>
    intro fenv env lctx rets st rest hnf ih s r s' h
    rw [trStmts] at h
    · split at h
      · exact ih s r s' h
      · rename_i hc; exact absurd rfl hc
    · exact hnf
  case stmtsCons =>
    intro fenv env lctx rets d st rest hnf hd ih4 ih3n ih3t s r s' h
    rw [trStmts] at h
    · rw [if_neg hd] at h
      obtain ⟨renv, s₁, h1, h2⟩ := M.bind_inv h
      have g1 : SGrows s s₁ := ih4 s renv s₁ h1
      cases renv with
      | some env' => exact SGrows.trans g1 (ih3n env' s₁ r s' h2)
      | none => exact SGrows.trans g1 (ih3t s₁ r s' h2)
    · exact hnf
  case block =>
    intro fenv env lctx rets body ih s r s' h
    rw [trStmt] at h
    exact ih s r s' h
  case funDef =>
    intro fenv env lctx rets name ps rs body s r s' h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case letNoneBad =>
    intro fenv env lctx rets vars hgate s r s' h
    rw [trStmt] at h
    rw [if_pos hgate] at h
    obtain ⟨u, s₁, h1, -⟩ := M.bind_inv h
    exact absurd h1 (by simp [reject])
  case letNone =>
    intro fenv env lctx rets vars hgate s r s' h
    rw [trStmt] at h
    rw [if_neg hgate] at h
    obtain ⟨u, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_pure h1)
      (SGrows.trans (SGrows.of_grows (Grows.of_mapM_constZero h2))
        (SGrowsAt.of_pure h3))
  case letSomeBad =>
    intro fenv env lctx rets vars e hgate s r s' h
    rw [trStmt] at h
    rw [if_pos hgate] at h
    obtain ⟨u, s₁, h1, -⟩ := M.bind_inv h
    exact absurd h1 (by simp [reject])
  case letSome =>
    intro fenv env lctx rets vars e hgate s r s' h
    rw [trStmt] at h
    rw [if_neg hgate] at h
    obtain ⟨u, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_pure h1)
      (SGrows.trans (SGrows.of_grows (trExprN_grows h2)) (SGrowsAt.of_pure h3))
  case assignBad =>
    intro fenv env lctx rets vars e hgate s r s' h
    rw [trStmt] at h
    rw [if_pos hgate] at h
    obtain ⟨u, s₁, h1, -⟩ := M.bind_inv h
    exact absurd h1 (by simp [reject])
  case assign =>
    intro fenv env lctx rets vars e hgate s r s' h
    rw [trStmt] at h
    rw [if_neg hgate] at h
    obtain ⟨u, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_pure h1)
      (SGrows.trans (SGrows.of_grows (trExprN_grows h2)) (SGrowsAt.of_pure h3))
  case cond =>
    intro fenv env lctx rets c body ih s r s' h
    rw [trStmt] at h
    obtain ⟨cv, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨xvals, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨bodyId, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨joinParams, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨joinId, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨u6, s6, h6, h⟩ := M.bind_inv h
    obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
    obtain ⟨renv, s8, h8, h⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 :=
      SGrowsAt.of_grows (trExpr_grows c fenv env s s1 cv h1)
    have a2 := a1.trans (SGrowsAt.of_edgeArgs h2)
    have a3 := a2.trans (SGrowsAt.of_newBlock h3)
    have a4 := a3.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h4))
    have a5 := a4.trans (SGrowsAt.of_newBlock h5)
    have a6 := a5.trans (SGrowsAt.of_sealCur h6)
    have hbody : s.fn.blocks.size ≤ bodyId := by
      rw [SGrowsAt.newBlock_id h3]; exact a2.size
    have hjoin : s.fn.blocks.size ≤ joinId := by
      rw [SGrowsAt.newBlock_id h5]; exact a4.size
    have a7 := a6.trans (SGrowsAt.of_moveTo (Or.inl hbody) h7)
    have a8 := a7.trans ((ih s7 renv s8 h8).mono a7.size)
    refine a8.trans ?_
    cases renv with
    | none =>
      obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, hc2⟩ := M.bind_inv h
      exact (SGrowsAt.of_pure ha).trans
        ((SGrowsAt.of_moveTo (Or.inl hjoin) hb2).trans (SGrowsAt.of_pure hc2))
    | some env' =>
      obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
      obtain ⟨uc, sc, hc2, hd2⟩ := M.bind_inv h
      exact (SGrowsAt.of_edgeArgs ha).trans
        ((SGrowsAt.of_sealCur hb2).trans
          ((SGrowsAt.of_moveTo (Or.inl hjoin) hc2).trans (SGrowsAt.of_pure hd2)))
  case switch =>
    intro fenv env lctx rets c cases dflt ih s r s' h
    unfold trStmt at h
    obtain ⟨sv, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨joinParams, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨joinId, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨u5, s5, h5, h6⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 :=
      SGrowsAt.of_grows (trExpr_grows c fenv env s s1 sv h1)
    have a2 := a1.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h2))
    have a3 := a2.trans (SGrowsAt.of_newBlock h3)
    have hjoin : s.fn.blocks.size ≤ joinId := by
      rw [SGrowsAt.newBlock_id h3]; exact a2.size
    have a4 := a3.trans ((ih 0 0 _ _ _ s3 u4 s4 h4).mono a3.size)
    exact (a4.trans (SGrowsAt.of_moveTo (Or.inl hjoin) h5)).trans
      (SGrowsAt.of_pure h6)
  case forLoop =>
    intro fenv env lctx rets init c post body ihInit ihBody ihPost s r s' h
    unfold trStmt at h
    obtain ⟨scope, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨rinit, s2, h2, h⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 := allocScope_sgrows h1
    have a2 := a1.trans ((ihInit scope s1 rinit s2 h2).mono a1.size)
    cases rinit with
    | none => exact a2.trans (SGrowsAt.of_pure h)
    | some envI =>
      obtain ⟨xvals, s3, h3, h⟩ := M.bind_inv h
      obtain ⟨hParams, s4, h4, h⟩ := M.bind_inv h
      obtain ⟨hId, s5, h5, h⟩ := M.bind_inv h
      obtain ⟨exitParams, s6, h6, h⟩ := M.bind_inv h
      obtain ⟨exitId, s7, h7, h⟩ := M.bind_inv h
      obtain ⟨postParams, s8, h8, h⟩ := M.bind_inv h
      obtain ⟨postId, s9, h9, h⟩ := M.bind_inv h
      obtain ⟨u10, s10, h10, h⟩ := M.bind_inv h
      obtain ⟨u11, s11, h11, h⟩ := M.bind_inv h
      obtain ⟨cv, s12, h12, h⟩ := M.bind_inv h
      obtain ⟨bodyId, s13, h13, h⟩ := M.bind_inv h
      obtain ⟨hX, s14, h14, h⟩ := M.bind_inv h
      obtain ⟨u15, s15, h15, h⟩ := M.bind_inv h
      obtain ⟨u16, s16, h16, h⟩ := M.bind_inv h
      obtain ⟨renvB, s17, h17, h⟩ := M.bind_inv h
      have a3 := a2.trans (SGrowsAt.of_edgeArgs h3)
      have a4 := a3.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h4))
      have a5 := a4.trans (SGrowsAt.of_newBlock h5)
      have a6 := a5.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h6))
      have a7 := a6.trans (SGrowsAt.of_newBlock h7)
      have a8 := a7.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h8))
      have a9 := a8.trans (SGrowsAt.of_newBlock h9)
      have a10 := a9.trans (SGrowsAt.of_sealCur h10)
      have hhdr : s.fn.blocks.size ≤ hId := by
        rw [SGrowsAt.newBlock_id h5]; exact a4.size
      have hexit : s.fn.blocks.size ≤ exitId := by
        rw [SGrowsAt.newBlock_id h7]; exact a6.size
      have hpost : s.fn.blocks.size ≤ postId := by
        rw [SGrowsAt.newBlock_id h9]; exact a8.size
      have a11 := a10.trans (SGrowsAt.of_moveTo (Or.inl hhdr) h11)
      have a12 := a11.trans (SGrowsAt.of_grows
        (trExpr_grows c (scope :: fenv) _ s11 s12 cv h12))
      have a13 := a12.trans (SGrowsAt.of_newBlock h13)
      have a14 := a13.trans (SGrowsAt.of_edgeArgs h14)
      have a15 := a14.trans (SGrowsAt.of_sealCur h15)
      have hbody : s.fn.blocks.size ≤ bodyId := by
        rw [SGrowsAt.newBlock_id h13]; exact a12.size
      have a16 := a15.trans (SGrowsAt.of_moveTo (Or.inl hbody) h16)
      have a17 := a16.trans
        ((ihBody scope envI hParams exitId postId s16 renvB s17 h17).mono a16.size)
      -- the `post` scope and the loop exit, under both `if let` branches
      cases renvB with
      | none =>
        obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
        obtain ⟨renvP, sc, hc2, h⟩ := M.bind_inv h
        have b1 := a17.trans (SGrowsAt.of_pure ha)
        have b2 := b1.trans (SGrowsAt.of_moveTo (Or.inl hpost) hb2)
        have b3 := b2.trans
          ((ihPost scope envI postParams sb renvP sc hc2).mono b2.size)
        cases renvP with
        | none =>
          obtain ⟨ud, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, hf⟩ := M.bind_inv h
          exact ((b3.trans (SGrowsAt.of_pure hd)).trans
            (SGrowsAt.of_moveTo (Or.inl hexit) he)).trans (SGrowsAt.of_pure hf)
        | some envP' =>
          obtain ⟨xvP, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, h⟩ := M.bind_inv h
          obtain ⟨uf, sf, hf, hg2⟩ := M.bind_inv h
          exact (((b3.trans (SGrowsAt.of_edgeArgs hd)).trans
            (SGrowsAt.of_sealCur he)).trans
              (SGrowsAt.of_moveTo (Or.inl hexit) hf)).trans (SGrowsAt.of_pure hg2)
      | some envB =>
        obtain ⟨xvB, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ua', sa', ha', h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
        obtain ⟨renvP, sc, hc2, h⟩ := M.bind_inv h
        have b0 := a17.trans (SGrowsAt.of_edgeArgs ha)
        have b1 := b0.trans (SGrowsAt.of_sealCur ha')
        have b2 := b1.trans (SGrowsAt.of_moveTo (Or.inl hpost) hb2)
        have b3 := b2.trans
          ((ihPost scope envI postParams sb renvP sc hc2).mono b2.size)
        cases renvP with
        | none =>
          obtain ⟨ud, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, hf⟩ := M.bind_inv h
          exact ((b3.trans (SGrowsAt.of_pure hd)).trans
            (SGrowsAt.of_moveTo (Or.inl hexit) he)).trans (SGrowsAt.of_pure hf)
        | some envP' =>
          obtain ⟨xvP, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, h⟩ := M.bind_inv h
          obtain ⟨uf, sf, hf, hg2⟩ := M.bind_inv h
          exact (((b3.trans (SGrowsAt.of_edgeArgs hd)).trans
            (SGrowsAt.of_sealCur he)).trans
              (SGrowsAt.of_moveTo (Or.inl hexit) hf)).trans (SGrowsAt.of_pure hg2)
  case exprBuiltin =>
    intro fenv env lctx rets op args s r s' h
    rw [trStmt] at h
    obtain ⟨as, s₁, h1, h⟩ := M.bind_inv h
    refine SGrows.trans (SGrows.of_grows (trArgs_grows args fenv env s s₁ as h1)) ?_
    by_cases hop : isHaltingOp op = true
    · rw [if_pos hop] at h
      obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
      exact SGrows.trans (SGrowsAt.of_sealCur h2) (SGrowsAt.of_pure h3)
    · rw [if_neg hop] at h
      obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
      exact SGrows.trans (SGrows.of_grows (Grows.of_emit h2)) (SGrowsAt.of_pure h3)
  case exprCall =>
    intro fenv env lctx rets fn args s r s' h
    rw [trStmt] at h
    obtain ⟨as, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨fid, s₂, h2, h⟩ := M.bind_inv h
    obtain ⟨u, s₃, h3, h4⟩ := M.bind_inv h
    exact SGrows.trans (SGrows.of_grows (trArgs_grows args fenv env s s₁ as h1))
      (SGrows.trans (SGrowsAt.of_liftO h2)
        (SGrows.trans (SGrows.of_grows (Grows.of_emit h3)) (SGrowsAt.of_pure h4)))
  case exprBad =>
    intro fenv env lctx rets e hnb hnc s r s' h
    rw [trStmt] at h
    · exact absurd h (by simp [reject])
    · exact hnb
    · exact hnc
  case breakNone =>
    intro fenv env rets s r s' h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case breakSome =>
    intro fenv env rets l s r s' h
    rw [trStmt] at h
    obtain ⟨vals, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_edgeArgs h1)
      (SGrows.trans (SGrowsAt.of_sealCur h2) (SGrowsAt.of_pure h3))
  case contNone =>
    intro fenv env rets s r s' h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case contSome =>
    intro fenv env rets l s r s' h
    rw [trStmt] at h
    obtain ⟨vals, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_edgeArgs h1)
      (SGrows.trans (SGrowsAt.of_sealCur h2) (SGrowsAt.of_pure h3))
  case leaveNone =>
    intro fenv env lctx s r s' h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case leaveSome =>
    intro fenv env lctx rs s r s' h
    rw [trStmt] at h
    obtain ⟨vals, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_edgeArgs h1)
      (SGrows.trans (SGrowsAt.of_sealCur h2) (SGrowsAt.of_pure h3))
  case casesNilNone =>
    intro fenv env lctx rets _sv _X _joinId sv X joinId s u s' h
    rw [trCases] at h
    obtain ⟨xvals, s₁, h1, h2⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_edgeArgs h1) (SGrowsAt.of_sealCur h2)
  case casesNilSome =>
    intro fenv env lctx rets _sv _X _joinId dbody ih sv X joinId s u s' h
    rw [trCases] at h
    obtain ⟨renv, s₁, h1, h2⟩ := M.bind_inv h
    refine SGrows.trans (ih s renv s₁ h1) ?_
    cases renv with
    | none => exact SGrowsAt.of_pure h2
    | some env' =>
      obtain ⟨xv, s₂, h3, h4⟩ := M.bind_inv h2
      exact SGrows.trans (SGrowsAt.of_edgeArgs h3) (SGrowsAt.of_sealCur h4)
  case casesCons =>
    intro fenv env lctx rets _sv _X _joinId lit cbody restCases dflt ihc ihr
      sv X joinId s u s' h
    rw [trCases] at h
    obtain ⟨t, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨u2, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨e, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨caseId, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨nextId, s6, h6, h⟩ := M.bind_inv h
    obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
    obtain ⟨u8, s8, h8, h⟩ := M.bind_inv h
    obtain ⟨renv, s9, h9, h⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 :=
      SGrowsAt.of_grows (Grows.of_freshVal h1)
    have a2 := a1.trans (SGrowsAt.of_grows (Grows.of_emit h2))
    have a3 := a2.trans (SGrowsAt.of_grows (Grows.of_freshVal h3))
    have a4 := a3.trans (SGrowsAt.of_grows (Grows.of_emit h4))
    have a5 := a4.trans (SGrowsAt.of_newBlock h5)
    have a6 := a5.trans (SGrowsAt.of_newBlock h6)
    have a7 := a6.trans (SGrowsAt.of_sealCur h7)
    have hcase : s.fn.blocks.size ≤ caseId := by
      rw [SGrowsAt.newBlock_id h5]; exact a4.size
    have hnext : s.fn.blocks.size ≤ nextId := by
      rw [SGrowsAt.newBlock_id h6]; exact a5.size
    have a8 := a7.trans (SGrowsAt.of_moveTo (Or.inl hcase) h8)
    have a9 := a8.trans ((ihc s8 renv s9 h9).mono a8.size)
    refine a9.trans ?_
    cases renv with
    | none =>
      obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, hc2⟩ := M.bind_inv h
      refine (SGrowsAt.of_pure ha).trans
        ((SGrowsAt.of_moveTo (Or.inl hnext) hb2).trans ?_)
      exact ((ihr sv X joinId sb u s' hc2).mono
        (Nat.le_trans (Nat.le_trans a9.size (SGrowsAt.of_pure (N := 0) ha).size)
          (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) hb2).size))
    | some env' =>
      obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
      obtain ⟨uc, sc, hc2, hd2⟩ := M.bind_inv h
      refine (SGrowsAt.of_edgeArgs ha).trans
        ((SGrowsAt.of_sealCur hb2).trans
          ((SGrowsAt.of_moveTo (Or.inl hnext) hc2).trans ?_))
      exact ((ihr sv X joinId sc u s' hd2).mono
        (Nat.le_trans (Nat.le_trans (Nat.le_trans a9.size
          (SGrowsAt.of_edgeArgs (N := 0) ha).size)
            (SGrowsAt.of_sealCur (N := 0) hb2).size)
          (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) hc2).size))

omit model in
/-- **Mutual function-table frame theorem.** Every translation preserves the
prefix below its entry allocation watermark.  The statement-list member has
the one necessary side condition: the slots it is entitled to fill lie at or
above that watermark.  `trScope` establishes the condition from its own
`allocScope`, so the four public translation members are unconditional. -/
theorem trFrames_fprefix :
    (∀ (fenv : FMap) (ps rs : List Ident)
      (body : List (Stmt Op)), FuncFrame fenv ps rs body) ∧
    (∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
      (rets : Option (List Ident)) (body : List (Stmt Op)),
        ScopeFrame fenv env lctx rets body) ∧
    (∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
      (rets : Option (List Ident)) (d : Bool) (ss : List (Stmt Op)),
        StmtsFrame fenv env lctx rets d ss) ∧
    (∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
      (rets : Option (List Ident)) (st : Stmt Op),
        StmtFrame fenv env lctx rets st) ∧
    (∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
      (rets : Option (List Ident)) (sv : ValId) (X : List Ident)
      (joinId : BlockId) (cases : List (Literal × List (Stmt Op)))
      (dflt : Option (List (Stmt Op))),
        CasesFrame fenv env lctx rets sv X joinId cases dflt) := by
  refine trFunc.mutual_induct FuncFrame ScopeFrame StmtsFrame StmtFrame CasesFrame
    ?trFunc ?trScope ?stmtsNil ?stmtsFunDef ?stmtsSkip ?stmtsCons
    ?block ?funDef ?letNoneBad ?letNone ?letSomeBad ?letSome ?assignBad ?assign
    ?cond ?switch ?forLoop ?exprBuiltin ?exprCall ?exprBad
    ?breakNone ?breakSome ?contNone ?contSome ?leaveNone ?leaveSome
    ?casesNilNone ?casesNilSome ?casesCons
  case trFunc =>
    intro fenv ps rs body ih N s g s' hN h
    unfold trFunc at h
    obtain ⟨saved, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨u2, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨entry, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨pids, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨rids, s6, h6, h⟩ := M.bind_inv h
    have p6 : FPrefix N s s6 :=
      (((((FPrefix.of_getFn h1).trans (FPrefix.of_setFn h2)).trans
        (FPrefix.of_newBlock h3)).trans (FPrefix.of_moveTo h4)).trans
        (FPrefix.of_grows (Grows.of_mapM_freshVal h5))).trans
        (FPrefix.of_grows (Grows.of_mapM_constZero h6))
    by_cases hg : (!decide (ps ++ rs).Nodup) = true
    · rw [if_pos hg] at h
      obtain ⟨u7, s7, h7, -⟩ := M.bind_inv h
      exact absurd h7 (by simp [reject])
    · rw [if_neg hg] at h
      obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
      obtain ⟨renv, s8, h8, h⟩ := M.bind_inv h
      have p7 := p6.trans (FPrefix.of_pure h7)
      have p8 : FPrefix N s s8 := p7.trans
        (ih pids rids N s7 renv s8 (p7.size hN) h8)
      have finish : ∀ (sk : BState), FPrefix N s sk →
          (getFn >>= fun done => setFn saved >>= fun _ =>
          (pure { params := pids, nrets := rs.length, entry := entry,
                  blocks := done.blocks } : M Func)) sk = some (g, s') →
          FPrefix N s s' := by
        intro sk pk hk
        obtain ⟨done, sa, ha, hk⟩ := M.bind_inv hk
        obtain ⟨ub, sb, hb, hc⟩ := M.bind_inv hk
        exact ((pk.trans (FPrefix.of_getFn ha)).trans
          (FPrefix.of_setFn hb)).trans (FPrefix.of_pure hc)
      cases renv with
      | none =>
          obtain ⟨ua, sa, ha, hh⟩ := M.bind_inv h
          exact finish sa (p8.trans (FPrefix.of_pure ha)) hh
      | some envEnd =>
          obtain ⟨vals, sa, ha, h⟩ := M.bind_inv h
          obtain ⟨ub, sb, hb, hh⟩ := M.bind_inv h
          exact finish sb ((p8.trans (FPrefix.of_liftO ha)).trans
            (FPrefix.of_sealCur hb)) hh
  case trScope =>
    intro fenv env lctx rets body ih N s r s' hN h
    rw [trScope] at h
    obtain ⟨scope, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨renv, s2, h2, h3⟩ := M.bind_inv h
    have pa : FPrefix N s s1 := (allocScope_fprefix h1).mono hN
    have habove : FillAbove N (scope :: fenv) body :=
      (allocScope_fillAbove h1 fenv).mono hN
    have pb := ih scope N s1 renv s2 (pa.size hN) habove h2
    cases renv <;> exact (pa.trans pb).trans (FPrefix.of_pure h3)
  case stmtsNil =>
    intro fenv env lctx rets d N s r s' hN ha h
    rw [trStmts] at h
    exact FPrefix.of_pure h
  case stmtsFunDef =>
    intro fenv env lctx rets d n ps rs body rest ihf ihr N s r s' hN ha h
    rw [trStmts] at h
    obtain ⟨fid, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨g, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨u, s3, h3, h4⟩ := M.bind_inv h
    have hfid : N ≤ fid := ha n ps rs body (by simp) fid
      (M.liftO_inv h1).1
    have p1 : FPrefix N s s1 := FPrefix.of_liftO h1
    have p2 := ihf N s1 g s2 (p1.size hN) h2
    have p3 := FPrefix.of_fillFunc hfid h3
    have p03 := (p1.trans p2).trans p3
    exact p03.trans (ihr N s3 r s' (p03.size hN) ha.tail h4)
  case stmtsSkip =>
    intro fenv env lctx rets st rest hnf ih N s r s' hN ha h
    rw [trStmts] at h
    · split at h
      · exact ih N s r s' hN ha.tail h
      · rename_i hc; exact absurd rfl hc
    · exact hnf
  case stmtsCons =>
    intro fenv env lctx rets d st rest hnf hd ihs ihN ihT N s r s' hN ha h
    rw [trStmts] at h
    · rw [if_neg hd] at h
      obtain ⟨renv, s1, h1, h2⟩ := M.bind_inv h
      have p1 := ihs N s renv s1 hN h1
      have hN1 := Nat.le_trans hN
        (trStmt_grows fenv env lctx rets st s renv s1 h1).funcsSize
      cases renv with
      | some env' => exact p1.trans (ihN env' N s1 r s' hN1 ha.tail h2)
      | none => exact p1.trans (ihT N s1 r s' hN1 ha.tail h2)
    · exact hnf
  case block =>
    intro fenv env lctx rets body ih N s r s' hN h
    rw [trStmt] at h
    exact ih N s r s' hN h
  case funDef =>
    intro fenv env lctx rets n ps rs body N s r s' hN h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case letNoneBad =>
    intro fenv env lctx rets vars hg N s r s' hN h
    rw [trStmt, if_pos hg] at h
    obtain ⟨u, t, hb, -⟩ := M.bind_inv h
    exact absurd hb (by simp [reject])
  case letNone =>
    intro fenv env lctx rets vars hg N s r s' hN h
    rw [trStmt, if_neg hg] at h
    obtain ⟨u, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s2, h2, h3⟩ := M.bind_inv h
    exact ((FPrefix.of_pure h1).trans
      (FPrefix.of_grows (Grows.of_mapM_constZero h2))).trans
      (FPrefix.of_pure h3)
  case letSomeBad =>
    intro fenv env lctx rets vars e hg N s r s' hN h
    rw [trStmt, if_pos hg] at h
    obtain ⟨u, t, hb, -⟩ := M.bind_inv h
    exact absurd hb (by simp [reject])
  case letSome =>
    intro fenv env lctx rets vars e hg N s r s' hN h
    rw [trStmt, if_neg hg] at h
    obtain ⟨u, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s2, h2, h3⟩ := M.bind_inv h
    exact ((FPrefix.of_pure h1).trans
      (FPrefix.of_grows (trExprN_grows h2))).trans (FPrefix.of_pure h3)
  case assignBad =>
    intro fenv env lctx rets vars e hg N s r s' hN h
    rw [trStmt, if_pos hg] at h
    obtain ⟨u, t, hb, -⟩ := M.bind_inv h
    exact absurd hb (by simp [reject])
  case assign =>
    intro fenv env lctx rets vars e hg N s r s' hN h
    rw [trStmt, if_neg hg] at h
    obtain ⟨u, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s2, h2, h3⟩ := M.bind_inv h
    exact ((FPrefix.of_pure h1).trans
      (FPrefix.of_grows (trExprN_grows h2))).trans (FPrefix.of_pure h3)
  case cond =>
    intro fenv env lctx rets c body ih N s r s' hN h
    rw [trStmt] at h
    obtain ⟨cv, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨xv, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨bodyId, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨jps, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨joinId, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨u6, s6, h6, h⟩ := M.bind_inv h
    obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
    obtain ⟨renv, s8, h8, h⟩ := M.bind_inv h
    have p7 : FPrefix N s s7 :=
      ((((((FPrefix.of_grows (trExpr_grows c fenv env s s1 cv h1)).trans
        (FPrefix.of_edgeArgs h2)).trans (FPrefix.of_newBlock h3)).trans
        (FPrefix.of_grows (Grows.of_mapM_freshVal h4))).trans
        (FPrefix.of_newBlock h5)).trans (FPrefix.of_sealCur h6)).trans
        (FPrefix.of_moveTo h7)
    have p8 : FPrefix N s s8 := p7.trans
      (ih N s7 renv s8 (p7.size hN) h8)
    cases renv with
    | none =>
        obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb, hc⟩ := M.bind_inv h
        exact ((p8.trans (FPrefix.of_pure ha)).trans
          (FPrefix.of_moveTo hb)).trans (FPrefix.of_pure hc)
    | some env' =>
        obtain ⟨xa, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb, h⟩ := M.bind_inv h
        obtain ⟨uc, sc, hc, hd⟩ := M.bind_inv h
        exact (((p8.trans (FPrefix.of_edgeArgs ha)).trans
          (FPrefix.of_sealCur hb)).trans (FPrefix.of_moveTo hc)).trans
          (FPrefix.of_pure hd)
  case switch =>
    intro fenv env lctx rets c cases dflt ih N s r s' hN h
    unfold trStmt at h
    obtain ⟨sv, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨jps, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨jid, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨u5, s5, h5, h6⟩ := M.bind_inv h
    have p3 : FPrefix N s s3 := ((FPrefix.of_grows
      (trExpr_grows c fenv env s s1 sv h1)).trans
      (FPrefix.of_grows (Grows.of_mapM_freshVal h2))).trans
      (FPrefix.of_newBlock h3)
    exact ((p3.trans
      (ih sv jid sv _ jid N s3 u4 s4 (p3.size hN) h4)).trans
      (FPrefix.of_moveTo h5)).trans (FPrefix.of_pure h6)
  case forLoop =>
    intro fenv env lctx rets init c post body ihI ihB ihP N s r s' hN h
    unfold trStmt at h
    obtain ⟨scope, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨rinit, s2, h2, h⟩ := M.bind_inv h
    have p1 : FPrefix N s s1 := (allocScope_fprefix h1).mono hN
    have habove : FillAbove N (scope :: fenv) init :=
      (allocScope_fillAbove h1 fenv).mono hN
    have p2 := ihI scope N s1 rinit s2 (p1.size hN) habove h2
    have pinit := p1.trans p2
    cases rinit with
    | none => exact pinit.trans (FPrefix.of_pure h)
    | some envI =>
      obtain ⟨xv, s3, h3, h⟩ := M.bind_inv h
      obtain ⟨hps, s4, h4, h⟩ := M.bind_inv h
      obtain ⟨hid, s5, h5, h⟩ := M.bind_inv h
      obtain ⟨eps, s6, h6, h⟩ := M.bind_inv h
      obtain ⟨eid, s7, h7, h⟩ := M.bind_inv h
      obtain ⟨pps, s8, h8, h⟩ := M.bind_inv h
      obtain ⟨pid, s9, h9, h⟩ := M.bind_inv h
      obtain ⟨u10, s10, h10, h⟩ := M.bind_inv h
      obtain ⟨u11, s11, h11, h⟩ := M.bind_inv h
      obtain ⟨cv, s12, h12, h⟩ := M.bind_inv h
      obtain ⟨bid, s13, h13, h⟩ := M.bind_inv h
      obtain ⟨hx, s14, h14, h⟩ := M.bind_inv h
      obtain ⟨u15, s15, h15, h⟩ := M.bind_inv h
      obtain ⟨u16, s16, h16, h⟩ := M.bind_inv h
      obtain ⟨rb, s17, h17, h⟩ := M.bind_inv h
      have p3 := pinit.trans (FPrefix.of_edgeArgs h3)
      have p4 := p3.trans (FPrefix.of_grows (Grows.of_mapM_freshVal h4))
      have p5 := p4.trans (FPrefix.of_newBlock h5)
      have p6 := p5.trans (FPrefix.of_grows (Grows.of_mapM_freshVal h6))
      have p7 := p6.trans (FPrefix.of_newBlock h7)
      have p8 := p7.trans (FPrefix.of_grows (Grows.of_mapM_freshVal h8))
      have p9 := p8.trans (FPrefix.of_newBlock h9)
      have p10 := p9.trans (FPrefix.of_sealCur h10)
      have p11 := p10.trans (FPrefix.of_moveTo h11)
      have p12 := p11.trans (FPrefix.of_grows
        (trExpr_grows c (scope :: fenv) _ s11 s12 cv h12))
      have p13 := p12.trans (FPrefix.of_newBlock h13)
      have p14 := p13.trans (FPrefix.of_edgeArgs h14)
      have p15 := p14.trans (FPrefix.of_sealCur h15)
      have p16 := p15.trans (FPrefix.of_moveTo h16)
      have p17 : FPrefix N s s17 := p16.trans
        (ihB scope envI hps eid pid N s16 rb s17 (p16.size hN) h17)
      cases rb with
      | none =>
        obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb, h⟩ := M.bind_inv h
        obtain ⟨rp, sc, hc, h⟩ := M.bind_inv h
        have pp := (p17.trans (FPrefix.of_pure ha)).trans
          (FPrefix.of_moveTo hb)
        have pc := pp.trans
          (ihP scope envI pps N sb rp sc (pp.size hN) hc)
        cases rp with
        | none =>
          obtain ⟨ud, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, hf⟩ := M.bind_inv h
          exact ((pc.trans (FPrefix.of_pure hd)).trans
            (FPrefix.of_moveTo he)).trans (FPrefix.of_pure hf)
        | some ep =>
          obtain ⟨xd, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, h⟩ := M.bind_inv h
          obtain ⟨uf, sf, hf, h⟩ := M.bind_inv h
          exact (((pc.trans (FPrefix.of_edgeArgs hd)).trans
            (FPrefix.of_sealCur he)).trans (FPrefix.of_moveTo hf)).trans
            (FPrefix.of_pure h)
      | some eb =>
        obtain ⟨xa, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb, h⟩ := M.bind_inv h
        obtain ⟨uc, sc, hc, h⟩ := M.bind_inv h
        obtain ⟨rp, sd, hd, h⟩ := M.bind_inv h
        have pp := ((p17.trans (FPrefix.of_edgeArgs ha)).trans
          (FPrefix.of_sealCur hb)).trans (FPrefix.of_moveTo hc)
        have pd := pp.trans
          (ihP scope envI pps N sc rp sd (pp.size hN) hd)
        cases rp with
        | none =>
          obtain ⟨ue, se, he, h⟩ := M.bind_inv h
          obtain ⟨uf, sf, hf, hg⟩ := M.bind_inv h
          exact ((pd.trans (FPrefix.of_pure he)).trans
            (FPrefix.of_moveTo hf)).trans (FPrefix.of_pure hg)
        | some ep =>
          obtain ⟨xe, se, he, h⟩ := M.bind_inv h
          obtain ⟨uf, sf, hf, h⟩ := M.bind_inv h
          obtain ⟨ug, sg, hg, h⟩ := M.bind_inv h
          exact (((pd.trans (FPrefix.of_edgeArgs he)).trans
            (FPrefix.of_sealCur hf)).trans (FPrefix.of_moveTo hg)).trans
            (FPrefix.of_pure h)
  case exprBuiltin =>
    intro fenv env lctx rets op args N s r s' hN h
    rw [trStmt] at h
    obtain ⟨as, s1, h1, h⟩ := M.bind_inv h
    have p1 : FPrefix N s s1 :=
      FPrefix.of_grows (trArgs_grows args fenv env s s1 as h1)
    by_cases hop : isHaltingOp op = true
    · rw [if_pos hop] at h
      obtain ⟨u, s2, h2, h3⟩ := M.bind_inv h
      exact (p1.trans (FPrefix.of_sealCur h2)).trans (FPrefix.of_pure h3)
    · rw [if_neg hop] at h
      obtain ⟨u, s2, h2, h3⟩ := M.bind_inv h
      exact (p1.trans (FPrefix.of_grows (Grows.of_emit h2))).trans
        (FPrefix.of_pure h3)
  case exprCall =>
    intro fenv env lctx rets fn args N s r s' hN h
    rw [trStmt] at h
    obtain ⟨as, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨fid, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨u, s3, h3, h4⟩ := M.bind_inv h
    exact ((FPrefix.of_grows (trArgs_grows args fenv env s s1 as h1)).trans
      (FPrefix.of_liftO h2)).trans
      ((FPrefix.of_grows (Grows.of_emit h3)).trans (FPrefix.of_pure h4))
  case exprBad =>
    intro fenv env lctx rets e hnb hnc N s r s' hN h
    rw [trStmt] at h
    · exact absurd h (by simp [reject])
    · exact hnb
    · exact hnc
  case breakNone =>
    intro fenv env rets N s r s' hN h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case breakSome =>
    intro fenv env rets l N s r s' hN h
    rw [trStmt] at h
    obtain ⟨vals, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s2, h2, h3⟩ := M.bind_inv h
    exact ((FPrefix.of_edgeArgs h1).trans (FPrefix.of_sealCur h2)).trans
      (FPrefix.of_pure h3)
  case contNone =>
    intro fenv env rets N s r s' hN h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case contSome =>
    intro fenv env rets l N s r s' hN h
    rw [trStmt] at h
    obtain ⟨vals, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s2, h2, h3⟩ := M.bind_inv h
    exact ((FPrefix.of_edgeArgs h1).trans (FPrefix.of_sealCur h2)).trans
      (FPrefix.of_pure h3)
  case leaveNone =>
    intro fenv env lctx N s r s' hN h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case leaveSome =>
    intro fenv env lctx rs N s r s' hN h
    rw [trStmt] at h
    obtain ⟨vals, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s2, h2, h3⟩ := M.bind_inv h
    exact ((FPrefix.of_edgeArgs h1).trans (FPrefix.of_sealCur h2)).trans
      (FPrefix.of_pure h3)
  case casesNilNone =>
    intro fenv env lctx rets _sv _X _jid sv X jid N s u s' hN h
    rw [trCases] at h
    obtain ⟨xv, s1, h1, h2⟩ := M.bind_inv h
    exact (FPrefix.of_edgeArgs h1).trans (FPrefix.of_sealCur h2)
  case casesNilSome =>
    intro fenv env lctx rets _sv _X _jid body ih sv X jid N s u s' hN h
    rw [trCases] at h
    obtain ⟨renv, s1, h1, h2⟩ := M.bind_inv h
    have p1 := ih N s renv s1 hN h1
    cases renv with
    | none => exact p1.trans (FPrefix.of_pure h2)
    | some env' =>
      obtain ⟨xv, s2, h3, h4⟩ := M.bind_inv h2
      exact (p1.trans (FPrefix.of_edgeArgs h3)).trans
        (FPrefix.of_sealCur h4)
  case casesCons =>
    intro fenv env lctx rets _sv _X _jid lit body rest dflt ihB ihR
      sv X jid N s u s' hN h
    rw [trCases] at h
    obtain ⟨t, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨u2, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨e, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨cid, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨nid, s6, h6, h⟩ := M.bind_inv h
    obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
    obtain ⟨u8, s8, h8, h⟩ := M.bind_inv h
    obtain ⟨renv, s9, h9, h⟩ := M.bind_inv h
    have p8 : FPrefix N s s8 :=
      (((((((FPrefix.of_grows (Grows.of_freshVal h1)).trans
        (FPrefix.of_grows (Grows.of_emit h2))).trans
        (FPrefix.of_grows (Grows.of_freshVal h3))).trans
        (FPrefix.of_grows (Grows.of_emit h4))).trans
        (FPrefix.of_newBlock h5)).trans (FPrefix.of_newBlock h6)).trans
        (FPrefix.of_sealCur h7)).trans (FPrefix.of_moveTo h8)
    have p9 : FPrefix N s s9 := p8.trans
      (ihB N s8 renv s9 (p8.size hN) h9)
    cases renv with
    | none =>
      obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb, hc⟩ := M.bind_inv h
      have pp := (p9.trans (FPrefix.of_pure ha)).trans
        (FPrefix.of_moveTo hb)
      exact pp.trans (ihR sv X jid N sb u s' (pp.size hN) hc)
    | some env' =>
      obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb, h⟩ := M.bind_inv h
      obtain ⟨uc, sc, hc, hd⟩ := M.bind_inv h
      have pp := ((p9.trans (FPrefix.of_edgeArgs ha)).trans
        (FPrefix.of_sealCur hb)).trans (FPrefix.of_moveTo hc)
      exact pp.trans (ihR sv X jid N sc u s' (pp.size hN) hd)

omit model in
theorem trFunc_fprefix : ∀ (fenv : FMap) (ps rs : List Ident)
    (body : List (Stmt Op)), FuncFrame fenv ps rs body :=
  trFrames_fprefix.1

omit model in
theorem trScope_fprefix : ∀ (fenv : FMap) (env : VMap)
    (lctx : Option LoopCtx) (rets : Option (List Ident))
    (body : List (Stmt Op)), ScopeFrame fenv env lctx rets body :=
  trFrames_fprefix.2.1

omit model in
theorem trStmts_fprefix : ∀ (fenv : FMap) (env : VMap)
    (lctx : Option LoopCtx) (rets : Option (List Ident)) (d : Bool)
    (ss : List (Stmt Op)), StmtsFrame fenv env lctx rets d ss :=
  trFrames_fprefix.2.2.1

omit model in
theorem trStmt_fprefix : ∀ (fenv : FMap) (env : VMap)
    (lctx : Option LoopCtx) (rets : Option (List Ident)) (st : Stmt Op),
    StmtFrame fenv env lctx rets st :=
  trFrames_fprefix.2.2.2.1

omit model in
theorem trCases_fprefix : ∀ (fenv : FMap) (env : VMap)
    (lctx : Option LoopCtx) (rets : Option (List Ident)) (sv : ValId)
    (X : List Ident) (joinId : BlockId)
    (cases : List (Literal × List (Stmt Op)))
    (dflt : Option (List (Stmt Op))),
    CasesFrame fenv env lctx rets sv X joinId cases dflt :=
  trFrames_fprefix.2.2.2.2

omit model in
/-- Natural-watermark specialization used by callers protecting all slots
that existed before a nested closed translation. -/
theorem trFunc_prefix (fenv : FMap) (ps rs : List Ident)
    (body : List (Stmt Op)) {s s' : BState} {g : Func}
    (h : trFunc fenv ps rs body s = some (g, s')) :
    FPrefix s.funcs.size s s' :=
  trFunc_fprefix fenv ps rs body s.funcs.size s g s' (Nat.le_refl _) h

/-- The ordered function-slot budget consumed by a statement walk.  Function
definitions are the only statements which consume a reservation; all other
statements are closed translations and therefore preserve the caller's
budget.  Successful `trStmts` runs ensure every `filterMap` entry is present. -/
def stmtFuncIds (fenv : FMap) : List (Stmt Op) → List FuncId
  | [] => []
  | .funDef n _ _ _ :: rest => (fenv.get n).toList ++ stmtFuncIds fenv rest
  | _ :: rest => stmtFuncIds fenv rest

omit model in
/-- Pull a completed output ownership budget backward through a statement
walk.  The input additionally owns exactly the slots selected by its direct
`funDef`s.  `hslots` is supplied by the enclosing `allocScope`; its `Nodup`
clause rules out duplicate selection, which is precisely what permits each
`fillFunc` to consume one distinct reservation.

This is the input/output ownership transition used by the simulation motive.
Nested statements and functions frame every input slot by `FPrefix`; the sole
consuming step is discharged by `FOwned.back_fillFunc`. -/
theorem trStmts_owned_back (fenv : FMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) :
    ∀ (ss : List (Stmt Op)) (env : VMap) (d : Bool)
      (s s' done : BState) (r : Option VMap) (owned : List FuncId),
      (∀ i : FuncId, i ∈ stmtFuncIds fenv ss ++ owned → i < s.funcs.size) →
      (∀ i : FuncId, i ∈ stmtFuncIds fenv ss →
        s.funcs[i]? = some none) →
      (stmtFuncIds fenv ss ++ owned).Nodup →
      FOwned owned s' done →
      trStmts fenv env lctx rets d ss s = some (r, s') →
      FOwned (stmtFuncIds fenv ss ++ owned) s done := by
  intro ss
  induction ss with
  | nil =>
      intro env d s s' done r owned _ _ _ ho htr
      rw [trStmts] at htr
      obtain ⟨-, rfl⟩ := M.pure_inv htr
      simpa [stmtFuncIds] using ho
  | cons st rest ih =>
      intro env d s s' done r owned hbound hslots hnd ho htr
      let st0 := st
      cases st with
      | funDef n ps rs body =>
          rw [trStmts] at htr
          obtain ⟨fid, s1, hget, htr⟩ := M.bind_inv htr
          obtain ⟨g, s2, hfunc, htr⟩ := M.bind_inv htr
          obtain ⟨u, s3, hfill, htail⟩ := M.bind_inv htr
          obtain ⟨hfid, hs1⟩ := M.liftO_inv hget
          subst s1
          simp only [stmtFuncIds, hfid, Option.toList_some,
            List.singleton_append] at hbound hslots hnd ⊢
          have hfid0 : s.funcs[fid]? = some none :=
            hslots fid (by simp)
          have hp := trFunc_prefix fenv ps rs body hfunc
          have hfid2 : s2.funcs[fid]? = some none := by
            rw [hp fid (lt_size_of_getElem? hfid0)]
            exact hfid0
          have hndTail : (stmtFuncIds fenv rest ++ owned).Nodup :=
            (List.nodup_cons.mp hnd).2
          have hfidNot : fid ∉ stmtFuncIds fenv rest ++ owned :=
            (List.nodup_cons.mp hnd).1
          have hs3 := (M.fillFunc_inv hfill).choose_spec
          have hboundTail : ∀ i : FuncId,
              i ∈ stmtFuncIds fenv rest ++ owned → i < s3.funcs.size := by
            intro i hi
            have hi0 := hbound i (by simp [hi])
            have hsize : s.funcs.size ≤ s2.funcs.size :=
              (trFunc_fprefix fenv ps rs body s.funcs.size s g s2
                (Nat.le_refl _) hfunc).size (Nat.le_refl _)
            rw [hs3]
            simpa using Nat.lt_of_lt_of_le hi0 hsize
          have hslotsTail : ∀ i : FuncId, i ∈ stmtFuncIds fenv rest →
              s3.funcs[i]? = some none := by
            intro i hi
            have hiAll : i ∈ stmtFuncIds fenv rest ++ owned :=
              List.mem_append_left _ hi
            have hi0 : s.funcs[i]? = some none :=
              hslots i (by simp [hi])
            have hi2 : s2.funcs[i]? = some none := by
              rw [hp i (lt_size_of_getElem? hi0)]
              exact hi0
            have hine : i ≠ fid := by
              intro heq
              subst i
              exact hfidNot hiAll
            rw [hs3, Array.getElem?_set, if_neg (Ne.symm hine)]
            exact hi2
          have ho3 := ih env d s3 s' done r owned hboundTail hslotsTail
            hndTail ho htail
          have ho2 : FOwned (fid :: (stmtFuncIds fenv rest ++ owned)) s2 done :=
            FOwned.back_fillFunc hfid2 hfill ho3
          have hbound2 : ∀ i : FuncId,
              i ∈ fid :: (stmtFuncIds fenv rest ++ owned) →
                i < s.funcs.size := by
            intro i hi
            exact hbound i (by simpa using hi)
          exact FOwned.back_fprefix hp hbound2 ho2
      | block body | letDecl vars val | assign vars e | cond e body
      | forLoop init e post body | «break» | «continue» | leave
      | switch e cases dflt | exprStmt e =>
          simp only [stmtFuncIds] at hbound hslots hnd ⊢
          have runTail (env' : VMap) (d' : Bool) (s1 : BState)
              (hhead : trStmt fenv env lctx rets st0 s = some (some env', s1) ∨
                trStmt fenv env lctx rets st0 s = some (none, s1))
              (htail : trStmts fenv env' lctx rets d' rest s1 = some (r, s')) :
              FOwned (stmtFuncIds fenv rest ++ owned) s done := by
            have htrHead : ∃ ro, trStmt fenv env lctx rets st0 s = some (ro, s1) :=
              hhead.elim (fun h => ⟨some env', h⟩) (fun h => ⟨none, h⟩)
            obtain ⟨ro, hro⟩ := htrHead
            have hp := trStmt_fprefix fenv env lctx rets st0 s.funcs.size
              s ro s1 (Nat.le_refl _) hro
            have hbound1 : ∀ i : FuncId,
                i ∈ stmtFuncIds fenv rest ++ owned → i < s1.funcs.size := by
              intro i hi
              exact hp.size (Nat.le_refl _) |>
                Nat.lt_of_lt_of_le (hbound i hi)
            have hslots1 : ∀ i : FuncId, i ∈ stmtFuncIds fenv rest →
                s1.funcs[i]? = some none := by
              intro i hi
              rw [hp i (hbound i (List.mem_append_left _ hi))]
              exact hslots i hi
            have ho1 := ih env' d' s1 s' done r owned hbound1 hslots1
              hnd ho htail
            exact FOwned.back_fprefix hp hbound ho1
          rw [trStmts] at htr
          · split at htr
            · exact ih env true s s' done r owned hbound hslots hnd ho htr
            · obtain ⟨renv, s1, hhead, htail⟩ := M.bind_inv htr
              cases renv with
              | none =>
                  exact runTail env true s1 (Or.inr hhead) htail
              | some env' =>
                  exact runTail env' false s1 (Or.inl hhead) htail
          · intro n ps rs fbody heq
            cases heq

omit model in
/-- A single statement is a closed translation with respect to every pending
slot which existed at entry.  Unlike `trStmts`, it cannot consume a direct
function reservation (`funDef` is rejected by `trStmt`). -/
theorem trStmt_owned_back (fenv : FMap) (env : VMap)
    (lctx : Option LoopCtx) (rets : Option (List Ident)) (st : Stmt Op)
    {s s' done : BState} {r : Option VMap} {owned : List FuncId}
    (hbound : ∀ i : FuncId, i ∈ owned → i < s.funcs.size)
    (ho : FOwned owned s' done)
    (htr : trStmt fenv env lctx rets st s = some (r, s')) :
    FOwned owned s done :=
  FOwned.back_fprefix
    (trStmt_fprefix fenv env lctx rets st s.funcs.size s r s'
      (Nat.le_refl _) htr) hbound ho

omit model in
/-- The scope wrapper allocates and discharges only its own reservations, so
it preserves every caller-owned entry slot. -/
theorem trScope_owned_back (fenv : FMap) (env : VMap)
    (lctx : Option LoopCtx) (rets : Option (List Ident))
    (body : List (Stmt Op)) {s s' done : BState} {r : Option VMap}
    {owned : List FuncId}
    (hbound : ∀ i : FuncId, i ∈ owned → i < s.funcs.size)
    (ho : FOwned owned s' done)
    (htr : trScope fenv env lctx rets body s = some (r, s')) :
    FOwned owned s done :=
  FOwned.back_fprefix
    (trScope_fprefix fenv env lctx rets body s.funcs.size s r s'
      (Nat.le_refl _) htr) hbound ho

omit model in
/-- Translating a nested function saves and restores the caller function and
frames its entire function table prefix. -/
theorem trFunc_owned_back (fenv : FMap) (ps rs : List Ident)
    (body : List (Stmt Op)) {s s' done : BState} {g : Func}
    {owned : List FuncId}
    (hbound : ∀ i : FuncId, i ∈ owned → i < s.funcs.size)
    (ho : FOwned owned s' done)
    (htr : trFunc fenv ps rs body s = some (g, s')) :
    FOwned owned s done :=
  FOwned.back_fprefix (trFunc_prefix fenv ps rs body htr) hbound ho

omit model in
/-- A pending function slot which no declaration in a statement suffix selects
survives that suffix.  Nested scopes and nested function translations frame
the whole table present at their entry; the only operation which can touch the
protected slot is therefore the direct `fillFunc` at a `funDef` head. -/
theorem trStmts_pending_survives (fenv : FMap) (env : VMap)
    (lctx : Option LoopCtx) (rets : Option (List Ident)) (d : Bool) :
    ∀ (ss : List (Stmt Op)) (s s' : BState) (r : Option VMap) (i : FuncId),
      s.funcs[i]? = some none →
      (∀ (n : Ident) (ps rs : List Ident) (body : List (Stmt Op)),
        Stmt.funDef n ps rs body ∈ ss → fenv.get n ≠ some i) →
      trStmts fenv env lctx rets d ss s = some (r, s') →
      s'.funcs[i]? = some none := by
  intro ss
  induction ss generalizing env d with
  | nil =>
      intro s s' r i hi _ h
      rw [trStmts] at h
      obtain ⟨-, rfl⟩ := M.pure_inv h
      exact hi
  | cons st rest ih =>
      intro s s' r i hi hskip h
      cases st with
      | funDef n ps rs body =>
          rw [trStmts] at h
          obtain ⟨fid, s1, h1, h⟩ := M.bind_inv h
          obtain ⟨g, s2, h2, h⟩ := M.bind_inv h
          obtain ⟨u, s3, h3, h4⟩ := M.bind_inv h
          obtain ⟨hget, hs1⟩ := M.liftO_inv h1
          subst s1
          have hlt : i < s.funcs.size := lt_size_of_getElem? hi
          have hi2 : s2.funcs[i]? = some none := by
            rw [trFunc_prefix fenv ps rs body h2 i hlt]
            exact hi
          have hne : i ≠ fid := by
            intro heq
            subst fid
            exact hskip n ps rs body (by simp) hget
          obtain ⟨hfid, hs3⟩ := M.fillFunc_inv h3
          have hi3 : s3.funcs[i]? = some none := by
            rw [hs3]
            rw [Array.getElem?_set (h := hfid), if_neg (Ne.symm hne)]
            exact hi2
          have hskipRest : ∀ (n' : Ident) (ps' rs' : List Ident)
              (body' : List (Stmt Op)),
              Stmt.funDef n' ps' rs' body' ∈ rest →
                fenv.get n' ≠ some i := by
            intro n' ps' rs' body' hm
            exact hskip n' ps' rs' body' (List.mem_cons_of_mem _ hm)
          exact ih env d s3 s' r i hi3 hskipRest h4
      | block body | letDecl vars val | assign vars e | cond e body
      | forLoop init e post body | «break» | «continue» | leave
      | switch e cases dflt | exprStmt e =>
          have hskipRest : ∀ (n : Ident) (ps rs : List Ident)
              (body : List (Stmt Op)),
              Stmt.funDef n ps rs body ∈ rest → fenv.get n ≠ some i := by
            intro n ps rs body hm
            exact hskip n ps rs body (List.mem_cons_of_mem _ hm)
          rw [trStmts] at h
          · split at h
            · exact ih env true s s' r i hi hskipRest h
            · obtain ⟨renv, s1, h1, h2⟩ := M.bind_inv h
              have hlt : i < s.funcs.size := lt_size_of_getElem? hi
              have hi1 : s1.funcs[i]? = some none := by
                have hp := trStmt_fprefix fenv env lctx rets _ s.funcs.size
                  s renv s1 (Nat.le_refl _) h1
                rw [hp i hlt]
                exact hi
              cases renv with
              | none => exact ih env true s1 s' r i hi1 hskipRest h2
              | some env' => exact ih env' false s1 s' r i hi1 hskipRest h2
          · intro n ps rs fbody heq
            cases heq

omit model in
/-- Once control has diverted, `trStmts` only fills hoisted function slots;
the caller's per-function construction state is restored exactly. -/
theorem trStmts_true_fn (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) : ∀ (ss : List (Stmt Op)) (s s' : BState)
      (r : Option VMap),
      trStmts fenv env lctx rets true ss s = some (r, s') →
        r = none ∧ s'.fn = s.fn := by
  intro ss
  induction ss with
  | nil =>
    intro s s' r h
    rw [trStmts] at h
    obtain ⟨rfl, rfl⟩ := M.pure_inv h
    exact ⟨rfl, rfl⟩
  | cons st rest ih =>
    cases st with
    | funDef n ps rs body =>
      intro s s' r h
      rw [trStmts] at h
      obtain ⟨fid, s₁, h1, h⟩ := M.bind_inv h
      obtain ⟨g, s₂, h2, h⟩ := M.bind_inv h
      obtain ⟨u, s₃, h3, h4⟩ := M.bind_inv h
      have hfn₁ : s₁.fn = s.fn := congrArg BState.fn (M.liftO_inv h1).2
      have hfn₂ : s₂.fn = s₁.fn := (trFunc_grows fenv ps rs body s₁ g s₂ h2).1
      obtain ⟨hlt, rfl⟩ := M.fillFunc_inv h3
      obtain ⟨hr, hfn₃⟩ := ih _ s' r h4
      exact ⟨hr, hfn₃.trans (hfn₂.trans hfn₁)⟩
    | block body | letDecl vars val | assign vars e | cond c body
    | forLoop init c post body | «break» | «continue» | leave
    | switch c cases dflt | exprStmt e =>
      intro s s' r h
      exact ih s s' r (by simpa [trStmts] using h)

omit model in
/-- Invert the live, non-function head of a statement list. -/
theorem trStmts_false_cons_inv {fenv : FMap} {env : VMap}
    {lctx : Option LoopCtx} {rets : Option (List Ident)} {st : Stmt Op}
    {rest : List (Stmt Op)} {s₀ s₁ : BState} {renv : Option VMap}
    (hnf : ∀ n ps rs body, st ≠ .funDef n ps rs body)
    (h : trStmts fenv env lctx rets false (st :: rest) s₀ = some (renv, s₁)) :
    ∃ (renvA : Option VMap) (sA : BState),
      trStmt fenv env lctx rets st s₀ = some (renvA, sA) ∧
      (match renvA with
        | some env' => trStmts fenv env' lctx rets false rest sA
        | none => trStmts fenv env lctx rets true rest sA) = some (renv, s₁) := by
  rw [trStmts] at h
  · obtain ⟨renvA, sA, h1, h2⟩ := M.bind_inv h
    refine ⟨renvA, sA, h1, ?_⟩
    cases renvA <;> exact h2
  · exact fun n ps rs body => hnf n ps rs body

/-- **`edgeArgs` carries the right values.** The ids an edge passes read back,
through `EnvOK`, as exactly the values the source environment records for those
names. This is the fact behind every join edge and every non-local exit
(`break`/`continue`/`leave`): the values the target block's parameters receive
agree with the source configuration at the jump. -/
theorem edgeArgs_ok {env : VMap} {V : VEnv yulD} {R : Regs} {xs : List Ident}
    {ids : List ValId} {s s' : BState}
    (henv : EnvOK (model := model) env V R)
    (h : edgeArgs env xs s = some (ids, s')) :
    s' = s ∧ ∃ vals, R.getMany ids = some vals
      ∧ List.Forall₂ (fun x v => YulSemantics.VEnv.get V x = some v) xs vals := by
  obtain ⟨hm, rfl⟩ := M.edgeArgs_inv h
  exact ⟨rfl, EnvOK.edge_vals henv (Forall2.mapM_eq_some_iff.mp hm)⟩

/-! ## Dialect facts the construction relies on -/

/-- The dialect zero is the machine zero (so `bindZeros` matches `const _ 0`). -/
theorem yulD_zero : YulSemantics.Dialect.zero yulD = (0 : U256) := rfl

/-- The source dialect's built-in relation *is* the one the SSA semantics
steps by, so no per-operation agreement is owed. -/
theorem yulD_Builtin (op : Op) (args : List U256) (st : EvmState)
    (r : YulSemantics.BuiltinResult U256 EvmState) :
    (yulD).Builtin op args st r
      ↔ builtinWithExternal model.calls model.creates op args st r := Iff.rfl

set_option linter.unnecessarySeqFocus false in
/-- `isHaltingOp` is sound: the operations the construction turns into a
`Term.halt` really do always halt, so sealing the block with them loses no
behavior. This is the fact that makes `trStmt`'s `exprStmt` case correct. -/
theorem isHaltingOp_halts {op : Op} (hop : isHaltingOp op = true)
    {args : List U256} {st : EvmState} {r : YulSemantics.BuiltinResult U256 EvmState}
    (hb : builtinWithExternal model.calls model.creates op args st r) :
    ∃ st', r = .halt st' := by
  -- the five halting ops are outside the CALL/CREATE/GAS families, so the
  -- open-world relation is `stepOp`, whose result for them is always a `.halt`
  have hop' : op = .stop ∨ op = .ret ∨ op = .revert ∨ op = .invalid
      ∨ op = .selfdestruct := by
    cases op <;> simp_all [isHaltingOp]
  have hstep : YulSemantics.EVM.stepOp op args st = some r := by
    rcases hop' with rfl | rfl | rfl | rfl | rfl <;> exact hb
  rcases hop' with rfl | rfl | rfl | rfl | rfl
  · rcases args with _ | ⟨a, l⟩ <;>
      simp_all [YulSemantics.EVM.stepOp] <;> exact ⟨_, hstep.symm⟩
  · rcases args with _ | ⟨a, _ | ⟨b, _ | l⟩⟩ <;>
      simp_all [YulSemantics.EVM.stepOp] <;> exact ⟨_, hstep.symm⟩
  · rcases args with _ | ⟨a, _ | ⟨b, _ | l⟩⟩ <;>
      simp_all [YulSemantics.EVM.stepOp] <;> exact ⟨_, hstep.symm⟩
  · rcases args with _ | ⟨a, l⟩ <;>
      simp_all [YulSemantics.EVM.stepOp] <;> exact ⟨_, hstep.symm⟩
  · rcases args with _ | ⟨a, _ | l⟩ <;>
      simp_all [YulSemantics.EVM.stepOp, YulSemantics.EVM.guardStatic] <;>
      by_cases hs : st.env.static <;> simp_all <;> exact ⟨_, hstep.symm⟩

/-- The `eq` test the switch chain emits. -/
theorem builtin_eq (a b : U256) (st : EvmState) :
    builtinWithExternal model.calls model.creates .eq [a, b] st
      (.ok [YulSemantics.EVM.b2w (a = b)] st) := rfl

/-! ## The simulation shapes

The construction fills one basic block at a time, so a fragment's meaning is
*continuation-passing*: "whatever the rest of the finished block does from the
second configuration, it also does from the first". That is the SSA analogue of
`SimAsm`'s `ASimS`, with `FnState` in place of a list position. -/

/-- `CurOK f fn rest`: in the finished function `f`, the block the builder is
currently filling continues with `rest` after the instructions it has already
emitted (`fn.cur`, reversed). -/
def CurOK (f : Func) (fn : FnState) (rest : Rest) : Prop :=
  ∃ b, f.blocks[fn.curId]? = some b
    ∧ b.instrs = fn.cur.reverse ++ rest.instrs ∧ b.term = rest.term

omit model in
/-- Exact backward transport of a finished current block when builder-only
steps changed neither its id nor its pending instruction list. -/
theorem CurOK.back_of_cur_eq {f : Func} {fn fn' : FnState} {rest : Rest}
    (hid : fn'.curId = fn.curId) (hcur : fn'.cur = fn.cur)
    (h : CurOK f fn' rest) : CurOK f fn rest := by
  obtain ⟨b, hb, hi, ht⟩ := h
  exact ⟨b, by simpa only [hid] using hb, by simpa only [hcur] using hi, ht⟩

/-- Execution of the rest of the block the builder is currently filling. -/
def ExecFrom (P : Prog) (f : Func) (fn : FnState) (R : Regs) (st : EvmState)
    (res : FRes) : Prop :=
  ∃ rest, CurOK f fn rest ∧ Exec (model := model) P f R st rest res

/-- `SimS`: the fragment the builder laid down between `fn₀` and `fn₁` carries
⟨`R₀`, `st`⟩ to ⟨`R₁`, `st'`⟩ — every continuation of the second configuration
is realized from the first. -/
def SimS (P : Prog) (f : Func) (fn₀ : FnState) (R₀ : Regs) (st : EvmState)
    (fn₁ : FnState) (R₁ : Regs) (st' : EvmState) : Prop :=
  ∀ res, ExecFrom (model := model) P f fn₁ R₁ st' res
    → ExecFrom (model := model) P f fn₀ R₀ st res

/-- Taking a control-flow edge to `bid` that carries `vals`. -/
def JumpTo (P : Prog) (f : Func) (bid : BlockId) (vals : List U256) (R : Regs)
    (st : EvmState) (res : FRes) : Prop :=
  ∃ tb, f.blocks[bid]? = some tb ∧ tb.params.length = vals.length
    ∧ Exec (model := model) P f (R.setMany tb.params vals) st
        ⟨tb.instrs, tb.term⟩ res

/-- SSA execution is monotone in already-defined registers.  The generated
code only reads registers and applies the same bindings on both sides, so
extra bindings cannot invalidate an execution.  Loop iterations use this to
re-enter a statically shared header with the register facts accumulated by the
previous iteration. -/
theorem Exec.mono {P : Prog} {f : Func} {R R' : Regs} {st : EvmState}
    {rest : Rest} {res : FRes} (hle : Regs.Le R R')
    (h : Exec (model := model) P f R st rest res) :
    Exec (model := model) P f R' st rest res := by
  induction h generalizing R' with
  | const h ih =>
    exact .const (ih (hle.setBoth _ _))
  | op hargs hb hlen hrest ih =>
    exact .op (Regs.getMany_mono hle hargs) hb hlen
      (ih (hle.setManyBoth))
  | opHalt hargs hb =>
    exact .opHalt (Regs.getMany_mono hle hargs) hb
  | call hg hargs hparams heb hbody hlen hrest _ihbody ihrest =>
    exact .call hg (Regs.getMany_mono hle hargs) hparams heb hbody hlen
      (ihrest hle.setManyBoth)
  | callHalt hg hargs hparams heb hbody =>
    exact .callHalt hg (Regs.getMany_mono hle hargs) hparams heb hbody
  | jump htarget hargs hlen hbody ih =>
    exact .jump htarget (Regs.getMany_mono hle hargs) hlen
      (ih hle.setManyBoth)
  | branchTrue hc hnz htarget hargs hlen hbody ih =>
    exact .branchTrue (hle _ _ hc) hnz htarget
      (Regs.getMany_mono hle hargs) hlen (ih hle.setManyBoth)
  | branchFalse hc htarget hargs hlen hbody ih =>
    exact .branchFalse (hle _ _ hc) htarget
      (Regs.getMany_mono hle hargs) hlen (ih hle.setManyBoth)
  | ret hvals => exact .ret (Regs.getMany_mono hle hvals)
  | halt hargs hb => exact .halt (Regs.getMany_mono hle hargs) hb

theorem ExecFrom.mono {P : Prog} {f : Func} {fn : FnState} {R R' : Regs}
    {st : EvmState} {res : FRes} (hle : Regs.Le R R')
    (h : ExecFrom (model := model) P f fn R st res) :
    ExecFrom (model := model) P f fn R' st res := by
  obtain ⟨rest, hcur, hex⟩ := h
  exact ⟨rest, hcur, hex.mono hle⟩

namespace SimS

theorem rfl' {P : Prog} {f : Func} {fn : FnState} {R : Regs} {st : EvmState} :
    SimS (model := model) P f fn R st fn R st := fun _ h => h

theorem trans {P : Prog} {f : Func} {fn₀ fn₁ fn₂ : FnState} {R₀ R₁ R₂ : Regs}
    {st₀ st₁ st₂ : EvmState}
    (h₁ : SimS (model := model) P f fn₀ R₀ st₀ fn₁ R₁ st₁)
    (h₂ : SimS (model := model) P f fn₁ R₁ st₁ fn₂ R₂ st₂) :
    SimS (model := model) P f fn₀ R₀ st₀ fn₂ R₂ st₂ :=
  fun res h => h₁ res (h₂ res h)

end SimS

/-! ### Leaves: prepending an emitted instruction

Each `emit` in the construction is one of these three steps. They are the only
place `Exec`'s instruction rules are used, and they are unconditional. -/

/-- `emit (.const d v)`. -/
theorem simS_const {P : Prog} {f : Func} {fn fn' : FnState} {R : Regs}
    {st : EvmState} {d : ValId} {v : U256}
    (hc : fn'.curId = fn.curId) (hcur : fn'.cur = .const d v :: fn.cur) :
    SimS (model := model) P f fn R st fn' (R.set d v) st := by
  intro res h
  obtain ⟨rest, ⟨b, hb, hinstrs, hterm⟩, hexec⟩ := h
  rw [hc] at hb
  rw [hcur] at hinstrs
  refine ⟨⟨.const d v :: rest.instrs, rest.term⟩, ⟨b, hb, ?_, hterm⟩, .const hexec⟩
  simpa using hinstrs

/-- `emit (.op ds yop as)` on the returning path. -/
theorem simS_op {P : Prog} {f : Func} {fn : FnState} {R : Regs}
    {st st' : EvmState} {ds : List ValId} {yop : Op} {as : List ValId}
    {args rets : List U256}
    (hargs : R.getMany as = some args)
    (hb : builtinWithExternal model.calls model.creates yop args st (.ok rets st'))
    (hlen : ds.length = rets.length)
    {fn' : FnState} (hc : fn'.curId = fn.curId)
    (hcur : fn'.cur = .op ds yop as :: fn.cur) :
    SimS (model := model) P f fn R st fn' (R.setMany ds rets) st' := by
  intro res h
  obtain ⟨rest, ⟨b, hbl, hinstrs, hterm⟩, hexec⟩ := h
  rw [hc] at hbl
  rw [hcur] at hinstrs
  refine ⟨⟨.op ds yop as :: rest.instrs, rest.term⟩, ⟨b, hbl, ?_, hterm⟩,
    .op hargs hb hlen hexec⟩
  simpa using hinstrs

/-- `emit (.op ds yop as)` where the built-in halts. -/
theorem execFrom_opHalt {P : Prog} {f : Func} {fn : FnState} {R : Regs}
    {st st' : EvmState} {ds : List ValId} {yop : Op} {as : List ValId}
    {args : List U256} {rest : Rest}
    (hcur : CurOK f { fn with cur := .op ds yop as :: fn.cur } rest)
    (hargs : R.getMany as = some args)
    (hb : builtinWithExternal model.calls model.creates yop args st (.halt st')) :
    ExecFrom (model := model) P f fn R st (.halt st') := by
  obtain ⟨b, hbl, hinstrs, hterm⟩ := hcur
  exact ⟨⟨.op ds yop as :: rest.instrs, rest.term⟩, ⟨b, hbl, by simpa using hinstrs, hterm⟩,
    .opHalt hargs hb⟩

/-- `emit (.call ds fid as)` on the returning path. -/
theorem simS_call {P : Prog} {f g : Func} {fn : FnState} {R : Regs}
    {st st' : EvmState} {ds as : List ValId} {fid : FuncId}
    {args rvals : List U256} {eb : Block}
    (hg : P.funcs[fid]? = some g)
    (hargs : R.getMany as = some args)
    (hparams : g.params.length = args.length)
    (heb : g.blocks[g.entry]? = some eb)
    (hbody : Exec (model := model) P g (Regs.empty.setMany g.params args) st
      ⟨eb.instrs, eb.term⟩ (.ret rvals st'))
    (hlen : ds.length = rvals.length)
    {fn' : FnState} (hc : fn'.curId = fn.curId)
    (hcur : fn'.cur = .call ds fid as :: fn.cur) :
    SimS (model := model) P f fn R st fn' (R.setMany ds rvals) st' := by
  intro res h
  obtain ⟨rest, ⟨b, hbl, hinstrs, hterm⟩, hexec⟩ := h
  rw [hc] at hbl
  rw [hcur] at hinstrs
  refine ⟨⟨.call ds fid as :: rest.instrs, rest.term⟩, ⟨b, hbl, ?_, hterm⟩,
    .call hg hargs hparams heb hbody hlen hexec⟩
  simpa using hinstrs

/-- `emit (.call ds fid as)` where the callee halts. -/
theorem execFrom_callHalt {P : Prog} {f g : Func} {fn : FnState} {R : Regs}
    {st st' : EvmState} {ds as : List ValId} {fid : FuncId} {args : List U256}
    {eb : Block} {rest : Rest}
    (hcur : CurOK f { fn with cur := .call ds fid as :: fn.cur } rest)
    (hg : P.funcs[fid]? = some g)
    (hargs : R.getMany as = some args)
    (hparams : g.params.length = args.length)
    (heb : g.blocks[g.entry]? = some eb)
    (hbody : Exec (model := model) P g (Regs.empty.setMany g.params args) st
      ⟨eb.instrs, eb.term⟩ (.halt st')) :
    ExecFrom (model := model) P f fn R st (.halt st') := by
  obtain ⟨b, hbl, hinstrs, hterm⟩ := hcur
  exact ⟨⟨.call ds fid as :: rest.instrs, rest.term⟩,
    ⟨b, hbl, by simpa using hinstrs, hterm⟩, .callHalt hg hargs hparams heb hbody⟩

/-- No instructions emitted. -/
theorem simS_id {P : Prog} {f : Func} {fn fn' : FnState} {R : Regs}
    {st : EvmState} (hc : fn'.curId = fn.curId) (hcur : fn'.cur = fn.cur) :
    SimS (model := model) P f fn R st fn' R st := by
  intro res h
  obtain ⟨rest, ⟨b, hb, hinstrs, hterm⟩, hexec⟩ := h
  rw [hc] at hb
  rw [hcur] at hinstrs
  exact ⟨rest, ⟨b, hb, hinstrs, hterm⟩, hexec⟩

/-- A whole block of zero-initialising `const`s — `let x` without a value, and
`trFunc`'s return variables. -/
theorem simS_consts {P : Prog} {f : Func} {st : EvmState} :
    ∀ (ids : List ValId) (R : Regs) (fn fn' : FnState), fn'.curId = fn.curId →
      fn'.cur = (ids.map (fun v => Instr.const v 0)).reverse ++ fn.cur →
      SimS (model := model) P f fn R st fn'
        (R.setMany ids (List.replicate ids.length 0)) st := by
  intro ids
  induction ids with
  | nil => intro R fn fn' hc hcur; simpa using simS_id hc (by simpa using hcur)
  | cons v ids ih =>
    intro R fn fn' hc hcur
    have hstep : SimS (model := model) P f fn R st
        { fn with cur := .const v 0 :: fn.cur } (R.set v 0) st :=
      simS_const rfl rfl
    have htail := ih (R.set v 0) { fn with cur := .const v 0 :: fn.cur } fn' hc (by
      rw [hcur]; simp)
    rw [List.length_cons, List.replicate_succ, Regs.setMany_cons]
    exact hstep.trans htail

/-! ### Leaves: the terminators the construction seals with -/

/-- A block sealed with `ret xs` returns. -/
theorem execFrom_ret {P : Prog} {f : Func} {fn : FnState} {R : Regs}
    {st : EvmState} {xs : List ValId} {vals : List U256}
    (hcur : CurOK f fn ⟨[], .ret xs⟩) (hg : R.getMany xs = some vals) :
    ExecFrom (model := model) P f fn R st (.ret vals st) :=
  ⟨⟨[], .ret xs⟩, hcur, .ret hg⟩

/-- A block sealed with `halt yop as` halts. -/
theorem execFrom_halt {P : Prog} {f : Func} {fn : FnState} {R : Regs}
    {st st' : EvmState} {yop : Op} {as : List ValId} {args : List U256}
    (hcur : CurOK f fn ⟨[], .halt yop as⟩) (hg : R.getMany as = some args)
    (hb : builtinWithExternal model.calls model.creates yop args st (.halt st')) :
    ExecFrom (model := model) P f fn R st (.halt st') :=
  ⟨⟨[], .halt yop as⟩, hcur, .halt hg hb⟩

/-- A block sealed with `jump e` transfers along `e`. -/
theorem execFrom_jump {P : Prog} {f : Func} {fn : FnState} {R : Regs}
    {st : EvmState} {e : Edge} {vals : List U256} {res : FRes}
    (hcur : CurOK f fn ⟨[], .jump e⟩) (hg : R.getMany e.args = some vals)
    (hjmp : JumpTo (model := model) P f e.target vals R st res) :
    ExecFrom (model := model) P f fn R st res := by
  obtain ⟨tb, htb, hlen, hexec⟩ := hjmp
  exact ⟨⟨[], .jump e⟩, hcur, .jump htb hg hlen hexec⟩

/-- Converse of `execFrom_jump` when the finished current block is known to
end at that jump.  This is the loop back-edge bridge: the recursive loop IH
produces an `ExecFrom` at the original preheader, while the current iteration
has reached a `JumpTo` into the header.  Uniqueness of the finished current
block identifies the existential continuation with the known jump. -/
theorem jumpTo_of_execFrom_jump {P : Prog} {f : Func} {fn : FnState} {R : Regs}
    {st : EvmState} {e : Edge} {res : FRes}
    (hcur : CurOK f fn ⟨[], .jump e⟩)
    (hex : ExecFrom (model := model) P f fn R st res) :
    ∃ vals, R.getMany e.args = some vals ∧
      JumpTo (model := model) P f e.target vals R st res := by
  obtain ⟨b, hb, hib, htb⟩ := hcur
  obtain ⟨rest, ⟨b', hb', hib', htb'⟩, hexec⟩ := hex
  have hbb : b' = b := Option.some.inj (hb'.symm.trans hb)
  subst b'
  have hi : rest.instrs = [] := by
    apply List.append_cancel_left
    simpa only [List.append_nil] using hib'.symm.trans hib
  have ht : rest.term = .jump e := htb'.symm.trans htb
  cases rest with
  | mk instrs term =>
    simp only at hi ht
    subst instrs
    subst term
    cases hexec with
    | jump htarget hargs hlen hbody =>
      exact ⟨_, hargs, ⟨_, htarget, hlen, hbody⟩⟩

/-- Package execution from an empty current target block back into `JumpTo`.
This is the other half of the loop back-edge bridge: the recursive header IH
starts at the builder's empty `sI.cur`, while the post terminator expects a
`JumpTo` witness for the same finished block. -/
theorem jumpTo_of_execFrom_empty {P : Prog} {f : Func} {fn : FnState}
    {R : Regs} {st : EvmState} {bid : BlockId} {params : List ValId}
    {vals : List U256} {b : Block} {res : FRes}
    (hb : f.blocks[bid]? = some b) (hparams : b.params = params)
    (hcur : fn.curId = bid) (hcur0 : fn.cur = [])
    (hlen : params.length = vals.length)
    (hex : ExecFrom (model := model) P f fn (R.setMany params vals) st res) :
    JumpTo (model := model) P f bid vals R st res := by
  obtain ⟨rest, ⟨b', hb', hi, ht⟩, hexec⟩ := hex
  rw [hcur] at hb'
  have hbb : b' = b := Option.some.inj (hb'.symm.trans hb)
  subst b'
  refine ⟨b, hb, by simpa only [hparams] using hlen, ?_⟩
  rw [hparams]
  rw [hcur0] at hi
  have hi' : b.instrs = rest.instrs := by simpa using hi
  simpa only [hi', ht] using hexec

/-- A block sealed with `branch c t f`, true edge. -/
theorem execFrom_branchTrue {P : Prog} {f : Func} {fn : FnState} {R : Regs}
    {st : EvmState} {c : ValId} {v : U256} {et ef : Edge} {vals : List U256}
    {res : FRes} (hcur : CurOK f fn ⟨[], .branch c et ef⟩)
    (hc : R c = some v) (hnz : v ≠ 0)
    (hg : R.getMany et.args = some vals)
    (hjmp : JumpTo (model := model) P f et.target vals R st res) :
    ExecFrom (model := model) P f fn R st res := by
  obtain ⟨tb, htb, hlen, hexec⟩ := hjmp
  exact ⟨⟨[], .branch c et ef⟩, hcur, .branchTrue hc hnz htb hg hlen hexec⟩

/-- A block sealed with `branch c t f`, false edge. -/
theorem execFrom_branchFalse {P : Prog} {f : Func} {fn : FnState} {R : Regs}
    {st : EvmState} {c : ValId} {et ef : Edge} {vals : List U256} {res : FRes}
    (hcur : CurOK f fn ⟨[], .branch c et ef⟩) (hc : R c = some 0)
    (hg : R.getMany ef.args = some vals)
    (hjmp : JumpTo (model := model) P f ef.target vals R st res) :
    ExecFrom (model := model) P f fn R st res := by
  obtain ⟨tb, htb, hlen, hexec⟩ := hjmp
  exact ⟨⟨[], .branch c et ef⟩, hcur, .branchFalse hc htb hg hlen hexec⟩

/-! ### The freshness invariant

The register file only ever binds ids the builder has already handed out. This
is what makes `Regs.Le` available at every `freshVal`: the id just allocated is
provably unbound, so binding it *extends* the register file and every earlier
fact survives (`EnvOK.mono`). -/

/-- `R` binds nothing the builder has not yet allocated. -/
def RegsFresh (R : Regs) (fn : FnState) : Prop :=
  ∀ i : ValId, fn.nextVal ≤ i → R i = none

namespace RegsFresh

omit model in
theorem mono {R : Regs} {fn fn' : FnState} (h : RegsFresh R fn)
    (hle : fn.nextVal ≤ fn'.nextVal) : RegsFresh R fn' :=
  fun i hi => h i (Nat.le_trans hle hi)

omit model in
/-- The id `freshVal` is about to hand out is unbound. -/
theorem unbound {R : Regs} {fn : FnState} (h : RegsFresh R fn) :
    R fn.nextVal = none := h _ (Nat.le_refl _)

omit model in
theorem set {R : Regs} {fn fn' : FnState} (h : RegsFresh R fn) (v : U256)
    (hnv : fn.nextVal + 1 ≤ fn'.nextVal) :
    RegsFresh (R.set fn.nextVal v) fn' := by
  intro i hi
  have hlt : fn.nextVal < i := Nat.lt_of_lt_of_le hnv hi
  rw [Regs.set_other R v (Nat.ne_of_gt hlt)]
  exact h i (Nat.le_of_lt hlt)

omit model in
/-- A whole `mapM freshVal` block of ids. -/
theorem setMany {R : Regs} {fn fn' : FnState} (h : RegsFresh R fn) {n : Nat}
    {vs : List U256} (hnv : fn.nextVal + n ≤ fn'.nextVal) :
    RegsFresh (R.setMany (List.range' fn.nextVal n) vs) fn' := by
  intro i hi
  have hchain : fn.nextVal + n ≤ i := Nat.le_trans hnv hi
  have hnm : i ∉ List.range' fn.nextVal n := by
    intro hmem
    obtain ⟨-, hb2⟩ := M.mem_range'_bounds hmem
    exact absurd (Nat.lt_of_lt_of_le hb2 hchain) (Nat.lt_irrefl i)
  rw [Regs.setMany_other hnm]
  exact h i (Nat.le_trans (Nat.le_add_right _ n) hchain)

end RegsFresh

/-! ### Expression-class simulation

The motive the `.expr` / `.args` cases of the main induction carry: the fragment
the construction laid down transports the machine state, defines the
expression's `ValId`, and *extends* the register file (single assignment). -/

/-- One expression: `i` holds `v` in the extended register file. -/
def EOut (P : Prog) (f : Func) (s₀ s₁ : BState) (R₀ : Regs) (i : ValId)
    (v : U256) (yst yst' : EvmState) : Prop :=
  ∃ R₁ : Regs, Regs.Le R₀ R₁ ∧ Regs.BelowEq s₀.fn.nextVal R₀ R₁
    ∧ RegsFresh R₁ s₁.fn ∧ R₁ i = some v
    ∧ SimS (model := model) P f s₀.fn R₀ yst s₁.fn R₁ yst'

/-- An argument list: the ids read back as the value list, in source order. -/
def EOutL (P : Prog) (f : Func) (s₀ s₁ : BState) (R₀ : Regs)
    (ids : List ValId) (vs : List U256) (yst yst' : EvmState) : Prop :=
  ∃ R₁ : Regs, Regs.Le R₀ R₁ ∧ Regs.BelowEq s₀.fn.nextVal R₀ R₁
    ∧ RegsFresh R₁ s₁.fn ∧ R₁.getMany ids = some vs
    ∧ SimS (model := model) P f s₀.fn R₀ yst s₁.fn R₁ yst'

/-- **`lit`** — the construction emits a `const`; the source rule leaves the
machine state alone. -/
theorem sim_lit {P : Prog} {f : Func} {fenv : FMap} {env : VMap} {R : Regs}
    {l : Literal} {s₀ s₁ : BState} {i : ValId} {yst : EvmState}
    (hfresh : RegsFresh R s₀.fn)
    (htr : trExpr fenv env (.lit l) s₀ = some (i, s₁)) :
    EOut (model := model) P f s₀ s₁ R i (YulSemantics.EVM.litValue l) yst yst := by
  rw [trExpr] at htr
  obtain ⟨w, sA, h1, htr⟩ := M.bind_inv htr
  obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
  rw [M.freshVal_apply] at h1
  obtain ⟨hw, hsA⟩ := M.some_pair_inj h1
  subst hw
  subst hsA
  rw [M.emit_apply] at h2
  obtain ⟨-, hsB⟩ := M.some_pair_inj h2
  subst hsB
  obtain ⟨hi, hs₁⟩ := M.pure_inv h3
  subst hi
  subst hs₁
  exact ⟨R.set s₀.fn.nextVal (YulSemantics.EVM.litValue l),
    Regs.Le.set _ hfresh.unbound, Regs.BelowEq.set _ (Nat.le_refl _),
    hfresh.set _ (Nat.le_refl _),
    Regs.set_same .., simS_const rfl rfl⟩

/-- **`var`** — the construction resolves the name in its `VMap`; `EnvOK` says
the id it finds holds the value the source environment records. -/
theorem sim_var {P : Prog} {f : Func} {fenv : FMap} {env : VMap} {R : Regs}
    {V : VEnv yulD} {x : Ident} {v : U256} {s₀ s₁ : BState} {i : ValId}
    {yst : EvmState}
    (hfresh : RegsFresh R s₀.fn) (henv : EnvOK (model := model) env V R)
    (hget : YulSemantics.VEnv.get V x = some v)
    (htr : trExpr fenv env (.var x) s₀ = some (i, s₁)) :
    EOut (model := model) P f s₀ s₁ R i v yst yst := by
  rw [trExpr] at htr
  obtain ⟨hlk, hs₁⟩ := M.liftO_inv htr
  obtain ⟨j, hj, hRj⟩ := henv.get_rev hget
  obtain rfl : i = j := Option.some.inj (hlk.symm.trans hj)
  subst hs₁
  exact ⟨R, Regs.Le.rfl R, Regs.BelowEq.rfl _ _, hfresh, hRj, SimS.rfl'⟩

/-- **`args []`** — nothing emitted. -/
theorem sim_args_nil {P : Prog} {f : Func} {fenv : FMap} {env : VMap} {R : Regs}
    {s₀ s₁ : BState} {ids : List ValId} {yst : EvmState}
    (hfresh : RegsFresh R s₀.fn)
    (htr : trArgs fenv env [] s₀ = some (ids, s₁)) :
    EOutL (model := model) P f s₀ s₁ R ids [] yst yst := by
  rw [trArgs] at htr
  obtain ⟨hids, hs₁⟩ := M.pure_inv htr
  subst hs₁; subst hids
  exact ⟨R, Regs.Le.rfl R, Regs.BelowEq.rfl _ _, hfresh, rfl, SimS.rfl'⟩

/-- **`args (e :: rest)`** — the construction translates `rest` first, matching
the source's right-to-left evaluation order; the two fragments compose and the
earlier ids survive because the register file only extends. -/
theorem sim_args_cons {P : Prog} {f : Func} {s₀ sA s₁ : BState} {R : Regs}
    {restIds : List ValId} {i : ValId} {restvals : List U256} {v : U256}
    {yst yst1 yst2 : EvmState}
    (hrest : EOutL (model := model) P f s₀ sA R restIds restvals yst yst1)
    (hgrow : s₀.fn.nextVal ≤ sA.fn.nextVal)
    (hhead : ∀ R', Regs.Le R R' → RegsFresh R' sA.fn →
      EOut (model := model) P f sA s₁ R' i v yst1 yst2) :
    EOutL (model := model) P f s₀ s₁ R (i :: restIds) (v :: restvals) yst yst2 := by
  obtain ⟨Ra, hle, hbelow, hfr, hget, hsim⟩ := hrest
  obtain ⟨Rb, hle2, hbelow2, hfr2, hi, hsim2⟩ := hhead Ra hle hfr
  refine ⟨Rb, hle.trans hle2,
    hbelow.trans (hbelow2.mono hgrow), hfr2, ?_, hsim.trans hsim2⟩
  rw [Regs.getMany_cons, hi, Regs.getMany_mono hle2 hget]
  simp

/-! ## Function environments

`FMap` mirrors `FunEnv` scope by scope, exactly like `SimAsm.FEnvOK` mirrors it
for the classic backend. Unlike `lookupF`, `FMap.get` does not hand back the
scope tail visible at the definition site, so the correspondence lemma
existentially produces it. -/

/-- What the construction guarantees about the slot a function name resolves
to: the slot holds the `trFunc` translation of that source declaration against
the scopes visible at its definition site, and the nested slots that
translation filled survived into the finished program. -/
def FuncOK (P : Prog) (fenv : FMap) (decl : YulSemantics.FDecl yulD)
    (fid : FuncId) : Prop :=
  ∃ (g : Func) (s₀ s₁ : BState),
    P.funcs[fid]? = some g
    ∧ trFunc fenv decl.params decl.rets decl.body s₀ = some (g, s₁)
    ∧ ∀ (i : Nat) (g' : Func), s₁.funcs[i]? = some (some g') → P.funcs[i]? = some g'

/-- Scopewise agreement between the semantic function environment and the
construction's. Each function's `FMap` is its own scope outward — exactly what
`lookupFun` returns as the callee environment. -/
inductive FEnvOK (P : Prog) : YulSemantics.FunEnv yulD → FMap → Prop
  | nil : FEnvOK P [] []
  | cons {scope : YulSemantics.FScope yulD} {mp : List (Ident × FuncId)}
      {rest : YulSemantics.FunEnv yulD} {restM : FMap} :
      List.Forall₂ (fun (p : Ident × YulSemantics.FDecl yulD) (q : Ident × FuncId) =>
        p.1 = q.1 ∧ FuncOK (model := model) P (mp :: restM) p.2 q.2) scope mp →
      FEnvOK P rest restM →
      FEnvOK P (scope :: rest) (mp :: restM)

/-- The two scope searches agree, entry by entry. -/
private theorem find?_agree {P : Prog} {fenv : FMap} {x : Ident} :
    ∀ {scope : YulSemantics.FScope yulD} {mp : List (Ident × FuncId)},
      List.Forall₂ (fun (p : Ident × YulSemantics.FDecl yulD) (q : Ident × FuncId) =>
        p.1 = q.1 ∧ FuncOK (model := model) P fenv p.2 q.2) scope mp →
      (scope.find? (fun p => p.1 = x) = none ∧ mp.find? (fun q => q.1 = x) = none)
      ∨ (∃ p q, scope.find? (fun p => p.1 = x) = some p
          ∧ mp.find? (fun q => q.1 = x) = some q
          ∧ FuncOK (model := model) P fenv p.2 q.2) := by
  intro scope mp h
  induction h with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | @cons p q scope' mp' hpq _ ih =>
    obtain ⟨hname, hok⟩ := hpq
    by_cases hf : p.1 = x
    · refine Or.inr ⟨p, q, ?_, ?_, hok⟩
      · rw [List.find?_cons_of_pos (by simpa using hf)]
      · rw [List.find?_cons_of_pos (by simp [← hname, hf])]
    · rw [show scope'.find? (fun p => p.1 = x)
          = (p :: scope').find? (fun p => p.1 = x) from by
        rw [List.find?_cons_of_neg (by simpa using hf)]] at ih
      rw [show mp'.find? (fun q => q.1 = x)
          = (q :: mp').find? (fun q => q.1 = x) from by
        rw [List.find?_cons_of_neg (by simp [← hname, hf])]] at ih
      exact ih

/-- Successful lookups on corresponding environments correspond: the source
resolves `x` to `decl` with callee environment `cenv` exactly when the
construction resolves it to a slot translated against a `FMap` mirroring
`cenv`. -/
theorem FMap.get_ok {P : Prog} {funs : YulSemantics.FunEnv yulD} {fenv : FMap}
    (h : FEnvOK (model := model) P funs fenv) {x : Ident}
    {decl : YulSemantics.FDecl yulD} {cenv : YulSemantics.FunEnv yulD}
    (hlk : YulSemantics.lookupFun funs x = some (decl, cenv)) :
    ∃ (fid : FuncId) (fenv' : FMap),
      FMap.get fenv x = some fid ∧ FuncOK (model := model) P fenv' decl fid
        ∧ FEnvOK (model := model) P cenv fenv' := by
  induction h with
  | nil => exact absurd hlk (by simp [YulSemantics.lookupFun])
  | @cons scope mp rest restM hscope hrest ih =>
    rw [YulSemantics.lookupFun] at hlk
    rw [FMap.get]
    rcases find?_agree hscope (x := x) with ⟨hn1, hn2⟩ | ⟨p, q, hs1, hs2, hok⟩
    · rw [hn1] at hlk
      rw [hn2]
      exact ih hlk
    · rw [hs1] at hlk
      rw [hs2]
      obtain ⟨rfl, rfl⟩ : p.2 = decl ∧ scope :: rest = cenv := by
        refine ⟨?_, ?_⟩ <;> · injection hlk with h'; cases h'; rfl
      exact ⟨q.2, mp :: restM, rfl, hok, .cons hscope hrest⟩

/-! ## Inverting the top-level build -/

/-- The builder state the top level hands to `trScope`: block `0` reserved and
current, nothing else allocated. -/
def initBState : BState :=
  { fn := { blocks := #[⟨[], [], .ret []⟩], curId := 0, cur := [], nextVal := 0 },
    funcs := #[] }

/-- The top-level build action (the `let build := …` of `ofBlockRaw`). -/
def buildMain (prog : List (Stmt Op)) : M Func := do
  let entry ← newBlock []
  moveTo entry
  let renv ← trScope [] [] none none prog
  if let some _ := renv then sealCur (.ret [])
  let done ← getFn
  pure { params := [], nrets := 0, entry := entry, blocks := done.blocks }

omit model in
/-- The top-level build, decomposed: the whole program is one `trScope` over
`prog` from `initBState`, followed by the fall-through `ret []` seal when
control was not diverted. -/
theorem buildMain_inv {prog : List (Stmt Op)} {main : Func} {s : BState}
    (h : buildMain prog {} = some (main, s)) :
    ∃ (renv : Option VMap) (s₁ : BState),
      trScope [] [] none none prog initBState = some (renv, s₁)
      ∧ main.params = [] ∧ main.nrets = 0 ∧ main.entry = 0
      ∧ s.funcs = s₁.funcs
      ∧ (match renv with
          | some _ => ∃ b, s₁.fn.blocks[s₁.fn.curId]? = some b
              ∧ main.blocks
                  = s₁.fn.blocks.set! s₁.fn.curId ⟨b.params, s₁.fn.cur.reverse, .ret []⟩
          | none => main.blocks = s₁.fn.blocks) := by
  rw [buildMain] at h
  obtain ⟨entry, sA, h1, h⟩ := M.bind_inv h
  rw [M.newBlock_apply] at h1
  obtain ⟨rfl, rfl⟩ : entry = 0 ∧ sA = initBState := by
    have h' := Option.some.inj h1
    exact ⟨(congrArg Prod.fst h').symm, (congrArg Prod.snd h').symm⟩
  obtain ⟨u, sB, h2, h⟩ := M.bind_inv h
  rw [M.moveTo_apply] at h2
  obtain rfl : sB = initBState := (congrArg Prod.snd (Option.some.inj h2)).symm
  obtain ⟨renv, s₁, h3, h⟩ := M.bind_inv h
  refine ⟨renv, s₁, h3, ?_⟩
  cases renv with
  | none =>
    -- the `if let` takes its `pure ()` branch, and `getFn`/`pure` are total, so
    -- the whole tail computes
    have h' : some ((⟨[], 0, 0, s₁.fn.blocks⟩ : Func), s₁) = some (main, s) := h
    have he := Option.some.inj h'
    obtain rfl : main = (⟨[], 0, 0, s₁.fn.blocks⟩ : Func) :=
      (congrArg Prod.fst he).symm
    obtain rfl : s = s₁ := (congrArg Prod.snd he).symm
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | some e =>
    obtain ⟨u', s₂, h4, h⟩ := M.bind_inv h
    obtain ⟨b, hb, rfl⟩ := M.sealCur_inv h4
    obtain ⟨fnv, s₃, h5, h⟩ := M.bind_inv h
    rw [M.getFn_apply] at h5
    obtain ⟨rfl, rfl⟩ :
        fnv = { s₁.fn with
                  blocks := s₁.fn.blocks.set! s₁.fn.curId
                    ⟨b.params, s₁.fn.cur.reverse, .ret []⟩, cur := [] }
          ∧ s₃ = { s₁ with fn := { s₁.fn with
                  blocks := s₁.fn.blocks.set! s₁.fn.curId
                    ⟨b.params, s₁.fn.cur.reverse, .ret []⟩, cur := [] } } := by
      have h' := Option.some.inj h5
      exact ⟨(congrArg Prod.fst h').symm, (congrArg Prod.snd h').symm⟩
    obtain ⟨rfl, rfl⟩ := M.pure_inv h
    exact ⟨rfl, rfl, rfl, rfl, ⟨b, hb, rfl⟩⟩

omit model in
/-- The public entry point, inverted: `wfCheck` passed, and the build ran as
`buildMain_inv` describes with all function slots filled. -/
theorem ofBlock_inv {prog : List (Stmt Op)} {P : Prog}
    (hof : ofBlock prog = some P) :
    P.wfCheck = true ∧ ∃ (main : Func) (s : BState),
      buildMain prog {} = some (main, s)
      ∧ s.funcs.mapM id = some P.funcs ∧ P.main = main := by
  refine ⟨ofBlock_wfCheck hof, ?_⟩
  unfold ofBlock at hof
  rcases hraw : ofBlockRaw prog with _ | Q <;> rw [hraw] at hof
  · exact absurd hof (by simp)
  have hQ : Q = P := by
    by_cases hwf : Q.wfCheck
    · simp only [Option.bind_some, hwf, if_true] at hof; exact Option.some.inj hof
    · simp only [Option.bind_some, hwf, Bool.false_eq_true, if_false] at hof
      exact absurd hof (by simp)
  rw [hQ] at hraw
  unfold ofBlockRaw at hraw
  simp only [bind, Option.bind] at hraw
  split at hraw
  · exact absurd hraw (by simp)
  · rename_i p hp
    have hp' : buildMain prog {} = some p := hp
    dsimp only at hraw
    split at hraw
    · exact absurd hraw (by simp)
    · rename_i fs hfs
      obtain rfl : P = ⟨p.1, fs⟩ := (Option.some.inj hraw).symm
      exact ⟨p.1, p.2, hp', hfs, rfl⟩

omit model in
/-- Elementwise consequence of a successful whole-table `mapM id`: every slot
was filled, with the function the finished program records. -/
theorem funcs_mapM_getElem? {a : Array (Option Func)} {fs : Array Func}
    (h : a.mapM id = some fs) {i : Nat} {g : Func}
    (hi : a[i]? = some (some g)) : fs[i]? = some g := by
  have hlist : a.toList.mapM id = some fs.toList := by
    have := congrArg (Option.map Array.toList) h
    simpa [Array.mapM_eq_mapM_toList, Option.map_some] using this
  have : ∀ (l : List (Option Func)) (l' : List Func), l.mapM id = some l' →
      ∀ (j : Nat) (x : Func), l[j]? = some (some x) → l'[j]? = some x := by
    intro l
    induction l with
    | nil => intro l' hl j x hj; exact absurd hj (by simp)
    | cons o l ih =>
      intro l' hl j x hj
      rw [List.mapM_cons] at hl
      cases o with
      | none => exact absurd hl (by simp)
      | some y =>
        rcases ht : l.mapM id with _ | t <;> rw [ht] at hl
        · exact absurd hl (by simp)
        · obtain rfl : l' = y :: t := by simpa using hl.symm
          cases j with
          | zero => simpa using hj
          | succ j => simpa using ih t ht j x (by simpa using hj)
  have := this a.toList fs.toList hlist i g (by simpa using hi)
  simpa using this

/-- A builder function table is *complete for* `P` when every allocated slot
has been filled and erasing the `Option` layer gives exactly `P.funcs`.

This is deliberately a fact about one fixed, completed table rather than the
table of each intermediate builder state.  `allocScope` reserves all of a
scope's slots before its statement walk fills them, and `trFunc` may reserve
further slots while outer ones are still pending.  The construction simulation
therefore keeps the eventual completed table fixed across every recursive IH;
the hoist/call bridges only have to prove that their filled slots survive into
that table. -/
def FuncTableComplete (P : Prog) (done : Array (Option Func)) : Prop :=
  done.mapM id = some P.funcs

omit model in
theorem FuncTableComplete.get {P : Prog} {done : Array (Option Func)}
    (h : FuncTableComplete P done) {i : Nat} {g : Func}
    (hi : done[i]? = some (some g)) : P.funcs[i]? = some g :=
  funcs_mapM_getElem? h hi

omit model in
/-- A completed table has no pending reservations, hence owns the empty
budget.  This is the top-level instantiation of the slot-ownership invariant. -/
theorem FuncTableComplete.owned_nil {P : Prog} {done : Array (Option Func)}
    (h : FuncTableComplete P done) : FOwned [] { fn := {}, funcs := done }
      { fn := {}, funcs := done } := by
  apply FOwned.rfl_of_no_pending
  intro i hi
  have hlist : done.toList.mapM id = some P.funcs.toList := by
    have hm := congrArg (Option.map Array.toList) h
    simpa [Array.mapM_eq_mapM_toList, Option.map_some] using hm
  have noNone : ∀ (l : List (Option Func)) (fs : List Func),
      l.mapM id = some fs → ∀ j : Nat, l[j]? ≠ some none := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
      intro fs hm j
      rw [List.mapM_cons] at hm
      cases x with
      | none => simp at hm
      | some g =>
        cases ht : xs.mapM id with
        | none => rw [ht] at hm; simp at hm
        | some gs =>
          rw [ht] at hm
          obtain rfl : fs = g :: gs := by simpa using hm.symm
          cases j with
          | zero => simp
          | succ j => simpa using ih gs ht j
  exact noNone done.toList P.funcs.toList hlist i (by simpa using hi)

/-- Package the function-table half of `FuncOK` once the structural hoist walk
has shown that the translated function and every nested function it allocated
survive into the fixed completed table. -/
theorem FuncTableComplete.funcOK {P : Prog} {done : Array (Option Func)}
    (h : FuncTableComplete P done) {fenv : FMap}
    {decl : YulSemantics.FDecl yulD} {fid : FuncId} {g : Func}
    {s₀ s₁ : BState}
    (htr : trFunc fenv decl.params decl.rets decl.body s₀ = some (g, s₁))
    (hslot : done[fid]? = some (some g))
    (hnested : ∀ (i : Nat) (g' : Func),
      s₁.funcs[i]? = some (some g') → done[i]? = some (some g')) :
    FuncOK (model := model) P fenv decl fid :=
  ⟨g, s₀, s₁, h.get hslot, htr,
    fun i g' hi => h.get (hnested i g' hi)⟩

/-- Content refinement is the local-to-final transport consumed by hoisted
scope construction: once the just-filled declaration slot and every nested
slot are present in a local builder table, `FContents` moves them to the one
completed table and `FuncTableComplete` erases the `Option` layer. -/
theorem FuncTableComplete.funcOK_of_contents {P : Prog}
    {done : Array (Option Func)} (h : FuncTableComplete P done)
    {fenv : FMap} {decl : YulSemantics.FDecl yulD} {fid : FuncId}
    {g : Func} {s₀ s₁ sLocal sDone : BState}
    (htr : trFunc fenv decl.params decl.rets decl.body s₀ = some (g, s₁))
    (hslot : sLocal.funcs[fid]? = some (some g))
    (hnested : ∀ (i : Nat) (g' : Func),
      s₁.funcs[i]? = some (some g') → sLocal.funcs[i]? = some (some g'))
    (href : FContents sLocal sDone) (hdone : sDone.funcs = done) :
    FuncOK (model := model) P fenv decl fid := by
  apply h.funcOK htr
  · rw [← hdone]
    exact href fid g hslot
  · intro i g' hi
    rw [← hdone]
    exact href i g' (hnested i g' hi)

omit model in
theorem stmtFuncIds_mem {fenv : FMap} {ss : List (Stmt Op)}
    {n : Ident} {ps rs : List Ident} {body : List (Stmt Op)}
    (hmem : Stmt.funDef n ps rs body ∈ ss) :
    (fenv.get n).toList ⊆ stmtFuncIds fenv ss := by
  induction ss with
  | nil => simp at hmem
  | cons st rest ih =>
    cases st with
    | funDef n' ps' rs' body' =>
      simp only [List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · cases heq
        simpa [stmtFuncIds]
      · exact fun i hi => by
          simp only [stmtFuncIds, List.mem_append]
          exact Or.inr (ih hmem hi)
    | block b | letDecl ps' e | assign ps' e | cond e b
    | forLoop b e post body' | «break» | «continue» | leave
    | switch e cases dflt | exprStmt e =>
      simp only [List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · cases heq
      · simpa only [stmtFuncIds] using ih hmem

theorem stmtFuncIds_length_of_trStmts (fenv : FMap) (env : VMap)
    (lctx : Option LoopCtx) (rets : Option (List Ident)) (d : Bool) :
    ∀ (ss : List (Stmt Op)) (s s' : BState) (r : Option VMap),
      trStmts fenv env lctx rets d ss s = some (r, s') →
      (stmtFuncIds fenv ss).length = (YulSemantics.hoist yulD ss).length := by
  intro ss
  induction ss generalizing env d with
  | nil => intro s s' r _; rfl
  | cons st rest ih =>
    intro s s' r htr
    cases st with
    | funDef n ps rs body =>
      rw [trStmts] at htr
      obtain ⟨fid, s1, h1, htr⟩ := M.bind_inv htr
      obtain ⟨g, s2, h2, htr⟩ := M.bind_inv htr
      obtain ⟨u, s3, h3, htail⟩ := M.bind_inv htr
      obtain ⟨hget, -⟩ := M.liftO_inv h1
      have hh := congrArg Nat.succ (ih env d s3 s' r htail)
      simpa [stmtFuncIds, hget, YulSemantics.hoist, Nat.add_comm] using hh
    | block b | letDecl ps e | assign ps e | cond e b
    | forLoop b e post body | «break» | «continue» | leave
    | switch e cases dflt | exprStmt e =>
      simp only [stmtFuncIds, YulSemantics.hoist, List.filterMap_cons]
      rw [trStmts] at htr
      · split at htr
        · exact ih env true s s' r htr
        · obtain ⟨renv, s1, h1, h2⟩ := M.bind_inv htr
          cases renv with
          | none => exact ih env true s1 s' r h2
          | some env' => exact ih env' false s1 s' r h2
      · intro n ps rs body heq
        cases heq

theorem allocScope_length {ss : List (Stmt Op)} {s s' : BState}
    {scope : List (Ident × FuncId)} (h : allocScope ss s = some (scope, s')) :
    scope.length = (YulSemantics.hoist yulD ss).length := by
  rw [allocScope] at h
  have fold : ∀ (l : List (Stmt Op)) (acc : List (Ident × FuncId))
      (s0 s1 : BState) (out : List (Ident × FuncId)),
      (l.foldlM (init := acc) fun acc (st : Stmt Op) =>
        match st with
        | Stmt.funDef n _ _ _ => do
            let fid ← allocFunc
            pure (acc ++ [(n, fid)])
        | _ => pure acc) s0 = some (out, s1) →
      out.length = acc.length + (YulSemantics.hoist yulD l).length := by
    intro l
    induction l with
    | nil =>
      intro acc s0 s1 out hl
      obtain ⟨rfl, rfl⟩ := M.pure_inv hl
      simp [YulSemantics.hoist]
    | cons st rest ih =>
      intro acc s0 s1 out hl
      rw [List.foldlM_cons] at hl
      obtain ⟨acc', t, hst, hrest⟩ := M.bind_inv hl
      cases st with
      | funDef n ps rs body =>
        obtain ⟨fid, u, ha, hp⟩ := M.bind_inv hst
        obtain ⟨rfl, rfl⟩ := M.pure_inv hp
        have hh := ih (acc ++ [(n, fid)]) t s1 out hrest
        simp [YulSemantics.hoist] at *
        omega
      | block b | letDecl ps e | assign ps e | cond e b
      | forLoop b e post body | «break» | «continue» | leave
      | switch e cases dflt | exprStmt e =>
        obtain ⟨rfl, rfl⟩ := M.pure_inv hst
        simpa [YulSemantics.hoist] using ih _ _ _ _ hrest
  simpa using fold ss [] s s' scope h

theorem allocScope_forall2 {ss : List (Stmt Op)} {s s' : BState}
    {scope : List (Ident × FuncId)} (h : allocScope ss s = some (scope, s')) :
    List.Forall₂ (fun (p : Ident × YulSemantics.FDecl yulD)
      (q : Ident × FuncId) => p.1 = q.1)
      (YulSemantics.hoist yulD ss) scope := by
  rw [allocScope] at h
  have fold : ∀ (l : List (Stmt Op)) (acc : List (Ident × FuncId))
      (s0 s1 : BState) (out : List (Ident × FuncId)),
      (l.foldlM (init := acc) fun acc (st : Stmt Op) =>
        match st with
        | Stmt.funDef n _ _ _ => do
            let fid ← allocFunc
            pure (acc ++ [(n, fid)])
        | _ => pure acc) s0 = some (out, s1) →
      ∃ added, out = acc ++ added ∧
        List.Forall₂ (fun (p : Ident × YulSemantics.FDecl yulD)
          (q : Ident × FuncId) => p.1 = q.1)
          (YulSemantics.hoist yulD l) added := by
    intro l
    induction l with
    | nil =>
      intro acc s0 s1 out hl
      obtain ⟨rfl, rfl⟩ := M.pure_inv hl
      exact ⟨[], by simp [YulSemantics.hoist]⟩
    | cons st rest ih =>
      intro acc s0 s1 out hl
      rw [List.foldlM_cons] at hl
      obtain ⟨acc', t, hst, hrest⟩ := M.bind_inv hl
      cases st with
      | funDef n ps rs body =>
        obtain ⟨fid, u, ha, hp⟩ := M.bind_inv hst
        obtain ⟨rfl, rfl⟩ := M.pure_inv hp
        obtain ⟨added, hout, hrel⟩ := ih (acc ++ [(n, fid)]) t s1 out hrest
        refine ⟨(n, fid) :: added, ?_, ?_⟩
        · simpa [List.append_assoc] using hout
        · have hc : List.Forall₂
              (fun (p : Ident × YulSemantics.FDecl yulD)
                (q : Ident × FuncId) => p.1 = q.1)
              ((n, { params := ps, rets := rs, body := body }) ::
                YulSemantics.hoist yulD rest)
              ((n, fid) :: added) := .cons rfl hrel
          simpa [YulSemantics.hoist] using hc
      | block b | letDecl ps e | assign ps e | cond e b
      | forLoop b e post body | «break» | «continue» | leave
      | switch e cases dflt | exprStmt e =>
        obtain ⟨rfl, rfl⟩ := M.pure_inv hst
        obtain ⟨added, hout, hrel⟩ := ih _ _ _ _ hrest
        exact ⟨added, hout, by simpa [YulSemantics.hoist] using hrel⟩
  obtain ⟨added, hout, hrel⟩ := fold ss [] s s' scope h
  simpa using hout ▸ hrel

theorem mem_hoist_names {ss : List (Stmt Op)} {n : Ident}
    (h : n ∈ (YulSemantics.hoist yulD ss).map Prod.fst) :
    ∃ ps rs body, Stmt.funDef n ps rs body ∈ ss := by
  induction ss with
  | nil => simp [YulSemantics.hoist] at h
  | cons st rest ih =>
    cases st with
    | funDef n' ps rs body =>
      simp only [YulSemantics.hoist, List.filterMap_cons, List.map_cons,
        List.mem_cons] at h
      rcases h with h | h
      · exact ⟨ps, rs, body, by simp [h]⟩
      · obtain ⟨ps', rs', body', hm⟩ := ih h
        exact ⟨ps', rs', body', List.mem_cons_of_mem _ hm⟩
    | block b | letDecl ps e | assign ps e | cond e b
    | forLoop b e post body | «break» | «continue» | leave
    | switch e cases dflt | exprStmt e =>
      have hh : n ∈ (YulSemantics.hoist yulD rest).map Prod.fst := by
        simpa [YulSemantics.hoist] using h
      obtain ⟨ps', rs', body', hm⟩ := ih hh
      exact ⟨ps', rs', body', List.mem_cons_of_mem _ hm⟩

theorem hoist_names_nodup_of_stmtFuncIds (fenv : FMap) (env : VMap)
    (lctx : Option LoopCtx) (rets : Option (List Ident)) (d : Bool) :
    ∀ (ss : List (Stmt Op)) (s s' : BState) (r : Option VMap),
      (stmtFuncIds fenv ss).Nodup →
      trStmts fenv env lctx rets d ss s = some (r, s') →
      ((YulSemantics.hoist yulD ss).map Prod.fst).Nodup := by
  intro ss
  induction ss generalizing env d with
  | nil => intro s s' r _ _; simp [YulSemantics.hoist]
  | cons st rest ih =>
    intro s s' r hnd htr
    cases st with
    | funDef n ps rs body =>
      rw [trStmts] at htr
      obtain ⟨fid, s1, h1, htr⟩ := M.bind_inv htr
      obtain ⟨g, s2, h2, htr⟩ := M.bind_inv htr
      obtain ⟨u, s3, h3, htail⟩ := M.bind_inv htr
      obtain ⟨hget, -⟩ := M.liftO_inv h1
      simp only [stmtFuncIds, hget, Option.toList_some,
        List.singleton_append] at hnd
      have hndTail := (List.nodup_cons.mp hnd).2
      have hnmem : n ∉ (YulSemantics.hoist yulD rest).map Prod.fst := by
        intro hn
        obtain ⟨ps', rs', body', hm⟩ := mem_hoist_names hn
        apply (List.nodup_cons.mp hnd).1
        apply stmtFuncIds_mem hm
        simp [hget]
      simpa [YulSemantics.hoist] using
        (List.nodup_cons.mpr ⟨hnmem, ih env d s3 s' r hndTail htail⟩)
    | block b | letDecl ps e | assign ps e | cond e b
    | forLoop b e post body | «break» | «continue» | leave
    | switch e cases dflt | exprStmt e =>
      simp only [stmtFuncIds] at hnd
      rw [trStmts] at htr
      · split at htr
        · simpa [YulSemantics.hoist] using ih env true s s' r hnd htr
        · obtain ⟨renv, s1, h1, h2⟩ := M.bind_inv htr
          cases renv with
          | none => simpa [YulSemantics.hoist] using ih env true s1 s' r hnd h2
          | some env' =>
            simpa [YulSemantics.hoist] using ih env' false s1 s' r hnd h2
      · intro n ps rs body heq
        cases heq

omit model in
theorem allocScope_slots {ss : List (Stmt Op)} {s s' : BState}
    {scope : List (Ident × FuncId)} (h : allocScope ss s = some (scope, s')) :
    (scope.map Prod.snd).Nodup ∧
      ∀ i : FuncId, i ∈ scope.map Prod.snd →
        s.funcs.size ≤ i ∧ s'.funcs[i]? = some none := by
  rw [allocScope] at h
  have fold : ∀ (l : List (Stmt Op)) (acc : List (Ident × FuncId))
      (s0 s1 : BState) (out : List (Ident × FuncId)) (base : Nat),
      base ≤ s0.funcs.size →
      (acc.map Prod.snd).Nodup →
      (∀ i : FuncId, i ∈ acc.map Prod.snd →
        base ≤ i ∧ s0.funcs[i]? = some none) →
      (l.foldlM (init := acc) fun acc (st : Stmt Op) =>
        match st with
        | Stmt.funDef n _ _ _ => do
            let fid ← allocFunc
            pure (acc ++ [(n, fid)])
        | _ => pure acc) s0 = some (out, s1) →
      (out.map Prod.snd).Nodup ∧
        ∀ i : FuncId, i ∈ out.map Prod.snd →
          base ≤ i ∧ s1.funcs[i]? = some none := by
    intro l
    induction l with
    | nil =>
      intro acc s0 s1 out base _ hnd hslots hl
      obtain ⟨rfl, rfl⟩ := M.pure_inv hl
      exact ⟨hnd, hslots⟩
    | cons st rest ih =>
      intro acc s0 s1 out base hbase hnd hslots hl
      rw [List.foldlM_cons] at hl
      obtain ⟨acc', t, hst, hrest⟩ := M.bind_inv hl
      cases st with
      | funDef n ps rs body =>
        obtain ⟨fid, u, ha, hp⟩ := M.bind_inv hst
        rw [M.allocFunc_apply] at ha
        obtain ⟨rfl, rfl⟩ := M.some_pair_inj ha
        obtain ⟨rfl, rfl⟩ := M.pure_inv hp
        have hnot : s0.funcs.size ∉ acc.map Prod.snd := by
          intro hm
          exact Nat.ne_of_lt (lt_size_of_getElem? (hslots _ hm).2) rfl
        have hnd' : ((acc ++ [(n, s0.funcs.size)]).map Prod.snd).Nodup := by
          rw [List.map_append]
          simp only [List.map_singleton]
          rw [List.nodup_append]
          refine ⟨hnd, by simp, ?_⟩
          intro a ha b hb
          simp only [List.mem_singleton] at hb
          subst b
          exact fun he => hnot (he ▸ ha)
        have hslots' : ∀ i : FuncId,
            i ∈ (acc ++ [(n, s0.funcs.size)]).map Prod.snd →
            base ≤ i ∧ (s0.funcs.push none)[i]? = some none := by
          intro i hi
          simp only [List.map_append, List.map_singleton, List.mem_append,
            List.mem_singleton] at hi
          rcases hi with hi | rfl
          · refine ⟨(hslots i hi).1, ?_⟩
            rw [Array.getElem?_push, if_neg]
            · exact (hslots i hi).2
            · exact Nat.ne_of_lt (lt_size_of_getElem? (hslots i hi).2)
          · exact ⟨hbase, by simp⟩
        exact ih (acc ++ [(n, s0.funcs.size)]) _ s1 out base
          (Nat.le_trans hbase (by simp)) hnd' hslots' hrest
      | block b | letDecl ps e | assign ps e | cond e b
      | forLoop b e post body | «break» | «continue» | leave
      | switch e cases dflt | exprStmt e =>
        obtain ⟨rfl, rfl⟩ := M.pure_inv hst
        exact ih _ _ _ _ base hbase hnd hslots hrest
  exact fold ss [] s s' scope s.funcs.size (Nat.le_refl _) (by simp) (by simp) h

theorem allocScope_stmtFuncIds_perm {fenv : FMap} {env : VMap}
    {lctx : Option LoopCtx} {rets : Option (List Ident)} {d : Bool}
    {ss : List (Stmt Op)} {s0 sA s1 done : BState}
    {scope : List (Ident × FuncId)} {r : Option VMap}
    {owned : List FuncId}
    (hbound : ∀ i : FuncId, i ∈ owned → i < s0.funcs.size)
    (ha : allocScope ss s0 = some (scope, sA))
    (ht : trStmts (scope :: fenv) env lctx rets d ss sA = some (r, s1))
    (ho1 : FOwned owned s1 done) :
    (stmtFuncIds (scope :: fenv) ss).Perm (scope.map Prod.snd) := by
  let selected := stmtFuncIds (scope :: fenv) ss
  let slots := scope.map Prod.snd
  have hraw := allocScope_slots ha
  have hndSlots : slots.Nodup := hraw.1
  have hsub : slots ⊆ selected := by
    intro i hi
    by_contra hnot
    have hiA : sA.funcs[i]? = some none := (hraw.2 i hi).2
    have hskip : ∀ (n : Ident) (ps rs : List Ident)
        (body : List (Stmt Op)),
        Stmt.funDef n ps rs body ∈ ss → FMap.get (scope :: fenv) n ≠ some i := by
      intro n ps rs body hmem hget
      apply hnot
      apply stmtFuncIds_mem hmem
      simp [hget]
    have hi1 : s1.funcs[i]? = some none :=
      trStmts_pending_survives (scope :: fenv) env lctx rets d
        ss sA s1 r i hiA hskip ht
    have hio : i ∈ owned := (ho1.pending i).mpr hi1
    exact Nat.not_lt_of_ge (hraw.2 i hi).1 (hbound i hio)
  have hlen : selected.length = slots.length := by
    dsimp [selected, slots]
    rw [List.length_map, stmtFuncIds_length_of_trStmts
      (scope :: fenv) env lctx rets d ss sA s1 r ht,
      ← allocScope_length ha]
  have hs : slots.Subperm selected := hndSlots.subperm hsub
  exact (hs.perm_of_length_le hlen.le).symm

theorem forall2_hoist_scope_names
    {as : List (Ident × YulSemantics.FDecl yulD)}
    {bs : List (Ident × FuncId)}
    (h : List.Forall₂ (fun p q => p.1 = q.1) as bs) :
    as.map Prod.fst = bs.map Prod.fst := by
  induction h with
  | nil => rfl
  | cons hh ht ih => simp [hh, ih]

omit model in
private theorem find?_scope_suffix_nodup {top : List (Ident × FuncId)}
    {n : Ident} {fid : FuncId} {tl : List (Ident × FuncId)}
    (hnd : (top.map Prod.fst).Nodup)
    (hsuf : (n, fid) :: tl <:+ top) :
    top.find? (fun q => q.1 = n) = some (n, fid) := by
  obtain ⟨pre, hpre⟩ := hsuf
  subst hpre
  have hnp : n ∉ pre.map Prod.fst := by
    rw [List.map_append, List.map_cons] at hnd
    exact fun hm => (List.nodup_append.mp hnd).2.2 n hm n (by simp) rfl
  clear hnd
  induction pre with
  | nil => simp
  | cons a pre ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hnp
    rw [List.cons_append, List.find?_cons_of_neg (by
      simp only [decide_eq_true_eq]
      exact fun he => hnp.1 he.symm)]
    exact ih hnp.2

theorem trStmts_hoist_owned {P : Prog}
    {doneFuncs : Array (Option Func)}
    (hfuncs : FuncTableComplete P doneFuncs)
    {done : BState} (hdone : done.funcs = doneFuncs)
    {top : List (Ident × FuncId)} {fenv : FMap}
    (htop : (top.map Prod.fst).Nodup) :
    ∀ (ss : List (Stmt Op)) (rem : List (Ident × FuncId))
      (env : VMap) (lctx : Option LoopCtx) (rets : Option (List Ident))
      (d : Bool) (s s' : BState) (r : Option VMap) (owned : List FuncId),
      List.Forall₂ (fun (p : Ident × YulSemantics.FDecl yulD)
        (q : Ident × FuncId) => p.1 = q.1)
        (YulSemantics.hoist yulD ss) rem →
      rem <:+ top →
      (∀ i : FuncId, i ∈ rem.map Prod.snd → s.funcs[i]? = some none) →
      (∀ i : FuncId, i ∈ rem.map Prod.snd ++ owned →
        i < s.funcs.size) →
      (rem.map Prod.snd ++ owned).Nodup →
      FOwned owned s' done →
      trStmts (top :: fenv) env lctx rets d ss s = some (r, s') →
      List.Forall₂
        (fun (p : Ident × YulSemantics.FDecl yulD) (q : Ident × FuncId) =>
          p.1 = q.1 ∧ FuncOK (model := model) P (top :: fenv) p.2 q.2)
        (YulSemantics.hoist yulD ss) rem
        ∧ FOwned (rem.map Prod.snd ++ owned) s done := by
  intro ss
  induction ss with
  | nil =>
    intro rem env lctx rets d s s' r owned hrel _ _ _ hnd ho htr
    cases hrel
    rw [trStmts] at htr
    obtain ⟨-, rfl⟩ := M.pure_inv htr
    exact ⟨List.Forall₂.nil, by simpa using ho⟩
  | cons st rest ih =>
    intro rem env lctx rets d s s' r owned hrel hsuf hslots hbound hnd ho htr
    cases st with
    | funDef n ps rs body =>
      cases hrel with
      | cons hname hrelTail =>
        rename_i q remTail
        obtain ⟨qn, qfid⟩ := q
        dsimp only at hname
        subst qn
        have hsufHead : (n, qfid) :: remTail <:+ top := hsuf
        have hfind := find?_scope_suffix_nodup htop hsufHead
        have hget : FMap.get (top :: fenv) n = some qfid := by
          rw [FMap.get, hfind]
          rfl
        rw [trStmts] at htr
        obtain ⟨fid, s1, h1, htr⟩ := M.bind_inv htr
        obtain ⟨g, s2, h2, htr⟩ := M.bind_inv htr
        obtain ⟨u, s3, h3, htail⟩ := M.bind_inv htr
        obtain ⟨hget1, hs1⟩ := M.liftO_inv h1
        have hfidEq : fid = qfid := Option.some.inj (hget1.symm.trans hget)
        subst fid
        subst s1
        have hp := trFunc_prefix (top :: fenv) ps rs body h2
        have hq0 : s.funcs[qfid]? = some none := hslots qfid (by simp)
        have hq2 : s2.funcs[qfid]? = some none := by
          rw [hp qfid (lt_size_of_getElem? hq0)]
          exact hq0
        obtain ⟨hqLt, hs3⟩ := M.fillFunc_inv h3
        have hndTail : (remTail.map Prod.snd ++ owned).Nodup := by
          simpa using (List.nodup_cons.mp (by simpa using hnd)).2
        have hqNot : qfid ∉ remTail.map Prod.snd ++ owned :=
          (List.nodup_cons.mp (by simpa using hnd)).1
        have hslotsTail : ∀ i : FuncId, i ∈ remTail.map Prod.snd →
            s3.funcs[i]? = some none := by
          intro i hi
          have hi0 := hslots i (by simp [hi])
          have hi2 : s2.funcs[i]? = some none := by
            rw [hp i (lt_size_of_getElem? hi0)]
            exact hi0
          have hine : i ≠ qfid := by
            intro he
            subst i
            exact hqNot (List.mem_append_left _ hi)
          rw [hs3, Array.getElem?_set (h := hqLt), if_neg (Ne.symm hine)]
          exact hi2
        have hboundTail : ∀ i : FuncId, i ∈ remTail.map Prod.snd ++ owned →
            i < s3.funcs.size := by
          intro i hi
          have hi0 : i < s.funcs.size := hbound i (by simp [hi])
          have hsizes : s.funcs.size ≤ s2.funcs.size := hp.size (Nat.le_refl _)
          rw [hs3]
          simpa using Nat.lt_of_lt_of_le hi0 hsizes
        have hsufTail : remTail <:+ top := (List.suffix_cons _ _).trans hsufHead
        obtain ⟨hrelOut, ho3⟩ := ih remTail env lctx rets d s3 s' r owned
          hrelTail hsufTail hslotsTail hboundTail hndTail ho htail
        have hslot3 : s3.funcs[qfid]? = some (some g) := by
          rw [hs3]
          simp
        have hfillContents : FContents s2 s3 :=
          FContents.of_fillFunc_empty hq2 h3
        have hok : FuncOK (model := model) P (top :: fenv)
            { params := ps, rets := rs, body := body } qfid := by
          apply hfuncs.funcOK_of_contents h2 hslot3
          · intro i g' hi
            exact hfillContents i g' hi
          · exact ho3.filled
          · exact hdone
        have ho2 : FOwned (qfid :: (remTail.map Prod.snd ++ owned)) s2 done :=
          FOwned.back_fillFunc hq2 h3 ho3
        have hbound2 : ∀ i : FuncId,
            i ∈ qfid :: (remTail.map Prod.snd ++ owned) → i < s.funcs.size := by
          intro i hi
          exact hbound i (by simpa using hi)
        have ho0 := FOwned.back_fprefix hp hbound2 ho2
        refine ⟨?_, ?_⟩
        · exact .cons ⟨rfl, hok⟩ hrelOut
        · simpa using ho0
    | block body | letDecl vars val | assign vars e | cond e body
    | forLoop init e post body | «break» | «continue» | leave
    | switch e cases dflt | exprStmt e =>
      simp only [YulSemantics.hoist, List.filterMap_cons] at hrel
      rw [trStmts] at htr
      · split at htr
        · exact ih rem env lctx rets true s s' r owned hrel hsuf hslots
            hbound hnd ho htr
        · obtain ⟨renv, s1, h1, h2⟩ := M.bind_inv htr
          have hp := trStmt_fprefix (top :: fenv) env lctx rets _ s.funcs.size
            s renv s1 (Nat.le_refl _) h1
          have hslots1 : ∀ i : FuncId, i ∈ rem.map Prod.snd →
              s1.funcs[i]? = some none := by
            intro i hi
            rw [hp i (hbound i (List.mem_append_left _ hi))]
            exact hslots i hi
          have hbound1 : ∀ i : FuncId, i ∈ rem.map Prod.snd ++ owned →
              i < s1.funcs.size := by
            intro i hi
            exact Nat.lt_of_lt_of_le (hbound i hi) (hp.size (Nat.le_refl _))
          cases renv with
          | none =>
            obtain ⟨hrelOut, ho1⟩ := ih rem env lctx rets true s1 s' r owned
              hrel hsuf hslots1 hbound1 hnd ho h2
            exact ⟨hrelOut, FOwned.back_fprefix hp hbound ho1⟩
          | some env' =>
            obtain ⟨hrelOut, ho1⟩ := ih rem env' lctx rets false s1 s' r owned
              hrel hsuf hslots1 hbound1 hnd ho h2
            exact ⟨hrelOut, FOwned.back_fprefix hp hbound ho1⟩
      · intro n ps rs body heq
        cases heq

/-- Relate `allocScope`'s fresh reservations to the declarations selected by
`trStmts`, reconstruct the caller's pending-slot ownership, and realize the
hoisted semantic scope in the completed function table. -/
theorem allocScope_bridge {P : Prog}
    {doneFuncs : Array (Option Func)}
    (hfuncs : FuncTableComplete P doneFuncs)
    {funs : YulSemantics.FunEnv yulD} {fenv : FMap}
    (hfe : FEnvOK (model := model) P funs fenv)
    {env : VMap} {lctx : Option LoopCtx} {rets : Option (List Ident)} {d : Bool}
    {ss : List (Stmt Op)} {s0 sA s1 done : BState}
    {scope : List (Ident × FuncId)} {r : Option VMap}
    {owned : List FuncId}
    (hdone : done.funcs = doneFuncs)
    (hbound : ∀ i : FuncId, i ∈ owned → i < s0.funcs.size)
    (ho1 : FOwned owned s1 done)
    (ha : allocScope ss s0 = some (scope, sA))
    (ht : trStmts (scope :: fenv) env lctx rets d ss sA = some (r, s1)) :
    FEnvOK (model := model) P (YulSemantics.hoist yulD ss :: funs)
      (scope :: fenv) ∧ FOwned owned s0 done := by
  let selected := stmtFuncIds (scope :: fenv) ss
  let slots := scope.map Prod.snd
  have hraw := allocScope_slots ha
  have hperm : selected.Perm slots :=
    allocScope_stmtFuncIds_perm hbound ha ht ho1
  have hndSlots : slots.Nodup := hraw.1
  have hndSelected : (stmtFuncIds (scope :: fenv) ss).Nodup :=
    hperm.nodup_iff.mpr hndSlots
  have hndHoist := hoist_names_nodup_of_stmtFuncIds
    (scope :: fenv) env lctx rets d ss sA s1 r hndSelected ht
  have hrel := allocScope_forall2 ha
  have hnames : (YulSemantics.hoist yulD ss).map Prod.fst =
      scope.map Prod.fst := forall2_hoist_scope_names hrel
  have hndNames : (scope.map Prod.fst).Nodup := by rwa [← hnames]
  have hslots : ∀ i : FuncId, i ∈ scope.map Prod.snd →
      sA.funcs[i]? = some none := fun i hi => (hraw.2 i hi).2
  have hslotsSelected : ∀ i : FuncId,
      i ∈ stmtFuncIds (scope :: fenv) ss → sA.funcs[i]? = some none := by
    intro i hi
    exact hslots i (hperm.mem_iff.mp hi)
  have hsizeA : s0.funcs.size ≤ sA.funcs.size := (allocScope_funcsOnly ha).2
  have hboundSelected : ∀ i : FuncId,
      i ∈ stmtFuncIds (scope :: fenv) ss ++ owned → i < sA.funcs.size := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact lt_size_of_getElem? (hslotsSelected i hi)
    · exact Nat.lt_of_lt_of_le (hbound i hi) hsizeA
  have hndAll : (stmtFuncIds (scope :: fenv) ss ++ owned).Nodup := by
    rw [List.nodup_append]
    refine ⟨hndSelected, ho1.nodup, ?_⟩
    intro i hi j hj heq
    subst j
    have hislot : i ∈ slots := hperm.mem_iff.mp hi
    exact Nat.not_lt_of_ge (hraw.2 i hislot).1 (hbound i hj)
  have hoSelected := trStmts_owned_back (scope :: fenv) lctx rets ss env d
    sA s1 done r owned hboundSelected hslotsSelected hndAll ho1 ht
  have hoScope : FOwned (scope.map Prod.snd ++ owned) sA done :=
    FOwned.perm (hperm.append_right owned) hoSelected
  have hboundScope : ∀ i : FuncId, i ∈ scope.map Prod.snd ++ owned →
      i < sA.funcs.size := by
    intro i hi
    exact lt_size_of_getElem? ((hoScope.pending i).mp hi)
  obtain ⟨hrelOK, -⟩ := trStmts_hoist_owned hfuncs hdone hndNames
    ss scope env lctx rets d sA s1 r owned hrel (List.suffix_refl _)
      hslots hboundScope hoScope.nodup ho1 ht
  have hoAlloc : FOwned (owned ++ scope.map Prod.snd) sA done :=
    FOwned.perm List.perm_append_comm hoScope
  have ho0 : FOwned owned s0 done := FOwned.back_allocScope ha hoAlloc
  exact ⟨FEnvOK.cons hrelOK hfe, ho0⟩

/-- The exact initializer premises consumed by the statement-list clause of
`Motive`, reconstructed from an enclosing `allocScope` and the completed
function table. -/
theorem allocScope_motive_inputs {P : Prog}
    {doneFuncs : Array (Option Func)}
    (hfuncs : FuncTableComplete P doneFuncs)
    {funs : YulSemantics.FunEnv yulD} {fenv : FMap}
    (hfe : FEnvOK (model := model) P funs fenv)
    {env : VMap} {lctx : Option LoopCtx} {rets : Option (List Ident)} {d : Bool}
    {ss : List (Stmt Op)} {s0 sA s1 done : BState}
    {scope : List (Ident × FuncId)} {r : Option VMap}
    {owned : List FuncId}
    (hdone : done.funcs = doneFuncs)
    (hbound : ∀ i : FuncId, i ∈ owned → i < s0.funcs.size)
    (ho1 : FOwned owned s1 done)
    (ha : allocScope ss s0 = some (scope, sA))
    (ht : trStmts (scope :: fenv) env lctx rets d ss sA = some (r, s1)) :
    FEnvOK (model := model) P (YulSemantics.hoist yulD ss :: funs)
        (scope :: fenv)
      ∧ (∀ i : FuncId, i ∈ stmtFuncIds (scope :: fenv) ss ++ owned →
          i < sA.funcs.size)
      ∧ (∀ i : FuncId, i ∈ stmtFuncIds (scope :: fenv) ss →
          sA.funcs[i]? = some none)
      ∧ (stmtFuncIds (scope :: fenv) ss ++ owned).Nodup
      ∧ FOwned owned s0 done := by
  let selected := stmtFuncIds (scope :: fenv) ss
  let slots := scope.map Prod.snd
  have hraw := allocScope_slots ha
  have hperm : selected.Perm slots :=
    allocScope_stmtFuncIds_perm hbound ha ht ho1
  have hslots : ∀ i : FuncId, i ∈ scope.map Prod.snd →
      sA.funcs[i]? = some none := fun i hi => (hraw.2 i hi).2
  have hslotsSelected : ∀ i : FuncId,
      i ∈ stmtFuncIds (scope :: fenv) ss → sA.funcs[i]? = some none := by
    intro i hi
    exact hslots i (hperm.mem_iff.mp hi)
  have hsizeA : s0.funcs.size ≤ sA.funcs.size := (allocScope_funcsOnly ha).2
  have hboundSelected : ∀ i : FuncId,
      i ∈ stmtFuncIds (scope :: fenv) ss ++ owned → i < sA.funcs.size := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact lt_size_of_getElem? (hslotsSelected i hi)
    · exact Nat.lt_of_lt_of_le (hbound i hi) hsizeA
  have hndSelected : (stmtFuncIds (scope :: fenv) ss).Nodup :=
    hperm.nodup_iff.mpr hraw.1
  have hndAll : (stmtFuncIds (scope :: fenv) ss ++ owned).Nodup := by
    rw [List.nodup_append]
    refine ⟨hndSelected, ho1.nodup, ?_⟩
    intro i hi j hj heq
    subst j
    have hislot : i ∈ slots := hperm.mem_iff.mp hi
    exact Nat.not_lt_of_ge (hraw.2 i hislot).1 (hbound i hj)
  obtain ⟨hfe', ho0⟩ := allocScope_bridge hfuncs hfe hdone hbound ho1 ha ht
  exact ⟨hfe', hboundSelected, hslotsSelected, hndAll, ho0⟩

/-! ## The residual obligation

Everything above is unconditional. What remains is the derivation induction
itself: a single `induction … with` over the source `Step` derivation whose
motive is `SOut` below, mirroring `SimAsm.sim`'s `Motive`. -/

/-- What a statement-class source derivation means on the SSA side, by outcome
— the SSA analogue of `SimAsm.SOut`. `normal` hands back the register file the
fragment ends with (an extension of the one it started with, by single
assignment) together with the environment correspondence; the non-local
outcomes hand back the values their edge carries and consume any continuation
of the target block. -/
def SOut (P : Prog) (f : Func) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (s₀ s₁ : BState) (R₀ : Regs)
    (renv : Option VMap) (V' : VEnv yulD) (yst yst' : EvmState) (o : Outcome) :
    Prop :=
  match o with
  | .normal => ∃ (env' : VMap) (R₁ : Regs),
      renv = some env' ∧ Regs.Le R₀ R₁
        ∧ Regs.BelowEq s₀.fn.nextVal R₀ R₁ ∧ RegsFresh R₁ s₁.fn
        ∧ EnvOK (model := model) env' V' R₁
        ∧ env'.Unique
        ∧ SimS (model := model) P f s₀.fn R₀ yst s₁.fn R₁ yst'
  | .halt => ExecFrom (model := model) P f s₀.fn R₀ yst (.halt yst')
  | .break => ∃ (lc : LoopCtx) (R₁ : Regs) (vals : List U256),
      lctx = some lc ∧ Regs.Le R₀ R₁
        ∧ Regs.BelowEq s₀.fn.nextVal R₀ R₁ ∧ RegsFresh R₁ s₁.fn
        ∧ List.Forall₂ (fun x v => YulSemantics.VEnv.get V' x = some v) lc.vars vals
        ∧ ∀ res, JumpTo (model := model) P f lc.brkTgt vals R₁ yst' res
            → ExecFrom (model := model) P f s₀.fn R₀ yst res
  | .continue => ∃ (lc : LoopCtx) (R₁ : Regs) (vals : List U256),
      lctx = some lc ∧ Regs.Le R₀ R₁
        ∧ Regs.BelowEq s₀.fn.nextVal R₀ R₁ ∧ RegsFresh R₁ s₁.fn
        ∧ List.Forall₂ (fun x v => YulSemantics.VEnv.get V' x = some v) lc.vars vals
        ∧ ∀ res, JumpTo (model := model) P f lc.contTgt vals R₁ yst' res
            → ExecFrom (model := model) P f s₀.fn R₀ yst res
  | .leave => ∃ (rs : List Ident) (vals : List U256),
      rets = some rs
        ∧ List.Forall₂ (fun x v => YulSemantics.VEnv.get V' x = some v) rs vals
        ∧ ExecFrom (model := model) P f s₀.fn R₀ yst (.ret vals yst')

/-! ## The `modStmts` over-approximation

A statement list only changes the *outer* bindings its `modStmts` analysis
names. This is exactly what licenses `trStmt`'s `cond`, `switch` and `forLoop`
cases to thread only `modifiedX env bodies` through their join / header / exit
block parameters and to keep the *old* `ValId` for every other variable: SSA
registers persist across blocks, so an unreported variable's existing id still
holds its value. Missing names would be unsound; extra ones are harmless,
because then both incoming edges pass the same value. -/

omit model in
theorem modifiedX_mem_names {env : VMap} {bodies : List (List (Stmt Op))}
    {x : Ident} (h : x ∈ modifiedX env bodies) : x ∈ env.map Prod.fst := by
  simp only [modifiedX] at h
  exact List.mem_eraseDups.mp (List.mem_filter.mp h).1

omit model in
theorem modifiedX_nodup {env : VMap} (h : env.Unique)
    (bodies : List (List (Stmt Op))) : (modifiedX env bodies).Nodup := by
  rw [modifiedX, VMap.eraseDups_names_eq_self h]
  exact h.filter _

omit model in
theorem mem_modifiedX {env : VMap}
    {bodies : List (List (Stmt Op))} {x : Ident}
    (henv : x ∈ env.map Prod.fst) (hmod : x ∈ bodies.flatMap (modStmts [])) :
    x ∈ modifiedX env bodies := by
  simp only [modifiedX, List.mem_filter]
  exact ⟨List.mem_eraseDups.mpr henv, by simpa using hmod⟩

/-- Every name the enclosing statement list has declared so far is bound within
the innermost `locals.length` entries — the invariant `modStmts` threads through
its `letDecl` case, and the reason its `filter` may drop a name without lying:
a `set` to such a name reaches the inner binding, which the enclosing `restore`
drops. Stated as a *set* condition, because a list's declarations reach the
environment in reverse group order. -/
def LocalsOK (locals : List Ident) (V : VEnv yulD) : Prop :=
  ∀ x ∈ locals, x ∈ VEnv.names (V.take locals.length)

@[simp] theorem localsOK_nil (V : VEnv yulD) : LocalsOK [] V := by
  intro x hx; simp at hx

theorem names_take (V : VEnv yulD) (k : Nat) :
    VEnv.names (V.take k) = (VEnv.names V).take k := by
  simp [VEnv.names, List.map_take]

omit model in
theorem drop_append_len {α : Type} (A B : List α) (i : Nat) :
    (A ++ B).drop (A.length + i) = B.drop i := by
  induction A with
  | nil => simp
  | cons a A ih =>
    rw [List.length_cons, List.cons_append,
      show A.length + 1 + i = (A.length + i) + 1 from by omega,
      List.drop_succ_cons]
    exact ih

omit model in
theorem take_append_len {α : Type} (A B : List α) (i : Nat) :
    (A ++ B).take (A.length + i) = A ++ B.take i := by
  induction A with
  | nil => simp
  | cons a A ih =>
    rw [List.length_cons, List.cons_append,
      show A.length + 1 + i = (A.length + i) + 1 from by omega,
      List.take_succ_cons, ih, List.cons_append]

omit model in
theorem mem_take_mono {α : Type} {l : List α} {m k : Nat} (h : m ≤ k) {x : α}
    (hx : x ∈ l.take m) : x ∈ l.take k := by
  have he : l.take m = (l.take k).take m := by
    rw [List.take_take, Nat.min_eq_left h]
  rw [he] at hx
  exact List.mem_of_mem_take hx

/-- What a statement-class execution does to the environment: nothing shrinks,
and at every *outer* depth `n` — outside the `locals` the enclosing list has
declared — the surviving bindings keep their names and either keep their values
or are named by the analysis.

Quantifying over the outer depth is what makes the relation compose through
`seqCons` without any prefix bookkeeping: the tail's guarantee, stated at every
depth, specializes to the depth the head's `let`-bindings left. -/
def ModOut (locals mods : List Ident) (V W : VEnv yulD) : Prop :=
  V.length ≤ W.length
  ∧ ∀ n : Nat, n + locals.length ≤ V.length →
      List.Forall₂
        (fun (p q : Ident × U256) => p.1 = q.1 ∧ (q.2 = p.2 ∨ q.1 ∈ mods))
        (V.drop (V.length - n)) (W.drop (W.length - n))

/-- The `assign` engine: folding `set` over a list of names changes a position
past `k` only when that name is reported by the analysis — the names that are
*not* reported are exactly the ones bound inside the first `k` entries, which
`set` reaches first. -/
theorem setMany_drop_forall₂ : ∀ {xs : List Ident} {vs : List U256}
    {V : VEnv yulD} {k : Nat} {mods : List Ident},
    (∀ x ∈ xs, x ∈ mods ∨ x ∈ VEnv.names (V.take k)) →
    List.Forall₂ (fun (p q : Ident × U256) => p.1 = q.1 ∧ (q.2 = p.2 ∨ q.1 ∈ mods))
      (V.drop k) ((YulSemantics.VEnv.setMany V xs vs).drop k) := by
  intro xs
  induction xs with
  | nil => intro vs V k mods _; exact Forall2.refl (fun _ => ⟨rfl, Or.inl rfl⟩) _
  | cons x xs ih =>
    intro vs V k mods hall
    cases vs with
    | nil => exact Forall2.refl (fun _ => ⟨rfl, Or.inl rfl⟩) _
    | cons v vs =>
      rw [VEnv.setMany_cons]
      have hnames : VEnv.names ((YulSemantics.VEnv.set V x v).take k)
          = VEnv.names (V.take k) := by
        have hns := VEnv.names_set V x v
        rw [VEnv.names, VEnv.names] at hns ⊢
        rw [List.map_take, List.map_take, hns]
      have htail := ih (vs := vs) (V := YulSemantics.VEnv.set V x v) (k := k)
        (mods := mods) (by
          intro y hy
          rcases hall y (List.mem_cons_of_mem _ hy) with hm | hm
          · exact Or.inl hm
          · exact Or.inr (by rw [hnames]; exact hm))
      have hstep : List.Forall₂
          (fun (p q : Ident × U256) => p.1 = q.1 ∧ (q.2 = p.2 ∨ q.1 ∈ mods))
          (V.drop k) ((YulSemantics.VEnv.set V x v).drop k) := by
        rcases hall x (List.mem_cons_self ..) with hm | hm
        · refine Forall2.imp (fun a b hab => ⟨hab.1, hab.2.imp id (fun he => ?_)⟩)
            (Forall2.drop k (VEnv.set_positional V x v))
          rw [← hab.1, he]; exact hm
        · rw [VEnv.set_drop_of_mem_take V x v k hm]
          exact Forall2.refl (fun _ => ⟨rfl, Or.inl rfl⟩) _
      refine Forall2.trans' ?_ hstep htail
      intro a b c hab hbc
      exact ⟨hab.1.trans hbc.1, by
        rcases hbc.2 with h | h
        · rcases hab.2 with h' | h'
          · exact Or.inl (h.trans h')
          · exact Or.inr (by rw [← hbc.1]; exact h')
        · exact Or.inr h⟩

namespace ModOut

theorem rfl' (locals mods : List Ident) (V : VEnv yulD) : ModOut locals mods V V :=
  ⟨Nat.le_refl _, fun _ _ => Forall2.refl (fun _ => ⟨rfl, Or.inl rfl⟩) _⟩

theorem mono_mods {locals mods mods' : List Ident} {V W : VEnv yulD}
    (hsub : ∀ x ∈ mods, x ∈ mods') (h : ModOut locals mods V W) :
    ModOut locals mods' V W :=
  ⟨h.1, fun n hn => Forall2.imp (fun _ _ hpq =>
    ⟨hpq.1, hpq.2.imp id (fun hm => hsub _ hm)⟩) (h.2 n hn)⟩

/-- Weakening the local scope: fewer locals is a stronger statement. -/
theorem mono_locals {locals locals' mods : List Ident} {V W : VEnv yulD}
    (hle : locals.length ≤ locals'.length) (h : ModOut locals mods V W) :
    ModOut locals' mods V W :=
  ⟨h.1, fun n hn => h.2 n (by omega)⟩

/-- Composition. The side condition says the second fragment's guarantee reaches
every depth the first one does — immediate when the head neither declares nor
the tail's `locals` grows, and provided by the `letDecl` length shape otherwise. -/
theorem trans {l₁ l₂ m₁ m₂ : List Ident} {V V₁ V₂ : VEnv yulD}
    (h₁ : ModOut l₁ m₁ V V₁) (h₂ : ModOut l₂ m₂ V₁ V₂)
    (hd : ∀ n : Nat, n + l₁.length ≤ V.length → n + l₂.length ≤ V₁.length) :
    ModOut l₁ (m₁ ++ m₂) V V₂ := by
  refine ⟨Nat.le_trans h₁.1 h₂.1, fun n hn => ?_⟩
  refine Forall2.trans' ?_ (h₁.2 n hn) (h₂.2 n (hd n hn))
  intro a b c hab hbc
  refine ⟨hab.1.trans hbc.1, ?_⟩
  rcases hbc.2 with h | h
  · rcases hab.2 with h' | h'
    · exact Or.inl (h.trans h')
    · exact Or.inr (List.mem_append.mpr (Or.inl (by rw [← hbc.1]; exact h')))
  · exact Or.inr (List.mem_append.mpr (Or.inr h))

/-- A scope exit on the right: `restore V W` and `W` agree at every outer
depth. -/
theorem restore_right {locals mods : List Ident} {V W : VEnv yulD}
    (h : ModOut locals mods V W) :
    ModOut locals mods V (YulSemantics.restore V W) := by
  refine ⟨by rw [VEnv.length_restore h.1], fun n hn => ?_⟩
  have h2 := h.2 n hn
  rw [VEnv.length_restore h.1, VEnv.restore_def, List.drop_drop]
  have he : W.length - V.length + (V.length - n) = W.length - n := by
    have := h.1; omega
  rw [he]
  exact h2

end ModOut

/-- Reading back through a `ModOut`: a name the analysis does not report reads
the same in both environments. -/
theorem get_congr_of_forall₂ {mods : List Ident} {x : Ident} (hx : x ∉ mods) :
    ∀ {V W : VEnv yulD},
      List.Forall₂
        (fun (p q : Ident × U256) => p.1 = q.1 ∧ (q.2 = p.2 ∨ q.1 ∈ mods)) V W →
      YulSemantics.VEnv.get W x = YulSemantics.VEnv.get V x := by
  intro V W h
  induction h with
  | nil => rfl
  | @cons p q V' W' hpq _ ih =>
    rw [VEnv.get_cons, VEnv.get_cons, ← hpq.1]
    by_cases hc : p.1 = x
    · rw [if_pos hc, if_pos hc]
      rcases hpq.2 with heq | hmem
      · rw [heq]
      · exact absurd (by rw [← hc, hpq.1]; exact hmem) hx
    · rw [if_neg hc, if_neg hc]; exact ih

/-- The names a statement declares in the environment it leaves behind. -/
def declsOfStmt : Stmt Op → List Ident
  | .letDecl vars _ => vars
  | _ => []

omit model in
/-- The declarations of a statement list, split at the head. -/
theorem declsOf_cons (s : Stmt Op) (rest : List (Stmt Op)) :
    declsOf (s :: rest) = declsOfStmt s ++ declsOf rest := by
  cases s <;> rfl

/-- The local scope the analysis threads past a statement. -/
def localsAfter (locals : List Ident) : Stmt Op → List Ident
  | .letDecl vars _ => vars ++ locals
  | _ => locals

omit model in
theorem localsAfter_eq (locals : List Ident) (s : Stmt Op) :
    localsAfter locals s = declsOfStmt s ++ locals := by
  cases s <;> rfl

omit model in
theorem modStmts_cons (locals : List Ident) (s : Stmt Op)
    (rest : List (Stmt Op)) :
    modStmts locals (s :: rest)
      = modStmt locals s ++ modStmts (localsAfter locals s) rest := by
  cases s <;> rfl

theorem LocalsOK.ofNames {locals : List Ident} {V W : VEnv yulD}
    (h : VEnv.names W = VEnv.names V) (hl : LocalsOK locals V) : LocalsOK locals W := by
  intro x hx
  rw [names_take, h, ← names_take]
  exact hl x hx

omit model in
/-- Every case body is scanned by `modCases`. -/
theorem mem_modCases {locals : List Ident} :
    ∀ {cases : List (Literal × List (Stmt Op))} {p : Literal × List (Stmt Op)},
      p ∈ cases → ∀ x ∈ modStmts locals p.2, x ∈ modCases locals cases := by
  intro cases
  induction cases with
  | nil => intro p hp; exact absurd hp (by simp)
  | cons q cs ih =>
    intro p hp x hx
    obtain ⟨ql, qb⟩ := q
    rw [modCases]
    rcases List.mem_cons.mp hp with rfl | hm
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (ih hm x hx)

/-- `selectSwitch` picks a scanned case body, or the default. -/
theorem selectSwitch_cases (cv : U256)
    (cases : List (Literal × List (Stmt Op)))
    (dflt : Option (List (Stmt Op))) :
    (∃ p ∈ cases, YulSemantics.selectSwitch yulD cv cases dflt = p.2)
      ∨ YulSemantics.selectSwitch yulD cv cases dflt = dflt.getD [] := by
  unfold YulSemantics.selectSwitch
  cases hf : cases.find? (fun p => decide (cv = YulSemantics.EVM.litValue p.1)) with
  | none => exact Or.inr rfl
  | some p => exact Or.inl ⟨p, List.mem_of_find?_eq_some hf, rfl⟩

/-- The block a `switch` selects is one the analysis scanned. -/
theorem mem_modStmt_switch {locals : List Ident} {cv : U256}
    {cases : List (Literal × List (Stmt Op))} {dflt : Option (List (Stmt Op))}
    {x : Ident}
    (hx : x ∈ modStmts locals (YulSemantics.selectSwitch yulD cv cases dflt)) :
    x ∈ modStmt locals (.switch (.lit (.number 0)) cases dflt) := by
  cases dflt with
  | none =>
    rcases selectSwitch_cases cv cases none with ⟨p, hp, he⟩ | he
    · rw [he] at hx
      exact List.mem_append_left _ (mem_modCases hp x hx)
    · rw [he] at hx
      exact absurd hx (by simp [modStmts])
  | some b =>
    rcases selectSwitch_cases cv cases (some b) with ⟨p, hp, he⟩ | he
    · rw [he] at hx
      exact List.mem_append_left _ (mem_modCases hp x hx)
    · rw [he] at hx
      exact List.mem_append_right _ hx

/-- The induction motive: what a source derivation says about the environment,
by syntactic class. Expression classes say nothing — they do not touch `V`. -/
def ModMotive (V : VEnv yulD) :
    YulSemantics.Code Op → YulSemantics.Res yulD → Prop
  | .stmt s, .sres V' _ o =>
      VEnv.names V'
          = (if o = .normal then declsOfStmt s else []) ++ VEnv.names V
      ∧ ∀ locals, LocalsOK locals V →
          ModOut locals (modStmt locals s) V V'
  | .stmts ss, .sres V' _ o =>
      (∃ W : List Ident, VEnv.names V' = W ++ VEnv.names V
        ∧ (o = .normal → W.length = (declsOf ss).length
            ∧ ∀ x ∈ declsOf ss, x ∈ W))
      ∧ ∀ locals, LocalsOK locals V →
          ModOut locals (modStmts locals ss) V V'
  | .loop _c post body, .sres V' _ _ =>
      (∃ W : List Ident, VEnv.names V' = W ++ VEnv.names V)
      ∧ ∀ locals, LocalsOK locals V →
          ModOut locals (modStmts locals post ++ modStmts locals body) V V'
  | _, _ => True

/-- `ModOut` with a `restore` on the right — the shape `modStmts_pos` states. -/
theorem ModOut.restoreR {locals mods : List Ident} {V W : VEnv yulD}
    (h : ModOut locals mods V W) :
    ModOut locals mods V (YulSemantics.restore V W) := h.restore_right

/-- Names survive a scope exit. -/
theorem names_restore {V W : VEnv yulD} {Wn : List Ident}
    (hlen : V.length ≤ W.length) (hsh : VEnv.names W = Wn ++ VEnv.names V) :
    VEnv.names (YulSemantics.restore V W) = VEnv.names V := by
  have hWn : Wn.length = W.length - V.length := by
    have := congrArg List.length hsh
    simp [VEnv.length_names] at this
    omega
  rw [VEnv.names, VEnv.restore_def, List.map_drop]
  rw [show List.map Prod.fst W = VEnv.names W from rfl, hsh, ← hWn]
  simp

/--
**The `modStmts` over-approximation is sound** — the analysis obligation, in the
form the induction carries.

The proof is one `induction … with` over the source `Step` derivation with
`ModMotive` above. `ModOut`'s `∀ n` (outer-depth) quantification is what makes
`seqCons` compose without prefix bookkeeping, and `setMany_drop_forall₂` is the
engine of the `assign` case — the one place `LocalsOK` is consumed.
-/
theorem mod_sim {funs : YulSemantics.FunEnv yulD} {V : VEnv yulD}
    {yst : EvmState} {res : YulSemantics.Res yulD}
    {c : YulSemantics.Code Op}
    (h : YulSemantics.Step yulD funs V yst c res) : ModMotive V c res := by
  induction h with
  | lit => trivial
  | var => trivial
  | builtinOk => trivial
  | builtinHalt => trivial
  | builtinArgsHalt => trivial
  | callOk => trivial
  | callHalt => trivial
  | callArgsHalt => trivial
  | argsNil => trivial
  | argsCons => trivial
  | argsRestHalt => trivial
  | argsHeadHalt => trivial
  | funDef => exact ⟨by simp [declsOfStmt], fun locals _ => ModOut.rfl' ..⟩
  | letHalt => exact ⟨by simp, fun locals _ => ModOut.rfl' ..⟩
  | assignHalt => exact ⟨by simp, fun locals _ => ModOut.rfl' ..⟩
  | exprStmt => exact ⟨by simp [declsOfStmt], fun locals _ => ModOut.rfl' ..⟩
  | exprStmtHalt => exact ⟨by simp, fun locals _ => ModOut.rfl' ..⟩
  | ifFalse => exact ⟨by simp [declsOfStmt], fun locals _ => ModOut.rfl' ..⟩
  | ifHalt => exact ⟨by simp, fun locals _ => ModOut.rfl' ..⟩
  | switchHalt => exact ⟨by simp, fun locals _ => ModOut.rfl' ..⟩
  | «break» => exact ⟨by simp, fun locals _ => ModOut.rfl' ..⟩
  | «continue» => exact ⟨by simp, fun locals _ => ModOut.rfl' ..⟩
  | leave => exact ⟨by simp, fun locals _ => ModOut.rfl' ..⟩
  | seqNil => exact ⟨⟨[], rfl, fun _ => ⟨rfl, by simp [declsOf]⟩⟩,
      fun locals _ => ModOut.rfl' ..⟩
  | loopDone => exact ⟨⟨[], rfl⟩, fun locals _ => ModOut.rfl' ..⟩
  | loopCondHalt => exact ⟨⟨[], rfl⟩, fun locals _ => ModOut.rfl' ..⟩
  | @letZero funs V st vars =>
    have hbn : VEnv.names (YulSemantics.bindZeros yulD vars) = vars := by
      simp [VEnv.names, YulSemantics.bindZeros, Function.comp_def]
    have hbl : (YulSemantics.bindZeros yulD vars).length = vars.length := by
      simp [YulSemantics.bindZeros]
    refine ⟨by rw [VEnv.names_append, hbn]; simp [declsOfStmt], fun locals _ => ?_⟩
    refine ⟨by simp [hbl], fun n hn => ?_⟩
    rw [show ((YulSemantics.bindZeros yulD vars ++ V).length - n)
        = (YulSemantics.bindZeros yulD vars).length + (V.length - n) from by
      rw [List.length_append, hbl]; omega, drop_append_len]
    exact Forall2.refl (fun _ => ⟨rfl, Or.inl rfl⟩) _
  | @letVal funs V st vars e vals st1 _ hlen _ =>
    have hbn : VEnv.names (vars.zip vals) = vars := by
      rw [VEnv.names, List.map_fst_zip]
      omega
    have hbl : (vars.zip vals).length = vars.length := by
      simp; omega
    refine ⟨by rw [VEnv.names_append, hbn]; simp [declsOfStmt], fun locals _ => ?_⟩
    refine ⟨by simp [hbl], fun n hn => ?_⟩
    rw [show ((vars.zip vals ++ V).length - n)
        = (vars.zip vals).length + (V.length - n) from by
      rw [List.length_append, hbl]; omega, drop_append_len]
    exact Forall2.refl (fun _ => ⟨rfl, Or.inl rfl⟩) _
  | @assignVal funs V st vars e vals st1 _ hlen _ =>
    refine ⟨by rw [VEnv.names_setMany]; simp [declsOfStmt], fun locals hloc => ?_⟩
    refine ⟨by rw [VEnv.length_setMany], fun n hn => ?_⟩
    rw [VEnv.length_setMany]
    refine setMany_drop_forall₂ ?_
    intro x hx
    by_cases hxl : x ∈ locals
    · refine Or.inr ?_
      rw [names_take]
      exact mem_take_mono (m := locals.length) (by omega)
        (by rw [← names_take]; exact hloc x hxl)
    · exact Or.inl (List.mem_filter.mpr ⟨hx, by simpa using hxl⟩)
  | @block funs V st body Vb stb o _ ih =>
    have hlen : V.length ≤ Vb.length := (ih.2 [] (localsOK_nil V)).1
    obtain ⟨W, hsh, -⟩ := ih.1
    exact ⟨by rw [names_restore hlen hsh]; simp [declsOfStmt],
      fun locals hloc => (ih.2 locals hloc).restoreR⟩
  | @ifTrue funs V st c body cv st1 V' st2 o _ _ _ _ ih3 =>
    exact ⟨by rw [ih3.1]; rfl, fun locals hloc => ih3.2 locals hloc⟩
  | @switchExec funs V st c cases dflt cv st1 V' st2 o _ _ _ ih2 =>
    refine ⟨by rw [ih2.1]; rfl, fun locals hloc => (ih2.2 locals hloc).mono_mods ?_⟩
    intro x hx
    exact mem_modStmt_switch hx
  | @forLoop funs V st init c post body Vinit stinit Vend stend o _ _ ih1 ih2 =>
    obtain ⟨W1, hn1, hd1⟩ := ih1.1
    obtain ⟨hW1len, hW1mem⟩ := hd1 rfl
    obtain ⟨W2, hn2⟩ := ih2.1
    have hlenV : V.length ≤ Vinit.length := (ih1.2 [] (localsOK_nil V)).1
    have hlenI : Vinit.length ≤ Vend.length := (ih2.2 [] (localsOK_nil Vinit)).1
    have hVi : Vinit.length = (declsOf init).length + V.length := by
      have hh := congrArg List.length hn1
      simp only [VEnv.length_names, List.length_append] at hh
      omega
    refine ⟨by
      rw [names_restore (Nat.le_trans hlenV hlenI)
        (show VEnv.names Vend = (W2 ++ W1) ++ VEnv.names V by
          rw [hn2, hn1, List.append_assoc])]
      simp [declsOfStmt], fun locals hloc => ?_⟩
    have hloc2 : LocalsOK (declsOf init ++ locals) Vinit := by
      intro x hx
      rw [names_take, hn1,
        show (declsOf init ++ locals).length = W1.length + locals.length from by
          rw [List.length_append, hW1len],
        take_append_len]
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append_left _ (hW1mem x h)
      · exact List.mem_append_right _ (by rw [← names_take]; exact hloc x h)
    refine ((ModOut.trans (ih1.2 locals hloc) (ih2.2 _ hloc2) ?_).mono_mods
      ?_).restoreR
    · intro n hn
      rw [List.length_append, hVi]
      omega
    · intro x hx
      simp only [modStmt]
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append_left _ (List.mem_append_left _ h)
      · rcases List.mem_append.mp h with h' | h'
        · exact List.mem_append_left _ (List.mem_append_right _ h')
        · exact List.mem_append_right _ h'
  | @forInitHalt funs V st init c post body Vinit stinit _ ih =>
    have hlen : V.length ≤ Vinit.length := (ih.2 [] (localsOK_nil V)).1
    obtain ⟨W, hsh, -⟩ := ih.1
    refine ⟨by rw [names_restore hlen hsh]; simp,
      fun locals hloc => ((ih.2 locals hloc).restoreR).mono_mods ?_⟩
    intro x hx
    simp only [modStmt]
    exact List.mem_append_left _ (List.mem_append_left _ hx)
  | @seqCons funs V st s rest V1 st1 V2 st2 o _ _ ih1 ih2 =>
    have hn1 : VEnv.names V1 = declsOfStmt s ++ VEnv.names V := by
      have hh := ih1.1; simpa using hh
    have hl1 : V1.length = (declsOfStmt s).length + V.length := by
      have hh := congrArg List.length hn1
      simp only [VEnv.length_names, List.length_append] at hh
      omega
    have hlocT : ∀ locals, LocalsOK locals V → LocalsOK (localsAfter locals s) V1 := by
      intro locals hloc x hx
      rw [localsAfter_eq] at hx
      rw [localsAfter_eq, names_take, hn1,
        show (declsOfStmt s ++ locals).length
          = (declsOfStmt s).length + locals.length from by simp,
        take_append_len]
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (by rw [← names_take]; exact hloc x h)
    obtain ⟨W2, hn2, hd2⟩ := ih2.1
    refine ⟨⟨W2 ++ declsOfStmt s, by rw [hn2, hn1, List.append_assoc], ?_⟩,
      fun locals hloc => ?_⟩
    · intro ho
      obtain ⟨hlen2, hmem2⟩ := hd2 ho
      refine ⟨by rw [declsOf_cons, List.length_append, List.length_append, hlen2]; omega, ?_⟩
      intro x hx
      rw [declsOf_cons] at hx
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append_right _ h
      · exact List.mem_append_left _ (hmem2 x h)
    · rw [modStmts_cons]
      refine ModOut.trans (ih1.2 locals hloc) (ih2.2 _ (hlocT locals hloc)) ?_
      intro n hn
      rw [localsAfter_eq, List.length_append, hl1]
      omega
  | @seqStop funs V st s rest V1 st1 o _ ho ih =>
    refine ⟨⟨_, ih.1, fun hn => absurd hn ho⟩,
      fun locals hloc => (ih.2 locals hloc).mono_mods ?_⟩
    intro x hx
    simp only [modStmts]
    exact List.mem_append_left _ hx
  | @loopStep funs V st c post body cv st1 Vb stb ob Vp stp Vend stend o
      _h1 _hne _h3 _hob _h5 _h6 _ih1 ih3 ih5 ih6 =>
    have hnb : VEnv.names Vb = VEnv.names V := by
      have hh := ih3.1; simpa [declsOfStmt] using hh
    have hnp : VEnv.names Vp = VEnv.names Vb := by
      have hh := ih5.1; simpa [declsOfStmt] using hh
    obtain ⟨W, hnW⟩ := ih6.1
    refine ⟨⟨W, by rw [hnW, hnp, hnb]⟩, fun locals hloc => ?_⟩
    have hlocB : LocalsOK locals Vb := LocalsOK.ofNames hnb hloc
    have hlocP : LocalsOK locals Vp := LocalsOK.ofNames hnp hlocB
    have hlb : V.length ≤ Vb.length := by
      rw [← VEnv.length_names, ← VEnv.length_names, hnb]
    have hlp : Vb.length ≤ Vp.length := by
      rw [← VEnv.length_names, ← VEnv.length_names, hnp]
    refine ((ModOut.trans (ih3.2 locals hloc)
      (ModOut.trans (ih5.2 locals hlocB) (ih6.2 locals hlocP)
        (fun n hn => by omega)) (fun n hn => by omega)).mono_mods ?_)
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append_right _ h
    · rcases List.mem_append.mp h with h' | h'
      · exact List.mem_append_left _ h'
      · exact h'
  | @loopPostHalt funs V st c post body cv st1 Vb stb ob Vp stp
      _h1 _hne _h3 _hob _h5 _ih1 ih3 ih5 =>
    have hnb : VEnv.names Vb = VEnv.names V := by
      have hh := ih3.1; simpa [declsOfStmt] using hh
    have hnp : VEnv.names Vp = VEnv.names Vb := by
      have hh := ih5.1; simpa using hh
    refine ⟨⟨[], by rw [hnp, hnb]; simp⟩, fun locals hloc => ?_⟩
    have hlocB : LocalsOK locals Vb := LocalsOK.ofNames hnb hloc
    have hlb : V.length ≤ Vb.length := by
      rw [← VEnv.length_names, ← VEnv.length_names, hnb]
    refine ((ModOut.trans (ih3.2 locals hloc) (ih5.2 locals hlocB)
      (fun n hn => by omega)).mono_mods ?_)
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append_right _ h
    · exact List.mem_append_left _ h
  | @loopBreak funs V st c post body cv st1 Vb stb _ _ _ _ ih =>
    exact ⟨⟨_, ih.1⟩, fun locals hloc =>
      (ih.2 locals hloc).mono_mods (fun x hx => List.mem_append_right _ hx)⟩
  | @loopLeave funs V st c post body cv st1 Vb stb _ _ _ _ ih =>
    exact ⟨⟨_, ih.1⟩, fun locals hloc =>
      (ih.2 locals hloc).mono_mods (fun x hx => List.mem_append_right _ hx)⟩
  | @loopBodyHalt funs V st c post body cv st1 Vb stb _ _ _ _ ih =>
    exact ⟨⟨_, ih.1⟩, fun locals hloc =>
      (ih.2 locals hloc).mono_mods (fun x hx => List.mem_append_right _ hx)⟩

theorem modStmts_pos {funs : YulSemantics.FunEnv yulD} {V Vb : VEnv yulD}
    {yst ystb : EvmState} {o : Outcome} {locals : List Ident}
    {ss : List (Stmt Op)}
    (hloc : LocalsOK locals V)
    (h : YulSemantics.ExecStmts yulD funs V yst ss Vb ystb o) :
    ModOut locals (modStmts locals ss) V (YulSemantics.restore V Vb) :=
  ((mod_sim h).2 locals hloc).restoreR
/-- **The form the construction consumes.** `modifiedX` analyses each body with
`modStmts []`, so this is `modStmts_pos` at the empty local scope: every name
the analysis does not report reads back unchanged after the list has run. -/
theorem modStmts_sound {funs : YulSemantics.FunEnv yulD} {V Vb : VEnv yulD}
    {yst ystb : EvmState} {o : Outcome} {ss : List (Stmt Op)}
    (h : YulSemantics.ExecStmts yulD funs V yst ss Vb ystb o) :
    ∀ x : Ident, x ∉ modStmts [] ss →
      YulSemantics.VEnv.get (YulSemantics.restore V Vb) x
        = YulSemantics.VEnv.get V x := by
  intro x hx
  obtain ⟨hlen, hvals⟩ := modStmts_pos (localsOK_nil V) h
  have hrl : (YulSemantics.restore V Vb).length = V.length := by
    rw [VEnv.restore_def, List.length_drop]
    rw [VEnv.restore_def, List.length_drop] at hlen
    omega
  have hf := hvals V.length (by simp)
  rw [Nat.sub_self, List.drop_zero, hrl, Nat.sub_self, List.drop_zero] at hf
  exact get_congr_of_forall₂ hx hf

/-- Reconstruct a join environment from the values carried for every possibly
modified visible name.  Uniqueness is exactly what turns agreement of visible
lookups back into equality of the positional environments. -/
theorem setMany_eq_of_modOut {env : VMap} {R : Regs} {V W : VEnv yulD}
    {mods xs : List Ident} {vals : List U256}
    (henv : EnvOK (model := model) env V R) (huniq : env.Unique)
    (hnames : VEnv.names W = VEnv.names V) (hmod : ModOut [] mods V W)
    (hvals : List.Forall₂
      (fun x v => YulSemantics.VEnv.get W x = some v) xs vals)
    (hxs : ∀ x ∈ xs, x ∈ env.map Prod.fst)
    (hcover : ∀ x ∈ env.map Prod.fst, x ∈ mods → x ∈ xs) :
    YulSemantics.VEnv.setMany V xs vals = W := by
  apply VEnv.eq_of_names_get
  · rw [VEnv.names_setMany]
    exact henv.unique_names huniq
  · rw [VEnv.names_setMany, hnames]
  · intro x hx
    rw [VEnv.names_setMany] at hx
    by_cases hxm : x ∈ xs
    · have hWset : YulSemantics.VEnv.setMany W xs vals = W :=
        VEnv.setMany_self hvals
      calc
        YulSemantics.VEnv.get (YulSemantics.VEnv.setMany V xs vals) x =
            YulSemantics.VEnv.get (YulSemantics.VEnv.setMany W xs vals) x :=
          VEnv.get_setMany_congr_of_mem hvals.length_eq hxm hx
            (by rw [hnames]; exact hx)
        _ = YulSemantics.VEnv.get W x := by rw [hWset]
    · rw [VEnv.get_setMany_not_mem hxm]
      have hxenv : x ∈ env.map Prod.fst := by rw [henv.names]; exact hx
      have hxmod : x ∉ mods := fun hm => hxm (hcover x hxenv hm)
      have hf := hmod.2 V.length (by simp)
      have hlen : W.length = V.length := by
        rw [← VEnv.length_names, ← VEnv.length_names, hnames]
      rw [Nat.sub_self, List.drop_zero, hlen, Nat.sub_self, List.drop_zero] at hf
      exact (get_congr_of_forall₂ hxmod hf).symm

/-! ### Statement-class leaves

Per-case pieces of the main induction, each usable on its own. -/

/-- The block a *diverting* statement seals is final in the finished function.
`Completes.sealed` deliberately exempts the current block, so the diverting
leaves take this separately; the enclosing `cond`/`switch`/`forLoop` supplies
it, because each `moveTo`s a fresh join/exit block afterwards and its own
`Completes` then covers the sealed one. -/
def CurFinal (f : Func) (fn : FnState) : Prop :=
  ∀ b : Block, fn.blocks[fn.curId]? = some b → f.blocks[fn.curId]? = some b

omit model in
/-- After leaving a sealed block, statement-level growth preserves it: it is
no longer the exceptional current block in `SGrows.keep`. -/
theorem curFinal_of_move_grows {f : Func} {s sM sEnd : BState}
    {bid : BlockId} {u : Unit} {joins : List BlockId}
    (hmv : moveTo bid s = some (u, sM)) (hne : s.fn.curId ≠ bid)
    (hprot : s.fn.curId ∉ joins)
    (hg : SGrows sM sEnd) (hcompl : Completes f sEnd.fn joins) :
    CurFinal f s.fn := by
  rw [M.moveTo_apply] at hmv
  obtain ⟨-, rfl⟩ := M.some_pair_inj hmv
  intro b hb
  have hlt : s.fn.curId < s.fn.blocks.size := lt_size_of_getElem? hb
  have hkeep : sEnd.fn.blocks[s.fn.curId]? = some b :=
    hg.keep s.fn.curId b hlt hne hb
  have hneEnd : s.fn.curId ≠ sEnd.fn.curId := by
    rcases hg.curId with heq | hge
    · simpa [heq] using hne
    · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hlt (by simpa using hge))
  exact hcompl.sealed s.fn.curId b hprot hneEnd hkeep

omit model in
/-- Variant of `curFinal_of_move_grows` for a surrounding structured
translation.  Its later current block may be another block reserved by the
same construct, so freshness is measured against the construct's base `N`.
The block being left predates that base and therefore remains protected by
`SGrowsAt.keep`. -/
theorem curFinal_of_move_sgrowsAt {f : Func} {N : Nat} {s sM sEnd : BState}
    {bid : BlockId} {u : Unit} {joins : List BlockId}
    (hold : s.fn.curId < N)
    (hmv : moveTo bid s = some (u, sM)) (hne : s.fn.curId ≠ bid)
    (hprot : s.fn.curId ∉ joins)
    (hg : SGrowsAt N sM sEnd) (hcompl : Completes f sEnd.fn joins) :
    CurFinal f s.fn := by
  rw [M.moveTo_apply] at hmv
  obtain ⟨-, rfl⟩ := M.some_pair_inj hmv
  intro b hb
  have hkeep : sEnd.fn.blocks[s.fn.curId]? = some b :=
    hg.keep s.fn.curId b hold hne hb
  have hneEnd : s.fn.curId ≠ sEnd.fn.curId := by
    rcases hg.curId with heq | hge
    · simpa [heq] using hne
    · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hold hge)
  exact hcompl.sealed s.fn.curId b hprot hneEnd hkeep

omit model in
/-- What `sealCur` leaves behind: same current block id, empty pending list, and
the block now carrying the emitted instructions and the terminator. -/
theorem sealCur_cur {t : Term} {s s' : BState} {u : Unit}
    (h : sealCur t s = some (u, s')) :
    ∃ b : Block, s'.fn.curId = s.fn.curId ∧ s'.fn.cur = []
      ∧ s'.fn.blocks[s'.fn.curId]? = some ⟨b.params, s.fn.cur.reverse, t⟩ := by
  obtain ⟨b, hb, rfl⟩ := M.sealCur_inv h
  refine ⟨b, rfl, rfl, ?_⟩
  dsimp only
  rw [Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds_self_of_lt (lt_size_of_getElem? hb)]

omit model in
/-- …hence the sealed block *is* the rest of the fragment's current block. -/
theorem curOK_of_sealCur {f : Func} {t : Term} {s s' : BState} {u : Unit}
    (hfin : CurFinal f s'.fn) (h : sealCur t s = some (u, s')) :
    CurOK f s.fn ⟨[], t⟩ := by
  obtain ⟨b, hc, -, hg⟩ := sealCur_cur h
  refine ⟨⟨b.params, s.fn.cur.reverse, t⟩, ?_, by simp, rfl⟩
  rw [← hc]
  exact hfin _ hg

/-- **`leave`** — the construction reads the return variables and seals with
`ret`; the source rule leaves the environment and machine state alone. -/
theorem sim_leave {P : Prog} {f : Func} {fenv : FMap} {env : VMap} {R : Regs}
    {V : VEnv yulD} {lctx : Option LoopCtx} {rs : List Ident} {s₀ s₁ : BState}
    {renv : Option VMap} {yst : EvmState}
    (henv : EnvOK (model := model) env V R)
    (hfin : CurFinal f s₁.fn)
    (htr : trStmt fenv env lctx (some rs) .leave s₀ = some (renv, s₁)) :
    SOut (model := model) P f lctx (some rs) s₀ s₁ R renv V yst yst .leave := by
  rw [trStmt] at htr
  obtain ⟨ids, sA, h1, htr⟩ := M.bind_inv htr
  obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
  obtain ⟨hsA, vals, hget, hforall⟩ := edgeArgs_ok henv h1
  subst hsA
  obtain ⟨-, hs₁⟩ := M.pure_inv h3
  rw [hs₁] at hfin
  refine ⟨rs, vals, rfl, hforall, ?_⟩
  exact execFrom_ret (curOK_of_sealCur hfin h2) hget

/-- **`break`** — seal a jump to the loop's exit block carrying the loop's
variable set; `edgeArgs_ok` says the ids it passes hold the source values. -/
theorem sim_break {P : Prog} {f : Func} {fenv : FMap} {env : VMap} {R : Regs}
    {V : VEnv yulD} {l : LoopCtx} {rets : Option (List Ident)} {s₀ s₁ : BState}
    {renv : Option VMap} {yst : EvmState}
    (henv : EnvOK (model := model) env V R)
    (hfresh : RegsFresh R s₁.fn)
    (hfin : CurFinal f s₁.fn)
    (htr : trStmt fenv env (some l) rets .break s₀ = some (renv, s₁)) :
    SOut (model := model) P f (some l) rets s₀ s₁ R renv V yst yst .break := by
  rw [trStmt] at htr
  obtain ⟨ids, sA, h1, htr⟩ := M.bind_inv htr
  obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
  obtain ⟨hsA, vals, hget, hforall⟩ := edgeArgs_ok henv h1
  subst hsA
  obtain ⟨-, hs₁⟩ := M.pure_inv h3
  rw [hs₁] at hfin
  refine ⟨l, R, vals, rfl, Regs.Le.rfl R, Regs.BelowEq.rfl _ _, hfresh,
    hforall, fun res hjmp => ?_⟩
  exact execFrom_jump (curOK_of_sealCur hfin h2) hget hjmp

/-- **`continue`** — the same, to the loop's `post` block. -/
theorem sim_continue {P : Prog} {f : Func} {fenv : FMap} {env : VMap} {R : Regs}
    {V : VEnv yulD} {l : LoopCtx} {rets : Option (List Ident)} {s₀ s₁ : BState}
    {renv : Option VMap} {yst : EvmState}
    (henv : EnvOK (model := model) env V R)
    (hfresh : RegsFresh R s₁.fn)
    (hfin : CurFinal f s₁.fn)
    (htr : trStmt fenv env (some l) rets .continue s₀ = some (renv, s₁)) :
    SOut (model := model) P f (some l) rets s₀ s₁ R renv V yst yst .continue := by
  rw [trStmt] at htr
  obtain ⟨ids, sA, h1, htr⟩ := M.bind_inv htr
  obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
  obtain ⟨hsA, vals, hget, hforall⟩ := edgeArgs_ok henv h1
  subst hsA
  obtain ⟨-, hs₁⟩ := M.pure_inv h3
  rw [hs₁] at hfin
  refine ⟨l, R, vals, rfl, Regs.Le.rfl R, Regs.BelowEq.rfl _ _, hfresh,
    hforall, fun res hjmp => ?_⟩
  exact execFrom_jump (curOK_of_sealCur hfin h2) hget hjmp

/-- The construction rejects shadowing (`letDecl` checks `VMap.mem`), so the
names a scope declares are disjoint from the ones already visible. This is what
makes scope exit transparent to the outer environment. -/
def NoShadow (V Vb : VEnv yulD) : Prop :=
  ∀ x ∈ VEnv.names (Vb.take (Vb.length - V.length)), x ∉ VEnv.names V

/-- **Scope exit is transparent to outer names.** An outer variable reads the
same before and after `restore` — the bindings `restore` drops are the scope's
own declarations, whose names no outer variable shares. This is what the
`block`/`cond`/`switch`/`for` cases need to carry a non-local exit's edge values
(read at the divert point, inside the scope) out through the source's
`restore`. -/
theorem get_restore_of_noShadow {V Vb : VEnv yulD} (hns : NoShadow V Vb)
    {x : Ident} (hx : x ∈ VEnv.names V) :
    YulSemantics.VEnv.get (YulSemantics.restore V Vb) x
      = YulSemantics.VEnv.get Vb x := by
  have hsplit : Vb = Vb.take (Vb.length - V.length)
      ++ YulSemantics.restore V Vb := by
    rw [VEnv.restore_def, List.take_append_drop]
  conv_rhs => rw [hsplit]
  rw [VEnv.get_append_of_not_mem (fun hmem => hns x hmem hx)]

/-- Transport a *non-normal* `SOut` across a later builder state. The diverting
outcomes never mention the fragment's output environment — only its freshness
bound — so a fragment that diverts keeps its meaning when the construction goes
on to translate the dead code after it. -/
theorem SOut.of_nonNormal {P : Prog} {f : Func} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {s₀ s₁ s₁' : BState} {R : Regs}
    {renv renv' : Option VMap} {V' : VEnv yulD} {yst yst' : EvmState}
    {o : Outcome} (ho : o ≠ .normal)
    (hgrow : s₁.fn.nextVal ≤ s₁'.fn.nextVal)
    (h : SOut (model := model) P f lctx rets s₀ s₁ R renv V' yst yst' o) :
    SOut (model := model) P f lctx rets s₀ s₁' R renv' V' yst yst' o := by
  cases o with
  | normal => exact absurd rfl ho
  | halt => exact h
  | «break» =>
    obtain ⟨lc, R₁, vals, hlc, hle, hbelow, hfr, hforall, hcont⟩ := h
    exact ⟨lc, R₁, vals, hlc, hle, hbelow, hfr.mono hgrow, hforall, hcont⟩
  | «continue» =>
    obtain ⟨lc, R₁, vals, hlc, hle, hbelow, hfr, hforall, hcont⟩ := h
    exact ⟨lc, R₁, vals, hlc, hle, hbelow, hfr.mono hgrow, hforall, hcont⟩
  | leave => exact h

/-- Prepend a straight-line simulation to a statement result.  Structured
control uses this for the expression/dispatch edge before the selected body. -/
theorem SOut.prefix {P : Prog} {f : Func} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {s₀ sA s₁ : BState} {R₀ RA : Regs}
    {renv : Option VMap} {V' : VEnv yulD} {yst ystA yst' : EvmState}
    {o : Outcome}
    (hle : Regs.Le R₀ RA)
    (hbelow : Regs.BelowEq s₀.fn.nextVal R₀ RA)
    (hgrow : s₀.fn.nextVal ≤ sA.fn.nextVal)
    (hsim : SimS (model := model) P f s₀.fn R₀ yst sA.fn RA ystA)
    (h : SOut (model := model) P f lctx rets sA s₁ RA renv V' ystA yst' o) :
    SOut (model := model) P f lctx rets s₀ s₁ R₀ renv V' yst yst' o := by
  cases o with
  | normal =>
    obtain ⟨env', R₁, hr, hle1, hbelow1, hfr, henv, huniq, hsim1⟩ := h
    exact ⟨env', R₁, hr, hle.trans hle1,
      hbelow.trans (hbelow1.mono hgrow), hfr, henv, huniq,
      hsim.trans hsim1⟩
  | halt => exact hsim _ h
  | «break» =>
    obtain ⟨lc, R₁, vals, hlc, hle1, hbelow1, hfr, hvals, hcont⟩ := h
    exact ⟨lc, R₁, vals, hlc, hle.trans hle1,
      hbelow.trans (hbelow1.mono hgrow), hfr, hvals,
      fun res hj => hsim res (hcont res hj)⟩
  | «continue» =>
    obtain ⟨lc, R₁, vals, hlc, hle1, hbelow1, hfr, hvals, hcont⟩ := h
    exact ⟨lc, R₁, vals, hlc, hle.trans hle1,
      hbelow.trans (hbelow1.mono hgrow), hfr, hvals,
      fun res hj => hsim res (hcont res hj)⟩
  | leave =>
    obtain ⟨rs, vals, hrs, hvals, hex⟩ := h
    exact ⟨rs, vals, hrs, hvals, hsim _ hex⟩

/-- **`seqCons`** — the sequence combinator. A statement that completes
normally hands its register file, environment correspondence and freshness
bound to the rest of the list, and the two fragments' `SimS`s compose; every
non-normal outcome of the tail is carried back through the head's `SimS`.

This is a pure `SOut` combinator: it needs no construction inversion, which is
why the `seqCons` case of the main induction is a one-liner. -/
theorem SOut.seq {P : Prog} {f : Func} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {s₀ sA s₁ : BState} {R : Regs}
    {renv : Option VMap} {env' : VMap} {V1 V2 : VEnv yulD}
    {yst yst1 yst2 : EvmState} {o : Outcome}
    (hgrow : s₀.fn.nextVal ≤ sA.fn.nextVal)
    (hhead : SOut (model := model) P f lctx rets s₀ sA R (some env') V1 yst yst1 .normal)
    (htail : ∀ R₁ : Regs, Regs.Le R R₁ → RegsFresh R₁ sA.fn →
        EnvOK (model := model) env' V1 R₁ →
        env'.Unique →
        SOut (model := model) P f lctx rets sA s₁ R₁ renv V2 yst1 yst2 o) :
    SOut (model := model) P f lctx rets s₀ s₁ R renv V2 yst yst2 o := by
  obtain ⟨e', R₁, he', hle, hbelow, hfr, henv', huniq', hsim⟩ := hhead
  obtain rfl : e' = env' := (Option.some.inj he').symm
  have ht := htail R₁ hle hfr henv' huniq'
  cases o with
  | normal =>
    obtain ⟨e2, R₂, hr2, hle2, hbelow2, hfr2, henv2, huniq2, hsim2⟩ := ht
    exact ⟨e2, R₂, hr2, hle.trans hle2,
      hbelow.trans (hbelow2.mono hgrow), hfr2, henv2, huniq2,
      hsim.trans hsim2⟩
  | halt => exact hsim _ ht
  | «break» =>
    obtain ⟨lc, R₂, vals, hlc, hle2, hbelow2, hfr2, hforall, hcont⟩ := ht
    exact ⟨lc, R₂, vals, hlc, hle.trans hle2,
      hbelow.trans (hbelow2.mono hgrow), hfr2, hforall,
      fun res hj => hsim res (hcont res hj)⟩
  | «continue» =>
    obtain ⟨lc, R₂, vals, hlc, hle2, hbelow2, hfr2, hforall, hcont⟩ := ht
    exact ⟨lc, R₂, vals, hlc, hle.trans hle2,
      hbelow.trans (hbelow2.mono hgrow), hfr2, hforall,
      fun res hj => hsim res (hcont res hj)⟩
  | leave =>
    obtain ⟨rs, vals, hrs, hforall, hex⟩ := ht
    exact ⟨rs, vals, hrs, hforall, hsim _ hex⟩

/-- **Scope exit** — the `block` combinator. The construction drops the scope's
own `VMap` entries; the source `restore`s. `EnvOK.restore` matches the two, and
`get_restore_of_noShadow` carries a non-local exit's edge values (read inside
the scope) out through the `restore`. -/
theorem SOut.scope {P : Prog} {f : Func} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {s₀ s₁ : BState} {R : Regs}
    {renv : Option VMap} {env : VMap} {V Vb : VEnv yulD}
    {yst yst' : EvmState} {o : Outcome}
    (hlen : env.length = V.length) (hns : NoShadow V Vb)
    (hvars : ∀ lc : LoopCtx, lctx = some lc → ∀ x ∈ lc.vars, x ∈ VEnv.names V)
    (hrets : ∀ rs, rets = some rs → ∀ x ∈ rs, x ∈ VEnv.names V)
    (h : SOut (model := model) P f lctx rets s₀ s₁ R renv Vb yst yst' o) :
    SOut (model := model) P f lctx rets s₀ s₁ R
      (renv.map (fun e => e.drop (e.length - env.length)))
      (YulSemantics.restore V Vb) yst yst' o := by
  cases o with
  | normal =>
    obtain ⟨e', R₁, hr, hle, hbelow, hfr, henv', huniq, hsim⟩ := h
    exact ⟨e'.drop (e'.length - env.length), R₁, by rw [hr]; rfl, hle,
      hbelow, hfr,
      henv'.restore hlen, huniq.drop _, hsim⟩
  | halt => exact h
  | «break» =>
    obtain ⟨lc, R₁, vals, hlc, hle, hbelow, hfr, hforall, hcont⟩ := h
    exact ⟨lc, R₁, vals, hlc, hle, hbelow, hfr,
      Forall2.imp_mem hforall (fun x hx v hv => by
        rw [get_restore_of_noShadow hns (hvars lc hlc x hx)]; exact hv), hcont⟩
  | «continue» =>
    obtain ⟨lc, R₁, vals, hlc, hle, hbelow, hfr, hforall, hcont⟩ := h
    exact ⟨lc, R₁, vals, hlc, hle, hbelow, hfr,
      Forall2.imp_mem hforall (fun x hx v hv => by
        rw [get_restore_of_noShadow hns (hvars lc hlc x hx)]; exact hv), hcont⟩
  | leave =>
    obtain ⟨rs, vals, hrs, hforall, hex⟩ := h
    exact ⟨rs, vals, hrs,
      Forall2.imp_mem hforall (fun x hx v hv => by
        rw [get_restore_of_noShadow hns (hrets rs hrs x hx)]; exact hv), hex⟩

/-- **`seqNil`** — the empty live statement list emits nothing. -/
theorem sim_seqNil {P : Prog} {f : Func} {fenv : FMap} {env : VMap} {R : Regs}
    {V : VEnv yulD} {lctx : Option LoopCtx} {rets : Option (List Ident)}
    {s₀ s₁ : BState} {renv : Option VMap} {yst : EvmState}
    (henv : EnvOK (model := model) env V R) (huniq : env.Unique)
    (hfresh : RegsFresh R s₀.fn)
    (htr : trStmts fenv env lctx rets false [] s₀ = some (renv, s₁)) :
    SOut (model := model) P f lctx rets s₀ s₁ R renv V yst yst .normal := by
  rw [trStmts] at htr
  obtain ⟨hrenv, hs₁⟩ := M.pure_inv htr
  subst hs₁
  exact ⟨env, R, by simpa using hrenv, Regs.Le.rfl R, Regs.BelowEq.rfl _ _,
    hfresh, henv, huniq,
    SimS.rfl'⟩

/-- **The edge into a reserved join block.** `cond`'s join, `switch`'s join and
the loop's header/exit/post blocks are all *reserved* (`newBlock`) before the
edges into them are sealed, so the construction never sees their finished
bodies — only their parameter lists. `Completes.params` is exactly the
strengthening that bridges that gap: it fixes the finished block's parameters,
which is what `Exec`'s jump/branch rules need to bind the edge arguments. -/
theorem jumpTo_of_completes {P : Prog} {f : Func} {sRes sCont : BState}
    {bid : BlockId} {b : Block} {vals : List U256} {R : Regs} {st : EvmState}
    {res : FRes} {joins : List BlockId}
    (hcompl : Completes f sRes.fn joins)
    (hres : sRes.fn.blocks[bid]? = some b)
    (hcur : sCont.fn.curId = bid) (hcur0 : sCont.fn.cur = [])
    (hlen : b.params.length = vals.length)
    (hex : ExecFrom (model := model) P f sCont.fn (R.setMany b.params vals) st res) :
    JumpTo (model := model) P f bid vals R st res := by
  obtain ⟨rest, ⟨jb, hjb, hi, ht⟩, hexec⟩ := hex
  rw [hcur] at hjb
  rw [hcur0] at hi
  simp only [List.reverse_nil, List.nil_append] at hi
  obtain ⟨bf, hbf, hbp⟩ := hcompl.params bid b hres
  have heq : jb = bf := (Option.some.inj (hbf.symm.trans hjb)).symm
  rw [heq] at hi ht
  refine ⟨jb, hjb, by rw [heq, hbp]; exact hlen, ?_⟩
  rw [heq, hbp, hi, ht]
  cases rest
  exact hexec

/-! ### Edges into reserved blocks, as `SimS` steps

`cond`, `switch` and the loop family all end a block with an edge into a block
the construction reserved earlier. These three steps are the whole content of
those cases; what is left for the induction shell is the (mechanical) inversion
of the corresponding `trStmt` equation. -/

/-- A fall-through `jump` into a reserved join block. -/
theorem simS_jump_join {P : Prog} {f : Func} {R : Regs} {sEnd s₁ : BState}
    {joinId : BlockId} {xv : List ValId} {vals : List U256} {jb : Block}
    {st : EvmState} {joins : List BlockId}
    (hcompl : Completes f s₁.fn joins)
    (hseal : CurOK f sEnd.fn ⟨[], .jump ⟨joinId, xv⟩⟩)
    (hres : s₁.fn.blocks[joinId]? = some jb)
    (hcur : s₁.fn.curId = joinId) (hcur0 : s₁.fn.cur = [])
    (hg : R.getMany xv = some vals)
    (hlen : jb.params.length = vals.length) :
    SimS (model := model) P f sEnd.fn R st s₁.fn
      (R.setMany jb.params vals) st := by
  intro res hex
  exact execFrom_jump hseal hg
    (jumpTo_of_completes hcompl hres hcur hcur0 hlen hex)

/-- The *false* edge of an `if`: straight to the join, carrying the current
values of the join's variable set. -/
theorem simS_branchFalse_join {P : Prog} {f : Func} {R : Regs} {sA s₁ : BState}
    {cv0 : ValId} {bodyId joinId : BlockId} {xvals : List ValId}
    {vals : List U256} {jb : Block} {st : EvmState} {joins : List BlockId}
    (hcompl : Completes f s₁.fn joins)
    (hbranch : CurOK f sA.fn ⟨[], .branch cv0 ⟨bodyId, []⟩ ⟨joinId, xvals⟩⟩)
    (hc : R cv0 = some 0)
    (hres : s₁.fn.blocks[joinId]? = some jb)
    (hcur : s₁.fn.curId = joinId) (hcur0 : s₁.fn.cur = [])
    (hg : R.getMany xvals = some vals)
    (hlen : jb.params.length = vals.length) :
    SimS (model := model) P f sA.fn R st s₁.fn
      (R.setMany jb.params vals) st := by
  intro res hex
  exact execFrom_branchFalse hbranch hc hg
    (jumpTo_of_completes hcompl hres hcur hcur0 hlen hex)

/-- The *true* edge of an `if`: into the body block, which takes no arguments,
so the register file is unchanged. -/
theorem simS_branchTrue_body {P : Prog} {f : Func} {R : Regs} {sA sB s₁ : BState}
    {cv0 : ValId} {v : U256} {bodyId joinId : BlockId} {xvals : List ValId}
    {bb : Block} {st : EvmState} {joins : List BlockId}
    (hcompl : Completes f s₁.fn joins)
    (hbranch : CurOK f sA.fn ⟨[], .branch cv0 ⟨bodyId, []⟩ ⟨joinId, xvals⟩⟩)
    (hc : R cv0 = some v) (hv : v ≠ 0)
    (hres : s₁.fn.blocks[bodyId]? = some bb) (hbp : bb.params = [])
    (hcur : sB.fn.curId = bodyId) (hcur0 : sB.fn.cur = []) :
    SimS (model := model) P f sA.fn R st sB.fn R st := by
  intro res hex
  refine execFrom_branchTrue (vals := []) hbranch hc hv (by simp) ?_
  refine jumpTo_of_completes hcompl hres hcur hcur0 (by rw [hbp]; simp) ?_
  rw [hbp]
  simpa using hex

/-- The finished function's current block continues where the builder left off.

The *normal* path never needs this — `SimS` is continuation-passing, so it
consumes an `ExecFrom` at the output state and produces one at the input. A
*halting* fragment has no continuation to consume, so it has to exhibit the
block itself; this is that witness. -/
def CurPlaced (f : Func) (fn : FnState) : Prop := ∃ rest, CurOK f fn rest

omit model in
/-- If an empty current block is left by `moveTo`, completion of the moved-to
state places that former current block in the finished function. -/
theorem CurPlaced.of_moveTo_empty {f : Func} {s s' : BState} {bid : BlockId}
    {u : Unit} {joins : List BlockId}
    (hv : s.fn.curId < s.fn.blocks.size) (hcur : s.fn.cur = [])
    (hne : s.fn.curId ≠ bid) (hmv : moveTo bid s = some (u, s'))
    (hprot : s.fn.curId ∉ joins)
    (hcompl : Completes f s'.fn joins) : CurPlaced f s.fn := by
  rw [M.moveTo_apply] at hmv
  obtain ⟨-, rfl⟩ := M.some_pair_inj hmv
  let b := s.fn.blocks[s.fn.curId]
  have hb : s.fn.blocks[s.fn.curId]? = some b :=
    Array.getElem?_eq_getElem hv
  have hf : f.blocks[s.fn.curId]? = some b :=
    hcompl.sealed _ b hprot hne hb
  exact ⟨⟨b.instrs, b.term⟩, b, hf, by rw [hcur]; simp, rfl⟩

omit model in
/-- `CurPlaced` travels backwards along instructions emitted into the same
block. -/
theorem CurPlaced.ofPrefix {f : Func} {fn fn' : FnState} (h : CurPlaced f fn')
    (hc : fn'.curId = fn.curId) (Δ : List Instr) (hcur : fn'.cur = Δ ++ fn.cur) :
    CurPlaced f fn := by
  obtain ⟨rest, b, hb, hi, ht⟩ := h
  refine ⟨⟨Δ.reverse ++ rest.instrs, rest.term⟩, b, by rw [← hc]; exact hb, ?_, ht⟩
  rw [hi, hcur]
  simp

omit model in
/-- A fragment that leaves its incoming block open.  Besides the pending-list
prefix, remember that the reserved block at the current id was not overwritten;
this is what lets an already-sealed predecessor survive the dead-code walk. -/
def CurSame (s s' : BState) : Prop :=
  s'.fn.curId = s.fn.curId
    ∧ (∃ Δ : List Instr, s'.fn.cur = Δ ++ s.fn.cur)
    ∧ ∀ b : Block, s.fn.blocks[s.fn.curId]? = some b →
        s'.fn.blocks[s.fn.curId]? = some b

/-- The incoming block was sealed and the construction moved to another block. -/
def CurMoved (s s' : BState) : Prop :=
  s.fn.curId ≠ s'.fn.curId ∧ ∃ b : Block,
    s'.fn.blocks[s.fn.curId]? = some b
      ∧ ∃ Δ : List Instr, b.instrs = s.fn.cur.reverse ++ Δ

/-- The incoming block was sealed but remains current.  This is the shape of a
bare `break`/`continue`/`leave`/halting expression before an enclosing construct
moves to its join. -/
def CurSealed (s s' : BState) : Prop :=
  s'.fn.curId = s.fn.curId ∧ ∃ b : Block,
    s'.fn.blocks[s.fn.curId]? = some b
      ∧ ∃ Δ : List Instr, b.instrs = s.fn.cur.reverse ++ Δ

/-- A fall-through fragment is either still filling its incoming block or has
sealed it and moved to a fresh continuation. -/
def CurOpen (s s' : BState) : Prop := CurSame s s' ∨ CurMoved s s'

/-- A diverting fragment has sealed its incoming block, with or without a later
move performed by an enclosing structured construct. -/
def CurClosed (s s' : BState) : Prop := CurMoved s s' ∨ CurSealed s s'

/-- The non-result-sensitive union used by the backwards-placement consumer. -/
def CurKeeps (s s' : BState) : Prop := CurOpen s s' ∨ CurSealed s s'

/-- The result-sensitive form threaded through the construction induction.
Fall-through must be open; diversion must be closed. -/
def CurResult : Option VMap → BState → BState → Prop
  | some _, s, s' => CurOpen s s'
  | none, s, s' => CurClosed s s'

/-- The builder's current id names a reserved block.  This premise is true at
the top-level entry and is the validity fact that must be threaded through the
mutual construction induction. -/
def CurValid (s : BState) : Prop := s.fn.curId < s.fn.blocks.size

namespace CurValid

omit model in
theorem of_grows {s s' : BState} (hv : CurValid s) (hg : Grows s s') :
    CurValid s' := by
  rw [CurValid, ← hg.curId, ← hg.blocks]
  exact hv

omit model in
theorem of_same_sgrows {N : Nat} {s s' : BState} (hv : CurValid s)
    (hg : SGrowsAt N s s') (hc : s'.fn.curId = s.fn.curId) : CurValid s' := by
  rw [CurValid, hc]
  exact Nat.lt_of_lt_of_le hv hg.size

omit model in
theorem of_moveTo {bid : BlockId} {s s' : BState} {u : Unit}
    (hlt : bid < s.fn.blocks.size) (h : moveTo bid s = some (u, s')) :
    CurValid s' := by
  rw [M.moveTo_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact hlt

end CurValid

namespace CurSame

omit model in
theorem rfl' (s : BState) : CurSame s s :=
  ⟨rfl, ⟨[], rfl⟩, fun _ hb => hb⟩

omit model in
theorem of_grows {s s' : BState} (h : Grows s s') : CurSame s s' :=
  ⟨h.curId.symm, h.cur, fun b hb => by rw [← h.blocks]; exact hb⟩

omit model in
theorem of_fnEq {s s' : BState} (h : s'.fn = s.fn) : CurSame s s' := by
  rw [CurSame, h]
  exact ⟨rfl, ⟨[], rfl⟩, fun _ hb => hb⟩

omit model in
theorem trans {s s₁ s₂ : BState} (h₁ : CurSame s s₁) (h₂ : CurSame s₁ s₂) :
    CurSame s s₂ := by
  rcases h₁ with ⟨hc1, ⟨Δ1, hi1⟩, hb1⟩
  rcases h₂ with ⟨hc2, ⟨Δ2, hi2⟩, hb2⟩
  refine ⟨hc2.trans hc1, ⟨Δ2 ++ Δ1, by rw [hi2, hi1, List.append_assoc]⟩,
    fun b hb => ?_⟩
  rw [← hc1]
  exact hb2 b (by simpa only [hc1] using hb1 b hb)

omit model in
theorem of_newBlock {ps : List ValId} {s s' : BState} {bid : BlockId}
    (h : newBlock ps s = some (bid, s')) : CurSame s s' := by
  rw [M.newBlock_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  refine ⟨rfl, ⟨[], rfl⟩, fun b hb => ?_⟩
  have hlt := lt_size_of_getElem? hb
  dsimp only
  rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hlt)]
  exact hb

omit model in
theorem transMoved {s s₁ s₂ : BState} (h₁ : CurSame s s₁)
    (h₂ : CurMoved s₁ s₂) : CurMoved s s₂ := by
  rcases h₁ with ⟨hc1, ⟨Δ1, hi1⟩, -⟩
  rcases h₂ with ⟨hne2, b, hb, Δ2, hi2⟩
  refine ⟨by rw [← hc1]; exact hne2, b, by simpa only [hc1] using hb,
    Δ1.reverse ++ Δ2, ?_⟩
  rw [hi2, hi1]
  simp

omit model in
/-- Backward transfer of current-block placement through builder steps that
leave the current block open. -/
theorem placed_back {f : Func} {s s' : BState} (h : CurSame s s')
    (hp : CurPlaced f s'.fn) : CurPlaced f s.fn := by
  obtain ⟨hc, ⟨Δ, hcur⟩, -⟩ := h
  exact hp.ofPrefix hc Δ hcur

end CurSame

omit model in
theorem curSealed_of_sealCur {t : Term} {s s' : BState} {u : Unit}
    (h : sealCur t s = some (u, s')) : CurSealed s s' := by
  obtain ⟨b, hc, -, hb⟩ := sealCur_cur h
  exact ⟨hc, ⟨b.params, s.fn.cur.reverse, t⟩, by simpa only [hc] using hb,
    [], by simp⟩

omit model in
theorem curMoved_of_seal_move {t : Term} {bid : BlockId} {s sA s' : BState}
    {u v : Unit} (hne : s.fn.curId ≠ bid)
    (hseal : sealCur t s = some (u, sA))
    (hmove : moveTo bid sA = some (v, s')) : CurMoved s s' := by
  obtain ⟨b, hc, -, hb⟩ := sealCur_cur hseal
  rw [M.moveTo_apply] at hmove
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj hmove
  refine ⟨hne, ⟨b.params, s.fn.cur.reverse, t⟩, ?_, [], by simp⟩
  simpa only [hc] using hb

omit model in
/-- **Backward transfer of `CurPlaced`.** The placement of the current block
travels from a fragment's output state to its input state, given `CurKeeps`.
This is the primitive `seqCons`/`seqStop` need in order to hand their head IH a
`CurPlaced` at the intermediate state: `Completes` already travels backwards
(`SGrowsAt.completes_of`), and this closes the gap for `CurPlaced`. -/
theorem curPlaced_back {f : Func} {s s' : BState} {renv : Option VMap}
    {joins : List BlockId}
    (hk : CurResult renv s s') (hprot : s.fn.curId ∉ joins)
    (hcompl : Completes f s'.fn joins)
    (hfin : renv = none → CurFinal f s'.fn) (hcp : CurPlaced f s'.fn) :
    CurPlaced f s.fn := by
  cases renv with
  | some env =>
    rcases hk with ⟨hc, ⟨Δ, hcur⟩, -⟩ | ⟨hne, b, hb, Δ, hi⟩
    · exact hcp.ofPrefix hc Δ hcur
    · exact ⟨⟨Δ, b.term⟩, b, hcompl.sealed _ b hprot hne hb, hi, rfl⟩
  | none =>
    rcases hk with ⟨hne, b, hb, Δ, hi⟩ | ⟨hc, b, hb, Δ, hi⟩
    · exact ⟨⟨Δ, b.term⟩, b, hcompl.sealed _ b hprot hne hb, hi, rfl⟩
    · have hf : f.blocks[s.fn.curId]? = some b := by
        rw [← hc]
        exact hfin rfl b (by simpa only [hc] using hb)
      exact ⟨⟨Δ, b.term⟩, b, hf, hi, rfl⟩

omit model in
/-- `CurKeeps` composes along a chain of fragments. The `SGrowsAt` witnesses
supply the two facts the composition needs: that the block array only grows, and
that a fragment which moves the current block moves it to a *fresh* one — so a
block left behind is never returned to. -/
theorem CurOpen.trans {N : Nat} {s s₁ s₂ : BState}
    (hcur : s.fn.curId < s.fn.blocks.size)
    (hg₁ : SGrowsAt N s s₁) (hg₂ : SGrowsAt s₁.fn.blocks.size s₁ s₂)
    (h₁ : CurOpen s s₁) (h₂ : CurOpen s₁ s₂) : CurOpen s s₂ := by
  rcases h₁ with ⟨hc1, ⟨Δ1, hcur1⟩, hbcur1⟩ | ⟨hne1, b1, hb1, Δ1, hi1⟩
  · rcases h₂ with ⟨hc2, ⟨Δ2, hcur2⟩, hbcur2⟩ | ⟨hne2, b2, hb2, Δ2, hi2⟩
    · exact Or.inl ⟨hc2.trans hc1, ⟨Δ2 ++ Δ1,
        by rw [hcur2, hcur1, List.append_assoc]⟩, fun b hb => by
          rw [← hc1]
          apply hbcur2
          simpa only [hc1] using hbcur1 b hb⟩
    · refine Or.inr ⟨by rw [← hc1]; exact hne2, b2, by rw [← hc1]; exact hb2,
        Δ1.reverse ++ Δ2, ?_⟩
      rw [hi2, hcur1]
      simp
  · have hne2' : s.fn.curId ≠ s₂.fn.curId := by
      rcases hg₂.curId with hc2 | hge2
      · rw [hc2]; exact hne1
      · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le
          (Nat.lt_of_lt_of_le hcur hg₁.size) hge2)
    exact Or.inr ⟨hne2', b1,
      hg₂.keep s.fn.curId b1 (Nat.lt_of_lt_of_le hcur hg₁.size) hne1 hb1, Δ1, hi1⟩

omit model in
/-- An open prefix composes with a diverting suffix. -/
theorem CurOpen.transClosed {N : Nat} {s s₁ s₂ : BState}
  (hcur : s.fn.curId < s.fn.blocks.size)
    (hg₁ : SGrowsAt N s s₁) (hg₂ : SGrowsAt s₁.fn.blocks.size s₁ s₂)
    (h₁ : CurOpen s s₁) (h₂ : CurClosed s₁ s₂) : CurClosed s s₂ := by
  rcases h₂ with hmove | hseal
  · rcases h₁ with ⟨hc1, ⟨Δ1, hcur1⟩, -⟩ | ⟨hne1, b1, hb1, Δ1, hi1⟩
    · rcases hmove with ⟨hne2, b2, hb2, Δ2, hi2⟩
      refine Or.inl ⟨by rw [← hc1]; exact hne2, b2, by simpa only [hc1] using hb2,
        Δ1.reverse ++ Δ2, ?_⟩
      rw [hi2, hcur1]
      simp
    · have hne2' : s.fn.curId ≠ s₂.fn.curId := by
        rcases hg₂.curId with hc2 | hge2
        · rw [hc2]; exact hne1
        · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le
            (Nat.lt_of_lt_of_le hcur hg₁.size) hge2)
      exact Or.inl ⟨hne2', b1,
        hg₂.keep s.fn.curId b1 (Nat.lt_of_lt_of_le hcur hg₁.size) hne1 hb1,
        Δ1, hi1⟩
  rcases h₁ with ⟨hc1, ⟨Δ1, hcur1⟩, -⟩ | ⟨hne1, b1, hb1, Δ1, hi1⟩
  · rcases hseal with ⟨hc2, b2, hb2, Δ2, hi2⟩
    refine Or.inr ⟨hc2.trans hc1, b2, by simpa only [hc1] using hb2,
      Δ1.reverse ++ Δ2, ?_⟩
    rw [hi2, hcur1]
    simp
  · have hne2' : s.fn.curId ≠ s₂.fn.curId := by
      rcases hg₂.curId with hc2 | hge2
      · rw [hc2]; exact hne1
      · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le
          (Nat.lt_of_lt_of_le hcur hg₁.size) hge2)
    exact Or.inl ⟨hne2', b1,
      hg₂.keep s.fn.curId b1 (Nat.lt_of_lt_of_le hcur hg₁.size) hne1 hb1, Δ1, hi1⟩

omit model in
theorem CurOpen.transMoved {N : Nat} {s s₁ s₂ : BState}
    (hcur : CurValid s) (hg₁ : SGrowsAt N s s₁)
    (hg₂ : SGrowsAt s₁.fn.blocks.size s₁ s₂)
    (h₁ : CurOpen s s₁) (h₂ : CurMoved s₁ s₂) : CurMoved s s₂ := by
  rcases h₁ with hs | hm
  · exact hs.transMoved h₂
  · rcases hm with ⟨hne1, b, hb, Δ, hi⟩
    have hne2 : s.fn.curId ≠ s₂.fn.curId := by
      rcases hg₂.curId with hc | hge
      · rw [hc]; exact hne1
      · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le
          (Nat.lt_of_lt_of_le hcur hg₁.size) hge)
    exact ⟨hne2, b,
      hg₂.keep s.fn.curId b (Nat.lt_of_lt_of_le hcur hg₁.size) hne1 hb,
      Δ, hi⟩

omit model in
/-- Dead-code traversal leaves `fn` unchanged, so it preserves a preceding
closed fragment. -/
theorem CurClosed.transSame {N : Nat} {s s₁ s₂ : BState}
    (hcur : s.fn.curId < s.fn.blocks.size)
    (hg₁ : SGrowsAt N s s₁) (hg₂ : SGrowsAt s₁.fn.blocks.size s₁ s₂)
    (h₁ : CurClosed s s₁) (h₂ : CurSame s₁ s₂) : CurClosed s s₂ := by
  rcases h₁ with ⟨hne1, b1, hb1, Δ1, hi1⟩ | ⟨hc1, b1, hb1, Δ1, hi1⟩
  · have hne2 : s.fn.curId ≠ s₂.fn.curId := by rw [h₂.1]; exact hne1
    exact Or.inl ⟨hne2, b1,
      hg₂.keep s.fn.curId b1 (Nat.lt_of_lt_of_le hcur hg₁.size) hne1 hb1, Δ1, hi1⟩
  · exact Or.inr ⟨h₂.1.trans hc1, b1, by
      rw [← hc1]
      exact h₂.2.2 b1 (by simpa only [hc1] using hb1), Δ1, hi1⟩

omit model in
/-- Once the incoming block has been sealed and the builder has moved to a
fresh block, any later statement-level growth preserves that sealed block and
cannot return to its id. -/
theorem CurMoved.forward {s s₁ s₂ : BState}
    (hcur : CurValid s) (_hg₁ : SGrows s s₁)
    (hg₂ : SGrowsAt s.fn.blocks.size s₁ s₂) (hm : CurMoved s s₁) :
    CurMoved s s₂ := by
  rcases hm with ⟨hne1, b, hb, Δ, hi⟩
  have hne2 : s.fn.curId ≠ s₂.fn.curId := by
    rcases hg₂.curId with hc | hge
    · rw [hc]; exact hne1
    · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hcur hge)
  exact ⟨hne2, b,
    hg₂.keep s.fn.curId b hcur hne1 hb, Δ, hi⟩

omit model in
theorem newBlock_size {ps : List ValId} {s s' : BState} {bid : BlockId}
    (h : newBlock ps s = some (bid, s')) :
    s'.fn.blocks.size = s.fn.blocks.size + 1 := by
  rw [M.newBlock_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  simp

omit model in
theorem newBlock_target_lt {ps : List ValId} {s s' : BState} {bid : BlockId}
    (h : newBlock ps s = some (bid, s')) : bid < s'.fn.blocks.size := by
  rw [SGrowsAt.newBlock_id h, newBlock_size h]
  exact Nat.lt_succ_self _

omit model in
/-- The block just reserved by `newBlock` is present with exactly the supplied
parameter list. -/
theorem newBlock_target_get {ps : List ValId} {s s' : BState} {bid : BlockId}
    (h : newBlock ps s = some (bid, s')) :
    s'.fn.blocks[bid]? = some ⟨ps, [], .ret []⟩ := by
  rw [M.newBlock_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  simp

/-! ### Current-block validity and shape of the mutual translation -/

def ScopeCur (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (body : List (Stmt Op)) : Prop :=
  ∀ (s : BState) (r : Option VMap) (s' : BState), CurValid s →
    trScope fenv env lctx rets body s = some (r, s') →
      CurValid s' ∧ CurResult r s s'

def StmtsCur (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (d : Bool) (ss : List (Stmt Op)) : Prop :=
  if d then True else
    ∀ (s : BState) (r : Option VMap) (s' : BState), CurValid s →
      trStmts fenv env lctx rets d ss s = some (r, s') →
        CurValid s' ∧ CurResult r s s'

def StmtCur (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (st : Stmt Op) : Prop :=
  ∀ (s : BState) (r : Option VMap) (s' : BState), CurValid s →
    trStmt fenv env lctx rets st s = some (r, s') →
      CurValid s' ∧ CurResult r s s'

def CasesCur (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (_sv : ValId) (_X : List Ident)
    (_joinId : BlockId) (cases : List (Literal × List (Stmt Op)))
    (dflt : Option (List (Stmt Op))) : Prop :=
  ∀ (sv : ValId) (X : List Ident) (joinId : BlockId) (s : BState) (u : Unit)
    (s' : BState), CurValid s →
    trCases fenv env lctx rets sv X joinId cases dflt s = some (u, s') →
      CurValid s' ∧ CurClosed s s'

omit model in
/-- A successful translation preserves current-id validity and records whether
its incoming block stayed open or was sealed.  `trFunc` is irrelevant to the
caller-current invariant because it restores the saved `FnState`; its motive is
therefore `True`, while the other four mutually recursive functions carry the
result-sensitive relation. -/
theorem trStmts_cur : ∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (d : Bool) (ss : List (Stmt Op)),
    StmtsCur fenv env lctx rets d ss := by
  refine trStmts.induct (fun _ _ _ _ => True) ScopeCur StmtsCur StmtCur CasesCur
    ?trFunc ?trScope ?stmtsNil ?stmtsFunDef ?stmtsSkip ?stmtsCons
    ?block ?funDef ?letNoneBad ?letNone ?letSomeBad ?letSome ?assignBad ?assign
    ?cond ?switch ?forLoop ?exprBuiltin ?exprCall ?exprBad
    ?breakNone ?breakSome ?contNone ?contSome ?leaveNone ?leaveSome
    ?casesNilNone ?casesNilSome ?casesCons
  case trFunc =>
    intro fenv ps rs body ih
    trivial
  case trScope =>
    intro fenv env lctx rets body ih s r s' hv h
    rw [trScope] at h
    obtain ⟨scope, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨renv, s₂, h2, h3⟩ := M.bind_inv h
    obtain ⟨hfn1, -⟩ := allocScope_funcsOnly h1
    have hv1 : CurValid s₁ := by rw [CurValid, hfn1]; exact hv
    obtain ⟨hv2, hk2⟩ := ih scope s₁ renv s₂ hv1 h2
    have hg2 := trStmts_grows (scope :: fenv) env lctx rets false body
      s₁ renv s₂ h2
    cases renv with
    | none =>
      obtain ⟨rfl, rfl⟩ := M.pure_inv h3
      refine ⟨hv2, ?_⟩
      exact CurOpen.transClosed hv (allocScope_sgrows h1)
        hg2 (Or.inl (CurSame.of_fnEq hfn1)) hk2
    | some env' =>
      obtain ⟨rfl, rfl⟩ := M.pure_inv h3
      refine ⟨hv2, ?_⟩
      exact CurOpen.trans hv (allocScope_sgrows h1)
        hg2 (Or.inl (CurSame.of_fnEq hfn1)) hk2
  case stmtsNil =>
    intro fenv env lctx rets d
    cases d <;> simp only [StmtsCur, Bool.false_eq_true, ↓reduceIte]
    intro s r s' hv h
    rw [trStmts] at h
    obtain ⟨rfl, rfl⟩ := M.pure_inv h
    exact ⟨hv, Or.inl (CurSame.rfl' _)⟩
  case stmtsFunDef =>
    intro fenv env lctx rets d n ps rs fbody rest ihf ihr
    cases d with
    | true => simp [StmtsCur]
    | false =>
      simp only [StmtsCur, Bool.false_eq_true, ↓reduceIte]
      intro s r s' hv h
      rw [trStmts] at h
      obtain ⟨fid, s₁, h1, h⟩ := M.bind_inv h
      obtain ⟨g, s₂, h2, h⟩ := M.bind_inv h
      obtain ⟨u, s₃, h3, h4⟩ := M.bind_inv h
      have hfn1 : s₁.fn = s.fn := congrArg BState.fn (M.liftO_inv h1).2
      have hfn2 : s₂.fn = s₁.fn := (trFunc_grows fenv ps rs fbody s₁ g s₂ h2).1
      have hfn3 : s₃.fn = s₂.fn := by rw [(M.fillFunc_inv h3).choose_spec]
      have hfn : s₃.fn = s.fn := hfn3.trans (hfn2.trans hfn1)
      have hv3 : CurValid s₃ := by rw [CurValid, hfn]; exact hv
      obtain ⟨hv', hk⟩ := ihr s₃ r s' hv3 h4
      have hgpre : SGrows s s₃ := ((SGrows.trans (SGrowsAt.of_liftO h1)
        (SGrowsAt.of_funcsOnly hfn2
          (trFunc_grows fenv ps rs fbody s₁ g s₂ h2).2)).trans
            (SGrowsAt.of_fillFunc h3))
      have hs : CurOpen s s₃ := Or.inl (CurSame.of_fnEq hfn)
      have hgtail := trStmts_grows fenv env lctx rets false rest s₃ r s' h4
      refine ⟨hv', ?_⟩
      cases r with
      | none => exact CurOpen.transClosed hv hgpre hgtail hs hk
      | some e => exact CurOpen.trans hv hgpre hgtail hs hk
  case stmtsSkip =>
    intro fenv env lctx rets st rest hnf ih
    simp [StmtsCur]
  case stmtsCons =>
    intro fenv env lctx rets d st rest hnf hd ih4 ih3n ih3t
    have hd0 : d = false := Bool.eq_false_of_not_eq_true hd
    subst d
    simp only [StmtsCur, Bool.false_eq_true, ↓reduceIte]
    intro s r s' hv h
    rw [trStmts] at h
    · rw [if_neg hd] at h
      obtain ⟨renv, s₁, h1, h2⟩ := M.bind_inv h
      obtain ⟨hv1, hk1⟩ := ih4 s renv s₁ hv h1
      have hg1 := trStmt_grows fenv env lctx rets st s renv s₁ h1
      cases renv with
      | some env' =>
        obtain ⟨hv2, hk2⟩ := ih3n env' s₁ r s' hv1 h2
        have hg2 := trStmts_grows fenv env' lctx rets false rest s₁ r s' h2
        refine ⟨hv2, ?_⟩
        cases r with
        | none => exact CurOpen.transClosed hv hg1 hg2 hk1 hk2
        | some e => exact CurOpen.trans hv hg1 hg2 hk1 hk2
      | none =>
        obtain ⟨hr, hfn⟩ := trStmts_true_fn fenv env lctx rets rest s₁ s' r h2
        subst r
        have hs : CurSame s₁ s' := CurSame.of_fnEq hfn
        have hg2 := trStmts_grows fenv env lctx rets true rest s₁ none s' h2
        exact ⟨by rw [CurValid, hfn]; exact hv1,
          CurClosed.transSame hv hg1 hg2 hk1 hs⟩
    · exact hnf
  case block =>
    intro fenv env lctx rets body ih s r s' hv h
    rw [trStmt] at h
    exact ih s r s' hv h
  case funDef =>
    intro fenv env lctx rets name ps rs body s r s' hv h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case letNoneBad =>
    intro fenv env lctx rets vars hgate s r s' hv h
    rw [trStmt, if_pos hgate] at h
    obtain ⟨u, s₁, h1, -⟩ := M.bind_inv h
    exact absurd h1 (by simp [reject])
  case letNone =>
    intro fenv env lctx rets vars hgate s r s' hv h
    rw [trStmt, if_neg hgate] at h
    obtain ⟨u, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s₂, h2, h3⟩ := M.bind_inv h
    obtain ⟨rfl, rfl⟩ := M.pure_inv h3
    have hg := (Grows.of_pure h1).trans (Grows.of_mapM_constZero h2)
    exact ⟨hv.of_grows hg, Or.inl (CurSame.of_grows hg)⟩
  case letSomeBad =>
    intro fenv env lctx rets vars e hgate s r s' hv h
    rw [trStmt, if_pos hgate] at h
    obtain ⟨u, s₁, h1, -⟩ := M.bind_inv h
    exact absurd h1 (by simp [reject])
  case letSome =>
    intro fenv env lctx rets vars e hgate s r s' hv h
    rw [trStmt, if_neg hgate] at h
    obtain ⟨u, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s₂, h2, h3⟩ := M.bind_inv h
    obtain ⟨rfl, rfl⟩ := M.pure_inv h3
    have hg := (Grows.of_pure h1).trans (trExprN_grows h2)
    exact ⟨hv.of_grows hg, Or.inl (CurSame.of_grows hg)⟩
  case assignBad =>
    intro fenv env lctx rets vars e hgate s r s' hv h
    rw [trStmt, if_pos hgate] at h
    obtain ⟨u, s₁, h1, -⟩ := M.bind_inv h
    exact absurd h1 (by simp [reject])
  case assign =>
    intro fenv env lctx rets vars e hgate s r s' hv h
    rw [trStmt, if_neg hgate] at h
    obtain ⟨u, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s₂, h2, h3⟩ := M.bind_inv h
    obtain ⟨rfl, rfl⟩ := M.pure_inv h3
    have hg := (Grows.of_pure h1).trans (trExprN_grows h2)
    exact ⟨hv.of_grows hg, Or.inl (CurSame.of_grows hg)⟩
  case cond =>
    intro fenv env lctx rets c body ih s r s' hv h
    rw [trStmt] at h
    obtain ⟨cv, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨xvals, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨bodyId, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨joinParams, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨joinId, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨u6, s6, h6, h⟩ := M.bind_inv h
    obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
    obtain ⟨renv, s8, h8, h⟩ := M.bind_inv h
    have g1 := trExpr_grows c fenv env s s1 cv h1
    have g2 := Grows.of_liftO h2
    have g4 := Grows.of_mapM_freshVal h4
    have cs5 := ((((CurSame.of_grows g1).trans (CurSame.of_grows g2)).trans
      (CurSame.of_newBlock h3)).trans (CurSame.of_grows g4)).trans
        (CurSame.of_newBlock h5)
    have a1 : SGrowsAt s.fn.blocks.size s s1 := SGrowsAt.of_grows g1
    have a2 := a1.trans (SGrowsAt.of_edgeArgs h2)
    have a3 := a2.trans (SGrowsAt.of_newBlock h3)
    have a4 := a3.trans (SGrowsAt.of_grows g4)
    have a5 := a4.trans (SGrowsAt.of_newBlock h5)
    have a6 := a5.trans (SGrowsAt.of_sealCur h6)
    have hbodyNe : s5.fn.curId ≠ bodyId := by
      rw [cs5.1, SGrowsAt.newBlock_id h3]
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hv a2.size)
    have hm57 := curMoved_of_seal_move hbodyNe h6 h7
    have hm : CurMoved s s7 := cs5.transMoved hm57
    have hbodyBase : s.fn.blocks.size ≤ bodyId := by
      rw [SGrowsAt.newBlock_id h3]
      exact a2.size
    have a7 := a6.trans (SGrowsAt.of_moveTo (Or.inl hbodyBase) h7)
    have hbodyLt : bodyId < s6.fn.blocks.size :=
      Nat.lt_of_lt_of_le (newBlock_target_lt h3)
        (((SGrowsAt.of_grows (N := 0) g4).trans
          (SGrowsAt.of_newBlock h5)).trans (SGrowsAt.of_sealCur h6)).size
    have hv7 := CurValid.of_moveTo hbodyLt h7
    obtain ⟨hv8, hk8⟩ := ih s7 renv s8 hv7 h8
    have gbody := trScope_grows fenv env lctx rets body s7 renv s8 h8
    have hjoinBase : s.fn.blocks.size ≤ joinId := by
      rw [SGrowsAt.newBlock_id h5]
      exact a4.size
    cases renv with
    | none =>
      obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, hc2⟩ := M.bind_inv h
      obtain ⟨-, rfl⟩ := M.pure_inv ha
      obtain ⟨rfl, rfl⟩ := M.pure_inv hc2
      have g5a : SGrowsAt 0 s5 sa := ((SGrowsAt.of_sealCur h6).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h7)).trans
          (gbody.mono (Nat.zero_le _))
      have hjoinLt : joinId < sa.fn.blocks.size :=
        Nat.lt_of_lt_of_le (newBlock_target_lt h5) g5a.size
      have hv' := CurValid.of_moveTo hjoinLt hb2
      have gb : SGrowsAt s.fn.blocks.size s7 s' :=
        (gbody.mono a7.size).trans (SGrowsAt.of_moveTo (Or.inl hjoinBase) hb2)
      exact ⟨hv', Or.inr (hm.forward hv a7 gb)⟩
    | some env' =>
      obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
      obtain ⟨uc, sc, hc2, hd2⟩ := M.bind_inv h
      obtain ⟨rfl, rfl⟩ := M.pure_inv hd2
      have g5sb : SGrowsAt 0 s5 sb := (((SGrowsAt.of_sealCur h6).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h7)).trans
          (gbody.mono (Nat.zero_le _))).trans
            ((SGrowsAt.of_edgeArgs ha).trans (SGrowsAt.of_sealCur hb2))
      have hjoinLt : joinId < sb.fn.blocks.size :=
        Nat.lt_of_lt_of_le (newBlock_target_lt h5) g5sb.size
      have hv' := CurValid.of_moveTo hjoinLt hc2
      have gb : SGrowsAt s.fn.blocks.size s7 s' :=
        (((gbody.mono a7.size).trans (SGrowsAt.of_edgeArgs ha)).trans
          (SGrowsAt.of_sealCur hb2)).trans
            (SGrowsAt.of_moveTo (Or.inl hjoinBase) hc2)
      exact ⟨hv', Or.inr (hm.forward hv a7 gb)⟩
  case switch =>
    intro fenv env lctx rets c cases dflt ih s r s' hv h
    unfold trStmt at h
    obtain ⟨sv, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨joinParams, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨joinId, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨u5, s5, h5, h6⟩ := M.bind_inv h
    have g1 := trExpr_grows c fenv env s s1 sv h1
    have g2 := Grows.of_mapM_freshVal h2
    have cs3 := ((CurSame.of_grows g1).trans (CurSame.of_grows g2)).trans
      (CurSame.of_newBlock h3)
    have a1 : SGrowsAt s.fn.blocks.size s s1 := SGrowsAt.of_grows g1
    have a2 := a1.trans (SGrowsAt.of_grows g2)
    have a3 := a2.trans (SGrowsAt.of_newBlock h3)
    have hv3 := CurValid.of_same_sgrows hv a3 cs3.1
    have hh : CurValid s4 ∧ CurClosed s3 s4 := by
      apply ih 0 0
      · exact hv3
      · exact h4
    obtain ⟨hv4, hk4⟩ := hh
    have gcases : SGrows s3 s4 := by
      apply trCases_grows fenv env lctx rets 0 [] 0 cases dflt
      exact h4
    have hjoinBase : s.fn.blocks.size ≤ joinId := by
      rw [SGrowsAt.newBlock_id h3]
      exact a2.size
    have g3s4 : SGrowsAt 0 s3 s4 := gcases.mono (Nat.zero_le _)
    have hjoinLt : joinId < s4.fn.blocks.size :=
      Nat.lt_of_lt_of_le (newBlock_target_lt h3) g3s4.size
    have hv5 := CurValid.of_moveTo hjoinLt h5
    rcases hk4 with hm | hs
    · have hm0 : CurMoved s s4 := cs3.transMoved hm
      have a4 := a3.trans (gcases.mono a3.size)
      have hout : CurOpen s s5 := Or.inr (hm0.forward hv a4
        (SGrowsAt.of_moveTo (Or.inl hjoinBase) h5))
      obtain ⟨rfl, rfl⟩ := M.pure_inv h6
      exact ⟨hv5, hout⟩
    · have hm35 : CurMoved s3 s5 := by
        rcases hs with ⟨hc, b, hb, Δ, hi⟩
        rw [M.moveTo_apply] at h5
        obtain ⟨rfl, rfl⟩ := M.some_pair_inj h5
        have hne : s3.fn.curId ≠ joinId := by
          rw [cs3.1, SGrowsAt.newBlock_id h3]
          exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hv a2.size)
        exact ⟨hne, b, by simpa only [hc] using hb, Δ, hi⟩
      have hout : CurOpen s s5 := Or.inr (cs3.transMoved hm35)
      obtain ⟨rfl, rfl⟩ := M.pure_inv h6
      exact ⟨hv5, hout⟩
  case forLoop =>
    intro fenv env lctx rets init c post body ihInit ihBody ihPost s r s' hv h
    unfold trStmt at h
    obtain ⟨scope, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨rinit, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨hfn1, -⟩ := allocScope_funcsOnly h1
    have hv1 : CurValid s1 := by rw [CurValid, hfn1]; exact hv
    obtain ⟨hv2, hk2⟩ := ihInit scope s1 rinit s2 hv1 h2
    have a1 : SGrows s s1 := allocScope_sgrows h1
    have gi := trStmts_grows (scope :: fenv) env lctx rets false init
      s1 rinit s2 h2
    have a2 := a1.trans gi
    cases rinit with
    | none =>
      obtain ⟨rfl, rfl⟩ := M.pure_inv h
      exact ⟨hv2, CurOpen.transClosed hv a1 gi
        (Or.inl (CurSame.of_fnEq hfn1)) hk2⟩
    | some envI =>
      obtain ⟨xvals, s3, h3, h⟩ := M.bind_inv h
      obtain ⟨hParams, s4, h4, h⟩ := M.bind_inv h
      obtain ⟨hId, s5, h5, h⟩ := M.bind_inv h
      obtain ⟨exitParams, s6, h6, h⟩ := M.bind_inv h
      obtain ⟨exitId, s7, h7, h⟩ := M.bind_inv h
      obtain ⟨postParams, s8, h8, h⟩ := M.bind_inv h
      obtain ⟨postId, s9, h9, h⟩ := M.bind_inv h
      obtain ⟨u10, s10, h10, h⟩ := M.bind_inv h
      obtain ⟨u11, s11, h11, h⟩ := M.bind_inv h
      obtain ⟨cv, s12, h12, h⟩ := M.bind_inv h
      obtain ⟨bodyId, s13, h13, h⟩ := M.bind_inv h
      obtain ⟨hX, s14, h14, h⟩ := M.bind_inv h
      obtain ⟨u15, s15, h15, h⟩ := M.bind_inv h
      obtain ⟨u16, s16, h16, h⟩ := M.bind_inv h
      obtain ⟨renvB, s17, h17, h⟩ := M.bind_inv h
      have hopen2 : CurOpen s s2 := CurOpen.trans hv a1 gi
        (Or.inl (CurSame.of_fnEq hfn1)) hk2
      have g3 := Grows.of_liftO h3
      have g4 := Grows.of_mapM_freshVal h4
      have g6 := Grows.of_mapM_freshVal h6
      have g8 := Grows.of_mapM_freshVal h8
      have cs9 := ((((((CurSame.of_grows g3).trans (CurSame.of_grows g4)).trans
        (CurSame.of_newBlock h5)).trans (CurSame.of_grows g6)).trans
          (CurSame.of_newBlock h7)).trans (CurSame.of_grows g8)).trans
            (CurSame.of_newBlock h9)
      have b3 : SGrowsAt s2.fn.blocks.size s2 s3 := SGrowsAt.of_grows g3
      have b4 := b3.trans (SGrowsAt.of_grows g4)
      have b5 := b4.trans (SGrowsAt.of_newBlock h5)
      have b6 := b5.trans (SGrowsAt.of_grows g6)
      have b7 := b6.trans (SGrowsAt.of_newBlock h7)
      have b8 := b7.trans (SGrowsAt.of_grows g8)
      have b9 := b8.trans (SGrowsAt.of_newBlock h9)
      have b10 := b9.trans (SGrowsAt.of_sealCur h10)
      have hheadNe : s9.fn.curId ≠ hId := by
        rw [cs9.1, SGrowsAt.newBlock_id h5]
        exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hv2 b4.size)
      have hm911 := curMoved_of_seal_move hheadNe h10 h11
      have hm2 : CurMoved s2 s11 := cs9.transMoved hm911
      have hhead2 : s2.fn.blocks.size ≤ hId := by
        rw [SGrowsAt.newBlock_id h5]
        exact b4.size
      have b11 := b10.trans (SGrowsAt.of_moveTo (Or.inl hhead2) h11)
      have hm : CurMoved s s11 := hopen2.transMoved hv a2 b11 hm2
      have a11 := a2.trans b11
      have hheadLt : hId < s10.fn.blocks.size :=
        Nat.lt_of_lt_of_le (newBlock_target_lt h5)
          (((((SGrowsAt.of_grows (N := 0) g6).trans
            (SGrowsAt.of_newBlock h7)).trans (SGrowsAt.of_grows g8)).trans
              (SGrowsAt.of_newBlock h9)).trans (SGrowsAt.of_sealCur h10)).size
      have hv11 := CurValid.of_moveTo hheadLt h11
      have gc := trExpr_grows c (scope :: fenv) _ s11 s12 cv h12
      have hv12 := hv11.of_grows gc
      have hv13 := CurValid.of_same_sgrows hv12
        (SGrowsAt.of_newBlock (N := s12.fn.blocks.size) h13)
        (CurSame.of_newBlock h13).1
      have hv14 := hv13.of_grows (Grows.of_liftO h14)
      have hs15 := curSealed_of_sealCur h15
      have hv15 := CurValid.of_same_sgrows hv14
        (SGrowsAt.of_sealCur (N := s14.fn.blocks.size) h15) hs15.1
      have hbodyLt : bodyId < s15.fn.blocks.size :=
        Nat.lt_of_lt_of_le (newBlock_target_lt h13)
          ((SGrowsAt.of_edgeArgs (N := 0) h14).trans
            (SGrowsAt.of_sealCur h15)).size
      have hv16 := CurValid.of_moveTo hbodyLt h16
      obtain ⟨hv17, hk17⟩ := ihBody scope envI hParams exitId postId
        s16 renvB s17 hv16 h17
      have gBody := trScope_grows (scope :: fenv) _ (some ⟨exitId, postId, _⟩)
        rets body s16 renvB s17 h17
      have hbodyBase : s.fn.blocks.size ≤ bodyId := by
        rw [SGrowsAt.newBlock_id h13]
        exact (a11.trans (SGrowsAt.of_grows gc)).size
      have q16 : SGrowsAt s.fn.blocks.size s11 s16 := ((((
        SGrowsAt.of_grows gc).trans (SGrowsAt.of_newBlock h13)).trans
          (SGrowsAt.of_edgeArgs h14)).trans (SGrowsAt.of_sealCur h15)).trans
            (SGrowsAt.of_moveTo (Or.inl hbodyBase) h16)
      have a16 : SGrowsAt s.fn.blocks.size s s16 := SGrowsAt.trans a11 q16
      have g7s11 : SGrowsAt 0 s7 s11 := ((SGrowsAt.of_grows g8).trans
        (SGrowsAt.of_newBlock h9)).trans ((SGrowsAt.of_sealCur h10).trans
          (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h11))
      have g11s16z : SGrowsAt 0 s11 s16 := ((((SGrowsAt.of_grows gc).trans
        (SGrowsAt.of_newBlock h13)).trans (SGrowsAt.of_edgeArgs h14)).trans
          (SGrowsAt.of_sealCur h15)).trans
            (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h16)
      have hpostBase : s.fn.blocks.size ≤ postId := by
        rw [SGrowsAt.newBlock_id h9]
        exact (a2.trans b8).size
      have hexitBase : s.fn.blocks.size ≤ exitId := by
        rw [SGrowsAt.newBlock_id h7]
        exact (a2.trans b6).size
      cases renvB with
      | none =>
        obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
        obtain ⟨renvP, sc, hc2, h⟩ := M.bind_inv h
        obtain ⟨-, rfl⟩ := M.pure_inv ha
        have g9s11 : SGrowsAt 0 s9 s11 := (SGrowsAt.of_sealCur h10).trans
          (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h11)
        have g9sa : SGrowsAt 0 s9 sa := (g9s11.trans g11s16z).trans
          (gBody.mono (Nat.zero_le _))
        have hpostLt : postId < sa.fn.blocks.size :=
          Nat.lt_of_lt_of_le (newBlock_target_lt h9) g9sa.size
        have hvb := CurValid.of_moveTo hpostLt hb2
        obtain ⟨hvc, hkc⟩ := ihPost scope envI postParams sb renvP sc hvb hc2
        have gPost := trScope_grows (scope :: fenv) _ none rets post
          sb renvP sc hc2
        have qBody : SGrowsAt s.fn.blocks.size s16 sa :=
          gBody.mono a16.size
        have qPostIn : SGrowsAt s.fn.blocks.size s11 sb :=
          (q16.trans qBody).trans (SGrowsAt.of_moveTo (Or.inl hpostBase) hb2)
        cases renvP with
        | none =>
          obtain ⟨ud, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, hf⟩ := M.bind_inv h
          obtain ⟨-, rfl⟩ := M.pure_inv hd
          obtain ⟨rfl, rfl⟩ := M.pure_inv hf
          have g7sd : SGrowsAt 0 s7 sd := (g7s11.trans g11s16z).trans
            (((gBody.mono (Nat.zero_le _)).trans
              (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) hb2)).trans
                (gPost.mono (Nat.zero_le _)))
          have hexitLt : exitId < sd.fn.blocks.size :=
            Nat.lt_of_lt_of_le (newBlock_target_lt h7) g7sd.size
          have hv' := CurValid.of_moveTo hexitLt he
          have qFinal := (qPostIn.trans (gPost.mono
            (Nat.le_trans a11.size qPostIn.size))).trans
            (SGrowsAt.of_moveTo (Or.inl hexitBase) he)
          exact ⟨hv', Or.inr (hm.forward hv a11 qFinal)⟩
        | some envP' =>
          obtain ⟨xvP, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, h⟩ := M.bind_inv h
          obtain ⟨uf, sf, hf, hg2⟩ := M.bind_inv h
          obtain ⟨rfl, rfl⟩ := M.pure_inv hg2
          have g16se : SGrowsAt 0 s16 se := ((((gBody.mono (Nat.zero_le _)).trans
            (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) hb2)).trans
              (gPost.mono (Nat.zero_le _))).trans
                (SGrowsAt.of_edgeArgs hd)).trans (SGrowsAt.of_sealCur he)
          have g7se : SGrowsAt 0 s7 se := (g7s11.trans g11s16z).trans g16se
          have hexitLt : exitId < se.fn.blocks.size :=
            Nat.lt_of_lt_of_le (newBlock_target_lt h7) g7se.size
          have hv' := CurValid.of_moveTo hexitLt hf
          have qFinal := (((qPostIn.trans (gPost.mono
            (Nat.le_trans a11.size qPostIn.size))).trans
              (SGrowsAt.of_edgeArgs hd)).trans (SGrowsAt.of_sealCur he)).trans
                (SGrowsAt.of_moveTo (Or.inl hexitBase) hf)
          exact ⟨hv', Or.inr (hm.forward hv a11 qFinal)⟩
      | some envB =>
        obtain ⟨xvB, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ua', sa', ha', h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
        obtain ⟨renvP, sc, hc2, h⟩ := M.bind_inv h
        have g9s11 : SGrowsAt 0 s9 s11 := (SGrowsAt.of_sealCur h10).trans
          (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h11)
        have gBodyClosed0 : SGrowsAt 0 s16 sa' :=
          ((gBody.mono (Nat.zero_le _)).trans (SGrowsAt.of_edgeArgs ha)).trans
            (SGrowsAt.of_sealCur ha')
        have g9sa' : SGrowsAt 0 s9 sa' := (g9s11.trans g11s16z).trans
          gBodyClosed0
        have hpostLt : postId < sa'.fn.blocks.size :=
          Nat.lt_of_lt_of_le (newBlock_target_lt h9) g9sa'.size
        have hvb := CurValid.of_moveTo hpostLt hb2
        obtain ⟨hvc, hkc⟩ := ihPost scope envI postParams sb renvP sc hvb hc2
        have gPost := trScope_grows (scope :: fenv) _ none rets post
          sb renvP sc hc2
        have qBody : SGrowsAt s.fn.blocks.size s16 s17 :=
          gBody.mono a16.size
        have qPostIn : SGrowsAt s.fn.blocks.size s11 sb := ((((q16.trans qBody).trans
          (SGrowsAt.of_edgeArgs ha)).trans (SGrowsAt.of_sealCur ha')).trans
            (SGrowsAt.of_moveTo (Or.inl hpostBase) hb2))
        cases renvP with
        | none =>
          obtain ⟨ud, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, hf⟩ := M.bind_inv h
          obtain ⟨-, rfl⟩ := M.pure_inv hd
          obtain ⟨rfl, rfl⟩ := M.pure_inv hf
          have g7sd : SGrowsAt 0 s7 sd := (g7s11.trans g11s16z).trans
            ((gBodyClosed0.trans
              (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) hb2)).trans
                (gPost.mono (Nat.zero_le _)))
          have hexitLt : exitId < sd.fn.blocks.size :=
            Nat.lt_of_lt_of_le (newBlock_target_lt h7) g7sd.size
          have hv' := CurValid.of_moveTo hexitLt he
          have qFinal := (qPostIn.trans (gPost.mono
            (Nat.le_trans a11.size qPostIn.size))).trans
            (SGrowsAt.of_moveTo (Or.inl hexitBase) he)
          exact ⟨hv', Or.inr (hm.forward hv a11 qFinal)⟩
        | some envP' =>
          obtain ⟨xvP, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, h⟩ := M.bind_inv h
          obtain ⟨uf, sf, hf, hg2⟩ := M.bind_inv h
          obtain ⟨rfl, rfl⟩ := M.pure_inv hg2
          have g16se : SGrowsAt 0 s16 se := (((gBodyClosed0.trans
            (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) hb2)).trans
              (gPost.mono (Nat.zero_le _))).trans
                (SGrowsAt.of_edgeArgs hd)).trans (SGrowsAt.of_sealCur he)
          have g7se : SGrowsAt 0 s7 se := (g7s11.trans g11s16z).trans g16se
          have hexitLt : exitId < se.fn.blocks.size :=
            Nat.lt_of_lt_of_le (newBlock_target_lt h7) g7se.size
          have hv' := CurValid.of_moveTo hexitLt hf
          have qFinal := (((qPostIn.trans (gPost.mono
            (Nat.le_trans a11.size qPostIn.size))).trans
              (SGrowsAt.of_edgeArgs hd)).trans (SGrowsAt.of_sealCur he)).trans
                (SGrowsAt.of_moveTo (Or.inl hexitBase) hf)
          exact ⟨hv', Or.inr (hm.forward hv a11 qFinal)⟩
  case exprBuiltin =>
    intro fenv env lctx rets op args s r s' hv h
    rw [trStmt] at h
    obtain ⟨as, s₁, h1, h⟩ := M.bind_inv h
    have hg1 := trArgs_grows args fenv env s s₁ as h1
    by_cases hop : isHaltingOp op = true
    · rw [if_pos hop] at h
      obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
      obtain ⟨rfl, rfl⟩ := M.pure_inv h3
      have hseal := curSealed_of_sealCur h2
      refine ⟨CurValid.of_same_sgrows (hv.of_grows hg1)
        (SGrowsAt.of_sealCur (N := s₁.fn.blocks.size) h2) hseal.1, Or.inr ?_⟩
      rcases hseal with ⟨hc, b, hb, Δ, hi⟩
      rcases CurSame.of_grows hg1 with ⟨hc1, ⟨Δ1, hi1⟩, -⟩
      refine ⟨hc.trans hc1, b, by simpa only [hc1] using hb,
        Δ1.reverse ++ Δ, ?_⟩
      rw [hi, hi1]
      simp
    · rw [if_neg hop] at h
      obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
      obtain ⟨rfl, rfl⟩ := M.pure_inv h3
      have hg := hg1.trans (Grows.of_emit h2)
      exact ⟨hv.of_grows hg, Or.inl (CurSame.of_grows hg)⟩
  case exprCall =>
    intro fenv env lctx rets fn args s r s' hv h
    rw [trStmt] at h
    obtain ⟨as, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨fid, s₂, h2, h⟩ := M.bind_inv h
    obtain ⟨u, s₃, h3, h4⟩ := M.bind_inv h
    obtain ⟨rfl, rfl⟩ := M.pure_inv h4
    have hg := (trArgs_grows args fenv env s s₁ as h1).trans
      ((Grows.of_liftO h2).trans (Grows.of_emit h3))
    exact ⟨hv.of_grows hg, Or.inl (CurSame.of_grows hg)⟩
  case exprBad =>
    intro fenv env lctx rets e hnb hnc s r s' hv h
    rw [trStmt] at h
    · exact absurd h (by simp [reject])
    · exact hnb
    · exact hnc
  case breakNone =>
    intro fenv env rets s r s' hv h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case breakSome =>
    intro fenv env rets l s r s' hv h
    rw [trStmt] at h
    obtain ⟨vals, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    obtain ⟨rfl, rfl⟩ := M.pure_inv h3
    have hg1 := Grows.of_liftO h1
    have hs := curSealed_of_sealCur h2
    refine ⟨CurValid.of_same_sgrows (hv.of_grows hg1)
      (SGrowsAt.of_sealCur (N := s₁.fn.blocks.size) h2) hs.1, Or.inr ?_⟩
    rcases hs with ⟨hc, b, hb, Δ, hi⟩
    rcases CurSame.of_grows hg1 with ⟨hc1, ⟨Δ1, hi1⟩, -⟩
    refine ⟨hc.trans hc1, b, by simpa only [hc1] using hb,
      Δ1.reverse ++ Δ, ?_⟩
    rw [hi, hi1]
    simp
  case contNone =>
    intro fenv env rets s r s' hv h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case contSome =>
    intro fenv env rets l s r s' hv h
    rw [trStmt] at h
    obtain ⟨vals, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    obtain ⟨rfl, rfl⟩ := M.pure_inv h3
    have hg1 := Grows.of_liftO h1
    have hs := curSealed_of_sealCur h2
    refine ⟨CurValid.of_same_sgrows (hv.of_grows hg1)
      (SGrowsAt.of_sealCur (N := s₁.fn.blocks.size) h2) hs.1, Or.inr ?_⟩
    rcases hs with ⟨hc, b, hb, Δ, hi⟩
    rcases CurSame.of_grows hg1 with ⟨hc1, ⟨Δ1, hi1⟩, -⟩
    refine ⟨hc.trans hc1, b, by simpa only [hc1] using hb,
      Δ1.reverse ++ Δ, ?_⟩
    rw [hi, hi1]
    simp
  case leaveNone =>
    intro fenv env lctx s r s' hv h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case leaveSome =>
    intro fenv env lctx rs s r s' hv h
    rw [trStmt] at h
    obtain ⟨vals, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    obtain ⟨rfl, rfl⟩ := M.pure_inv h3
    have hg1 := Grows.of_liftO h1
    have hs := curSealed_of_sealCur h2
    refine ⟨CurValid.of_same_sgrows (hv.of_grows hg1)
      (SGrowsAt.of_sealCur (N := s₁.fn.blocks.size) h2) hs.1, Or.inr ?_⟩
    rcases hs with ⟨hc, b, hb, Δ, hi⟩
    rcases CurSame.of_grows hg1 with ⟨hc1, ⟨Δ1, hi1⟩, -⟩
    refine ⟨hc.trans hc1, b, by simpa only [hc1] using hb,
      Δ1.reverse ++ Δ, ?_⟩
    rw [hi, hi1]
    simp
  case casesNilNone =>
    intro fenv env lctx rets _sv _X _joinId sv X joinId s u s' hv h
    rw [trCases] at h
    obtain ⟨xvals, s₁, h1, h2⟩ := M.bind_inv h
    have hg1 := Grows.of_liftO h1
    have hs := curSealed_of_sealCur h2
    refine ⟨CurValid.of_same_sgrows (hv.of_grows hg1)
      (SGrowsAt.of_sealCur (N := s₁.fn.blocks.size) h2) hs.1, Or.inr ?_⟩
    rcases hs with ⟨hc, b, hb, Δ, hi⟩
    rcases CurSame.of_grows hg1 with ⟨hc1, ⟨Δ1, hi1⟩, -⟩
    refine ⟨hc.trans hc1, b, by simpa only [hc1] using hb,
      Δ1.reverse ++ Δ, ?_⟩
    rw [hi, hi1]
    simp
  case casesNilSome =>
    intro fenv env lctx rets _sv _X _joinId dbody ih sv X joinId s u s' hv h
    rw [trCases] at h
    obtain ⟨renv, s₁, h1, h2⟩ := M.bind_inv h
    obtain ⟨hv1, hk1⟩ := ih s renv s₁ hv h1
    have hg1 := trScope_grows fenv env lctx rets dbody s renv s₁ h1
    cases renv with
    | none =>
      obtain ⟨rfl, rfl⟩ := M.pure_inv h2
      exact ⟨hv1, hk1⟩
    | some env' =>
      obtain ⟨xv, s₂, h3, h4⟩ := M.bind_inv h2
      have hgE := Grows.of_liftO h3
      have hs := curSealed_of_sealCur h4
      have hv2 := hv1.of_grows hgE
      have hv' := CurValid.of_same_sgrows hv2
        (SGrowsAt.of_sealCur (N := s₂.fn.blocks.size) h4) hs.1
      have hclosed : CurClosed s₁ s' := by
        refine Or.inr ?_
        rcases hs with ⟨hc, b, hb, Δ, hi⟩
        rcases CurSame.of_grows hgE with ⟨hc1, ⟨Δ1, hi1⟩, -⟩
        refine ⟨hc.trans hc1, b, by simpa only [hc1] using hb,
          Δ1.reverse ++ Δ, ?_⟩
        rw [hi, hi1]
        simp
      exact ⟨hv', CurOpen.transClosed hv hg1
        (SGrows.trans (SGrows.of_grows hgE) (SGrowsAt.of_sealCur h4))
        hk1 hclosed⟩
  case casesCons =>
    intro fenv env lctx rets _sv _X _joinId lit cbody restCases dflt ihc ihr
      sv X joinId s u s' hv h
    rw [trCases] at h
    obtain ⟨t, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨u2, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨e, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨caseId, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨nextId, s6, h6, h⟩ := M.bind_inv h
    obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
    obtain ⟨u8, s8, h8, h⟩ := M.bind_inv h
    obtain ⟨renv, s9, h9, h⟩ := M.bind_inv h
    have g1 := Grows.of_freshVal h1
    have g2 := Grows.of_emit h2
    have g3 := Grows.of_freshVal h3
    have g4 := Grows.of_emit h4
    have cs4 := (((CurSame.of_grows g1).trans (CurSame.of_grows g2)).trans
      (CurSame.of_grows g3)).trans (CurSame.of_grows g4)
    have cs5 := cs4.trans (CurSame.of_newBlock h5)
    have cs6 := cs5.trans (CurSame.of_newBlock h6)
    have a1 : SGrowsAt s.fn.blocks.size s s1 := SGrowsAt.of_grows g1
    have a2 := a1.trans (SGrowsAt.of_grows g2)
    have a3 := a2.trans (SGrowsAt.of_grows g3)
    have a4 := a3.trans (SGrowsAt.of_grows g4)
    have a5 := a4.trans (SGrowsAt.of_newBlock h5)
    have a6 := a5.trans (SGrowsAt.of_newBlock h6)
    have a7 := a6.trans (SGrowsAt.of_sealCur h7)
    have hcaseNe : s6.fn.curId ≠ caseId := by
      have hid := SGrowsAt.newBlock_id h5
      rw [cs6.1, hid]
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hv a4.size)
    have hm68 : CurMoved s6 s8 := curMoved_of_seal_move hcaseNe h7 h8
    have hm : CurMoved s s8 := cs6.transMoved hm68
    have a8 := a7.trans (SGrowsAt.of_moveTo
      (Or.inl (by rw [SGrowsAt.newBlock_id h5]; exact a4.size)) h8)
    have hcaseLt : caseId < s7.fn.blocks.size := by
      exact Nat.lt_of_lt_of_le (newBlock_target_lt h5)
        ((SGrowsAt.of_newBlock (N := 0) h6).trans
          (SGrowsAt.of_sealCur h7)).size
    have hv8 : CurValid s8 := CurValid.of_moveTo hcaseLt h8
    obtain ⟨hv9, hk9⟩ := ihc s8 renv s9 hv8 h9
    have gbody := trScope_grows fenv env lctx rets cbody s8 renv s9 h9
    cases renv with
    | none =>
      obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, hc2⟩ := M.bind_inv h
      obtain ⟨-, rfl⟩ := M.pure_inv ha
      have g6a : SGrowsAt 0 s6 sa := ((SGrowsAt.of_sealCur h7).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h8)).trans
          (gbody.mono (Nat.zero_le _))
      have hnextLt : nextId < sa.fn.blocks.size :=
        Nat.lt_of_lt_of_le (newBlock_target_lt h6) g6a.size
      have hvb : CurValid sb := CurValid.of_moveTo hnextLt hb2
      obtain ⟨hv', hkrest⟩ := ihr sv X joinId sb u s' hvb hc2
      have hnextBase : s.fn.blocks.size ≤ nextId := by
        rw [SGrowsAt.newBlock_id h6]
        exact a5.size
      have gb : SGrowsAt s.fn.blocks.size s8 sb :=
        (gbody.mono a8.size).trans
          (SGrowsAt.of_moveTo (Or.inl hnextBase) hb2)
      have gr := trCases_grows fenv env lctx rets sv X joinId restCases dflt
        sv X joinId sb u s' hc2
      exact ⟨hv', Or.inl (hm.forward hv a8
        (gb.trans (gr.mono (Nat.le_trans a8.size gb.size))))⟩
    | some env' =>
      obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
      obtain ⟨uc, sc, hc2, hd2⟩ := M.bind_inv h
      have g6sb : SGrowsAt 0 s6 sb := (((SGrowsAt.of_sealCur h7).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h8)).trans
          (gbody.mono (Nat.zero_le _))).trans
            ((SGrowsAt.of_edgeArgs ha).trans (SGrowsAt.of_sealCur hb2))
      have hnextLt : nextId < sb.fn.blocks.size :=
        Nat.lt_of_lt_of_le (newBlock_target_lt h6) g6sb.size
      have hvc : CurValid sc := CurValid.of_moveTo hnextLt hc2
      obtain ⟨hv', hkrest⟩ := ihr sv X joinId sc u s' hvc hd2
      have hnextBase : s.fn.blocks.size ≤ nextId := by
        rw [SGrowsAt.newBlock_id h6]
        exact a5.size
      have gb : SGrowsAt s.fn.blocks.size s8 sc :=
        (((gbody.mono a8.size).trans (SGrowsAt.of_edgeArgs ha)).trans
          (SGrowsAt.of_sealCur hb2)).trans
            (SGrowsAt.of_moveTo (Or.inl hnextBase) hc2)
      have gr := trCases_grows fenv env lctx rets sv X joinId restCases dflt
        sv X joinId sc u s' hd2
      exact ⟨hv', Or.inl (hm.forward hv a8
        (gb.trans (gr.mono (Nat.le_trans a8.size gb.size))))⟩

omit model in
/-- A diverting scope has no pending instructions in its current block.

This is deliberately separate from `CurResult`: the latter records how the
*incoming* block is preserved, whereas this fact is about the output selected
by a later structured-control `moveTo`. -/
theorem trScope_none_cur_nil : ∀ (fenv : FMap) (env : VMap)
    (lctx : Option LoopCtx) (rets : Option (List Ident))
    (body : List (Stmt Op)) (s s' : BState),
    trScope fenv env lctx rets body s = some (none, s') → s'.fn.cur = [] := by
  let ScopeNil := fun (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (body : List (Stmt Op)) =>
      ∀ (s s' : BState),
        trScope fenv env lctx rets body s = some (none, s') → s'.fn.cur = []
  let StmtsNil := fun (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (d : Bool) (ss : List (Stmt Op)) =>
      if d then True else ∀ (s s' : BState),
        trStmts fenv env lctx rets d ss s = some (none, s') → s'.fn.cur = []
  let StmtNil := fun (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (st : Stmt Op) =>
      ∀ (s s' : BState),
        trStmt fenv env lctx rets st s = some (none, s') → s'.fn.cur = []
  have hall : ∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
      (rets : Option (List Ident)) (d : Bool) (body : List (Stmt Op)),
      StmtsNil fenv env lctx rets d body := by
    refine trStmts.induct (fun _ _ _ _ => True) ScopeNil StmtsNil StmtNil
      (fun _ _ _ _ _ _ _ _ _ => True)
      ?trFunc ?trScope ?stmtsNil ?stmtsFunDef ?stmtsSkip ?stmtsCons
      ?block ?funDef ?letNoneBad ?letNone ?letSomeBad ?letSome ?assignBad ?assign
      ?cond ?switch ?forLoop ?exprBuiltin ?exprCall ?exprBad
      ?breakNone ?breakSome ?contNone ?contSome ?leaveNone ?leaveSome
      ?casesNilNone ?casesNilSome ?casesCons
    case trFunc => intros; trivial
    case trScope =>
      intro fenv env lctx rets body ih s s' h
      rw [trScope] at h
      obtain ⟨scope, s1, h1, h⟩ := M.bind_inv h
      obtain ⟨renv, s2, h2, h3⟩ := M.bind_inv h
      cases renv with
      | none =>
        obtain ⟨-, hs⟩ := M.pure_inv h3
        rw [hs]
        exact ih scope s1 s2 h2
      | some env' => exact absurd h3 (by simp)
    case stmtsNil =>
      intro fenv env lctx rets d
      cases d <;> simp only [StmtsNil, Bool.false_eq_true, ↓reduceIte]
      intro s s' h
      rw [trStmts] at h
      exact absurd h (by simp)
    case stmtsFunDef =>
      intro fenv env lctx rets d n ps rs fbody rest ihf ihr
      cases d with
      | true => simp [StmtsNil]
      | false =>
        simp only [StmtsNil, Bool.false_eq_true, ↓reduceIte]
        intro s s' h
        rw [trStmts] at h
        obtain ⟨fid, s1, h1, h⟩ := M.bind_inv h
        obtain ⟨g, s2, h2, h⟩ := M.bind_inv h
        obtain ⟨u, s3, h3, h4⟩ := M.bind_inv h
        exact ihr s3 s' h4
    case stmtsSkip => intros; simp [StmtsNil]
    case stmtsCons =>
      intro fenv env lctx rets d st rest hnf hd ihs ihr0 ihr1
      have hd0 : d = false := Bool.eq_false_of_not_eq_true hd
      subst d
      simp only [StmtsNil, Bool.false_eq_true, ↓reduceIte]
      intro s s' h
      rw [trStmts] at h
      · rw [if_neg hd] at h
        obtain ⟨renv, s1, h1, h2⟩ := M.bind_inv h
        cases renv with
        | some env' => exact ihr0 env' s1 s' h2
        | none =>
          obtain ⟨-, hfn⟩ := trStmts_true_fn fenv env lctx rets rest
            s1 s' none h2
          rw [hfn]
          exact ihs s s1 h1
      · exact hnf
    case block =>
      intro fenv env lctx rets body ih s s' h
      rw [trStmt] at h
      exact ih s s' h
    case funDef =>
      intro fenv env lctx rets name ps rs body s s' h
      rw [trStmt] at h
      exact absurd h (by simp [reject])
    case letNoneBad =>
      intro fenv env lctx rets vars hgate s s' h
      rw [trStmt, if_pos hgate] at h
      obtain ⟨u, s1, h1, -⟩ := M.bind_inv h
      exact absurd h1 (by simp [reject])
    case letNone =>
      intro fenv env lctx rets vars hgate s s' h
      rw [trStmt, if_neg hgate] at h
      obtain ⟨u, s1, h1, h⟩ := M.bind_inv h
      obtain ⟨ids, s2, h2, h3⟩ := M.bind_inv h
      exact absurd h3 (by simp)
    case letSomeBad =>
      intro fenv env lctx rets vars e hgate s s' h
      rw [trStmt, if_pos hgate] at h
      obtain ⟨u, s1, h1, -⟩ := M.bind_inv h
      exact absurd h1 (by simp [reject])
    case letSome =>
      intro fenv env lctx rets vars e hgate s s' h
      rw [trStmt, if_neg hgate] at h
      obtain ⟨u, s1, h1, h⟩ := M.bind_inv h
      obtain ⟨ids, s2, h2, h3⟩ := M.bind_inv h
      exact absurd h3 (by simp)
    case assignBad =>
      intro fenv env lctx rets vars e hgate s s' h
      rw [trStmt, if_pos hgate] at h
      obtain ⟨u, s1, h1, -⟩ := M.bind_inv h
      exact absurd h1 (by simp [reject])
    case assign =>
      intro fenv env lctx rets vars e hgate s s' h
      rw [trStmt, if_neg hgate] at h
      obtain ⟨u, s1, h1, h⟩ := M.bind_inv h
      obtain ⟨ids, s2, h2, h3⟩ := M.bind_inv h
      exact absurd h3 (by simp)
    case cond =>
      intro fenv env lctx rets c body ih s s' h
      rw [trStmt] at h
      obtain ⟨cv, s1, h1, h⟩ := M.bind_inv h
      obtain ⟨xvals, s2, h2, h⟩ := M.bind_inv h
      obtain ⟨bodyId, s3, h3, h⟩ := M.bind_inv h
      obtain ⟨joinParams, s4, h4, h⟩ := M.bind_inv h
      obtain ⟨joinId, s5, h5, h⟩ := M.bind_inv h
      obtain ⟨u6, s6, h6, h⟩ := M.bind_inv h
      obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
      obtain ⟨renv, s8, h8, h⟩ := M.bind_inv h
      cases renv with
      | none =>
        obtain ⟨u9, s9, h9, h10⟩ := M.bind_inv h
        obtain ⟨u10, s10, hmove, hpure⟩ := M.bind_inv h10
        exact absurd hpure (by simp)
      | some env' =>
        obtain ⟨xv, s9, h9, h⟩ := M.bind_inv h
        obtain ⟨u10, s10, h10, h⟩ := M.bind_inv h
        obtain ⟨u11, s11, h11, h12⟩ := M.bind_inv h
        exact absurd h12 (by simp)
    case switch =>
      intro fenv env lctx rets c cases dflt ih s s' h
      unfold trStmt at h
      obtain ⟨sv, s1, h1, h⟩ := M.bind_inv h
      obtain ⟨joinParams, s2, h2, h⟩ := M.bind_inv h
      obtain ⟨joinId, s3, h3, h⟩ := M.bind_inv h
      obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
      obtain ⟨u5, s5, h5, h6⟩ := M.bind_inv h
      exact absurd h6 (by simp)
    case forLoop =>
      intro fenv env lctx rets init c post body ihInit ihBody ihPost s s' h
      unfold trStmt at h
      obtain ⟨scope, s1, h1, h⟩ := M.bind_inv h
      obtain ⟨rinit, s2, h2, h⟩ := M.bind_inv h
      cases rinit with
      | none =>
        obtain ⟨-, hs⟩ := M.pure_inv h
        rw [hs]
        exact ihInit scope s1 s2 h2
      | some envI =>
        obtain ⟨xvals, s3, h3, h⟩ := M.bind_inv h
        obtain ⟨hParams, s4, h4, h⟩ := M.bind_inv h
        obtain ⟨hId, s5, h5, h⟩ := M.bind_inv h
        obtain ⟨exitParams, s6, h6, h⟩ := M.bind_inv h
        obtain ⟨exitId, s7, h7, h⟩ := M.bind_inv h
        obtain ⟨postParams, s8, h8, h⟩ := M.bind_inv h
        obtain ⟨postId, s9, h9, h⟩ := M.bind_inv h
        obtain ⟨u10, s10, h10, h⟩ := M.bind_inv h
        obtain ⟨u11, s11, h11, h⟩ := M.bind_inv h
        obtain ⟨cv, s12, h12, h⟩ := M.bind_inv h
        obtain ⟨bodyId, s13, h13, h⟩ := M.bind_inv h
        obtain ⟨hX, s14, h14, h⟩ := M.bind_inv h
        obtain ⟨u15, s15, h15, h⟩ := M.bind_inv h
        obtain ⟨u16, s16, h16, h⟩ := M.bind_inv h
        obtain ⟨renvB, s17, h17, h⟩ := M.bind_inv h
        cases renvB with
        | none =>
          obtain ⟨u18, s18, h18, h⟩ := M.bind_inv h
          obtain ⟨u19, s19, h19, h⟩ := M.bind_inv h
          obtain ⟨renvP, s20, h20, h⟩ := M.bind_inv h
          cases renvP with
          | none =>
            obtain ⟨u21, s21, h21, h⟩ := M.bind_inv h
            obtain ⟨u22, s22, h22, h23⟩ := M.bind_inv h
            exact absurd h23 (by simp)
          | some envP =>
            obtain ⟨xvP, s21, h21, h⟩ := M.bind_inv h
            obtain ⟨u22, s22, h22, h⟩ := M.bind_inv h
            obtain ⟨u23, s23, h23, h⟩ := M.bind_inv h
            exact absurd h (by simp)
        | some envB =>
          obtain ⟨xvB, s18, h18, h⟩ := M.bind_inv h
          obtain ⟨u19, s19, h19, h⟩ := M.bind_inv h
          obtain ⟨u20, s20, h20, h⟩ := M.bind_inv h
          obtain ⟨renvP, s21, h21, h⟩ := M.bind_inv h
          cases renvP with
          | none =>
            obtain ⟨u22, s22, h22, h⟩ := M.bind_inv h
            obtain ⟨u23, s23, h23, h24⟩ := M.bind_inv h
            exact absurd h24 (by simp)
          | some envP =>
            obtain ⟨xvP, s22, h22, h⟩ := M.bind_inv h
            obtain ⟨u23, s23, h23, h⟩ := M.bind_inv h
            obtain ⟨u24, s24, h24, h25⟩ := M.bind_inv h
            exact absurd h25 (by simp)
    case exprBuiltin =>
      intro fenv env lctx rets op args s s' h
      rw [trStmt] at h
      obtain ⟨as, s1, h1, h⟩ := M.bind_inv h
      by_cases hop : isHaltingOp op = true
      · rw [if_pos hop] at h
        obtain ⟨u, s2, h2, h3⟩ := M.bind_inv h
        obtain ⟨-, rfl⟩ := M.pure_inv h3
        exact (sealCur_cur h2).choose_spec.2.1
      · rw [if_neg hop] at h
        obtain ⟨u, s2, h2, h3⟩ := M.bind_inv h
        exact absurd h3 (by simp)
    case exprCall =>
      intro fenv env lctx rets fn args s s' h
      rw [trStmt] at h
      obtain ⟨as, s1, h1, h⟩ := M.bind_inv h
      obtain ⟨fid, s2, h2, h⟩ := M.bind_inv h
      obtain ⟨u, s3, h3, h4⟩ := M.bind_inv h
      exact absurd h4 (by simp)
    case exprBad =>
      intro fenv env lctx rets e hnb hnc s s' h
      rw [trStmt] at h
      · exact absurd h (by simp [reject])
      · exact hnb
      · exact hnc
    case breakNone =>
      intro fenv env rets s s' h
      rw [trStmt] at h
      exact absurd h (by simp [reject])
    case breakSome =>
      intro fenv env rets l s s' h
      rw [trStmt] at h
      obtain ⟨vals, s1, h1, h⟩ := M.bind_inv h
      obtain ⟨u, s2, h2, h3⟩ := M.bind_inv h
      obtain ⟨-, rfl⟩ := M.pure_inv h3
      exact (sealCur_cur h2).choose_spec.2.1
    case contNone =>
      intro fenv env rets s s' h
      rw [trStmt] at h
      exact absurd h (by simp [reject])
    case contSome =>
      intro fenv env rets l s s' h
      rw [trStmt] at h
      obtain ⟨vals, s1, h1, h⟩ := M.bind_inv h
      obtain ⟨u, s2, h2, h3⟩ := M.bind_inv h
      obtain ⟨-, rfl⟩ := M.pure_inv h3
      exact (sealCur_cur h2).choose_spec.2.1
    case leaveNone =>
      intro fenv env lctx s s' h
      rw [trStmt] at h
      exact absurd h (by simp [reject])
    case leaveSome =>
      intro fenv env lctx rs s s' h
      rw [trStmt] at h
      obtain ⟨vals, s1, h1, h⟩ := M.bind_inv h
      obtain ⟨u, s2, h2, h3⟩ := M.bind_inv h
      obtain ⟨-, rfl⟩ := M.pure_inv h3
      exact (sealCur_cur h2).choose_spec.2.1
    case casesNilNone => intros; trivial
    case casesNilSome => intros; trivial
    case casesCons => intros; trivial
  intro fenv env lctx rets body s s' h
  rw [trScope] at h
  obtain ⟨scope, s1, h1, h⟩ := M.bind_inv h
  obtain ⟨renv, s2, h2, h3⟩ := M.bind_inv h
  cases renv with
  | none =>
    obtain ⟨-, hs⟩ := M.pure_inv h3
    rw [hs]
    exact hall (scope :: fenv) env lctx rets false body s1 s2 h2
  | some env' => exact absurd h3 (by simp)

omit model in
/-- Every completed switch dispatch chain ends in a sealed block. -/
theorem trCases_cur_nil (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (sv : ValId) (X : List Ident)
    (joinId : BlockId) (cs : List (Literal × List (Stmt Op)))
    (df : Option (List (Stmt Op))) (s s' : BState) (u : Unit)
    (h : trCases fenv env lctx rets sv X joinId cs df s = some (u, s')) :
    s'.fn.cur = [] := by
  induction cs generalizing s with
  | nil =>
    cases df with
    | none =>
      rw [trCases] at h
      obtain ⟨xv, sA, h1, h2⟩ := M.bind_inv h
      exact (sealCur_cur h2).choose_spec.2.1
    | some body =>
      rw [trCases] at h
      obtain ⟨renv, sA, h1, h2⟩ := M.bind_inv h
      cases renv with
      | none =>
        obtain ⟨-, rfl⟩ := M.pure_inv h2
        exact trScope_none_cur_nil fenv env lctx rets body s s' h1
      | some env' =>
        obtain ⟨xv, sB, h3, h4⟩ := M.bind_inv h2
        exact (sealCur_cur h4).choose_spec.2.1
  | cons p rest ih =>
    obtain ⟨lit, body⟩ := p
    rw [trCases] at h
    obtain ⟨t, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨u2, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨e, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨caseId, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨nextId, s6, h6, h⟩ := M.bind_inv h
    obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
    obtain ⟨u8, s8, h8, h⟩ := M.bind_inv h
    obtain ⟨renv, s9, h9, h⟩ := M.bind_inv h
    cases renv with
    | none =>
      obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb, hc⟩ := M.bind_inv h
      exact ih sb hc
    | some env' =>
      obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb, h⟩ := M.bind_inv h
      obtain ⟨uc, sc, hc, hd⟩ := M.bind_inv h
      exact ih sc hd

/- The accessible version of this lemma is placed below `trStmt_cur`, whose
block-specialisation it uses.  Keeping the proof text here while that theorem
is defined would be an illegal forward reference.
omit model in
/-- Switch-chain translation keeps the selected/current block id in bounds. -/
theorem trCases_cur_valid (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (sv : ValId) (X : List Ident)
    (joinId : BlockId) (cs : List (Literal × List (Stmt Op)))
    (df : Option (List (Stmt Op))) (s s' : BState) (u : Unit)
    (hv : CurValid s)
    (h : trCases fenv env lctx rets sv X joinId cs df s = some (u, s')) :
    CurValid s' := by
  induction cs generalizing s with
  | nil =>
    cases df with
    | none =>
      rw [trCases] at h
      obtain ⟨xv, sA, h1, h2⟩ := M.bind_inv h
      have hvA := hv.of_grows (Grows.of_liftO h1)
      exact CurValid.of_same_sgrows hvA (SGrowsAt.of_sealCur h2)
        (curSealed_of_sealCur h2).1
    | some body =>
      rw [trCases] at h
      obtain ⟨renv, sA, h1, h2⟩ := M.bind_inv h
      have h1' : trStmt fenv env lctx rets (.block body) s = some (renv, sA) := by
        rw [trStmt]
        exact h1
      have hvA := (trStmt_cur hv h1').1
      cases renv with
      | none =>
        obtain ⟨-, rfl⟩ := M.pure_inv h2
        exact hvA
      | some env' =>
        obtain ⟨xv, sB, h3, h4⟩ := M.bind_inv h2
        have hvB := hvA.of_grows (Grows.of_liftO h3)
        exact CurValid.of_same_sgrows hvB (SGrowsAt.of_sealCur h4)
          (curSealed_of_sealCur h4).1
  | cons p rest ih =>
    obtain ⟨lit, body⟩ := p
    rw [trCases] at h
    obtain ⟨t, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨u2, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨e, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨caseId, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨nextId, s6, h6, h⟩ := M.bind_inv h
    obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
    obtain ⟨u8, s8, h8, h⟩ := M.bind_inv h
    obtain ⟨renv, s9, h9, h⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 := SGrowsAt.of_grows (Grows.of_freshVal h1)
    have a2 := a1.trans (SGrowsAt.of_grows (Grows.of_emit h2))
    have a3 := a2.trans (SGrowsAt.of_grows (Grows.of_freshVal h3))
    have a4 := a3.trans (SGrowsAt.of_grows (Grows.of_emit h4))
    have a5 := a4.trans (SGrowsAt.of_newBlock h5)
    have a6 := a5.trans (SGrowsAt.of_newBlock h6)
    have a7 := a6.trans (SGrowsAt.of_sealCur h7)
    have hcase : s.fn.blocks.size ≤ caseId := by
      rw [SGrowsAt.newBlock_id h5]
      exact a4.size
    have hv8 : CurValid s8 := CurValid.of_moveTo
      (Nat.lt_of_lt_of_le (newBlock_target_lt h5)
        ((SGrowsAt.of_newBlock (N := 0) h6).trans
          (SGrowsAt.of_sealCur h7)).size) h8
    have h9' : trStmt fenv env lctx rets (.block body) s8 = some (renv, s9) := by
      rw [trStmt]
      exact h9
    have hv9 := (trStmt_cur hv8 h9').1
    have gbody := trScope_grows fenv env lctx rets body s8 renv s9 h9
    cases renv with
    | none =>
      obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb, hc⟩ := M.bind_inv h
      have g6a : SGrowsAt 0 s6 sa :=
        ((SGrowsAt.of_sealCur h7).trans
          (SGrowsAt.of_moveTo (Or.inl (by simpa using hcase)) h8)).trans
            (gbody.mono (Nat.zero_le _))
      have hvb : CurValid sb := CurValid.of_moveTo
        (Nat.lt_of_lt_of_le (newBlock_target_lt h6) g6a.size) hb
      exact ih sb hvb hc
    | some env' =>
      obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb, h⟩ := M.bind_inv h
      obtain ⟨uc, sc, hc, hd⟩ := M.bind_inv h
      have g6b : SGrowsAt 0 s6 sb :=
        (((SGrowsAt.of_sealCur h7).trans
          (SGrowsAt.of_moveTo (Or.inl (by simpa using hcase)) h8)).trans
            (gbody.mono (Nat.zero_le _))).trans
              ((SGrowsAt.of_edgeArgs ha).trans (SGrowsAt.of_sealCur hb))
      have hvc : CurValid sc := CurValid.of_moveTo
        (Nat.lt_of_lt_of_le (newBlock_target_lt h6) g6b.size) hc
      exact ih sc hvc hd
-/

omit model in
/-- Statement-current validity as a corollary of the list invariant, using a
singleton list.  Function definitions are handled by `trStmts` itself and are
rejected by `trStmt`. -/
theorem trStmt_cur {fenv : FMap} {env : VMap} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {st : Stmt Op} {s s' : BState}
    {renv : Option VMap} (hv : CurValid s)
    (h : trStmt fenv env lctx rets st s = some (renv, s')) :
    CurValid s' ∧ CurResult renv s s' := by
  cases st with
  | funDef n ps rs body =>
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  | block body =>
    apply trStmts_cur fenv env lctx rets false [.block body] s renv s' hv
    rw [trStmts] <;> try { intros; contradiction }
    simp only [Bool.false_eq_true, if_false]
    rw [M.bind_eq, h]; cases renv <;> simp [trStmts]
  | letDecl vars val =>
    apply trStmts_cur fenv env lctx rets false [.letDecl vars val] s renv s' hv
    rw [trStmts] <;> try { intros; contradiction }
    simp only [Bool.false_eq_true, if_false]
    rw [M.bind_eq, h]; cases renv <;> simp [trStmts]
  | assign vars e =>
    apply trStmts_cur fenv env lctx rets false [.assign vars e] s renv s' hv
    rw [trStmts] <;> try { intros; contradiction }
    simp only [Bool.false_eq_true, if_false]
    rw [M.bind_eq, h]; cases renv <;> simp [trStmts]
  | cond e body =>
    apply trStmts_cur fenv env lctx rets false [.cond e body] s renv s' hv
    rw [trStmts] <;> try { intros; contradiction }
    simp only [Bool.false_eq_true, if_false]
    rw [M.bind_eq, h]; cases renv <;> simp [trStmts]
  | switch e cases dflt =>
    apply trStmts_cur fenv env lctx rets false [.switch e cases dflt] s renv s' hv
    rw [trStmts] <;> try { intros; contradiction }
    simp only [Bool.false_eq_true, if_false]
    rw [M.bind_eq, h]; cases renv <;> simp [trStmts]
  | forLoop init e post body =>
    apply trStmts_cur fenv env lctx rets false [.forLoop init e post body] s renv s' hv
    rw [trStmts] <;> try { intros; contradiction }
    simp only [Bool.false_eq_true, if_false]
    rw [M.bind_eq, h]; cases renv <;> simp [trStmts]
  | exprStmt e =>
    apply trStmts_cur fenv env lctx rets false [.exprStmt e] s renv s' hv
    rw [trStmts] <;> try { intros; contradiction }
    simp only [Bool.false_eq_true, if_false]
    rw [M.bind_eq, h]; cases renv <;> simp [trStmts]
  | «break» =>
    apply trStmts_cur fenv env lctx rets false [.break] s renv s' hv
    rw [trStmts] <;> try { intros; contradiction }
    simp only [Bool.false_eq_true, if_false]
    rw [M.bind_eq, h]; cases renv <;> simp [trStmts]
  | «continue» =>
    apply trStmts_cur fenv env lctx rets false [.continue] s renv s' hv
    rw [trStmts] <;> try { intros; contradiction }
    simp only [Bool.false_eq_true, if_false]
    rw [M.bind_eq, h]; cases renv <;> simp [trStmts]
  | leave =>
    apply trStmts_cur fenv env lctx rets false [.leave] s renv s' hv
    rw [trStmts] <;> try { intros; contradiction }
    simp only [Bool.false_eq_true, if_false]
    rw [M.bind_eq, h]
    cases renv <;> simp [trStmts]

omit model in
/-- Switch dispatch always seals the block in which it starts.  This is the
standalone `trCases` specialization of the mutual current-shape invariant. -/
theorem trCases_cur_closed (fenv : FMap) (env : VMap)
    (lctx : Option LoopCtx) (rets : Option (List Ident)) (sv : ValId)
    (X : List Ident) (joinId : BlockId)
    (cs : List (Literal × List (Stmt Op)))
    (df : Option (List (Stmt Op))) (s s' : BState) (u : Unit)
    (hv : CurValid s)
    (h : trCases fenv env lctx rets sv X joinId cs df s = some (u, s')) :
    CurValid s' ∧ CurClosed s s' := by
  induction cs generalizing s with
  | nil =>
    cases df with
    | none =>
      rw [trCases] at h
      obtain ⟨xvals, s₁, h1, h2⟩ := M.bind_inv h
      have hg1 := Grows.of_liftO h1
      have hs := curSealed_of_sealCur h2
      refine ⟨CurValid.of_same_sgrows (hv.of_grows hg1)
        (SGrowsAt.of_sealCur (N := s₁.fn.blocks.size) h2) hs.1, Or.inr ?_⟩
      rcases hs with ⟨hc, b, hb, Δ, hi⟩
      rcases CurSame.of_grows hg1 with ⟨hc1, ⟨Δ1, hi1⟩, -⟩
      refine ⟨hc.trans hc1, b, by simpa only [hc1] using hb,
        Δ1.reverse ++ Δ, ?_⟩
      rw [hi, hi1]
      simp
    | some dbody =>
      rw [trCases] at h
      obtain ⟨renv, s₁, h1, h2⟩ := M.bind_inv h
      have h1' : trStmt fenv env lctx rets (.block dbody) s = some (renv, s₁) := by
        rw [trStmt]
        exact h1
      obtain ⟨hv1, hk1⟩ := trStmt_cur hv h1'
      have hg1 := trScope_grows fenv env lctx rets dbody s renv s₁ h1
      cases renv with
      | none =>
        obtain ⟨rfl, rfl⟩ := M.pure_inv h2
        exact ⟨hv1, hk1⟩
      | some env' =>
        obtain ⟨xv, s₂, h3, h4⟩ := M.bind_inv h2
        have hgE := Grows.of_liftO h3
        have hs := curSealed_of_sealCur h4
        have hv2 := hv1.of_grows hgE
        have hv' := CurValid.of_same_sgrows hv2
          (SGrowsAt.of_sealCur (N := s₂.fn.blocks.size) h4) hs.1
        have hclosed : CurClosed s₁ s' := by
          refine Or.inr ?_
          rcases hs with ⟨hc, b, hb, Δ, hi⟩
          rcases CurSame.of_grows hgE with ⟨hc1, ⟨Δ1, hi1⟩, -⟩
          refine ⟨hc.trans hc1, b, by simpa only [hc1] using hb,
            Δ1.reverse ++ Δ, ?_⟩
          rw [hi, hi1]
          simp
        exact ⟨hv', CurOpen.transClosed hv hg1
          (SGrows.trans (SGrows.of_grows hgE) (SGrowsAt.of_sealCur h4))
          hk1 hclosed⟩
  | cons p rest ih =>
    obtain ⟨lit, cbody⟩ := p
    rw [trCases] at h
    obtain ⟨t, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨u2, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨e, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨caseId, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨nextId, s6, h6, h⟩ := M.bind_inv h
    obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
    obtain ⟨u8, s8, h8, h⟩ := M.bind_inv h
    obtain ⟨renv, s9, h9, h⟩ := M.bind_inv h
    have g1 := Grows.of_freshVal h1
    have g2 := Grows.of_emit h2
    have g3 := Grows.of_freshVal h3
    have g4 := Grows.of_emit h4
    have cs4 := (((CurSame.of_grows g1).trans (CurSame.of_grows g2)).trans
      (CurSame.of_grows g3)).trans (CurSame.of_grows g4)
    have cs5 := cs4.trans (CurSame.of_newBlock h5)
    have cs6 := cs5.trans (CurSame.of_newBlock h6)
    have a1 : SGrowsAt s.fn.blocks.size s s1 := SGrowsAt.of_grows g1
    have a2 := a1.trans (SGrowsAt.of_grows g2)
    have a3 := a2.trans (SGrowsAt.of_grows g3)
    have a4 := a3.trans (SGrowsAt.of_grows g4)
    have a5 := a4.trans (SGrowsAt.of_newBlock h5)
    have a6 := a5.trans (SGrowsAt.of_newBlock h6)
    have a7 := a6.trans (SGrowsAt.of_sealCur h7)
    have hcaseNe : s6.fn.curId ≠ caseId := by
      rw [cs6.1, SGrowsAt.newBlock_id h5]
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hv a4.size)
    have hm68 : CurMoved s6 s8 := curMoved_of_seal_move hcaseNe h7 h8
    have hm : CurMoved s s8 := cs6.transMoved hm68
    have a8 := a7.trans (SGrowsAt.of_moveTo
      (Or.inl (by rw [SGrowsAt.newBlock_id h5]; exact a4.size)) h8)
    have hcaseLt : caseId < s7.fn.blocks.size :=
      Nat.lt_of_lt_of_le (newBlock_target_lt h5)
        ((SGrowsAt.of_newBlock (N := 0) h6).trans
          (SGrowsAt.of_sealCur h7)).size
    have hv8 : CurValid s8 := CurValid.of_moveTo hcaseLt h8
    have gbody := trScope_grows fenv env lctx rets cbody s8 renv s9 h9
    cases renv with
    | none =>
      obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, hc2⟩ := M.bind_inv h
      obtain ⟨-, rfl⟩ := M.pure_inv ha
      have g6a : SGrowsAt 0 s6 sa := ((SGrowsAt.of_sealCur h7).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h8)).trans
          (gbody.mono (Nat.zero_le _))
      have hnextLt : nextId < sa.fn.blocks.size :=
        Nat.lt_of_lt_of_le (newBlock_target_lt h6) g6a.size
      have hvb : CurValid sb := CurValid.of_moveTo hnextLt hb2
      obtain ⟨hv', -⟩ := ih sb hvb hc2
      have hnextBase : s.fn.blocks.size ≤ nextId := by
        rw [SGrowsAt.newBlock_id h6]
        exact a5.size
      have gb : SGrowsAt s.fn.blocks.size s8 sb :=
        (gbody.mono a8.size).trans
          (SGrowsAt.of_moveTo (Or.inl hnextBase) hb2)
      have gr := trCases_grows fenv env lctx rets sv X joinId rest df
        sv X joinId sb u s' hc2
      exact ⟨hv', Or.inl (hm.forward hv a8
        (gb.trans (gr.mono (Nat.le_trans a8.size gb.size))))⟩
    | some env' =>
      obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
      obtain ⟨uc, sc, hc2, hd2⟩ := M.bind_inv h
      have g6sb : SGrowsAt 0 s6 sb := (((SGrowsAt.of_sealCur h7).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h8)).trans
          (gbody.mono (Nat.zero_le _))).trans
            ((SGrowsAt.of_edgeArgs ha).trans (SGrowsAt.of_sealCur hb2))
      have hnextLt : nextId < sb.fn.blocks.size :=
        Nat.lt_of_lt_of_le (newBlock_target_lt h6) g6sb.size
      have hvc : CurValid sc := CurValid.of_moveTo hnextLt hc2
      obtain ⟨hv', -⟩ := ih sc hvc hd2
      have hnextBase : s.fn.blocks.size ≤ nextId := by
        rw [SGrowsAt.newBlock_id h6]
        exact a5.size
      have gb : SGrowsAt s.fn.blocks.size s8 sc :=
        (((gbody.mono a8.size).trans (SGrowsAt.of_edgeArgs ha)).trans
          (SGrowsAt.of_sealCur hb2)).trans
            (SGrowsAt.of_moveTo (Or.inl hnextBase) hc2)
      have gr := trCases_grows fenv env lctx rets sv X joinId rest df
        sv X joinId sc u s' hd2
      exact ⟨hv', Or.inl (hm.forward hv a8
        (gb.trans (gr.mono (Nat.le_trans a8.size gb.size))))⟩

omit model in
/-- A non-dependent spelling of the optional default-body list.  Rewriting to
`Option.toList` avoids dependent `match` terms acquiring local proof arguments
when a switch equation is inverted. -/
theorem switchBodies_eq (cases : List (Literal × List (Stmt Op)))
    (dflt : Option (List (Stmt Op))) :
    cases.map Prod.snd ++ (match dflt with | some b => [b] | none => []) =
      cases.map Prod.snd ++ dflt.toList := by
  cases dflt <;> rfl

omit model in
/-- `CurPlaced` travels backwards along an expression-level step. -/
theorem curPlaced_back_grows {f : Func} {sA sB : BState} (hg : Grows sA sB)
    (h : CurPlaced f sB.fn) : CurPlaced f sA.fn := by
  obtain ⟨Δ, hΔ⟩ := hg.cur
  exact h.ofPrefix hg.curId.symm Δ hΔ

omit model in
/-- Backward placement across a statement-list construction.  The `CurFinal`
premise is used precisely when the list diverts after sealing (and therefore
clearing) the same current block; in the fall-through case `curPlaced_back`
and the list's growth witness suffice. -/
theorem trStmts_curPlaced_back {f : Func} {fenv : FMap} {env : VMap}
    {lctx : Option LoopCtx} {rets : Option (List Ident)} {d : Bool}
    {ss : List (Stmt Op)} {s₀ s₁ : BState} {renv : Option VMap}
    {joins : List BlockId} (hvalid : CurValid s₀)
    (hprot : ProtectedAt joins s₀.fn)
    (hcompl : Completes f s₁.fn joins) (hcp : CurPlaced f s₁.fn)
    (hfin : renv = none → CurFinal f s₁.fn)
    (htr : trStmts fenv env lctx rets d ss s₀ = some (renv, s₁)) :
    CurPlaced f s₀.fn := by
  cases d with
  | false =>
    obtain ⟨-, hk⟩ := trStmts_cur fenv env lctx rets false ss s₀ renv s₁
      hvalid htr
    exact curPlaced_back hk hprot.away hcompl hfin hcp
  | true =>
    obtain ⟨hrenv, hfn⟩ := trStmts_true_fn fenv env lctx rets ss
      s₀ s₁ renv htr
    have : renv = none := hrenv
    subst renv
    simpa only [hfn] using hcp

/-- An expression whose evaluation halts: the fragment the construction laid
down reaches that halt from the fragment's entry configuration. -/
def EOutHalt (P : Prog) (f : Func) (s₀ : BState) (R₀ : Regs)
    (yst yst' : EvmState) : Prop :=
  ExecFrom (model := model) P f s₀.fn R₀ yst (.halt yst')

/-- **Every "the right-hand side halted" statement rule at once.** `letHalt`,
`assignHalt`, `exprStmtHalt`, `ifHalt` and `switchHalt` all leave the
environment untouched and report `.halt`; on the SSA side the halt happens
inside the expression's own fragment, which is a prefix of the statement's, so
the statement's `SOut` *is* the expression's. -/
theorem SOut.ofExprHalt {P : Prog} {f : Func} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {s₀ s₁ : BState} {R : Regs}
    {renv : Option VMap} {V : VEnv yulD} {yst yst' : EvmState}
    (h : EOutHalt (model := model) P f s₀ R yst yst') :
    SOut (model := model) P f lctx rets s₀ s₁ R renv V yst yst' .halt := h

omit model in
/-- `trExprN` on a right-hand side that is *not* a user call is `trExpr` plus a
singleton: the arity gate forces `n = 1`. -/
theorem trExprN_nonCall_inv {fenv : FMap} {env : VMap} {n : Nat} {e : Expr Op}
    {s₀ s₁ : BState} {ids : List ValId}
    (hne : ∀ (fn : Ident) (args : List (Expr Op)), e ≠ .call fn args)
    (h : trExprN fenv env n e s₀ = some (ids, s₁)) :
    n = 1 ∧ ∃ i : ValId, ids = [i] ∧ trExpr fenv env e s₀ = some (i, s₁) := by
  cases e with
  | call fn args => exact absurd rfl (hne fn args)
  | lit l =>
    rw [trExprN] at h
    · obtain ⟨hn, h⟩ := M.ite_reject_inv' h
      obtain ⟨i, sX, h1, h2⟩ := M.bind_inv h
      obtain ⟨hids, hsX⟩ := M.pure_inv h2
      exact ⟨hn, i, hids, by rw [← hsX] at h1; exact h1⟩
    · intro fn' args' hc; exact absurd hc (hne fn' args')
  | var x =>
    rw [trExprN] at h
    · obtain ⟨hn, h⟩ := M.ite_reject_inv' h
      obtain ⟨i, sX, h1, h2⟩ := M.bind_inv h
      obtain ⟨hids, hsX⟩ := M.pure_inv h2
      exact ⟨hn, i, hids, by rw [← hsX] at h1; exact h1⟩
    · intro fn' args' hc; exact absurd hc (hne fn' args')
  | builtin op args =>
    rw [trExprN] at h
    · obtain ⟨hn, h⟩ := M.ite_reject_inv' h
      obtain ⟨i, sX, h1, h2⟩ := M.bind_inv h
      obtain ⟨hids, hsX⟩ := M.pure_inv h2
      exact ⟨hn, i, hids, by rw [← hsX] at h1; exact h1⟩
    · intro fn' args' hc; exact absurd hc (hne fn' args')

/-- A one-value expression result read as a one-element argument list. -/
theorem EOut.toEOutL {P : Prog} {f : Func} {s₀ s₁ : BState} {R : Regs}
    {i : ValId} {v : U256} {yst yst' : EvmState}
    (h : EOut (model := model) P f s₀ s₁ R i v yst yst') :
    EOutL (model := model) P f s₀ s₁ R [i] [v] yst yst' := by
  obtain ⟨R₁, hle, hbelow, hfr, hi, hsim⟩ := h
  exact ⟨R₁, hle, hbelow, hfr, by rw [Regs.getMany_cons, hi]; simp, hsim⟩

/-- **`letDecl vars (some e)`** — the right-hand side's ids become the new
bindings; `EnvOK.zip` pairs them with the source values. -/
theorem sim_letDecl_some {P : Prog} {f : Func} {fenv : FMap} {env : VMap}
    {R : Regs} {V : VEnv yulD} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {vars : List Ident} {e : Expr Op}
    {s₀ s₁ sA : BState} {renv : Option VMap} {ids : List ValId}
    {vals : List U256} {yst yst1 : EvmState}
    (henv : EnvOK (model := model) env V R)
    (huniq : env.Unique)
    (hvals : vals.length = vars.length)
    (htrN : trExprN fenv env vars.length e s₀ = some (ids, sA))
    (hE : EOutL (model := model) P f s₀ sA R ids vals yst yst1)
    (htr : trStmt fenv env lctx rets (.letDecl vars (some e)) s₀
        = some (renv, s₁)) :
    SOut (model := model) P f lctx rets s₀ s₁ R renv
      (vars.zip vals ++ V) yst yst1 .normal := by
  rw [trStmt] at htr
  by_cases hgate : (vars.any env.mem || !decide vars.Nodup) = true
  · rw [if_pos hgate] at htr
    obtain ⟨u, sX, h1, -⟩ := M.bind_inv htr
    exact absurd h1 (by simp [reject])
  rw [if_neg hgate] at htr
  obtain ⟨u, sX, h1, htr⟩ := M.bind_inv htr
  obtain ⟨-, hsX⟩ := M.pure_inv h1
  rw [hsX] at htr
  obtain ⟨ids', sA', h2, h3⟩ := M.bind_inv htr
  obtain ⟨rfl, rfl⟩ : ids' = ids ∧ sA' = sA := by
    have he := h2.symm.trans htrN
    exact ⟨(M.some_pair_inj he).1, (M.some_pair_inj he).2⟩
  obtain ⟨hrenv, hs₁⟩ := M.pure_inv h3
  subst hs₁
  obtain ⟨R₁, hle, hbelow, hfr, hget, hsim⟩ := hE
  refine ⟨vars.zip ids' ++ env, R₁, hrenv, hle, hbelow, hfr, ?_, ?_, hsim⟩
  · refine EnvOK.append (EnvOK.zip (Regs.getMany_eq_some_iff.mp hget) ?_)
      (henv.mono hle)
    rw [Regs.getMany_length hget]
    exact hvals.symm
  · have ha : vars.any env.mem = false := by
      cases he : vars.any env.mem with
      | false => rfl
      | true => exact False.elim (hgate (by simp [he]))
    have hnd : vars.Nodup := by
      by_contra hn
      exact hgate (by simp [hn])
    refine huniq.zip_append hnd ?_ ?_
    · intro x hx
      exact Bool.eq_false_of_not_eq_true (List.any_eq_false.mp ha x hx)
    · exact ((Regs.getMany_length hget).trans hvals).symm

/-- **`assign vars e`** — the right-hand side's ids replace the bindings in
place; `EnvOK.setMany` tracks `VEnv.setMany`. -/
theorem sim_assign {P : Prog} {f : Func} {fenv : FMap} {env : VMap}
    {R : Regs} {V : VEnv yulD} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {vars : List Ident} {e : Expr Op}
    {s₀ s₁ sA : BState} {renv : Option VMap} {ids : List ValId}
    {vals : List U256} {yst yst1 : EvmState}
    (henv : EnvOK (model := model) env V R)
    (huniq : env.Unique)
    (htrN : trExprN fenv env vars.length e s₀ = some (ids, sA))
    (hE : EOutL (model := model) P f s₀ sA R ids vals yst yst1)
    (htr : trStmt fenv env lctx rets (.assign vars e) s₀ = some (renv, s₁)) :
    SOut (model := model) P f lctx rets s₀ s₁ R renv
      (YulSemantics.VEnv.setMany V vars vals) yst yst1 .normal := by
  rw [trStmt] at htr
  by_cases hgate : (!vars.all env.mem) = true
  · rw [if_pos hgate] at htr
    obtain ⟨u, sX, h1, -⟩ := M.bind_inv htr
    exact absurd h1 (by simp [reject])
  rw [if_neg hgate] at htr
  obtain ⟨u, sX, h1, htr⟩ := M.bind_inv htr
  obtain ⟨-, hsX⟩ := M.pure_inv h1
  rw [hsX] at htr
  obtain ⟨ids', sA', h2, h3⟩ := M.bind_inv htr
  obtain ⟨rfl, rfl⟩ : ids' = ids ∧ sA' = sA := by
    have he := h2.symm.trans htrN
    exact ⟨(M.some_pair_inj he).1, (M.some_pair_inj he).2⟩
  obtain ⟨hrenv, hs₁⟩ := M.pure_inv h3
  subst hs₁
  obtain ⟨R₁, hle, hbelow, hfr, hget, hsim⟩ := hE
  exact ⟨env.setMany vars ids', R₁, hrenv, hle, hbelow, hfr,
    EnvOK.setMany (henv.mono hle) (Regs.getMany_eq_some_iff.mp hget),
    huniq.setMany _ _, hsim⟩

/-- **`exprStmt` of an always-halting built-in** — the construction seals the
block with `Term.halt`, and `isHaltingOp_halts` says the source really does
halt there, so no execution is lost. -/
theorem sim_exprStmt_halt {P : Prog} {f : Func} {fenv : FMap} {env : VMap}
    {R : Regs} {V : VEnv yulD} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {op : Op} {args : List (Expr Op)}
    {s₀ s₁ sA : BState} {renv : Option VMap} {ids : List ValId}
    {argvals : List U256} {yst yst1 yst' : EvmState}
    (hop : isHaltingOp op = true)
    (hfin : CurFinal f s₁.fn)
    (htrA : trArgs fenv env args s₀ = some (ids, sA))
    (hA : EOutL (model := model) P f s₀ sA R ids argvals yst yst1)
    (hb : builtinWithExternal model.calls model.creates op argvals yst1 (.halt yst'))
    (htr : trStmt fenv env lctx rets (.exprStmt (.builtin op args)) s₀
        = some (renv, s₁)) :
    SOut (model := model) P f lctx rets s₀ s₁ R renv V yst yst' .halt := by
  rw [trStmt] at htr
  obtain ⟨ids', sA', h1, htr⟩ := M.bind_inv htr
  obtain ⟨rfl, rfl⟩ : ids' = ids ∧ sA' = sA := by
    have he := h1.symm.trans htrA
    exact ⟨(M.some_pair_inj he).1, (M.some_pair_inj he).2⟩
  rw [if_pos hop] at htr
  obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
  obtain ⟨-, hs₁⟩ := M.pure_inv h3
  rw [hs₁] at hfin
  obtain ⟨R₁, -, -, -, hget, hsim⟩ := hA
  exact hsim (.halt yst')
    (execFrom_halt (curOK_of_sealCur hfin h2) hget hb)

/-- **`exprStmt` of a value-less built-in** — one `op` instruction with no
destinations; the source rule forces the built-in to return no values. -/
theorem sim_exprStmt_op {P : Prog} {f : Func} {fenv : FMap} {env : VMap}
    {R : Regs} {V : VEnv yulD} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {op : Op} {args : List (Expr Op)}
    {s₀ s₁ sA : BState} {renv : Option VMap} {ids : List ValId}
    {argvals : List U256} {yst yst1 yst' : EvmState}
    (hop : ¬ isHaltingOp op = true)
    (henv : EnvOK (model := model) env V R)
    (huniq : env.Unique)
    (htrA : trArgs fenv env args s₀ = some (ids, sA))
    (hA : EOutL (model := model) P f s₀ sA R ids argvals yst yst1)
    (hb : builtinWithExternal model.calls model.creates op argvals yst1
      (.ok [] yst'))
    (htr : trStmt fenv env lctx rets (.exprStmt (.builtin op args)) s₀
        = some (renv, s₁)) :
    SOut (model := model) P f lctx rets s₀ s₁ R renv V yst yst' .normal := by
  rw [trStmt] at htr
  obtain ⟨ids', sA', h1, htr⟩ := M.bind_inv htr
  obtain ⟨rfl, rfl⟩ : ids' = ids ∧ sA' = sA := by
    have he := h1.symm.trans htrA
    exact ⟨(M.some_pair_inj he).1, (M.some_pair_inj he).2⟩
  rw [if_neg hop] at htr
  obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
  rw [M.emit_apply] at h2
  obtain ⟨-, hsB⟩ := M.some_pair_inj h2
  obtain ⟨hrenv, hs₁⟩ := M.pure_inv h3
  obtain ⟨R₁, hle, hbelow, hfr, hget, hsim⟩ := hA
  subst hsB
  subst hs₁
  refine ⟨env, R₁, hrenv, hle, hbelow, hfr, henv.mono hle, huniq, ?_⟩
  refine hsim.trans ?_
  simpa using simS_op (model := model) (P := P) (f := f) (ds := ([] : List ValId))
    (fn := sA'.fn)
    (fn' := { sA'.fn with cur := Instr.op [] op ids' :: sA'.fn.cur })
    hget hb rfl rfl rfl

/-- **`letDecl vars none`** — the construction emits one zero `const` per
declared name and prepends them to its `VMap`; the source rule prepends
`bindZeros`. -/
theorem sim_letDecl_none {P : Prog} {f : Func} {fenv : FMap} {env : VMap}
    {R : Regs} {V : VEnv yulD} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {vars : List Ident} {s₀ s₁ : BState}
    {renv : Option VMap} {yst : EvmState}
    (hfresh : RegsFresh R s₀.fn) (henv : EnvOK (model := model) env V R)
    (huniq : env.Unique)
    (htr : trStmt fenv env lctx rets (.letDecl vars none) s₀ = some (renv, s₁)) :
    SOut (model := model) P f lctx rets s₀ s₁ R renv
      (YulSemantics.bindZeros yulD vars ++ V) yst yst .normal := by
  rw [trStmt] at htr
  by_cases hgate : (vars.any env.mem || !decide vars.Nodup) = true
  · rw [if_pos hgate] at htr
    obtain ⟨u, sA, h1, -⟩ := M.bind_inv htr
    exact absurd h1 (by simp [reject])
  rw [if_neg hgate] at htr
  obtain ⟨u, sA, h1, htr⟩ := M.bind_inv htr
  obtain ⟨-, hsA⟩ := M.pure_inv h1
  rw [hsA] at htr
  obtain ⟨ids, sB, h2, h3⟩ := M.bind_inv htr
  rw [mapM_constZero_spec] at h2
  obtain ⟨hids, hsB⟩ := M.some_pair_inj h2
  subst hids
  subst hsB
  obtain ⟨hrenv, hs₁⟩ := M.pure_inv h3
  subst hs₁
  have hnd : (List.range' s₀.fn.nextVal vars.length).Nodup := M.nodup_range' _ _
  have hlen : (List.range' s₀.fn.nextVal vars.length).length = vars.length := by simp
  have hnone : ∀ i ∈ List.range' s₀.fn.nextVal vars.length, R i = none :=
    fun i hi => hfresh i (M.mem_range'_bounds hi).1
  have hle := Regs.Le.setMany (vs := List.replicate
      (List.range' s₀.fn.nextVal vars.length).length (0 : U256)) hnd hnone
  refine ⟨vars.zip (List.range' s₀.fn.nextVal vars.length) ++ env,
    R.setMany (List.range' s₀.fn.nextVal vars.length)
      (List.replicate (List.range' s₀.fn.nextVal vars.length).length 0),
    hrenv, hle, ?_, ?_, ?_, ?_, ?_⟩
  · exact Regs.BelowEq.setMany fun i hi => (M.mem_range'_bounds hi).1
  · rw [hlen]
    exact hfresh.setMany (Nat.le_refl _)
  · exact EnvOK.append (EnvOK.zip_bindZeros hlen.symm
      (fun i hi => Regs.setMany_replicate_mem hnd i hi)) (henv.mono hle)
  · have ha : vars.any env.mem = false := by
      cases he : vars.any env.mem with
      | false => rfl
      | true => exact False.elim (hgate (by simp [he]))
    have hvnd : vars.Nodup := by
      by_contra hn
      exact hgate (by simp [hn])
    exact huniq.zip_append hvnd
      (fun x hx => Bool.eq_false_of_not_eq_true (List.any_eq_false.mp ha x hx)) hlen.symm
  · exact simS_consts _ R s₀.fn _ rfl rfl

/-- The statement-expression entry point needs its own expression induction
clause: unlike `trExpr`, it deliberately emits no destination for zero-result
builtins and calls. -/
def EStmtOut (P : Prog) (f : Func) (funs : YulSemantics.FunEnv yulD)
    (V : VEnv yulD) (yst : EvmState) (e : Expr Op)
    (V' : VEnv yulD) (yst' : EvmState) (o : Outcome) : Prop :=
  ∀ (fenv : FMap) (env : VMap) (R : Regs) (lctx : Option LoopCtx)
      (rets : Option (List Ident)) (s₀ s₁ : BState) (renv : Option VMap)
      (joins : List BlockId),
    FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
    env.Unique → RegsFresh R s₀.fn → CurValid s₀ →
    ProtectedAt joins s₀.fn → Completes f s₁.fn joins → CurPlaced f s₁.fn →
    (renv = none → CurFinal f s₁.fn) →
    trStmt fenv env lctx rets (.exprStmt e) s₀ = some (renv, s₁) →
    SOut (model := model) P f lctx rets s₀ s₁ R renv V' yst yst' o

/-- The construction tail corresponding exactly to the source `.loop` code
class, after the `for` initializer has run and its hoisted scope/environment
have been installed.  Keeping this as a named relation is what lets the loop
iteration IH talk about the header/body/post cycle independently of the outer
initializer and its final scope drop. -/
def trLoopCore (fenv : FMap) (env : VMap) (rets : Option (List Ident))
    (c : Expr Op) (post body : List (Stmt Op)) : M (Option VMap) := do
  let X := modifiedX env [post, body]
  let xvals ← edgeArgs env X
  let hParams ← X.mapM (fun _ => freshVal)
  let hId ← newBlock hParams
  let exitParams ← X.mapM (fun _ => freshVal)
  let exitId ← newBlock exitParams
  let postParams ← X.mapM (fun _ => freshVal)
  let postId ← newBlock postParams
  sealCur (.jump ⟨hId, xvals⟩)
  moveTo hId
  let envH := env.setMany X hParams
  let cv ← trExpr fenv envH c
  let bodyId ← newBlock []
  let hX ← edgeArgs envH X
  sealCur (.branch cv ⟨bodyId, []⟩ ⟨exitId, hX⟩)
  moveTo bodyId
  let lctx' : LoopCtx := ⟨exitId, postId, X⟩
  let renvB ← trScope fenv envH (some lctx') rets body
  if let some envB := renvB then
    let xvB ← edgeArgs envB X
    sealCur (.jump ⟨postId, xvB⟩)
  moveTo postId
  let envP := env.setMany X postParams
  let renvP ← trScope fenv envP none rets post
  if let some envP' := renvP then
    let xvP ← edgeArgs envP' X
    sealCur (.jump ⟨hId, xvP⟩)
  moveTo exitId
  pure (some (env.setMany X exitParams))

/-- A named decomposition of the one statically generated loop.  The source
loop induction revisits `sI`, but never translates another copy of the loop;
keeping the complete layout in one witness lets its IH reuse precisely these
header/body/post/exit blocks. -/
structure LoopLayout (fenv : FMap) (env : VMap) (rets : Option (List Ident))
    (c : Expr Op) (post body : List (Stmt Op)) (s₀ s₁ : BState)
    (renv : Option VMap) where
  xvals : List ValId
  sA : BState
  h1 : edgeArgs env (modifiedX env [post, body]) s₀ = some (xvals, sA)
  hParams : List ValId
  sB : BState
  h2 : (modifiedX env [post, body]).mapM (fun _ => freshVal) sA =
    some (hParams, sB)
  hId : BlockId
  sC : BState
  h3 : newBlock hParams sB = some (hId, sC)
  exitParams : List ValId
  sD : BState
  h4 : (modifiedX env [post, body]).mapM (fun _ => freshVal) sC =
    some (exitParams, sD)
  exitId : BlockId
  sE : BState
  h5 : newBlock exitParams sD = some (exitId, sE)
  postParams : List ValId
  sF : BState
  h6 : (modifiedX env [post, body]).mapM (fun _ => freshVal) sE =
    some (postParams, sF)
  postId : BlockId
  sG : BState
  h7 : newBlock postParams sF = some (postId, sG)
  sH : BState
  h8 : sealCur (.jump ⟨hId, xvals⟩) sG = some ((), sH)
  sI : BState
  h9 : moveTo hId sH = some ((), sI)
  cvId : ValId
  sJ : BState
  h10 : trExpr fenv
      (env.setMany (modifiedX env [post, body]) hParams) c sI =
    some (cvId, sJ)
  bodyId : BlockId
  sK : BState
  h11 : newBlock [] sJ = some (bodyId, sK)
  hX : List ValId
  sL : BState
  h12 : edgeArgs (env.setMany (modifiedX env [post, body]) hParams)
      (modifiedX env [post, body]) sK = some (hX, sL)
  sM : BState
  h13 : sealCur (.branch cvId ⟨bodyId, []⟩ ⟨exitId, hX⟩) sL =
    some ((), sM)
  sN : BState
  h14 : moveTo bodyId sM = some ((), sN)
  bodyEnv : Option VMap
  sO : BState
  h15 : trScope fenv
      (env.setMany (modifiedX env [post, body]) hParams)
      (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body sN =
    some (bodyEnv, sO)
  tail : (do
      if let some envB := bodyEnv then
        let xvB ← edgeArgs envB (modifiedX env [post, body])
        sealCur (.jump ⟨postId, xvB⟩)
      moveTo postId
      let envP := env.setMany (modifiedX env [post, body]) postParams
      let renvP ← trScope fenv envP none rets post
      if let some envP' := renvP then
        let xvP ← edgeArgs envP' (modifiedX env [post, body])
        sealCur (.jump ⟨hId, xvP⟩)
      moveTo exitId
      pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sO =
    some (renv, s₁)

/-- Successful construction exposes exactly one `LoopLayout`. -/
theorem LoopLayout.of_trLoopCore {fenv : FMap} {env : VMap}
    {rets : Option (List Ident)} {c : Expr Op} {post body : List (Stmt Op)}
    {s₀ s₁ : BState} {renv : Option VMap}
    (h : trLoopCore fenv env rets c post body s₀ = some (renv, s₁)) :
    Nonempty (LoopLayout fenv env rets c post body s₀ s₁ renv) := by
  unfold trLoopCore at h
  obtain ⟨xvals, sA, h1, h⟩ := M.bind_inv h
  obtain ⟨hParams, sB, h2, h⟩ := M.bind_inv h
  obtain ⟨hId, sC, h3, h⟩ := M.bind_inv h
  obtain ⟨exitParams, sD, h4, h⟩ := M.bind_inv h
  obtain ⟨exitId, sE, h5, h⟩ := M.bind_inv h
  obtain ⟨postParams, sF, h6, h⟩ := M.bind_inv h
  obtain ⟨postId, sG, h7, h⟩ := M.bind_inv h
  obtain ⟨uH, sH, h8, h⟩ := M.bind_inv h
  obtain ⟨uI, sI, h9, h⟩ := M.bind_inv h
  obtain ⟨cvId, sJ, h10, h⟩ := M.bind_inv h
  obtain ⟨bodyId, sK, h11, h⟩ := M.bind_inv h
  obtain ⟨hX, sL, h12, h⟩ := M.bind_inv h
  obtain ⟨uM, sM, h13, h⟩ := M.bind_inv h
  obtain ⟨uN, sN, h14, h⟩ := M.bind_inv h
  obtain ⟨bodyEnv, sO, h15, htail⟩ := M.bind_inv h
  exact ⟨⟨xvals, sA, h1, hParams, sB, h2, hId, sC, h3,
    exitParams, sD, h4, exitId, sE, h5, postParams, sF, h6,
    postId, sG, h7, sH, h8, sI, h9, cvId, sJ, h10,
    bodyId, sK, h11, hX, sL, h12, sM, h13, sN, h14,
    bodyEnv, sO, h15, htail⟩⟩

omit model in
/-- Replace only the final scope-dropping `pure` in the loop tail.  The four
body/post result shapes have identical builder effects before that `pure`. -/
theorem loopTail_drop_inv {fenv : FMap} {env envI : VMap}
    {rets : Option (List Ident)} {post body : List (Stmt Op)}
    {hId exitId postId : BlockId} {exitParams postParams : List ValId}
    {bodyEnv : Option VMap} {sO s₁ : BState} {renv : Option VMap}
    (h : (do
      if let some envB := bodyEnv then
        let xvB ← edgeArgs envB (modifiedX envI [post, body])
        sealCur (.jump ⟨postId, xvB⟩)
      moveTo postId
      let envP := envI.setMany (modifiedX envI [post, body]) postParams
      let renvP ← trScope fenv envP none rets post
      if let some envP' := renvP then
        let xvP ← edgeArgs envP' (modifiedX envI [post, body])
        sealCur (.jump ⟨hId, xvP⟩)
      moveTo exitId
      let envX := envI.setMany (modifiedX envI [post, body]) exitParams
      pure (some (envX.drop (envX.length - env.length)))) sO =
        some (renv, s₁)) :
    (do
      if let some envB := bodyEnv then
        let xvB ← edgeArgs envB (modifiedX envI [post, body])
        sealCur (.jump ⟨postId, xvB⟩)
      moveTo postId
      let envP := envI.setMany (modifiedX envI [post, body]) postParams
      let renvP ← trScope fenv envP none rets post
      if let some envP' := renvP then
        let xvP ← edgeArgs envP' (modifiedX envI [post, body])
        sealCur (.jump ⟨hId, xvP⟩)
      moveTo exitId
      pure (some (envI.setMany (modifiedX envI [post, body]) exitParams))) sO =
        some (some (envI.setMany (modifiedX envI [post, body]) exitParams), s₁) ∧
      renv = some ((envI.setMany (modifiedX envI [post, body]) exitParams).drop
        ((envI.setMany (modifiedX envI [post, body]) exitParams).length - env.length)) := by
  cases bodyEnv with
  | none =>
      obtain ⟨uP, sP, h16, h⟩ := M.bind_inv h
      obtain ⟨-, hsP⟩ := M.pure_inv h16
      subst sP
      obtain ⟨uQ, sQ, h17, h⟩ := M.bind_inv h
      obtain ⟨postEnv, sR, h18, h⟩ := M.bind_inv h
      cases postEnv with
      | none =>
          obtain ⟨uS, sS, h19, h⟩ := M.bind_inv h
          obtain ⟨-, hsS⟩ := M.pure_inv h19
          subst sS
          obtain ⟨uT, sT, h20, h⟩ := M.bind_inv h
          obtain ⟨hrenv, hs₁⟩ := M.pure_inv h
          subst s₁
          constructor
          · simp only [bind, StateT.bind, Option.bind, pure, StateT.pure,
              h17, h18, h20]
          · exact hrenv
      | some envP =>
          obtain ⟨xvP, sS, h19, h⟩ := M.bind_inv h
          obtain ⟨uT, sT, h20, h⟩ := M.bind_inv h
          obtain ⟨uU, sU, h21, h⟩ := M.bind_inv h
          obtain ⟨hrenv, hs₁⟩ := M.pure_inv h
          subst s₁
          constructor
          · simp only [bind, StateT.bind, Option.bind, pure, StateT.pure,
              h17, h18, h19, h20, h21]
          · exact hrenv
  | some envB =>
      obtain ⟨xvB, sP, h16, h⟩ := M.bind_inv h
      obtain ⟨uQ, sQ, h17, h⟩ := M.bind_inv h
      obtain ⟨uR, sR, h18, h⟩ := M.bind_inv h
      obtain ⟨postEnv, sS, h19, h⟩ := M.bind_inv h
      cases postEnv with
      | none =>
          obtain ⟨uT, sT, h20, h⟩ := M.bind_inv h
          obtain ⟨-, hsT⟩ := M.pure_inv h20
          subst sT
          obtain ⟨uU, sU, h21, h⟩ := M.bind_inv h
          obtain ⟨hrenv, hs₁⟩ := M.pure_inv h
          subst s₁
          constructor
          · simp only [bind, StateT.bind, Option.bind, pure, StateT.pure,
              h16, h17, h18, h19, h21]
          · exact hrenv
      | some envP =>
          obtain ⟨xvP, sT, h20, h⟩ := M.bind_inv h
          obtain ⟨uU, sU, h21, h⟩ := M.bind_inv h
          obtain ⟨uW, sW, h22, h⟩ := M.bind_inv h
          obtain ⟨hrenv, hs₁⟩ := M.pure_inv h
          subst s₁
          constructor
          · simp only [bind, StateT.bind, Option.bind, pure, StateT.pure,
              h16, h17, h18, h19, h20, h21, h22]
          · exact hrenv

omit model in
/-- Invert the `forLoop` wrapper into its initializer and the inner static loop
layout.  The layout ends before the wrapper drops initializer declarations. -/
theorem trStmt_forLoop_inv {fenv : FMap} {env : VMap}
    {lctx : Option LoopCtx} {rets : Option (List Ident)}
    {init post body : List (Stmt Op)} {c : Expr Op}
    {s₀ s₁ : BState} {renv : Option VMap}
    (h : trStmt fenv env lctx rets (.forLoop init c post body) s₀ =
      some (renv, s₁)) :
    ∃ (scope : List (Ident × FuncId)) (sA sI : BState)
        (rinit : Option VMap),
      allocScope init s₀ = some (scope, sA) ∧
      trStmts (scope :: fenv) env lctx rets false init sA = some (rinit, sI) ∧
      match rinit with
      | none => renv = none ∧ s₁ = sI
      | some envI => ∃ envX,
          Nonempty (LoopLayout (scope :: fenv) envI rets c post body
            sI s₁ (some envX)) ∧
          renv = some (envX.drop (envX.length - env.length)) := by
  unfold trStmt at h
  obtain ⟨scope, sA, ha, h⟩ := M.bind_inv h
  obtain ⟨rinit, sI, hi, h⟩ := M.bind_inv h
  refine ⟨scope, sA, sI, rinit, ha, hi, ?_⟩
  cases rinit with
  | none => exact M.pure_inv h
  | some envI =>
      obtain ⟨xvals, sB, h1, h⟩ := M.bind_inv h
      obtain ⟨hParams, sC, h2, h⟩ := M.bind_inv h
      obtain ⟨hId, sD, h3, h⟩ := M.bind_inv h
      obtain ⟨exitParams, sE, h4, h⟩ := M.bind_inv h
      obtain ⟨exitId, sF, h5, h⟩ := M.bind_inv h
      obtain ⟨postParams, sG, h6, h⟩ := M.bind_inv h
      obtain ⟨postId, sH, h7, h⟩ := M.bind_inv h
      obtain ⟨uI, sI', h8, h⟩ := M.bind_inv h
      obtain ⟨uJ, sJ, h9, h⟩ := M.bind_inv h
      obtain ⟨cvId, sK, h10, h⟩ := M.bind_inv h
      obtain ⟨bodyId, sL, h11, h⟩ := M.bind_inv h
      obtain ⟨hX, sM, h12, h⟩ := M.bind_inv h
      obtain ⟨uN, sN, h13, h⟩ := M.bind_inv h
      obtain ⟨uO, sO, h14, h⟩ := M.bind_inv h
      obtain ⟨bodyEnv, sP, h15, htail⟩ := M.bind_inv h
      obtain ⟨htail', hrenv⟩ := loopTail_drop_inv htail
      let envX := envI.setMany (modifiedX envI [post, body]) exitParams
      exact ⟨envX, ⟨⟨xvals, sB, h1, hParams, sC, h2, hId, sD, h3,
        exitParams, sE, h4, exitId, sF, h5, postParams, sG, h6,
        postId, sH, h7, sI', h8, sJ, h9, cvId, sK, h10,
        bodyId, sL, h11, hX, sM, h12, sN, h13, sO, h14,
        bodyEnv, sP, h15, htail'⟩⟩, hrenv⟩

omit model in
/-- The code after the body of a fixed loop layout is closed with respect to
the function table present at body exit. -/
theorem LoopLayout.tail_fprefix {fenv : FMap} {env : VMap}
    {rets : Option (List Ident)} {c : Expr Op} {post body : List (Stmt Op)}
    {s₀ s₁ : BState} {renv : Option VMap}
    (layout : LoopLayout fenv env rets c post body s₀ s₁ renv) :
    FPrefix layout.sO.funcs.size layout.sO s₁ := by
  rcases layout with
    ⟨xvals, sA, h1, hParams, sB, h2, hId, sC, h3,
     exitParams, sD, h4, exitId, sE, h5, postParams, sF, h6,
     postId, sG, h7, sH, h8, sI, h9, cvId, sJ, h10,
     bodyId, sK, h11, hX, sL, h12, sM, h13, sN, h14,
     bodyEnv, sO, h15, htail⟩
  cases bodyEnv with
  | none =>
      change (do
        moveTo postId
        let envP := env.setMany (modifiedX env [post, body]) postParams
        let renvP ← trScope fenv envP none rets post
        if let some envP' := renvP then
          let xvP ← edgeArgs envP' (modifiedX env [post, body])
          sealCur (.jump ⟨hId, xvP⟩)
        moveTo exitId
        pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sO =
          some (renv, s₁) at htail
      obtain ⟨uP, sP, h16, htail⟩ := M.bind_inv htail
      obtain ⟨postEnv, sQ, h17, htail⟩ := M.bind_inv htail
      have pOP : FPrefix sO.funcs.size sO sP := FPrefix.of_moveTo h16
      have pOQ : FPrefix sO.funcs.size sO sQ := pOP.trans
        (trScope_fprefix fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sO.funcs.size sP postEnv sQ (pOP.size (Nat.le_refl _)) h17)
      cases postEnv with
      | none =>
          obtain ⟨uR, sR, h18, htail⟩ := M.bind_inv htail
          obtain ⟨-, rfl⟩ := M.pure_inv h18
          obtain ⟨uT, sT, h19, htail⟩ := M.bind_inv htail
          obtain ⟨-, rfl⟩ := M.pure_inv h19
          obtain ⟨-, rfl⟩ := M.pure_inv htail
          exact pOQ
      | some envP =>
          obtain ⟨xvP, sR, h18, htail⟩ := M.bind_inv htail
          obtain ⟨uS, sS, h19, htail⟩ := M.bind_inv htail
          obtain ⟨uT, sT, h20, htail⟩ := M.bind_inv htail
          obtain ⟨-, rfl⟩ := M.pure_inv htail
          exact ((pOQ.trans (FPrefix.of_edgeArgs h18)).trans
            (FPrefix.of_sealCur h19)).trans (FPrefix.of_moveTo h20)
  | some envB =>
      obtain ⟨xvB, sP, h16, htail⟩ := M.bind_inv htail
      obtain ⟨uQ, sQ, h17, htail⟩ := M.bind_inv htail
      obtain ⟨uR, sR, h18, htail⟩ := M.bind_inv htail
      obtain ⟨postEnv, sS, h19, htail⟩ := M.bind_inv htail
      have pOR : FPrefix sO.funcs.size sO sR :=
        (((FPrefix.of_edgeArgs h16).trans (FPrefix.of_sealCur h17)).trans
          (FPrefix.of_moveTo h18))
      have pOS : FPrefix sO.funcs.size sO sS := pOR.trans
        (trScope_fprefix fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sO.funcs.size sR postEnv sS (pOR.size (Nat.le_refl _)) h19)
      cases postEnv with
      | none =>
          obtain ⟨uT, sT, h20, htail⟩ := M.bind_inv htail
          obtain ⟨-, rfl⟩ := M.pure_inv h20
          obtain ⟨uU, sU, h21, htail⟩ := M.bind_inv htail
          obtain ⟨-, rfl⟩ := M.pure_inv h21
          obtain ⟨-, rfl⟩ := M.pure_inv htail
          exact pOS
      | some envP =>
          obtain ⟨xvP, sT, h20, htail⟩ := M.bind_inv htail
          obtain ⟨uU, sU, h21, htail⟩ := M.bind_inv htail
          obtain ⟨uW, sW, h22, htail⟩ := M.bind_inv htail
          obtain ⟨-, rfl⟩ := M.pure_inv htail
          exact ((pOS.trans (FPrefix.of_edgeArgs h20)).trans
            (FPrefix.of_sealCur h21)).trans (FPrefix.of_moveTo h22)

omit model in
/-- A complete loop layout preserves every function-table slot that existed at
its preheader. -/
theorem LoopLayout.fprefix {fenv : FMap} {env : VMap}
    {rets : Option (List Ident)} {c : Expr Op} {post body : List (Stmt Op)}
    {s₀ s₁ : BState} {renv : Option VMap}
    (layout : LoopLayout fenv env rets c post body s₀ s₁ renv) :
    FPrefix s₀.funcs.size s₀ s₁ := by
  have ptail := layout.tail_fprefix
  rcases layout with
    ⟨xvals, sA, h1, hParams, sB, h2, hId, sC, h3,
     exitParams, sD, h4, exitId, sE, h5, postParams, sF, h6,
     postId, sG, h7, sH, h8, sI, h9, cvId, sJ, h10,
     bodyId, sK, h11, hX, sL, h12, sM, h13, sN, h14,
     bodyEnv, sO, h15, htail⟩
  have p0A : FPrefix s₀.funcs.size s₀ sA := FPrefix.of_edgeArgs h1
  have p0B := p0A.trans (FPrefix.of_grows (Grows.of_mapM_freshVal h2))
  have p0C := p0B.trans (FPrefix.of_newBlock h3)
  have p0D := p0C.trans (FPrefix.of_grows (Grows.of_mapM_freshVal h4))
  have p0E := p0D.trans (FPrefix.of_newBlock h5)
  have p0F := p0E.trans (FPrefix.of_grows (Grows.of_mapM_freshVal h6))
  have p0G := p0F.trans (FPrefix.of_newBlock h7)
  have p0H := p0G.trans (FPrefix.of_sealCur h8)
  have p0I := p0H.trans (FPrefix.of_moveTo h9)
  have p0J := p0I.trans
    (FPrefix.of_grows (trExpr_grows c fenv
      (env.setMany (modifiedX env [post, body]) hParams) sI sJ cvId h10))
  have p0K := p0J.trans (FPrefix.of_newBlock h11)
  have p0L := p0K.trans (FPrefix.of_edgeArgs h12)
  have p0M := p0L.trans (FPrefix.of_sealCur h13)
  have p0N := p0M.trans (FPrefix.of_moveTo h14)
  have p0O := p0N.trans
    (trScope_fprefix fenv
      (env.setMany (modifiedX env [post, body]) hParams)
      (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
      s₀.funcs.size sN bodyEnv sO (p0N.size (Nat.le_refl _)) h15)
  exact p0O.trans (ptail.mono (p0O.size (Nat.le_refl _)))

omit model in
/-- Everything after entering the loop header grows above the loop's entry
block watermark.  This is the framing fact needed to recover placement of the
initializer's open continuation from the completed loop layout. -/
theorem LoopLayout.header_tail_sgrows {fenv : FMap} {env : VMap}
    {rets : Option (List Ident)} {c : Expr Op} {post body : List (Stmt Op)}
    {s₀ s₁ : BState} {renv : Option VMap}
    (layout : LoopLayout fenv env rets c post body s₀ s₁ renv) :
    SGrowsAt s₀.fn.blocks.size layout.sI s₁ := by
  rcases layout with
    ⟨xvals, sA, h1, hParams, sB, h2, hId, sC, h3,
     exitParams, sD, h4, exitId, sE, h5, postParams, sF, h6,
     postId, sG, h7, sH, h8, sI, h9, cvId, sJ, h10,
     bodyId, sK, h11, hX, sL, h12, sM, h13, sN, h14,
     bodyEnv, sO, h15, htail⟩
  have g0A : Grows s₀ sA := Grows.of_liftO h1
  have a0B : SGrowsAt s₀.fn.blocks.size s₀ sB :=
    (SGrowsAt.of_grows g0A).trans
      (SGrowsAt.of_grows (Grows.of_mapM_freshVal h2))
  have a0C := a0B.trans (SGrowsAt.of_newBlock h3)
  have a0D := a0C.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h4))
  have a0E := a0D.trans (SGrowsAt.of_newBlock h5)
  have a0F := a0E.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h6))
  have a0G := a0F.trans (SGrowsAt.of_newBlock h7)
  have a0H := a0G.trans (SGrowsAt.of_sealCur h8)
  have hheader : s₀.fn.blocks.size ≤ hId := by
    rw [SGrowsAt.newBlock_id h3]
    exact a0B.size
  have a0I := a0H.trans (SGrowsAt.of_moveTo (Or.inl hheader) h9)
  have aIJ : SGrowsAt s₀.fn.blocks.size sI sJ :=
    SGrowsAt.of_grows (trExpr_grows c fenv
      (env.setMany (modifiedX env [post, body]) hParams) sI sJ cvId h10)
  have aIK := aIJ.trans (SGrowsAt.of_newBlock h11)
  have aIL := aIK.trans (SGrowsAt.of_edgeArgs h12)
  have aIM := aIL.trans (SGrowsAt.of_sealCur h13)
  have hbody : s₀.fn.blocks.size ≤ bodyId := by
    rw [SGrowsAt.newBlock_id h11]
    exact Nat.le_trans a0I.size aIJ.size
  have aIN := aIM.trans (SGrowsAt.of_moveTo (Or.inl hbody) h14)
  have gbody := trScope_grows fenv
    (env.setMany (modifiedX env [post, body]) hParams)
    (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
    sN bodyEnv sO h15
  have aIO := aIN.trans (gbody.mono (Nat.le_trans a0I.size aIN.size))
  have hpost : s₀.fn.blocks.size ≤ postId := by
    rw [SGrowsAt.newBlock_id h7]
    exact a0F.size
  have hexit : s₀.fn.blocks.size ≤ exitId := by
    rw [SGrowsAt.newBlock_id h5]
    exact a0D.size
  cases bodyEnv with
  | none =>
      change (do
        moveTo postId
        let envP := env.setMany (modifiedX env [post, body]) postParams
        let renvP ← trScope fenv envP none rets post
        if let some envP' := renvP then
          let xvP ← edgeArgs envP' (modifiedX env [post, body])
          sealCur (.jump ⟨hId, xvP⟩)
        moveTo exitId
        pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sO =
          some (renv, s₁) at htail
      obtain ⟨uP, sP, h16, htail⟩ := M.bind_inv htail
      obtain ⟨postEnv, sQ, h17, htail⟩ := M.bind_inv htail
      have aIP := aIO.trans (SGrowsAt.of_moveTo (Or.inl hpost) h16)
      have gp := trScope_grows fenv
        (env.setMany (modifiedX env [post, body]) postParams) none rets post
        sP postEnv sQ h17
      have aIQ := aIP.trans (gp.mono (Nat.le_trans a0I.size aIP.size))
      cases postEnv with
      | none =>
          obtain ⟨uR, sR, h18, htail⟩ := M.bind_inv htail
          obtain ⟨uT, sT, h19, htail⟩ := M.bind_inv htail
          exact ((aIQ.trans (SGrowsAt.of_pure h18)).trans
            (SGrowsAt.of_moveTo (Or.inl hexit) h19)).trans
              (SGrowsAt.of_pure htail)
      | some envP =>
          obtain ⟨xvP, sR, h18, htail⟩ := M.bind_inv htail
          obtain ⟨uS, sS, h19, htail⟩ := M.bind_inv htail
          obtain ⟨uT, sT, h20, htail⟩ := M.bind_inv htail
          obtain ⟨-, rfl⟩ := M.pure_inv htail
          exact (((aIQ.trans (SGrowsAt.of_edgeArgs h18)).trans
            (SGrowsAt.of_sealCur h19)).trans
              (SGrowsAt.of_moveTo (Or.inl hexit) h20))
  | some envB =>
      obtain ⟨xvB, sP, h16, htail⟩ := M.bind_inv htail
      obtain ⟨uQ, sQ, h17, htail⟩ := M.bind_inv htail
      obtain ⟨uR, sR, h18, htail⟩ := M.bind_inv htail
      obtain ⟨postEnv, sS, h19, htail⟩ := M.bind_inv htail
      have aIR := (((aIO.trans (SGrowsAt.of_edgeArgs h16)).trans
        (SGrowsAt.of_sealCur h17)).trans
          (SGrowsAt.of_moveTo (Or.inl hpost) h18))
      have gp := trScope_grows fenv
        (env.setMany (modifiedX env [post, body]) postParams) none rets post
        sR postEnv sS h19
      have aIS := aIR.trans (gp.mono (Nat.le_trans a0I.size aIR.size))
      cases postEnv with
      | none =>
          obtain ⟨uT, sT, h20, htail⟩ := M.bind_inv htail
          obtain ⟨uU, sU, h21, htail⟩ := M.bind_inv htail
          exact ((aIS.trans (SGrowsAt.of_pure h20)).trans
            (SGrowsAt.of_moveTo (Or.inl hexit) h21)).trans
              (SGrowsAt.of_pure htail)
      | some envP =>
          obtain ⟨xvP, sT, h20, htail⟩ := M.bind_inv htail
          obtain ⟨uU, sU, h21, htail⟩ := M.bind_inv htail
          obtain ⟨uW, sW, h22, htail⟩ := M.bind_inv htail
          obtain ⟨-, rfl⟩ := M.pure_inv htail
          exact (((aIS.trans (SGrowsAt.of_edgeArgs h20)).trans
            (SGrowsAt.of_sealCur h21)).trans
              (SGrowsAt.of_moveTo (Or.inl hexit) h22))

omit model in
/-- A complete loop layout grows above its preheader's block watermark. -/
theorem LoopLayout.sgrows {fenv : FMap} {env : VMap}
    {rets : Option (List Ident)} {c : Expr Op} {post body : List (Stmt Op)}
    {s₀ s₁ : BState} {renv : Option VMap}
    (layout : LoopLayout fenv env rets c post body s₀ s₁ renv) :
    SGrowsAt s₀.fn.blocks.size s₀ s₁ := by
  have htail := layout.header_tail_sgrows
  rcases layout with
    ⟨xvals, sA, h1, hParams, sB, h2, hId, sC, h3,
     exitParams, sD, h4, exitId, sE, h5, postParams, sF, h6,
     postId, sG, h7, sH, h8, sI, h9, cvId, sJ, h10,
     bodyId, sK, h11, hX, sL, h12, sM, h13, sN, h14,
     bodyEnv, sO, h15, htr⟩
  have a0A : SGrowsAt s₀.fn.blocks.size s₀ sA :=
    SGrowsAt.of_grows (Grows.of_liftO h1)
  have a0B := a0A.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h2))
  have a0C := a0B.trans (SGrowsAt.of_newBlock h3)
  have a0D := a0C.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h4))
  have a0E := a0D.trans (SGrowsAt.of_newBlock h5)
  have a0F := a0E.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h6))
  have a0G := a0F.trans (SGrowsAt.of_newBlock h7)
  have a0H := a0G.trans (SGrowsAt.of_sealCur h8)
  have hheader : s₀.fn.blocks.size ≤ hId := by
    rw [SGrowsAt.newBlock_id h3]
    exact a0B.size
  exact (a0H.trans (SGrowsAt.of_moveTo (Or.inl hheader) h9)).trans htail

omit model in
/-- The preheader in a successful loop layout is sealed and left for the fresh
header, and later construction cannot return to it. -/
theorem LoopLayout.curMoved {fenv : FMap} {env : VMap}
    {rets : Option (List Ident)} {c : Expr Op} {post body : List (Stmt Op)}
    {s₀ s₁ : BState} {renv : Option VMap}
    (layout : LoopLayout fenv env rets c post body s₀ s₁ renv)
    (hvalid : CurValid s₀) : CurMoved s₀ s₁ := by
  have htail := layout.header_tail_sgrows
  rcases layout with
    ⟨xvals, sA, h1, hParams, sB, h2, hId, sC, h3,
     exitParams, sD, h4, exitId, sE, h5, postParams, sF, h6,
     postId, sG, h7, sH, h8, sI, h9, cvId, sJ, h10,
     bodyId, sK, h11, hX, sL, h12, sM, h13, sN, h14,
     bodyEnv, sO, h15, htr⟩
  have cs0G : CurSame s₀ sG :=
    ((((((CurSame.of_grows (Grows.of_liftO h1)).trans
      (CurSame.of_grows (Grows.of_mapM_freshVal h2))).trans
      (CurSame.of_newBlock h3)).trans
      (CurSame.of_grows (Grows.of_mapM_freshVal h4))).trans
      (CurSame.of_newBlock h5)).trans
      (CurSame.of_grows (Grows.of_mapM_freshVal h6))).trans
      (CurSame.of_newBlock h7)
  have hne : sG.fn.curId ≠ hId := by
    rw [cs0G.1, SGrowsAt.newBlock_id h3]
    have a0B : SGrowsAt s₀.fn.blocks.size s₀ sB :=
      (SGrowsAt.of_grows (N := s₀.fn.blocks.size) (Grows.of_liftO h1)).trans
        (SGrowsAt.of_grows (Grows.of_mapM_freshVal h2))
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hvalid a0B.size)
  have hmGI : CurMoved sG sI := curMoved_of_seal_move hne h8 h9
  have hm0I : CurMoved s₀ sI := cs0G.transMoved hmGI
  have a0B : SGrows s₀ sB :=
    (SGrowsAt.of_grows (N := s₀.fn.blocks.size) (Grows.of_liftO h1)).trans
      (SGrowsAt.of_grows (Grows.of_mapM_freshVal h2))
  have a0C := a0B.trans (SGrowsAt.of_newBlock h3)
  have a0D := a0C.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h4))
  have a0E := a0D.trans (SGrowsAt.of_newBlock h5)
  have a0F := a0E.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h6))
  have a0G := a0F.trans (SGrowsAt.of_newBlock h7)
  have a0H := a0G.trans (SGrowsAt.of_sealCur h8)
  have hheader : s₀.fn.blocks.size ≤ hId := by
    rw [SGrowsAt.newBlock_id h3]
    exact a0B.size
  have g0I : SGrows s₀ sI :=
    SGrowsAt.trans a0H
      (SGrowsAt.of_moveTo (N := s₀.fn.blocks.size) (Or.inl hheader) h9)
  exact hm0I.forward hvalid g0I htail

omit model in
theorem loopPostTail_fprefix {envP : Option VMap} {X : List Ident}
    {hId exitId : BlockId} {s s' : BState} {out renv : Option VMap}
    (h : (do
      if let some envP' := envP then
        let xvP ← edgeArgs envP' X
        sealCur (.jump ⟨hId, xvP⟩)
      moveTo exitId
      pure out) s = some (renv, s')) :
    FPrefix s.funcs.size s s' := by
  cases envP with
  | none =>
      obtain ⟨u, s1, h1, h2⟩ := M.bind_inv h
      obtain ⟨-, rfl⟩ := M.pure_inv h1
      obtain ⟨u', s2, h2, h3⟩ := M.bind_inv h2
      obtain ⟨-, rfl⟩ := M.pure_inv h3
      exact FPrefix.of_moveTo h2
  | some envP' =>
      obtain ⟨xv, s1, h1, h⟩ := M.bind_inv h
      obtain ⟨u, s2, h2, h⟩ := M.bind_inv h
      obtain ⟨u', s3, h3, h4⟩ := M.bind_inv h
      obtain ⟨-, rfl⟩ := M.pure_inv h4
      exact ((FPrefix.of_edgeArgs h1).trans (FPrefix.of_sealCur h2)).trans
        (FPrefix.of_moveTo h3)

/-- Loop simulation beginning at the already-bound header parameters.  The
`base` watermark precedes all three reserved parameter vectors, so a normal
result may bind post/exit parameters while still preserving the caller's
register file below `base`. -/
def LHOut (P : Prog) (f : Func) (rets : Option (List Ident)) (base : Nat)
    (sH s₁ : BState) (RH : Regs) (renv : Option VMap)
    (V' : VEnv yulD) (yst yst' : EvmState) (o : Outcome) : Prop :=
  match o with
  | .normal => ∃ (env' : VMap) (R₁ : Regs),
      renv = some env' ∧ Regs.BelowEq base RH R₁
        ∧ RegsFresh R₁ s₁.fn ∧ EnvOK (model := model) env' V' R₁
        ∧ env'.Unique
        ∧ SimS (model := model) P f sH.fn RH yst s₁.fn R₁ yst'
  | .halt => ExecFrom (model := model) P f sH.fn RH yst (.halt yst')
  | .leave => ∃ (rs : List Ident) (vals : List U256),
      rets = some rs
        ∧ List.Forall₂ (fun x v => YulSemantics.VEnv.get V' x = some v) rs vals
        ∧ ExecFrom (model := model) P f sH.fn RH yst (.ret vals yst')
  | .break | .continue => False

/-- Prepend the preheader-to-header simulation to a loop result. -/
theorem LHOut.prefix {P : Prog} {f : Func} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {base : Nat} {s₀ sH s₁ : BState}
    {R₀ RH : Regs} {renv : Option VMap} {V' : VEnv yulD}
    {yst ystH yst' : EvmState} {o : Outcome}
    (hbase : s₀.fn.nextVal ≤ base)
    (hbelow : Regs.BelowEq s₀.fn.nextVal R₀ RH)
    (hfresh : RegsFresh R₀ s₀.fn)
    (hsim : SimS (model := model) P f s₀.fn R₀ yst sH.fn RH ystH)
    (h : LHOut (model := model) P f rets base sH s₁ RH renv
      V' ystH yst' o) :
    SOut (model := model) P f lctx rets s₀ s₁ R₀ renv
      V' yst yst' o := by
  cases o with
  | normal =>
      obtain ⟨env', R₁, hrenv, hbelow₁, hfr, henv, huniq, hsim₁⟩ := h
      have hbelowEnd := hbelow.trans (hbelow₁.mono hbase)
      have hleEnd : Regs.Le R₀ R₁ := by
        intro i v hi
        by_cases hilow : i < s₀.fn.nextVal
        · rw [hbelowEnd i hilow]
          exact hi
        · exact absurd hi (by rw [hfresh i (Nat.le_of_not_gt hilow)]; simp)
      exact ⟨env', R₁, hrenv, hleEnd, hbelowEnd,
        hfr, henv, huniq, hsim.trans hsim₁⟩
  | halt => exact hsim _ h
  | leave =>
      obtain ⟨rs, vals, hrets, hvals, hex⟩ := h
      exact ⟨rs, vals, hrets, hvals, hsim _ hex⟩
  | «break» => exact h.elim
  | «continue» => exact h.elim

/-- A source loop iteration cannot expose `break` or `continue`: both are
consumed by the loop rules themselves. -/
theorem loop_outcome_ssa {funs : YulSemantics.FunEnv yulD} {V : VEnv yulD}
    {yst : EvmState} {c : Expr Op} {post body : List (Stmt Op)}
    {V' : VEnv yulD} {yst' : EvmState} {o : Outcome}
    (h : YulSemantics.Step yulD funs V yst (.loop c post body)
      (.sres V' yst' o)) :
    o = .normal ∨ o = .halt ∨ o = .leave := by
  generalize hc : (YulSemantics.Code.loop c post body
    : YulSemantics.Code Op) = code at h
  generalize hr : (YulSemantics.Res.sres V' yst' o
    : YulSemantics.Res yulD) = res at h
  induction h generalizing V' yst' o <;> try cases hc
  case loopDone =>
    cases hr
    exact .inl rfl
  case loopCondHalt =>
    cases hr
    exact .inr (.inl rfl)
  case loopStep ihc ihbody ihpost ihrest =>
    exact ihrest rfl hr
  case loopPostHalt =>
    cases hr
    exact .inr (.inl rfl)
  case loopBreak =>
    cases hr
    exact .inl rfl
  case loopLeave =>
    cases hr
    exact .inr (.inr rfl)
  case loopBodyHalt =>
    cases hr
    exact .inr (.inl rfl)

/-- At a loop header, only its parameter vector may be bound among ids
reserved since the preheader watermark.  A back edge obtains such a file by
starting from the preheader file and rebinding exactly `hParams`; the live file
may contain more iteration temporaries and is reached later with `Exec.mono`. -/
def HeaderClean (base : Nat) (hParams : List ValId) (R : Regs) : Prop :=
  ∀ i, base ≤ i → i ∉ hParams → R i = none

/-- Rebinding the header parameter vector updates exactly the source variables
represented by the header map.  This packages the no-alias placement fact the
static layout establishes for its fresh parameter ids. -/
def HeaderRebind (envH : VMap) (X : List Ident) (hParams : List ValId)
    (V : VEnv yulD) (R : Regs) : Prop :=
  ∀ (vals : List U256) (W : VEnv yulD),
    X.length = vals.length →
    YulSemantics.VEnv.setMany V X vals = W →
    EnvOK (model := model) envH W (R.setMany hParams vals)

set_option maxHeartbeats 1000000 in
/-- Execute the loop preheader edge and bind the first header parameter
vector, establishing the iteration invariant expected by `LOut`. -/
theorem LoopLayout.enter {P : Prog} {f : Func} {fenv : FMap} {env : VMap}
    {rets : Option (List Ident)} {c : Expr Op} {post body : List (Stmt Op)}
    {s₀ s₁ : BState} {renv : Option VMap} {joins : List BlockId}
    {V : VEnv yulD} {R : Regs} {yst : EvmState}
    (layout : LoopLayout fenv env rets c post body s₀ s₁ renv)
    (henv : EnvOK (model := model) env V R) (huniq : env.Unique)
    (hfr : RegsFresh R s₀.fn) (hvalid : CurValid s₀)
    (hp : ProtectedAt joins s₀.fn) (hcompl : Completes f s₁.fn joins) :
    ∃ RH : Regs,
      Regs.BelowEq s₀.fn.nextVal R RH ∧
      RegsFresh RH layout.sI.fn ∧
      EnvOK (model := model)
        (env.setMany (modifiedX env [post, body]) layout.hParams) V RH ∧
      HeaderClean layout.sA.fn.nextVal layout.hParams RH ∧
      HeaderRebind (model := model)
        (env.setMany (modifiedX env [post, body]) layout.hParams)
        (modifiedX env [post, body]) layout.hParams V RH ∧
      SimS (model := model) P f s₀.fn R yst layout.sI.fn RH yst := by
  have htail := layout.header_tail_sgrows
  rcases layout with
    ⟨xvals, sA, h1, hParams, sB, h2, hId, sC, h3,
     exitParams, sD, h4, exitId, sE, h5, postParams, sF, h6,
     postId, sG, h7, sH, h8, sI, h9, cvId, sJ, h10,
     bodyId, sK, h11, hX, sL, h12, sM, h13, sN, h14,
     bodyEnv, sO, h15, htr⟩
  simp only [LoopLayout.sI, LoopLayout.hParams, LoopLayout.sA] at htail ⊢
  obtain ⟨hsA, vals, hget, hvals⟩ := edgeArgs_ok henv h1
  subst sA
  obtain ⟨hlenH, hrangeH, hsB⟩ := M.mapM_freshVal_length h2
  have hndH : hParams.Nodup := by rw [hrangeH]; exact M.nodup_range' _ _
  have hnoneH : ∀ i ∈ hParams, R i = none := by
    intro i hi
    exact hfr i (by rw [hrangeH] at hi; exact (M.mem_range'_bounds hi).1)
  let RH := R.setMany hParams vals
  have hleH : Regs.Le R RH := Regs.Le.setMany hndH hnoneH
  have hbelowH : Regs.BelowEq s₀.fn.nextVal R RH := by
    exact Regs.BelowEq.setMany (fun i hi => by
      rw [hrangeH] at hi
      exact (M.mem_range'_bounds hi).1)
  have hgetH : RH.getMany hParams = some vals :=
    Regs.getMany_setMany_self hndH (hlenH.trans hvals.length_eq)
  have henvH : EnvOK (model := model)
      (env.setMany (modifiedX env [post, body]) hParams) V RH := by
    have he := EnvOK.setMany (xs := modifiedX env [post, body])
      (henv.mono hleH)
      (Regs.getMany_eq_some_iff.mp hgetH)
    rw [VEnv.setMany_self hvals] at he
    exact he
  have hcleanH : HeaderClean s₀.fn.nextVal hParams RH := by
    intro i hi hnot
    dsimp [RH]
    rw [Regs.setMany_other hnot]
    exact hfr i hi
  have hrebH : HeaderRebind (model := model)
      (env.setMany (modifiedX env [post, body]) hParams)
      (modifiedX env [post, body]) hParams V RH := by
    intro vals' W hlen' hset'
    have hle' : Regs.Le R (R.setMany hParams vals') :=
      Regs.Le.setMany hndH hnoneH
    have hget' : (R.setMany hParams vals').getMany hParams = some vals' :=
      Regs.getMany_setMany_self hndH (hlenH.trans hlen')
    have he := EnvOK.setMany (xs := modifiedX env [post, body])
      (henv.mono hle')
      (Regs.getMany_eq_some_iff.mp hget')
    dsimp [RH]
    rw [Regs.setMany_overwrite R hndH
      (hlenH.trans hvals.length_eq) (hlenH.trans hlen')]
    rwa [hset'] at he
  have g0B : SGrowsAt s₀.fn.blocks.size s₀ sB :=
    (SGrowsAt.of_grows (Grows.of_liftO h1)).trans
      (SGrowsAt.of_grows (Grows.of_mapM_freshVal h2))
  have g0C := g0B.trans (SGrowsAt.of_newBlock h3)
  have g0D := g0C.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h4))
  have g0E := g0D.trans (SGrowsAt.of_newBlock h5)
  have g0F := g0E.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h6))
  have g0G := g0F.trans (SGrowsAt.of_newBlock h7)
  have g0H := g0G.trans (SGrowsAt.of_sealCur h8)
  have hheader : s₀.fn.blocks.size ≤ hId := by
    rw [SGrowsAt.newBlock_id h3]
    exact g0B.size
  have g0I := g0H.trans (SGrowsAt.of_moveTo (Or.inl hheader) h9)
  have gBI : SGrowsAt 0 sB sI :=
    ((((((SGrowsAt.of_newBlock (N := 0) h3).trans
      (SGrowsAt.of_grows (Grows.of_mapM_freshVal h4))).trans
      (SGrowsAt.of_newBlock h5)).trans
      (SGrowsAt.of_grows (Grows.of_mapM_freshVal h6))).trans
      (SGrowsAt.of_newBlock h7)).trans
      (SGrowsAt.of_sealCur h8)).trans
      (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)
  have hendH : s₀.fn.nextVal + (modifiedX env [post, body]).length ≤
      sI.fn.nextVal := by
    simpa only [hsB] using gBI.nextVal
  have hfrH : RegsFresh RH sI.fn := by
    dsimp [RH]
    rw [hrangeH]
    exact hfr.setMany hendH
  have cs0G : CurSame s₀ sG :=
    ((((((CurSame.of_grows (Grows.of_liftO h1)).trans
      (CurSame.of_grows (Grows.of_mapM_freshVal h2))).trans
      (CurSame.of_newBlock h3)).trans
      (CurSame.of_grows (Grows.of_mapM_freshVal h4))).trans
      (CurSame.of_newBlock h5)).trans
      (CurSame.of_grows (Grows.of_mapM_freshVal h6))).trans
      (CurSame.of_newBlock h7)
  have hne : sG.fn.curId ≠ hId := by
    rw [cs0G.1, SGrowsAt.newBlock_id h3]
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hvalid g0B.size)
  have hpH : ProtectedAt joins sH.fn := ProtectedAt.forward hp g0H
  have hfinalH : CurFinal f sH.fn :=
    curFinal_of_move_sgrowsAt
      (by rw [(sealCur_cur h8).choose_spec.1, cs0G.1]; exact hvalid) h9
      (by simpa only [(sealCur_cur h8).choose_spec.1] using hne)
      hpH.away htail hcompl
  have hsealG : CurOK f sG.fn ⟨[], .jump ⟨hId, xvals⟩⟩ :=
    curOK_of_sealCur hfinalH h8
  have hcur0G : sG.fn.cur = s₀.fn.cur := by
    have hcurAB : sB.fn.cur = s₀.fn.cur := by rw [hsB]
    have hcurBC : sC.fn.cur = sB.fn.cur := by
      have hh := h3
      rw [M.newBlock_apply] at hh
      exact (congrArg (fun z => z.fn.cur) (M.some_pair_inj hh).2).symm
    have hcurCD : sD.fn.cur = sC.fn.cur := by
      obtain ⟨-, -, hsD⟩ := M.mapM_freshVal_length h4
      rw [hsD]
    have hcurDE : sE.fn.cur = sD.fn.cur := by
      have hh := h5
      rw [M.newBlock_apply] at hh
      exact (congrArg (fun z => z.fn.cur) (M.some_pair_inj hh).2).symm
    have hcurEF : sF.fn.cur = sE.fn.cur := by
      obtain ⟨-, -, hsF⟩ := M.mapM_freshVal_length h6
      rw [hsF]
    have hcurFG : sG.fn.cur = sF.fn.cur := by
      have hh := h7
      rw [M.newBlock_apply] at hh
      exact (congrArg (fun z => z.fn.cur) (M.some_pair_inj hh).2).symm
    exact hcurFG.trans (hcurEF.trans (hcurDE.trans
      (hcurCD.trans (hcurBC.trans hcurAB))))
  have hseal0 : CurOK f s₀.fn ⟨[], .jump ⟨hId, xvals⟩⟩ :=
    CurOK.back_of_cur_eq cs0G.1 hcur0G hsealG
  have cI : SGrowsAt 0 sC sI :=
    (((((SGrowsAt.of_grows (N := 0) (Grows.of_mapM_freshVal h4)).trans
      (SGrowsAt.of_newBlock h5)).trans
      (SGrowsAt.of_grows (Grows.of_mapM_freshVal h6))).trans
      (SGrowsAt.of_newBlock h7)).trans
      (SGrowsAt.of_sealCur h8)).trans
      (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)
  obtain ⟨hbI, hhbI, hbpI⟩ := cI.params hId
    ⟨hParams, [], .ret []⟩ (newBlock_target_get h3)
  obtain ⟨hbEnd, hhbEnd, hbpEnd⟩ :=
    htail.params hId hbI hhbI
  have hcurI : sI.fn.curId = hId := by
    rw [M.moveTo_apply] at h9
    exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h9).2).symm
  have hcurI0 : sI.fn.cur = [] := by
    rw [M.moveTo_apply] at h9
    simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h9).2
  have hlenEnd : hbEnd.params.length = vals.length := by
    rw [hbpEnd, hbpI]
    exact hlenH.trans hvals.length_eq
  have hsimH : SimS (model := model) P f s₀.fn R yst sI.fn RH yst := by
    intro res hex
    exact execFrom_jump hseal0 hget
      (jumpTo_of_completes hcompl hhbEnd hcurI hcurI0 hlenEnd (by
        simpa only [RH, hbpEnd, hbpI] using hex))
  exact ⟨RH, hbelowH, hfrH, henvH, hcleanH, hrebH, hsimH⟩

/-- The genuine loop-iteration induction clause is parametric in the register
file at the shared header.  This is the crucial difference from `SOut`: the
static `LoopLayout` is fixed, while a recursive source iteration may rebind the
header parameters to different values. -/
def LOut (P : Prog) (f : Func) (funs : YulSemantics.FunEnv yulD)
    (V : VEnv yulD) (yst : EvmState) (c : Expr Op)
    (post body : List (Stmt Op)) (V' : VEnv yulD) (yst' : EvmState)
    (o : Outcome) (doneFuncs : Array (Option Func)) : Prop :=
  ∀ (fenv : FMap) (env : VMap) (rets : Option (List Ident))
      (s₀ s₁ : BState) (renv : Option VMap) (joins : List BlockId)
      (layout : LoopLayout fenv env rets c post body s₀ s₁ renv),
    FEnvOK (model := model) P funs fenv → env.Unique → CurValid s₀ →
    ProtectedAt joins s₀.fn → Completes f s₁.fn joins → CurPlaced f s₁.fn →
    (renv = none → CurFinal f s₁.fn) →
    ∀ (done : BState) (owned : List FuncId),
      done.funcs = doneFuncs →
      (∀ i : FuncId, i ∈ owned → i < s₀.funcs.size) →
      FOwned owned s₁ done →
    ∀ (RH : Regs),
      EnvOK (model := model)
          (env.setMany (modifiedX env [post, body]) layout.hParams) V RH →
      RegsFresh RH layout.sI.fn →
      HeaderClean layout.sA.fn.nextVal layout.hParams RH →
      HeaderRebind (model := model)
        (env.setMany (modifiedX env [post, body]) layout.hParams)
        (modifiedX env [post, body]) layout.hParams V RH →
      LHOut (model := model) P f rets layout.sA.fn.nextVal layout.sI s₁ RH
        renv V' yst yst' o

/-- **The induction motive** for the construction simulation: what a source
derivation of each syntactic class means on the SSA side, against *any*
construction run that accepts the same syntax. The SSA analogue of
`SimAsm.Motive`.

Shape notes:

* the expression class carries three clauses, for the construction's three
  expression entry points — `trExpr` (one value, `EOut`), `trExprN` (the
  `let`/`assign` right-hand side, `EOutL`), and the zero-destination
  `exprStmt` path (`EStmtOut`);
* statement clauses additionally require `VMap.Unique` at entry and return it
  in normal `SOut`; declaration gates establish it and `seqCons` threads it;
* the placement hypotheses are `Completes f s₁.fn` (the finished function
  completes the state the fragment ends in — travels inwards by
  `SGrowsAt.completes_of`) and, **only when the fragment diverts**,
  `CurFinal f s₁.fn`. The conditioning on `renv = none` matters: a fragment that
  falls through leaves its current block *unsealed*, so `CurFinal` is false
  there — and unnecessary, since only a diverting statement needs its own
  sealed block to be final.
* `doneFuncs` and its `FuncTableComplete` witness are fixed across the whole
  source induction.  Intermediate scopes may still contain pending `none`
  slots; once an `allocScope`/`trFunc` inversion shows that a filled slot
  survives into `doneFuncs`, `FuncTableComplete.get` places it in `P.funcs`.

The `.loop` clause is deliberately `True` for now: the loop-iteration class
needs the header/exit/post choreography, which is the round that attacks the
`for` family. Every other clause is final. -/
def Motive (P : Prog) (f : Func) (funs : YulSemantics.FunEnv yulD)
    (V : VEnv yulD) (yst : EvmState)
    (doneFuncs : Array (Option Func))
    (_hfuncs : FuncTableComplete P doneFuncs) :
    YulSemantics.Code Op → YulSemantics.Res yulD → Prop
  | .expr e, .eres (.vals vs yst') =>
      (∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState) (i : ValId)
          (v : U256) (joins : List BlockId),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        RegsFresh R s₀.fn → ProtectedAt joins s₀.fn →
        Completes f s₁.fn joins → CurPlaced f s₁.fn → vs = [v] →
        trExpr fenv env e s₀ = some (i, s₁) →
        EOut (model := model) P f s₀ s₁ R i v yst yst')
      ∧ (∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState) (n : Nat)
          (ids : List ValId) (joins : List BlockId),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        RegsFresh R s₀.fn → ProtectedAt joins s₀.fn →
        Completes f s₁.fn joins → CurPlaced f s₁.fn →
        vs.length = n →
        trExprN fenv env n e s₀ = some (ids, s₁) →
        EOutL (model := model) P f s₀ s₁ R ids vs yst yst')
      ∧ (vs = [] → EStmtOut (model := model) P f funs V yst e V yst' .normal)
  | .expr e, .eres (.halt yst') =>
      (∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState) (i : ValId)
          (joins : List BlockId),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        RegsFresh R s₀.fn → ProtectedAt joins s₀.fn →
        Completes f s₁.fn joins → CurPlaced f s₁.fn →
        trExpr fenv env e s₀ = some (i, s₁) →
        EOutHalt (model := model) P f s₀ R yst yst')
      ∧ (∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState) (n : Nat)
          (ids : List ValId) (joins : List BlockId),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        RegsFresh R s₀.fn → ProtectedAt joins s₀.fn →
        Completes f s₁.fn joins → CurPlaced f s₁.fn →
        trExprN fenv env n e s₀ = some (ids, s₁) →
        EOutHalt (model := model) P f s₀ R yst yst')
      ∧ EStmtOut (model := model) P f funs V yst e V yst' .halt
  | .args es, .eres (.vals vs yst') =>
      ∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState)
        (ids : List ValId) (joins : List BlockId),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        RegsFresh R s₀.fn → ProtectedAt joins s₀.fn →
        Completes f s₁.fn joins → CurPlaced f s₁.fn →
        trArgs fenv env es s₀ = some (ids, s₁) →
        EOutL (model := model) P f s₀ s₁ R ids vs yst yst'
  | .args es, .eres (.halt yst') =>
      ∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState)
        (ids : List ValId) (joins : List BlockId),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        RegsFresh R s₀.fn → ProtectedAt joins s₀.fn →
        Completes f s₁.fn joins → CurPlaced f s₁.fn →
        trArgs fenv env es s₀ = some (ids, s₁) →
        EOutHalt (model := model) P f s₀ R yst yst'
  | .stmt st, .sres V' yst' o =>
      ∀ (fenv : FMap) (env : VMap) (R : Regs) (lctx : Option LoopCtx)
        (rets : Option (List Ident)) (s₀ s₁ : BState) (renv : Option VMap)
        (joins : List BlockId),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        env.Unique → RegsFresh R s₀.fn → CurValid s₀ →
        ProtectedAt joins s₀.fn → Completes f s₁.fn joins → CurPlaced f s₁.fn →
        (renv = none → CurFinal f s₁.fn) →
        ∀ (done : BState) (owned : List FuncId),
        done.funcs = doneFuncs →
        (∀ i : FuncId, i ∈ owned → i < s₀.funcs.size) →
        FOwned owned s₁ done →
        trStmt fenv env lctx rets st s₀ = some (renv, s₁) →
        SOut (model := model) P f lctx rets s₀ s₁ R renv V' yst yst' o
  | .stmts ss, .sres V' yst' o =>
      ∀ (fenv : FMap) (env : VMap) (R : Regs) (lctx : Option LoopCtx)
        (rets : Option (List Ident)) (s₀ s₁ : BState) (renv : Option VMap)
        (joins : List BlockId),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        env.Unique → RegsFresh R s₀.fn → CurValid s₀ →
        ProtectedAt joins s₀.fn → Completes f s₁.fn joins → CurPlaced f s₁.fn →
        (renv = none → CurFinal f s₁.fn) →
        ∀ (done : BState) (owned : List FuncId),
        done.funcs = doneFuncs →
        (∀ i : FuncId, i ∈ stmtFuncIds fenv ss ++ owned →
          i < s₀.funcs.size) →
        (∀ i : FuncId, i ∈ stmtFuncIds fenv ss →
          s₀.funcs[i]? = some none) →
        (stmtFuncIds fenv ss ++ owned).Nodup →
        FOwned owned s₁ done →
        trStmts fenv env lctx rets false ss s₀ = some (renv, s₁) →
        SOut (model := model) P f lctx rets s₀ s₁ R renv V' yst yst' o
  | .loop c post body, .sres V' yst' o =>
      LOut (model := model) P f funs V yst c post body V' yst' o doneFuncs
  | _, _ => True

set_option maxHeartbeats 1000000 in
/-- The shared nonzero-condition/body prefix for loop outcomes which bypass
post and the back edge. A body `break` uses the same prefix, then consumes its
edge at the protected exit block and becomes a normal loop result. -/
theorem sim_loopBodyNonNormal {P : Prog} {f : Func}
    {funs : YulSemantics.FunEnv yulD} {V Vb : VEnv yulD}
    {st st1 stb : EvmState} {c : Expr Op} {post body : List (Stmt Op)}
    {cv : U256} {o : Outcome} {doneFuncs : Array (Option Func)}
    (hfuncs : FuncTableComplete P doneFuncs)
    (ihc : Motive (model := model) P f funs V st doneFuncs hfuncs
      (.expr c) (.eres (.vals [cv] st1)))
    (hb : YulSemantics.Step yulD funs V st1 (.stmt (.block body))
      (.sres Vb stb o))
    (ihb : Motive (model := model) P f funs V st1 doneFuncs hfuncs
      (.stmt (.block body)) (.sres Vb stb o))
    (hnz : cv ≠ YulSemantics.Dialect.zero yulD)
    (ho : o = .halt ∨ o = .leave ∨ o = .break) :
    LOut (model := model) P f funs V st c post body Vb stb
      (if o = .break then .normal else o) doneFuncs := by
    intro fenv env rets s₀ s₁ renv joins layout hfe huniq hvalid hp
      hcompl hcp _hfin done owned hdone hbound hown R henv hfr hclean hreb
    have hpTail := layout.tail_fprefix
    rcases layout with
      ⟨xvals, sA, h1, hParams, sB, h2, hId, sC, h3,
       exitParams, sD, h4, exitId, sE, h5, postParams, sF, h6,
       postId, sG, h7, sH, h8, sI, h9, cvId, sJ, h10,
       bodyId, sK, h11, hX, sL, h12, sM, h13, sN, h14,
       bodyEnv, sO, h15, htr⟩
    simp only [LoopLayout.hParams, LoopLayout.sI, LoopLayout.sA] at henv hfr hclean hreb ⊢
    have g0A : Grows s₀ sA := Grows.of_liftO h1
    have gAB : Grows sA sB := Grows.of_mapM_freshVal h2
    have gCD : Grows sC sD := Grows.of_mapM_freshVal h4
    have gEF : Grows sE sF := Grows.of_mapM_freshVal h6
    have a0A : SGrowsAt s₀.fn.blocks.size s₀ sA := SGrowsAt.of_grows g0A
    have a0B := a0A.trans (SGrowsAt.of_grows gAB)
    have a0C := a0B.trans (SGrowsAt.of_newBlock h3)
    have a0D := a0C.trans (SGrowsAt.of_grows gCD)
    have a0E := a0D.trans (SGrowsAt.of_newBlock h5)
    have a0F := a0E.trans (SGrowsAt.of_grows gEF)
    have a0G := a0F.trans (SGrowsAt.of_newBlock h7)
    have a0H := a0G.trans (SGrowsAt.of_sealCur h8)
    have hheadBase : s₀.fn.blocks.size ≤ hId := by
      rw [SGrowsAt.newBlock_id h3]
      exact a0B.size
    have a0I := a0H.trans (SGrowsAt.of_moveTo (Or.inl hheadBase) h9)
    have aAI : SGrowsAt 0 sA sI :=
      (((((((SGrowsAt.of_grows (N := 0) gAB).trans
        (SGrowsAt.of_newBlock h3)).trans (SGrowsAt.of_grows gCD)).trans
        (SGrowsAt.of_newBlock h5)).trans (SGrowsAt.of_grows gEF)).trans
        (SGrowsAt.of_newBlock h7)).trans (SGrowsAt.of_sealCur h8)).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)
    have gIJ : Grows sI sJ := trExpr_grows c fenv
      (env.setMany (modifiedX env [post, body]) hParams) sI sJ cvId h10
    have aJK : SGrowsAt sJ.fn.blocks.size sJ sK := SGrowsAt.of_newBlock h11
    have gKL : Grows sK sL := Grows.of_liftO h12
    have aJL := aJK.trans (SGrowsAt.of_grows gKL)
    have aJM := aJL.trans (SGrowsAt.of_sealCur h13)
    have hbodyBase : sJ.fn.blocks.size ≤ bodyId := by
      rw [SGrowsAt.newBlock_id h11]
    have aJN := aJM.trans (SGrowsAt.of_moveTo (Or.inl hbodyBase) h14)
    have eF : SGrowsAt 0 sE sF := SGrowsAt.of_grows gEF
    have eG := eF.trans (SGrowsAt.of_newBlock h7)
    have eH := eG.trans (SGrowsAt.of_sealCur h8)
    have eI := eH.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)
    have eJ := eI.trans (SGrowsAt.of_grows gIJ)
    have eK := eJ.trans (SGrowsAt.of_newBlock h11)
    have eL := eK.trans (SGrowsAt.of_grows gKL)
    have eM := eL.trans (SGrowsAt.of_sealCur h13)
    have eN := eM.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h14)
    have hcN : Completes f sN.fn (exitId :: postId :: joins) := by
      have gb := trScope_grows fenv
        (env.setMany (modifiedX env [post, body]) hParams)
        (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
        sN bodyEnv sO h15
      cases bodyEnv with
      | none =>
        change (do
          moveTo postId
          let envP := env.setMany (modifiedX env [post, body]) postParams
          let renvP ← trScope fenv envP none rets post
          if let some envP' := renvP then
            let xvP ← edgeArgs envP' (modifiedX env [post, body])
            sealCur (.jump ⟨hId, xvP⟩)
          moveTo exitId
          pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sO =
            some (renv, s₁) at htr
        obtain ⟨uP, sP, h16, htr⟩ := M.bind_inv htr
        obtain ⟨postEnv, sQ, h17, htr⟩ := M.bind_inv htr
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sP postEnv sQ h17
        cases postEnv with
        | none =>
          change (do
            moveTo exitId
            pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sQ =
              some (renv, s₁) at htr
          obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
          obtain ⟨-, hs₁⟩ := M.pure_inv htr
          subst s₁
          have hcQ : Completes f sQ.fn (exitId :: postId :: joins) :=
            Completes.of_moveTo_protected (by simp) h18
              ((hcompl.protect postId).protect exitId)
          have hcP := SGrowsAt.completes_of gp hcQ
          have hcO := Completes.of_moveTo_protected (by simp) h16 hcP
          exact SGrowsAt.completes_of gb hcO
        | some envP =>
          obtain ⟨xvP, sR, h18, htr⟩ := M.bind_inv htr
          obtain ⟨uS, sS, h19, htr⟩ := M.bind_inv htr
          obtain ⟨uT, sT, h20, htr⟩ := M.bind_inv htr
          obtain ⟨-, hs₁⟩ := M.pure_inv htr
          subst s₁
          have hcS : Completes f sS.fn (exitId :: postId :: joins) :=
            Completes.of_moveTo_protected (by simp) h20
              ((hcompl.protect postId).protect exitId)
          have gQS : SGrows sQ sS :=
            (SGrowsAt.of_grows (Grows.of_liftO h18)).trans
              (SGrowsAt.of_sealCur h19)
          have hcQ := SGrowsAt.completes_of gQS hcS
          have hcP := SGrowsAt.completes_of gp hcQ
          have hcO := Completes.of_moveTo_protected (by simp) h16 hcP
          exact SGrowsAt.completes_of gb hcO
      | some envB =>
        obtain ⟨xvB, sP, h16, htr⟩ := M.bind_inv htr
        obtain ⟨uQ, sQ, h17, htr⟩ := M.bind_inv htr
        obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
        obtain ⟨postEnv, sS, h19, htr⟩ := M.bind_inv htr
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sR postEnv sS h19
        have gOQ : SGrows sO sQ :=
          (SGrowsAt.of_grows (Grows.of_liftO h16)).trans
            (SGrowsAt.of_sealCur h17)
        cases postEnv with
        | none =>
          change (do
            moveTo exitId
            pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sS =
              some (renv, s₁) at htr
          obtain ⟨uT, sT, h20, htr⟩ := M.bind_inv htr
          obtain ⟨-, hs₁⟩ := M.pure_inv htr
          subst s₁
          have hcS : Completes f sS.fn (exitId :: postId :: joins) :=
            Completes.of_moveTo_protected (by simp) h20
              ((hcompl.protect postId).protect exitId)
          have hcR := SGrowsAt.completes_of gp hcS
          have hcQ := Completes.of_moveTo_protected (by simp) h18 hcR
          have hcO := SGrowsAt.completes_of gOQ hcQ
          exact SGrowsAt.completes_of gb hcO
        | some envP =>
          obtain ⟨xvP, sT, h20, htr⟩ := M.bind_inv htr
          obtain ⟨uU, sU, h21, htr⟩ := M.bind_inv htr
          obtain ⟨uW, sW, h22, htr⟩ := M.bind_inv htr
          obtain ⟨-, hs₁⟩ := M.pure_inv htr
          subst s₁
          have hcU : Completes f sU.fn (exitId :: postId :: joins) :=
            Completes.of_moveTo_protected (by simp) h22
              ((hcompl.protect postId).protect exitId)
          have gSU : SGrows sS sU :=
            (SGrowsAt.of_grows (Grows.of_liftO h20)).trans
              (SGrowsAt.of_sealCur h21)
          have hcS := SGrowsAt.completes_of gSU hcU
          have hcR := SGrowsAt.completes_of gp hcS
          have hcQ := Completes.of_moveTo_protected (by simp) h18 hcR
          have hcO := SGrowsAt.completes_of gOQ hcQ
          exact SGrowsAt.completes_of gb hcO
    have hcJ : Completes f sJ.fn (exitId :: postId :: joins) :=
      SGrowsAt.completes_of aJN hcN
    have hcI : Completes f sI.fn (exitId :: postId :: joins) :=
      SGrowsAt.completes_of (SGrowsAt.of_grows gIJ) hcJ
    have hcurI : sI.fn.curId = hId := by
      rw [M.moveTo_apply] at h9
      exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h9).2).symm
    have hcurI0 : sI.fn.cur = [] := by
      rw [M.moveTo_apply] at h9
      simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h9).2
    have hheadExit : hId < exitId := by
      rw [SGrowsAt.newBlock_id h5]
      exact Nat.lt_of_lt_of_le (newBlock_target_lt h3)
        (SGrowsAt.of_grows (N := 0) gCD).size
    have hexitPost : exitId < postId := by
      rw [SGrowsAt.newBlock_id h7]
      exact Nat.lt_of_lt_of_le (newBlock_target_lt h5)
        (SGrowsAt.of_grows (N := 0) gEF).size
    have hpI0 : ProtectedAt joins sI.fn := ProtectedAt.forward hp a0I
    have hpI : ProtectedAt (exitId :: postId :: joins) sI.fn := by
      refine ⟨?_, ?_⟩
      · intro i hi
        simp only [List.mem_cons] at hi
        rcases hi with rfl | rfl | hi
        · exact Nat.lt_of_lt_of_le (newBlock_target_lt h5) eI.size
        · exact Nat.lt_of_lt_of_le (newBlock_target_lt h7)
            ((SGrowsAt.of_sealCur (N := 0) h8).trans
              (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h9)).size
        · exact hpI0.below i hi
      · simp only [List.mem_cons, not_or]
        exact ⟨by rw [hcurI]; exact Nat.ne_of_lt hheadExit,
          by rw [hcurI]; exact Nat.ne_of_lt (Nat.lt_trans hheadExit hexitPost),
          hpI0.away⟩
    have hvalidI : CurValid sI := by
      apply CurValid.of_moveTo _ h9
      exact Nat.lt_of_lt_of_le (newBlock_target_lt h3)
        (((((SGrowsAt.of_grows (N := 0) gCD).trans
          (SGrowsAt.of_newBlock h5)).trans
          (SGrowsAt.of_grows gEF)).trans
          (SGrowsAt.of_newBlock h7)).trans
          (SGrowsAt.of_sealCur h8)).size
    have hvalidJ : CurValid sJ := hvalidI.of_grows gIJ
    have csJL : CurSame sJ sL :=
      (CurSame.of_newBlock h11).trans (CurSame.of_grows gKL)
    have hcurM : sM.fn.curId = sJ.fn.curId := by
      rw [(sealCur_cur h13).choose_spec.1, csJL.1]
    have hbodyNe : sM.fn.curId ≠ bodyId := by
      rw [hcurM, SGrowsAt.newBlock_id h11]
      exact Nat.ne_of_lt hvalidJ
    have hpM : ProtectedAt (exitId :: postId :: joins) sM.fn := by
      have hgIM : SGrowsAt sI.fn.blocks.size sI sM :=
        ((SGrowsAt.of_grows (N := sI.fn.blocks.size) gIJ).trans
          (aJL.mono
            (SGrowsAt.of_grows (N := sI.fn.blocks.size) gIJ).size)).trans
          (SGrowsAt.of_sealCur h13)
      exact ProtectedAt.forward hpI hgIM
    have hfinM : CurFinal f sM.fn :=
      curFinal_of_move_grows h14 hbodyNe hpM.away (SGrows.rfl' sN) hcN
    have hbranchL : CurOK f sL.fn
        ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨exitId, hX⟩⟩ :=
      curOK_of_sealCur hfinM h13
    have hbranchJ : CurOK f sJ.fn
        ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨exitId, hX⟩⟩ :=
      CurOK.back_of_cur_eq csJL.1 (by
        have hnew : sK.fn.cur = sJ.fn.cur := by
          rw [M.newBlock_apply] at h11
          simpa using (congrArg (fun z => z.fn.cur) (M.some_pair_inj h11).2).symm
        have hedge : sL = sK := (M.edgeArgs_inv h12).2
        rw [hedge, hnew]) hbranchL
    have hcpJ : CurPlaced f sJ.fn := ⟨_, hbranchJ⟩
    have hcpI : CurPlaced f sI.fn := curPlaced_back_grows gIJ hcpJ
    obtain ⟨hlenH, hrangeH, hsB⟩ := M.mapM_freshVal_length h2
    have hndH : hParams.Nodup := by
      rw [hrangeH]
      exact M.nodup_range' _ _
    obtain ⟨RA, hleA, hbelowA, hfrA, hcv, hsimC⟩ := ihc.1 fenv
      (env.setMany (modifiedX env [post, body]) hParams) R sI sJ cvId cv
      (exitId :: postId :: joins) hfe henv hfr hpI hcJ hcpJ rfl h10
    have hnz' : cv ≠ 0 := by simpa only [yulD_zero] using hnz
    have aKN : SGrowsAt 0 sK sN :=
      ((SGrowsAt.of_grows gKL).trans (SGrowsAt.of_sealCur h13)).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h14)
    obtain ⟨bb, hbb, hbp⟩ := aKN.params bodyId ⟨[], [], .ret []⟩
      (newBlock_target_get h11)
    have hcurN : sN.fn.curId = bodyId := by
      rw [M.moveTo_apply] at h14
      exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h14).2).symm
    have hcurN0 : sN.fn.cur = [] := by
      rw [M.moveTo_apply] at h14
      simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h14).2
    have hsimB := simS_branchTrue_body (model := model) (P := P) (f := f)
      (st := st1) hcN hbranchJ hcv hnz' hbb hbp hcurN hcurN0
    have hvalidN : CurValid sN := by
      apply CurValid.of_moveTo _ h14
      exact Nat.lt_of_lt_of_le (newBlock_target_lt h11)
        ((SGrowsAt.of_grows (N := 0) gKL).trans
          (SGrowsAt.of_sealCur h13)).size
    have aIJ : SGrows sI sJ := SGrowsAt.of_grows gIJ
    have gIN : SGrows sI sN :=
      SGrowsAt.trans aIJ (aJN.mono aIJ.size)
    have hpN : ProtectedAt (exitId :: postId :: joins) sN.fn :=
      ProtectedAt.forward hpI gIN
    have gbody : SGrows sN sO := trScope_grows fenv
      (env.setMany (modifiedX env [post, body]) hParams)
      (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
      sN bodyEnv sO h15
    have hpO : ProtectedAt (exitId :: postId :: joins) sO.fn :=
      ProtectedAt.forward hpN gbody
    have htrB : trStmt fenv
        (env.setMany (modifiedX env [post, body]) hParams)
        (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets
        (.block body) sN = some (bodyEnv, sO) := by
      rw [trStmt]
      exact h15
    have hvalidO : CurValid sO := (trStmt_cur hvalidN htrB).1
    have tailBody :
        Completes f sO.fn (exitId :: postId :: joins) ∧
        CurPlaced f sO.fn ∧
        (bodyEnv = none → CurFinal f sO.fn) := by
      cases bodyEnv with
      | none =>
        change (do
          moveTo postId
          let envP := env.setMany (modifiedX env [post, body]) postParams
          let renvP ← trScope fenv envP none rets post
          if let some envP' := renvP then
            let xvP ← edgeArgs envP' (modifiedX env [post, body])
            sealCur (.jump ⟨hId, xvP⟩)
          moveTo exitId
          pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sO =
            some (renv, s₁) at htr
        obtain ⟨uP, sP, h16, htr⟩ := M.bind_inv htr
        obtain ⟨postEnv, sQ, h17, htr⟩ := M.bind_inv htr
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sP postEnv sQ h17
        have hcP : Completes f sP.fn (exitId :: postId :: joins) := by
          cases postEnv with
          | none =>
            change (do
              moveTo exitId
              pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sQ =
                some (renv, s₁) at htr
            obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
            obtain ⟨-, hs₁⟩ := M.pure_inv htr
            subst s₁
            have hcQ : Completes f sQ.fn (exitId :: postId :: joins) :=
              Completes.of_moveTo_protected (by simp) h18
                ((hcompl.protect postId).protect exitId)
            exact SGrowsAt.completes_of gp hcQ
          | some envP =>
            obtain ⟨xvP, sR, h18, htr⟩ := M.bind_inv htr
            obtain ⟨uS, sS, h19, htr⟩ := M.bind_inv htr
            obtain ⟨uT, sT, h20, htr⟩ := M.bind_inv htr
            obtain ⟨-, hs₁⟩ := M.pure_inv htr
            subst s₁
            have hcS : Completes f sS.fn (exitId :: postId :: joins) :=
              Completes.of_moveTo_protected (by simp) h20
                ((hcompl.protect postId).protect exitId)
            have gQS : SGrows sQ sS :=
              (SGrowsAt.of_grows (Grows.of_liftO h18)).trans
                (SGrowsAt.of_sealCur h19)
            exact SGrowsAt.completes_of gp
              (SGrowsAt.completes_of gQS hcS)
        have hpostNe : sO.fn.curId ≠ postId := fun he =>
          hpO.away (by simp [he])
        have hcurO0 := trScope_none_cur_nil fenv
          (env.setMany (modifiedX env [post, body]) hParams)
          (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
          sN sO h15
        have hcomplO := Completes.of_moveTo_protected (by simp) h16 hcP
        have hfinO := curFinal_of_move_grows h16 hpostNe hpO.away
          (SGrows.rfl' sP) hcP
        exact ⟨hcomplO,
          CurPlaced.of_moveTo_empty hvalidO hcurO0 hpostNe h16 hpO.away hcP,
          fun _ => hfinO⟩
      | some envB =>
        obtain ⟨xvB, sP, h16, htr⟩ := M.bind_inv htr
        obtain ⟨uQ, sQ, h17, htr⟩ := M.bind_inv htr
        obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
        obtain ⟨postEnv, sS, h19, htr⟩ := M.bind_inv htr
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sR postEnv sS h19
        have hcR : Completes f sR.fn (exitId :: postId :: joins) := by
          cases postEnv with
          | none =>
            change (do
              moveTo exitId
              pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sS =
                some (renv, s₁) at htr
            obtain ⟨uT, sT, h20, htr⟩ := M.bind_inv htr
            obtain ⟨-, hs₁⟩ := M.pure_inv htr
            subst s₁
            have hcS : Completes f sS.fn (exitId :: postId :: joins) :=
              Completes.of_moveTo_protected (by simp) h20
                ((hcompl.protect postId).protect exitId)
            exact SGrowsAt.completes_of gp hcS
          | some envP =>
            obtain ⟨xvP, sT, h20, htr⟩ := M.bind_inv htr
            obtain ⟨uU, sU, h21, htr⟩ := M.bind_inv htr
            obtain ⟨uW, sW, h22, htr⟩ := M.bind_inv htr
            obtain ⟨-, hs₁⟩ := M.pure_inv htr
            subst s₁
            have hcU : Completes f sU.fn (exitId :: postId :: joins) :=
              Completes.of_moveTo_protected (by simp) h22
                ((hcompl.protect postId).protect exitId)
            have gSU : SGrows sS sU :=
              (SGrowsAt.of_grows (Grows.of_liftO h20)).trans
                (SGrowsAt.of_sealCur h21)
            exact SGrowsAt.completes_of gp
              (SGrowsAt.completes_of gSU hcU)
        have hcQ : Completes f sQ.fn (exitId :: postId :: joins) :=
          Completes.of_moveTo_protected (by simp) h18 hcR
        have gOQ : SGrows sO sQ :=
          (SGrowsAt.of_grows (Grows.of_liftO h16)).trans
            (SGrowsAt.of_sealCur h17)
        have hpostNe : sQ.fn.curId ≠ postId := by
          have hpQ := ProtectedAt.forward hpO gOQ
          exact fun he => hpQ.away (by simp [he])
        have hfinQ := curFinal_of_move_grows h18 hpostNe
          (ProtectedAt.forward hpO gOQ).away (SGrows.rfl' sR) hcR
        have hsealP : CurOK f sP.fn ⟨[], .jump ⟨postId, xvB⟩⟩ :=
          curOK_of_sealCur hfinQ h17
        have hsP : sP = sO := (M.edgeArgs_inv h16).2
        subst sP
        exact ⟨SGrowsAt.completes_of gOQ hcQ, ⟨_, hsealP⟩,
          fun hbad => nomatch hbad⟩
    have hfrN : RegsFresh RA sN.fn := hfrA.mono aJN.nextVal
    have hboundN : ∀ i : FuncId, i ∈ owned → i < sN.funcs.size := by
      intro i hi
      exact Nat.lt_of_lt_of_le (hbound i hi)
        (Nat.le_trans a0I.funcsSize
          (Nat.le_trans (SGrows.of_grows gIJ).funcsSize aJN.funcsSize))
    have hboundO : ∀ i : FuncId, i ∈ owned → i < sO.funcs.size := by
      intro i hi
      exact Nat.lt_of_lt_of_le (hboundN i hi) gbody.funcsSize
    have hownO : FOwned owned sO done :=
      FOwned.back_fprefix hpTail hboundO hown
    have hbodySim := ihb fenv
      (env.setMany (modifiedX env [post, body]) hParams) RA
      (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets
      sN sO bodyEnv (exitId :: postId :: joins) hfe
      (henv.mono hleA) (huniq.setMany _ _) hfrN hvalidN hpN
      tailBody.1 tailBody.2.1 tailBody.2.2 done owned hdone hboundN hownO htrB
    have hpre := hsimC.trans hsimB
    rcases ho with rfl | rfl | rfl
    · rw [if_neg (by decide)]
      exact hpre (.halt stb) hbodySim
    · rw [if_neg (by decide)]
      obtain ⟨rs, vals, hrs, hvals, hex⟩ := hbodySim
      exact ⟨rs, vals, hrs, hvals, hpre (.ret vals stb) hex⟩
    · rw [if_pos rfl]
      obtain ⟨lc, RB, vals, hlc, hleB, hbelowB, hfrB, hvals, hcont⟩ :=
        hbodySim
      have hlc' : lc = ⟨exitId, postId, modifiedX env [post, body]⟩ :=
        Option.some.inj hlc.symm
      subst lc
      have tailData :
          SGrowsAt 0 sE s₁ ∧ sO.fn.nextVal ≤ s₁.fn.nextVal
            ∧ s₁.fn.curId = exitId ∧ s₁.fn.cur = []
            ∧ renv = some
              (env.setMany (modifiedX env [post, body]) exitParams) := by
        have gb := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) hParams)
          (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
          sN bodyEnv sO h15
        cases bodyEnv with
        | none =>
          change (do
            moveTo postId
            let envP := env.setMany (modifiedX env [post, body]) postParams
            let renvP ← trScope fenv envP none rets post
            if let some envP' := renvP then
              let xvP ← edgeArgs envP' (modifiedX env [post, body])
              sealCur (.jump ⟨hId, xvP⟩)
            moveTo exitId
            pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sO =
              some (renv, s₁) at htr
          obtain ⟨uP, sP, h16, htr⟩ := M.bind_inv htr
          obtain ⟨postEnv, sQ, h17, htr⟩ := M.bind_inv htr
          have gp := trScope_grows fenv
            (env.setMany (modifiedX env [post, body]) postParams) none rets post
            sP postEnv sQ h17
          cases postEnv with
          | none =>
            change (do
              moveTo exitId
              pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sQ =
                some (renv, s₁) at htr
            obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
            obtain ⟨hrenv, hs₁⟩ := M.pure_inv htr
            subst s₁
            have go1 := (SGrowsAt.of_moveTo (N := 0)
              (Or.inl (Nat.zero_le _)) h16).trans (gp.mono (Nat.zero_le _))
            have go := go1.trans (SGrowsAt.of_moveTo
              (Or.inl (Nat.zero_le _)) h18)
            exact ⟨eN.trans ((gb.mono (Nat.zero_le _)).trans go), go.nextVal,
              by rw [M.moveTo_apply] at h18
                 exact (congrArg (fun z => z.fn.curId)
                   (M.some_pair_inj h18).2).symm,
              by rw [M.moveTo_apply] at h18
                 simpa using congrArg (fun z => z.fn.cur)
                   (M.some_pair_inj h18).2,
              hrenv⟩
          | some envP =>
            obtain ⟨xvP, sR, h18, htr⟩ := M.bind_inv htr
            obtain ⟨uS, sS, h19, htr⟩ := M.bind_inv htr
            obtain ⟨uT, sT, h20, htr⟩ := M.bind_inv htr
            obtain ⟨hrenv, hs₁⟩ := M.pure_inv htr
            subst s₁
            have gQS : SGrows sQ sS :=
              (SGrowsAt.of_grows (Grows.of_liftO h18)).trans
                (SGrowsAt.of_sealCur h19)
            have go1 := (SGrowsAt.of_moveTo (N := 0)
              (Or.inl (Nat.zero_le _)) h16).trans (gp.mono (Nat.zero_le _))
            have go2 := go1.trans (gQS.mono (Nat.zero_le _))
            have go := go2.trans (SGrowsAt.of_moveTo
              (Or.inl (Nat.zero_le _)) h20)
            exact ⟨eN.trans ((gb.mono (Nat.zero_le _)).trans go), go.nextVal,
              by rw [M.moveTo_apply] at h20
                 exact (congrArg (fun z => z.fn.curId)
                   (M.some_pair_inj h20).2).symm,
              by rw [M.moveTo_apply] at h20
                 simpa using congrArg (fun z => z.fn.cur)
                   (M.some_pair_inj h20).2,
              hrenv⟩
        | some envB =>
          obtain ⟨xvB, sP, h16, htr⟩ := M.bind_inv htr
          obtain ⟨uQ, sQ, h17, htr⟩ := M.bind_inv htr
          obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
          obtain ⟨postEnv, sS, h19, htr⟩ := M.bind_inv htr
          have gOQ : SGrows sO sQ :=
            (SGrowsAt.of_grows (Grows.of_liftO h16)).trans
              (SGrowsAt.of_sealCur h17)
          have gp := trScope_grows fenv
            (env.setMany (modifiedX env [post, body]) postParams) none rets post
            sR postEnv sS h19
          cases postEnv with
          | none =>
            change (do
              moveTo exitId
              pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sS =
                some (renv, s₁) at htr
            obtain ⟨uT, sT, h20, htr⟩ := M.bind_inv htr
            obtain ⟨hrenv, hs₁⟩ := M.pure_inv htr
            subst s₁
            have go1 := (gOQ.mono (Nat.zero_le _)).trans
              (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h18)
            have go2 := go1.trans (gp.mono (Nat.zero_le _))
            have go := go2.trans (SGrowsAt.of_moveTo
              (Or.inl (Nat.zero_le _)) h20)
            exact ⟨eN.trans ((gb.mono (Nat.zero_le _)).trans go), go.nextVal,
              by rw [M.moveTo_apply] at h20
                 exact (congrArg (fun z => z.fn.curId)
                   (M.some_pair_inj h20).2).symm,
              by rw [M.moveTo_apply] at h20
                 simpa using congrArg (fun z => z.fn.cur)
                   (M.some_pair_inj h20).2,
              hrenv⟩
          | some envP =>
            obtain ⟨xvP, sT, h20, htr⟩ := M.bind_inv htr
            obtain ⟨uU, sU, h21, htr⟩ := M.bind_inv htr
            obtain ⟨uW, sW, h22, htr⟩ := M.bind_inv htr
            obtain ⟨hrenv, hs₁⟩ := M.pure_inv htr
            subst s₁
            have gSU : SGrows sS sU :=
              (SGrowsAt.of_grows (Grows.of_liftO h20)).trans
                (SGrowsAt.of_sealCur h21)
            have go1 := (gOQ.mono (Nat.zero_le _)).trans
              (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h18)
            have go2 := go1.trans (gp.mono (Nat.zero_le _))
            have go3 := go2.trans (gSU.mono (Nat.zero_le _))
            have go := go3.trans (SGrowsAt.of_moveTo
              (Or.inl (Nat.zero_le _)) h22)
            exact ⟨eN.trans ((gb.mono (Nat.zero_le _)).trans go), go.nextVal,
              by rw [M.moveTo_apply] at h22
                 exact (congrArg (fun z => z.fn.curId)
                   (M.some_pair_inj h22).2).symm,
              by rw [M.moveTo_apply] at h22
                 simpa using congrArg (fun z => z.fn.cur)
                   (M.some_pair_inj h22).2,
              hrenv⟩
      obtain ⟨ge, hnextO1, hcurExit, hcurExit0, hrenv⟩ := tailData
      obtain ⟨hlenE, hrangeE, hsD⟩ := M.mapM_freshVal_length h4
      have hndE : exitParams.Nodup := by
        rw [hrangeE]
        exact M.nodup_range' _ _
      have dI : SGrowsAt 0 sD sI :=
        (((((SGrowsAt.of_newBlock (N := 0) h5).trans
          (SGrowsAt.of_grows gEF)).trans (SGrowsAt.of_newBlock h7)).trans
          (SGrowsAt.of_sealCur h8)).trans
          (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9))
      have dN : SGrowsAt 0 sD sN := dI.trans
        (((SGrowsAt.of_grows (N := 0) gIJ).trans (aJL.mono (Nat.zero_le _))).trans
          (SGrowsAt.of_sealCur h13) |>.trans
            (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h14))
      have hparamsLtN : ∀ i ∈ exitParams, i < sN.fn.nextVal := by
        intro i hi
        rw [hrangeE] at hi
        exact Nat.lt_of_lt_of_le (by simpa [hsD] using (M.mem_range'_bounds hi).2)
          dN.nextVal
      have hnoneE : ∀ i ∈ exitParams, RB i = none := by
        intro i hi
        rw [hbelowB i (hparamsLtN i hi)]
        have hiRange := hi
        rw [hrangeE] at hiRange
        have hiLtI : i < sI.fn.nextVal := Nat.lt_of_lt_of_le
          (by simpa [hsD] using (M.mem_range'_bounds hiRange).2) dI.nextVal
        rw [hbelowA i hiLtI]
        apply hclean i
        · exact Nat.le_trans
            ((SGrowsAt.of_grows (N := 0) gAB).trans
              (SGrowsAt.of_newBlock h3)).nextVal
            (M.mem_range'_bounds hiRange).1
        · intro hiH
          rw [hrangeH] at hiH
          have hu := (M.mem_range'_bounds hiH).2
          have hl := (M.mem_range'_bounds hiRange).1
          have hnextCB : sC.fn.nextVal = sB.fn.nextVal := by
            rw [M.newBlock_apply] at h3
            exact (congrArg (fun z => z.fn.nextVal)
              (M.some_pair_inj h3).2).symm
          have hend : sA.fn.nextVal + (modifiedX env [post, body]).length =
              sC.fn.nextVal := by rw [hnextCB, hsB]
          have hu' : i < sC.fn.nextVal := by rwa [hend] at hu
          exact Nat.not_lt_of_ge hl hu'
      let RE := RB.setMany exitParams vals
      have hleE : Regs.Le RB RE := Regs.Le.setMany hndE hnoneE
      have hbelowE : Regs.BelowEq sA.fn.nextVal RB RE := by
        apply Regs.BelowEq.setMany
        intro i hi
        rw [hrangeE] at hi
        exact Nat.le_trans
          ((SGrowsAt.of_grows (N := 0) gAB).trans
            (SGrowsAt.of_newBlock h3)).nextVal
          (M.mem_range'_bounds hi).1
      have hfrE : RegsFresh RE s₁.fn := by
        intro i hi
        dsimp [RE]
        rw [Regs.setMany_other]
        · exact hfrB i (Nat.le_trans hnextO1 hi)
        · intro him
          exact absurd (hparamsLtN i him)
            (Nat.not_lt_of_ge (Nat.le_trans
              ((trScope_grows fenv
                (env.setMany (modifiedX env [post, body]) hParams)
                (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
                sN bodyEnv sO h15).nextVal) (Nat.le_trans hnextO1 hi)))
      obtain ⟨eb, heb, hep⟩ := ge.params exitId ⟨exitParams, [], .ret []⟩
        (newBlock_target_get h5)
      have hlenEB : eb.params.length = vals.length := by
        rw [hep, hlenE]
        exact hvals.length_eq
      have hsimExit : SimS (model := model) P f sI.fn R st s₁.fn RE stb := by
        intro res hex
        apply hpre res
        apply hcont res
        apply jumpTo_of_completes hcompl heb
          hcurExit hcurExit0 hlenEB
        simpa only [RE, hep] using hex
      have hnames : VEnv.names Vb = VEnv.names V := by
        have hm := (mod_sim hb).1
        simpa [declsOfStmt] using hm
      have hmod : ModOut [] (modStmts [] body) V Vb := by
        have hm := (mod_sim hb).2 [] (localsOK_nil V)
        simpa [modStmt] using hm
      have hVexit : YulSemantics.VEnv.setMany V
          (modifiedX env [post, body]) vals = Vb :=
        setMany_eq_of_modOut (xs := modifiedX env [post, body]) henv
          (huniq.setMany _ _) hnames hmod hvals
          (fun x hx => by
            rw [VMap.names_setMany]
            exact modifiedX_mem_names hx)
          (fun x hx hm => mem_modifiedX (by
            rw [VMap.names_setMany] at hx
            exact hx) (by
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
            exact List.mem_append_right _ hm))
      have hpgetE : RE.getMany exitParams = some vals :=
        Regs.getMany_setMany_self hndE (by rw [hlenE]; exact hvals.length_eq)
      have henvE : EnvOK (model := model)
          (env.setMany (modifiedX env [post, body]) exitParams) Vb RE := by
        have he : EnvOK (model := model)
            ((env.setMany (modifiedX env [post, body]) hParams).setMany
              (modifiedX env [post, body]) exitParams)
            (YulSemantics.VEnv.setMany V (modifiedX env [post, body]) vals) RE :=
          EnvOK.setMany
            (henv.mono (hleA.trans (hleB.trans hleE)))
            (Regs.getMany_eq_some_iff.mp hpgetE)
        rw [VMap.setMany_overwrite env (modifiedX_nodup huniq _)
          hlenH.symm hlenE.symm] at he
        rwa [hVexit] at he
      have hbelowFinal : Regs.BelowEq sA.fn.nextVal R RE :=
        (hbelowA.mono aAI.nextVal).trans
          ((hbelowB.mono (Nat.le_trans aAI.nextVal
            (Nat.le_trans (SGrowsAt.of_grows (N := 0) gIJ).nextVal
              aJN.nextVal))).trans hbelowE)
      exact ⟨env.setMany (modifiedX env [post, body]) exitParams, RE, hrenv,
        hbelowFinal,
        hfrE, henvE, huniq.setMany _ _, hsimExit⟩

/-- Bind the values carried by a body fall-through/`continue` edge to the
reserved post block's parameters.  This is the common post-entry boundary of
`loopStep` and `loopPostHalt`: it extends the register file at the fresh post
parameters, reconstructs the fixed post environment, and turns the body's
edge continuation into a straight-line simulation ending at the post block. -/
theorem sim_loopPostEntry {P : Prog} {f : Func} {X : List Ident}
    {V Vb : VEnv yulD} {env : VMap} {R₀ RB : Regs}
    {st stb : EvmState} {fn₀ : FnState} {sBody sPost : BState}
    {postId : BlockId} {postParams : List ValId} {vals : List U256}
    {pb : Block} {joins : List BlockId} {base : Nat}
    (henv : EnvOK (model := model) env V R₀)
    (hV : YulSemantics.VEnv.setMany V X vals = Vb)
    (hle : Regs.Le R₀ RB) (hbelow : Regs.BelowEq base R₀ RB)
    (hnd : postParams.Nodup) (hnone : ∀ i ∈ postParams, RB i = none)
    (hbase : ∀ i ∈ postParams, base ≤ i)
    (hparamsLt : ∀ i ∈ postParams, i < sBody.fn.nextVal)
    (hfr : RegsFresh RB sBody.fn)
    (hnext : sBody.fn.nextVal ≤ sPost.fn.nextVal)
    (hcompl : Completes f sPost.fn joins)
    (hpb : sPost.fn.blocks[postId]? = some pb)
    (hpp : pb.params = postParams)
    (hcur : sPost.fn.curId = postId) (hcur0 : sPost.fn.cur = [])
    (hlen : postParams.length = vals.length)
    (hcont : ∀ res, JumpTo (model := model) P f postId vals RB stb res →
      ExecFrom (model := model) P f fn₀ R₀ st res) :
    ∃ RP : Regs, Regs.Le R₀ RP ∧ Regs.BelowEq base R₀ RP
      ∧ RegsFresh RP sPost.fn
      ∧ EnvOK (model := model) (env.setMany X postParams) Vb RP
      ∧ SimS (model := model) P f fn₀ R₀ st sPost.fn RP stb := by
  let RP := RB.setMany postParams vals
  have hleP : Regs.Le RB RP := Regs.Le.setMany hnd hnone
  have hbelowP : Regs.BelowEq base RB RP :=
    Regs.BelowEq.setMany hbase
  have hfrP : RegsFresh RP sPost.fn := by
    intro i hi
    dsimp [RP]
    rw [Regs.setMany_other]
    · exact hfr i (Nat.le_trans hnext hi)
    · intro him
      exact absurd (hparamsLt i him)
        (Nat.not_lt_of_ge (Nat.le_trans hnext hi))
  have hpget : RP.getMany postParams = some vals :=
    Regs.getMany_setMany_self hnd hlen
  have henvP : EnvOK (model := model) (env.setMany X postParams) Vb RP := by
    have he : EnvOK (model := model) (env.setMany X postParams)
        (YulSemantics.VEnv.setMany V X vals) RP :=
      EnvOK.setMany (henv.mono (hle.trans hleP))
        (Regs.getMany_eq_some_iff.mp hpget)
    rwa [hV] at he
  have hsimP : SimS (model := model) P f fn₀ R₀ st sPost.fn RP stb := by
    intro res hex
    apply hcont res
    apply jumpTo_of_completes hcompl hpb hcur hcur0
    · rw [hpp]
      exact hlen
    · simpa only [RP, hpp] using hex
  exact ⟨RP, hle.trans hleP, hbelow.trans hbelowP, hfrP, henvP, hsimP⟩

/-- Backward reconstruction at the output of the loop post fragment.  The
overall loop builder always leaves the post block by moving to the protected
exit block.  If the post diverts, that move directly makes its sealed current
block final; if it falls through, the generated back edge seals it first. -/
theorem loopPost_back {f : Func} {fenv : FMap} {env : VMap}
    {rets : Option (List Ident)} {post : List (Stmt Op)} {X : List Ident}
    {hId exitId : BlockId} {sP sQ s₁ : BState}
    {postEnv : Option VMap} {renv : Option VMap} {outEnv : VMap}
    {joins : List BlockId}
    (hvalidQ : CurValid sQ)
    (hpQ : ProtectedAt (exitId :: joins) sQ.fn)
    (hpost : trScope fenv env none rets post sP = some (postEnv, sQ))
    (htail : (do
      if let some envP := postEnv then
        let xvP ← edgeArgs envP X
        sealCur (.jump ⟨hId, xvP⟩)
      moveTo exitId
      pure (some outEnv)) sQ = some (renv, s₁))
    (hcompl : Completes f s₁.fn joins) :
    Completes f sQ.fn (exitId :: joins) ∧
      CurPlaced f sQ.fn ∧ (postEnv = none → CurFinal f sQ.fn) := by
  cases postEnv with
  | none =>
    change (do
      moveTo exitId
      pure (some outEnv)) sQ = some (renv, s₁) at htail
    obtain ⟨uR, sR, hmove, htail⟩ := M.bind_inv htail
    obtain ⟨-, hs₁⟩ := M.pure_inv htail
    subst s₁
    have hcR : Completes f sR.fn (exitId :: joins) := hcompl.protect exitId
    have hcQ : Completes f sQ.fn (exitId :: joins) :=
      Completes.of_moveTo_protected (by simp) hmove hcR
    have hne : sQ.fn.curId ≠ exitId := fun he => hpQ.away (by simp [he])
    have hcur0 : sQ.fn.cur = [] :=
      trScope_none_cur_nil fenv env none rets post sP sQ hpost
    have hfin : CurFinal f sQ.fn :=
      curFinal_of_move_grows hmove hne hpQ.away (SGrows.rfl' sR) hcR
    exact ⟨hcQ,
      CurPlaced.of_moveTo_empty hvalidQ hcur0 hne hmove hpQ.away hcR,
      fun _ => hfin⟩
  | some envP =>
    obtain ⟨xvP, sR, hargs, htail⟩ := M.bind_inv htail
    obtain ⟨uS, sS, hseal, htail⟩ := M.bind_inv htail
    obtain ⟨uT, sT, hmove, htail⟩ := M.bind_inv htail
    obtain ⟨-, hs₁⟩ := M.pure_inv htail
    subst s₁
    have gQS : SGrows sQ sS :=
      (SGrowsAt.of_grows (Grows.of_liftO hargs)).trans
        (SGrowsAt.of_sealCur hseal)
    have hpS : ProtectedAt (exitId :: joins) sS.fn :=
      ProtectedAt.forward hpQ gQS
    have hcT : Completes f sT.fn (exitId :: joins) := hcompl.protect exitId
    have hcS : Completes f sS.fn (exitId :: joins) :=
      Completes.of_moveTo_protected (by simp) hmove hcT
    have hne : sS.fn.curId ≠ exitId := fun he => hpS.away (by simp [he])
    have hfinS : CurFinal f sS.fn :=
      curFinal_of_move_grows hmove hne hpS.away (SGrows.rfl' sT) hcT
    have hplacedR : CurPlaced f sR.fn :=
      ⟨_, curOK_of_sealCur hfinS hseal⟩
    have hsR : sR = sQ := (M.edgeArgs_inv hargs).2
    subst sR
    exact ⟨SGrowsAt.completes_of gQS hcS, hplacedR, fun h => nomatch h⟩

/-- The matching backward reconstruction at the body boundary.  A diverting
body leaves a sealed block before the protected move to `postId`; a normal
body receives the generated fall-through jump first. -/
theorem loopBody_back {f : Func} {fenv : FMap} {env : VMap}
    {lctx : LoopCtx} {rets : Option (List Ident)} {body : List (Stmt Op)}
    {X : List Ident} {postId : BlockId} {sN sO sP : BState}
    {bodyEnv : Option VMap} {joins : List BlockId}
    (hvalidO : CurValid sO) (hpO : ProtectedAt joins sO.fn)
    (hpostMem : postId ∈ joins)
    (hbody : trScope fenv env (some lctx) rets body sN = some (bodyEnv, sO))
    (htail : (do
      if let some envB := bodyEnv then
        let xvB ← edgeArgs envB X
        sealCur (.jump ⟨postId, xvB⟩)
      moveTo postId) sO = some ((), sP))
    (hcomplP : Completes f sP.fn joins) :
    Completes f sO.fn joins ∧ CurPlaced f sO.fn ∧
      (bodyEnv = none → CurFinal f sO.fn) := by
  cases bodyEnv with
  | none =>
    change moveTo postId sO = some ((), sP) at htail
    have hne : sO.fn.curId ≠ postId := fun he => hpO.away (he ▸ hpostMem)
    have hcur0 : sO.fn.cur = [] :=
      trScope_none_cur_nil fenv env (some lctx) rets body sN sO hbody
    have hfin : CurFinal f sO.fn :=
      curFinal_of_move_grows htail hne hpO.away (SGrows.rfl' sP) hcomplP
    exact ⟨Completes.of_moveTo_protected hpostMem htail hcomplP,
      CurPlaced.of_moveTo_empty hvalidO hcur0 hne htail hpO.away hcomplP,
      fun _ => hfin⟩
  | some envB =>
    obtain ⟨xvB, sQ, hargs, htail⟩ := M.bind_inv htail
    obtain ⟨uR, sR, hseal, hmove⟩ := M.bind_inv htail
    have gOR : SGrows sO sR :=
      (SGrowsAt.of_grows (Grows.of_liftO hargs)).trans
        (SGrowsAt.of_sealCur hseal)
    have hpR : ProtectedAt joins sR.fn := ProtectedAt.forward hpO gOR
    have hcR : Completes f sR.fn joins :=
      Completes.of_moveTo_protected hpostMem hmove hcomplP
    have hne : sR.fn.curId ≠ postId := fun he => hpR.away (he ▸ hpostMem)
    have hfinR : CurFinal f sR.fn :=
      curFinal_of_move_grows hmove hne hpR.away (SGrows.rfl' sP) hcomplP
    have hplacedQ : CurPlaced f sQ.fn := ⟨_, curOK_of_sealCur hfinR hseal⟩
    have hsQ : sQ = sO := (M.edgeArgs_inv hargs).2
    subst sQ
    exact ⟨SGrowsAt.completes_of gOR hcR, hplacedQ, fun h => nomatch h⟩



/-! ### The switch dispatch chain

`trCases` lays down one `const; eq; branch` test per case, each guarding a
block that runs the case body and jumps to the reserved join.  `CasesOut`
is what a whole chain achieves against a source derivation of the *selected*
block, and `trCases_sim` is the induction over the case list that establishes
it. -/

/-- What the switch dispatch chain achieves, by source outcome. -/
def CasesOut (P : Prog) (f : Func) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (X : List Ident) (joinId : BlockId)
    (s₀ s₁ : BState) (R₀ : Regs) (V' : VEnv yulD) (yst yst' : EvmState)
    (o : Outcome) : Prop :=
  match o with
  | .normal => ∃ (R₁ : Regs) (vals : List U256),
      Regs.Le R₀ R₁ ∧ Regs.BelowEq s₀.fn.nextVal R₀ R₁ ∧ RegsFresh R₁ s₁.fn
        ∧ List.Forall₂ (fun x v => YulSemantics.VEnv.get V' x = some v) X vals
        ∧ ∀ res, JumpTo (model := model) P f joinId vals R₁ yst' res
            → ExecFrom (model := model) P f s₀.fn R₀ yst res
  | o => SOut (model := model) P f lctx rets s₀ s₁ R₀ none V' yst yst' o

theorem CasesOut.prefix {P : Prog} {f : Func} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {X : List Ident} {joinId : BlockId}
    {s₀ sA s₁ : BState} {R₀ RA : Regs} {V' : VEnv yulD}
    {yst ystA yst' : EvmState} {o : Outcome}
    (hle : Regs.Le R₀ RA)
    (hbelow : Regs.BelowEq s₀.fn.nextVal R₀ RA)
    (hgrow : s₀.fn.nextVal ≤ sA.fn.nextVal)
    (hsim : SimS (model := model) P f s₀.fn R₀ yst sA.fn RA ystA)
    (h : CasesOut (model := model) P f lctx rets X joinId sA s₁ RA V' ystA yst' o) :
    CasesOut (model := model) P f lctx rets X joinId s₀ s₁ R₀ V' yst yst' o := by
  cases o with
  | normal =>
    obtain ⟨R₁, vals, hle1, hbelow1, hfr, hvals, hcont⟩ := h
    exact ⟨R₁, vals, hle.trans hle1, hbelow.trans (hbelow1.mono hgrow), hfr, hvals,
      fun res hj => hsim res (hcont res hj)⟩
  | halt =>
    have h' : SOut (model := model) P f lctx rets sA s₁ RA none V' ystA yst' .halt := h
    show SOut (model := model) P f lctx rets s₀ s₁ R₀ none V' yst yst' .halt
    exact SOut.prefix hle hbelow hgrow hsim h'
  | «break» =>
    have h' : SOut (model := model) P f lctx rets sA s₁ RA none V' ystA yst' .break := h
    show SOut (model := model) P f lctx rets s₀ s₁ R₀ none V' yst yst' .break
    exact SOut.prefix hle hbelow hgrow hsim h'
  | «continue» =>
    have h' : SOut (model := model) P f lctx rets sA s₁ RA none V' ystA yst' .continue := h
    show SOut (model := model) P f lctx rets s₀ s₁ R₀ none V' yst yst' .continue
    exact SOut.prefix hle hbelow hgrow hsim h'
  | leave =>
    have h' : SOut (model := model) P f lctx rets sA s₁ RA none V' ystA yst' .leave := h
    show SOut (model := model) P f lctx rets s₀ s₁ R₀ none V' yst yst' .leave
    exact SOut.prefix hle hbelow hgrow hsim h'

omit model in
/-- A sealed, in-bounds current block that the finished function keeps is
placed. -/
theorem curPlaced_of_curFinal {f : Func} {fn : FnState}
    (hv : fn.curId < fn.blocks.size) (hcur : fn.cur = [])
    (hfin : CurFinal f fn) : CurPlaced f fn := by
  refine ⟨⟨(fn.blocks[fn.curId]).instrs, (fn.blocks[fn.curId]).term⟩,
    fn.blocks[fn.curId], hfin _ (Array.getElem?_eq_getElem hv), ?_, rfl⟩
  rw [hcur]
  simp

theorem CasesOut.ofNonNormal {P : Prog} {f : Func} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {X : List Ident} {joinId : BlockId}
    {s₀ sA s₁ : BState} {R : Regs} {renv : Option VMap} {V' : VEnv yulD}
    {yst yst' : EvmState} {o : Outcome}
    (ho : o ≠ .normal) (hgrow : sA.fn.nextVal ≤ s₁.fn.nextVal)
    (h : SOut (model := model) P f lctx rets s₀ sA R renv V' yst yst' o) :
    CasesOut (model := model) P f lctx rets X joinId s₀ s₁ R V' yst yst' o := by
  cases o with
  | normal => exact absurd rfl ho
  | halt =>
    show SOut (model := model) P f lctx rets s₀ s₁ R none V' yst yst' .halt
    exact SOut.of_nonNormal (by simp) hgrow h
  | «break» =>
    show SOut (model := model) P f lctx rets s₀ s₁ R none V' yst yst' .break
    exact SOut.of_nonNormal (by simp) hgrow h
  | «continue» =>
    show SOut (model := model) P f lctx rets s₀ s₁ R none V' yst yst' .continue
    exact SOut.of_nonNormal (by simp) hgrow h
  | leave =>
    show SOut (model := model) P f lctx rets s₀ s₁ R none V' yst yst' .leave
    exact SOut.of_nonNormal (by simp) hgrow h

omit model in
theorem newBlock_fn {ps : List ValId} {s s' : BState} {bid : BlockId}
    (h : newBlock ps s = some (bid, s')) :
    bid = s.fn.blocks.size ∧ s'.fn.nextVal = s.fn.nextVal ∧ s'.fn.cur = s.fn.cur
      ∧ s'.fn.curId = s.fn.curId := by
  rw [M.newBlock_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact ⟨rfl, rfl, rfl, rfl⟩

omit model in
theorem moveTo_fn {bid : BlockId} {s s' : BState} {u : Unit}
    (h : moveTo bid s = some (u, s')) :
    s'.fn.nextVal = s.fn.nextVal ∧ s'.fn.cur = [] ∧ s'.fn.curId = bid
      ∧ s'.fn.blocks = s.fn.blocks := by
  rw [M.moveTo_apply] at h
  obtain ⟨-, rfl⟩ := M.some_pair_inj h
  exact ⟨rfl, rfl, rfl, rfl⟩

omit model in
theorem freshVal_fn {s s' : BState} {v : ValId} (h : freshVal s = some (v, s')) :
    v = s.fn.nextVal ∧ s'.fn.nextVal = s.fn.nextVal + 1 ∧ s'.fn.cur = s.fn.cur
      ∧ s'.fn.curId = s.fn.curId ∧ s'.fn.blocks = s.fn.blocks := by
  rw [M.freshVal_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

omit model in
theorem emit_fn {i : Instr} {s s' : BState} {u : Unit} (h : emit i s = some (u, s')) :
    s'.fn.nextVal = s.fn.nextVal ∧ s'.fn.cur = i :: s.fn.cur
      ∧ s'.fn.curId = s.fn.curId ∧ s'.fn.blocks = s.fn.blocks := by
  rw [M.emit_apply] at h
  obtain ⟨-, rfl⟩ := M.some_pair_inj h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- One `case` test of the switch dispatch chain: materialise the literal,
compare it with the scrutinee, and land on the `eq` result register. -/
theorem trCases_test_step {P : Prog} {f : Func} {R : Regs} {st : EvmState}
    {sv t e : ValId} {cv w : U256} {s₀ s1 s2 s3 s4 : BState} {u2 u4 : Unit}
    (hfr : RegsFresh R s₀.fn) (hsv : R sv = some cv)
    (h1 : freshVal s₀ = some (t, s1))
    (h2 : emit (Instr.const t w) s1 = some (u2, s2))
    (h3 : freshVal s2 = some (e, s3))
    (h4 : emit (Instr.op [e] .eq [sv, t]) s3 = some (u4, s4)) :
    ∃ R' : Regs, Regs.Le R R' ∧ Regs.BelowEq s₀.fn.nextVal R R'
      ∧ RegsFresh R' s4.fn
      ∧ R' e = some (YulSemantics.EVM.b2w (decide (cv = w)))
      ∧ SimS (model := model) P f s₀.fn R st s4.fn R' st := by
  obtain ⟨htv, hnv1, hcur1, hid1, hbl1⟩ := freshVal_fn h1
  obtain ⟨hnv2, hcur2, hid2, hbl2⟩ := emit_fn h2
  obtain ⟨hev, hnv3, hcur3, hid3, hbl3⟩ := freshVal_fn h3
  obtain ⟨hnv4, hcur4, hid4, hbl4⟩ := emit_fn h4
  subst htv
  -- the literal register
  have hfr1 : RegsFresh (R.set s₀.fn.nextVal w) s2.fn := by
    refine hfr.set w ?_
    rw [hnv2, hnv1]
  have hle1 : Regs.Le R (R.set s₀.fn.nextVal w) :=
    Regs.Le.set _ hfr.unbound
  have hbelow1 : Regs.BelowEq s₀.fn.nextVal R (R.set s₀.fn.nextVal w) :=
    Regs.BelowEq.set _ (Nat.le_refl _)
  have hstep1 : SimS (model := model) P f s₀.fn R st s2.fn
      (R.set s₀.fn.nextVal w) st :=
    simS_const (hid2.trans hid1) (by rw [hcur2, hcur1])
  -- the comparison register
  subst hev
  have hfr2 : RegsFresh ((R.set s₀.fn.nextVal w).set s2.fn.nextVal
      (YulSemantics.EVM.b2w (decide (cv = w)))) s4.fn := by
    refine hfr1.set _ ?_
    rw [hnv4, hnv3]
  have hle2 : Regs.Le (R.set s₀.fn.nextVal w)
      ((R.set s₀.fn.nextVal w).set s2.fn.nextVal
        (YulSemantics.EVM.b2w (decide (cv = w)))) :=
    Regs.Le.set _ hfr1.unbound
  have hbelow2 : Regs.BelowEq s₀.fn.nextVal (R.set s₀.fn.nextVal w)
      ((R.set s₀.fn.nextVal w).set s2.fn.nextVal
        (YulSemantics.EVM.b2w (decide (cv = w)))) := by
    refine Regs.BelowEq.set _ ?_
    rw [hnv2, hnv1]
    omega
  have hargs : (R.set s₀.fn.nextVal w).getMany [sv, s₀.fn.nextVal]
      = some [cv, w] := by
    rw [Regs.getMany_cons, Regs.getMany_cons]
    have hsv' : (R.set s₀.fn.nextVal w) sv = some cv := hle1 sv cv hsv
    rw [hsv', Regs.set_same]
    rfl
  have hstep2 : SimS (model := model) P f s2.fn (R.set s₀.fn.nextVal w) st s4.fn
      ((R.set s₀.fn.nextVal w).setMany [s2.fn.nextVal]
        [YulSemantics.EVM.b2w (decide (cv = w))]) st :=
    simS_op hargs (builtin_eq cv w st) rfl (hid4.trans hid3) (by rw [hcur4, hcur3])
  have hsm : (R.set s₀.fn.nextVal w).setMany [s2.fn.nextVal]
      [YulSemantics.EVM.b2w (decide (cv = w))]
      = (R.set s₀.fn.nextVal w).set s2.fn.nextVal
        (YulSemantics.EVM.b2w (decide (cv = w))) := rfl
  rw [hsm] at hstep2
  exact ⟨_, hle1.trans hle2, hbelow1.trans hbelow2, hfr2, Regs.set_same ..,
    hstep1.trans hstep2⟩

theorem trCases_sim {P : Prog} {f : Func} {funs : YulSemantics.FunEnv yulD}
    {V V' : VEnv yulD} {st1 st2 : EvmState} {cv : U256} {o : Outcome}
    {doneFuncs : Array (Option Func)} {hfuncs : FuncTableComplete P doneFuncs}
    {dflt : Option (List (Stmt Op))} :
    ∀ (cases : List (Literal × List (Stmt Op)))
      (fenv : FMap) (env : VMap) (R : Regs) (lctx : Option LoopCtx)
      (rets : Option (List Ident)) (sv : ValId) (X : List Ident)
      (joinId : BlockId) (s₀ s₁ : BState) (u : Unit) (joins : List BlockId),
      Motive (model := model) P f funs V st1 doneFuncs hfuncs
        (.stmt (.block (YulSemantics.selectSwitch yulD cv cases dflt)))
        (.sres V' st2 o) →
      FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
      env.Unique → RegsFresh R s₀.fn → CurValid s₀ → R sv = some cv →
      joinId ∈ joins → ProtectedAt joins s₀.fn →
      Completes f s₁.fn joins → CurFinal f s₁.fn →
      ∀ (done : BState) (owned : List FuncId),
      done.funcs = doneFuncs →
      (∀ i : FuncId, i ∈ owned → i < s₀.funcs.size) →
      FOwned owned s₁ done →
      trCases fenv env lctx rets sv X joinId cases dflt s₀ = some (u, s₁) →
      CasesOut (model := model) P f lctx rets X joinId s₀ s₁ R V' st1 st2 o := by
  intro cases
  induction cases with
  | nil =>
    intro fenv env R lctx rets sv X joinId s₀ s₁ u joins ihs hfe henv huniq hfr
      hvalid _hsv _hjmem hp hcompl hfin done owned hdone hbound hown h
    cases dflt with
    | none =>
      rw [trCases] at h
      obtain ⟨xvals, sA, h1, h2⟩ := M.bind_inv h
      obtain rfl : s₀ = sA := ((M.edgeArgs_inv h1).2).symm
      have aA1 : SGrowsAt s₀.fn.blocks.size s₀ s₁ := SGrowsAt.of_sealCur h2
      have hcompl0 : Completes f s₀.fn joins := SGrowsAt.completes_of aA1 hcompl
      have hseal : CurOK f s₀.fn ⟨[], .jump ⟨joinId, xvals⟩⟩ :=
        curOK_of_sealCur hfin h2
      have hsel0 : YulSemantics.selectSwitch yulD cv
          ([] : List (Literal × List (Stmt Op))) none = [] := rfl
      rw [hsel0] at ihs
      have htrs : trStmt fenv env lctx rets (.block ([] : List (Stmt Op))) s₀
          = some (some env, s₀) := by
        rw [trStmt, trScope]
        simp [allocScope, trStmts]
      have hout := ihs fenv env R lctx rets s₀ s₀ (some env) joins hfe henv huniq
        hfr hvalid hp hcompl0 ⟨_, hseal⟩ (by simp) done owned hdone hbound
        (FOwned.back_fprefix (FPrefix.of_sealCur h2) hbound hown) htrs
      cases o with
      | normal =>
        obtain ⟨env2, R₁, henv2, hle, hbelow, hfr1, henvOK, _huniq2, hsim⟩ := hout
        obtain rfl : env2 = env := (Option.some.inj henv2).symm
        obtain ⟨-, vals, hget, hvals⟩ := edgeArgs_ok henvOK h1
        exact ⟨R₁, vals, hle, hbelow, hfr1.mono aA1.nextVal, hvals,
          fun res hj => hsim res (execFrom_jump hseal hget hj)⟩
      | halt => exact CasesOut.ofNonNormal (by simp) aA1.nextVal hout
      | «break» => exact CasesOut.ofNonNormal (by simp) aA1.nextVal hout
      | «continue» => exact CasesOut.ofNonNormal (by simp) aA1.nextVal hout
      | leave => exact CasesOut.ofNonNormal (by simp) aA1.nextVal hout
    | some dbody =>
      rw [trCases] at h
      obtain ⟨renv, sA, h1, h2⟩ := M.bind_inv h
      have hsel0 : YulSemantics.selectSwitch yulD cv
          ([] : List (Literal × List (Stmt Op))) (some dbody) = dbody := rfl
      rw [hsel0] at ihs
      have h1' : trStmt fenv env lctx rets (.block dbody) s₀ = some (renv, sA) := by
        rw [trStmt]; exact h1
      have hvalidA : CurValid sA := (trStmt_cur hvalid h1').1
      cases renv with
      | none =>
        obtain ⟨-, rfl⟩ := M.pure_inv h2
        have hcurA : s₁.fn.cur = [] :=
          trScope_none_cur_nil fenv env lctx rets dbody s₀ s₁ h1
        have hcpA : CurPlaced f s₁.fn := curPlaced_of_curFinal hvalidA hcurA hfin
        have hout := ihs fenv env R lctx rets s₀ s₁ none joins hfe henv huniq hfr
          hvalid hp hcompl hcpA (fun _ => hfin) done owned hdone hbound hown h1'
        cases o with
        | normal =>
          obtain ⟨env2, R₁, hbad, -⟩ := hout
          exact absurd hbad (by simp)
        | halt => exact CasesOut.ofNonNormal (by simp) (Nat.le_refl _) hout
        | «break» => exact CasesOut.ofNonNormal (by simp) (Nat.le_refl _) hout
        | «continue» => exact CasesOut.ofNonNormal (by simp) (Nat.le_refl _) hout
        | leave => exact CasesOut.ofNonNormal (by simp) (Nat.le_refl _) hout
      | some env' =>
        obtain ⟨xv, sB, h3, h4⟩ := M.bind_inv h2
        obtain rfl : sA = sB := ((M.edgeArgs_inv h3).2).symm
        have aA1 : SGrowsAt sA.fn.blocks.size sA s₁ := SGrowsAt.of_sealCur h4
        have hcomplA : Completes f sA.fn joins := SGrowsAt.completes_of aA1 hcompl
        have hsealA : CurOK f sA.fn ⟨[], .jump ⟨joinId, xv⟩⟩ :=
          curOK_of_sealCur hfin h4
        have hout := ihs fenv env R lctx rets s₀ sA (some env') joins hfe henv
          huniq hfr hvalid hp hcomplA ⟨_, hsealA⟩ (by simp) done owned hdone
          hbound (FOwned.back_fprefix (FPrefix.of_sealCur h4)
            (fun i hi => Nat.lt_of_lt_of_le (hbound i hi)
              (trScope_grows fenv env lctx rets dbody s₀ (some env') sA h1).funcsSize)
            hown) h1'
        cases o with
        | normal =>
          obtain ⟨env2, R₁, henv2, hle, hbelow, hfr1, henvOK, _huniq2, hsim⟩ := hout
          obtain rfl : env2 = env' := (Option.some.inj henv2).symm
          obtain ⟨-, vals, hget, hvals⟩ := edgeArgs_ok henvOK h3
          exact ⟨R₁, vals, hle, hbelow, hfr1.mono aA1.nextVal, hvals,
            fun res hj => hsim res (execFrom_jump hsealA hget hj)⟩
        | halt => exact CasesOut.ofNonNormal (by simp) aA1.nextVal hout
        | «break» => exact CasesOut.ofNonNormal (by simp) aA1.nextVal hout
        | «continue» => exact CasesOut.ofNonNormal (by simp) aA1.nextVal hout
        | leave => exact CasesOut.ofNonNormal (by simp) aA1.nextVal hout
  | cons pcase rest ih =>
    obtain ⟨lit, cbody⟩ := pcase
    intro fenv env R lctx rets sv X joinId s₀ s₁ u joins ihs hfe henv huniq hfr
      hvalid hsv hjmem hp hcompl hfin done owned hdone hbound hown h
    rw [trCases] at h
    obtain ⟨t, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨u2, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨e, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨caseId, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨nextId, s6, h6, h⟩ := M.bind_inv h
    obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
    obtain ⟨u8, s8, h8, h⟩ := M.bind_inv h
    obtain ⟨renv, s9, h9, h⟩ := M.bind_inv h
    -- the dispatch test
    obtain ⟨R4, hle4, hbelow4, hfr4, hE4, hsim4⟩ :=
      trCases_test_step (P := P) (f := f) (st := st1) hfr hsv h1 h2 h3 h4
    -- builder bookkeeping for the two reserved blocks
    obtain ⟨-, -, -, -, hbl1⟩ := freshVal_fn h1
    obtain ⟨-, -, -, hbl2⟩ := emit_fn h2
    obtain ⟨-, -, -, -, hbl3⟩ := freshVal_fn h3
    obtain ⟨-, -, -, hbl4⟩ := emit_fn h4
    obtain ⟨hcase5, -, hcur5, hid5⟩ := newBlock_fn h5
    obtain ⟨hnext6, -, hcur6, hid6⟩ := newBlock_fn h6
    obtain ⟨-, hcur8, hid8, -⟩ := moveTo_fn h8
    have hbl04 : s4.fn.blocks = s₀.fn.blocks := by rw [hbl4, hbl3, hbl2, hbl1]
    have hid04 : s4.fn.curId = s₀.fn.curId := by
      obtain ⟨-, -, -, hi1, -⟩ := freshVal_fn h1
      obtain ⟨-, -, hi2, -⟩ := emit_fn h2
      obtain ⟨-, -, -, hi3, -⟩ := freshVal_fn h3
      obtain ⟨-, -, hi4, -⟩ := emit_fn h4
      rw [hi4, hi3, hi2, hi1]
    have hsz5 : s5.fn.blocks.size = s4.fn.blocks.size + 1 := newBlock_size h5
    have hsz6 : s6.fn.blocks.size = s5.fn.blocks.size + 1 := newBlock_size h6
    have hcaseEq : caseId = s₀.fn.blocks.size := by rw [hcase5, hbl04]
    have hnextEq : nextId = s₀.fn.blocks.size + 1 := by rw [hnext6, hsz5, hbl04]
    have hsz60 : s6.fn.blocks.size = s₀.fn.blocks.size + 2 := by
      rw [hsz6, hsz5, hbl04]
    have hnextLt6 : nextId < s6.fn.blocks.size := by
      rw [hnextEq, hsz60]; exact Nat.lt_succ_self _
    have hcaseLt6 : caseId < s6.fn.blocks.size := by
      rw [hcaseEq, hsz60]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)
    have hcaseNeNext : caseId ≠ nextId := by
      rw [hcaseEq, hnextEq]; exact Nat.ne_of_lt (Nat.lt_succ_self _)
    have a04 : SGrowsAt s₀.fn.blocks.size s₀ s4 :=
      (((SGrowsAt.of_grows (Grows.of_freshVal h1)).trans
        (SGrowsAt.of_grows (Grows.of_emit h2))).trans
        (SGrowsAt.of_grows (Grows.of_freshVal h3))).trans
        (SGrowsAt.of_grows (Grows.of_emit h4))
    have a06 : SGrowsAt s₀.fn.blocks.size s₀ s6 :=
      (a04.trans (SGrowsAt.of_newBlock h5)).trans (SGrowsAt.of_newBlock h6)
    have a08 : SGrowsAt s₀.fn.blocks.size s₀ s8 :=
      (a06.trans (SGrowsAt.of_sealCur h7)).trans
        (SGrowsAt.of_moveTo (N := s₀.fn.blocks.size)
          (Or.inl (Nat.le_of_eq hcaseEq.symm)) h8)
    have hsz68 : s6.fn.blocks.size ≤ s8.fn.blocks.size :=
      ((SGrowsAt.of_sealCur (N := 0) h7).trans
        (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h8)).size
    have hnextLt8 : nextId < s8.fn.blocks.size := Nat.lt_of_lt_of_le hnextLt6 hsz68
    have hcaseLt8 : caseId < s8.fn.blocks.size := Nat.lt_of_lt_of_le hcaseLt6 hsz68
    have hcurId6 : s6.fn.curId = s₀.fn.curId := by rw [hid6, hid5, hid04]
    have hcurId7 : s7.fn.curId = s6.fn.curId := (sealCur_cur h7).choose_spec.1
    have hnextNotIn : nextId ∉ joins := by
      intro hi
      exact Nat.lt_irrefl _ (Nat.lt_of_succ_lt (hnextEq ▸ hp.below nextId hi))
    have hcaseNotIn : caseId ∉ joins := by
      intro hi
      exact Nat.lt_irrefl _ (hcaseEq ▸ hp.below caseId hi)
    have hne7case : s7.fn.curId ≠ caseId := by
      rw [hcurId7, hcurId6, hcaseEq]
      exact Nat.ne_of_lt hvalid
    have hprot7 : s7.fn.curId ∉ joins := by rw [hcurId7, hcurId6]; exact hp.away
    have hold7 : s7.fn.curId < nextId := by
      rw [hcurId7, hcurId6, hnextEq]
      exact Nat.lt_succ_of_lt hvalid
    have hsim46 : SimS (model := model) P f s4.fn R4 st1 s6.fn R4 st1 :=
      simS_id (by rw [hid6, hid5]) (by rw [hcur6, hcur5])
    have gbody : SGrows s8 s9 :=
      trScope_grows fenv env lctx rets cbody s8 renv s9 h9
    have hbound9 : ∀ i : FuncId, i ∈ owned → i < s9.funcs.size := by
      intro i hi
      exact Nat.lt_of_lt_of_le (hbound i hi)
        (Nat.le_trans a08.funcsSize gbody.funcsSize)
    have hnextLe8 : nextId ≤ s8.fn.blocks.size := Nat.le_of_lt hnextLt8
    have hcur9 : s9.fn.curId = caseId ∨ s8.fn.blocks.size ≤ s9.fn.curId := by
      rcases gbody.curId with hq | hq
      · exact Or.inl (by rw [hq, hid8])
      · exact Or.inr hq
    have hne9next : s9.fn.curId ≠ nextId := by
      rcases hcur9 with hq | hq
      · rw [hq]; exact hcaseNeNext
      · exact (Nat.ne_of_lt (Nat.lt_of_lt_of_le hnextLt8 hq)).symm
    have hprot9 : s9.fn.curId ∉ joins := by
      intro hi
      have hlt := hp.below _ hi
      rcases hcur9 with hq | hq
      · exact Nat.lt_irrefl _ (hcaseEq ▸ hq ▸ hlt)
      · exact Nat.lt_irrefl _
          (Nat.lt_of_lt_of_le hlt (Nat.le_trans a08.size hq))
    have h9' : trStmt fenv env lctx rets (.block cbody) s8 = some (renv, s9) := by
      rw [trStmt]; exact h9
    have hvalid8 : CurValid s8 := by
      show s8.fn.curId < s8.fn.blocks.size
      rw [hid8]; exact hcaseLt8
    have hvalid9 : CurValid s9 := (trStmt_cur hvalid8 h9').1
    have hfr8 : RegsFresh R4 s8.fn := hfr4.mono
      (((SGrowsAt.of_newBlock (N := 0) h5).trans
        ((SGrowsAt.of_newBlock (N := 0) h6).trans
          ((SGrowsAt.of_sealCur (N := 0) h7).trans
            (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h8)))).nextVal)
    have hp8 : ProtectedAt (nextId :: joins) s8.fn := by
      refine ⟨?_, ?_⟩
      · intro i hi
        simp only [List.mem_cons] at hi
        rcases hi with rfl | hi
        · exact hnextLt8
        · exact Nat.lt_of_lt_of_le (hp.below i hi) a08.size
      · rw [hid8]
        simp only [List.mem_cons, not_or]
        exact ⟨hcaseNeNext, hcaseNotIn⟩
    have hnv08 : s₀.fn.nextVal ≤ s8.fn.nextVal := a08.nextVal
    by_cases hmatch : cv = YulSemantics.EVM.litValue lit
    · -- the scrutinee selects this case: enter `caseId`
      have hsel0 : YulSemantics.selectSwitch yulD cv ((lit, cbody) :: rest) dflt
          = cbody := by
        simp [YulSemantics.selectSwitch, hmatch]
      rw [hsel0] at ihs
      have hE1 : R4 e = some 1 := by
        rw [hE4]; simp [YulSemantics.EVM.b2w, hmatch]
      have a59 : SGrowsAt 0 s5 s9 :=
        ((SGrowsAt.of_newBlock (N := 0) h6).trans
          ((SGrowsAt.of_sealCur (N := 0) h7).trans
            (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h8))).trans
          (gbody.mono (Nat.zero_le _))
      obtain ⟨bb, hbb, hbp⟩ := a59.params caseId ⟨[], [], .ret []⟩
        (newBlock_target_get h5)
      cases renv with
      | none =>
        obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb, hc⟩ := M.bind_inv h
        have gT1 : SGrows sb s₁ :=
          trCases_grows fenv env lctx rets sv X joinId rest dflt sv X joinId sb u
            s₁ hc
        have aP : SGrowsAt nextId s8 sa :=
          (gbody.mono hnextLe8).trans (SGrowsAt.of_pure ha)
        have aPT : SGrowsAt nextId sa sb :=
          SGrowsAt.of_moveTo (Or.inl (Nat.le_refl _)) hb
        have hnextLtT : nextId < sb.fn.blocks.size :=
          Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hnextLt8 aP.size) aPT.size
        have a81 : SGrowsAt nextId s8 s₁ :=
          (aP.trans aPT).trans (gT1.mono (Nat.le_of_lt hnextLtT))
        have hfin7 : CurFinal f s7.fn :=
          curFinal_of_move_sgrowsAt hold7 h8 hne7case hprot7 a81 hcompl
        have hbranch : CurOK f s6.fn
            ⟨[], .branch e ⟨caseId, []⟩ ⟨nextId, []⟩⟩ :=
          curOK_of_sealCur hfin7 h7
        have hcomplb : Completes f sb.fn joins := SGrowsAt.completes_of gT1 hcompl
        have hcompla : Completes f sa.fn (nextId :: joins) :=
          Completes.of_moveTo_protected (by simp) hb (hcomplb.protect nextId)
        have hcompl9 : Completes f s9.fn (nextId :: joins) :=
          SGrowsAt.completes_of (SGrowsAt.of_pure ha) hcompla
        have hcura : sa.fn.curId = s9.fn.curId := by
          obtain ⟨-, rfl⟩ := M.pure_inv ha; rfl
        have hfina : CurFinal f sa.fn :=
          curFinal_of_move_grows hb (by rw [hcura]; exact hne9next)
            (by rw [hcura]; exact hprot9) gT1 hcompl
        have hfin9 : CurFinal f s9.fn := by
          obtain ⟨-, hq⟩ := M.pure_inv ha; rw [← hq]; exact hfina
        have hcur9nil : s9.fn.cur = [] :=
          trScope_none_cur_nil fenv env lctx rets cbody s8 s9 h9
        have hcp9 : CurPlaced f s9.fn :=
          curPlaced_of_curFinal hvalid9 hcur9nil hfin9
        have hsimTrue : SimS (model := model) P f s6.fn R4 st1 s8.fn R4 st1 :=
          simS_branchTrue_body hcompl9 hbranch hE1 (by decide) hbb hbp hid8 hcur8
        have hsimPre : SimS (model := model) P f s₀.fn R st1 s8.fn R4 st1 :=
          hsim4.trans (hsim46.trans hsimTrue)
        have p9a : FPrefix s9.funcs.size s9 sa := FPrefix.of_pure ha
        have p9b : FPrefix s9.funcs.size sa sb := FPrefix.of_moveTo hb
        have p9rest : FPrefix s9.funcs.size sb s₁ :=
          trCases_fprefix fenv env lctx rets sv X joinId rest dflt
            sv X joinId s9.funcs.size sb u s₁
              ((p9a.trans p9b).size (Nat.le_refl _)) hc
        have hown9 : FOwned owned s9 done :=
          FOwned.back_fprefix ((p9a.trans p9b).trans p9rest) hbound9 hown
        have hout := ihs fenv env R4 lctx rets s8 s9 none (nextId :: joins) hfe
          (henv.mono hle4) huniq hfr8 hvalid8 hp8 hcompl9 hcp9 (fun _ => hfin9)
          done owned hdone
          (fun i hi => Nat.lt_of_lt_of_le (hbound i hi) a08.funcsSize)
          hown9 h9'
        have a91 : SGrowsAt 0 s9 s₁ :=
          ((SGrowsAt.of_pure (N := 0) ha).trans
            (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) hb)).trans
            (gT1.mono (Nat.zero_le _))
        cases o with
        | normal =>
          obtain ⟨env2, R2, hbad, -⟩ := hout
          exact absurd hbad (by simp)
        | halt =>
          exact CasesOut.ofNonNormal (by simp) a91.nextVal
            (SOut.prefix hle4 hbelow4 hnv08 hsimPre hout)
        | «break» =>
          exact CasesOut.ofNonNormal (by simp) a91.nextVal
            (SOut.prefix hle4 hbelow4 hnv08 hsimPre hout)
        | «continue» =>
          exact CasesOut.ofNonNormal (by simp) a91.nextVal
            (SOut.prefix hle4 hbelow4 hnv08 hsimPre hout)
        | leave =>
          exact CasesOut.ofNonNormal (by simp) a91.nextVal
            (SOut.prefix hle4 hbelow4 hnv08 hsimPre hout)
      | some envB =>
        obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb, h⟩ := M.bind_inv h
        obtain ⟨uc, sc, hc, hd⟩ := M.bind_inv h
        obtain rfl : s9 = sa := ((M.edgeArgs_inv ha).2).symm
        have gT1 : SGrows sc s₁ :=
          trCases_grows fenv env lctx rets sv X joinId rest dflt sv X joinId sc u
            s₁ hd
        have aP : SGrowsAt nextId s8 sb :=
          (gbody.mono hnextLe8).trans (SGrowsAt.of_sealCur hb)
        have aPT : SGrowsAt nextId sb sc :=
          SGrowsAt.of_moveTo (Or.inl (Nat.le_refl _)) hc
        have hnextLtT : nextId < sc.fn.blocks.size :=
          Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hnextLt8 aP.size) aPT.size
        have a81 : SGrowsAt nextId s8 s₁ :=
          (aP.trans aPT).trans (gT1.mono (Nat.le_of_lt hnextLtT))
        have hfin7 : CurFinal f s7.fn :=
          curFinal_of_move_sgrowsAt hold7 h8 hne7case hprot7 a81 hcompl
        have hbranch : CurOK f s6.fn
            ⟨[], .branch e ⟨caseId, []⟩ ⟨nextId, []⟩⟩ :=
          curOK_of_sealCur hfin7 h7
        have hcomplc : Completes f sc.fn joins := SGrowsAt.completes_of gT1 hcompl
        have hcomplb : Completes f sb.fn (nextId :: joins) :=
          Completes.of_moveTo_protected (by simp) hc (hcomplc.protect nextId)
        have hcompl9 : Completes f s9.fn (nextId :: joins) :=
          SGrowsAt.completes_of (SGrowsAt.of_sealCur hb) hcomplb
        have hcurb : sb.fn.curId = s9.fn.curId := (sealCur_cur hb).choose_spec.1
        have hfinb : CurFinal f sb.fn :=
          curFinal_of_move_grows hc (by rw [hcurb]; exact hne9next)
            (by rw [hcurb]; exact hprot9) gT1 hcompl
        have hseal9 : CurOK f s9.fn ⟨[], .jump ⟨joinId, xv⟩⟩ :=
          curOK_of_sealCur hfinb hb
        have hsimTrue : SimS (model := model) P f s6.fn R4 st1 s8.fn R4 st1 :=
          simS_branchTrue_body hcompl9 hbranch hE1 (by decide) hbb hbp hid8 hcur8
        have hsimPre : SimS (model := model) P f s₀.fn R st1 s8.fn R4 st1 :=
          hsim4.trans (hsim46.trans hsimTrue)
        have p9a : FPrefix s9.funcs.size s9 s9 := FPrefix.of_edgeArgs ha
        have p9b : FPrefix s9.funcs.size s9 sb := FPrefix.of_sealCur hb
        have p9c : FPrefix s9.funcs.size sb sc := FPrefix.of_moveTo hc
        have p9rest : FPrefix s9.funcs.size sc s₁ :=
          trCases_fprefix fenv env lctx rets sv X joinId rest dflt
            sv X joinId s9.funcs.size sc u s₁
              (((p9a.trans p9b).trans p9c).size (Nat.le_refl _)) hd
        have hown9 : FOwned owned s9 done := FOwned.back_fprefix
          (((p9a.trans p9b).trans p9c).trans p9rest) hbound9 hown
        have hout := ihs fenv env R4 lctx rets s8 s9 (some envB) (nextId :: joins)
          hfe (henv.mono hle4) huniq hfr8 hvalid8 hp8 hcompl9 ⟨_, hseal9⟩ (by simp)
          done owned hdone
          (fun i hi => Nat.lt_of_lt_of_le (hbound i hi) a08.funcsSize)
          hown9 h9'
        have a91 : SGrowsAt 0 s9 s₁ :=
          ((SGrowsAt.of_sealCur (N := 0) hb).trans
            (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) hc)).trans
            (gT1.mono (Nat.zero_le _))
        cases o with
        | normal =>
          obtain ⟨envB', RB, henvB', hleB, hbelowB, hfrB, henvOK, -, hsimBody⟩ :=
            hout
          obtain rfl : envB' = envB := (Option.some.inj henvB').symm
          obtain ⟨-, vals, hget, hvals⟩ := edgeArgs_ok henvOK ha
          exact ⟨RB, vals, hle4.trans hleB,
            hbelow4.trans (hbelowB.mono hnv08), hfrB.mono a91.nextVal, hvals,
            fun res hj =>
              hsimPre res (hsimBody res (execFrom_jump hseal9 hget hj))⟩
        | halt =>
          exact CasesOut.ofNonNormal (by simp) a91.nextVal
            (SOut.prefix hle4 hbelow4 hnv08 hsimPre hout)
        | «break» =>
          exact CasesOut.ofNonNormal (by simp) a91.nextVal
            (SOut.prefix hle4 hbelow4 hnv08 hsimPre hout)
        | «continue» =>
          exact CasesOut.ofNonNormal (by simp) a91.nextVal
            (SOut.prefix hle4 hbelow4 hnv08 hsimPre hout)
        | leave =>
          exact CasesOut.ofNonNormal (by simp) a91.nextVal
            (SOut.prefix hle4 hbelow4 hnv08 hsimPre hout)
    · -- the scrutinee skips this case: fall through to `nextId`
      have hsel0 : YulSemantics.selectSwitch yulD cv ((lit, cbody) :: rest) dflt
          = YulSemantics.selectSwitch yulD cv rest dflt := by
        simp [YulSemantics.selectSwitch, hmatch]
      rw [hsel0] at ihs
      have hE0 : R4 e = some 0 := by
        rw [hE4]; simp [YulSemantics.EVM.b2w, hmatch]
      have hkey : ∀ (sP sT : BState) (u' : Unit),
          SGrowsAt nextId s8 sP → moveTo nextId sP = some (u', sT) →
          trCases fenv env lctx rets sv X joinId rest dflt sT = some (u, s₁) →
          CasesOut (model := model) P f lctx rets X joinId s₀ s₁ R V' st1 st2 o := by
        intro sP sT u' aP hmv hT
        obtain ⟨-, hcurT0, hcurT, -⟩ := moveTo_fn hmv
        have gT1 : SGrows sT s₁ :=
          trCases_grows fenv env lctx rets sv X joinId rest dflt sv X joinId sT u
            s₁ hT
        have aPT : SGrowsAt nextId sP sT :=
          SGrowsAt.of_moveTo (Or.inl (Nat.le_refl _)) hmv
        have a6T : SGrowsAt 0 s6 sT :=
          ((SGrowsAt.of_sealCur (N := 0) h7).trans
            (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h8)).trans
            ((aP.mono (Nat.zero_le _)).trans (aPT.mono (Nat.zero_le _)))
        have hnextLtT : nextId < sT.fn.blocks.size :=
          Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hnextLt8 aP.size) aPT.size
        have a81 : SGrowsAt nextId s8 s₁ :=
          (aP.trans aPT).trans (gT1.mono (Nat.le_of_lt hnextLtT))
        have hfin7 : CurFinal f s7.fn :=
          curFinal_of_move_sgrowsAt hold7 h8 hne7case hprot7 a81 hcompl
        have hbranch : CurOK f s6.fn
            ⟨[], .branch e ⟨caseId, []⟩ ⟨nextId, []⟩⟩ :=
          curOK_of_sealCur hfin7 h7
        have hcomplT : Completes f sT.fn joins := SGrowsAt.completes_of gT1 hcompl
        have hpT : ProtectedAt joins sT.fn := by
          refine ⟨fun i hi => ?_, ?_⟩
          · exact Nat.lt_of_lt_of_le (hp.below i hi)
              (Nat.le_trans a06.size a6T.size)
          · rw [hcurT]; exact hnextNotIn
        have hvalidT : CurValid sT := by
          show sT.fn.curId < sT.fn.blocks.size
          rw [hcurT]; exact hnextLtT
        have a4T : SGrowsAt 0 s4 sT :=
          ((SGrowsAt.of_newBlock (N := 0) h5).trans
            (SGrowsAt.of_newBlock (N := 0) h6)).trans a6T
        have hres := ih fenv env R4 lctx rets sv X joinId sT s₁ u joins ihs hfe
          (henv.mono hle4) huniq (hfr4.mono a4T.nextVal) hvalidT (hle4 sv cv hsv)
          hjmem hpT hcompl hfin done owned hdone
          (fun i hi => Nat.lt_of_lt_of_le (hbound i hi)
            (Nat.le_trans a04.funcsSize a4T.funcsSize))
          hown hT
        obtain ⟨nb, hnb, hnbp⟩ := a6T.params nextId ⟨[], [], .ret []⟩
          (newBlock_target_get h6)
        have hsimBr : SimS (model := model) P f s6.fn R4 st1 sT.fn
            (R4.setMany nb.params []) st1 :=
          simS_branchFalse_join (vals := []) hcomplT hbranch hE0 hnb hcurT hcurT0
            (by simp) (by rw [hnbp]; simp)
        have hsm : R4.setMany nb.params [] = R4 := by rw [hnbp]; rfl
        rw [hsm] at hsimBr
        exact CasesOut.prefix hle4 hbelow4
          (Nat.le_trans a04.nextVal a4T.nextVal)
          (hsim4.trans (hsim46.trans hsimBr)) hres
      cases renv with
      | none =>
        obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb, hc⟩ := M.bind_inv h
        exact hkey sa sb ub ((gbody.mono hnextLe8).trans (SGrowsAt.of_pure ha))
          hb hc
      | some envB =>
        obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb, h⟩ := M.bind_inv h
        obtain ⟨uc, sc, hc, hd⟩ := M.bind_inv h
        exact hkey sb sc uc
          (((gbody.mono hnextLe8).trans (SGrowsAt.of_edgeArgs ha)).trans
            (SGrowsAt.of_sealCur hb)) hc hd

omit model in
/-- The switch analysis scans every case body and the default. -/
theorem modCases_flatMap (cases : List (Literal × List (Stmt Op))) :
    (cases.map Prod.snd).flatMap (modStmts []) = modCases [] cases := by
  induction cases with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨l, b⟩ := p
    rw [List.map_cons, List.flatMap_cons, modCases, ih]

omit model in
theorem mem_switch_flatMap {cases : List (Literal × List (Stmt Op))}
    {dflt : Option (List (Stmt Op))} {x : Ident}
    (hx : x ∈ modStmt ([] : List Ident)
      (.switch (.lit (.number 0)) cases dflt)) :
    x ∈ (cases.map Prod.snd ++ dflt.toList).flatMap (modStmts []) := by
  rw [List.flatMap_append, modCases_flatMap]
  cases dflt with
  | none => simpa [modStmt] using hx
  | some b => simpa [modStmt] using hx

set_option maxHeartbeats 1000000 in
/-- **`switchExec`** — evaluate the scrutinee, run the dispatch chain, and
reconstruct the environment at the reserved join block. -/
theorem sim_switchExec {P : Prog} {f : Func} {funs : YulSemantics.FunEnv yulD}
    {V V' : VEnv yulD} {st st1 st2 : EvmState} {cv : U256} {o : Outcome}
    {c : Expr Op} {cases : List (Literal × List (Stmt Op))}
    {dflt : Option (List (Stmt Op))}
    {doneFuncs : Array (Option Func)} {hfuncs : FuncTableComplete P doneFuncs}
    (hsel : YulSemantics.Step yulD funs V st1
      (.stmt (.block (YulSemantics.selectSwitch yulD cv cases dflt)))
      (.sres V' st2 o))
    (ihc : Motive (model := model) P f funs V st doneFuncs hfuncs
      (.expr c) (.eres (.vals [cv] st1)))
    (ihs : Motive (model := model) P f funs V st1 doneFuncs hfuncs
      (.stmt (.block (YulSemantics.selectSwitch yulD cv cases dflt)))
      (.sres V' st2 o)) :
    Motive (model := model) P f funs V st doneFuncs hfuncs
      (.stmt (.switch c cases dflt)) (.sres V' st2 o) := by
  intro fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq hfr hvalid hp
    hcompl _hcp _hfin done owned hdone hbound hown htr
  let X := modifiedX env (cases.map Prod.snd ++ dflt.toList)
  unfold trStmt at htr
  obtain ⟨sv, sA, h1, htr⟩ := M.bind_inv htr
  obtain ⟨joinParams, sB, h2, htr⟩ := M.bind_inv htr
  obtain ⟨joinId, sC, h3, htr⟩ := M.bind_inv htr
  obtain ⟨uD, sD, h4, htr⟩ := M.bind_inv htr
  obtain ⟨uE, sE, h5, h6⟩ := M.bind_inv htr
  obtain ⟨hrenv, rfl⟩ := M.pure_inv h6
  have hXE := congrArg (modifiedX env) (switchBodies_eq cases dflt)
  have h2X : X.mapM (fun _ => freshVal) sA = some (joinParams, sB) := by
    exact Eq.mp (congrArg
      (fun X' => X'.mapM (fun _ => freshVal) sA = some (joinParams, sB)) hXE) h2
  have h4X : trCases fenv env lctx rets sv X joinId cases dflt sC =
      some (uD, sD) := by
    exact Eq.mp (congrArg (fun X' =>
      trCases fenv env lctx rets sv X' joinId cases dflt sC = some (uD, sD)) hXE) h4
  have hrenvX : renv = some (env.setMany X joinParams) :=
    Eq.mp (congrArg (fun X' => renv = some (env.setMany X' joinParams)) hXE) hrenv
  have g0A : Grows s₀ sA := trExpr_grows c fenv env s₀ sA sv h1
  have hvalidA : CurValid sA := hvalid.of_grows g0A
  have aAB : SGrowsAt sA.fn.blocks.size sA sB :=
    SGrowsAt.of_grows (Grows.of_mapM_freshVal h2X)
  have aAC := aAB.trans (SGrowsAt.of_newBlock h3)
  have csAC := (CurSame.of_grows (Grows.of_mapM_freshVal h2X)).trans
    (CurSame.of_newBlock h3)
  have hvalidC : CurValid sC := CurValid.of_same_sgrows hvalidA aAC csAC.1
  obtain ⟨hvalidD, hkCD⟩ := trCases_cur_closed fenv env lctx rets sv
    X joinId cases dflt sC sD uD hvalidC h4X
  have gCD := trCases_grows fenv env lctx rets sv X joinId cases dflt
    sv X joinId sC uD sD h4X
  have hjoinLt : joinId < sC.fn.blocks.size := newBlock_target_lt h3
  have hcurLtJoin : sC.fn.curId < joinId := by
    rw [csAC.1, SGrowsAt.newBlock_id h3]
    exact Nat.lt_of_lt_of_le hvalidA aAB.size
  have hjoinNeC : sC.fn.curId ≠ joinId := Nat.ne_of_lt hcurLtJoin
  have hjoinNeD : sD.fn.curId ≠ joinId := by
    intro heq
    rcases gCD.curId with heqC | hge
    · exact hjoinNeC (heqC ▸ heq)
    · exact Nat.not_lt_of_ge (heq ▸ hge) hjoinLt
  have hpA : ProtectedAt joins sA.fn :=
    ProtectedAt.forward hp (SGrows.of_grows g0A)
  have hpC : ProtectedAt joins sC.fn := ProtectedAt.forward hpA aAC
  have hpD : ProtectedAt joins sD.fn := ProtectedAt.forward hpC gCD
  have hcomplD : Completes f sD.fn (joinId :: joins) :=
    Completes.of_moveTo_protected (by simp) h5 (hcompl.protect joinId)
  have hprotD : sD.fn.curId ∉ joinId :: joins := by
    simp only [List.mem_cons]
    exact fun hq => hq.elim hjoinNeD hpD.away
  have hcurD : sD.fn.cur = [] := trCases_cur_nil fenv env lctx rets sv
    X joinId cases dflt sC sD uD h4X
  have hcpD : CurPlaced f sD.fn := CurPlaced.of_moveTo_empty hvalidD hcurD
    hjoinNeD h5 hprotD (hcompl.protect joinId)
  have hfinD : CurFinal f sD.fn := curFinal_of_move_grows h5 hjoinNeD
    hpD.away (SGrows.rfl' s₁) hcompl
  have hprotC : sC.fn.curId ∉ joinId :: joins := by
    simp only [List.mem_cons]
    exact fun hq => hq.elim hjoinNeC hpC.away
  have hcpC : CurPlaced f sC.fn :=
    curPlaced_back (renv := none) hkCD hprotC hcomplD (fun _ => hfinD) hcpD
  have hcpB : CurPlaced f sB.fn :=
    (CurSame.of_newBlock h3).placed_back hcpC
  have hcpA : CurPlaced f sA.fn :=
    curPlaced_back_grows (Grows.of_mapM_freshVal h2X) hcpB
  have hjoinBase : sA.fn.blocks.size ≤ joinId := by
    rw [SGrowsAt.newBlock_id h3]
    exact aAB.size
  have htail : SGrowsAt sA.fn.blocks.size sA s₁ :=
    aAC.trans ((gCD.mono aAC.size).trans
      (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hjoinBase) h5))
  have hcomplA : Completes f sA.fn joins := htail.completes_of hcompl
  obtain ⟨RA, hleA, hbelowA, hfrA, hcv, hsimC⟩ :=
    ihc.1 fenv env R s₀ sA sv cv joins hfe henv hfr hp hcomplA hcpA rfl h1
  have hfrC : RegsFresh RA sC.fn := hfrA.mono aAC.nextVal
  have hpC' : ProtectedAt (joinId :: joins) sC.fn := by
    refine ⟨?_, hprotC⟩
    intro i hi
    simp only [List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact hjoinLt
    · exact hpC.below i hi
  have hboundD : ∀ i : FuncId, i ∈ owned → i < sD.funcs.size := by
    intro i hi
    exact Nat.lt_of_lt_of_le (hbound i hi)
      (((SGrows.of_grows g0A).trans aAC).trans gCD).funcsSize
  have hownD : FOwned owned sD done :=
    FOwned.back_fprefix (FPrefix.of_moveTo h5) hboundD hown
  have hcasesOut := trCases_sim (model := model) (P := P) (f := f) (funs := funs)
    (V := V) (st1 := st1) (st2 := st2) (cv := cv) (o := o) (V' := V')
    (doneFuncs := doneFuncs) (hfuncs := hfuncs) (dflt := dflt)
    cases fenv env RA lctx rets sv X joinId sC sD uD (joinId :: joins)
    ihs hfe (henv.mono hleA) huniq hfrC hvalidC hcv (by simp) hpC' hcomplD hfinD
    done owned hdone
    (fun i hi => Nat.lt_of_lt_of_le (hbound i hi)
      ((SGrows.of_grows g0A).trans aAC).funcsSize)
    hownD h4X
  have hnv0C : s₀.fn.nextVal ≤ sC.fn.nextVal :=
    Nat.le_trans g0A.nextVal aAC.nextVal
  obtain ⟨hparamLen, hparamRange, hsB⟩ := M.mapM_freshVal_length h2X
  obtain ⟨-, -, hcurC, hidC⟩ := newBlock_fn h3
  have hsimAC : SimS (model := model) P f sA.fn RA st1 sC.fn RA st1 :=
    simS_id (by rw [hidC, hsB]) (by rw [hcurC, hsB])
  have hsimPre : SimS (model := model) P f s₀.fn R st sC.fn RA st1 :=
    hsimC.trans hsimAC
  have hnvD1 : sD.fn.nextVal ≤ s₁.fn.nextVal :=
    (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h5).nextVal
  cases o with
  | halt =>
    exact SOut.prefix hleA hbelowA hnv0C hsimPre
      (SOut.of_nonNormal (renv := none) (by simp) hnvD1 hcasesOut)
  | «break» =>
    exact SOut.prefix hleA hbelowA hnv0C hsimPre
      (SOut.of_nonNormal (renv := none) (by simp) hnvD1 hcasesOut)
  | «continue» =>
    exact SOut.prefix hleA hbelowA hnv0C hsimPre
      (SOut.of_nonNormal (renv := none) (by simp) hnvD1 hcasesOut)
  | leave =>
    exact SOut.prefix hleA hbelowA hnv0C hsimPre
      (SOut.of_nonNormal (renv := none) (by simp) hnvD1 hcasesOut)
  | normal =>
    obtain ⟨R₁, vals, hleB, hbelowB, hfrB, hvals, hcont⟩ := hcasesOut
    have hnd : joinParams.Nodup := by
      rw [hparamRange]; exact M.nodup_range' _ _
    have hparamsLt : ∀ i ∈ joinParams, i < sC.fn.nextVal := by
      intro i hi
      rw [hparamRange] at hi
      have hi' := (M.mem_range'_bounds hi).2
      have hiB : i < sB.fn.nextVal := by rw [hsB]; exact hi'
      exact Nat.lt_of_lt_of_le hiB (SGrowsAt.of_newBlock (N := 0) h3).nextVal
    have hparamsGe : ∀ i ∈ joinParams, sA.fn.nextVal ≤ i := by
      intro i hi
      rw [hparamRange] at hi
      exact (M.mem_range'_bounds hi).1
    have hnone : ∀ i ∈ joinParams, R₁ i = none := by
      intro i hi
      rw [hbelowB i (hparamsLt i hi)]
      exact hfrA i (hparamsGe i hi)
    have hleJ : Regs.Le R₁ (R₁.setMany joinParams vals) :=
      Regs.Le.setMany hnd hnone
    have hbelowJ : Regs.BelowEq s₀.fn.nextVal R₁ (R₁.setMany joinParams vals) := by
      apply Regs.BelowEq.setMany
      intro i hi
      exact Nat.le_trans g0A.nextVal (hparamsGe i hi)
    have hfrJ : RegsFresh (R₁.setMany joinParams vals) s₁.fn := by
      intro i hi
      rw [Regs.setMany_other]
      · exact hfrB i (Nat.le_trans
          (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h5).nextVal hi)
      · intro himem
        exact absurd (hparamsLt i himem)
          (Nat.not_lt_of_ge (Nat.le_trans
            (Nat.le_trans (gCD.mono (Nat.zero_le _)).nextVal
              (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h5).nextVal)
            hi))
    have aC1 : SGrowsAt 0 sC s₁ :=
      (gCD.mono (Nat.zero_le _)).trans
        (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h5)
    obtain ⟨jb, hjb, hjp⟩ := aC1.params joinId ⟨joinParams, [], .ret []⟩
      (newBlock_target_get h3)
    obtain ⟨-, hcur0, hcur, -⟩ := moveTo_fn h5
    have hjbLen : jb.params.length = vals.length := by
      rw [hjp, hparamLen]
      exact hvals.length_eq
    have hsimJoin : SimS (model := model) P f sC.fn RA st1 s₁.fn
        (R₁.setMany joinParams vals) st2 := by
      have hs : SimS (model := model) P f sC.fn RA st1 s₁.fn
          (R₁.setMany jb.params vals) st2 := fun res hex =>
        hcont res (jumpTo_of_completes hcompl hjb hcur hcur0 hjbLen hex)
      simpa only [hjp] using hs
    have hnames : VEnv.names V' = VEnv.names V := by
      have hm := (mod_sim hsel).1
      simpa [declsOfStmt] using hm
    have hmod : ModOut []
        (modStmts [] (YulSemantics.selectSwitch yulD cv cases dflt)) V V' := by
      have hm := (mod_sim hsel).2 [] (localsOK_nil V)
      simpa [modStmt] using hm
    have hVjoin : YulSemantics.VEnv.setMany V X vals = V' :=
      setMany_eq_of_modOut henv huniq hnames hmod hvals
        (fun x hx => modifiedX_mem_names hx)
        (fun x hx hm => mem_modifiedX hx (mem_switch_flatMap
          (mem_modStmt_switch (cv := cv) hm)))
    have hpget : (R₁.setMany joinParams vals).getMany joinParams = some vals :=
      Regs.getMany_setMany_self hnd (by rw [hparamLen]; exact hvals.length_eq)
    have henvJ : EnvOK (model := model) (env.setMany X joinParams) V'
        (R₁.setMany joinParams vals) := by
      have he : EnvOK (model := model) (env.setMany X joinParams)
          (YulSemantics.VEnv.setMany V X vals) (R₁.setMany joinParams vals) :=
        EnvOK.setMany (henv.mono (hleA.trans (hleB.trans hleJ)))
          (Regs.getMany_eq_some_iff.mp hpget)
      rwa [hVjoin] at he
    exact ⟨env.setMany X joinParams, R₁.setMany joinParams vals, hrenvX,
      hleA.trans (hleB.trans hleJ),
      (hbelowA.trans (hbelowB.mono hnv0C)).trans hbelowJ,
      hfrJ, henvJ, huniq.setMany _ _,
      hsimPre.trans hsimJoin⟩


set_option maxHeartbeats 1000000 in
/-- **The construction simulation induction.** One `induction … with` over the
source `Step` derivation, with `Motive` above. Cases still open carry their own
`sorry`; everything else is discharged by the per-case lemmas above.  The
completed function table is an induction-wide parameter, so every recursive IH
uses the same final table and completion proof. -/
theorem sim {P : Prog} {f : Func} {funs : YulSemantics.FunEnv yulD}
    {V : VEnv yulD} {yst : EvmState} {c : YulSemantics.Code Op}
    {res : YulSemantics.Res yulD} {doneFuncs : Array (Option Func)}
    (hfuncs : FuncTableComplete P doneFuncs)
    (h : YulSemantics.Step yulD funs V yst c res) :
    Motive (model := model) P f funs V yst doneFuncs hfuncs c res := by
  induction h generalizing f with
  | @lit funs V st l =>
    refine ⟨?_, ?_, ?_⟩
    · intro fenv env R s₀ s₁ i v _joins _ _ hfr _hp _ _ hvs htr
      obtain rfl : v = YulSemantics.EVM.litValue l := by simpa using hvs.symm
      exact sim_lit hfr htr
    · intro fenv env R s₀ s₁ n ids _joins _ _ hfr _hp _ _ _ htr
      obtain ⟨-, i, rfl, htrE⟩ := trExprN_nonCall_inv (by intro fn args; simp) htr
      exact (sim_lit hfr htrE).toEOutL
    · intro _ fenv env R lctx rets s₀ s₁ renv _joins _ _ _ _ _ _ _ _ _ htr
      rw [trStmt] at htr
      · exact absurd htr (by simp [reject])
      · intro op args h; cases h
      · intro fn args h; cases h
  | @var funs V st x v hget =>
    refine ⟨?_, ?_, ?_⟩
    · intro fenv env R s₀ s₁ i v' _joins _ henv hfr _hp _ _ hvs htr
      obtain rfl : v' = v := by simpa using hvs.symm
      exact sim_var hfr henv hget htr
    · intro fenv env R s₀ s₁ n ids _joins _ henv hfr _hp _ _ _ htr
      obtain ⟨-, i, rfl, htrE⟩ := trExprN_nonCall_inv (by intro fn args; simp) htr
      exact (sim_var hfr henv hget htrE).toEOutL
    · intro _ fenv env R lctx rets s₀ s₁ renv _joins _ _ _ _ _ _ _ _ _ htr
      rw [trStmt] at htr
      · exact absurd htr (by simp [reject])
      · intro op args h; cases h
      · intro fn args h; cases h
  | @builtinOk funs V st op args argvals st1 rets st2 hargs hb iha =>
    have key : ∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState)
        (i : ValId) (v : U256) (joins : List BlockId),
        FEnvOK (model := model) P funs fenv →
        EnvOK (model := model) env V R → RegsFresh R s₀.fn →
        ProtectedAt joins s₀.fn → Completes f s₁.fn joins →
        CurPlaced f s₁.fn → rets = [v] →
        trExpr fenv env (.builtin op args) s₀ = some (i, s₁) →
        EOut (model := model) P f s₀ s₁ R i v st st2 := by
      intro fenv env R s₀ s₁ i v joins hfe henv hfr hp hcompl hcp hvs htr
      rw [trExpr] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      obtain ⟨d, sB, h2, htr⟩ := M.bind_inv htr
      obtain ⟨u, sC, h3, h4⟩ := M.bind_inv htr
      obtain ⟨rfl, rfl⟩ := M.pure_inv h4
      rw [M.freshVal_apply] at h2
      obtain ⟨rfl, rfl⟩ := M.some_pair_inj h2
      rw [M.emit_apply] at h3
      obtain ⟨-, rfl⟩ := M.some_pair_inj h3
      obtain rfl : rets = [v] := hvs
      obtain ⟨R₁, hle, hbelow, hfr₁, hget, hsim⟩ :=
        iha fenv env R s₀ sA as joins hfe henv hfr hp
        (SGrowsAt.completes_of
          (SGrows.of_grows ((Grows.of_freshVal rfl).trans (Grows.of_emit rfl))) hcompl)
        (curPlaced_back_grows ((Grows.of_freshVal rfl).trans (Grows.of_emit rfl)) hcp) h1
      have g0A := trArgs_grows args fenv env s₀ sA as h1
      refine ⟨R₁.set sA.fn.nextVal v, hle.trans (Regs.Le.set _ hfr₁.unbound),
        hbelow.trans ((Regs.BelowEq.set _ (Nat.le_refl _)).mono g0A.nextVal),
        hfr₁.set _ (Nat.le_refl _), Regs.set_same .., hsim.trans ?_⟩
      exact simS_op (P := P) (f := f) (fn := sA.fn)
        (fn' := { { sA.fn with nextVal := sA.fn.nextVal + 1 } with
          cur := Instr.op [sA.fn.nextVal] op as :: sA.fn.cur }) hget hb rfl rfl rfl
    refine ⟨key, ?_, ?_⟩
    · intro fenv env R s₀ s₁ n ids joins hfe henv hfr hp hcompl hcp hlen htr
      obtain ⟨rfl, i, rfl, htrE⟩ := trExprN_nonCall_inv (by intro fn args'; simp) htr
      obtain ⟨v, rfl⟩ : ∃ v, rets = [v] := by
        cases rets with
        | nil => simp at hlen
        | cons v vs =>
          cases vs with
          | nil => exact ⟨v, rfl⟩
          | cons w ws => simp at hlen
      exact (key fenv env R s₀ s₁ i v joins hfe henv hfr hp hcompl hcp rfl htrE).toEOutL
    · intro hrets fenv env R lctx rs s₀ s₁ renv joins hfe henv huniq hfr _ hp hcompl hcp _ htr
      have htr0 := htr
      rw [trStmt] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      by_cases hop : isHaltingOp op = true
      · rw [if_pos hop] at htr
        obtain ⟨st', hbad⟩ := isHaltingOp_halts (model := model) hop hb
        rw [hrets] at hbad
        cases hbad
      · rw [if_neg hop] at htr
        obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
        obtain ⟨-, rfl⟩ := M.pure_inv h3
        have hg : Grows sA s₁ := Grows.of_emit h2
        exact sim_exprStmt_op hop henv huniq h1
          (iha fenv env R s₀ sA as joins hfe henv hfr hp
            (SGrowsAt.completes_of (SGrows.of_grows hg) hcompl)
            (curPlaced_back_grows hg hcp) h1)
          (hrets ▸ hb) htr0
  | @builtinHalt funs V st op args argvals st1 st2 hargs hb iha =>
    have key : ∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState)
        (i : ValId) (joins : List BlockId), FEnvOK (model := model) P funs fenv →
        EnvOK (model := model) env V R → RegsFresh R s₀.fn →
        ProtectedAt joins s₀.fn → Completes f s₁.fn joins → CurPlaced f s₁.fn →
        trExpr fenv env (.builtin op args) s₀ = some (i, s₁) →
        EOutHalt (model := model) P f s₀ R st st2 := by
      intro fenv env R s₀ s₁ i joins hfe henv hfr hp hcompl hcp htr
      rw [trExpr] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      obtain ⟨d, sB, h2, htr⟩ := M.bind_inv htr
      obtain ⟨u, sC, h3, h4⟩ := M.bind_inv htr
      obtain ⟨rfl, rfl⟩ := M.pure_inv h4
      rw [M.freshVal_apply] at h2
      obtain ⟨rfl, rfl⟩ := M.some_pair_inj h2
      rw [M.emit_apply] at h3
      obtain ⟨-, rfl⟩ := M.some_pair_inj h3
      have hg : Grows sA
          { sA with fn := { { sA.fn with nextVal := sA.fn.nextVal + 1 } with
            cur := Instr.op [sA.fn.nextVal] op as :: sA.fn.cur } } :=
        (Grows.of_freshVal rfl).trans (Grows.of_emit rfl)
      obtain ⟨R₁, -, -, -, hget, hsim⟩ :=
        iha fenv env R s₀ sA as joins hfe henv hfr hp
        (SGrowsAt.completes_of (SGrows.of_grows hg) hcompl)
        (curPlaced_back_grows hg hcp) h1
      obtain ⟨rest, hcur⟩ := hcp
      exact hsim (.halt st2) (execFrom_opHalt hcur hget hb)
    refine ⟨key, ?_, ?_⟩
    · intro fenv env R s₀ s₁ n ids joins hfe henv hfr hp hcompl hcp htr
      obtain ⟨-, i, -, htrE⟩ := trExprN_nonCall_inv (by intro fn args'; simp) htr
      exact key fenv env R s₀ s₁ i joins hfe henv hfr hp hcompl hcp htrE
    · intro fenv env R lctx rs s₀ s₁ renv joins hfe henv _huniq hfr _ hp hcompl hcp hfin htr
      have htr0 := htr
      rw [trStmt] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      by_cases hop : isHaltingOp op = true
      · rw [if_pos hop] at htr
        obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
        obtain ⟨hrenv, rfl⟩ := M.pure_inv h3
        have hfinal : CurFinal f s₁.fn := hfin hrenv
        have hcpA : CurPlaced f sA.fn :=
          ⟨⟨[], .halt op as⟩, curOK_of_sealCur hfinal h2⟩
        exact sim_exprStmt_halt hop hfinal h1
          (iha fenv env R s₀ sA as joins hfe henv hfr hp
            (SGrowsAt.completes_of (SGrowsAt.of_sealCur h2) hcompl) hcpA h1)
          hb htr0
      · rw [if_neg hop] at htr
        obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
        have hemit := h2
        rw [M.emit_apply] at h2
        obtain ⟨-, hsB⟩ := M.some_pair_inj h2
        subst hsB
        obtain ⟨hrenv, rfl⟩ := M.pure_inv h3
        subst renv
        have hg := Grows.of_emit hemit
        obtain ⟨R₁, -, -, -, hget, hsim⟩ :=
          iha fenv env R s₀ sA as joins hfe henv hfr hp
            (SGrowsAt.completes_of (SGrows.of_grows hg) hcompl)
            (curPlaced_back_grows hg hcp) h1
        obtain ⟨rest, hcur⟩ := hcp
        exact hsim (.halt st2) (execFrom_opHalt hcur hget hb)
  | @builtinArgsHalt funs V st op args st1 hargs iha =>
    have key : ∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState)
        (i : ValId) (joins : List BlockId), FEnvOK (model := model) P funs fenv →
        EnvOK (model := model) env V R → RegsFresh R s₀.fn →
        ProtectedAt joins s₀.fn → Completes f s₁.fn joins → CurPlaced f s₁.fn →
        trExpr fenv env (.builtin op args) s₀ = some (i, s₁) →
        EOutHalt (model := model) P f s₀ R st st1 := by
      intro fenv env R s₀ s₁ i joins hfe henv hfr hp hcompl hcp htr
      rw [trExpr] at htr
      obtain ⟨as, sA, h1, htr'⟩ := M.bind_inv htr
      obtain ⟨d, sB, h2, htr''⟩ := M.bind_inv htr'
      obtain ⟨u, sC, h3, h4⟩ := M.bind_inv htr''
      obtain ⟨-, rfl⟩ := M.pure_inv h4
      have hg1 : Grows sA s₁ := (Grows.of_freshVal h2).trans (Grows.of_emit h3)
      exact iha fenv env R s₀ sA as joins hfe henv hfr hp
        (SGrowsAt.completes_of (SGrows.of_grows hg1) hcompl)
        (curPlaced_back_grows hg1 hcp) h1
    refine ⟨key, ?_, ?_⟩
    · intro fenv env R s₀ s₁ n ids joins hfe henv hfr hp hcompl hcp htr
      obtain ⟨-, i, -, htrE⟩ := trExprN_nonCall_inv (by intro fn args'; simp) htr
      exact key fenv env R s₀ s₁ i joins hfe henv hfr hp hcompl hcp htrE
    · intro fenv env R lctx rs s₀ s₁ renv joins hfe henv _huniq hfr _ hp hcompl hcp hfin htr
      rw [trStmt] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      by_cases hop : isHaltingOp op = true
      · rw [if_pos hop] at htr
        obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
        obtain ⟨hrenv, rfl⟩ := M.pure_inv h3
        have hfinal : CurFinal f s₁.fn := hfin hrenv
        have hcpA : CurPlaced f sA.fn :=
          ⟨⟨[], .halt op as⟩, curOK_of_sealCur hfinal h2⟩
        exact SOut.ofExprHalt
          (iha fenv env R s₀ sA as joins hfe henv hfr hp
            (SGrowsAt.completes_of (SGrowsAt.of_sealCur h2) hcompl) hcpA h1)
      · rw [if_neg hop] at htr
        obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
        obtain ⟨-, rfl⟩ := M.pure_inv h3
        have hg : Grows sA s₁ := Grows.of_emit h2
        exact SOut.ofExprHalt
          (iha fenv env R s₀ sA as joins hfe henv hfr hp
            (SGrowsAt.completes_of (SGrows.of_grows hg) hcompl)
            (curPlaced_back_grows hg hcp) h1)
  -- Blocked on a callee-construction bridge: inverting `FuncOK`/`trFunc` must
  -- provide `Completes`/entry placement for the generated callee and relate
  -- its parameter/zero-return register initialization to the source call env.
  | callOk hargs hlk harity hbody ho iha ihb => sorry
  | callHalt hargs hlk harity hbody iha ihb => sorry
  | @callArgsHalt funs V st fn args st1 hargs iha =>
    have key : ∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState)
        (i : ValId) (joins : List BlockId), FEnvOK (model := model) P funs fenv →
        EnvOK (model := model) env V R → RegsFresh R s₀.fn →
        ProtectedAt joins s₀.fn → Completes f s₁.fn joins → CurPlaced f s₁.fn →
        trExpr fenv env (.call fn args) s₀ = some (i, s₁) →
        EOutHalt (model := model) P f s₀ R st st1 := by
      intro fenv env R s₀ s₁ i joins hfe henv hfr hp hcompl hcp htr
      rw [trExpr] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      obtain ⟨fid, sB, h2, htr⟩ := M.bind_inv htr
      obtain ⟨d, sC, h3, htr⟩ := M.bind_inv htr
      obtain ⟨u, sD, h4, h5⟩ := M.bind_inv htr
      obtain ⟨-, rfl⟩ := M.pure_inv h5
      have hg : Grows sA s₁ := (Grows.of_liftO h2).trans
        ((Grows.of_freshVal h3).trans (Grows.of_emit h4))
      exact iha fenv env R s₀ sA as joins hfe henv hfr hp
        (SGrowsAt.completes_of (SGrows.of_grows hg) hcompl)
        (curPlaced_back_grows hg hcp) h1
    refine ⟨key, ?_, ?_⟩
    · intro fenv env R s₀ s₁ n ids joins hfe henv hfr hp hcompl hcp htr
      rw [trExprN] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      obtain ⟨fid, sB, h2, htr⟩ := M.bind_inv htr
      obtain ⟨ds, sC, h3, htr⟩ := M.bind_inv htr
      obtain ⟨u, sD, h4, h5⟩ := M.bind_inv htr
      obtain ⟨-, rfl⟩ := M.pure_inv h5
      have hg : Grows sA s₁ := (Grows.of_liftO h2).trans
        ((Grows.of_mapM_freshVal h3).trans (Grows.of_emit h4))
      exact iha fenv env R s₀ sA as joins hfe henv hfr hp
        (SGrowsAt.completes_of (SGrows.of_grows hg) hcompl)
        (curPlaced_back_grows hg hcp) h1
    · intro fenv env R lctx rs s₀ s₁ renv joins hfe henv _huniq hfr _ hp hcompl hcp _ htr
      rw [trStmt] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      obtain ⟨fid, sB, h2, htr⟩ := M.bind_inv htr
      obtain ⟨u, sC, h3, h4⟩ := M.bind_inv htr
      obtain ⟨-, rfl⟩ := M.pure_inv h4
      have hg : Grows sA s₁ := (Grows.of_liftO h2).trans (Grows.of_emit h3)
      exact SOut.ofExprHalt
        (iha fenv env R s₀ sA as joins hfe henv hfr hp
          (SGrowsAt.completes_of (SGrows.of_grows hg) hcompl)
          (curPlaced_back_grows hg hcp) h1)
  | @argsNil funs V st =>
    intro fenv env R s₀ s₁ ids _joins _ _ hfr _hp _ _ htr
    exact sim_args_nil hfr htr
  | @argsCons funs V st e rest restvals st1 v st2 hrest hhead ihr ihh =>
    intro fenv env R s₀ s₁ ids joins hfe henv hfr hp hcompl hcp htr
    rw [trArgs] at htr
    obtain ⟨restIds, sA, h1, htr'⟩ := M.bind_inv htr
    obtain ⟨i, s₁, h2, h3⟩ := M.bind_inv htr'
    obtain ⟨rfl, rfl⟩ := M.pure_inv h3
    have hgE : Grows sA s₁ := trExpr_grows e fenv env sA s₁ i h2
    have hcomplA : Completes f sA.fn joins :=
      SGrowsAt.completes_of (SGrows.of_grows hgE) hcompl
    have hcpA : CurPlaced f sA.fn := curPlaced_back_grows hgE hcp
    have hpA : ProtectedAt joins sA.fn :=
      ProtectedAt.forward hp (SGrows.of_grows
        (trArgs_grows rest fenv env s₀ sA restIds h1))
    refine sim_args_cons
      (ihr fenv env R s₀ sA restIds joins hfe henv hfr hp hcomplA hcpA h1)
      (trArgs_grows rest fenv env s₀ sA restIds h1).nextVal ?_
    intro R' hle hfrA
    exact (ihh.1 fenv env R' sA s₁ i v joins hfe (henv.mono hle) hfrA hpA
      hcompl hcp rfl h2)
  | @argsRestHalt funs V st e rest st1 hrest ihr =>
    intro fenv env R s₀ s₁ ids joins hfe henv hfr hp hcompl hcp htr
    rw [trArgs] at htr
    obtain ⟨restIds, sA, h1, htr'⟩ := M.bind_inv htr
    obtain ⟨i, s₁, h2, h3⟩ := M.bind_inv htr'
    obtain ⟨rfl, rfl⟩ := M.pure_inv h3
    have hgE : Grows sA s₁ := trExpr_grows e fenv env sA s₁ i h2
    exact ihr fenv env R s₀ sA restIds joins hfe henv hfr hp
      (SGrowsAt.completes_of (SGrows.of_grows hgE) hcompl)
      (curPlaced_back_grows hgE hcp) h1
  | @argsHeadHalt funs V st e rest restvals st1 st2 hrest hhead ihr ihh =>
    intro fenv env R s₀ s₁ ids joins hfe henv hfr hp hcompl hcp htr
    rw [trArgs] at htr
    obtain ⟨restIds, sA, h1, htr'⟩ := M.bind_inv htr
    obtain ⟨i, s₁, h2, h3⟩ := M.bind_inv htr'
    obtain ⟨rfl, rfl⟩ := M.pure_inv h3
    have hgE : Grows sA s₁ := trExpr_grows e fenv env sA s₁ i h2
    have hcomplA : Completes f sA.fn joins :=
      SGrowsAt.completes_of (SGrows.of_grows hgE) hcompl
    have hcpA : CurPlaced f sA.fn := curPlaced_back_grows hgE hcp
    have hpA : ProtectedAt joins sA.fn :=
      ProtectedAt.forward hp (SGrows.of_grows
        (trArgs_grows rest fenv env s₀ sA restIds h1))
    obtain ⟨R₁, hle, _hbelow, hfrA, hget, hsim⟩ :=
      ihr fenv env R s₀ sA restIds joins hfe henv hfr hp hcomplA hcpA h1
    exact hsim (.halt st2)
      (ihh.1 fenv env R₁ sA s₁ i joins hfe (henv.mono hle) hfrA hpA hcompl hcp h2)
  | @funDef funs V st n ps rs b =>
    intro fenv env R lctx rets s₀ s₁ renv _joins _ _ _ _ _ _ _ _ _
      _done _owned _hdone _hbound _hown htr
    rw [trStmt] at htr
    exact absurd htr (by simp [reject])
  -- **Blocked on a motive extension, not on a missing lemma.**  To invoke
  -- `ihb` this case must supply `FEnvOK P (hoist yulD body :: funs)
  -- (scope :: fenv)`, i.e. for every `(n, decl) ∈ hoist yulD body` paired with
  -- its `(n, fid) ∈ scope`, a `FuncOK P (scope :: fenv) decl fid` — whose first
  -- conjunct is `P.funcs[fid]? = some g`.
  --
  -- Everything on the *local* side is available: `allocScope body` reserves the
  -- slots, the `.funDef` step of `trStmts` runs `trFunc (scope :: fenv) …` and
  -- `fillFunc fid g`, and `FuncTableComplete.funcOK_of_contents` turns
  -- "`sLocal.funcs[fid]? = some (some g)` plus `FContents sLocal sDone` with
  -- `sDone.funcs = doneFuncs`" into exactly that `FuncOK`.
  --
  -- The single missing input is `FContents sLocal sDone`: `Motive` carries
  -- `doneFuncs` and `FuncTableComplete P doneFuncs` but **no relation at all**
  -- between `doneFuncs` and the builder states `s₀`/`s₁` a case is applied at.
  -- `FuncTableComplete doneFuncs` is deliberately a fact about one fixed
  -- completed table, so no derivation can bridge the two; the premise has to be
  -- threaded through the motive (a sixth invariant, alongside
  -- `Completes`/`CurPlaced`/`CurFinal`/`ProtectedAt`/`RegsFresh`).
  --
  -- Two costs make that a standalone round rather than a local patch:
  --   * every one of the ~40 already-proved cases of this induction must
  --     re-establish the new premise for each of its IHs (`FContents` transport
  --     across `Grows`/`SGrowsAt` handles most, but each call site changes);
  --   * the naive premise `FContents s₁ ⟨_, doneFuncs⟩` is *not* enough, for the
  --     reason spelled out at the `forLoop` hole below: with duplicate hoisted
  --     names both `FMap.get`s select the first reservation, `fillFunc`
  --     overwrites it, and the second reservation stays `none`, so
  --     `FContents.of_fillFunc_empty` does not apply.  The invariant must track
  --     the *pending reservation multiset* (`FOwned`) as well.
  | block hb ihb => sorry
  | @letZero funs V st vars =>
    intro fenv env R lctx rets s₀ s₁ renv _joins _ henv huniq hfr _ _hp _ _ _
      _done _owned _hdone _hbound _hown htr
    exact sim_letDecl_none hfr henv huniq htr
  | @letVal funs V st vars e vals st1 he hlen ihe =>
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq hfr _ hp hcompl hcp _
      _done _owned _hdone _hbound _hown htr
    have htr0 := htr
    rw [trStmt] at htr
    by_cases hgate : (vars.any env.mem || !decide vars.Nodup) = true
    · rw [if_pos hgate] at htr
      obtain ⟨u, sX, hx, -⟩ := M.bind_inv htr
      exact absurd hx (by simp [reject])
    rw [if_neg hgate] at htr
    obtain ⟨u, sX, hx, htr'⟩ := M.bind_inv htr
    obtain ⟨-, hsX⟩ := M.pure_inv hx
    rw [hsX] at htr'
    obtain ⟨ids, sA, h1, h2⟩ := M.bind_inv htr'
    obtain ⟨-, rfl⟩ := M.pure_inv h2
    exact sim_letDecl_some henv huniq hlen h1
      (ihe.2.1 fenv env R s₀ s₁ vars.length ids joins hfe henv hfr hp hcompl hcp hlen h1) htr0
  | @letHalt funs V st vars e st1 he ihe =>
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv _huniq hfr _ hp hcompl hcp _
      _done _owned _hdone _hbound _hown htr
    rw [trStmt] at htr
    by_cases hgate : (vars.any env.mem || !decide vars.Nodup) = true
    · rw [if_pos hgate] at htr
      obtain ⟨u, sX, hx, -⟩ := M.bind_inv htr
      exact absurd hx (by simp [reject])
    rw [if_neg hgate] at htr
    obtain ⟨u, sX, hx, htr'⟩ := M.bind_inv htr
    obtain ⟨-, hsX⟩ := M.pure_inv hx
    rw [hsX] at htr'
    obtain ⟨ids, sA, h1, h2⟩ := M.bind_inv htr'
    obtain ⟨-, rfl⟩ := M.pure_inv h2
    exact SOut.ofExprHalt
      (ihe.2.1 fenv env R s₀ s₁ vars.length ids joins hfe henv hfr hp hcompl hcp h1)
  | @assignVal funs V st vars e vals st1 he hlen ihe =>
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq hfr _ hp hcompl hcp _
      _done _owned _hdone _hbound _hown htr
    have htr0 := htr
    rw [trStmt] at htr
    by_cases hgate : (!vars.all env.mem) = true
    · rw [if_pos hgate] at htr
      obtain ⟨u, sX, hx, -⟩ := M.bind_inv htr
      exact absurd hx (by simp [reject])
    rw [if_neg hgate] at htr
    obtain ⟨u, sX, hx, htr'⟩ := M.bind_inv htr
    obtain ⟨-, hsX⟩ := M.pure_inv hx
    rw [hsX] at htr'
    obtain ⟨ids, sA, h1, h2⟩ := M.bind_inv htr'
    obtain ⟨-, rfl⟩ := M.pure_inv h2
    exact sim_assign henv huniq h1
      (ihe.2.1 fenv env R s₀ s₁ vars.length ids joins hfe henv hfr hp hcompl hcp hlen h1) htr0
  | @assignHalt funs V st vars e st1 he ihe =>
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv _huniq hfr _ hp hcompl hcp _
      _done _owned _hdone _hbound _hown htr
    rw [trStmt] at htr
    by_cases hgate : (!vars.all env.mem) = true
    · rw [if_pos hgate] at htr
      obtain ⟨u, sX, hx, -⟩ := M.bind_inv htr
      exact absurd hx (by simp [reject])
    rw [if_neg hgate] at htr
    obtain ⟨u, sX, hx, htr'⟩ := M.bind_inv htr
    obtain ⟨-, hsX⟩ := M.pure_inv hx
    rw [hsX] at htr'
    obtain ⟨ids, sA, h1, h2⟩ := M.bind_inv htr'
    obtain ⟨-, rfl⟩ := M.pure_inv h2
    exact SOut.ofExprHalt
      (ihe.2.1 fenv env R s₀ s₁ vars.length ids joins hfe henv hfr hp hcompl hcp h1)
  | exprStmt he ihe =>
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq hfr hvalid hp
      hcompl hcp hfin _done _owned _hdone _hbound _hown htr
    exact ihe.2.2 rfl fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq
      hfr hvalid hp hcompl hcp hfin htr
  | exprStmtHalt he ihe =>
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq hfr hvalid hp
      hcompl hcp hfin _done _owned _hdone _hbound _hown htr
    exact ihe.2.2 fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq
      hfr hvalid hp hcompl hcp hfin htr
  -- The selected-body path below now threads the reserved join through the
  -- protected `Completes` refinement, including the non-fresh move back to the
  -- join.  Its diverting (`bodyEnv = none`) half is fully discharged.  The
  -- fall-through half reaches the next independent invariant described at its
  -- remaining hole: preservation of pre-body unbound reserved parameter ids.
  | @ifTrue funs V st c body cv st1 V' st2 o hc hnz hbody ihc ihb =>
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq hfr hvalid hp
      hcompl hcp _ done owned hdone hbound hown htr
    rw [trStmt] at htr
    obtain ⟨cvId, sA, h1, htr⟩ := M.bind_inv htr
    obtain ⟨xvals, sB, h2, htr⟩ := M.bind_inv htr
    obtain ⟨bodyId, sC, h3, htr⟩ := M.bind_inv htr
    obtain ⟨joinParams, sD, h4, htr⟩ := M.bind_inv htr
    obtain ⟨joinId, sE, h5, htr⟩ := M.bind_inv htr
    obtain ⟨uF, sF, h6, htr⟩ := M.bind_inv htr
    obtain ⟨uG, sG, h7, htr⟩ := M.bind_inv htr
    obtain ⟨bodyEnv, sH, h8, htr⟩ := M.bind_inv htr
    have g0A : Grows s₀ sA := trExpr_grows c fenv env s₀ sA cvId h1
    have hvalidA : CurValid sA := hvalid.of_grows g0A
    have gAB : Grows sA sB := Grows.of_liftO h2
    have gCD : Grows sC sD := Grows.of_mapM_freshVal h4
    have aAB : SGrowsAt sA.fn.blocks.size sA sB := SGrowsAt.of_grows gAB
    have aAC := SGrowsAt.trans aAB
      (SGrowsAt.of_newBlock (N := sA.fn.blocks.size) h3)
    have aAD := SGrowsAt.trans aAC
      (SGrowsAt.of_grows (N := sA.fn.blocks.size) gCD)
    have aAE := SGrowsAt.trans aAD
      (SGrowsAt.of_newBlock (N := sA.fn.blocks.size) h5)
    have aAF := SGrowsAt.trans aAE
      (SGrowsAt.of_sealCur (N := sA.fn.blocks.size) h6)
    have hbodyBase : sA.fn.blocks.size ≤ bodyId := by
      rw [SGrowsAt.newBlock_id h3]
      exact aAB.size
    have hjoinBase : sA.fn.blocks.size ≤ joinId := by
      rw [SGrowsAt.newBlock_id h5]
      exact aAD.size
    have aAG := SGrowsAt.trans aAF
      (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hbodyBase) h7)
    have csAE : CurSame sA sE :=
      (((CurSame.of_grows gAB).trans (CurSame.of_newBlock h3)).trans
        (CurSame.of_grows gCD)).trans (CurSame.of_newBlock h5)
    have hbodyNe : sE.fn.curId ≠ bodyId := by
      rw [csAE.1, SGrowsAt.newBlock_id h3]
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hvalidA aAB.size)
    have hjoinBody : joinId ≠ bodyId := by
      rw [SGrowsAt.newBlock_id h5]
      exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (newBlock_target_lt h3)
        (SGrowsAt.of_grows (N := sC.fn.blocks.size) gCD).size)
    have hvalidG : CurValid sG := by
      apply CurValid.of_moveTo _ h7
      exact Nat.lt_of_lt_of_le (newBlock_target_lt h3)
        (((SGrowsAt.of_grows (N := sC.fn.blocks.size) gCD).trans
          (SGrowsAt.of_newBlock h5)).trans (SGrowsAt.of_sealCur h6)).size
    have gbody : SGrows sG sH :=
      trScope_grows fenv env lctx rets body sG bodyEnv sH h8
    have hpA : ProtectedAt joins sA.fn :=
      ProtectedAt.forward hp (SGrows.of_grows g0A)
    have hpG0 : ProtectedAt joins sG.fn :=
      ProtectedAt.forward hpA aAG
    have hpG : ProtectedAt (joinId :: joins) sG.fn := by
      refine ⟨?_, ?_⟩
      · intro i hi
        simp only [List.mem_cons] at hi
        rcases hi with rfl | hi
        · exact Nat.lt_of_lt_of_le (newBlock_target_lt h5)
            ((SGrowsAt.of_sealCur (N := 0) h6).trans
              (SGrowsAt.of_moveTo (N := 0)
                (Or.inl (Nat.zero_le _)) h7)).size
        · exact hpG0.below i hi
      · simp only [List.mem_cons, not_or]
        exact ⟨by
          rw [M.moveTo_apply] at h7
          have hc := congrArg (fun z => z.fn.curId) (M.some_pair_inj h7).2
          simpa only using hc ▸ hjoinBody.symm, hpG0.away⟩
    have hpH : ProtectedAt (joinId :: joins) sH.fn :=
      ProtectedAt.forward hpG gbody
    cases bodyEnv with
    | none =>
      obtain ⟨ua, sa, ha, htr⟩ := M.bind_inv htr
      obtain ⟨ub, sb, hb, hc'⟩ := M.bind_inv htr
      obtain ⟨-, hsa⟩ := M.pure_inv ha
      subst sa
      obtain ⟨hrenv, hs₁⟩ := M.pure_inv hc'
      subst sb
      have htail : SGrowsAt sA.fn.blocks.size sH s₁ :=
        SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hjoinBase) hb
      have hcomplH : Completes f sH.fn (joinId :: joins) :=
        Completes.of_moveTo_protected (by simp) hb (hcompl.protect joinId)
      have hcurH0 : sH.fn.cur = [] :=
        trScope_none_cur_nil fenv env lctx rets body sG sH h8
      have h8' : trStmt fenv env lctx rets (.block body) sG = some (none, sH) := by
        rw [trStmt]
        exact h8
      have hvalidH : CurValid sH :=
        (trStmt_cur hvalidG h8').1
      have hHjoin : sH.fn.curId ≠ joinId := fun he =>
        hpH.away (by simp [he])
      have hfinH : CurFinal f sH.fn :=
        curFinal_of_move_grows hb hHjoin hpH.away (SGrows.rfl' s₁)
          (hcompl.protect joinId)
      have hcpH : CurPlaced f sH.fn :=
        CurPlaced.of_moveTo_empty hvalidH hcurH0 hHjoin hb hpH.away
          (hcompl.protect joinId)
      have gCH : SGrowsAt 0 sC sH :=
        (((((SGrowsAt.of_grows gCD).trans (SGrowsAt.of_newBlock h5)).trans
          (SGrowsAt.of_sealCur h6)).trans
            (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h7)).trans
              (gbody.mono (Nat.zero_le _)))
      obtain ⟨bb, hbb, hbp⟩ := gCH.params bodyId ⟨[], [], .ret []⟩
        (newBlock_target_get h3)
      have hcurFE : sF.fn.curId = sE.fn.curId := (sealCur_cur h6).choose_spec.1
      have hfinalF : CurFinal f sF.fn :=
        curFinal_of_move_sgrowsAt (by rw [hcurFE, csAE.1]; exact hvalidA)
          h7 (by rw [hcurFE]; exact hbodyNe)
          (by rw [hcurFE, csAE.1]; exact hpA.away)
          (SGrowsAt.trans (gbody.mono aAG.size)
            htail) hcompl
      have hbranchE : CurOK f sE.fn
          ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨joinId, xvals⟩⟩ :=
        curOK_of_sealCur hfinalF h6
      have hcurAE : sE.fn.cur = sA.fn.cur := by
        have hBA : sB = sA := (M.edgeArgs_inv h2).2
        have hCB : sC.fn.cur = sB.fn.cur := by
          rw [M.newBlock_apply] at h3
          simpa using (congrArg (fun z => z.fn.cur) (M.some_pair_inj h3).2).symm
        have hDC : sD.fn.cur = sC.fn.cur := by
          obtain ⟨-, -, hsD⟩ := M.mapM_freshVal_length h4
          rw [hsD]
        have hED : sE.fn.cur = sD.fn.cur := by
          rw [M.newBlock_apply] at h5
          simpa using (congrArg (fun z => z.fn.cur) (M.some_pair_inj h5).2).symm
        rw [hED, hDC, hCB, hBA]
      have hbranch : CurOK f sA.fn
          ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨joinId, xvals⟩⟩ :=
        CurOK.back_of_cur_eq csAE.1 hcurAE hbranchE
      have hcpA : CurPlaced f sA.fn := ⟨_, hbranch⟩
      have hcomplA : Completes f sA.fn joins := SGrowsAt.completes_of
        (SGrowsAt.trans aAG (SGrowsAt.trans
          (gbody.mono aAG.size)
          htail)) hcompl
      obtain ⟨RA, hleA, hbelowA, hfrA, hcv, hsimC⟩ :=
        ihc.1 fenv env R s₀ sA cvId cv joins hfe henv hfr hp hcomplA hcpA rfl h1
      have hfrG : RegsFresh RA sG.fn := hfrA.mono aAG.nextVal
      have hnz' : cv ≠ 0 := by simpa only [yulD_zero] using hnz
      have hcurG : sG.fn.curId = bodyId := by
        rw [M.moveTo_apply] at h7
        exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h7).2).symm
      have hcurG0 : sG.fn.cur = [] := by
        rw [M.moveTo_apply] at h7
        simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h7).2
      have hsimB := simS_branchTrue_body (model := model) (P := P) (f := f)
        (st := st1)
        hcomplH hbranch hcv hnz' hbb hbp hcurG hcurG0
      have hboundG : ∀ i : FuncId, i ∈ owned → i < sG.funcs.size := by
        intro i hi
        exact Nat.lt_of_lt_of_le (hbound i hi)
          (Nat.le_trans (SGrows.of_grows g0A).funcsSize aAG.funcsSize)
      have hboundH : ∀ i : FuncId, i ∈ owned → i < sH.funcs.size := by
        intro i hi
        exact Nat.lt_of_lt_of_le (hboundG i hi) gbody.funcsSize
      have hownH : FOwned owned sH done :=
        FOwned.back_fprefix (FPrefix.of_moveTo hb) hboundH hown
      have hbodySim := ihb fenv env RA lctx rets sG sH none (joinId :: joins)
        hfe (henv.mono hleA) huniq hfrG hvalidG hpG hcomplH hcpH
        (fun _ => hfinH) done owned hdone hboundG hownH h8'
      have hpre := hsimC.trans hsimB
      have hnext : sH.fn.nextVal ≤ s₁.fn.nextVal := by
        rw [M.moveTo_apply] at hb
        rw [(congrArg (fun z => z.fn.nextVal) (M.some_pair_inj hb).2).symm]
      cases o with
      | normal =>
        obtain ⟨env', R', hbad, -⟩ := hbodySim
        exact absurd hbad (by simp)
      | halt =>
        exact SOut.prefix hleA hbelowA
          (Nat.le_trans g0A.nextVal aAG.nextVal) hpre
          (SOut.of_nonNormal (by simp) hnext hbodySim)
      | «break» =>
        exact SOut.prefix hleA hbelowA
          (Nat.le_trans g0A.nextVal aAG.nextVal) hpre
          (SOut.of_nonNormal (by simp) hnext hbodySim)
      | «continue» =>
        exact SOut.prefix hleA hbelowA
          (Nat.le_trans g0A.nextVal aAG.nextVal) hpre
          (SOut.of_nonNormal (by simp) hnext hbodySim)
      | leave =>
        exact SOut.prefix hleA hbelowA
          (Nat.le_trans g0A.nextVal aAG.nextVal) hpre
          (SOut.of_nonNormal (by simp) hnext hbodySim)
    | some envB =>
      obtain ⟨xvB, sI, h9, htr⟩ := M.bind_inv htr
      obtain ⟨uJ, sJ, h10, htr⟩ := M.bind_inv htr
      obtain ⟨uK, sK, h11, htr⟩ := M.bind_inv htr
      obtain ⟨hrenv, hs₁⟩ := M.pure_inv htr
      subst sK
      have gHI : Grows sH sI := Grows.of_liftO h9
      have aHJ : SGrowsAt sA.fn.blocks.size sH sJ :=
        SGrowsAt.trans (SGrowsAt.of_grows gHI)
          (SGrowsAt.of_sealCur (N := sA.fn.blocks.size) h10)
      have aHJlocal : SGrows sH sJ :=
        SGrowsAt.trans (SGrowsAt.of_grows gHI) (SGrowsAt.of_sealCur h10)
      have htail : SGrowsAt sA.fn.blocks.size sH s₁ :=
        SGrowsAt.trans aHJ
          (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hjoinBase) h11)
      have hcomplJ : Completes f sJ.fn (joinId :: joins) :=
        Completes.of_moveTo_protected (by simp) h11 (hcompl.protect joinId)
      have hcomplH : Completes f sH.fn (joinId :: joins) :=
        SGrowsAt.completes_of aHJlocal hcomplJ
      have h8' : trStmt fenv env lctx rets (.block body) sG = some (some envB, sH) := by
        rw [trStmt]
        exact h8
      have hvalidH : CurValid sH := (trStmt_cur hvalidG h8').1
      have hjoinH : sH.fn.curId ≠ joinId := fun he => hpH.away (by simp [he])
      have hcurIH : sI.fn.curId = sH.fn.curId := gHI.curId.symm
      have hjoinI : sI.fn.curId ≠ joinId := by simpa only [hcurIH] using hjoinH
      have hcurJI : sJ.fn.curId = sI.fn.curId := (sealCur_cur h10).choose_spec.1
      have hjoinJ : sJ.fn.curId ≠ joinId := by simpa only [hcurJI] using hjoinI
      have hpJ : ProtectedAt (joinId :: joins) sJ.fn :=
        ProtectedAt.forward hpH aHJlocal
      have hfinJ : CurFinal f sJ.fn :=
        curFinal_of_move_grows h11 hjoinJ hpJ.away (SGrows.rfl' s₁)
          (hcompl.protect joinId)
      have hsealI : CurOK f sI.fn ⟨[], .jump ⟨joinId, xvB⟩⟩ :=
        curOK_of_sealCur hfinJ h10
      have hcurHI : sI.fn.cur = sH.fn.cur := by
        obtain ⟨Δ, he⟩ := gHI.cur
        have hEq : sI = sH := (M.edgeArgs_inv h9).2
        simpa only [hEq]
      have hsealH : CurOK f sH.fn ⟨[], .jump ⟨joinId, xvB⟩⟩ :=
        CurOK.back_of_cur_eq gHI.curId.symm hcurHI hsealI
      have hcpH : CurPlaced f sH.fn := ⟨_, hsealH⟩
      have hcurAE : sE.fn.cur = sA.fn.cur := by
        have hBA : sB = sA := (M.edgeArgs_inv h2).2
        have hCB : sC.fn.cur = sB.fn.cur := by
          rw [M.newBlock_apply] at h3
          simpa using (congrArg (fun z => z.fn.cur) (M.some_pair_inj h3).2).symm
        have hDC : sD.fn.cur = sC.fn.cur := by
          obtain ⟨-, -, hsD⟩ := M.mapM_freshVal_length h4
          rw [hsD]
        have hED : sE.fn.cur = sD.fn.cur := by
          rw [M.newBlock_apply] at h5
          simpa using (congrArg (fun z => z.fn.cur) (M.some_pair_inj h5).2).symm
        rw [hED, hDC, hCB, hBA]
      have hbranchE : CurOK f sE.fn
          ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨joinId, xvals⟩⟩ := by
        have hcurFE : sF.fn.curId = sE.fn.curId := (sealCur_cur h6).choose_spec.1
        have hfinalF : CurFinal f sF.fn :=
          curFinal_of_move_sgrowsAt (by rw [hcurFE, csAE.1]; exact hvalidA)
            h7 (by rw [hcurFE]; exact hbodyNe)
            (by rw [hcurFE, csAE.1]; exact hpA.away)
            (SGrowsAt.trans (gbody.mono aAG.size) htail) hcompl
        exact curOK_of_sealCur hfinalF h6
      have hbranch : CurOK f sA.fn
          ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨joinId, xvals⟩⟩ :=
        CurOK.back_of_cur_eq csAE.1 hcurAE hbranchE
      have gCH : SGrowsAt 0 sC sH :=
        (((((SGrowsAt.of_grows gCD).trans (SGrowsAt.of_newBlock h5)).trans
          (SGrowsAt.of_sealCur h6)).trans
            (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h7)).trans
              (gbody.mono (Nat.zero_le _)))
      obtain ⟨bb, hbb, hbp⟩ := gCH.params bodyId ⟨[], [], .ret []⟩
        (newBlock_target_get h3)
      have hcomplA : Completes f sA.fn joins := SGrowsAt.completes_of
        (SGrowsAt.trans aAG (SGrowsAt.trans
          (gbody.mono aAG.size) htail)) hcompl
      have hcpA : CurPlaced f sA.fn := ⟨_, hbranch⟩
      obtain ⟨RA, hleA, hbelowA, hfrA, hcv, hsimC⟩ :=
        ihc.1 fenv env R s₀ sA cvId cv joins hfe henv hfr hp hcomplA hcpA rfl h1
      have hfrG : RegsFresh RA sG.fn := hfrA.mono aAG.nextVal
      have hnz' : cv ≠ 0 := by simpa only [yulD_zero] using hnz
      have hcurG : sG.fn.curId = bodyId := by
        rw [M.moveTo_apply] at h7
        exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h7).2).symm
      have hcurG0 : sG.fn.cur = [] := by
        rw [M.moveTo_apply] at h7
        simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h7).2
      have hsimB := simS_branchTrue_body (model := model) (P := P) (f := f)
        (st := st1) hcomplH hbranch hcv hnz' hbb hbp hcurG hcurG0
      have hboundG : ∀ i : FuncId, i ∈ owned → i < sG.funcs.size := by
        intro i hi
        exact Nat.lt_of_lt_of_le (hbound i hi)
          (Nat.le_trans (SGrows.of_grows g0A).funcsSize aAG.funcsSize)
      have hboundH : ∀ i : FuncId, i ∈ owned → i < sH.funcs.size := by
        intro i hi
        exact Nat.lt_of_lt_of_le (hboundG i hi) gbody.funcsSize
      have hownH : FOwned owned sH done := FOwned.back_fprefix
        (((FPrefix.of_edgeArgs h9).trans (FPrefix.of_sealCur h10)).trans
          (FPrefix.of_moveTo h11)) hboundH hown
      have hbodySim := ihb fenv env RA lctx rets sG sH (some envB)
        (joinId :: joins) hfe (henv.mono hleA) huniq hfrG hvalidG hpG
        hcomplH hcpH (by simp) done owned hdone hboundG hownH h8'
      have hpre := hsimC.trans hsimB
      cases o with
      | halt =>
        exact SOut.prefix hleA hbelowA
          (Nat.le_trans g0A.nextVal aAG.nextVal) hpre
          (SOut.of_nonNormal (by simp) htail.nextVal hbodySim)
      | «break» =>
        exact SOut.prefix hleA hbelowA
          (Nat.le_trans g0A.nextVal aAG.nextVal) hpre
          (SOut.of_nonNormal (by simp) htail.nextVal hbodySim)
      | «continue» =>
        exact SOut.prefix hleA hbelowA
          (Nat.le_trans g0A.nextVal aAG.nextVal) hpre
          (SOut.of_nonNormal (by simp) htail.nextVal hbodySim)
      | leave =>
        exact SOut.prefix hleA hbelowA
          (Nat.le_trans g0A.nextVal aAG.nextVal) hpre
          (SOut.of_nonNormal (by simp) htail.nextVal hbodySim)
      | normal =>
        obtain ⟨envB', RB, henvB', hleB, hbelowB, hfrB, henvB, huniqB,
          hsimBody⟩ := hbodySim
        obtain rfl : envB' = envB := (Option.some.inj henvB').symm
        obtain ⟨rfl, vals, hxget, hxvals⟩ := edgeArgs_ok henvB h9
        obtain ⟨hparamLen, hparamRange, hsD⟩ := M.mapM_freshVal_length h4
        have hnd : joinParams.Nodup := by
          rw [hparamRange]
          exact M.nodup_range' _ _
        have hfrC : RegsFresh RA sC.fn := hfrA.mono aAC.nextVal
        have aDG : SGrowsAt 0 sD sG :=
          (SGrowsAt.of_newBlock (N := 0) h5).trans
            ((SGrowsAt.of_sealCur (N := 0) h6).trans
              (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h7))
        have hparamsLt : ∀ i ∈ joinParams, i < sG.fn.nextVal := by
          intro i hi
          rw [hparamRange] at hi
          have hi' := (M.mem_range'_bounds hi).2
          have hiD : i < sD.fn.nextVal := by rw [hsD]; exact hi'
          exact Nat.lt_of_lt_of_le hiD aDG.nextVal
        have hnone : ∀ i ∈ joinParams, RB i = none := by
          intro i hi
          rw [hbelowB i (hparamsLt i hi)]
          exact hfrC i (by
            rw [hparamRange] at hi
            exact (M.mem_range'_bounds hi).1)
        have hleJ : Regs.Le RB (RB.setMany joinParams vals) :=
          Regs.Le.setMany hnd hnone
        have hbelowJ : Regs.BelowEq s₀.fn.nextVal RB
            (RB.setMany joinParams vals) := by
          apply Regs.BelowEq.setMany
          intro i hi
          rw [hparamRange] at hi
          exact Nat.le_trans g0A.nextVal
            (Nat.le_trans aAC.nextVal (M.mem_range'_bounds hi).1)
        have hfrJ : RegsFresh (RB.setMany joinParams vals) s₁.fn := by
          intro i hi
          rw [Regs.setMany_other]
          · exact hfrB i (Nat.le_trans htail.nextVal hi)
          · intro himem
            exact absurd (hparamsLt i himem)
              (Nat.not_lt_of_ge
                (Nat.le_trans (Nat.le_trans gbody.nextVal htail.nextVal) hi))
        have hnew := newBlock_target_get h5
        have hE1 : SGrowsAt sA.fn.blocks.size sE s₁ :=
          SGrowsAt.trans (SGrowsAt.of_sealCur (N := sA.fn.blocks.size) h6)
            (SGrowsAt.trans
              (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hbodyBase) h7)
              (SGrowsAt.trans (gbody.mono aAG.size) htail))
        obtain ⟨jb, hjb, hjp⟩ := hE1.params joinId
          ⟨joinParams, [], .ret []⟩ hnew
        have hcur : s₁.fn.curId = joinId := by
          rw [M.moveTo_apply] at h11
          exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h11).2).symm
        have hcur0 : s₁.fn.cur = [] := by
          rw [M.moveTo_apply] at h11
          simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h11).2
        have hjbLen : jb.params.length = vals.length := by
          rw [hjp, hparamLen]
          exact hxvals.length_eq
        have hsimJ : SimS (model := model) P f sI.fn RB st2 s₁.fn
            (RB.setMany joinParams vals) st2 := by
          have hs := simS_jump_join (model := model) (P := P) (f := f)
            (st := st2) hcompl hsealH hjb hcur hcur0 hxget hjbLen
          simpa only [hjp] using hs
        have hnames : VEnv.names V' = VEnv.names V := by
          have hm := (mod_sim hbody).1
          simpa [declsOfStmt] using hm
        have hmod : ModOut [] (modStmts [] body) V V' := by
          have hm := (mod_sim hbody).2 [] (localsOK_nil V)
          simpa [modStmt] using hm
        have hVjoin : YulSemantics.VEnv.setMany V
            (modifiedX env [body]) vals = V' :=
          setMany_eq_of_modOut henv huniq hnames hmod hxvals
            (fun x hx => modifiedX_mem_names hx)
            (fun x hx hm => mem_modifiedX hx (by simpa using hm))
        have hpget : (RB.setMany joinParams vals).getMany joinParams = some vals :=
          Regs.getMany_setMany_self hnd (by rw [hparamLen]; exact hxvals.length_eq)
        have henvJ : EnvOK (model := model)
            (env.setMany (modifiedX env [body]) joinParams) V'
            (RB.setMany joinParams vals) := by
          have he : EnvOK (model := model)
              (env.setMany (modifiedX env [body]) joinParams)
              (YulSemantics.VEnv.setMany V (modifiedX env [body]) vals)
              (RB.setMany joinParams vals) :=
            EnvOK.setMany (henv.mono (hleA.trans (hleB.trans hleJ)))
              (Regs.getMany_eq_some_iff.mp hpget)
          rwa [hVjoin] at he
        exact ⟨env.setMany (modifiedX env [body]) joinParams,
          RB.setMany joinParams vals, hrenv, hleA.trans (hleB.trans hleJ),
          (hbelowA.trans
            (hbelowB.mono (Nat.le_trans g0A.nextVal aAG.nextVal))).trans hbelowJ,
          hfrJ, henvJ, huniq.setMany _ _,
          hpre.trans (hsimBody.trans hsimJ)⟩
  | @ifFalse funs V st c body cv st1 hc hz ihc =>
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq hfr hvalid hp hcompl hcp _
      _done _owned _hdone _hbound _hown htr
    rw [trStmt] at htr
    obtain ⟨cvId, sA, h1, htr⟩ := M.bind_inv htr
    obtain ⟨xvals, sB, h2, htr⟩ := M.bind_inv htr
    obtain ⟨bodyId, sC, h3, htr⟩ := M.bind_inv htr
    obtain ⟨joinParams, sD, h4, htr⟩ := M.bind_inv htr
    obtain ⟨joinId, sE, h5, htr⟩ := M.bind_inv htr
    obtain ⟨uF, sF, h6, htr⟩ := M.bind_inv htr
    obtain ⟨uG, sG, h7, htr⟩ := M.bind_inv htr
    obtain ⟨bodyEnv, sH, h8, htr⟩ := M.bind_inv htr
    have g0A : Grows s₀ sA := trExpr_grows c fenv env s₀ sA cvId h1
    have hvalidA : CurValid sA := hvalid.of_grows g0A
    have gAB : Grows sA sB := Grows.of_liftO h2
    have gCD : Grows sC sD := Grows.of_mapM_freshVal h4
    have aAB : SGrowsAt sA.fn.blocks.size sA sB := SGrowsAt.of_grows gAB
    have aAC := SGrowsAt.trans aAB
      (SGrowsAt.of_newBlock (N := sA.fn.blocks.size) h3)
    have aAD := SGrowsAt.trans aAC
      (SGrowsAt.of_grows (N := sA.fn.blocks.size) gCD)
    have aAE := SGrowsAt.trans aAD
      (SGrowsAt.of_newBlock (N := sA.fn.blocks.size) h5)
    have hbodyBase : sA.fn.blocks.size ≤ bodyId := by
      rw [SGrowsAt.newBlock_id h3]
      exact aAB.size
    have hjoinBase : sA.fn.blocks.size ≤ joinId := by
      rw [SGrowsAt.newBlock_id h5]
      exact aAD.size
    have csAE : CurSame sA sE :=
      (((CurSame.of_grows gAB).trans (CurSame.of_newBlock h3)).trans
        (CurSame.of_grows gCD)).trans (CurSame.of_newBlock h5)
    have hbodyNe : sE.fn.curId ≠ bodyId := by
      rw [csAE.1, SGrowsAt.newBlock_id h3]
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hvalidA aAB.size)
    have gbody : SGrows sG sH :=
      trScope_grows fenv env lctx rets body sG bodyEnv sH h8
    have tailData : SGrowsAt sA.fn.blocks.size sG s₁
        ∧ s₁.fn.curId = joinId ∧ s₁.fn.cur = []
        ∧ renv = some (env.setMany (modifiedX env [body]) joinParams) := by
      cases bodyEnv with
      | none =>
        obtain ⟨ua, sa, ha, htr⟩ := M.bind_inv htr
        obtain ⟨ub, sb, hb, hc'⟩ := M.bind_inv htr
        obtain ⟨-, hsa⟩ := M.pure_inv ha
        obtain ⟨hrenv, hs₁⟩ := M.pure_inv hc'
        subst hsa
        subst hs₁
        refine ⟨SGrowsAt.trans (gbody.mono
          (Nat.le_trans aAE.size
            ((SGrowsAt.of_sealCur (N := sA.fn.blocks.size) h6).trans
              (SGrowsAt.of_moveTo (N := sA.fn.blocks.size)
                (Or.inl hbodyBase) h7)).size))
            (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hjoinBase) hb),
          ?_, ?_, hrenv⟩
        · rw [M.moveTo_apply] at hb
          exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj hb).2).symm
        · rw [M.moveTo_apply] at hb
          simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj hb).2
      | some env' =>
        obtain ⟨xv, sa, ha, htr⟩ := M.bind_inv htr
        obtain ⟨ub, sb, hb, htr⟩ := M.bind_inv htr
        obtain ⟨uc, sc, hc', hd⟩ := M.bind_inv htr
        obtain ⟨hrenv, hs₁⟩ := M.pure_inv hd
        subst hs₁
        have abase : sA.fn.blocks.size ≤ sG.fn.blocks.size := by
          exact (SGrowsAt.trans aAE
            (SGrowsAt.trans (SGrowsAt.of_sealCur (N := sA.fn.blocks.size) h6)
              (SGrowsAt.of_moveTo (N := sA.fn.blocks.size)
                (Or.inl hbodyBase) h7))).size
        refine ⟨SGrowsAt.trans
          (SGrowsAt.trans
            (SGrowsAt.trans (gbody.mono abase)
              (SGrowsAt.of_edgeArgs (N := sA.fn.blocks.size) ha))
            (SGrowsAt.of_sealCur (N := sA.fn.blocks.size) hb))
          (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hjoinBase) hc'),
          ?_, ?_, hrenv⟩
        · rw [M.moveTo_apply] at hc'
          exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj hc').2).symm
        · rw [M.moveTo_apply] at hc'
          simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj hc').2
    obtain ⟨gsuffix, hcur, hcur0, hrenv⟩ := tailData
    have hcurFE : sF.fn.curId = sE.fn.curId := (sealCur_cur h6).choose_spec.1
    have hfinalF : CurFinal f sF.fn :=
      curFinal_of_move_sgrowsAt (by rw [hcurFE, csAE.1]; exact hvalidA)
        h7 (by rw [hcurFE]; exact hbodyNe)
        (by rw [hcurFE, csAE.1]
            exact (ProtectedAt.forward hp (SGrows.of_grows g0A)).away)
        gsuffix hcompl
    have hbranchE : CurOK f sE.fn
        ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨joinId, xvals⟩⟩ :=
      curOK_of_sealCur hfinalF h6
    have hcurIdAE : sE.fn.curId = sA.fn.curId := csAE.1
    have hcurAE : sE.fn.cur = sA.fn.cur := by
      have hBA : sB = sA := (M.edgeArgs_inv h2).2
      have hCB : sC.fn.cur = sB.fn.cur := by
        rw [M.newBlock_apply] at h3
        simpa using (congrArg (fun z => z.fn.cur) (M.some_pair_inj h3).2).symm
      have hDC : sD.fn.cur = sC.fn.cur := by
        obtain ⟨-, -, hsD⟩ := M.mapM_freshVal_length h4
        rw [hsD]
      have hED : sE.fn.cur = sD.fn.cur := by
        rw [M.newBlock_apply] at h5
        simpa using (congrArg (fun z => z.fn.cur) (M.some_pair_inj h5).2).symm
      rw [hED, hDC, hCB, hBA]
    have hbranch : CurOK f sA.fn
        ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨joinId, xvals⟩⟩ :=
      CurOK.back_of_cur_eq hcurIdAE hcurAE hbranchE
    obtain ⟨RA, hleA, hbelowA, hfrA, hcv, hsimC⟩ :=
      ihc.1 fenv env R s₀ sA cvId cv joins hfe henv hfr hp
        (SGrowsAt.completes_of
          (SGrowsAt.trans aAE
            (SGrowsAt.trans (SGrowsAt.of_sealCur (N := sA.fn.blocks.size) h6)
              (SGrowsAt.trans
                (SGrowsAt.of_moveTo (N := sA.fn.blocks.size)
                  (Or.inl hbodyBase) h7) gsuffix))) hcompl)
        (csAE.placed_back ⟨_, hbranchE⟩) rfl h1
    obtain ⟨hsB, vals, hxget, hxvals⟩ := edgeArgs_ok (henv.mono hleA) h2
    have hparams := M.mapM_freshVal_length h4
    obtain ⟨hparamLen, hparamRange, hsD⟩ := hparams
    have hnd : joinParams.Nodup := by rw [hparamRange]; exact M.nodup_range' _ _
    have hfrC : RegsFresh RA sC.fn := hfrA.mono aAC.nextVal
    have hnone : ∀ i ∈ joinParams, RA i = none := by
      intro i hi
      rw [hparamRange] at hi
      exact hfrC i (M.mem_range'_bounds hi).1
    have hleJ : Regs.Le RA (RA.setMany joinParams vals) :=
      Regs.Le.setMany hnd hnone
    have hbelowJ : Regs.BelowEq sA.fn.nextVal RA
        (RA.setMany joinParams vals) := by
      apply Regs.BelowEq.setMany
      intro i hi
      rw [hparamRange] at hi
      exact Nat.le_trans aAC.nextVal (M.mem_range'_bounds hi).1
    have hD1 : SGrowsAt sA.fn.blocks.size sD s₁ :=
      SGrowsAt.trans (SGrowsAt.of_newBlock (N := sA.fn.blocks.size) h5)
        (SGrowsAt.trans (SGrowsAt.of_sealCur (N := sA.fn.blocks.size) h6)
          (SGrowsAt.trans
            (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hbodyBase) h7)
            gsuffix))
    have hnext : sC.fn.nextVal + (modifiedX env [body]).length ≤ s₁.fn.nextVal := by
      simpa [hsD] using hD1.nextVal
    have hfrJ : RegsFresh (RA.setMany joinParams vals) s₁.fn := by
      rw [hparamRange]
      exact hfrC.setMany hnext
    have hnew := newBlock_target_get h5
    have hE1 : SGrowsAt sA.fn.blocks.size sE s₁ :=
      SGrowsAt.trans (SGrowsAt.of_sealCur (N := sA.fn.blocks.size) h6)
        (SGrowsAt.trans
          (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hbodyBase) h7)
          gsuffix)
    obtain ⟨jb, hjb, hjp⟩ := hE1.params joinId
      ⟨joinParams, [], .ret []⟩ hnew
    have hvalsLen : (modifiedX env [body]).length = vals.length := hxvals.length_eq
    have hjbLen : jb.params.length = vals.length := by
      rw [hjp, hparamLen, hvalsLen]
    have hzero : RA cvId = some 0 := by
      rw [hz] at hcv
      simpa only [yulD_zero] using hcv
    have hsimJ : SimS (model := model) P f sA.fn RA st1 s₁.fn
        (RA.setMany joinParams vals) st1 := by
      have hs := simS_branchFalse_join (model := model) (P := P) (f := f)
        (st := st1) hcompl hbranch hzero hjb hcur hcur0 hxget hjbLen
      simpa only [hjp] using hs
    have henvJ : EnvOK (model := model)
        (env.setMany (modifiedX env [body]) joinParams) V
        (RA.setMany joinParams vals) := by
      have hpget : (RA.setMany joinParams vals).getMany joinParams = some vals :=
        Regs.getMany_setMany_self hnd (by rw [hparamLen]; exact hvalsLen)
      have he : EnvOK (model := model)
          (env.setMany (modifiedX env [body]) joinParams)
          (YulSemantics.VEnv.setMany V (modifiedX env [body]) vals)
          (RA.setMany joinParams vals) :=
        EnvOK.setMany (henv.mono (hleA.trans hleJ))
          (Regs.getMany_eq_some_iff.mp hpget)
      rw [VEnv.setMany_self hxvals] at he
      exact he
    exact ⟨env.setMany (modifiedX env [body]) joinParams,
      RA.setMany joinParams vals, hrenv, hleA.trans hleJ,
      hbelowA.trans (hbelowJ.mono g0A.nextVal), hfrJ, henvJ,
      huniq.setMany _ _, hsimC.trans hsimJ⟩
  | @ifHalt funs V st c body st1 hc ihc =>
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv _huniq hfr hvalid hp hcompl hcp _
      _done _owned _hdone _hbound _hown htr
    rw [trStmt] at htr
    obtain ⟨cv, sA, h1, htr⟩ := M.bind_inv htr
    obtain ⟨xvals, sB, h2, htr⟩ := M.bind_inv htr
    obtain ⟨bodyId, sC, h3, htr⟩ := M.bind_inv htr
    obtain ⟨joinParams, sD, h4, htr⟩ := M.bind_inv htr
    obtain ⟨joinId, sE, h5, htr⟩ := M.bind_inv htr
    obtain ⟨uF, sF, h6, htr⟩ := M.bind_inv htr
    obtain ⟨uG, sG, h7, htr⟩ := M.bind_inv htr
    obtain ⟨bodyEnv, sH, h8, htr⟩ := M.bind_inv htr
    have g0A : Grows s₀ sA := trExpr_grows c fenv env s₀ sA cv h1
    have hvalidA : CurValid sA := hvalid.of_grows g0A
    have gAB : Grows sA sB := Grows.of_liftO h2
    have gCD : Grows sC sD := Grows.of_mapM_freshVal h4
    have csAE : CurSame sA sE :=
      (((CurSame.of_grows gAB).trans (CurSame.of_newBlock h3)).trans
        (CurSame.of_grows gCD)).trans (CurSame.of_newBlock h5)
    have aAB : SGrowsAt sA.fn.blocks.size sA sB := SGrowsAt.of_grows gAB
    have aAC := SGrowsAt.trans aAB
      (SGrowsAt.of_newBlock (N := sA.fn.blocks.size) h3)
    have aAD := SGrowsAt.trans aAC (SGrowsAt.of_grows (N := sA.fn.blocks.size) gCD)
    have aAE := SGrowsAt.trans aAD
      (SGrowsAt.of_newBlock (N := sA.fn.blocks.size) h5)
    have aAF := SGrowsAt.trans aAE
      (SGrowsAt.of_sealCur (N := sA.fn.blocks.size) h6)
    have hbodyBase : sA.fn.blocks.size ≤ bodyId := by
      rw [SGrowsAt.newBlock_id h3]
      exact aAB.size
    have aAG := SGrowsAt.trans aAF
      (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hbodyBase) h7)
    have gbody : SGrows sG sH :=
      trScope_grows fenv env lctx rets body sG bodyEnv sH h8
    have hjoinBase : sA.fn.blocks.size ≤ joinId := by
      rw [SGrowsAt.newBlock_id h5]
      exact aAD.size
    have hbodyNe : sE.fn.curId ≠ bodyId := by
      rw [csAE.1, SGrowsAt.newBlock_id h3]
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hvalidA aAB.size)
    have gsuffix : SGrowsAt sA.fn.blocks.size sG s₁ := by
      cases bodyEnv with
      | none =>
        obtain ⟨ua, sa, ha, htr⟩ := M.bind_inv htr
        obtain ⟨ub, sb, hb, hc'⟩ := M.bind_inv htr
        obtain ⟨-, rfl⟩ := M.pure_inv ha
        obtain ⟨rfl, rfl⟩ := M.pure_inv hc'
        exact SGrowsAt.trans (gbody.mono aAG.size)
          (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hjoinBase) hb)
      | some env' =>
        obtain ⟨xv, sa, ha, htr⟩ := M.bind_inv htr
        obtain ⟨ub, sb, hb, htr⟩ := M.bind_inv htr
        obtain ⟨uc, sc, hc', hd⟩ := M.bind_inv htr
        obtain ⟨rfl, rfl⟩ := M.pure_inv hd
        exact SGrowsAt.trans (SGrowsAt.trans
          (SGrowsAt.trans (gbody.mono aAG.size)
            (SGrowsAt.of_edgeArgs (N := sA.fn.blocks.size) ha))
          (SGrowsAt.of_sealCur (N := sA.fn.blocks.size) hb))
            (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hjoinBase) hc')
    have hcurFE : sF.fn.curId = sE.fn.curId := (sealCur_cur h6).choose_spec.1
    have hfinalF : CurFinal f sF.fn :=
      curFinal_of_move_sgrowsAt (by rw [hcurFE, csAE.1]; exact hvalidA)
        h7 (by rw [hcurFE]; exact hbodyNe)
        (by rw [hcurFE, csAE.1]
            exact (ProtectedAt.forward hp (SGrows.of_grows g0A)).away)
        gsuffix hcompl
    have hcpE : CurPlaced f sE.fn :=
      ⟨⟨[], .branch cv ⟨bodyId, []⟩ ⟨joinId, xvals⟩⟩,
        curOK_of_sealCur hfinalF h6⟩
    have hcpA : CurPlaced f sA.fn := csAE.placed_back hcpE
    have hcomplA : Completes f sA.fn joins := SGrowsAt.completes_of
      (SGrowsAt.trans aAE
        (SGrowsAt.trans (SGrowsAt.of_sealCur (N := sA.fn.blocks.size) h6)
          (SGrowsAt.trans
            (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hbodyBase) h7)
            gsuffix))) hcompl
    exact SOut.ofExprHalt
      (ihc.1 fenv env R s₀ sA cv joins hfe henv hfr hp hcomplA hcpA h1)
  -- The dispatch chain is `trCases_sim`; `sim_switchExec` glues it to the
  -- scrutinee's `EOut` and to the reserved-join reconstruction.
  | switchExec hc hsel ihc ihs => exact sim_switchExec hsel ihc ihs
  | @switchHalt funs V st c cases dflt st1 hc ihc =>
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv _huniq hfr hvalid hp
      hcompl _hcp _ _done _owned _hdone _hbound _hown htr
    let X := modifiedX env (cases.map Prod.snd ++ dflt.toList)
    unfold trStmt at htr
    obtain ⟨sv, sA, h1, htr⟩ := M.bind_inv htr
    obtain ⟨joinParams, sB, h2, htr⟩ := M.bind_inv htr
    obtain ⟨joinId, sC, h3, htr⟩ := M.bind_inv htr
    obtain ⟨uD, sD, h4, htr⟩ := M.bind_inv htr
    obtain ⟨uE, sE, h5, h6⟩ := M.bind_inv htr
    obtain ⟨-, hs₁⟩ := M.pure_inv h6
    have hXE := congrArg (modifiedX env) (switchBodies_eq cases dflt)
    have h2X : X.mapM (fun _ => freshVal) sA = some (joinParams, sB) := by
      exact Eq.mp (congrArg
        (fun X' => X'.mapM (fun _ => freshVal) sA = some (joinParams, sB)) hXE) h2
    have h4X : trCases fenv env lctx rets sv X joinId cases dflt sC =
        some (uD, sD) := by
      exact Eq.mp (congrArg (fun X' =>
        trCases fenv env lctx rets sv X' joinId cases dflt sC = some (uD, sD)) hXE) h4
    have hcomplE : Completes f sE.fn joins := by simpa only [hs₁] using hcompl
    have g0A : Grows s₀ sA := trExpr_grows c fenv env s₀ sA sv h1
    have hvalidA : CurValid sA := hvalid.of_grows g0A
    have aAB : SGrowsAt sA.fn.blocks.size sA sB :=
      SGrowsAt.of_grows (Grows.of_mapM_freshVal h2X)
    have aAC := aAB.trans (SGrowsAt.of_newBlock h3)
    have csAC := (CurSame.of_grows (Grows.of_mapM_freshVal h2X)).trans
      (CurSame.of_newBlock h3)
    have hvalidC : CurValid sC := CurValid.of_same_sgrows hvalidA aAC csAC.1
    obtain ⟨hvalidD, hkCD⟩ := trCases_cur_closed fenv env lctx rets sv
      X joinId cases dflt sC sD uD hvalidC h4X
    have gCD := trCases_grows fenv env lctx rets sv X joinId cases dflt
      sv X joinId sC uD sD h4X
    have hjoinLt : joinId < sC.fn.blocks.size := newBlock_target_lt h3
    have hcurLtJoin : sC.fn.curId < joinId := by
      rw [csAC.1, SGrowsAt.newBlock_id h3]
      exact Nat.lt_of_lt_of_le hvalidA aAB.size
    have hjoinNeC : sC.fn.curId ≠ joinId := Nat.ne_of_lt hcurLtJoin
    have hjoinNeD : sD.fn.curId ≠ joinId := by
      intro heq
      rcases gCD.curId with heqC | hge
      · exact hjoinNeC (heqC ▸ heq)
      · exact Nat.not_lt_of_ge (heq ▸ hge) hjoinLt
    have hpA : ProtectedAt joins sA.fn :=
      ProtectedAt.forward hp (SGrows.of_grows g0A)
    have hpC : ProtectedAt joins sC.fn := ProtectedAt.forward hpA aAC
    have hpD : ProtectedAt joins sD.fn := ProtectedAt.forward hpC gCD
    have hcomplD : Completes f sD.fn (joinId :: joins) :=
      Completes.of_moveTo_protected (by simp) h5 (hcomplE.protect joinId)
    have hprotD : sD.fn.curId ∉ joinId :: joins := by
      simp only [List.mem_cons]
      exact fun h => h.elim hjoinNeD hpD.away
    have hcurD : sD.fn.cur = [] := trCases_cur_nil fenv env lctx rets sv
      X joinId cases dflt sC sD uD h4X
    have hcpD : CurPlaced f sD.fn := CurPlaced.of_moveTo_empty hvalidD hcurD
      hjoinNeD h5 hprotD (hcomplE.protect joinId)
    have hfinD : CurFinal f sD.fn := curFinal_of_move_grows h5 hjoinNeD
      hpD.away (SGrows.rfl' sE) hcomplE
    have hprotC : sC.fn.curId ∉ joinId :: joins := by
      simp only [List.mem_cons]
      exact fun h => h.elim hjoinNeC hpC.away
    have hcpC : CurPlaced f sC.fn :=
      curPlaced_back (renv := none) hkCD hprotC hcomplD (fun _ => hfinD) hcpD
    have hcpB : CurPlaced f sB.fn :=
      (CurSame.of_newBlock h3).placed_back hcpC
    have hcpA : CurPlaced f sA.fn :=
      curPlaced_back_grows (Grows.of_mapM_freshVal h2X) hcpB
    have hjoinBase : sA.fn.blocks.size ≤ joinId := by
      rw [SGrowsAt.newBlock_id h3]
      exact aAB.size
    have htail : SGrowsAt sA.fn.blocks.size sA sE :=
      aAC.trans ((gCD.mono aAC.size).trans
        (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hjoinBase) h5))
    have hcomplA : Completes f sA.fn joins := htail.completes_of hcomplE
    exact SOut.ofExprHalt
      (ihc.1 fenv env R s₀ sA sv joins hfe henv hfr hp hcomplA hcpA h1)
  -- The loop motive is `LOut`; the seven iteration constructors still need the
  -- same below-watermark preservation at header/exit/post parameter binds.
  -- More precisely, at the condition point the reserved post/exit blocks are
  -- not yet final, so `Completes f fn joins` is false unless `postId` and
  -- `exitId` are added to `joins`.  A loop-layout bridge must transfer that
  -- protected `Completes` backward across the non-fresh `moveTo postId` and
  -- `moveTo exitId` steps (using `Completes.of_moveTo_protected`); a single
  -- `SGrowsAt.completes_of` cannot compose those continuations.
  -- The two enclosing `for` rules additionally need the structural
  -- hoisted-scope bridge `allocScope init` ->
  -- `FEnvOK P (hoist yulD init :: funs) (scope :: fenv)`.  `FContents` and
  -- `FuncTableComplete.funcOK_of_contents` now provide the filled-slot
  -- transport itself.  The precise remaining piece is a sixth mutually
  -- threaded builder invariant which (1) recovers that each `FMap.get` used by
  -- the hoist walk names its own reserved `none` singleton, so
  -- `FContents.of_fillFunc_empty` applies, and (2) supplies the resulting
  -- local-end-state -> `doneFuncs` witness as a premise of the statement/loop
  -- motive.  `FuncTableComplete doneFuncs` alone deliberately has no relation
  -- to an arbitrary local builder state, so invoking `ihi` before that witness
  -- is threaded would be unsound.
  --
  -- Precise failed re-establishment (`seqCons`/`seqStop`, at a `funDef` head):
  -- a pointwise `FContents local doneFuncs` premise is insufficient to recover
  -- the required `local.funcs[fid]? = some none`.  With duplicate hoisted
  -- names, both `FMap.get`s select the first reservation; `fillFunc` overwrites
  -- it and the second reservation stays `none`.  `trScope` itself still
  -- succeeds, and the contradiction appears only when the enclosing completed
  -- build's `mapM id` rejects that leftover slot.  The sixth invariant must
  -- therefore thread the *pending reservation multiset* (equivalently, a
  -- none-slot budget) through `trFunc`/`trScope`/`trStmts`/`trStmt`/`trCases`:
  -- `allocFunc` adds one owned pending slot, each `fillFunc` consumes its own
  -- slot, closed nested translations preserve the caller's pending slots, and
  -- `FuncTableComplete` makes the final pending set empty.  Only that stronger
  -- invariant justifies `FContents.of_fillFunc_empty` and the initializer IH.
  --
  -- The mutual frame part of that plan is now discharged by
  -- `trFunc_fprefix`/`trFunc_prefix`, and `FOwned.back_fprefix` is the exact
  -- backward bridge for a nested function.  The remaining obstruction is now
  -- narrower and explicit: `Motive` has no `owned` parameter and therefore no
  -- premise carrying both `FOwned owned s₁ done` and
  -- `∀ i ∈ owned, i < s₀.funcs.size`.  Without that bound the bridge is
  -- false: an index in `owned` could denote a slot freshly allocated by the
  -- nested translation.  Threading this bounded ownership pair through the
  -- statement/list/loop clauses lets the `seqCons` funDef branch apply, in
  -- order, `FOwned.back_fillFunc`, `FOwned.back_fprefix`, and
  -- `FOwned.back_allocFunc`; only then can `forLoop` invoke the initializer IH
  -- with the hoisted `FEnvOK` scope.
  -- Precise remaining reconstruction goal.  After inverting `allocScope` and
  -- `trStmts`, the `some envI` arm ends in the *outer* pure
  --   `some ((envI.setMany X exitParams).drop
  --     ((envI.setMany X exitParams).length - env.length))`.
  -- `LOut`, however, consumes a `LoopLayout` whose identical four-way
  -- body/post tail ends in the *inner* pure
  --   `some (envI.setMany X exitParams)`.
  -- `LoopLayout.header_tail_sgrows`, `.curMoved`, and `.fprefix` now discharge
  -- all block-placement and ownership framing once that tail equation is
  -- reconstructed.  What remains is to invert the four `bodyEnv`/`postEnv`
  -- arms, replace only that final pure, and package the common `LoopLayout`;
  -- then `allocScope_motive_inputs` supplies every premise of `ihi`.
  | @forLoop funs V st init c post body Vinit stinit Vend stend o
      hinit hloop ihi ihl =>
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq hfr hvalid hp
      hcompl hcp hfin done owned hdone hbound hown htr
    obtain ⟨scope, sA, sI, rinit, ha, hi, htail⟩ := trStmt_forLoop_inv htr
    have hfnA : sA.fn = s₀.fn := (allocScope_funcsOnly ha).1
    have hvalidA : CurValid sA := by rw [CurValid, hfnA]; exact hvalid
    have hfrA : RegsFresh R sA.fn := by simpa only [hfnA] using hfr
    have hpA : ProtectedAt joins sA.fn := by simpa only [hfnA] using hp
    have gAI := trStmts_grows (scope :: fenv) env lctx rets false init
      sA rinit sI hi
    have hvalidI : CurValid sI :=
      (trStmts_cur (scope :: fenv) env lctx rets false init
        sA rinit sI hvalidA hi).1
    have hpI : ProtectedAt joins sI.fn := ProtectedAt.forward hpA gAI
    have hboundI : ∀ i : FuncId, i ∈ owned → i < sI.funcs.size := by
      intro i him
      exact Nat.lt_of_lt_of_le (hbound i him)
        (Nat.le_trans (allocScope_funcsOnly ha).2 gAI.funcsSize)
    cases rinit with
    | none =>
        obtain ⟨hrenv, hs₁⟩ := htail
        subst renv
        subst s₁
        obtain ⟨hfe', hbound', hslots, hnd, -⟩ :=
          allocScope_motive_inputs hfuncs hfe hdone hbound hown ha hi
        have hout := ihi (scope :: fenv) env R lctx rets sA sI none joins
          hfe' henv huniq hfrA hvalidA hpA hcompl hcp hfin
          done owned hdone hbound' hslots hnd hown hi
        obtain ⟨env', R', hbad, -⟩ := hout
        cases hbad
    | some envI =>
        obtain ⟨envX, ⟨layout⟩, hrenv⟩ := htail
        have hcomplI : Completes f sI.fn joins :=
          layout.sgrows.completes_of hcompl
        have hcpI : CurPlaced f sI.fn :=
          curPlaced_back (renv := some envX)
            (Or.inr (layout.curMoved hvalidI)) hpI.away hcompl
            (fun hbad => nomatch hbad) hcp
        have hownI : FOwned owned sI done :=
          FOwned.back_fprefix layout.fprefix hboundI hown
        obtain ⟨hfe', hbound', hslots, hnd, -⟩ :=
          allocScope_motive_inputs hfuncs hfe hdone hbound hownI ha hi
        have hinitOut := ihi (scope :: fenv) env R lctx rets
          sA sI (some envI) joins hfe' henv huniq hfrA hvalidA hpA
          hcomplI hcpI (fun hbad => nomatch hbad)
          done owned hdone hbound' hslots hnd hownI hi
        have hinner : SOut (model := model) P f lctx rets sA s₁ R
            (some envX) Vend st stend o := by
          apply SOut.seq gAI.nextVal hinitOut
          intro RI hleI hfrI henvI huniqI
          obtain ⟨RH, hbelowH, hfrH, henvH, hcleanH, hrebH, hsimH⟩ :=
            layout.enter henvI huniqI hfrI hvalidI hpI hcompl
          have hloopOut := ihl (scope :: fenv) envI rets sI s₁
            (some envX) joins layout hfe' huniqI hvalidI hpI hcompl hcp
            (fun hbad => nomatch hbad) done owned hdone hboundI hown
            RH henvH hfrH hcleanH hrebH
          have hbase : sI.fn.nextVal ≤ layout.sA.fn.nextVal := by
            rw [(M.edgeArgs_inv layout.h1).2]
          exact LHOut.prefix hbase hbelowH hfrI hsimH hloopOut
        subst renv
        rcases loop_outcome_ssa hloop with rfl | rfl | rfl
        · obtain ⟨envEnd, REnd, henvEnd, hleEnd, hbelowEnd, hfrEnd,
            henvOK, huniqEnd, hsimEnd⟩ := hinner
          obtain rfl : envX = envEnd := Option.some.inj henvEnd
          refine ⟨(envX.drop (envX.length - env.length)), REnd, rfl,
            hleEnd, ?_, hfrEnd, henvOK.restore henv.length,
            huniqEnd.drop _, ?_⟩
          · simpa only [hfnA] using hbelowEnd
          · simpa only [hfnA] using hsimEnd
        · change ExecFrom (model := model) P f s₀.fn R st (.halt stend)
          change ExecFrom (model := model) P f sA.fn R st (.halt stend) at hinner
          rwa [hfnA] at hinner
        · obtain ⟨rs, vals, hrs, hvals, hex⟩ := hinner
          refine ⟨rs, vals, hrs, ?_, ?_⟩
          · -- Blocked: the generalized motive has no premise saying that
            -- `rets` names belong to the outer environment `V`.  `hvals` is
            -- over `Vend`, but this goal is over the initializer-scope drop.
            -- A local initializer may legally declare a fresh name appearing
            -- in an arbitrary `rets`, so this implication is false without a
            -- context-validity premise.
            show List.Forall₂
              (fun x v => YulSemantics.VEnv.get
                (YulSemantics.restore V Vend) x = some v) rs vals
            sorry
          · simpa only [hfnA] using hex
  | @forInitHalt funs V st init c post body Vinit stinit hinit ihi =>
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq hfr hvalid hp
      hcompl hcp hfin done owned hdone hbound hown htr
    obtain ⟨scope, sA, sI, rinit, ha, hi, htail⟩ := trStmt_forLoop_inv htr
    have hfnA : sA.fn = s₀.fn := (allocScope_funcsOnly ha).1
    have hvalidA : CurValid sA := by rw [CurValid, hfnA]; exact hvalid
    have hfrA : RegsFresh R sA.fn := by simpa only [hfnA] using hfr
    have hpA : ProtectedAt joins sA.fn := by simpa only [hfnA] using hp
    have gAI := trStmts_grows (scope :: fenv) env lctx rets false init
      sA rinit sI hi
    have hvalidI : CurValid sI :=
      (trStmts_cur (scope :: fenv) env lctx rets false init
        sA rinit sI hvalidA hi).1
    have hpI : ProtectedAt joins sI.fn := ProtectedAt.forward hpA gAI
    have hboundI : ∀ i : FuncId, i ∈ owned → i < sI.funcs.size := by
      intro i him
      exact Nat.lt_of_lt_of_le (hbound i him)
        (Nat.le_trans (allocScope_funcsOnly ha).2 gAI.funcsSize)
    cases rinit with
    | none =>
        obtain ⟨hrenv, hs₁⟩ := htail
        subst renv
        subst s₁
        obtain ⟨hfe', hbound', hslots, hnd, -⟩ :=
          allocScope_motive_inputs hfuncs hfe hdone hbound hown ha hi
        have hout := ihi (scope :: fenv) env R lctx rets sA sI none joins
          hfe' henv huniq hfrA hvalidA hpA hcompl hcp hfin
          done owned hdone hbound' hslots hnd hown hi
        change ExecFrom (model := model) P f s₀.fn R st (.halt stinit)
        change ExecFrom (model := model) P f sA.fn R st (.halt stinit) at hout
        rwa [hfnA] at hout
    | some envI =>
        obtain ⟨envX, ⟨layout⟩, hrenv⟩ := htail
        have hcomplI : Completes f sI.fn joins :=
          layout.sgrows.completes_of hcompl
        have hcpI : CurPlaced f sI.fn :=
          curPlaced_back (renv := some envX)
            (Or.inr (layout.curMoved hvalidI)) hpI.away hcompl
            (fun hbad => nomatch hbad) hcp
        have hownI : FOwned owned sI done :=
          FOwned.back_fprefix layout.fprefix hboundI hown
        obtain ⟨hfe', hbound', hslots, hnd, -⟩ :=
          allocScope_motive_inputs hfuncs hfe hdone hbound hownI ha hi
        have hout := ihi (scope :: fenv) env R lctx rets sA sI (some envI) joins
          hfe' henv huniq hfrA hvalidA hpA hcomplI hcpI
          (fun hbad => nomatch hbad) done owned hdone hbound' hslots hnd hownI hi
        change ExecFrom (model := model) P f s₀.fn R st (.halt stinit)
        change ExecFrom (model := model) P f sA.fn R st (.halt stinit) at hout
        rwa [hfnA] at hout
  | @«break» funs V st =>
    intro fenv env R lctx rets s₀ s₁ renv _joins _ henv _huniq hfr _ _hp _ _ hfin
      _done _owned _hdone _hbound _hown htr
    cases lctx with
    | none => rw [trStmt] at htr; exact absurd htr (by simp [reject])
    | some l =>
      have hnone : renv = none := by
        rw [trStmt] at htr
        obtain ⟨vals, sA, h1, htr⟩ := M.bind_inv htr
        obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
        exact (M.pure_inv h3).1
      exact sim_break henv
        (hfr.mono (trStmt_grows fenv env (some l) rets .break s₀ renv s₁ htr).nextVal)
        (hfin hnone) htr
  | @«continue» funs V st =>
    intro fenv env R lctx rets s₀ s₁ renv _joins _ henv _huniq hfr _ _hp _ _ hfin
      _done _owned _hdone _hbound _hown htr
    cases lctx with
    | none => rw [trStmt] at htr; exact absurd htr (by simp [reject])
    | some l =>
      have hnone : renv = none := by
        rw [trStmt] at htr
        obtain ⟨vals, sA, h1, htr⟩ := M.bind_inv htr
        obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
        exact (M.pure_inv h3).1
      exact sim_continue henv
        (hfr.mono (trStmt_grows fenv env (some l) rets .continue s₀ renv s₁ htr).nextVal)
        (hfin hnone) htr
  | @leave funs V st =>
    intro fenv env R lctx rets s₀ s₁ renv _joins _ henv _huniq hfr _ _hp _ _ hfin
      _done _owned _hdone _hbound _hown htr
    cases rets with
    | none => rw [trStmt] at htr; exact absurd htr (by simp [reject])
    | some rs =>
      have hnone : renv = none := by
        rw [trStmt] at htr
        obtain ⟨vals, sA, h1, htr⟩ := M.bind_inv htr
        obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
        exact (M.pure_inv h3).1
      exact sim_leave henv (hfin hnone) htr
  | @seqNil funs V st =>
    intro fenv env R lctx rets s₀ s₁ renv _joins _ henv huniq hfr _ _hp _ _ _
      _done _owned _hdone _hbound _hslots _hnd _hown htr
    exact sim_seqNil henv huniq hfr htr
  | @seqCons funs V st s rest V1 st1 V2 st2 o h1 h2 ih1 ih2 =>
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq hfr hvalid hp hcompl hcp hfin
      done owned hdone hbound hslots hnd hown htr
    cases s with
    | funDef n ps rs body =>
      cases h1
      rw [trStmts] at htr
      obtain ⟨fid, sA, ha, htr⟩ := M.bind_inv htr
      obtain ⟨g, sB, hb, htr⟩ := M.bind_inv htr
      obtain ⟨u, sC, hc, htail⟩ := M.bind_inv htr
      obtain ⟨hget, hsA⟩ := M.liftO_inv ha
      subst sA
      simp only [stmtFuncIds, hget, Option.toList_some,
        List.singleton_append] at hbound hslots hnd
      have hpFunc := trFunc_prefix fenv ps rs body hb
      have hfid0 : s₀.funcs[fid]? = some none := hslots fid (by simp)
      have hfidB : sB.funcs[fid]? = some none := by
        rw [hpFunc fid (lt_size_of_getElem? hfid0)]
        exact hfid0
      obtain ⟨hfidLt, hsC⟩ := M.fillFunc_inv hc
      have hndTail : (stmtFuncIds fenv rest ++ owned).Nodup :=
        (List.nodup_cons.mp hnd).2
      have hfidNot : fid ∉ stmtFuncIds fenv rest ++ owned :=
        (List.nodup_cons.mp hnd).1
      have hslotsTail : ∀ i : FuncId, i ∈ stmtFuncIds fenv rest →
          sC.funcs[i]? = some none := by
        intro i hi
        have hi0 := hslots i (by simp [hi])
        have hiB : sB.funcs[i]? = some none := by
          rw [hpFunc i (lt_size_of_getElem? hi0)]
          exact hi0
        have hine : i ≠ fid := by
          intro he
          subst i
          exact hfidNot (List.mem_append_left _ hi)
        rw [hsC, Array.getElem?_set (h := hfidLt), if_neg (Ne.symm hine)]
        exact hiB
      have hboundTail : ∀ i : FuncId,
          i ∈ stmtFuncIds fenv rest ++ owned → i < sC.funcs.size := by
        intro i hi
        have hi0 := hbound i (by simp [hi])
        rw [hsC]
        simpa using Nat.lt_of_lt_of_le hi0 (hpFunc.size (Nat.le_refl _))
      have hfnB : sB.fn = s₀.fn := (trFunc_grows fenv ps rs body s₀ g sB hb).1
      have hfnC : sC.fn = sB.fn := by rw [(M.fillFunc_inv hc).choose_spec]
      have hfn : sC.fn = s₀.fn := hfnC.trans hfnB
      have hvalidC : CurValid sC := by rw [CurValid, hfn]; exact hvalid
      have hpC : ProtectedAt joins sC.fn := by simpa only [hfn] using hp
      simpa only [SOut, hfn] using
        (ih2 fenv env R lctx rets sC s₁ renv joins hfe henv
          huniq (by simpa only [hfn] using hfr) hvalidC
          hpC hcompl hcp hfin done owned hdone hboundTail hslotsTail
          hndTail hown htail)
    | block body | letDecl vars val | assign vars e | cond e body
    | forLoop init e post body | «break» | «continue» | leave
    | switch e cases dflt | exprStmt e =>
      simp only [stmtFuncIds] at hbound hslots hnd
      obtain ⟨renvA, sA, hhead, htail⟩ := trStmts_false_cons_inv
        (by intros; simp) htr
      have hvalidA : CurValid sA := (trStmt_cur hvalid hhead).1
      have hgHead : SGrows s₀ sA :=
        trStmt_grows fenv env lctx rets _ s₀ renvA sA hhead
      have hpA : ProtectedAt joins sA.fn := ProtectedAt.forward hp hgHead
      have hpHead := trStmt_fprefix fenv env lctx rets _ s₀.funcs.size
        s₀ renvA sA (Nat.le_refl _) hhead
      have hboundA : ∀ i : FuncId,
          i ∈ stmtFuncIds fenv rest ++ owned → i < sA.funcs.size := by
        intro i hi
        exact Nat.lt_of_lt_of_le (hbound i hi) (hpHead.size (Nat.le_refl _))
      have hslotsA : ∀ i : FuncId, i ∈ stmtFuncIds fenv rest →
          sA.funcs[i]? = some none := by
        intro i hi
        rw [hpHead i (hbound i (List.mem_append_left _ hi))]
        exact hslots i hi
      cases renvA with
      | none =>
        obtain ⟨hrenv, hfn⟩ := trStmts_true_fn fenv env lctx rets rest sA s₁ renv htail
        have hcomplA : Completes f sA.fn joins := by simpa only [hfn] using hcompl
        have hcpA : CurPlaced f sA.fn := by simpa only [hfn] using hcp
        have hfinA : CurFinal f sA.fn := by
          simpa only [hfn] using hfin hrenv
        have hownA := trStmts_owned_back fenv lctx rets rest env true
          sA s₁ done renv owned hboundA hslotsA hnd hown htail
        obtain ⟨envA, R₁, hbad, -⟩ :=
          ih1 fenv env R lctx rets s₀ sA none joins hfe henv huniq hfr hvalid hp
            hcomplA hcpA
            (fun _ => hfinA) done (stmtFuncIds fenv rest ++ owned) hdone
            hbound hownA hhead
        exact absurd hbad (by simp)
      | some envA =>
        have hgTail : SGrows sA s₁ :=
          trStmts_grows fenv envA lctx rets false rest sA renv s₁ htail
        have hcomplA : Completes f sA.fn joins := SGrowsAt.completes_of hgTail hcompl
        have hcpA : CurPlaced f sA.fn :=
          trStmts_curPlaced_back hvalidA hpA hcompl hcp hfin htail
        have hownA := trStmts_owned_back fenv lctx rets rest envA false
          sA s₁ done renv owned hboundA hslotsA hnd hown htail
        refine SOut.seq hgHead.nextVal
          (ih1 fenv env R lctx rets s₀ sA (some envA) joins hfe henv huniq hfr
            hvalid hp hcomplA hcpA
            (by simp) done (stmtFuncIds fenv rest ++ owned) hdone hbound
            hownA hhead) ?_
        intro R₁ hle hfrA henvA huniqA
        exact ih2 fenv envA R₁ lctx rets sA s₁ renv joins hfe henvA huniqA hfrA
          hvalidA hpA hcompl hcp hfin done owned hdone hboundA hslotsA hnd
          hown htail
  | @seqStop funs V st s rest V1 st1 o h1 hne ih1 =>
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq hfr hvalid hp hcompl hcp hfin
      done owned hdone hbound hslots hnd hown htr
    cases s with
    | funDef n ps rs body =>
      cases h1
      exact absurd rfl hne
    | block body | letDecl vars val | assign vars e | cond e body
    | forLoop init e post body | «break» | «continue» | leave
    | switch e cases dflt | exprStmt e =>
      simp only [stmtFuncIds] at hbound hslots hnd
      obtain ⟨renvA, sA, hhead, htail⟩ := trStmts_false_cons_inv
        (by intros; simp) htr
      have hvalidA : CurValid sA := (trStmt_cur hvalid hhead).1
      have hgHead : SGrows s₀ sA :=
        trStmt_grows fenv env lctx rets _ s₀ renvA sA hhead
      have hpA : ProtectedAt joins sA.fn := ProtectedAt.forward hp hgHead
      have hpHead := trStmt_fprefix fenv env lctx rets _ s₀.funcs.size
        s₀ renvA sA (Nat.le_refl _) hhead
      have hboundA : ∀ i : FuncId,
          i ∈ stmtFuncIds fenv rest ++ owned → i < sA.funcs.size := by
        intro i hi
        exact Nat.lt_of_lt_of_le (hbound i hi) (hpHead.size (Nat.le_refl _))
      have hslotsA : ∀ i : FuncId, i ∈ stmtFuncIds fenv rest →
          sA.funcs[i]? = some none := by
        intro i hi
        rw [hpHead i (hbound i (List.mem_append_left _ hi))]
        exact hslots i hi
      cases renvA with
      | none =>
        obtain ⟨hrenv, hfn⟩ := trStmts_true_fn fenv env lctx rets rest sA s₁ renv htail
        have hcomplA : Completes f sA.fn joins := by simpa only [hfn] using hcompl
        have hcpA : CurPlaced f sA.fn := by simpa only [hfn] using hcp
        have hfinA : CurFinal f sA.fn := by simpa only [hfn] using hfin hrenv
        have hownA := trStmts_owned_back fenv lctx rets rest env true
          sA s₁ done renv owned hboundA hslotsA hnd hown htail
        exact SOut.of_nonNormal hne (by rw [hfn])
          (ih1 fenv env R lctx rets s₀ sA none joins hfe henv huniq hfr hvalid hp
            hcomplA hcpA
            (fun _ => hfinA) done (stmtFuncIds fenv rest ++ owned) hdone
            hbound hownA hhead)
      | some envA =>
        have hgTail : SGrows sA s₁ :=
          trStmts_grows fenv envA lctx rets false rest sA renv s₁ htail
        have hcomplA : Completes f sA.fn joins := SGrowsAt.completes_of hgTail hcompl
        have hcpA : CurPlaced f sA.fn :=
          trStmts_curPlaced_back hvalidA hpA hcompl hcp hfin htail
        have hownA := trStmts_owned_back fenv lctx rets rest envA false
          sA s₁ done renv owned hboundA hslotsA hnd hown htail
        exact SOut.of_nonNormal hne hgTail.nextVal
          (ih1 fenv env R lctx rets s₀ sA (some envA) joins hfe henv huniq hfr
            hvalid hp hcomplA hcpA
            (by simp) done (stmtFuncIds fenv rest ++ owned) hdone hbound
            hownA hhead)
  | @loopDone funs V st c post body cv st1 hc hz ihc =>
    intro fenv env rets s₀ s₁ renv joins layout hfe huniq hvalid hp
      hcompl hcp _hfin done owned hdone hbound hown R henv hfr hclean hreb
    rcases layout with
      ⟨xvals, sA, h1, hParams, sB, h2, hId, sC, h3,
       exitParams, sD, h4, exitId, sE, h5, postParams, sF, h6,
       postId, sG, h7, sH, h8, sI, h9, cvId, sJ, h10,
       bodyId, sK, h11, hX, sL, h12, sM, h13, sN, h14,
       bodyEnv, sO, h15, htr⟩
    simp only [LoopLayout.hParams, LoopLayout.sI, LoopLayout.sA] at henv hfr hclean hreb ⊢
    have g0A : Grows s₀ sA := Grows.of_liftO h1
    have gAB : Grows sA sB := Grows.of_mapM_freshVal h2
    have gCD : Grows sC sD := Grows.of_mapM_freshVal h4
    have gEF : Grows sE sF := Grows.of_mapM_freshVal h6
    have a0A : SGrowsAt s₀.fn.blocks.size s₀ sA := SGrowsAt.of_grows g0A
    have a0B := a0A.trans (SGrowsAt.of_grows gAB)
    have a0C := a0B.trans (SGrowsAt.of_newBlock h3)
    have a0D := a0C.trans (SGrowsAt.of_grows gCD)
    have a0E := a0D.trans (SGrowsAt.of_newBlock h5)
    have a0F := a0E.trans (SGrowsAt.of_grows gEF)
    have a0G := a0F.trans (SGrowsAt.of_newBlock h7)
    have a0H := a0G.trans (SGrowsAt.of_sealCur h8)
    have hheadBase : s₀.fn.blocks.size ≤ hId := by
      rw [SGrowsAt.newBlock_id h3]
      exact a0B.size
    have a0I := a0H.trans (SGrowsAt.of_moveTo (Or.inl hheadBase) h9)
    have aAI : SGrowsAt 0 sA sI :=
      (((((((SGrowsAt.of_grows (N := 0) gAB).trans
        (SGrowsAt.of_newBlock h3)).trans (SGrowsAt.of_grows gCD)).trans
        (SGrowsAt.of_newBlock h5)).trans (SGrowsAt.of_grows gEF)).trans
        (SGrowsAt.of_newBlock h7)).trans (SGrowsAt.of_sealCur h8)).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)
    have gIJ : Grows sI sJ := trExpr_grows c fenv
      (env.setMany (modifiedX env [post, body]) hParams) sI sJ cvId h10
    have aJK : SGrowsAt sJ.fn.blocks.size sJ sK := SGrowsAt.of_newBlock h11
    have gKL : Grows sK sL := Grows.of_liftO h12
    have aJL := aJK.trans (SGrowsAt.of_grows gKL)
    have aJM := aJL.trans (SGrowsAt.of_sealCur h13)
    have hbodyBase : sJ.fn.blocks.size ≤ bodyId := by
      rw [SGrowsAt.newBlock_id h11]
    have aJN := aJM.trans (SGrowsAt.of_moveTo (Or.inl hbodyBase) h14)
    have eF : SGrowsAt 0 sE sF := SGrowsAt.of_grows gEF
    have eG := eF.trans (SGrowsAt.of_newBlock h7)
    have eH := eG.trans (SGrowsAt.of_sealCur h8)
    have eI := eH.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)
    have eJ := eI.trans (SGrowsAt.of_grows gIJ)
    have eK := eJ.trans (SGrowsAt.of_newBlock h11)
    have eL := eK.trans (SGrowsAt.of_grows gKL)
    have eM := eL.trans (SGrowsAt.of_sealCur h13)
    have eN := eM.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h14)
    have finish :
        Completes f sN.fn (exitId :: postId :: joins) →
        SGrowsAt 0 sE s₁ → sJ.fn.nextVal ≤ s₁.fn.nextVal →
        s₁.fn.curId = exitId → s₁.fn.cur = [] →
        renv = some (env.setMany (modifiedX env [post, body]) exitParams) →
        LHOut (model := model) P f rets sA.fn.nextVal sI s₁ R
          renv V st st1 .normal := by
      intro hcN ge hnextJ1 hcurExit hcurExit0 hrenv
      have hcJ : Completes f sJ.fn (exitId :: postId :: joins) :=
        SGrowsAt.completes_of aJN hcN
      have hcI : Completes f sI.fn (exitId :: postId :: joins) :=
        SGrowsAt.completes_of (SGrowsAt.of_grows gIJ) hcJ
      have hcurI : sI.fn.curId = hId := by
        rw [M.moveTo_apply] at h9
        exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h9).2).symm
      have hcurI0 : sI.fn.cur = [] := by
        rw [M.moveTo_apply] at h9
        simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h9).2
      have hheadExit : hId < exitId := by
        rw [SGrowsAt.newBlock_id h5]
        exact Nat.lt_of_lt_of_le (newBlock_target_lt h3)
          (SGrowsAt.of_grows (N := 0) gCD).size
      have hexitPost : exitId < postId := by
        rw [SGrowsAt.newBlock_id h7]
        exact Nat.lt_of_lt_of_le (newBlock_target_lt h5)
          (SGrowsAt.of_grows (N := 0) gEF).size
      have hpI0 : ProtectedAt joins sI.fn := ProtectedAt.forward hp a0I
      have hpI : ProtectedAt (exitId :: postId :: joins) sI.fn := by
        refine ⟨?_, ?_⟩
        · intro i hi
          simp only [List.mem_cons] at hi
          rcases hi with rfl | rfl | hi
          · exact Nat.lt_of_lt_of_le (newBlock_target_lt h5) eI.size
          · exact Nat.lt_of_lt_of_le (newBlock_target_lt h7)
              ((SGrowsAt.of_sealCur (N := 0) h8).trans
                (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h9)).size
          · exact hpI0.below i hi
        · simp only [List.mem_cons, not_or]
          exact ⟨by rw [hcurI]; exact Nat.ne_of_lt hheadExit,
            by rw [hcurI]; exact Nat.ne_of_lt (Nat.lt_trans hheadExit hexitPost),
            hpI0.away⟩
      have hvalidI : CurValid sI := by
        apply CurValid.of_moveTo _ h9
        exact Nat.lt_of_lt_of_le (newBlock_target_lt h3)
          (((((SGrowsAt.of_grows (N := 0) gCD).trans
            (SGrowsAt.of_newBlock h5)).trans
            (SGrowsAt.of_grows gEF)).trans
            (SGrowsAt.of_newBlock h7)).trans
            (SGrowsAt.of_sealCur h8)).size
      have hvalidJ : CurValid sJ := hvalidI.of_grows gIJ
      have csJL : CurSame sJ sL :=
        (CurSame.of_newBlock h11).trans (CurSame.of_grows gKL)
      have hcurM : sM.fn.curId = sJ.fn.curId := by
        rw [(sealCur_cur h13).choose_spec.1, csJL.1]
      have hbodyNe : sM.fn.curId ≠ bodyId := by
        rw [hcurM, SGrowsAt.newBlock_id h11]
        exact Nat.ne_of_lt hvalidJ
      have hpM : ProtectedAt (exitId :: postId :: joins) sM.fn := by
        have hgIM : SGrowsAt sI.fn.blocks.size sI sM :=
          ((SGrowsAt.of_grows (N := sI.fn.blocks.size) gIJ).trans
            (aJL.mono
              (SGrowsAt.of_grows (N := sI.fn.blocks.size) gIJ).size)).trans
            (SGrowsAt.of_sealCur h13)
        exact ProtectedAt.forward hpI hgIM
      have hfinM : CurFinal f sM.fn :=
        curFinal_of_move_grows h14 hbodyNe hpM.away (SGrows.rfl' sN) hcN
      have hbranchL : CurOK f sL.fn
          ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨exitId, hX⟩⟩ :=
        curOK_of_sealCur hfinM h13
      have hbranchJ : CurOK f sJ.fn
          ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨exitId, hX⟩⟩ :=
        CurOK.back_of_cur_eq csJL.1 (by
          have hnew : sK.fn.cur = sJ.fn.cur := by
            rw [M.newBlock_apply] at h11
            simpa using (congrArg (fun z => z.fn.cur) (M.some_pair_inj h11).2).symm
          have hedge : sL = sK := (M.edgeArgs_inv h12).2
          rw [hedge, hnew]) hbranchL
      have hcpJ : CurPlaced f sJ.fn := ⟨_, hbranchJ⟩
      have hcpI : CurPlaced f sI.fn := curPlaced_back_grows gIJ hcpJ
      obtain ⟨hlenH, hrangeH, hsB⟩ := M.mapM_freshVal_length h2
      have hndH : hParams.Nodup := by
        rw [hrangeH]
        exact M.nodup_range' _ _
      obtain ⟨RA, hleA, hbelowA, hfrA, hcv, hsimC⟩ :=
        ihc.1 fenv (env.setMany (modifiedX env [post, body]) hParams) R
          sI sJ cvId cv (exitId :: postId :: joins) hfe henv hfr hpI
          hcJ hcpJ rfl h10
      obtain ⟨rfl, valsE, hXget, hXvals⟩ :=
        edgeArgs_ok (henv.mono hleA) h12
      obtain ⟨hlenE, hrangeE, hsD⟩ := M.mapM_freshVal_length h4
      have hndE : exitParams.Nodup := by
        rw [hrangeE]
        exact M.nodup_range' _ _
      have hnextCB : sC.fn.nextVal = sB.fn.nextVal := by
        rw [M.newBlock_apply] at h3
        exact (congrArg (fun z => z.fn.nextVal) (M.some_pair_inj h3).2).symm
      have dI : SGrowsAt 0 sD sI :=
        (((((SGrowsAt.of_newBlock (N := 0) h5).trans
          (SGrowsAt.of_grows gEF)).trans (SGrowsAt.of_newBlock h7)).trans
          (SGrowsAt.of_sealCur h8)).trans
          (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9))
      have hnoneE : ∀ i ∈ exitParams, RA i = none := by
        intro i hi
        have hiRange := hi
        rw [hrangeE] at hiRange
        have hiLtI : i < sI.fn.nextVal :=
          Nat.lt_of_lt_of_le (M.mem_range'_bounds hiRange).2 (by
            simpa [hsD] using dI.nextVal)
        rw [hbelowA i hiLtI]
        apply hclean i
        · exact Nat.le_trans
            ((SGrowsAt.of_grows (N := 0) gAB).trans
              (SGrowsAt.of_newBlock h3)).nextVal
            (M.mem_range'_bounds hiRange).1
        · intro hiH
          rw [hrangeH] at hiH
          have hu := (M.mem_range'_bounds hiH).2
          have hl := (M.mem_range'_bounds hiRange).1
          have hend : sA.fn.nextVal + (modifiedX env [post, body]).length =
              sC.fn.nextVal := by rw [hnextCB, hsB]
          have hu' : i < sC.fn.nextVal := by rwa [hend] at hu
          exact Nat.not_lt_of_ge hl hu'
      let RE := RA.setMany exitParams valsE
      have hleE : Regs.Le RA RE := Regs.Le.setMany hndE hnoneE
      have hbelowE : Regs.BelowEq sA.fn.nextVal RA RE := by
        apply Regs.BelowEq.setMany
        intro i hi
        rw [hrangeE] at hi
        exact Nat.le_trans
          ((SGrowsAt.of_grows (N := 0) gAB).trans
            (SGrowsAt.of_newBlock h3)).nextVal
          (M.mem_range'_bounds hi).1
      have hfrE : RegsFresh RE s₁.fn := by
        intro i hi
        dsimp [RE]
        rw [Regs.setMany_other]
        · exact hfrA i (Nat.le_trans hnextJ1 hi)
        · intro him
          rw [hrangeE] at him
          have hltD := (M.mem_range'_bounds him).2
          have hD1 : sD.fn.nextVal ≤ s₁.fn.nextVal := by
            exact Nat.le_trans
              (SGrowsAt.of_newBlock (N := 0) h5).nextVal ge.nextVal
          have hltD' : i < sD.fn.nextVal := by simpa [hsD] using hltD
          exact Nat.not_lt_of_ge (Nat.le_trans hD1 hi) hltD'
      obtain ⟨eb, heb, hep⟩ := ge.params exitId ⟨exitParams, [], .ret []⟩
        (newBlock_target_get h5)
      have hlenEB : eb.params.length = valsE.length := by
        rw [hep, hlenE]
        exact hXvals.length_eq
      have hzero : RA cvId = some 0 := by
        rw [hz] at hcv
        simpa only [yulD_zero] using hcv
      have hsimE : SimS (model := model) P f sJ.fn RA st1 s₁.fn RE st1 := by
        have hs := simS_branchFalse_join (model := model) (P := P) (f := f)
          (st := st1) hcompl hbranchJ hzero heb hcurExit hcurExit0 hXget hlenEB
        simpa only [hep] using hs
      have hpgetE : RE.getMany exitParams = some valsE :=
        Regs.getMany_setMany_self hndE (by rw [hlenE]; exact hXvals.length_eq)
      have henvE : EnvOK (model := model)
          (env.setMany (modifiedX env [post, body]) exitParams) V RE := by
        have he : EnvOK (model := model)
            ((env.setMany (modifiedX env [post, body]) hParams).setMany
              (modifiedX env [post, body]) exitParams)
            (YulSemantics.VEnv.setMany V (modifiedX env [post, body]) valsE) RE :=
          EnvOK.setMany (xs := modifiedX env [post, body])
            (henv.mono (hleA.trans hleE))
            (Regs.getMany_eq_some_iff.mp hpgetE)
        rw [VMap.setMany_overwrite env (modifiedX_nodup huniq _)
          hlenH.symm hlenE.symm] at he
        rw [VEnv.setMany_self hXvals] at he
        exact he
      exact ⟨env.setMany (modifiedX env [post, body]) exitParams, RE, hrenv,
        (hbelowA.mono aAI.nextVal).trans hbelowE, hfrE,
        henvE, huniq.setMany _ _, hsimC.trans hsimE⟩
    cases bodyEnv with
    | none =>
      change (do
        moveTo postId
        let envP := env.setMany (modifiedX env [post, body]) postParams
        let renvP ← trScope fenv envP none rets post
        if let some envP' := renvP then
          let xvP ← edgeArgs envP' (modifiedX env [post, body])
          sealCur (.jump ⟨hId, xvP⟩)
        moveTo exitId
        pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sO =
          some (renv, s₁) at htr
      obtain ⟨uP, sP, h16, htr⟩ := M.bind_inv htr
      obtain ⟨uQ, sQ, h17, htr⟩ := M.bind_inv htr
      cases uQ with
      | none =>
        change (do
          moveTo exitId
          pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sQ =
            some (renv, s₁) at htr
        obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
        obtain ⟨hrenv, hs₁⟩ := M.pure_inv htr
        subst s₁
        have hcQ : Completes f sQ.fn (exitId :: postId :: joins) :=
          Completes.of_moveTo_protected (by simp) h18
            ((hcompl.protect postId).protect exitId)
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sP none sQ h17
        have hcP := SGrowsAt.completes_of gp hcQ
        have hcO := Completes.of_moveTo_protected (by simp) h16 hcP
        have gb := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) hParams)
          (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
          sN none sO h15
        have hcN := SGrowsAt.completes_of gb hcO
        have ge0 := eN.trans (gb.mono (Nat.zero_le _))
        have ge1 := ge0.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h16)
        have ge2 := ge1.trans (gp.mono (Nat.zero_le _))
        have ge := ge2.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h18)
        have gn0 := gb.mono (Nat.zero_le _)
        have gn1 := gn0.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h16)
        have gn2 := gn1.trans (gp.mono (Nat.zero_le _))
        have gn := gn2.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h18)
        exact finish hcN ge
          (Nat.le_trans aJN.nextVal gn.nextVal)
          (by rw [M.moveTo_apply] at h18
              exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h18).2).symm)
          (by rw [M.moveTo_apply] at h18
              simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h18).2)
          hrenv
      | some envP =>
        obtain ⟨xvP, sR, h18, htr⟩ := M.bind_inv htr
        obtain ⟨uS, sS, h19, htr⟩ := M.bind_inv htr
        obtain ⟨uT, sT, h20, htr⟩ := M.bind_inv htr
        obtain ⟨hrenv, hs₁⟩ := M.pure_inv htr
        subst s₁
        have hcS : Completes f sS.fn (exitId :: postId :: joins) :=
          Completes.of_moveTo_protected (by simp) h20
            ((hcompl.protect postId).protect exitId)
        have gQS : SGrows sQ sS :=
          (SGrowsAt.of_grows (Grows.of_liftO h18)).trans
            (SGrowsAt.of_sealCur h19)
        have hcQ := SGrowsAt.completes_of gQS hcS
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sP (some envP) sQ h17
        have hcP := SGrowsAt.completes_of gp hcQ
        have hcO := Completes.of_moveTo_protected (by simp) h16 hcP
        have gb := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) hParams)
          (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
          sN none sO h15
        have hcN := SGrowsAt.completes_of gb hcO
        have ge0 := eN.trans (gb.mono (Nat.zero_le _))
        have ge1 := ge0.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h16)
        have ge2 := ge1.trans (gp.mono (Nat.zero_le _))
        have ge3 := ge2.trans (gQS.mono (Nat.zero_le _))
        have ge := ge3.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h20)
        have gn0 := gb.mono (Nat.zero_le _)
        have gn1 := gn0.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h16)
        have gn2 := gn1.trans (gp.mono (Nat.zero_le _))
        have gn3 := gn2.trans (gQS.mono (Nat.zero_le _))
        have gn := gn3.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h20)
        exact finish hcN ge
          (Nat.le_trans aJN.nextVal gn.nextVal)
          (by rw [M.moveTo_apply] at h20
              exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h20).2).symm)
          (by rw [M.moveTo_apply] at h20
              simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h20).2)
          hrenv
    | some envB =>
      obtain ⟨xvB, sP, h16, htr⟩ := M.bind_inv htr
      obtain ⟨uQ, sQ, h17, htr⟩ := M.bind_inv htr
      obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
      obtain ⟨postEnv, sS, h19, htr⟩ := M.bind_inv htr
      cases postEnv with
      | none =>
        change (do
          moveTo exitId
          pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sS =
            some (renv, s₁) at htr
        obtain ⟨uT, sT, h20, htr⟩ := M.bind_inv htr
        obtain ⟨hrenv, hs₁⟩ := M.pure_inv htr
        subst s₁
        have hcS : Completes f sS.fn (exitId :: postId :: joins) :=
          Completes.of_moveTo_protected (by simp) h20
            ((hcompl.protect postId).protect exitId)
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sR none sS h19
        have hcR := SGrowsAt.completes_of gp hcS
        have hcQ := Completes.of_moveTo_protected (by simp) h18 hcR
        have gOQ : SGrows sO sQ :=
          (SGrowsAt.of_grows (Grows.of_liftO h16)).trans
            (SGrowsAt.of_sealCur h17)
        have hcO := SGrowsAt.completes_of gOQ hcQ
        have gb := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) hParams)
          (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
          sN (some envB) sO h15
        have hcN := SGrowsAt.completes_of gb hcO
        have ge0 := eN.trans (gb.mono (Nat.zero_le _))
        have ge1 := ge0.trans (gOQ.mono (Nat.zero_le _))
        have ge2 := ge1.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h18)
        have ge3 := ge2.trans (gp.mono (Nat.zero_le _))
        have ge := ge3.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h20)
        have gn0 := gb.mono (Nat.zero_le _)
        have gn1 := gn0.trans (gOQ.mono (Nat.zero_le _))
        have gn2 := gn1.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h18)
        have gn3 := gn2.trans (gp.mono (Nat.zero_le _))
        have gn := gn3.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h20)
        exact finish hcN ge
          (Nat.le_trans aJN.nextVal gn.nextVal)
          (by rw [M.moveTo_apply] at h20
              exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h20).2).symm)
          (by rw [M.moveTo_apply] at h20
              simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h20).2)
          hrenv
      | some envP =>
        obtain ⟨xvP, sT, h20, htr⟩ := M.bind_inv htr
        obtain ⟨uU, sU, h21, htr⟩ := M.bind_inv htr
        obtain ⟨uW, sW, h22, htr⟩ := M.bind_inv htr
        obtain ⟨hrenv, hs₁⟩ := M.pure_inv htr
        subst s₁
        have hcU : Completes f sU.fn (exitId :: postId :: joins) :=
          Completes.of_moveTo_protected (by simp) h22
            ((hcompl.protect postId).protect exitId)
        have gSU : SGrows sS sU :=
          (SGrowsAt.of_grows (Grows.of_liftO h20)).trans
            (SGrowsAt.of_sealCur h21)
        have hcS := SGrowsAt.completes_of gSU hcU
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sR (some envP) sS h19
        have hcR := SGrowsAt.completes_of gp hcS
        have hcQ := Completes.of_moveTo_protected (by simp) h18 hcR
        have gOQ : SGrows sO sQ :=
          (SGrowsAt.of_grows (Grows.of_liftO h16)).trans
            (SGrowsAt.of_sealCur h17)
        have hcO := SGrowsAt.completes_of gOQ hcQ
        have gb := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) hParams)
          (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
          sN (some envB) sO h15
        have hcN := SGrowsAt.completes_of gb hcO
        have ge0 := eN.trans (gb.mono (Nat.zero_le _))
        have ge1 := ge0.trans (gOQ.mono (Nat.zero_le _))
        have ge2 := ge1.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h18)
        have ge3 := ge2.trans (gp.mono (Nat.zero_le _))
        have ge4 := ge3.trans (gSU.mono (Nat.zero_le _))
        have ge := ge4.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h22)
        have gn0 := gb.mono (Nat.zero_le _)
        have gn1 := gn0.trans (gOQ.mono (Nat.zero_le _))
        have gn2 := gn1.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h18)
        have gn3 := gn2.trans (gp.mono (Nat.zero_le _))
        have gn4 := gn3.trans (gSU.mono (Nat.zero_le _))
        have gn := gn4.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h22)
        exact finish hcN ge
          (Nat.le_trans aJN.nextVal gn.nextVal)
          (by rw [M.moveTo_apply] at h22
              exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h22).2).symm)
          (by rw [M.moveTo_apply] at h22
              simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h22).2)
          hrenv
  | @loopCondHalt funs V st c post body st1 hc ihc =>
    intro fenv env rets s₀ s₁ renv joins layout hfe huniq hvalid hp
      hcompl hcp _hfin done owned hdone hbound hown R henv hfr hclean hreb
    rcases layout with
      ⟨xvals, sA, h1, hParams, sB, h2, hId, sC, h3,
       exitParams, sD, h4, exitId, sE, h5, postParams, sF, h6,
       postId, sG, h7, sH, h8, sI, h9, cvId, sJ, h10,
       bodyId, sK, h11, hX, sL, h12, sM, h13, sN, h14,
       bodyEnv, sO, h15, htr⟩
    simp only [LoopLayout.hParams, LoopLayout.sI, LoopLayout.sA] at henv hfr hclean hreb ⊢
    have g0A : Grows s₀ sA := Grows.of_liftO h1
    have gAB : Grows sA sB := Grows.of_mapM_freshVal h2
    have gCD : Grows sC sD := Grows.of_mapM_freshVal h4
    have gEF : Grows sE sF := Grows.of_mapM_freshVal h6
    have a0A : SGrowsAt s₀.fn.blocks.size s₀ sA := SGrowsAt.of_grows g0A
    have a0B := a0A.trans (SGrowsAt.of_grows gAB)
    have a0C := a0B.trans (SGrowsAt.of_newBlock h3)
    have a0D := a0C.trans (SGrowsAt.of_grows gCD)
    have a0E := a0D.trans (SGrowsAt.of_newBlock h5)
    have a0F := a0E.trans (SGrowsAt.of_grows gEF)
    have a0G := a0F.trans (SGrowsAt.of_newBlock h7)
    have a0H := a0G.trans (SGrowsAt.of_sealCur h8)
    have hheadBase : s₀.fn.blocks.size ≤ hId := by
      rw [SGrowsAt.newBlock_id h3]
      exact a0B.size
    have a0I := a0H.trans (SGrowsAt.of_moveTo (Or.inl hheadBase) h9)
    have aAI : SGrowsAt 0 sA sI :=
      (((((((SGrowsAt.of_grows (N := 0) gAB).trans
        (SGrowsAt.of_newBlock h3)).trans (SGrowsAt.of_grows gCD)).trans
        (SGrowsAt.of_newBlock h5)).trans (SGrowsAt.of_grows gEF)).trans
        (SGrowsAt.of_newBlock h7)).trans (SGrowsAt.of_sealCur h8)).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)
    have gIJ : Grows sI sJ := trExpr_grows c fenv
      (env.setMany (modifiedX env [post, body]) hParams) sI sJ cvId h10
    have aJK : SGrowsAt sJ.fn.blocks.size sJ sK := SGrowsAt.of_newBlock h11
    have gKL : Grows sK sL := Grows.of_liftO h12
    have aJL := aJK.trans (SGrowsAt.of_grows gKL)
    have aJM := aJL.trans (SGrowsAt.of_sealCur h13)
    have hbodyBase : sJ.fn.blocks.size ≤ bodyId := by
      rw [SGrowsAt.newBlock_id h11]
    have aJN := aJM.trans (SGrowsAt.of_moveTo (Or.inl hbodyBase) h14)
    have eF : SGrowsAt 0 sE sF := SGrowsAt.of_grows gEF
    have eG := eF.trans (SGrowsAt.of_newBlock h7)
    have eH := eG.trans (SGrowsAt.of_sealCur h8)
    have eI := eH.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)
    have eJ := eI.trans (SGrowsAt.of_grows gIJ)
    have eK := eJ.trans (SGrowsAt.of_newBlock h11)
    have eL := eK.trans (SGrowsAt.of_grows gKL)
    have eM := eL.trans (SGrowsAt.of_sealCur h13)
    have eN := eM.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h14)
    have hcN : Completes f sN.fn (exitId :: postId :: joins) := by
      have gb := trScope_grows fenv
        (env.setMany (modifiedX env [post, body]) hParams)
        (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
        sN bodyEnv sO h15
      cases bodyEnv with
      | none =>
        change (do
          moveTo postId
          let envP := env.setMany (modifiedX env [post, body]) postParams
          let renvP ← trScope fenv envP none rets post
          if let some envP' := renvP then
            let xvP ← edgeArgs envP' (modifiedX env [post, body])
            sealCur (.jump ⟨hId, xvP⟩)
          moveTo exitId
          pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sO =
            some (renv, s₁) at htr
        obtain ⟨uP, sP, h16, htr⟩ := M.bind_inv htr
        obtain ⟨postEnv, sQ, h17, htr⟩ := M.bind_inv htr
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sP postEnv sQ h17
        cases postEnv with
        | none =>
          change (do
            moveTo exitId
            pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sQ =
              some (renv, s₁) at htr
          obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
          obtain ⟨-, hs₁⟩ := M.pure_inv htr
          subst s₁
          have hcQ : Completes f sQ.fn (exitId :: postId :: joins) :=
            Completes.of_moveTo_protected (by simp) h18
              ((hcompl.protect postId).protect exitId)
          have hcP := SGrowsAt.completes_of gp hcQ
          have hcO := Completes.of_moveTo_protected (by simp) h16 hcP
          exact SGrowsAt.completes_of gb hcO
        | some envP =>
          obtain ⟨xvP, sR, h18, htr⟩ := M.bind_inv htr
          obtain ⟨uS, sS, h19, htr⟩ := M.bind_inv htr
          obtain ⟨uT, sT, h20, htr⟩ := M.bind_inv htr
          obtain ⟨-, hs₁⟩ := M.pure_inv htr
          subst s₁
          have hcS : Completes f sS.fn (exitId :: postId :: joins) :=
            Completes.of_moveTo_protected (by simp) h20
              ((hcompl.protect postId).protect exitId)
          have gQS : SGrows sQ sS :=
            (SGrowsAt.of_grows (Grows.of_liftO h18)).trans
              (SGrowsAt.of_sealCur h19)
          have hcQ := SGrowsAt.completes_of gQS hcS
          have hcP := SGrowsAt.completes_of gp hcQ
          have hcO := Completes.of_moveTo_protected (by simp) h16 hcP
          exact SGrowsAt.completes_of gb hcO
      | some envB =>
        obtain ⟨xvB, sP, h16, htr⟩ := M.bind_inv htr
        obtain ⟨uQ, sQ, h17, htr⟩ := M.bind_inv htr
        obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
        obtain ⟨postEnv, sS, h19, htr⟩ := M.bind_inv htr
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sR postEnv sS h19
        have gOQ : SGrows sO sQ :=
          (SGrowsAt.of_grows (Grows.of_liftO h16)).trans
            (SGrowsAt.of_sealCur h17)
        cases postEnv with
        | none =>
          change (do
            moveTo exitId
            pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sS =
              some (renv, s₁) at htr
          obtain ⟨uT, sT, h20, htr⟩ := M.bind_inv htr
          obtain ⟨-, hs₁⟩ := M.pure_inv htr
          subst s₁
          have hcS : Completes f sS.fn (exitId :: postId :: joins) :=
            Completes.of_moveTo_protected (by simp) h20
              ((hcompl.protect postId).protect exitId)
          have hcR := SGrowsAt.completes_of gp hcS
          have hcQ := Completes.of_moveTo_protected (by simp) h18 hcR
          have hcO := SGrowsAt.completes_of gOQ hcQ
          exact SGrowsAt.completes_of gb hcO
        | some envP =>
          obtain ⟨xvP, sT, h20, htr⟩ := M.bind_inv htr
          obtain ⟨uU, sU, h21, htr⟩ := M.bind_inv htr
          obtain ⟨uW, sW, h22, htr⟩ := M.bind_inv htr
          obtain ⟨-, hs₁⟩ := M.pure_inv htr
          subst s₁
          have hcU : Completes f sU.fn (exitId :: postId :: joins) :=
            Completes.of_moveTo_protected (by simp) h22
              ((hcompl.protect postId).protect exitId)
          have gSU : SGrows sS sU :=
            (SGrowsAt.of_grows (Grows.of_liftO h20)).trans
              (SGrowsAt.of_sealCur h21)
          have hcS := SGrowsAt.completes_of gSU hcU
          have hcR := SGrowsAt.completes_of gp hcS
          have hcQ := Completes.of_moveTo_protected (by simp) h18 hcR
          have hcO := SGrowsAt.completes_of gOQ hcQ
          exact SGrowsAt.completes_of gb hcO
    have hcJ : Completes f sJ.fn (exitId :: postId :: joins) :=
      SGrowsAt.completes_of aJN hcN
    have hcI : Completes f sI.fn (exitId :: postId :: joins) :=
      SGrowsAt.completes_of (SGrowsAt.of_grows gIJ) hcJ
    have hcurI : sI.fn.curId = hId := by
      rw [M.moveTo_apply] at h9
      exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h9).2).symm
    have hcurI0 : sI.fn.cur = [] := by
      rw [M.moveTo_apply] at h9
      simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h9).2
    have hheadExit : hId < exitId := by
      rw [SGrowsAt.newBlock_id h5]
      exact Nat.lt_of_lt_of_le (newBlock_target_lt h3)
        (SGrowsAt.of_grows (N := 0) gCD).size
    have hexitPost : exitId < postId := by
      rw [SGrowsAt.newBlock_id h7]
      exact Nat.lt_of_lt_of_le (newBlock_target_lt h5)
        (SGrowsAt.of_grows (N := 0) gEF).size
    have hpI0 : ProtectedAt joins sI.fn := ProtectedAt.forward hp a0I
    have hpI : ProtectedAt (exitId :: postId :: joins) sI.fn := by
      refine ⟨?_, ?_⟩
      · intro i hi
        simp only [List.mem_cons] at hi
        rcases hi with rfl | rfl | hi
        · exact Nat.lt_of_lt_of_le (newBlock_target_lt h5) eI.size
        · exact Nat.lt_of_lt_of_le (newBlock_target_lt h7)
            ((SGrowsAt.of_sealCur (N := 0) h8).trans
              (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h9)).size
        · exact hpI0.below i hi
      · simp only [List.mem_cons, not_or]
        exact ⟨by rw [hcurI]; exact Nat.ne_of_lt hheadExit,
          by rw [hcurI]; exact Nat.ne_of_lt (Nat.lt_trans hheadExit hexitPost),
          hpI0.away⟩
    have hvalidI : CurValid sI := by
      apply CurValid.of_moveTo _ h9
      exact Nat.lt_of_lt_of_le (newBlock_target_lt h3)
        (((((SGrowsAt.of_grows (N := 0) gCD).trans
          (SGrowsAt.of_newBlock h5)).trans
          (SGrowsAt.of_grows gEF)).trans
          (SGrowsAt.of_newBlock h7)).trans
          (SGrowsAt.of_sealCur h8)).size
    have hvalidJ : CurValid sJ := hvalidI.of_grows gIJ
    have csJL : CurSame sJ sL :=
      (CurSame.of_newBlock h11).trans (CurSame.of_grows gKL)
    have hcurM : sM.fn.curId = sJ.fn.curId := by
      rw [(sealCur_cur h13).choose_spec.1, csJL.1]
    have hbodyNe : sM.fn.curId ≠ bodyId := by
      rw [hcurM, SGrowsAt.newBlock_id h11]
      exact Nat.ne_of_lt hvalidJ
    have hpM : ProtectedAt (exitId :: postId :: joins) sM.fn := by
      have hgIM : SGrowsAt sI.fn.blocks.size sI sM :=
        ((SGrowsAt.of_grows (N := sI.fn.blocks.size) gIJ).trans
          (aJL.mono
            (SGrowsAt.of_grows (N := sI.fn.blocks.size) gIJ).size)).trans
          (SGrowsAt.of_sealCur h13)
      exact ProtectedAt.forward hpI hgIM
    have hfinM : CurFinal f sM.fn :=
      curFinal_of_move_grows h14 hbodyNe hpM.away (SGrows.rfl' sN) hcN
    have hbranchL : CurOK f sL.fn
        ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨exitId, hX⟩⟩ :=
      curOK_of_sealCur hfinM h13
    have hbranchJ : CurOK f sJ.fn
        ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨exitId, hX⟩⟩ :=
      CurOK.back_of_cur_eq csJL.1 (by
        have hnew : sK.fn.cur = sJ.fn.cur := by
          rw [M.newBlock_apply] at h11
          simpa using (congrArg (fun z => z.fn.cur) (M.some_pair_inj h11).2).symm
        have hedge : sL = sK := (M.edgeArgs_inv h12).2
        rw [hedge, hnew]) hbranchL
    have hcpJ : CurPlaced f sJ.fn := ⟨_, hbranchJ⟩
    have hcpI : CurPlaced f sI.fn := curPlaced_back_grows gIJ hcpJ
    obtain ⟨hlenH, hrangeH, hsB⟩ := M.mapM_freshVal_length h2
    have hndH : hParams.Nodup := by
      rw [hrangeH]
      exact M.nodup_range' _ _
    have hhalt := ihc.1 fenv
      (env.setMany (modifiedX env [post, body]) hParams) R sI sJ cvId
      (exitId :: postId :: joins) hfe henv hfr hpI hcJ hcpJ h10
    exact hhalt
  | @loopStep funs V st c post body cv st1 Vb stb ob Vp stp Vend stend o
      hc hnz hbodyStep hob hpost hloop ihc ihb ihpost ihloop =>
    intro fenv env rets s₀ s₁ renv joins layout hfe huniq hvalid hp
      hcompl hcp _hfin done owned hdone hbound hown R henv hfr hclean hreb
    have hpTail := layout.tail_fprefix
    rcases layout with
      ⟨xvals, sA, h1, hParams, sB, h2, hId, sC, h3,
       exitParams, sD, h4, exitId, sE, h5, postParams, sF, h6,
       postId, sG, h7, sH, h8, sI, h9, cvId, sJ, h10,
       bodyId, sK, h11, hX, sL, h12, sM, h13, sN, h14,
       bodyEnv, sO, h15, htr⟩
    simp only [LoopLayout.hParams, LoopLayout.sI, LoopLayout.sA] at henv hfr hclean hreb ⊢
    have g0A : Grows s₀ sA := Grows.of_liftO h1
    have gAB : Grows sA sB := Grows.of_mapM_freshVal h2
    have gCD : Grows sC sD := Grows.of_mapM_freshVal h4
    have gEF : Grows sE sF := Grows.of_mapM_freshVal h6
    have a0A : SGrowsAt s₀.fn.blocks.size s₀ sA := SGrowsAt.of_grows g0A
    have a0B := a0A.trans (SGrowsAt.of_grows gAB)
    have a0C := a0B.trans (SGrowsAt.of_newBlock h3)
    have a0D := a0C.trans (SGrowsAt.of_grows gCD)
    have a0E := a0D.trans (SGrowsAt.of_newBlock h5)
    have a0F := a0E.trans (SGrowsAt.of_grows gEF)
    have a0G := a0F.trans (SGrowsAt.of_newBlock h7)
    have a0H := a0G.trans (SGrowsAt.of_sealCur h8)
    have hheadBase : s₀.fn.blocks.size ≤ hId := by
      rw [SGrowsAt.newBlock_id h3]
      exact a0B.size
    have a0I := a0H.trans (SGrowsAt.of_moveTo (Or.inl hheadBase) h9)
    have aAI : SGrowsAt 0 sA sI :=
      (((((((SGrowsAt.of_grows (N := 0) gAB).trans
        (SGrowsAt.of_newBlock h3)).trans (SGrowsAt.of_grows gCD)).trans
        (SGrowsAt.of_newBlock h5)).trans (SGrowsAt.of_grows gEF)).trans
        (SGrowsAt.of_newBlock h7)).trans (SGrowsAt.of_sealCur h8)).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)
    have gIJ : Grows sI sJ := trExpr_grows c fenv
      (env.setMany (modifiedX env [post, body]) hParams) sI sJ cvId h10
    have aJK : SGrowsAt sJ.fn.blocks.size sJ sK := SGrowsAt.of_newBlock h11
    have gKL : Grows sK sL := Grows.of_liftO h12
    have aJL := aJK.trans (SGrowsAt.of_grows gKL)
    have aJM := aJL.trans (SGrowsAt.of_sealCur h13)
    have hbodyBase : sJ.fn.blocks.size ≤ bodyId := by
      rw [SGrowsAt.newBlock_id h11]
    have aJN := aJM.trans (SGrowsAt.of_moveTo (Or.inl hbodyBase) h14)
    have eF : SGrowsAt 0 sE sF := SGrowsAt.of_grows gEF
    have eG := eF.trans (SGrowsAt.of_newBlock h7)
    have eH := eG.trans (SGrowsAt.of_sealCur h8)
    have eI := eH.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)
    have eJ := eI.trans (SGrowsAt.of_grows gIJ)
    have eK := eJ.trans (SGrowsAt.of_newBlock h11)
    have eL := eK.trans (SGrowsAt.of_grows gKL)
    have eM := eL.trans (SGrowsAt.of_sealCur h13)
    have eN := eM.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h14)
    have hcN : Completes f sN.fn (exitId :: postId :: joins) := by
      have gb := trScope_grows fenv
        (env.setMany (modifiedX env [post, body]) hParams)
        (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
        sN bodyEnv sO h15
      cases bodyEnv with
      | none =>
        change (do
          moveTo postId
          let envP := env.setMany (modifiedX env [post, body]) postParams
          let renvP ← trScope fenv envP none rets post
          if let some envP' := renvP then
            let xvP ← edgeArgs envP' (modifiedX env [post, body])
            sealCur (.jump ⟨hId, xvP⟩)
          moveTo exitId
          pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sO =
            some (renv, s₁) at htr
        obtain ⟨uP, sP, h16, htr⟩ := M.bind_inv htr
        obtain ⟨postEnv, sQ, h17, htr⟩ := M.bind_inv htr
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sP postEnv sQ h17
        cases postEnv with
        | none =>
          change (do
            moveTo exitId
            pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sQ =
              some (renv, s₁) at htr
          obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
          obtain ⟨-, hs₁⟩ := M.pure_inv htr
          subst s₁
          have hcQ : Completes f sQ.fn (exitId :: postId :: joins) :=
            Completes.of_moveTo_protected (by simp) h18
              ((hcompl.protect postId).protect exitId)
          have hcP := SGrowsAt.completes_of gp hcQ
          have hcO := Completes.of_moveTo_protected (by simp) h16 hcP
          exact SGrowsAt.completes_of gb hcO
        | some envP =>
          obtain ⟨xvP, sR, h18, htr⟩ := M.bind_inv htr
          obtain ⟨uS, sS, h19, htr⟩ := M.bind_inv htr
          obtain ⟨uT, sT, h20, htr⟩ := M.bind_inv htr
          obtain ⟨-, hs₁⟩ := M.pure_inv htr
          subst s₁
          have hcS : Completes f sS.fn (exitId :: postId :: joins) :=
            Completes.of_moveTo_protected (by simp) h20
              ((hcompl.protect postId).protect exitId)
          have gQS : SGrows sQ sS :=
            (SGrowsAt.of_grows (Grows.of_liftO h18)).trans
              (SGrowsAt.of_sealCur h19)
          have hcQ := SGrowsAt.completes_of gQS hcS
          have hcP := SGrowsAt.completes_of gp hcQ
          have hcO := Completes.of_moveTo_protected (by simp) h16 hcP
          exact SGrowsAt.completes_of gb hcO
      | some envB =>
        obtain ⟨xvB, sP, h16, htr⟩ := M.bind_inv htr
        obtain ⟨uQ, sQ, h17, htr⟩ := M.bind_inv htr
        obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
        obtain ⟨postEnv, sS, h19, htr⟩ := M.bind_inv htr
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sR postEnv sS h19
        have gOQ : SGrows sO sQ :=
          (SGrowsAt.of_grows (Grows.of_liftO h16)).trans
            (SGrowsAt.of_sealCur h17)
        cases postEnv with
        | none =>
          change (do
            moveTo exitId
            pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sS =
              some (renv, s₁) at htr
          obtain ⟨uT, sT, h20, htr⟩ := M.bind_inv htr
          obtain ⟨-, hs₁⟩ := M.pure_inv htr
          subst s₁
          have hcS : Completes f sS.fn (exitId :: postId :: joins) :=
            Completes.of_moveTo_protected (by simp) h20
              ((hcompl.protect postId).protect exitId)
          have hcR := SGrowsAt.completes_of gp hcS
          have hcQ := Completes.of_moveTo_protected (by simp) h18 hcR
          have hcO := SGrowsAt.completes_of gOQ hcQ
          exact SGrowsAt.completes_of gb hcO
        | some envP =>
          obtain ⟨xvP, sT, h20, htr⟩ := M.bind_inv htr
          obtain ⟨uU, sU, h21, htr⟩ := M.bind_inv htr
          obtain ⟨uW, sW, h22, htr⟩ := M.bind_inv htr
          obtain ⟨-, hs₁⟩ := M.pure_inv htr
          subst s₁
          have hcU : Completes f sU.fn (exitId :: postId :: joins) :=
            Completes.of_moveTo_protected (by simp) h22
              ((hcompl.protect postId).protect exitId)
          have gSU : SGrows sS sU :=
            (SGrowsAt.of_grows (Grows.of_liftO h20)).trans
              (SGrowsAt.of_sealCur h21)
          have hcS := SGrowsAt.completes_of gSU hcU
          have hcR := SGrowsAt.completes_of gp hcS
          have hcQ := Completes.of_moveTo_protected (by simp) h18 hcR
          have hcO := SGrowsAt.completes_of gOQ hcQ
          exact SGrowsAt.completes_of gb hcO
    have hcJ : Completes f sJ.fn (exitId :: postId :: joins) :=
      SGrowsAt.completes_of aJN hcN
    have hcI : Completes f sI.fn (exitId :: postId :: joins) :=
      SGrowsAt.completes_of (SGrowsAt.of_grows gIJ) hcJ
    have hcurI : sI.fn.curId = hId := by
      rw [M.moveTo_apply] at h9
      exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h9).2).symm
    have hcurI0 : sI.fn.cur = [] := by
      rw [M.moveTo_apply] at h9
      simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h9).2
    have hheadExit : hId < exitId := by
      rw [SGrowsAt.newBlock_id h5]
      exact Nat.lt_of_lt_of_le (newBlock_target_lt h3)
        (SGrowsAt.of_grows (N := 0) gCD).size
    have hexitPost : exitId < postId := by
      rw [SGrowsAt.newBlock_id h7]
      exact Nat.lt_of_lt_of_le (newBlock_target_lt h5)
        (SGrowsAt.of_grows (N := 0) gEF).size
    have hpI0 : ProtectedAt joins sI.fn := ProtectedAt.forward hp a0I
    have hpI : ProtectedAt (exitId :: postId :: joins) sI.fn := by
      refine ⟨?_, ?_⟩
      · intro i hi
        simp only [List.mem_cons] at hi
        rcases hi with rfl | rfl | hi
        · exact Nat.lt_of_lt_of_le (newBlock_target_lt h5) eI.size
        · exact Nat.lt_of_lt_of_le (newBlock_target_lt h7)
            ((SGrowsAt.of_sealCur (N := 0) h8).trans
              (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h9)).size
        · exact hpI0.below i hi
      · simp only [List.mem_cons, not_or]
        exact ⟨by rw [hcurI]; exact Nat.ne_of_lt hheadExit,
          by rw [hcurI]; exact Nat.ne_of_lt (Nat.lt_trans hheadExit hexitPost),
          hpI0.away⟩
    have hvalidI : CurValid sI := by
      apply CurValid.of_moveTo _ h9
      exact Nat.lt_of_lt_of_le (newBlock_target_lt h3)
        (((((SGrowsAt.of_grows (N := 0) gCD).trans
          (SGrowsAt.of_newBlock h5)).trans
          (SGrowsAt.of_grows gEF)).trans
          (SGrowsAt.of_newBlock h7)).trans
          (SGrowsAt.of_sealCur h8)).size
    have hvalidJ : CurValid sJ := hvalidI.of_grows gIJ
    have csJL : CurSame sJ sL :=
      (CurSame.of_newBlock h11).trans (CurSame.of_grows gKL)
    have hcurM : sM.fn.curId = sJ.fn.curId := by
      rw [(sealCur_cur h13).choose_spec.1, csJL.1]
    have hbodyNe : sM.fn.curId ≠ bodyId := by
      rw [hcurM, SGrowsAt.newBlock_id h11]
      exact Nat.ne_of_lt hvalidJ
    have hpM : ProtectedAt (exitId :: postId :: joins) sM.fn := by
      have hgIM : SGrowsAt sI.fn.blocks.size sI sM :=
        ((SGrowsAt.of_grows (N := sI.fn.blocks.size) gIJ).trans
          (aJL.mono
            (SGrowsAt.of_grows (N := sI.fn.blocks.size) gIJ).size)).trans
          (SGrowsAt.of_sealCur h13)
      exact ProtectedAt.forward hpI hgIM
    have hfinM : CurFinal f sM.fn :=
      curFinal_of_move_grows h14 hbodyNe hpM.away (SGrows.rfl' sN) hcN
    have hbranchL : CurOK f sL.fn
        ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨exitId, hX⟩⟩ :=
      curOK_of_sealCur hfinM h13
    have hbranchJ : CurOK f sJ.fn
        ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨exitId, hX⟩⟩ :=
      CurOK.back_of_cur_eq csJL.1 (by
        have hnew : sK.fn.cur = sJ.fn.cur := by
          rw [M.newBlock_apply] at h11
          simpa using (congrArg (fun z => z.fn.cur) (M.some_pair_inj h11).2).symm
        have hedge : sL = sK := (M.edgeArgs_inv h12).2
        rw [hedge, hnew]) hbranchL
    have hcpJ : CurPlaced f sJ.fn := ⟨_, hbranchJ⟩
    have hcpI : CurPlaced f sI.fn := curPlaced_back_grows gIJ hcpJ
    obtain ⟨hlenH, hrangeH, hsB⟩ := M.mapM_freshVal_length h2
    have hndH : hParams.Nodup := by
      rw [hrangeH]
      exact M.nodup_range' _ _
    obtain ⟨RA, hleA, hbelowA, hfrA, hcv, hsimC⟩ := ihc.1 fenv
      (env.setMany (modifiedX env [post, body]) hParams) R sI sJ cvId cv
      (exitId :: postId :: joins) hfe henv hfr hpI hcJ hcpJ rfl h10
    have hnz' : cv ≠ 0 := by simpa only [yulD_zero] using hnz
    have aKN : SGrowsAt 0 sK sN :=
      ((SGrowsAt.of_grows gKL).trans (SGrowsAt.of_sealCur h13)).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h14)
    obtain ⟨bb, hbb, hbp⟩ := aKN.params bodyId ⟨[], [], .ret []⟩
      (newBlock_target_get h11)
    have hcurN : sN.fn.curId = bodyId := by
      rw [M.moveTo_apply] at h14
      exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h14).2).symm
    have hcurN0 : sN.fn.cur = [] := by
      rw [M.moveTo_apply] at h14
      simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h14).2
    have hsimB := simS_branchTrue_body (model := model) (P := P) (f := f)
      (st := st1) hcN hbranchJ hcv hnz' hbb hbp hcurN hcurN0
    have hvalidN : CurValid sN := by
      apply CurValid.of_moveTo _ h14
      exact Nat.lt_of_lt_of_le (newBlock_target_lt h11)
        ((SGrowsAt.of_grows (N := 0) gKL).trans
          (SGrowsAt.of_sealCur h13)).size
    have aIJ : SGrows sI sJ := SGrowsAt.of_grows gIJ
    have gIN : SGrows sI sN :=
      SGrowsAt.trans aIJ (aJN.mono aIJ.size)
    have hpN : ProtectedAt (exitId :: postId :: joins) sN.fn :=
      ProtectedAt.forward hpI gIN
    have gbody : SGrows sN sO := trScope_grows fenv
      (env.setMany (modifiedX env [post, body]) hParams)
      (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
      sN bodyEnv sO h15
    have hpO : ProtectedAt (exitId :: postId :: joins) sO.fn :=
      ProtectedAt.forward hpN gbody
    have htrB : trStmt fenv
        (env.setMany (modifiedX env [post, body]) hParams)
        (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets
        (.block body) sN = some (bodyEnv, sO) := by
      rw [trStmt]
      exact h15
    have hvalidO : CurValid sO := (trStmt_cur hvalidN htrB).1
    have tailBody :
        Completes f sO.fn (exitId :: postId :: joins) ∧
        CurPlaced f sO.fn ∧
        (bodyEnv = none → CurFinal f sO.fn) := by
      cases bodyEnv with
      | none =>
        change (do
          moveTo postId
          let envP := env.setMany (modifiedX env [post, body]) postParams
          let renvP ← trScope fenv envP none rets post
          if let some envP' := renvP then
            let xvP ← edgeArgs envP' (modifiedX env [post, body])
            sealCur (.jump ⟨hId, xvP⟩)
          moveTo exitId
          pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sO =
            some (renv, s₁) at htr
        obtain ⟨uP, sP, h16, htr⟩ := M.bind_inv htr
        obtain ⟨postEnv, sQ, h17, htr⟩ := M.bind_inv htr
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sP postEnv sQ h17
        have hcP : Completes f sP.fn (exitId :: postId :: joins) := by
          cases postEnv with
          | none =>
            change (do
              moveTo exitId
              pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sQ =
                some (renv, s₁) at htr
            obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
            obtain ⟨-, hs₁⟩ := M.pure_inv htr
            subst s₁
            have hcQ : Completes f sQ.fn (exitId :: postId :: joins) :=
              Completes.of_moveTo_protected (by simp) h18
                ((hcompl.protect postId).protect exitId)
            exact SGrowsAt.completes_of gp hcQ
          | some envP =>
            obtain ⟨xvP, sR, h18, htr⟩ := M.bind_inv htr
            obtain ⟨uS, sS, h19, htr⟩ := M.bind_inv htr
            obtain ⟨uT, sT, h20, htr⟩ := M.bind_inv htr
            obtain ⟨-, hs₁⟩ := M.pure_inv htr
            subst s₁
            have hcS : Completes f sS.fn (exitId :: postId :: joins) :=
              Completes.of_moveTo_protected (by simp) h20
                ((hcompl.protect postId).protect exitId)
            have gQS : SGrows sQ sS :=
              (SGrowsAt.of_grows (Grows.of_liftO h18)).trans
                (SGrowsAt.of_sealCur h19)
            exact SGrowsAt.completes_of gp
              (SGrowsAt.completes_of gQS hcS)
        have hpostNe : sO.fn.curId ≠ postId := fun he =>
          hpO.away (by simp [he])
        have hcurO0 := trScope_none_cur_nil fenv
          (env.setMany (modifiedX env [post, body]) hParams)
          (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
          sN sO h15
        have hcomplO := Completes.of_moveTo_protected (by simp) h16 hcP
        have hfinO := curFinal_of_move_grows h16 hpostNe hpO.away
          (SGrows.rfl' sP) hcP
        exact ⟨hcomplO,
          CurPlaced.of_moveTo_empty hvalidO hcurO0 hpostNe h16 hpO.away hcP,
          fun _ => hfinO⟩
      | some envB =>
        obtain ⟨xvB, sP, h16, htr⟩ := M.bind_inv htr
        obtain ⟨uQ, sQ, h17, htr⟩ := M.bind_inv htr
        obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
        obtain ⟨postEnv, sS, h19, htr⟩ := M.bind_inv htr
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sR postEnv sS h19
        have hcR : Completes f sR.fn (exitId :: postId :: joins) := by
          cases postEnv with
          | none =>
            change (do
              moveTo exitId
              pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sS =
                some (renv, s₁) at htr
            obtain ⟨uT, sT, h20, htr⟩ := M.bind_inv htr
            obtain ⟨-, hs₁⟩ := M.pure_inv htr
            subst s₁
            have hcS : Completes f sS.fn (exitId :: postId :: joins) :=
              Completes.of_moveTo_protected (by simp) h20
                ((hcompl.protect postId).protect exitId)
            exact SGrowsAt.completes_of gp hcS
          | some envP =>
            obtain ⟨xvP, sT, h20, htr⟩ := M.bind_inv htr
            obtain ⟨uU, sU, h21, htr⟩ := M.bind_inv htr
            obtain ⟨uW, sW, h22, htr⟩ := M.bind_inv htr
            obtain ⟨-, hs₁⟩ := M.pure_inv htr
            subst s₁
            have hcU : Completes f sU.fn (exitId :: postId :: joins) :=
              Completes.of_moveTo_protected (by simp) h22
                ((hcompl.protect postId).protect exitId)
            have gSU : SGrows sS sU :=
              (SGrowsAt.of_grows (Grows.of_liftO h20)).trans
                (SGrowsAt.of_sealCur h21)
            exact SGrowsAt.completes_of gp
              (SGrowsAt.completes_of gSU hcU)
        have hcQ : Completes f sQ.fn (exitId :: postId :: joins) :=
          Completes.of_moveTo_protected (by simp) h18 hcR
        have gOQ : SGrows sO sQ :=
          (SGrowsAt.of_grows (Grows.of_liftO h16)).trans
            (SGrowsAt.of_sealCur h17)
        have hpostNe : sQ.fn.curId ≠ postId := by
          have hpQ := ProtectedAt.forward hpO gOQ
          exact fun he => hpQ.away (by simp [he])
        have hfinQ := curFinal_of_move_grows h18 hpostNe
          (ProtectedAt.forward hpO gOQ).away (SGrows.rfl' sR) hcR
        have hsealP : CurOK f sP.fn ⟨[], .jump ⟨postId, xvB⟩⟩ :=
          curOK_of_sealCur hfinQ h17
        have hsP : sP = sO := (M.edgeArgs_inv h16).2
        subst sP
        exact ⟨SGrowsAt.completes_of gOQ hcQ, ⟨_, hsealP⟩,
          fun hbad => nomatch hbad⟩
    have hfrN : RegsFresh RA sN.fn := hfrA.mono aJN.nextVal
    have hboundN : ∀ i : FuncId, i ∈ owned → i < sN.funcs.size := by
      intro i hi
      exact Nat.lt_of_lt_of_le (hbound i hi)
        (Nat.le_trans a0I.funcsSize
          (Nat.le_trans (SGrows.of_grows gIJ).funcsSize aJN.funcsSize))
    have hboundO : ∀ i : FuncId, i ∈ owned → i < sO.funcs.size := by
      intro i hi
      exact Nat.lt_of_lt_of_le (hboundN i hi) gbody.funcsSize
    have hownO : FOwned owned sO done :=
      FOwned.back_fprefix hpTail hboundO hown
    have hbodySim := ihb fenv
      (env.setMany (modifiedX env [post, body]) hParams) RA
      (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets
      sN sO bodyEnv (exitId :: postId :: joins) hfe
      (henv.mono hleA) (huniq.setMany _ _) hfrN hvalidN hpN
      tailBody.1 tailBody.2.1 tailBody.2.2 done owned hdone hboundN hownO htrB
    have hpre := hsimC.trans hsimB
    have gGNall : SGrowsAt 0 sG sN :=
      (((((SGrowsAt.of_sealCur (N := 0) h8).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)).trans
        (SGrowsAt.of_grows gIJ)).trans (aJL.mono (Nat.zero_le _))).trans
        (SGrowsAt.of_sealCur h13)).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h14)
    have finish : ∀ {sPost sPostOut : BState} {postEnv : Option VMap}
        {RB : Regs} {vals : List U256},
        SGrowsAt 0 sO sPost → sPost.fn.curId = postId → sPost.fn.cur = [] →
        CurValid sPost →
        trScope fenv (env.setMany (modifiedX env [post, body]) postParams)
            none rets post sPost = some (postEnv, sPostOut) →
        (do
          if let some envP := postEnv then
            let xvP ← edgeArgs envP (modifiedX env [post, body])
            sealCur (.jump ⟨hId, xvP⟩)
          moveTo exitId
          pure (some (env.setMany (modifiedX env [post, body]) exitParams)))
            sPostOut = some (renv, s₁) →
        Regs.Le RA RB → Regs.BelowEq sN.fn.nextVal RA RB →
        RegsFresh RB sO.fn →
        List.Forall₂ (fun x v => YulSemantics.VEnv.get Vb x = some v)
          (modifiedX env [post, body]) vals →
        (∀ res, JumpTo (model := model) P f postId vals RB stb res →
          ExecFrom (model := model) P f sI.fn R st res) →
        LHOut (model := model) P f rets sA.fn.nextVal sI s₁ R
          renv Vend st stend o := by
      intro sPost sPostOut postEnv RB vals gOP hcurPost hcurPost0 hvalidPost
        htrPost htailPost hleB hbelowB hfrB hvals hcont
      have gpost : SGrows sPost sPostOut := trScope_grows fenv
        (env.setMany (modifiedX env [post, body]) postParams) none rets post
        sPost postEnv sPostOut htrPost
      have hpostBase : s₀.fn.blocks.size ≤ postId := by
        rw [SGrowsAt.newBlock_id h7]
        exact a0F.size
      have hpPost : ProtectedAt (exitId :: joins) sPost.fn := by
        refine ⟨?_, ?_⟩
        · intro i hi
          apply Nat.lt_of_lt_of_le (hpO.below i ?_) gOP.size
          simp only [List.mem_cons] at hi ⊢
          rcases hi with rfl | hi
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hi)
        · rw [hcurPost]
          simp only [List.mem_cons, not_or]
          exact ⟨Nat.ne_of_gt hexitPost, fun hmem =>
            Nat.not_lt_of_ge hpostBase (hp.below postId hmem)⟩
      have hpPostOut : ProtectedAt (exitId :: joins) sPostOut.fn :=
        ProtectedAt.forward hpPost gpost
      have htrPostStmt : trStmt fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets
          (.block post) sPost = some (postEnv, sPostOut) := by
        rw [trStmt]
        exact htrPost
      have hvalidPostOut : CurValid sPostOut :=
        (trStmt_cur hvalidPost htrPostStmt).1
      obtain ⟨hcomplPostOut, hcpPostOut, hfinPostOut⟩ :=
        loopPost_back hvalidPostOut hpPostOut htrPost htailPost hcompl
      have hcomplPost : Completes f sPost.fn (exitId :: joins) :=
        SGrowsAt.completes_of gpost hcomplPostOut
      obtain ⟨hlenP, hrangeP, hsF⟩ := M.mapM_freshVal_length h6
      have hndP : postParams.Nodup := by
        rw [hrangeP]
        exact M.nodup_range' _ _
      have fI : SGrowsAt 0 sF sI :=
        ((SGrowsAt.of_newBlock (N := 0) h7).trans
          (SGrowsAt.of_sealCur h8)).trans
          (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)
      have fN : SGrowsAt 0 sF sN := fI.trans
        (((SGrowsAt.of_grows (N := 0) gIJ).trans
          (aJL.mono (Nat.zero_le _))).trans
          (SGrowsAt.of_sealCur h13) |>.trans
            (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h14))
      have hparamsLtN : ∀ i ∈ postParams, i < sN.fn.nextVal := by
        intro i hi
        rw [hrangeP] at hi
        exact Nat.lt_of_lt_of_le
          (by simpa [hsF] using (M.mem_range'_bounds hi).2) fN.nextVal
      have hparamsLtO : ∀ i ∈ postParams, i < sO.fn.nextVal := by
        intro i hi
        exact Nat.lt_of_lt_of_le (hparamsLtN i hi) gbody.nextVal
      have hnoneP : ∀ i ∈ postParams, RB i = none := by
        intro i hi
        rw [hbelowB i (hparamsLtN i hi)]
        have hiRange := hi
        rw [hrangeP] at hiRange
        have hiLtI : i < sI.fn.nextVal := Nat.lt_of_lt_of_le
          (by simpa [hsF] using (M.mem_range'_bounds hiRange).2) fI.nextVal
        rw [hbelowA i hiLtI]
        apply hclean i
        · exact Nat.le_trans
            (((SGrowsAt.of_grows (N := 0) gAB).trans
              (SGrowsAt.of_newBlock h3)).trans (SGrowsAt.of_grows gCD) |>.trans
              (SGrowsAt.of_newBlock h5)).nextVal
            (M.mem_range'_bounds hiRange).1
        · intro hiH
          rw [hrangeH] at hiH
          have hu := (M.mem_range'_bounds hiH).2
          have hl := (M.mem_range'_bounds hiRange).1
          have hnextCB : sC.fn.nextVal = sB.fn.nextVal := by
            rw [M.newBlock_apply] at h3
            exact (congrArg (fun z => z.fn.nextVal)
              (M.some_pair_inj h3).2).symm
          have hendH : sA.fn.nextVal + (modifiedX env [post, body]).length =
              sC.fn.nextVal := by rw [hnextCB, hsB]
          have huC : i < sC.fn.nextVal := by rwa [hendH] at hu
          have hCE : sC.fn.nextVal ≤ sE.fn.nextVal :=
            (SGrowsAt.of_grows (N := 0) gCD).trans
              (SGrowsAt.of_newBlock h5) |>.nextVal
          exact Nat.not_lt_of_ge (Nat.le_trans hCE hl) huC
      have hbaseP : ∀ i ∈ postParams, sA.fn.nextVal ≤ i := by
        intro i hi
        rw [hrangeP] at hi
        exact Nat.le_trans
          (((SGrowsAt.of_grows (N := 0) gAB).trans
            (SGrowsAt.of_newBlock h3)).trans (SGrowsAt.of_grows gCD) |>.trans
            (SGrowsAt.of_newBlock h5)).nextVal
          (M.mem_range'_bounds hi).1
      have gGPost : SGrowsAt 0 sG sPost :=
        (gGNall.trans (gbody.mono (Nat.zero_le _))).trans gOP
      obtain ⟨pb, hpb, hpp⟩ := gGPost.params postId
        ⟨postParams, [], .ret []⟩ (newBlock_target_get h7)
      have hnextOP : sO.fn.nextVal ≤ sPost.fn.nextVal := gOP.nextVal
      have hVbody : YulSemantics.VEnv.setMany V
          (modifiedX env [post, body]) vals = Vb := by
        have hnames : VEnv.names Vb = VEnv.names V := by
          have hm := (mod_sim hbodyStep).1
          simpa [declsOfStmt] using hm
        have hmod : ModOut [] (modStmts [] body) V Vb := by
          have hm := (mod_sim hbodyStep).2 [] (localsOK_nil V)
          simpa [modStmt] using hm
        exact setMany_eq_of_modOut (xs := modifiedX env [post, body]) henv
          (huniq.setMany _ _) hnames hmod hvals
          (fun x hx => by
            rw [VMap.names_setMany]
            exact modifiedX_mem_names hx)
          (fun x hx hm => mem_modifiedX (by
            rw [VMap.names_setMany] at hx
            exact hx) (by
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
            exact List.mem_append_right _ hm))
      have hleBody : Regs.Le R RB := hleA.trans hleB
      have hbelowBody : Regs.BelowEq sA.fn.nextVal R RB :=
        (hbelowA.mono aAI.nextVal).trans
          (hbelowB.mono (Nat.le_trans aAI.nextVal
            (Nat.le_trans (SGrowsAt.of_grows (N := 0) gIJ).nextVal
              aJN.nextVal)))
      obtain ⟨RP, hleP, hbelowP, hfrP, henvP, hsimP⟩ :=
        sim_loopPostEntry (model := model) (P := P) (f := f) (sBody := sO)
          (base := sA.fn.nextVal) henv hVbody hleBody hbelowBody hndP hnoneP
          hbaseP hparamsLtO hfrB hnextOP hcomplPost hpb hpp hcurPost
          hcurPost0 (by rw [hlenP]; exact hvals.length_eq) hcont
      rw [VMap.setMany_overwrite env (modifiedX_nodup huniq _)
        hlenH.symm hlenP.symm] at henvP
      have hboundPost : ∀ i : FuncId, i ∈ owned → i < sPost.funcs.size := by
        intro i hi
        exact Nat.lt_of_lt_of_le (hbound i hi)
          (Nat.le_trans a0G.funcsSize gGPost.funcsSize)
      have hboundPostOut : ∀ i : FuncId,
          i ∈ owned → i < sPostOut.funcs.size := by
        intro i hi
        exact Nat.lt_of_lt_of_le (hboundPost i hi) gpost.funcsSize
      have hownPostOut : FOwned owned sPostOut done :=
        FOwned.back_fprefix (loopPostTail_fprefix htailPost)
          hboundPostOut hown
      obtain ⟨envP, RPost, hpostEnv, hlePost, hbelowPost, hfrPost,
          henvPost, huniqPost, hsimPost⟩ := ihpost fenv
        (env.setMany (modifiedX env [post, body]) postParams) RP none rets
        sPost sPostOut postEnv (exitId :: joins) hfe henvP
        (huniq.setMany _ _) hfrP hvalidPost hpPost hcomplPostOut hcpPostOut
        hfinPostOut done owned hdone hboundPost hownPostOut htrPostStmt
      obtain rfl : postEnv = some envP := hpostEnv
      change (do
        let xvP ← edgeArgs envP (modifiedX env [post, body])
        sealCur (.jump ⟨hId, xvP⟩)
        moveTo exitId
        pure (some (env.setMany (modifiedX env [post, body]) exitParams)))
          sPostOut = some (renv, s₁) at htailPost
      obtain ⟨xvNext, sEdge, hargsNext, htailPost⟩ := M.bind_inv htailPost
      obtain ⟨uSeal, sSealed, hsealNext, htailPost⟩ := M.bind_inv htailPost
      obtain ⟨uExit, sExit, hmoveExit, htailPost⟩ := M.bind_inv htailPost
      obtain ⟨hrenv, hs₁⟩ := M.pure_inv htailPost
      subst s₁
      obtain ⟨rfl, valsNext, hgetNext, hvalsNext⟩ :=
        edgeArgs_ok henvPost hargsNext
      have hnamesBody : VEnv.names Vb = VEnv.names V := by
        have hm := (mod_sim hbodyStep).1
        simpa [declsOfStmt] using hm
      have hnamesPost : VEnv.names Vp = VEnv.names Vb := by
        have hm := (mod_sim hpost).1
        simpa [declsOfStmt] using hm
      have hnamesNext : VEnv.names Vp = VEnv.names V :=
        hnamesPost.trans hnamesBody
      have hmodBody : ModOut [] (modStmts [] body) V Vb := by
        have hm := (mod_sim hbodyStep).2 [] (localsOK_nil V)
        simpa [modStmt] using hm
      have hmodPost : ModOut [] (modStmts [] post) Vb Vp := by
        have hm := (mod_sim hpost).2 [] (localsOK_nil Vb)
        simpa [modStmt] using hm
      have hmodNext : ModOut []
          (modStmts [] body ++ modStmts [] post) V Vp :=
        ModOut.trans hmodBody hmodPost (fun _ hn => by
          rw [← VEnv.length_names, hnamesBody, VEnv.length_names]
          exact hn)
      have hVnext : YulSemantics.VEnv.setMany V
          (modifiedX env [post, body]) valsNext = Vp :=
        setMany_eq_of_modOut (xs := modifiedX env [post, body]) henv
          (huniq.setMany _ _) hnamesNext hmodNext hvalsNext
          (fun x hx => by
            rw [VMap.names_setMany]
            exact modifiedX_mem_names hx)
          (fun x hx hm => mem_modifiedX (by
            rw [VMap.names_setMany] at hx
            exact hx) (by
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
            rcases List.mem_append.mp hm with hb | hp'
            · exact List.mem_append_right _ hb
            · exact List.mem_append_left _ hp'))
      let RNext := R.setMany hParams valsNext
      have hlenNext : hParams.length = valsNext.length :=
        hlenH.trans hvalsNext.length_eq
      have henvNext : EnvOK (model := model)
          (env.setMany (modifiedX env [post, body]) hParams) Vp RNext := by
        exact hreb valsNext Vp hvalsNext.length_eq hVnext
      have bI : SGrowsAt 0 sB sI :=
        ((((((SGrowsAt.of_newBlock (N := 0) h3).trans
          (SGrowsAt.of_grows gCD)).trans (SGrowsAt.of_newBlock h5)).trans
          (SGrowsAt.of_grows gEF)).trans (SGrowsAt.of_newBlock h7)).trans
          (SGrowsAt.of_sealCur h8)).trans
          (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)
      have hendI : sA.fn.nextVal + (modifiedX env [post, body]).length ≤
          sI.fn.nextVal := by
        have hn := bI.nextVal
        rw [hsB] at hn
        exact hn
      have hfrNext : RegsFresh RNext sI.fn := by
        intro i hi
        dsimp [RNext]
        rw [Regs.setMany_other]
        · exact hfr i hi
        · intro him
          rw [hrangeH] at him
          exact absurd (Nat.lt_of_lt_of_le (M.mem_range'_bounds him).2 hendI)
            (Nat.not_lt_of_ge hi)
      have hcleanNext : HeaderClean sA.fn.nextVal hParams RNext := by
        intro i hi hnot
        dsimp [RNext]
        rw [Regs.setMany_other hnot]
        exact hclean i hi hnot
      have hrebNext : HeaderRebind (model := model)
          (env.setMany (modifiedX env [post, body]) hParams)
          (modifiedX env [post, body]) hParams Vp RNext := by
        intro vals' W hlen' hset'
        dsimp [RNext]
        rw [Regs.setMany_overwrite R hndH hlenNext (hlenH.trans hlen')]
        apply hreb vals' W hlen'
        rw [← hset', ← hVnext,
          VEnv.setMany_overwrite V (modifiedX_nodup huniq _)
            hvalsNext.length_eq hlen']
      let layout' : LoopLayout fenv env rets c post body s₀ sExit renv :=
        ⟨xvals, sA, h1, hParams, sB, h2, hId, sC, h3,
         exitParams, sD, h4, exitId, sE, h5, postParams, sF, h6,
         postId, sG, h7, sH, h8, sI, h9, cvId, sJ, h10,
         bodyId, sK, h11, hX, sL, h12, sM, h13, sN, h14,
         bodyEnv, sO, h15, htr⟩
      have hrec := ihloop fenv env rets s₀ sExit renv joins layout'
        hfe huniq hvalid hp hcompl hcp _hfin done owned hdone hbound hown
        RNext henvNext hfrNext hcleanNext hrebNext
      have cI : SGrowsAt 0 sC sI :=
        (((((SGrowsAt.of_grows (N := 0) gCD).trans
          (SGrowsAt.of_newBlock h5)).trans (SGrowsAt.of_grows gEF)).trans
          (SGrowsAt.of_newBlock h7)).trans (SGrowsAt.of_sealCur h8)).trans
          (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)
      obtain ⟨hbH, hhbH, hhpH⟩ := cI.params hId
        ⟨hParams, [], .ret []⟩ (newBlock_target_get h3)
      have hleToPost : Regs.Le R RPost := hleP.trans hlePost
      have hleBack : Regs.Le RNext (RPost.setMany hParams valsNext) := by
        exact Regs.Le.setManyBoth hleToPost
      have hlenBack : hbH.params.length = valsNext.length := by
        rw [hhpH]
        exact hlenNext
      have gPostSeal : SGrows sEdge sSealed :=
        (SGrowsAt.of_grows (Grows.of_liftO hargsNext)).trans
          (SGrowsAt.of_sealCur hsealNext)
      have hpSealed : ProtectedAt (exitId :: joins) sSealed.fn :=
        ProtectedAt.forward hpPostOut gPostSeal
      have hcExit : Completes f sExit.fn (exitId :: joins) := by
        exact hcompl.protect exitId
      have hcSealed : Completes f sSealed.fn (exitId :: joins) :=
        Completes.of_moveTo_protected (by simp) hmoveExit hcExit
      have hneExit : sSealed.fn.curId ≠ exitId := fun he =>
        hpSealed.away (by simp [he])
      have hfinSealed : CurFinal f sSealed.fn :=
        curFinal_of_move_grows hmoveExit hneExit hpSealed.away
          (SGrows.rfl' sExit) hcExit
      have hcurBack : CurOK f sEdge.fn
          ⟨[], .jump ⟨hId, xvNext⟩⟩ :=
        curOK_of_sealCur hfinSealed hsealNext
      have hbridge : ∀ res,
          ExecFrom (model := model) P f sI.fn RNext stp res →
          ExecFrom (model := model) P f sI.fn R st res := by
        intro res hex
        have hjump : JumpTo (model := model) P f hId valsNext RPost stp res :=
          jumpTo_of_completes hcI hhbH hcurI hcurI0 hlenBack (by
            simpa only [hhpH] using hex.mono hleBack)
        exact hsimP res (hsimPost res
          (execFrom_jump hcurBack hgetNext hjump))
      have hbaseH : ∀ i ∈ hParams, sA.fn.nextVal ≤ i := by
        intro i hi
        rw [hrangeH] at hi
        exact (M.mem_range'_bounds hi).1
      have hbelowNext : Regs.BelowEq sA.fn.nextVal R RNext :=
        Regs.BelowEq.setMany hbaseH
      cases o with
      | normal =>
        obtain ⟨envEnd, REnd, hrenvEnd, hbelowEnd, hfrEnd, henvEnd,
          huniqEnd, hsimEnd⟩ := hrec
        exact ⟨envEnd, REnd, hrenvEnd, hbelowNext.trans hbelowEnd,
          hfrEnd, henvEnd, huniqEnd, fun res hex => hbridge res (hsimEnd res hex)⟩
      | halt => exact hbridge (.halt stend) hrec
      | leave =>
        obtain ⟨rs, retVals, hrets, hretVals, hex⟩ := hrec
        exact ⟨rs, retVals, hrets, hretVals, hbridge (.ret retVals stend) hex⟩
      | «break» => exact hrec.elim
      | «continue» => exact hrec.elim
    rcases hob with rfl | rfl
    · obtain ⟨envB, RB, hbodyEnv, hleB, hbelowB, hfrB, henvB, _huniqB,
          hsimBody⟩ := hbodySim
      obtain rfl : bodyEnv = some envB := hbodyEnv
      obtain ⟨xvB, sP, h16, htr⟩ := M.bind_inv htr
      obtain ⟨uQ, sQ, h17, htr⟩ := M.bind_inv htr
      obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
      obtain ⟨postEnv, sS, h19, htailPost⟩ := M.bind_inv htr
      obtain ⟨rfl, vals, hgetB, hvals⟩ := edgeArgs_ok henvB h16
      have gOQ : SGrows sP sQ :=
        (SGrowsAt.of_grows (Grows.of_liftO h16)).trans
          (SGrowsAt.of_sealCur h17)
      have hpQ := ProtectedAt.forward hpO gOQ
      have gp := trScope_grows fenv
        (env.setMany (modifiedX env [post, body]) postParams) none rets post
        sR postEnv sS h19
      have gQR : SGrowsAt 0 sQ sR :=
        SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h18
      have hvalidR : CurValid sR := CurValid.of_moveTo
        (Nat.lt_of_lt_of_le (newBlock_target_lt h7)
          ((gGNall.trans (gbody.mono (Nat.zero_le _))).trans
            (gOQ.mono (Nat.zero_le _))).size)
        h18
      have hpostBase : s₀.fn.blocks.size ≤ postId := by
        rw [SGrowsAt.newBlock_id h7]
        exact a0F.size
      have hpRPost : ProtectedAt (exitId :: joins) sR.fn := by
        refine ⟨?_, ?_⟩
        · intro i hi
          have hi' : i ∈ exitId :: postId :: joins := by
            simp only [List.mem_cons] at hi ⊢
            rcases hi with rfl | hi
            · exact Or.inl rfl
            · exact Or.inr (Or.inr hi)
          exact Nat.lt_of_lt_of_le (hpQ.below i hi') gQR.size
        · have hcurR : sR.fn.curId = postId := by
            rw [M.moveTo_apply] at h18
            exact (congrArg (fun z => z.fn.curId)
              (M.some_pair_inj h18).2).symm
          rw [hcurR]
          simp only [List.mem_cons, not_or]
          exact ⟨Nat.ne_of_gt hexitPost, fun hmem =>
            Nat.not_lt_of_ge hpostBase (hp.below postId hmem)⟩
      have hvalidS : CurValid sS :=
        (trStmt_cur hvalidR (by rw [trStmt]; exact h19)).1
      have hpS : ProtectedAt (exitId :: joins) sS.fn :=
        ProtectedAt.forward hpRPost gp
      have hback := loopPost_back hvalidS hpS h19 htailPost hcompl
      have hcR := (SGrowsAt.completes_of gp hback.1).protect postId
      have hpQ' : ProtectedAt (postId :: exitId :: joins) sQ.fn := by
        refine ⟨?_, ?_⟩
        · intro i hi
          apply hpQ.below i
          simp only [List.mem_cons] at hi ⊢
          rcases hi with rfl | rfl | hi
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hi)
        · intro hi
          apply hpQ.away
          simp only [List.mem_cons] at hi ⊢
          rcases hi with h | h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
      have hfinQ := curFinal_of_move_grows h18
        (fun he => hpQ'.away (by simp [he])) hpQ'.away
        (SGrows.rfl' sR) hcR
      have hcurJump : CurOK f sP.fn ⟨[], .jump ⟨postId, xvB⟩⟩ :=
        curOK_of_sealCur hfinQ h17
      have hcont : ∀ res, JumpTo (model := model) P f postId vals RB stb res →
          ExecFrom (model := model) P f sI.fn R st res := by
        intro res hj
        exact hpre res (hsimBody res (execFrom_jump hcurJump hgetB hj))
      exact finish
        (((SGrowsAt.of_grows (N := 0) (Grows.of_liftO h16)).trans
          (SGrowsAt.of_sealCur h17)).trans
          (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h18))
        (by rw [M.moveTo_apply] at h18
            exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h18).2).symm)
        (by rw [M.moveTo_apply] at h18
            simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h18).2)
        (CurValid.of_moveTo
          (Nat.lt_of_lt_of_le (newBlock_target_lt h7)
            ((gGNall.trans (gbody.mono (Nat.zero_le _))).trans
              (gOQ.mono (Nat.zero_le _))).size)
          h18)
        h19 htailPost hleB hbelowB hfrB hvals hcont
    · obtain ⟨lc, RB, vals, hlc, hleB, hbelowB, hfrB, hvals, hcontB⟩ :=
        hbodySim
      have hlc' : lc = ⟨exitId, postId, modifiedX env [post, body]⟩ :=
        Option.some.inj hlc.symm
      subst lc
      cases bodyEnv with
      | none =>
        change (do
          moveTo postId
          let envP := env.setMany (modifiedX env [post, body]) postParams
          let renvP ← trScope fenv envP none rets post
          if let some envP' := renvP then
            let xvP ← edgeArgs envP' (modifiedX env [post, body])
            sealCur (.jump ⟨hId, xvP⟩)
          moveTo exitId
          pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sO =
            some (renv, s₁) at htr
        obtain ⟨uP, sP, h16, htr⟩ := M.bind_inv htr
        obtain ⟨postEnv, sQ, h17, htailPost⟩ := M.bind_inv htr
        have hcont : ∀ res,
            JumpTo (model := model) P f postId vals RB stb res →
            ExecFrom (model := model) P f sI.fn R st res :=
          fun res hj => hpre res (hcontB res hj)
        exact finish (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h16)
          (by rw [M.moveTo_apply] at h16
              exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h16).2).symm)
          (by rw [M.moveTo_apply] at h16
              simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h16).2)
          (CurValid.of_moveTo
            (Nat.lt_of_lt_of_le (newBlock_target_lt h7)
              (gGNall.trans (gbody.mono (Nat.zero_le _))).size) h16)
          h17 htailPost hleB hbelowB hfrB hvals hcont
      | some envB =>
        obtain ⟨xvB, sP, h16, htr⟩ := M.bind_inv htr
        obtain ⟨uQ, sQ, h17, htr⟩ := M.bind_inv htr
        obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
        obtain ⟨postEnv, sS, h19, htailPost⟩ := M.bind_inv htr
        have gOQ : SGrows sO sQ :=
          (SGrowsAt.of_grows (Grows.of_liftO h16)).trans
            (SGrowsAt.of_sealCur h17)
        have hcont : ∀ res,
            JumpTo (model := model) P f postId vals RB stb res →
            ExecFrom (model := model) P f sI.fn R st res :=
          fun res hj => hpre res (hcontB res hj)
        exact finish
          ((gOQ.mono (Nat.zero_le _)).trans
            (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h18))
          (by rw [M.moveTo_apply] at h18
              exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h18).2).symm)
          (by rw [M.moveTo_apply] at h18
              simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h18).2)
          (CurValid.of_moveTo
            (Nat.lt_of_lt_of_le (newBlock_target_lt h7)
              ((gGNall.trans (gbody.mono (Nat.zero_le _))).trans
                (gOQ.mono (Nat.zero_le _))).size)
            h18)
          h19 htailPost hleB hbelowB hfrB hvals hcont

  -- `sim_loopBodyNonNormal` also closes break: it consumes the body's
  -- `JumpTo exitId`, binds `exitParams`, and rebuilds `EnvOK` at the exit.
  | @loopPostHalt funs V st c post body cv st1 Vb stb ob Vp stp
      hc hnz hbodyStep hob hpost ihc ihb ihpost =>
    intro fenv env rets s₀ s₁ renv joins layout hfe huniq hvalid hp
      hcompl hcp _hfin done owned hdone hbound hown R henv hfr hclean hreb
    have hpTail := layout.tail_fprefix
    rcases layout with
      ⟨xvals, sA, h1, hParams, sB, h2, hId, sC, h3,
       exitParams, sD, h4, exitId, sE, h5, postParams, sF, h6,
       postId, sG, h7, sH, h8, sI, h9, cvId, sJ, h10,
       bodyId, sK, h11, hX, sL, h12, sM, h13, sN, h14,
       bodyEnv, sO, h15, htr⟩
    simp only [LoopLayout.hParams, LoopLayout.sI, LoopLayout.sA] at henv hfr hclean hreb ⊢
    have g0A : Grows s₀ sA := Grows.of_liftO h1
    have gAB : Grows sA sB := Grows.of_mapM_freshVal h2
    have gCD : Grows sC sD := Grows.of_mapM_freshVal h4
    have gEF : Grows sE sF := Grows.of_mapM_freshVal h6
    have a0A : SGrowsAt s₀.fn.blocks.size s₀ sA := SGrowsAt.of_grows g0A
    have a0B := a0A.trans (SGrowsAt.of_grows gAB)
    have a0C := a0B.trans (SGrowsAt.of_newBlock h3)
    have a0D := a0C.trans (SGrowsAt.of_grows gCD)
    have a0E := a0D.trans (SGrowsAt.of_newBlock h5)
    have a0F := a0E.trans (SGrowsAt.of_grows gEF)
    have a0G := a0F.trans (SGrowsAt.of_newBlock h7)
    have a0H := a0G.trans (SGrowsAt.of_sealCur h8)
    have hheadBase : s₀.fn.blocks.size ≤ hId := by
      rw [SGrowsAt.newBlock_id h3]
      exact a0B.size
    have a0I := a0H.trans (SGrowsAt.of_moveTo (Or.inl hheadBase) h9)
    have aAI : SGrowsAt 0 sA sI :=
      (((((((SGrowsAt.of_grows (N := 0) gAB).trans
        (SGrowsAt.of_newBlock h3)).trans (SGrowsAt.of_grows gCD)).trans
        (SGrowsAt.of_newBlock h5)).trans (SGrowsAt.of_grows gEF)).trans
        (SGrowsAt.of_newBlock h7)).trans (SGrowsAt.of_sealCur h8)).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)
    have gIJ : Grows sI sJ := trExpr_grows c fenv
      (env.setMany (modifiedX env [post, body]) hParams) sI sJ cvId h10
    have aJK : SGrowsAt sJ.fn.blocks.size sJ sK := SGrowsAt.of_newBlock h11
    have gKL : Grows sK sL := Grows.of_liftO h12
    have aJL := aJK.trans (SGrowsAt.of_grows gKL)
    have aJM := aJL.trans (SGrowsAt.of_sealCur h13)
    have hbodyBase : sJ.fn.blocks.size ≤ bodyId := by
      rw [SGrowsAt.newBlock_id h11]
    have aJN := aJM.trans (SGrowsAt.of_moveTo (Or.inl hbodyBase) h14)
    have eF : SGrowsAt 0 sE sF := SGrowsAt.of_grows gEF
    have eG := eF.trans (SGrowsAt.of_newBlock h7)
    have eH := eG.trans (SGrowsAt.of_sealCur h8)
    have eI := eH.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)
    have eJ := eI.trans (SGrowsAt.of_grows gIJ)
    have eK := eJ.trans (SGrowsAt.of_newBlock h11)
    have eL := eK.trans (SGrowsAt.of_grows gKL)
    have eM := eL.trans (SGrowsAt.of_sealCur h13)
    have eN := eM.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h14)
    have hcN : Completes f sN.fn (exitId :: postId :: joins) := by
      have gb := trScope_grows fenv
        (env.setMany (modifiedX env [post, body]) hParams)
        (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
        sN bodyEnv sO h15
      cases bodyEnv with
      | none =>
        change (do
          moveTo postId
          let envP := env.setMany (modifiedX env [post, body]) postParams
          let renvP ← trScope fenv envP none rets post
          if let some envP' := renvP then
            let xvP ← edgeArgs envP' (modifiedX env [post, body])
            sealCur (.jump ⟨hId, xvP⟩)
          moveTo exitId
          pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sO =
            some (renv, s₁) at htr
        obtain ⟨uP, sP, h16, htr⟩ := M.bind_inv htr
        obtain ⟨postEnv, sQ, h17, htr⟩ := M.bind_inv htr
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sP postEnv sQ h17
        cases postEnv with
        | none =>
          change (do
            moveTo exitId
            pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sQ =
              some (renv, s₁) at htr
          obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
          obtain ⟨-, hs₁⟩ := M.pure_inv htr
          subst s₁
          have hcQ : Completes f sQ.fn (exitId :: postId :: joins) :=
            Completes.of_moveTo_protected (by simp) h18
              ((hcompl.protect postId).protect exitId)
          have hcP := SGrowsAt.completes_of gp hcQ
          have hcO := Completes.of_moveTo_protected (by simp) h16 hcP
          exact SGrowsAt.completes_of gb hcO
        | some envP =>
          obtain ⟨xvP, sR, h18, htr⟩ := M.bind_inv htr
          obtain ⟨uS, sS, h19, htr⟩ := M.bind_inv htr
          obtain ⟨uT, sT, h20, htr⟩ := M.bind_inv htr
          obtain ⟨-, hs₁⟩ := M.pure_inv htr
          subst s₁
          have hcS : Completes f sS.fn (exitId :: postId :: joins) :=
            Completes.of_moveTo_protected (by simp) h20
              ((hcompl.protect postId).protect exitId)
          have gQS : SGrows sQ sS :=
            (SGrowsAt.of_grows (Grows.of_liftO h18)).trans
              (SGrowsAt.of_sealCur h19)
          have hcQ := SGrowsAt.completes_of gQS hcS
          have hcP := SGrowsAt.completes_of gp hcQ
          have hcO := Completes.of_moveTo_protected (by simp) h16 hcP
          exact SGrowsAt.completes_of gb hcO
      | some envB =>
        obtain ⟨xvB, sP, h16, htr⟩ := M.bind_inv htr
        obtain ⟨uQ, sQ, h17, htr⟩ := M.bind_inv htr
        obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
        obtain ⟨postEnv, sS, h19, htr⟩ := M.bind_inv htr
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sR postEnv sS h19
        have gOQ : SGrows sO sQ :=
          (SGrowsAt.of_grows (Grows.of_liftO h16)).trans
            (SGrowsAt.of_sealCur h17)
        cases postEnv with
        | none =>
          change (do
            moveTo exitId
            pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sS =
              some (renv, s₁) at htr
          obtain ⟨uT, sT, h20, htr⟩ := M.bind_inv htr
          obtain ⟨-, hs₁⟩ := M.pure_inv htr
          subst s₁
          have hcS : Completes f sS.fn (exitId :: postId :: joins) :=
            Completes.of_moveTo_protected (by simp) h20
              ((hcompl.protect postId).protect exitId)
          have hcR := SGrowsAt.completes_of gp hcS
          have hcQ := Completes.of_moveTo_protected (by simp) h18 hcR
          have hcO := SGrowsAt.completes_of gOQ hcQ
          exact SGrowsAt.completes_of gb hcO
        | some envP =>
          obtain ⟨xvP, sT, h20, htr⟩ := M.bind_inv htr
          obtain ⟨uU, sU, h21, htr⟩ := M.bind_inv htr
          obtain ⟨uW, sW, h22, htr⟩ := M.bind_inv htr
          obtain ⟨-, hs₁⟩ := M.pure_inv htr
          subst s₁
          have hcU : Completes f sU.fn (exitId :: postId :: joins) :=
            Completes.of_moveTo_protected (by simp) h22
              ((hcompl.protect postId).protect exitId)
          have gSU : SGrows sS sU :=
            (SGrowsAt.of_grows (Grows.of_liftO h20)).trans
              (SGrowsAt.of_sealCur h21)
          have hcS := SGrowsAt.completes_of gSU hcU
          have hcR := SGrowsAt.completes_of gp hcS
          have hcQ := Completes.of_moveTo_protected (by simp) h18 hcR
          have hcO := SGrowsAt.completes_of gOQ hcQ
          exact SGrowsAt.completes_of gb hcO
    have hcJ : Completes f sJ.fn (exitId :: postId :: joins) :=
      SGrowsAt.completes_of aJN hcN
    have hcI : Completes f sI.fn (exitId :: postId :: joins) :=
      SGrowsAt.completes_of (SGrowsAt.of_grows gIJ) hcJ
    have hcurI : sI.fn.curId = hId := by
      rw [M.moveTo_apply] at h9
      exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h9).2).symm
    have hcurI0 : sI.fn.cur = [] := by
      rw [M.moveTo_apply] at h9
      simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h9).2
    have hheadExit : hId < exitId := by
      rw [SGrowsAt.newBlock_id h5]
      exact Nat.lt_of_lt_of_le (newBlock_target_lt h3)
        (SGrowsAt.of_grows (N := 0) gCD).size
    have hexitPost : exitId < postId := by
      rw [SGrowsAt.newBlock_id h7]
      exact Nat.lt_of_lt_of_le (newBlock_target_lt h5)
        (SGrowsAt.of_grows (N := 0) gEF).size
    have hpI0 : ProtectedAt joins sI.fn := ProtectedAt.forward hp a0I
    have hpI : ProtectedAt (exitId :: postId :: joins) sI.fn := by
      refine ⟨?_, ?_⟩
      · intro i hi
        simp only [List.mem_cons] at hi
        rcases hi with rfl | rfl | hi
        · exact Nat.lt_of_lt_of_le (newBlock_target_lt h5) eI.size
        · exact Nat.lt_of_lt_of_le (newBlock_target_lt h7)
            ((SGrowsAt.of_sealCur (N := 0) h8).trans
              (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h9)).size
        · exact hpI0.below i hi
      · simp only [List.mem_cons, not_or]
        exact ⟨by rw [hcurI]; exact Nat.ne_of_lt hheadExit,
          by rw [hcurI]; exact Nat.ne_of_lt (Nat.lt_trans hheadExit hexitPost),
          hpI0.away⟩
    have hvalidI : CurValid sI := by
      apply CurValid.of_moveTo _ h9
      exact Nat.lt_of_lt_of_le (newBlock_target_lt h3)
        (((((SGrowsAt.of_grows (N := 0) gCD).trans
          (SGrowsAt.of_newBlock h5)).trans
          (SGrowsAt.of_grows gEF)).trans
          (SGrowsAt.of_newBlock h7)).trans
          (SGrowsAt.of_sealCur h8)).size
    have hvalidJ : CurValid sJ := hvalidI.of_grows gIJ
    have csJL : CurSame sJ sL :=
      (CurSame.of_newBlock h11).trans (CurSame.of_grows gKL)
    have hcurM : sM.fn.curId = sJ.fn.curId := by
      rw [(sealCur_cur h13).choose_spec.1, csJL.1]
    have hbodyNe : sM.fn.curId ≠ bodyId := by
      rw [hcurM, SGrowsAt.newBlock_id h11]
      exact Nat.ne_of_lt hvalidJ
    have hpM : ProtectedAt (exitId :: postId :: joins) sM.fn := by
      have hgIM : SGrowsAt sI.fn.blocks.size sI sM :=
        ((SGrowsAt.of_grows (N := sI.fn.blocks.size) gIJ).trans
          (aJL.mono
            (SGrowsAt.of_grows (N := sI.fn.blocks.size) gIJ).size)).trans
          (SGrowsAt.of_sealCur h13)
      exact ProtectedAt.forward hpI hgIM
    have hfinM : CurFinal f sM.fn :=
      curFinal_of_move_grows h14 hbodyNe hpM.away (SGrows.rfl' sN) hcN
    have hbranchL : CurOK f sL.fn
        ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨exitId, hX⟩⟩ :=
      curOK_of_sealCur hfinM h13
    have hbranchJ : CurOK f sJ.fn
        ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨exitId, hX⟩⟩ :=
      CurOK.back_of_cur_eq csJL.1 (by
        have hnew : sK.fn.cur = sJ.fn.cur := by
          rw [M.newBlock_apply] at h11
          simpa using (congrArg (fun z => z.fn.cur) (M.some_pair_inj h11).2).symm
        have hedge : sL = sK := (M.edgeArgs_inv h12).2
        rw [hedge, hnew]) hbranchL
    have hcpJ : CurPlaced f sJ.fn := ⟨_, hbranchJ⟩
    have hcpI : CurPlaced f sI.fn := curPlaced_back_grows gIJ hcpJ
    obtain ⟨hlenH, hrangeH, hsB⟩ := M.mapM_freshVal_length h2
    have hndH : hParams.Nodup := by
      rw [hrangeH]
      exact M.nodup_range' _ _
    obtain ⟨RA, hleA, hbelowA, hfrA, hcv, hsimC⟩ := ihc.1 fenv
      (env.setMany (modifiedX env [post, body]) hParams) R sI sJ cvId cv
      (exitId :: postId :: joins) hfe henv hfr hpI hcJ hcpJ rfl h10
    have hnz' : cv ≠ 0 := by simpa only [yulD_zero] using hnz
    have aKN : SGrowsAt 0 sK sN :=
      ((SGrowsAt.of_grows gKL).trans (SGrowsAt.of_sealCur h13)).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h14)
    obtain ⟨bb, hbb, hbp⟩ := aKN.params bodyId ⟨[], [], .ret []⟩
      (newBlock_target_get h11)
    have hcurN : sN.fn.curId = bodyId := by
      rw [M.moveTo_apply] at h14
      exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h14).2).symm
    have hcurN0 : sN.fn.cur = [] := by
      rw [M.moveTo_apply] at h14
      simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h14).2
    have hsimB := simS_branchTrue_body (model := model) (P := P) (f := f)
      (st := st1) hcN hbranchJ hcv hnz' hbb hbp hcurN hcurN0
    have hvalidN : CurValid sN := by
      apply CurValid.of_moveTo _ h14
      exact Nat.lt_of_lt_of_le (newBlock_target_lt h11)
        ((SGrowsAt.of_grows (N := 0) gKL).trans
          (SGrowsAt.of_sealCur h13)).size
    have aIJ : SGrows sI sJ := SGrowsAt.of_grows gIJ
    have gIN : SGrows sI sN :=
      SGrowsAt.trans aIJ (aJN.mono aIJ.size)
    have hpN : ProtectedAt (exitId :: postId :: joins) sN.fn :=
      ProtectedAt.forward hpI gIN
    have gbody : SGrows sN sO := trScope_grows fenv
      (env.setMany (modifiedX env [post, body]) hParams)
      (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
      sN bodyEnv sO h15
    have hpO : ProtectedAt (exitId :: postId :: joins) sO.fn :=
      ProtectedAt.forward hpN gbody
    have htrB : trStmt fenv
        (env.setMany (modifiedX env [post, body]) hParams)
        (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets
        (.block body) sN = some (bodyEnv, sO) := by
      rw [trStmt]
      exact h15
    have hvalidO : CurValid sO := (trStmt_cur hvalidN htrB).1
    have tailBody :
        Completes f sO.fn (exitId :: postId :: joins) ∧
        CurPlaced f sO.fn ∧
        (bodyEnv = none → CurFinal f sO.fn) := by
      cases bodyEnv with
      | none =>
        change (do
          moveTo postId
          let envP := env.setMany (modifiedX env [post, body]) postParams
          let renvP ← trScope fenv envP none rets post
          if let some envP' := renvP then
            let xvP ← edgeArgs envP' (modifiedX env [post, body])
            sealCur (.jump ⟨hId, xvP⟩)
          moveTo exitId
          pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sO =
            some (renv, s₁) at htr
        obtain ⟨uP, sP, h16, htr⟩ := M.bind_inv htr
        obtain ⟨postEnv, sQ, h17, htr⟩ := M.bind_inv htr
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sP postEnv sQ h17
        have hcP : Completes f sP.fn (exitId :: postId :: joins) := by
          cases postEnv with
          | none =>
            change (do
              moveTo exitId
              pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sQ =
                some (renv, s₁) at htr
            obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
            obtain ⟨-, hs₁⟩ := M.pure_inv htr
            subst s₁
            have hcQ : Completes f sQ.fn (exitId :: postId :: joins) :=
              Completes.of_moveTo_protected (by simp) h18
                ((hcompl.protect postId).protect exitId)
            exact SGrowsAt.completes_of gp hcQ
          | some envP =>
            obtain ⟨xvP, sR, h18, htr⟩ := M.bind_inv htr
            obtain ⟨uS, sS, h19, htr⟩ := M.bind_inv htr
            obtain ⟨uT, sT, h20, htr⟩ := M.bind_inv htr
            obtain ⟨-, hs₁⟩ := M.pure_inv htr
            subst s₁
            have hcS : Completes f sS.fn (exitId :: postId :: joins) :=
              Completes.of_moveTo_protected (by simp) h20
                ((hcompl.protect postId).protect exitId)
            have gQS : SGrows sQ sS :=
              (SGrowsAt.of_grows (Grows.of_liftO h18)).trans
                (SGrowsAt.of_sealCur h19)
            exact SGrowsAt.completes_of gp
              (SGrowsAt.completes_of gQS hcS)
        have hpostNe : sO.fn.curId ≠ postId := fun he =>
          hpO.away (by simp [he])
        have hcurO0 := trScope_none_cur_nil fenv
          (env.setMany (modifiedX env [post, body]) hParams)
          (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
          sN sO h15
        have hcomplO := Completes.of_moveTo_protected (by simp) h16 hcP
        have hfinO := curFinal_of_move_grows h16 hpostNe hpO.away
          (SGrows.rfl' sP) hcP
        exact ⟨hcomplO,
          CurPlaced.of_moveTo_empty hvalidO hcurO0 hpostNe h16 hpO.away hcP,
          fun _ => hfinO⟩
      | some envB =>
        obtain ⟨xvB, sP, h16, htr⟩ := M.bind_inv htr
        obtain ⟨uQ, sQ, h17, htr⟩ := M.bind_inv htr
        obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
        obtain ⟨postEnv, sS, h19, htr⟩ := M.bind_inv htr
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sR postEnv sS h19
        have hcR : Completes f sR.fn (exitId :: postId :: joins) := by
          cases postEnv with
          | none =>
            change (do
              moveTo exitId
              pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sS =
                some (renv, s₁) at htr
            obtain ⟨uT, sT, h20, htr⟩ := M.bind_inv htr
            obtain ⟨-, hs₁⟩ := M.pure_inv htr
            subst s₁
            have hcS : Completes f sS.fn (exitId :: postId :: joins) :=
              Completes.of_moveTo_protected (by simp) h20
                ((hcompl.protect postId).protect exitId)
            exact SGrowsAt.completes_of gp hcS
          | some envP =>
            obtain ⟨xvP, sT, h20, htr⟩ := M.bind_inv htr
            obtain ⟨uU, sU, h21, htr⟩ := M.bind_inv htr
            obtain ⟨uW, sW, h22, htr⟩ := M.bind_inv htr
            obtain ⟨-, hs₁⟩ := M.pure_inv htr
            subst s₁
            have hcU : Completes f sU.fn (exitId :: postId :: joins) :=
              Completes.of_moveTo_protected (by simp) h22
                ((hcompl.protect postId).protect exitId)
            have gSU : SGrows sS sU :=
              (SGrowsAt.of_grows (Grows.of_liftO h20)).trans
                (SGrowsAt.of_sealCur h21)
            exact SGrowsAt.completes_of gp
              (SGrowsAt.completes_of gSU hcU)
        have hcQ : Completes f sQ.fn (exitId :: postId :: joins) :=
          Completes.of_moveTo_protected (by simp) h18 hcR
        have gOQ : SGrows sO sQ :=
          (SGrowsAt.of_grows (Grows.of_liftO h16)).trans
            (SGrowsAt.of_sealCur h17)
        have hpostNe : sQ.fn.curId ≠ postId := by
          have hpQ := ProtectedAt.forward hpO gOQ
          exact fun he => hpQ.away (by simp [he])
        have hfinQ := curFinal_of_move_grows h18 hpostNe
          (ProtectedAt.forward hpO gOQ).away (SGrows.rfl' sR) hcR
        have hsealP : CurOK f sP.fn ⟨[], .jump ⟨postId, xvB⟩⟩ :=
          curOK_of_sealCur hfinQ h17
        have hsP : sP = sO := (M.edgeArgs_inv h16).2
        subst sP
        exact ⟨SGrowsAt.completes_of gOQ hcQ, ⟨_, hsealP⟩,
          fun hbad => nomatch hbad⟩
    have hfrN : RegsFresh RA sN.fn := hfrA.mono aJN.nextVal
    have hboundN : ∀ i : FuncId, i ∈ owned → i < sN.funcs.size := by
      intro i hi
      exact Nat.lt_of_lt_of_le (hbound i hi)
        (Nat.le_trans a0I.funcsSize
          (Nat.le_trans (SGrows.of_grows gIJ).funcsSize aJN.funcsSize))
    have hboundO : ∀ i : FuncId, i ∈ owned → i < sO.funcs.size := by
      intro i hi
      exact Nat.lt_of_lt_of_le (hboundN i hi) gbody.funcsSize
    have hownO : FOwned owned sO done :=
      FOwned.back_fprefix hpTail hboundO hown
    have hbodySim := ihb fenv
      (env.setMany (modifiedX env [post, body]) hParams) RA
      (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets
      sN sO bodyEnv (exitId :: postId :: joins) hfe
      (henv.mono hleA) (huniq.setMany _ _) hfrN hvalidN hpN
      tailBody.1 tailBody.2.1 tailBody.2.2 done owned hdone hboundN hownO htrB
    have hpre := hsimC.trans hsimB
    have gGNall : SGrowsAt 0 sG sN :=
      (((((SGrowsAt.of_sealCur (N := 0) h8).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)).trans
        (SGrowsAt.of_grows gIJ)).trans (aJL.mono (Nat.zero_le _))).trans
        (SGrowsAt.of_sealCur h13)).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h14)
    have finish : ∀ {sPost sPostOut : BState} {postEnv : Option VMap}
        {RB : Regs} {vals : List U256},
        SGrowsAt 0 sO sPost → sPost.fn.curId = postId → sPost.fn.cur = [] →
        CurValid sPost →
        trScope fenv (env.setMany (modifiedX env [post, body]) postParams)
            none rets post sPost = some (postEnv, sPostOut) →
        (do
          if let some envP := postEnv then
            let xvP ← edgeArgs envP (modifiedX env [post, body])
            sealCur (.jump ⟨hId, xvP⟩)
          moveTo exitId
          pure (some (env.setMany (modifiedX env [post, body]) exitParams)))
            sPostOut = some (renv, s₁) →
        Regs.Le RA RB → Regs.BelowEq sN.fn.nextVal RA RB →
        RegsFresh RB sO.fn →
        List.Forall₂ (fun x v => YulSemantics.VEnv.get Vb x = some v)
          (modifiedX env [post, body]) vals →
        (∀ res, JumpTo (model := model) P f postId vals RB stb res →
          ExecFrom (model := model) P f sI.fn R st res) →
        LHOut (model := model) P f rets sA.fn.nextVal sI s₁ R
          renv Vp st stp .halt := by
      intro sPost sPostOut postEnv RB vals gOP hcurPost hcurPost0 hvalidPost
        htrPost htailPost hleB hbelowB hfrB hvals hcont
      have gpost : SGrows sPost sPostOut := trScope_grows fenv
        (env.setMany (modifiedX env [post, body]) postParams) none rets post
        sPost postEnv sPostOut htrPost
      have hpostBase : s₀.fn.blocks.size ≤ postId := by
        rw [SGrowsAt.newBlock_id h7]
        exact a0F.size
      have hpPost : ProtectedAt (exitId :: joins) sPost.fn := by
        refine ⟨?_, ?_⟩
        · intro i hi
          apply Nat.lt_of_lt_of_le (hpO.below i ?_) gOP.size
          simp only [List.mem_cons] at hi ⊢
          rcases hi with rfl | hi
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hi)
        · rw [hcurPost]
          simp only [List.mem_cons, not_or]
          exact ⟨Nat.ne_of_gt hexitPost, fun hmem =>
            Nat.not_lt_of_ge hpostBase (hp.below postId hmem)⟩
      have hpPostOut : ProtectedAt (exitId :: joins) sPostOut.fn :=
        ProtectedAt.forward hpPost gpost
      have htrPostStmt : trStmt fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets
          (.block post) sPost = some (postEnv, sPostOut) := by
        rw [trStmt]
        exact htrPost
      have hvalidPostOut : CurValid sPostOut :=
        (trStmt_cur hvalidPost htrPostStmt).1
      obtain ⟨hcomplPostOut, hcpPostOut, hfinPostOut⟩ :=
        loopPost_back hvalidPostOut hpPostOut htrPost htailPost hcompl
      have hcomplPost : Completes f sPost.fn (exitId :: joins) :=
        SGrowsAt.completes_of gpost hcomplPostOut
      obtain ⟨hlenP, hrangeP, hsF⟩ := M.mapM_freshVal_length h6
      have hndP : postParams.Nodup := by
        rw [hrangeP]
        exact M.nodup_range' _ _
      have fI : SGrowsAt 0 sF sI :=
        ((SGrowsAt.of_newBlock (N := 0) h7).trans
          (SGrowsAt.of_sealCur h8)).trans
          (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)
      have fN : SGrowsAt 0 sF sN := fI.trans
        (((SGrowsAt.of_grows (N := 0) gIJ).trans
          (aJL.mono (Nat.zero_le _))).trans
          (SGrowsAt.of_sealCur h13) |>.trans
            (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h14))
      have hparamsLtN : ∀ i ∈ postParams, i < sN.fn.nextVal := by
        intro i hi
        rw [hrangeP] at hi
        exact Nat.lt_of_lt_of_le
          (by simpa [hsF] using (M.mem_range'_bounds hi).2) fN.nextVal
      have hparamsLtO : ∀ i ∈ postParams, i < sO.fn.nextVal := by
        intro i hi
        exact Nat.lt_of_lt_of_le (hparamsLtN i hi) gbody.nextVal
      have hnoneP : ∀ i ∈ postParams, RB i = none := by
        intro i hi
        rw [hbelowB i (hparamsLtN i hi)]
        have hiRange := hi
        rw [hrangeP] at hiRange
        have hiLtI : i < sI.fn.nextVal := Nat.lt_of_lt_of_le
          (by simpa [hsF] using (M.mem_range'_bounds hiRange).2) fI.nextVal
        rw [hbelowA i hiLtI]
        apply hclean i
        · exact Nat.le_trans
            (((SGrowsAt.of_grows (N := 0) gAB).trans
              (SGrowsAt.of_newBlock h3)).trans (SGrowsAt.of_grows gCD) |>.trans
              (SGrowsAt.of_newBlock h5)).nextVal
            (M.mem_range'_bounds hiRange).1
        · intro hiH
          rw [hrangeH] at hiH
          have hu := (M.mem_range'_bounds hiH).2
          have hl := (M.mem_range'_bounds hiRange).1
          have hnextCB : sC.fn.nextVal = sB.fn.nextVal := by
            rw [M.newBlock_apply] at h3
            exact (congrArg (fun z => z.fn.nextVal)
              (M.some_pair_inj h3).2).symm
          have hendH : sA.fn.nextVal + (modifiedX env [post, body]).length =
              sC.fn.nextVal := by rw [hnextCB, hsB]
          have huC : i < sC.fn.nextVal := by rwa [hendH] at hu
          have hCE : sC.fn.nextVal ≤ sE.fn.nextVal :=
            (SGrowsAt.of_grows (N := 0) gCD).trans
              (SGrowsAt.of_newBlock h5) |>.nextVal
          exact Nat.not_lt_of_ge (Nat.le_trans hCE hl) huC
      have hbaseP : ∀ i ∈ postParams, sA.fn.nextVal ≤ i := by
        intro i hi
        rw [hrangeP] at hi
        exact Nat.le_trans
          (((SGrowsAt.of_grows (N := 0) gAB).trans
            (SGrowsAt.of_newBlock h3)).trans (SGrowsAt.of_grows gCD) |>.trans
            (SGrowsAt.of_newBlock h5)).nextVal
          (M.mem_range'_bounds hi).1
      have gGPost : SGrowsAt 0 sG sPost :=
        (gGNall.trans (gbody.mono (Nat.zero_le _))).trans gOP
      obtain ⟨pb, hpb, hpp⟩ := gGPost.params postId
        ⟨postParams, [], .ret []⟩ (newBlock_target_get h7)
      have hnextOP : sO.fn.nextVal ≤ sPost.fn.nextVal := gOP.nextVal
      have hVbody : YulSemantics.VEnv.setMany V
          (modifiedX env [post, body]) vals = Vb := by
        have hnames : VEnv.names Vb = VEnv.names V := by
          have hm := (mod_sim hbodyStep).1
          simpa [declsOfStmt] using hm
        have hmod : ModOut [] (modStmts [] body) V Vb := by
          have hm := (mod_sim hbodyStep).2 [] (localsOK_nil V)
          simpa [modStmt] using hm
        exact setMany_eq_of_modOut (xs := modifiedX env [post, body]) henv
          (huniq.setMany _ _) hnames hmod hvals
          (fun x hx => by
            rw [VMap.names_setMany]
            exact modifiedX_mem_names hx)
          (fun x hx hm => mem_modifiedX (by
            rw [VMap.names_setMany] at hx
            exact hx) (by
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
            exact List.mem_append_right _ hm))
      have hleBody : Regs.Le R RB := hleA.trans hleB
      have hbelowBody : Regs.BelowEq sA.fn.nextVal R RB :=
        (hbelowA.mono aAI.nextVal).trans
          (hbelowB.mono (Nat.le_trans aAI.nextVal
            (Nat.le_trans (SGrowsAt.of_grows (N := 0) gIJ).nextVal
              aJN.nextVal)))
      obtain ⟨RP, hleP, hbelowP, hfrP, henvP, hsimP⟩ :=
        sim_loopPostEntry (model := model) (P := P) (f := f) (sBody := sO)
          (base := sA.fn.nextVal) henv hVbody hleBody hbelowBody hndP hnoneP
          hbaseP hparamsLtO hfrB hnextOP hcomplPost hpb hpp hcurPost
          hcurPost0 (by rw [hlenP]; exact hvals.length_eq) hcont
      rw [VMap.setMany_overwrite env (modifiedX_nodup huniq _)
        hlenH.symm hlenP.symm] at henvP
      have hboundPost : ∀ i : FuncId, i ∈ owned → i < sPost.funcs.size := by
        intro i hi
        exact Nat.lt_of_lt_of_le (hbound i hi)
          (Nat.le_trans a0G.funcsSize gGPost.funcsSize)
      have hboundPostOut : ∀ i : FuncId,
          i ∈ owned → i < sPostOut.funcs.size := by
        intro i hi
        exact Nat.lt_of_lt_of_le (hboundPost i hi) gpost.funcsSize
      have hownPostOut : FOwned owned sPostOut done :=
        FOwned.back_fprefix (loopPostTail_fprefix htailPost)
          hboundPostOut hown
      have hpostHalt := ihpost fenv
        (env.setMany (modifiedX env [post, body]) postParams) RP none rets
        sPost sPostOut postEnv (exitId :: joins) hfe henvP
        (huniq.setMany _ _) hfrP hvalidPost hpPost hcomplPostOut hcpPostOut
        hfinPostOut done owned hdone hboundPost hownPostOut htrPostStmt
      exact hsimP (.halt stp) hpostHalt
    rcases hob with rfl | rfl
    · obtain ⟨envB, RB, hbodyEnv, hleB, hbelowB, hfrB, henvB, _huniqB,
          hsimBody⟩ := hbodySim
      obtain rfl : bodyEnv = some envB := hbodyEnv
      obtain ⟨xvB, sP, h16, htr⟩ := M.bind_inv htr
      obtain ⟨uQ, sQ, h17, htr⟩ := M.bind_inv htr
      obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
      obtain ⟨postEnv, sS, h19, htailPost⟩ := M.bind_inv htr
      obtain ⟨rfl, vals, hgetB, hvals⟩ := edgeArgs_ok henvB h16
      have gOQ : SGrows sP sQ :=
        (SGrowsAt.of_grows (Grows.of_liftO h16)).trans
          (SGrowsAt.of_sealCur h17)
      have hpQ := ProtectedAt.forward hpO gOQ
      have gp := trScope_grows fenv
        (env.setMany (modifiedX env [post, body]) postParams) none rets post
        sR postEnv sS h19
      have gQR : SGrowsAt 0 sQ sR :=
        SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h18
      have hvalidR : CurValid sR := CurValid.of_moveTo
        (Nat.lt_of_lt_of_le (newBlock_target_lt h7)
          ((gGNall.trans (gbody.mono (Nat.zero_le _))).trans
            (gOQ.mono (Nat.zero_le _))).size)
        h18
      have hpostBase : s₀.fn.blocks.size ≤ postId := by
        rw [SGrowsAt.newBlock_id h7]
        exact a0F.size
      have hpRPost : ProtectedAt (exitId :: joins) sR.fn := by
        refine ⟨?_, ?_⟩
        · intro i hi
          have hi' : i ∈ exitId :: postId :: joins := by
            simp only [List.mem_cons] at hi ⊢
            rcases hi with rfl | hi
            · exact Or.inl rfl
            · exact Or.inr (Or.inr hi)
          exact Nat.lt_of_lt_of_le (hpQ.below i hi') gQR.size
        · have hcurR : sR.fn.curId = postId := by
            rw [M.moveTo_apply] at h18
            exact (congrArg (fun z => z.fn.curId)
              (M.some_pair_inj h18).2).symm
          rw [hcurR]
          simp only [List.mem_cons, not_or]
          exact ⟨Nat.ne_of_gt hexitPost, fun hmem =>
            Nat.not_lt_of_ge hpostBase (hp.below postId hmem)⟩
      have hvalidS : CurValid sS :=
        (trStmt_cur hvalidR (by rw [trStmt]; exact h19)).1
      have hpS : ProtectedAt (exitId :: joins) sS.fn :=
        ProtectedAt.forward hpRPost gp
      have hback := loopPost_back hvalidS hpS h19 htailPost hcompl
      have hcR := (SGrowsAt.completes_of gp hback.1).protect postId
      have hpQ' : ProtectedAt (postId :: exitId :: joins) sQ.fn := by
        refine ⟨?_, ?_⟩
        · intro i hi
          apply hpQ.below i
          simp only [List.mem_cons] at hi ⊢
          rcases hi with rfl | rfl | hi
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hi)
        · intro hi
          apply hpQ.away
          simp only [List.mem_cons] at hi ⊢
          rcases hi with h | h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
      have hfinQ := curFinal_of_move_grows h18
        (fun he => hpQ'.away (by simp [he])) hpQ'.away
        (SGrows.rfl' sR) hcR
      have hcurJump : CurOK f sP.fn ⟨[], .jump ⟨postId, xvB⟩⟩ :=
        curOK_of_sealCur hfinQ h17
      have hcont : ∀ res, JumpTo (model := model) P f postId vals RB stb res →
          ExecFrom (model := model) P f sI.fn R st res := by
        intro res hj
        exact hpre res (hsimBody res (execFrom_jump hcurJump hgetB hj))
      exact finish
        (((SGrowsAt.of_grows (N := 0) (Grows.of_liftO h16)).trans
          (SGrowsAt.of_sealCur h17)).trans
          (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h18))
        (by rw [M.moveTo_apply] at h18
            exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h18).2).symm)
        (by rw [M.moveTo_apply] at h18
            simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h18).2)
        (CurValid.of_moveTo
          (Nat.lt_of_lt_of_le (newBlock_target_lt h7)
            ((gGNall.trans (gbody.mono (Nat.zero_le _))).trans
              (gOQ.mono (Nat.zero_le _))).size)
          h18)
        h19 htailPost hleB hbelowB hfrB hvals hcont
    · obtain ⟨lc, RB, vals, hlc, hleB, hbelowB, hfrB, hvals, hcontB⟩ :=
        hbodySim
      have hlc' : lc = ⟨exitId, postId, modifiedX env [post, body]⟩ :=
        Option.some.inj hlc.symm
      subst lc
      cases bodyEnv with
      | none =>
        change (do
          moveTo postId
          let envP := env.setMany (modifiedX env [post, body]) postParams
          let renvP ← trScope fenv envP none rets post
          if let some envP' := renvP then
            let xvP ← edgeArgs envP' (modifiedX env [post, body])
            sealCur (.jump ⟨hId, xvP⟩)
          moveTo exitId
          pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sO =
            some (renv, s₁) at htr
        obtain ⟨uP, sP, h16, htr⟩ := M.bind_inv htr
        obtain ⟨postEnv, sQ, h17, htailPost⟩ := M.bind_inv htr
        have hcont : ∀ res,
            JumpTo (model := model) P f postId vals RB stb res →
            ExecFrom (model := model) P f sI.fn R st res :=
          fun res hj => hpre res (hcontB res hj)
        exact finish (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h16)
          (by rw [M.moveTo_apply] at h16
              exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h16).2).symm)
          (by rw [M.moveTo_apply] at h16
              simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h16).2)
          (CurValid.of_moveTo
            (Nat.lt_of_lt_of_le (newBlock_target_lt h7)
              (gGNall.trans (gbody.mono (Nat.zero_le _))).size) h16)
          h17 htailPost hleB hbelowB hfrB hvals hcont
      | some envB =>
        obtain ⟨xvB, sP, h16, htr⟩ := M.bind_inv htr
        obtain ⟨uQ, sQ, h17, htr⟩ := M.bind_inv htr
        obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
        obtain ⟨postEnv, sS, h19, htailPost⟩ := M.bind_inv htr
        have gOQ : SGrows sO sQ :=
          (SGrowsAt.of_grows (Grows.of_liftO h16)).trans
            (SGrowsAt.of_sealCur h17)
        have hcont : ∀ res,
            JumpTo (model := model) P f postId vals RB stb res →
            ExecFrom (model := model) P f sI.fn R st res :=
          fun res hj => hpre res (hcontB res hj)
        exact finish
          ((gOQ.mono (Nat.zero_le _)).trans
            (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h18))
          (by rw [M.moveTo_apply] at h18
              exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h18).2).symm)
          (by rw [M.moveTo_apply] at h18
              simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h18).2)
          (CurValid.of_moveTo
            (Nat.lt_of_lt_of_le (newBlock_target_lt h7)
              ((gGNall.trans (gbody.mono (Nat.zero_le _))).trans
                (gOQ.mono (Nat.zero_le _))).size)
            h18)
          h19 htailPost hleB hbelowB hfrB hvals hcont

  -- `sim_loopBodyNonNormal` also closes break: it consumes the body's
  -- `JumpTo exitId`, binds `exitParams`, and rebuilds `EnvOK` at the exit.
  | @loopBreak funs V st c post body cv st1 Vb stb _hc hnz hb ihc ihb =>
    change LOut (model := model) P f funs V st c post body Vb stb .normal doneFuncs
    simpa using sim_loopBodyNonNormal hfuncs ihc hb ihb hnz
      (Or.inr (Or.inr rfl))
  | @loopLeave funs V st c post body cv st1 Vb stb _hc hnz hb ihc ihb =>
    change LOut (model := model) P f funs V st c post body Vb stb .leave doneFuncs
    simpa using sim_loopBodyNonNormal hfuncs ihc hb ihb hnz
      (Or.inr (Or.inl rfl))
  | @loopBodyHalt funs V st c post body cv st1 Vb stb _hc hnz hb ihc ihb =>
    change LOut (model := model) P f funs V st c post body Vb stb .halt doneFuncs
    simpa using sim_loopBodyNonNormal hfuncs ihc hb ihb hnz (Or.inl rfl)

/-!
**The construction simulation — the remaining hole.**

Obligation: by induction on the source `Step` derivation (one
`induction … with` over the single indexed inductive, as in `SimAsm.sim`),
with `SOut` above as the statement-class motive and the analogous
expression-class motive
`∀ s₀ i s₁, trExpr fenv env e s₀ = some (i, s₁) → ∃ R₁, Regs.Le R R₁ ∧ R₁ i = some v ∧ SimS P f s₀.fn R yst s₁.fn R₁ yst'`
(and its `.halt` variant, and `trArgs`' list version). Each construction case
needs the `M.bind_inv` decomposition of the corresponding `trX` equation, the
freshness facts of `M.mapM_freshVal` to see that every emitted id is fresh (so
`Regs.Le` is preserved — `Regs.Le.set`/`Regs.Le.setMany`), `EnvOK`'s
`get`/`set`/`setMany`/`zip`/`restore` lemmas for the environment, `FMap.get_ok`
for calls, and `isHaltingOp_halts` for the `exprStmt` halt seal.

Two of the three sub-obligations this proof needs are now discharged above:

* **builder monotonicity** — `trStmt_grows` (and `trExpr_grows`/`trArgs_grows`/
  `trExprN_grows`) give `SGrowsAt`: `nextVal` and the block/function arrays only
  grow, no block's parameter list ever changes, and the only pre-existing block
  a fragment can seal is the one it starts on. `SGrowsAt.completes_of` turns
  that into the backwards transfer of the placement invariant.
* **the placement invariant** — `Completes` (strengthened to "every reserved
  block keeps its parameters", which the `cond`/`switch`/`forLoop` cases need
  because they reserve the join/exit block before sealing its predecessors) is
  established at the top level in `ofBlock_sound'` and travels inwards along
  each fragment by `SGrowsAt.completes_of`.

The analysis obligation is discharged too: `modStmts_sound` is proved
(via `mod_sim`), so `cond`/`switch`/`forLoop` may thread only
`modifiedX env bodies`.

Seventeen per-case leaves and combinators are proved above and plug straight
into the induction:

* expressions — `sim_lit`, `sim_var`, `sim_args_nil`, `sim_args_cons`, with the
  freshness invariant `RegsFresh` they thread (`EOut`/`EOutL`);
* statements — `sim_letDecl_none`, `sim_letDecl_some`, `sim_assign`,
  `sim_exprStmt_op`, `sim_exprStmt_halt`;
* non-local exits — `sim_break`, `sim_continue`, `sim_leave`, using `CurFinal`
  (the block a diverting statement seals is *its own* current block, which
  `Completes.sealed` deliberately exempts; the enclosing `cond`/`switch`/
  `forLoop` supplies it, because each `moveTo`s a fresh join/exit block
  afterwards and its own `Completes` then covers the sealed one);
* sequencing and scoping — `sim_seqNil`, `SOut.seq` (the `seqCons`
  combinator — pure, no construction inversion), `SOut.of_nonNormal` (the
  `seqStop` transport across the dead code the construction still walks), and
  `SOut.scope` (the `block` combinator, matching the construction's `drop`
  against the source's `restore`);
* every "the right-hand side halted" rule at once — `SOut.ofExprHalt` covers
  `letHalt`, `assignHalt`, `exprStmtHalt`, `ifHalt` and `switchHalt`;
* **edges into reserved blocks** — `jumpTo_of_completes` and its three `SimS`
  specialisations `simS_jump_join`, `simS_branchFalse_join`,
  `simS_branchTrue_body`. These are the whole semantic content of `cond`,
  `switch` and the loop family: those constructs reserve their join / body /
  header / exit / post blocks *before* sealing the edges into them, so the
  construction never sees the finished bodies — only the parameter lists, which
  is exactly what `Completes.params` fixes. What is left for those cases is the
  mechanical inversion of the corresponding `trStmt` equation, which belongs in
  the induction shell.

Two invariants the remaining cases must thread, both with their payoff lemmas
already proved:

* `NoShadow` — the construction rejects shadowing (`letDecl` checks
  `VMap.mem`), so a scope's declarations share no name with the outer
  environment. `get_restore_of_noShadow` turns that into "scope exit is
  transparent to outer names", which is what lets `SOut.scope` carry a
  non-local exit's edge values (read *inside* the scope) out through the
  source's `restore`.
* `Completes`/`CurFinal` — see above.

Groundwork for the shell is in place: `Motive` below is the statement of the
induction (every clause final except `.loop`, which the `for` round fills), and
`trScope_grows`/`trStmts_grows`/`trCases_grows`/`trFunc_grows` give the builder
monotonicity for *all five* construction functions, which the compound cases
need to see that a reserved block survives to the finished function.

The function-table invariant needed by the remaining hoist/call work is now in
the motive: one `doneFuncs` table and its `FuncTableComplete` proof stay fixed
through every recursive IH.  What remains in the `block` case is the structural
analogue of `SimAsm.hoist_ok`: walk the successful `allocScope body` and
`trStmts` equations, pair their entries with the source's `hoist body`, and
show each resulting `fillFunc` slot survives into `doneFuncs`.  At that point
`FuncTableComplete.funcOK` packages the `P.funcs` and nested-slot conjuncts.

What remains is the `induction … with` shell itself — which for `cond`,
`switch` and the loop family is now mostly the `trStmt`/`trCases` equation
inversion feeding the edge steps above (plus `edgeArgs_ok` for the edge values,
`modStmts_sound` for the variables the join does *not* carry, and `setMany_self`
for the `if`-false and loop-exit edges, which pass a variable its own current
value) — and the user-call pair `callOk`/`callHalt` (`FMap.get_ok`, `trFunc`,
and a fresh register file for the callee).
-/
/-! `trScope_sim` (the scope wrapper WITHOUT register-freshness premises) was
deleted: the statement is false as written.  `SOut.normal` asserts
`∃ R₁, Regs.Le R R₁ ∧ RegsFresh R₁ s₁.fn`, yet nothing constrained `R`:
with `body := []`, empty environments, `s₀ = s₁ = initBState`, and
`R := fun _ => some 0`, every premise holds while the conclusion forces both
`R₁ = Regs.empty` and `R₁ 0 = some 0`.  `CurValid s₀`, `CurPlaced f s₁.fn`,
and `renv = none → CurFinal f s₁.fn` were likewise underivable.
`trScope_sim_of_fresh` below is that statement with exactly the four missing
premises added; `ofBlock_sound'` uses it, discharging all four at the
top-level instantiation (`R = Regs.empty`, `s₀ = initBState`). -/

/-- **The scope wrapper, with the premises `Motive` actually needs.**  The
conclusion of the deleted false wrapper above, plus the four facts it omitted.  Every
one of them holds at the top-level instantiation in `ofBlock_sound'`. -/
theorem trScope_sim_of_fresh {P : Prog} {f : Func}
    {funs : YulSemantics.FunEnv yulD} {fenv : FMap}
    {V V' : VEnv yulD} {env : VMap} {R : Regs}
    {lctx : Option LoopCtx} {rets : Option (List Ident)}
    {body : List (Stmt Op)} {s₀ s₁ : BState} {renv : Option VMap}
    {doneFuncs : Array (Option Func)}
    {yst yst' : EvmState} {o : Outcome}
    (hfuncs : FuncTableComplete P doneFuncs)
    (hfe : FEnvOK (model := model) P funs fenv)
    (henv : EnvOK (model := model) env V R)
    (huniq : env.Unique)
    (hfr : RegsFresh R s₀.fn)
    (hvalid : CurValid s₀)
    (hcompl : Completes f s₁.fn)
    (hcp : CurPlaced f s₁.fn)
    (hfin : renv = none → CurFinal f s₁.fn)
    (hfuncsEq : s₁.funcs = doneFuncs)
    (htr : trScope fenv env lctx rets body s₀ = some (renv, s₁))
    (hstep : YulSemantics.ExecStmt yulD funs V yst (.block body) V' yst' o) :
    SOut (model := model) P f lctx rets s₀ s₁ R renv V' yst yst' o :=
  have hown : FOwned [] s₁ s₁ := by
    have ho := hfuncs.owned_nil
    rw [← hfuncsEq] at ho
    exact ⟨ho.nodup, ho.pending, ho.filled⟩
  sim (f := f) hfuncs hstep fenv env R lctx rets s₀ s₁ renv [] hfe henv huniq
    hfr hvalid (ProtectedAt.nil s₀.fn) hcompl hcp hfin s₁ [] hfuncsEq
    (by simp) hown (by rw [trStmt]; exact htr)

/-! ## Construction soundness -/

/-- **Construction soundness.** If the construction accepts `prog` and the Yul
semantics runs it, the SSA program runs to the same final state and outcome.

The non-local top-level outcomes are impossible: with no loop context and no
enclosing function, `SOut`'s `break`/`continue`/`leave` cases demand
`none = some _`. -/
theorem ofBlock_sound' {prog : YulSemantics.Block Op} {P : Prog}
    {yst0 : EvmState} {V' : VEnv yulD} {yst' : EvmState} {o : Outcome}
    (hof : ofBlock prog = some P)
    (hrun : YulSemantics.Run yulD prog yst0 V' yst' o) :
    Run (model := model) P yst0 yst' o := by
  obtain ⟨_hwf, main, s, hbuild, hmapM, rfl⟩ := ofBlock_inv hof
  obtain ⟨renv, s₁, htr, hparams, hnrets, hentry, hfuncs, hblocks⟩ :=
    buildMain_inv hbuild
  -- the finished `main` completes the builder state the top-level scope left
  have hext : Completes P.main s₁.fn := by
    cases renv with
    | none =>
      exact ⟨fun i b _ _ hi => by rw [hblocks]; exact hi,
        fun i b hb => ⟨b, by rw [hblocks]; exact hb, rfl⟩,
        by rw [hblocks]⟩
    | some e =>
      obtain ⟨b, hb, hmb⟩ := hblocks
      refine ⟨fun i b' _ hne hi => ?_, fun i b' hb' => ?_, ?_⟩
      · rw [hmb, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_ne (Ne.symm hne)]
        exact hi
      · by_cases hc : i = s₁.fn.curId
        · subst hc
          obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
          refine ⟨⟨b'.params, s₁.fn.cur.reverse, .ret []⟩, ?_, rfl⟩
          rw [hmb, Array.set!_eq_setIfInBounds,
            Array.getElem?_setIfInBounds_self_of_lt (lt_size_of_getElem? hb)]
        · refine ⟨b', ?_, rfl⟩
          rw [hmb, Array.set!_eq_setIfInBounds,
            Array.getElem?_setIfInBounds_ne (Ne.intro fun hh => hc hh.symm)]
          exact hb'
      · rw [hmb]; simp
  -- the four placement/freshness facts `Motive` needs, at the top level
  have hvalid0 : CurValid initBState := by
    simp [CurValid, initBState]
  have htrStmt : trStmt [] [] none none (.block prog) initBState
      = some (renv, s₁) := by
    rw [trStmt]; exact htr
  have hvalid1 : CurValid s₁ := (trStmt_cur hvalid0 htrStmt).1
  have hfresh0 : RegsFresh (Regs.empty) initBState.fn := fun _ _ => rfl
  have hplace : CurPlaced P.main s₁.fn ∧ (renv = none → CurFinal P.main s₁.fn) := by
    cases renv with
    | none =>
      have hfin : CurFinal P.main s₁.fn := by
        intro b hb; rw [hblocks]; exact hb
      exact ⟨curPlaced_of_curFinal hvalid1
        (trScope_none_cur_nil [] [] none none prog initBState s₁ htr) hfin,
        fun _ => hfin⟩
    | some e =>
      obtain ⟨b, hb, hmb⟩ := hblocks
      refine ⟨⟨⟨[], .ret []⟩, ⟨b.params, s₁.fn.cur.reverse, .ret []⟩, ?_, by simp,
        rfl⟩, fun hq => absurd hq (by simp)⟩
      rw [hmb, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_self_of_lt (lt_size_of_getElem? hb)]
  -- the top-level source derivation is one `block` rule over `prog`
  rw [YulSemantics.Run] at hrun
  cases hrun with
  | @block _ _ _ _ Vb stb o hstmts =>
    have hmapM' : FuncTableComplete P s₁.funcs := by
      rw [← hfuncs]
      exact hmapM
    have hsim := trScope_sim_of_fresh (model := model) (P := P) (f := P.main)
      (funs := []) (fenv := []) (V := []) (env := []) (R := Regs.empty)
      (doneFuncs := s₁.funcs)
      hmapM' .nil EnvOK.nil VMap.unique_nil hfresh0 hvalid0 hext hplace.1
      hplace.2 rfl htr (.block hstmts)
    -- `initBState` is the entry block, empty and current
    have hentryCur : ∀ rest, CurOK P.main initBState.fn rest
        → ∃ eb, P.main.blocks[P.main.entry]? = some eb
            ∧ rest = ⟨eb.instrs, eb.term⟩ := by
      intro rest hc
      obtain ⟨b, hb, hi, ht⟩ := hc
      refine ⟨b, by rw [hentry]; exact hb, ?_⟩
      cases rest
      simp only [initBState] at hi
      simp_all
    cases o with
    | normal =>
      obtain ⟨env', R₁, hrenv, _hle, _hbelow, _hfr, _henv', _huniq, hsimS⟩ := hsim
      -- the fall-through seal put `ret []` on the block the scope ended in
      obtain ⟨b, hb, hmb⟩ : ∃ b, s₁.fn.blocks[s₁.fn.curId]? = some b
          ∧ P.main.blocks
              = s₁.fn.blocks.set! s₁.fn.curId ⟨b.params, s₁.fn.cur.reverse, .ret []⟩ := by
        rw [hrenv] at hblocks; exact hblocks
      have hcur : CurOK P.main s₁.fn ⟨[], .ret []⟩ := by
        refine ⟨⟨b.params, s₁.fn.cur.reverse, .ret []⟩, ?_, by simp, rfl⟩
        rw [hmb, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_self_of_lt
            (Array.getElem?_eq_some_iff.mp hb |>.1)]
      obtain ⟨rest, hc, hexec⟩ :=
        hsimS (.ret [] yst') (execFrom_ret hcur (by simp))
      obtain ⟨eb, heb, rfl⟩ := hentryCur rest hc
      exact .normal heb hexec
    | halt =>
      obtain ⟨rest, hc, hexec⟩ := hsim
      obtain ⟨eb, heb, rfl⟩ := hentryCur rest hc
      exact .halt heb hexec
    | «break» =>
      obtain ⟨lc, _, _, hlc, _⟩ := hsim
      exact absurd hlc (by simp)
    | «continue» =>
      obtain ⟨lc, _, _, hlc, _⟩ := hsim
      exact absurd hlc (by simp)
    | leave =>
      obtain ⟨rs, _, hrs, _⟩ := hsim
      exact absurd hrs (by simp)

end Semantics

end YulEvmCompiler.SsaCfg
