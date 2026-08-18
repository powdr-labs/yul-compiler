import YulEvmCompiler.SsaCfg.Spec.Sem
import YulEvmCompiler.SsaCfg.Implementation.OfYul
import YulSemantics.BigStep
import YulEvmCompiler.Optimizer.Core.Equiv
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.OfYulSound.Basics

`Forall₂`, register-file, `VMap`/`VEnv` and environment-correspondence plumbing.

The bottom layer of the construction-soundness proof: pure data-structure
lemmas about `Regs`, `VMap` and Yul's `VEnv`, plus the `EnvOK`
source/target environment correspondence built on top of them.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics (Ident Literal Expr Stmt VEnv Outcome)
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal evmWithExternal)

/-! ## `YulSemantics.Forall₂` helpers

Self-contained so this file does not depend on which `Mathlib.Data.List`
modules happen to be transitively imported. -/

end YulEvmCompiler.SsaCfg

namespace YulSemantics.Forall₂

variable {α β : Type} {r s : α → β → Prop}

theorem length_eq : ∀ {l₁ : List α} {l₂ : List β},
    YulSemantics.Forall₂ r l₁ l₂ → l₁.length = l₂.length := by
  intro l₁ l₂ hr
  induction hr with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem append : ∀ {a : List α} {b : List β} {c : List α} {d : List β},
    YulSemantics.Forall₂ r a b → YulSemantics.Forall₂ r c d → YulSemantics.Forall₂ r (a ++ c) (b ++ d) := by
  intro a b c d hab hcd
  induction hab with
  | nil => simpa using hcd
  | cons hh _ ih => exact .cons hh ih

theorem drop : ∀ (n : Nat) {a : List α} {b : List β},
    YulSemantics.Forall₂ r a b → YulSemantics.Forall₂ r (a.drop n) (b.drop n) := by
  intro n
  induction n with
  | zero => intro a b h; simpa using h
  | succ n ih =>
    intro a b h
    cases h with
    | nil => simp only [List.drop_nil]; exact .nil
    | cons hh ht => simpa using ih ht

/-- An all-or-nothing `mapM` succeeds exactly when it succeeds pointwise. Used
for both `Regs.getMany` (`mapM R`) and `edgeArgs` (`mapM env.get`). -/
theorem mapM_eq_some_iff {f : α → Option β} :
    ∀ {xs : List α} {ys : List β},
      xs.mapM f = some ys ↔ YulSemantics.Forall₂ (fun x y => f x = some y) xs ys := by
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

theorem refl {r : α → α → Prop} (h : ∀ a, r a a) : ∀ l : List α, YulSemantics.Forall₂ r l l := by
  intro l
  induction l with
  | nil => exact .nil
  | cons a l ih => exact .cons (h a) ih

theorem trans' {γ : Type} {r : α → β → Prop} {t : β → γ → Prop} {u : α → γ → Prop}
    (hc : ∀ a b c, r a b → t b c → u a c) :
    ∀ {l₁ : List α} {l₂ : List β} {l₃ : List γ},
      YulSemantics.Forall₂ r l₁ l₂ → YulSemantics.Forall₂ t l₂ l₃ → YulSemantics.Forall₂ u l₁ l₃ := by
  intro l₁ l₂ l₃ h₁ h₂
  induction h₁ generalizing l₃ with
  | nil => cases h₂; exact .nil
  | cons hh ht ih =>
    cases h₂ with
    | cons hh2 ht2 => exact .cons (hc _ _ _ hh hh2) (ih ht2)

theorem imp_mem {r s : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, YulSemantics.Forall₂ r l₁ l₂ →
      (∀ a ∈ l₁, ∀ b, r a b → s a b) → YulSemantics.Forall₂ s l₁ l₂ := by
  intro l₁ l₂ h
  induction h with
  | nil => intro _; exact .nil
  | @cons a b l₁' l₂' hh _ ih =>
    intro hs
    exact .cons (hs a (List.mem_cons_self ..) b hh)
      (ih (fun y hy c hc => hs y (List.mem_cons_of_mem _ hy) c hc))

end YulSemantics.Forall₂

namespace YulEvmCompiler.SsaCfg
open YulSemantics (Ident Literal Expr Stmt VEnv Outcome)
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal evmWithExternal)

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
    R.getMany xs = some vs ↔ YulSemantics.Forall₂ (fun x v => R x = some v) xs vs := by
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
  exact YulSemantics.Forall₂.imp (fun x v hxv => h x v hxv) hg

theorem getMany_length {R : Regs} {xs : List ValId} {vs : List U256}
    (h : R.getMany xs = some vs) : xs.length = vs.length :=
  YulSemantics.Forall₂.length_eq (getMany_eq_some_iff.mp h)

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
      simp [VMap.set, hx, hxy]
    · by_cases hy : p.1 = y
      · simp [VMap.set, hy, Ne.symm hxy]
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
      simp [YulSemantics.VEnv.set, hx, hxy]
    · by_cases hy : p.1 = y
      · simp [YulSemantics.VEnv.set, hy, Ne.symm hxy]
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
    YulSemantics.Forall₂ (fun (p q : Ident × D.Value) => p.1 = q.1 ∧ (q.2 = p.2 ∨ p.1 = x))
      V (YulSemantics.VEnv.set V x v) := by
  intro V
  induction V with
  | nil => intro x v; exact .nil
  | cons p V ih =>
    intro x v
    obtain ⟨pn, pv⟩ := p
    rw [YulSemantics.VEnv.set]
    by_cases h : pn = x
    · exact (if_pos h) ▸ YulSemantics.Forall₂.cons ⟨h, Or.inr h⟩
        (YulSemantics.Forall₂.refl (fun _ => ⟨rfl, Or.inl rfl⟩) V)
    · exact (if_neg h) ▸ YulSemantics.Forall₂.cons ⟨rfl, Or.inl rfl⟩ (ih x v)

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
    YulSemantics.Forall₂ (fun x v => YulSemantics.VEnv.get V x = some v) xs vs →
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

end VEnv

section Correspondence

variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates YulSemantics.EVM.ExternalGas.any

/-! ## The environment invariant

`EnvOK env V R`: the construction-time map `env` and the runtime environment
`V` bind the same names in the same order, and every `ValId` `env` records
holds the value `V` records. This is the invariant that makes `VMap.get`
(construction) and `VEnv.get` (semantics) interchangeable. -/

/-- The construction-time environment mirrors the runtime one through `R`. -/
def EnvOK (env : VMap) (V : VEnv yulD) (R : Regs) : Prop :=
  YulSemantics.Forall₂ (fun (p : Ident × ValId) (q : Ident × U256) =>
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
  YulSemantics.Forall₂.length_eq h

/-- Register-file extension preserves the invariant — the single-assignment
payoff: nothing the construction does later can invalidate a binding. -/
theorem mono {env : VMap} {V : VEnv yulD} {R R' : Regs} (h : EnvOK env V R)
    (hle : Regs.Le R R') : EnvOK env V R' :=
  YulSemantics.Forall₂.imp (fun _ _ hpq => ⟨hpq.1, hle _ _ hpq.2⟩) h

theorem nil : EnvOK ([] : VMap) ([] : VEnv yulD) R := YulSemantics.Forall₂.nil

theorem cons {x : Ident} {i : ValId} {v : U256} {env : VMap} {V : VEnv yulD}
    {R : Regs} (hv : R i = some v) (h : EnvOK env V R) :
    EnvOK ((x, i) :: env) ((x, v) :: V) R :=
  YulSemantics.Forall₂.cons ⟨rfl, hv⟩ h

theorem append {env₁ env₂ : VMap} {V₁ V₂ : VEnv yulD} {R : Regs}
    (h₁ : EnvOK env₁ V₁ R) (h₂ : EnvOK env₂ V₂ R) :
    EnvOK (env₁ ++ env₂) (V₁ ++ V₂) R :=
  YulSemantics.Forall₂.append h₁ h₂

theorem drop {env : VMap} {V : VEnv yulD} {R : Regs} (n : Nat)
    (h : EnvOK env V R) : EnvOK (env.drop n) (V.drop n) R :=
  YulSemantics.Forall₂.drop n h

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
  | nil => exact YulSemantics.Forall₂.nil
  | @cons p q env' V' hpq htl ih =>
    obtain ⟨py, pi⟩ := p
    obtain ⟨qy, qv⟩ := q
    obtain ⟨rfl, hqv⟩ := hpq
    rw [VMap.set, YulSemantics.VEnv.set]
    by_cases hx : py = x
    · rw [if_pos hx, if_pos hx]
      exact YulSemantics.Forall₂.cons ⟨rfl, hv⟩ htl
    · rw [if_neg hx, if_neg hx]
      exact YulSemantics.Forall₂.cons ⟨rfl, hqv⟩ ih

/-- Multi-assignment: `VMap.setMany` tracks `VEnv.setMany` pointwise. -/
theorem setMany {R : Regs} : ∀ {xs : List Ident} {is : List ValId} {vs : List U256}
    {env : VMap} {V : VEnv yulD}, EnvOK env V R →
    YulSemantics.Forall₂ (fun i v => R i = some v) is vs →
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
    YulSemantics.Forall₂ (fun i v => R i = some v) is vs → xs.length = is.length →
    EnvOK (xs.zip is) (xs.zip vs) R := by
  intro xs
  induction xs with
  | nil => intro is vs _ _; exact YulSemantics.Forall₂.nil
  | cons x xs ih =>
    intro is vs hiv hlen
    cases hiv with
    | nil => exact absurd hlen (by simp)
    | @cons i v is' vs' hh ht =>
      simp only [List.zip_cons_cons]
      exact YulSemantics.Forall₂.cons ⟨rfl, hh⟩ (ih ht (by simpa using hlen))

/-- The `let`-without-value / return-variable case: ids bound to zero mirror
`bindZeros`. -/
theorem zip_bindZeros {R : Regs} : ∀ {xs : List Ident} {is : List ValId},
    xs.length = is.length → (∀ i ∈ is, R i = some 0) →
    EnvOK (xs.zip is) (YulSemantics.bindZeros yulD xs) R := by
  intro xs
  induction xs with
  | nil => intro is _ _; exact YulSemantics.Forall₂.nil
  | cons x xs ih =>
    intro is hlen hz
    cases is with
    | nil => exact absurd hlen (by simp)
    | cons i is =>
      simp only [List.zip_cons_cons, YulSemantics.bindZeros, List.map_cons]
      exact YulSemantics.Forall₂.cons ⟨rfl, hz i (List.mem_cons_self ..)⟩
        (ih (by simpa using hlen) (fun j hj => hz j (List.mem_cons_of_mem _ hj)))

/-- Pointwise version of `edgeArgs`' payoff. -/
theorem edge_vals {env : VMap} {V : VEnv yulD} {R : Regs} (henv : EnvOK env V R) :
    ∀ {xs : List Ident} {ids : List ValId},
      YulSemantics.Forall₂ (fun x i => VMap.get env x = some i) xs ids →
      ∃ vals, R.getMany ids = some vals
        ∧ YulSemantics.Forall₂ (fun x v => YulSemantics.VEnv.get V x = some v) xs vals := by
  intro xs ids h
  induction h with
  | nil => exact ⟨[], rfl, .nil⟩
  | @cons x i xs' ids' hh _ ih =>
    obtain ⟨v, hv, hRi⟩ := henv.get hh
    obtain ⟨vals, hvals, hf⟩ := ih
    exact ⟨v :: vals, by rw [Regs.getMany_cons, hRi, hvals]; simp, .cons hv hf⟩

end EnvOK

end Correspondence

end YulEvmCompiler.SsaCfg
