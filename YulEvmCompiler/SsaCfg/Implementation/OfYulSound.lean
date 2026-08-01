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
structure Completes (f : Func) (fn : FnState) : Prop where
  sealed : ∀ (i : Nat) (b : Block), i ≠ fn.curId → fn.blocks[i]? = some b
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
  ⟨h.sealed, fun b hb => h.params _ b hb⟩

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
theorem completes_of {f : Func} {s s' : BState}
    (h : SGrowsAt s.fn.blocks.size s s') (hc : Completes f s'.fn) :
    Completes f s.fn := by
  refine ⟨?_, ?_, Nat.le_trans h.size hc.size⟩
  · intro i b hne hb
    have hlt : i < s.fn.blocks.size := lt_size_of_getElem? hb
    have hne2 : i ≠ s'.fn.curId := by
      rcases h.curId with heq | hge
      · rw [heq]; exact hne
      · omega
    exact hc.sealed i b hne2 (h.keep i b hlt hne hb)
  · intro i b hb
    obtain ⟨b', hb', hp'⟩ := h.params i b hb
    obtain ⟨bf, hbf, hpf⟩ := hc.params i b' hb'
    exact ⟨bf, hbf, hpf.trans hp'⟩

end SGrowsAt

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
  ∃ R₁ : Regs, Regs.Le R₀ R₁ ∧ RegsFresh R₁ s₁.fn ∧ R₁ i = some v
    ∧ SimS (model := model) P f s₀.fn R₀ yst s₁.fn R₁ yst'

/-- An argument list: the ids read back as the value list, in source order. -/
def EOutL (P : Prog) (f : Func) (s₀ s₁ : BState) (R₀ : Regs)
    (ids : List ValId) (vs : List U256) (yst yst' : EvmState) : Prop :=
  ∃ R₁ : Regs, Regs.Le R₀ R₁ ∧ RegsFresh R₁ s₁.fn ∧ R₁.getMany ids = some vs
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
    Regs.Le.set _ hfresh.unbound, hfresh.set _ (Nat.le_refl _),
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
  exact ⟨R, Regs.Le.rfl R, hfresh, hRj, SimS.rfl'⟩

/-- **`args []`** — nothing emitted. -/
theorem sim_args_nil {P : Prog} {f : Func} {fenv : FMap} {env : VMap} {R : Regs}
    {s₀ s₁ : BState} {ids : List ValId} {yst : EvmState}
    (hfresh : RegsFresh R s₀.fn)
    (htr : trArgs fenv env [] s₀ = some (ids, s₁)) :
    EOutL (model := model) P f s₀ s₁ R ids [] yst yst := by
  rw [trArgs] at htr
  obtain ⟨hids, hs₁⟩ := M.pure_inv htr
  subst hs₁; subst hids
  exact ⟨R, Regs.Le.rfl R, hfresh, rfl, SimS.rfl'⟩

/-- **`args (e :: rest)`** — the construction translates `rest` first, matching
the source's right-to-left evaluation order; the two fragments compose and the
earlier ids survive because the register file only extends. -/
theorem sim_args_cons {P : Prog} {f : Func} {s₀ sA s₁ : BState} {R : Regs}
    {restIds : List ValId} {i : ValId} {restvals : List U256} {v : U256}
    {yst yst1 yst2 : EvmState}
    (hrest : EOutL (model := model) P f s₀ sA R restIds restvals yst yst1)
    (hhead : ∀ R', Regs.Le R R' → RegsFresh R' sA.fn →
      EOut (model := model) P f sA s₁ R' i v yst1 yst2) :
    EOutL (model := model) P f s₀ s₁ R (i :: restIds) (v :: restvals) yst yst2 := by
  obtain ⟨Ra, hle, hfr, hget, hsim⟩ := hrest
  obtain ⟨Rb, hle2, hfr2, hi, hsim2⟩ := hhead Ra hle hfr
  refine ⟨Rb, hle.trans hle2, hfr2, ?_, hsim.trans hsim2⟩
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
      renv = some env' ∧ Regs.Le R₀ R₁ ∧ RegsFresh R₁ s₁.fn
        ∧ EnvOK (model := model) env' V' R₁
        ∧ env'.Unique
        ∧ SimS (model := model) P f s₀.fn R₀ yst s₁.fn R₁ yst'
  | .halt => ExecFrom (model := model) P f s₀.fn R₀ yst (.halt yst')
  | .break => ∃ (lc : LoopCtx) (R₁ : Regs) (vals : List U256),
      lctx = some lc ∧ Regs.Le R₀ R₁ ∧ RegsFresh R₁ s₁.fn
        ∧ List.Forall₂ (fun x v => YulSemantics.VEnv.get V' x = some v) lc.vars vals
        ∧ ∀ res, JumpTo (model := model) P f lc.brkTgt vals R₁ yst' res
            → ExecFrom (model := model) P f s₀.fn R₀ yst res
  | .continue => ∃ (lc : LoopCtx) (R₁ : Regs) (vals : List U256),
      lctx = some lc ∧ Regs.Le R₀ R₁ ∧ RegsFresh R₁ s₁.fn
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
    {bid : BlockId} {u : Unit}
    (hmv : moveTo bid s = some (u, sM)) (hne : s.fn.curId ≠ bid)
    (hg : SGrows sM sEnd) (hcompl : Completes f sEnd.fn) :
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
  exact hcompl.sealed s.fn.curId b hneEnd hkeep

omit model in
/-- Variant of `curFinal_of_move_grows` for a surrounding structured
translation.  Its later current block may be another block reserved by the
same construct, so freshness is measured against the construct's base `N`.
The block being left predates that base and therefore remains protected by
`SGrowsAt.keep`. -/
theorem curFinal_of_move_sgrowsAt {f : Func} {N : Nat} {s sM sEnd : BState}
    {bid : BlockId} {u : Unit}
    (hold : s.fn.curId < N)
    (hmv : moveTo bid s = some (u, sM)) (hne : s.fn.curId ≠ bid)
    (hg : SGrowsAt N sM sEnd) (hcompl : Completes f sEnd.fn) :
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
  exact hcompl.sealed s.fn.curId b hneEnd hkeep

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
  refine ⟨l, R, vals, rfl, Regs.Le.rfl R, hfresh, hforall, fun res hjmp => ?_⟩
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
  refine ⟨l, R, vals, rfl, Regs.Le.rfl R, hfresh, hforall, fun res hjmp => ?_⟩
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
    obtain ⟨lc, R₁, vals, hlc, hle, hfr, hforall, hcont⟩ := h
    exact ⟨lc, R₁, vals, hlc, hle, hfr.mono hgrow, hforall, hcont⟩
  | «continue» =>
    obtain ⟨lc, R₁, vals, hlc, hle, hfr, hforall, hcont⟩ := h
    exact ⟨lc, R₁, vals, hlc, hle, hfr.mono hgrow, hforall, hcont⟩
  | leave => exact h

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
    (hhead : SOut (model := model) P f lctx rets s₀ sA R (some env') V1 yst yst1 .normal)
    (htail : ∀ R₁ : Regs, Regs.Le R R₁ → RegsFresh R₁ sA.fn →
        EnvOK (model := model) env' V1 R₁ →
        env'.Unique →
        SOut (model := model) P f lctx rets sA s₁ R₁ renv V2 yst1 yst2 o) :
    SOut (model := model) P f lctx rets s₀ s₁ R renv V2 yst yst2 o := by
  obtain ⟨e', R₁, he', hle, hfr, henv', huniq', hsim⟩ := hhead
  obtain rfl : e' = env' := (Option.some.inj he').symm
  have ht := htail R₁ hle hfr henv' huniq'
  cases o with
  | normal =>
    obtain ⟨e2, R₂, hr2, hle2, hfr2, henv2, huniq2, hsim2⟩ := ht
    exact ⟨e2, R₂, hr2, hle.trans hle2, hfr2, henv2, huniq2,
      hsim.trans hsim2⟩
  | halt => exact hsim _ ht
  | «break» =>
    obtain ⟨lc, R₂, vals, hlc, hle2, hfr2, hforall, hcont⟩ := ht
    exact ⟨lc, R₂, vals, hlc, hle.trans hle2, hfr2, hforall,
      fun res hj => hsim res (hcont res hj)⟩
  | «continue» =>
    obtain ⟨lc, R₂, vals, hlc, hle2, hfr2, hforall, hcont⟩ := ht
    exact ⟨lc, R₂, vals, hlc, hle.trans hle2, hfr2, hforall,
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
    obtain ⟨e', R₁, hr, hle, hfr, henv', huniq, hsim⟩ := h
    exact ⟨e'.drop (e'.length - env.length), R₁, by rw [hr]; rfl, hle, hfr,
      henv'.restore hlen, huniq.drop _, hsim⟩
  | halt => exact h
  | «break» =>
    obtain ⟨lc, R₁, vals, hlc, hle, hfr, hforall, hcont⟩ := h
    exact ⟨lc, R₁, vals, hlc, hle, hfr,
      Forall2.imp_mem hforall (fun x hx v hv => by
        rw [get_restore_of_noShadow hns (hvars lc hlc x hx)]; exact hv), hcont⟩
  | «continue» =>
    obtain ⟨lc, R₁, vals, hlc, hle, hfr, hforall, hcont⟩ := h
    exact ⟨lc, R₁, vals, hlc, hle, hfr,
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
  exact ⟨env, R, by simpa using hrenv, Regs.Le.rfl R, hfresh, henv, huniq,
    SimS.rfl'⟩

/-- **The edge into a reserved join block.** `cond`'s join, `switch`'s join and
the loop's header/exit/post blocks are all *reserved* (`newBlock`) before the
edges into them are sealed, so the construction never sees their finished
bodies — only their parameter lists. `Completes.params` is exactly the
strengthening that bridges that gap: it fixes the finished block's parameters,
which is what `Exec`'s jump/branch rules need to bind the edge arguments. -/
theorem jumpTo_of_completes {P : Prog} {f : Func} {sRes sCont : BState}
    {bid : BlockId} {b : Block} {vals : List U256} {R : Regs} {st : EvmState}
    {res : FRes}
    (hcompl : Completes f sRes.fn)
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
    {st : EvmState}
    (hcompl : Completes f s₁.fn)
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
    {vals : List U256} {jb : Block} {st : EvmState}
    (hcompl : Completes f s₁.fn)
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
    {bb : Block} {st : EvmState}
    (hcompl : Completes f s₁.fn)
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
    {u : Unit} (hv : s.fn.curId < s.fn.blocks.size) (hcur : s.fn.cur = [])
    (hne : s.fn.curId ≠ bid) (hmv : moveTo bid s = some (u, s'))
    (hcompl : Completes f s'.fn) : CurPlaced f s.fn := by
  rw [M.moveTo_apply] at hmv
  obtain ⟨-, rfl⟩ := M.some_pair_inj hmv
  let b := s.fn.blocks[s.fn.curId]
  have hb : s.fn.blocks[s.fn.curId]? = some b :=
    Array.getElem?_eq_getElem hv
  have hf : f.blocks[s.fn.curId]? = some b := hcompl.sealed _ b hne hb
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
    (hk : CurResult renv s s') (hcompl : Completes f s'.fn)
    (hfin : renv = none → CurFinal f s'.fn) (hcp : CurPlaced f s'.fn) :
    CurPlaced f s.fn := by
  cases renv with
  | some env =>
    rcases hk with ⟨hc, ⟨Δ, hcur⟩, -⟩ | ⟨hne, b, hb, Δ, hi⟩
    · exact hcp.ofPrefix hc Δ hcur
    · exact ⟨⟨Δ, b.term⟩, b, hcompl.sealed _ b hne hb, hi, rfl⟩
  | none =>
    rcases hk with ⟨hne, b, hb, Δ, hi⟩ | ⟨hc, b, hb, Δ, hi⟩
    · exact ⟨⟨Δ, b.term⟩, b, hcompl.sealed _ b hne hb, hi, rfl⟩
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
    (hvalid : CurValid s₀)
    (hcompl : Completes f s₁.fn) (hcp : CurPlaced f s₁.fn)
    (hfin : renv = none → CurFinal f s₁.fn)
    (htr : trStmts fenv env lctx rets d ss s₀ = some (renv, s₁)) :
    CurPlaced f s₀.fn := by
  cases d with
  | false =>
    obtain ⟨-, hk⟩ := trStmts_cur fenv env lctx rets false ss s₀ renv s₁
      hvalid htr
    exact curPlaced_back hk hcompl hfin hcp
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
  obtain ⟨R₁, hle, hfr, hi, hsim⟩ := h
  exact ⟨R₁, hle, hfr, by rw [Regs.getMany_cons, hi]; simp, hsim⟩

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
  obtain ⟨R₁, hle, hfr, hget, hsim⟩ := hE
  refine ⟨vars.zip ids' ++ env, R₁, hrenv, hle, hfr, ?_, ?_, hsim⟩
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
  obtain ⟨R₁, hle, hfr, hget, hsim⟩ := hE
  exact ⟨env.setMany vars ids', R₁, hrenv, hle, hfr,
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
  obtain ⟨R₁, -, -, hget, hsim⟩ := hA
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
  obtain ⟨R₁, hle, hfr, hget, hsim⟩ := hA
  subst hsB
  subst hs₁
  refine ⟨env, R₁, hrenv, hle, hfr, henv.mono hle, huniq, ?_⟩
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
    hrenv, hle, ?_, ?_, ?_, ?_⟩
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
      (rets : Option (List Ident)) (s₀ s₁ : BState) (renv : Option VMap),
    FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
    env.Unique → RegsFresh R s₀.fn → CurValid s₀ →
    Completes f s₁.fn → CurPlaced f s₁.fn →
    (renv = none → CurFinal f s₁.fn) →
    trStmt fenv env lctx rets (.exprStmt e) s₀ = some (renv, s₁) →
    SOut (model := model) P f lctx rets s₀ s₁ R renv V' yst yst' o

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

The `.loop` clause is deliberately `True` for now: the loop-iteration class
needs the header/exit/post choreography, which is the round that attacks the
`for` family. Every other clause is final. -/
def Motive (P : Prog) (f : Func) (funs : YulSemantics.FunEnv yulD)
    (V : VEnv yulD) (yst : EvmState) :
    YulSemantics.Code Op → YulSemantics.Res yulD → Prop
  | .expr e, .eres (.vals vs yst') =>
      (∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState) (i : ValId)
          (v : U256),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        RegsFresh R s₀.fn → Completes f s₁.fn → CurPlaced f s₁.fn → vs = [v] →
        trExpr fenv env e s₀ = some (i, s₁) →
        EOut (model := model) P f s₀ s₁ R i v yst yst')
      ∧ (∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState) (n : Nat)
          (ids : List ValId),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        RegsFresh R s₀.fn → Completes f s₁.fn → CurPlaced f s₁.fn →
        vs.length = n →
        trExprN fenv env n e s₀ = some (ids, s₁) →
        EOutL (model := model) P f s₀ s₁ R ids vs yst yst')
      ∧ (vs = [] → EStmtOut (model := model) P f funs V yst e V yst' .normal)
  | .expr e, .eres (.halt yst') =>
      (∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState) (i : ValId),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        RegsFresh R s₀.fn → Completes f s₁.fn → CurPlaced f s₁.fn →
        trExpr fenv env e s₀ = some (i, s₁) →
        EOutHalt (model := model) P f s₀ R yst yst')
      ∧ (∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState) (n : Nat)
          (ids : List ValId),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        RegsFresh R s₀.fn → Completes f s₁.fn → CurPlaced f s₁.fn →
        trExprN fenv env n e s₀ = some (ids, s₁) →
        EOutHalt (model := model) P f s₀ R yst yst')
      ∧ EStmtOut (model := model) P f funs V yst e V yst' .halt
  | .args es, .eres (.vals vs yst') =>
      ∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState)
        (ids : List ValId),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        RegsFresh R s₀.fn → Completes f s₁.fn → CurPlaced f s₁.fn →
        trArgs fenv env es s₀ = some (ids, s₁) →
        EOutL (model := model) P f s₀ s₁ R ids vs yst yst'
  | .args es, .eres (.halt yst') =>
      ∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState)
        (ids : List ValId),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        RegsFresh R s₀.fn → Completes f s₁.fn → CurPlaced f s₁.fn →
        trArgs fenv env es s₀ = some (ids, s₁) →
        EOutHalt (model := model) P f s₀ R yst yst'
  | .stmt st, .sres V' yst' o =>
      ∀ (fenv : FMap) (env : VMap) (R : Regs) (lctx : Option LoopCtx)
        (rets : Option (List Ident)) (s₀ s₁ : BState) (renv : Option VMap),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        env.Unique → RegsFresh R s₀.fn → CurValid s₀ →
        Completes f s₁.fn → CurPlaced f s₁.fn →
        (renv = none → CurFinal f s₁.fn) →
        trStmt fenv env lctx rets st s₀ = some (renv, s₁) →
        SOut (model := model) P f lctx rets s₀ s₁ R renv V' yst yst' o
  | .stmts ss, .sres V' yst' o =>
      ∀ (fenv : FMap) (env : VMap) (R : Regs) (lctx : Option LoopCtx)
        (rets : Option (List Ident)) (s₀ s₁ : BState) (renv : Option VMap),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        env.Unique → RegsFresh R s₀.fn → CurValid s₀ →
        Completes f s₁.fn → CurPlaced f s₁.fn →
        (renv = none → CurFinal f s₁.fn) →
        trStmts fenv env lctx rets false ss s₀ = some (renv, s₁) →
        SOut (model := model) P f lctx rets s₀ s₁ R renv V' yst yst' o
  | _, _ => True

set_option maxHeartbeats 1000000 in
/-- **The construction simulation induction.** One `induction … with` over the
source `Step` derivation, with `Motive` above. Cases still open carry their own
`sorry`; everything else is discharged by the per-case lemmas above. -/
theorem sim {P : Prog} {f : Func} {funs : YulSemantics.FunEnv yulD}
    {V : VEnv yulD} {yst : EvmState} {c : YulSemantics.Code Op}
    {res : YulSemantics.Res yulD}
    (h : YulSemantics.Step yulD funs V yst c res) :
    Motive (model := model) P f funs V yst c res := by
  induction h generalizing P f with
  | @lit funs V st l =>
    refine ⟨?_, ?_, ?_⟩
    · intro fenv env R s₀ s₁ i v _ _ hfr _ _ hvs htr
      obtain rfl : v = YulSemantics.EVM.litValue l := by simpa using hvs.symm
      exact sim_lit hfr htr
    · intro fenv env R s₀ s₁ n ids _ _ hfr _ _ _ htr
      obtain ⟨-, i, rfl, htrE⟩ := trExprN_nonCall_inv (by intro fn args; simp) htr
      exact (sim_lit hfr htrE).toEOutL
    · intro _ fenv env R lctx rets s₀ s₁ renv _ _ _ _ _ _ _ _ htr
      rw [trStmt] at htr
      · exact absurd htr (by simp [reject])
      · intro op args h; cases h
      · intro fn args h; cases h
  | @var funs V st x v hget =>
    refine ⟨?_, ?_, ?_⟩
    · intro fenv env R s₀ s₁ i v' _ henv hfr _ _ hvs htr
      obtain rfl : v' = v := by simpa using hvs.symm
      exact sim_var hfr henv hget htr
    · intro fenv env R s₀ s₁ n ids _ henv hfr _ _ _ htr
      obtain ⟨-, i, rfl, htrE⟩ := trExprN_nonCall_inv (by intro fn args; simp) htr
      exact (sim_var hfr henv hget htrE).toEOutL
    · intro _ fenv env R lctx rets s₀ s₁ renv _ _ _ _ _ _ _ _ htr
      rw [trStmt] at htr
      · exact absurd htr (by simp [reject])
      · intro op args h; cases h
      · intro fn args h; cases h
  | @builtinOk funs V st op args argvals st1 rets st2 hargs hb iha =>
    have key : ∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState)
        (i : ValId) (v : U256), FEnvOK (model := model) P funs fenv →
        EnvOK (model := model) env V R → RegsFresh R s₀.fn →
        Completes f s₁.fn → CurPlaced f s₁.fn → rets = [v] →
        trExpr fenv env (.builtin op args) s₀ = some (i, s₁) →
        EOut (model := model) P f s₀ s₁ R i v st st2 := by
      intro fenv env R s₀ s₁ i v hfe henv hfr hcompl hcp hvs htr
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
      obtain ⟨R₁, hle, hfr₁, hget, hsim⟩ := iha fenv env R s₀ sA as hfe henv hfr
        (SGrowsAt.completes_of
          (SGrows.of_grows ((Grows.of_freshVal rfl).trans (Grows.of_emit rfl))) hcompl)
        (curPlaced_back_grows ((Grows.of_freshVal rfl).trans (Grows.of_emit rfl)) hcp) h1
      refine ⟨R₁.set sA.fn.nextVal v, hle.trans (Regs.Le.set _ hfr₁.unbound),
        hfr₁.set _ (Nat.le_refl _), Regs.set_same .., hsim.trans ?_⟩
      exact simS_op (P := P) (f := f) (fn := sA.fn)
        (fn' := { { sA.fn with nextVal := sA.fn.nextVal + 1 } with
          cur := Instr.op [sA.fn.nextVal] op as :: sA.fn.cur }) hget hb rfl rfl rfl
    refine ⟨key, ?_, ?_⟩
    · intro fenv env R s₀ s₁ n ids hfe henv hfr hcompl hcp hlen htr
      obtain ⟨rfl, i, rfl, htrE⟩ := trExprN_nonCall_inv (by intro fn args'; simp) htr
      obtain ⟨v, rfl⟩ : ∃ v, rets = [v] := by
        cases rets with
        | nil => simp at hlen
        | cons v vs =>
          cases vs with
          | nil => exact ⟨v, rfl⟩
          | cons w ws => simp at hlen
      exact (key fenv env R s₀ s₁ i v hfe henv hfr hcompl hcp rfl htrE).toEOutL
    · intro hrets fenv env R lctx rs s₀ s₁ renv hfe henv huniq hfr _ hcompl hcp _ htr
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
          (iha fenv env R s₀ sA as hfe henv hfr
            (SGrowsAt.completes_of (SGrows.of_grows hg) hcompl)
            (curPlaced_back_grows hg hcp) h1)
          (hrets ▸ hb) htr0
  | @builtinHalt funs V st op args argvals st1 st2 hargs hb iha =>
    have key : ∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState)
        (i : ValId), FEnvOK (model := model) P funs fenv →
        EnvOK (model := model) env V R → RegsFresh R s₀.fn →
        Completes f s₁.fn → CurPlaced f s₁.fn →
        trExpr fenv env (.builtin op args) s₀ = some (i, s₁) →
        EOutHalt (model := model) P f s₀ R st st2 := by
      intro fenv env R s₀ s₁ i hfe henv hfr hcompl hcp htr
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
      obtain ⟨R₁, -, -, hget, hsim⟩ := iha fenv env R s₀ sA as hfe henv hfr
        (SGrowsAt.completes_of (SGrows.of_grows hg) hcompl)
        (curPlaced_back_grows hg hcp) h1
      obtain ⟨rest, hcur⟩ := hcp
      exact hsim (.halt st2) (execFrom_opHalt hcur hget hb)
    refine ⟨key, ?_, ?_⟩
    · intro fenv env R s₀ s₁ n ids hfe henv hfr hcompl hcp htr
      obtain ⟨-, i, -, htrE⟩ := trExprN_nonCall_inv (by intro fn args'; simp) htr
      exact key fenv env R s₀ s₁ i hfe henv hfr hcompl hcp htrE
    · intro fenv env R lctx rs s₀ s₁ renv hfe henv _huniq hfr _ hcompl hcp hfin htr
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
          (iha fenv env R s₀ sA as hfe henv hfr
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
        obtain ⟨R₁, -, -, hget, hsim⟩ :=
          iha fenv env R s₀ sA as hfe henv hfr
            (SGrowsAt.completes_of (SGrows.of_grows hg) hcompl)
            (curPlaced_back_grows hg hcp) h1
        obtain ⟨rest, hcur⟩ := hcp
        exact hsim (.halt st2) (execFrom_opHalt hcur hget hb)
  | @builtinArgsHalt funs V st op args st1 hargs iha =>
    have key : ∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState)
        (i : ValId), FEnvOK (model := model) P funs fenv →
        EnvOK (model := model) env V R → RegsFresh R s₀.fn →
        Completes f s₁.fn → CurPlaced f s₁.fn →
        trExpr fenv env (.builtin op args) s₀ = some (i, s₁) →
        EOutHalt (model := model) P f s₀ R st st1 := by
      intro fenv env R s₀ s₁ i hfe henv hfr hcompl hcp htr
      rw [trExpr] at htr
      obtain ⟨as, sA, h1, htr'⟩ := M.bind_inv htr
      obtain ⟨d, sB, h2, htr''⟩ := M.bind_inv htr'
      obtain ⟨u, sC, h3, h4⟩ := M.bind_inv htr''
      obtain ⟨-, rfl⟩ := M.pure_inv h4
      have hg1 : Grows sA s₁ := (Grows.of_freshVal h2).trans (Grows.of_emit h3)
      exact iha fenv env R s₀ sA as hfe henv hfr
        (SGrowsAt.completes_of (SGrows.of_grows hg1) hcompl)
        (curPlaced_back_grows hg1 hcp) h1
    refine ⟨key, ?_, ?_⟩
    · intro fenv env R s₀ s₁ n ids hfe henv hfr hcompl hcp htr
      obtain ⟨-, i, -, htrE⟩ := trExprN_nonCall_inv (by intro fn args'; simp) htr
      exact key fenv env R s₀ s₁ i hfe henv hfr hcompl hcp htrE
    · intro fenv env R lctx rs s₀ s₁ renv hfe henv _huniq hfr _ hcompl hcp hfin htr
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
          (iha fenv env R s₀ sA as hfe henv hfr
            (SGrowsAt.completes_of (SGrowsAt.of_sealCur h2) hcompl) hcpA h1)
      · rw [if_neg hop] at htr
        obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
        obtain ⟨-, rfl⟩ := M.pure_inv h3
        have hg : Grows sA s₁ := Grows.of_emit h2
        exact SOut.ofExprHalt
          (iha fenv env R s₀ sA as hfe henv hfr
            (SGrowsAt.completes_of (SGrows.of_grows hg) hcompl)
            (curPlaced_back_grows hg hcp) h1)
  -- Blocked on a callee-construction bridge: inverting `FuncOK`/`trFunc` must
  -- provide `Completes`/entry placement for the generated callee and relate
  -- its parameter/zero-return register initialization to the source call env.
  | callOk hargs hlk harity hbody ho iha ihb => sorry
  | callHalt hargs hlk harity hbody iha ihb => sorry
  | @callArgsHalt funs V st fn args st1 hargs iha =>
    have key : ∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState)
        (i : ValId), FEnvOK (model := model) P funs fenv →
        EnvOK (model := model) env V R → RegsFresh R s₀.fn →
        Completes f s₁.fn → CurPlaced f s₁.fn →
        trExpr fenv env (.call fn args) s₀ = some (i, s₁) →
        EOutHalt (model := model) P f s₀ R st st1 := by
      intro fenv env R s₀ s₁ i hfe henv hfr hcompl hcp htr
      rw [trExpr] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      obtain ⟨fid, sB, h2, htr⟩ := M.bind_inv htr
      obtain ⟨d, sC, h3, htr⟩ := M.bind_inv htr
      obtain ⟨u, sD, h4, h5⟩ := M.bind_inv htr
      obtain ⟨-, rfl⟩ := M.pure_inv h5
      have hg : Grows sA s₁ := (Grows.of_liftO h2).trans
        ((Grows.of_freshVal h3).trans (Grows.of_emit h4))
      exact iha fenv env R s₀ sA as hfe henv hfr
        (SGrowsAt.completes_of (SGrows.of_grows hg) hcompl)
        (curPlaced_back_grows hg hcp) h1
    refine ⟨key, ?_, ?_⟩
    · intro fenv env R s₀ s₁ n ids hfe henv hfr hcompl hcp htr
      rw [trExprN] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      obtain ⟨fid, sB, h2, htr⟩ := M.bind_inv htr
      obtain ⟨ds, sC, h3, htr⟩ := M.bind_inv htr
      obtain ⟨u, sD, h4, h5⟩ := M.bind_inv htr
      obtain ⟨-, rfl⟩ := M.pure_inv h5
      have hg : Grows sA s₁ := (Grows.of_liftO h2).trans
        ((Grows.of_mapM_freshVal h3).trans (Grows.of_emit h4))
      exact iha fenv env R s₀ sA as hfe henv hfr
        (SGrowsAt.completes_of (SGrows.of_grows hg) hcompl)
        (curPlaced_back_grows hg hcp) h1
    · intro fenv env R lctx rs s₀ s₁ renv hfe henv _huniq hfr _ hcompl hcp _ htr
      rw [trStmt] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      obtain ⟨fid, sB, h2, htr⟩ := M.bind_inv htr
      obtain ⟨u, sC, h3, h4⟩ := M.bind_inv htr
      obtain ⟨-, rfl⟩ := M.pure_inv h4
      have hg : Grows sA s₁ := (Grows.of_liftO h2).trans (Grows.of_emit h3)
      exact SOut.ofExprHalt
        (iha fenv env R s₀ sA as hfe henv hfr
          (SGrowsAt.completes_of (SGrows.of_grows hg) hcompl)
          (curPlaced_back_grows hg hcp) h1)
  | @argsNil funs V st =>
    intro fenv env R s₀ s₁ ids _ _ hfr _ _ htr
    exact sim_args_nil hfr htr
  | @argsCons funs V st e rest restvals st1 v st2 hrest hhead ihr ihh =>
    intro fenv env R s₀ s₁ ids hfe henv hfr hcompl hcp htr
    rw [trArgs] at htr
    obtain ⟨restIds, sA, h1, htr'⟩ := M.bind_inv htr
    obtain ⟨i, s₁, h2, h3⟩ := M.bind_inv htr'
    obtain ⟨rfl, rfl⟩ := M.pure_inv h3
    have hgE : Grows sA s₁ := trExpr_grows e fenv env sA s₁ i h2
    have hcomplA : Completes f sA.fn :=
      SGrowsAt.completes_of (SGrows.of_grows hgE) hcompl
    have hcpA : CurPlaced f sA.fn := curPlaced_back_grows hgE hcp
    refine sim_args_cons
      (ihr fenv env R s₀ sA restIds hfe henv hfr hcomplA hcpA h1) ?_
    intro R' hle hfrA
    exact (ihh.1 fenv env R' sA s₁ i v hfe (henv.mono hle) hfrA hcompl hcp rfl h2)
  | @argsRestHalt funs V st e rest st1 hrest ihr =>
    intro fenv env R s₀ s₁ ids hfe henv hfr hcompl hcp htr
    rw [trArgs] at htr
    obtain ⟨restIds, sA, h1, htr'⟩ := M.bind_inv htr
    obtain ⟨i, s₁, h2, h3⟩ := M.bind_inv htr'
    obtain ⟨rfl, rfl⟩ := M.pure_inv h3
    have hgE : Grows sA s₁ := trExpr_grows e fenv env sA s₁ i h2
    exact ihr fenv env R s₀ sA restIds hfe henv hfr
      (SGrowsAt.completes_of (SGrows.of_grows hgE) hcompl)
      (curPlaced_back_grows hgE hcp) h1
  | @argsHeadHalt funs V st e rest restvals st1 st2 hrest hhead ihr ihh =>
    intro fenv env R s₀ s₁ ids hfe henv hfr hcompl hcp htr
    rw [trArgs] at htr
    obtain ⟨restIds, sA, h1, htr'⟩ := M.bind_inv htr
    obtain ⟨i, s₁, h2, h3⟩ := M.bind_inv htr'
    obtain ⟨rfl, rfl⟩ := M.pure_inv h3
    have hgE : Grows sA s₁ := trExpr_grows e fenv env sA s₁ i h2
    have hcomplA : Completes f sA.fn :=
      SGrowsAt.completes_of (SGrows.of_grows hgE) hcompl
    have hcpA : CurPlaced f sA.fn := curPlaced_back_grows hgE hcp
    obtain ⟨R₁, hle, hfrA, hget, hsim⟩ :=
      ihr fenv env R s₀ sA restIds hfe henv hfr hcomplA hcpA h1
    exact hsim (.halt st2)
      (ihh.1 fenv env R₁ sA s₁ i hfe (henv.mono hle) hfrA hcompl hcp h2)
  | @funDef funs V st n ps rs b =>
    intro fenv env R lctx rets s₀ s₁ renv _ _ _ _ _ _ _ _ htr
    rw [trStmt] at htr
    exact absurd htr (by simp [reject])
  -- Blocked on the hoisted-function completion invariant described below:
  -- `allocScope` plus the later `fillFunc`s must construct the `FEnvOK` needed
  -- to instantiate the statement-list IH under `hoist body :: funs`.
  | block hb ihb => sorry
  | @letZero funs V st vars =>
    intro fenv env R lctx rets s₀ s₁ renv _ henv huniq hfr _ _ _ _ htr
    exact sim_letDecl_none hfr henv huniq htr
  | @letVal funs V st vars e vals st1 he hlen ihe =>
    intro fenv env R lctx rets s₀ s₁ renv hfe henv huniq hfr _ hcompl hcp _ htr
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
      (ihe.2.1 fenv env R s₀ s₁ vars.length ids hfe henv hfr hcompl hcp hlen h1) htr0
  | @letHalt funs V st vars e st1 he ihe =>
    intro fenv env R lctx rets s₀ s₁ renv hfe henv _huniq hfr _ hcompl hcp _ htr
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
      (ihe.2.1 fenv env R s₀ s₁ vars.length ids hfe henv hfr hcompl hcp h1)
  | @assignVal funs V st vars e vals st1 he hlen ihe =>
    intro fenv env R lctx rets s₀ s₁ renv hfe henv huniq hfr _ hcompl hcp _ htr
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
      (ihe.2.1 fenv env R s₀ s₁ vars.length ids hfe henv hfr hcompl hcp hlen h1) htr0
  | @assignHalt funs V st vars e st1 he ihe =>
    intro fenv env R lctx rets s₀ s₁ renv hfe henv _huniq hfr _ hcompl hcp _ htr
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
      (ihe.2.1 fenv env R s₀ s₁ vars.length ids hfe henv hfr hcompl hcp h1)
  | exprStmt he ihe => exact ihe.2.2 rfl
  | exprStmtHalt he ihe => exact ihe.2.2
  -- `trScope_none_cur_nil` now supplies the formerly missing `CurPlaced` at
  -- the selected body's output.  The next premise of `ihb`, however, is
  -- genuinely unavailable: `Completes f sH.fn` requires the enclosing join
  -- block (reserved before the body and non-current at `sH`) to equal its
  -- final block in `f`.  At the conditional output that join is current/open,
  -- so the available `Completes f s₁.fn` deliberately gives only parameter
  -- agreement there; later statements may extend the join, making exact
  -- equality false.  Closing this case therefore needs a completion invariant
  -- parameterized by protected enclosing joins (and corresponding backwards
  -- transfer/edge lemmas), not another current-placement fact.  The switch-arm
  -- pair has the same common-join obligation.
  | ifTrue hc hnz hbody ihc ihb => sorry
  | @ifFalse funs V st c body cv st1 hc hz ihc =>
    intro fenv env R lctx rets s₀ s₁ renv hfe henv huniq hfr hvalid hcompl hcp _ htr
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
        h7 (by rw [hcurFE]; exact hbodyNe) gsuffix hcompl
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
    obtain ⟨RA, hleA, hfrA, hcv, hsimC⟩ :=
      ihc.1 fenv env R s₀ sA cvId cv hfe henv hfr
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
      RA.setMany joinParams vals, hrenv, hleA.trans hleJ, hfrJ, henvJ,
      huniq.setMany _ _, hsimC.trans hsimJ⟩
  | @ifHalt funs V st c body st1 hc ihc =>
    intro fenv env R lctx rets s₀ s₁ renv hfe henv _huniq hfr hvalid hcompl hcp _ htr
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
        h7 (by rw [hcurFE]; exact hbodyNe) gsuffix hcompl
    have hcpE : CurPlaced f sE.fn :=
      ⟨⟨[], .branch cv ⟨bodyId, []⟩ ⟨joinId, xvals⟩⟩,
        curOK_of_sealCur hfinalF h6⟩
    have hcpA : CurPlaced f sA.fn := csAE.placed_back hcpE
    have hcomplA : Completes f sA.fn := SGrowsAt.completes_of
      (SGrowsAt.trans aAE
        (SGrowsAt.trans (SGrowsAt.of_sealCur (N := sA.fn.blocks.size) h6)
          (SGrowsAt.trans
            (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hbodyBase) h7)
            gsuffix))) hcompl
    exact SOut.ofExprHalt
      (ihc.1 fenv env R s₀ sA cv hfe henv hfr hcomplA hcpA h1)
  -- Blocked on the analogous selected-chain lemma for `trCases`: identify the
  -- `selectSwitch` body reached by the emitted equality-test chain and rebuild
  -- the common join environment/parameter register file.
  | switchExec hc hsel ihc ihs => sorry
  | switchHalt hc ihc => sorry
  -- Blocked earlier than the statement shell: `Motive`'s `.loop` clause is
  -- still `True`; it must carry the header/body/post/exit continuation and
  -- loop-parameter register invariant before `forLoop` can consume `ihl`.
  | forLoop hinit hloop ihi ihl => sorry
  | forInitHalt hinit ihi => sorry
  | @«break» funs V st =>
    intro fenv env R lctx rets s₀ s₁ renv _ henv _huniq hfr _ _ _ hfin htr
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
    intro fenv env R lctx rets s₀ s₁ renv _ henv _huniq hfr _ _ _ hfin htr
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
    intro fenv env R lctx rets s₀ s₁ renv _ henv _huniq hfr _ _ _ hfin htr
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
    intro fenv env R lctx rets s₀ s₁ renv _ henv huniq hfr _ _ _ _ htr
    exact sim_seqNil henv huniq hfr htr
  | @seqCons funs V st s rest V1 st1 V2 st2 o h1 h2 ih1 ih2 =>
    intro fenv env R lctx rets s₀ s₁ renv hfe henv huniq hfr hvalid hcompl hcp hfin htr
    cases s with
    | funDef n ps rs body =>
      cases h1
      rw [trStmts] at htr
      obtain ⟨fid, sA, ha, htr⟩ := M.bind_inv htr
      obtain ⟨g, sB, hb, htr⟩ := M.bind_inv htr
      obtain ⟨u, sC, hc, htail⟩ := M.bind_inv htr
      have hfnA : sA.fn = s₀.fn := congrArg BState.fn (M.liftO_inv ha).2
      have hfnB : sB.fn = sA.fn := (trFunc_grows fenv ps rs body sA g sB hb).1
      have hfnC : sC.fn = sB.fn := by rw [(M.fillFunc_inv hc).choose_spec]
      have hfn : sC.fn = s₀.fn := hfnC.trans (hfnB.trans hfnA)
      have hvalidC : CurValid sC := by rw [CurValid, hfn]; exact hvalid
      simpa only [SOut, hfn] using
        (ih2 fenv env R lctx rets sC s₁ renv hfe henv
          huniq (by simpa only [hfn] using hfr) hvalidC
          hcompl hcp hfin htail)
    | block body | letDecl vars val | assign vars e | cond e body
    | forLoop init e post body | «break» | «continue» | leave
    | switch e cases dflt | exprStmt e =>
      obtain ⟨renvA, sA, hhead, htail⟩ := trStmts_false_cons_inv
        (by intros; simp) htr
      have hvalidA : CurValid sA := (trStmt_cur hvalid hhead).1
      cases renvA with
      | none =>
        obtain ⟨hrenv, hfn⟩ := trStmts_true_fn fenv env lctx rets rest sA s₁ renv htail
        have hcomplA : Completes f sA.fn := by simpa only [hfn] using hcompl
        have hcpA : CurPlaced f sA.fn := by simpa only [hfn] using hcp
        have hfinA : CurFinal f sA.fn := by
          simpa only [hfn] using hfin hrenv
        obtain ⟨envA, R₁, hbad, -⟩ :=
          ih1 fenv env R lctx rets s₀ sA none hfe henv huniq hfr hvalid hcomplA hcpA
            (fun _ => hfinA) hhead
        exact absurd hbad (by simp)
      | some envA =>
        have hgTail : SGrows sA s₁ :=
          trStmts_grows fenv envA lctx rets false rest sA renv s₁ htail
        have hcomplA : Completes f sA.fn := SGrowsAt.completes_of hgTail hcompl
        have hcpA : CurPlaced f sA.fn :=
          trStmts_curPlaced_back hvalidA hcompl hcp hfin htail
        refine SOut.seq
          (ih1 fenv env R lctx rets s₀ sA (some envA) hfe henv huniq hfr hvalid hcomplA hcpA
            (by simp) hhead) ?_
        intro R₁ hle hfrA henvA huniqA
        exact ih2 fenv envA R₁ lctx rets sA s₁ renv hfe henvA huniqA hfrA
          hvalidA hcompl hcp hfin htail
  | @seqStop funs V st s rest V1 st1 o h1 hne ih1 =>
    intro fenv env R lctx rets s₀ s₁ renv hfe henv huniq hfr hvalid hcompl hcp hfin htr
    cases s with
    | funDef n ps rs body =>
      cases h1
      exact absurd rfl hne
    | block body | letDecl vars val | assign vars e | cond e body
    | forLoop init e post body | «break» | «continue» | leave
    | switch e cases dflt | exprStmt e =>
      obtain ⟨renvA, sA, hhead, htail⟩ := trStmts_false_cons_inv
        (by intros; simp) htr
      have hvalidA : CurValid sA := (trStmt_cur hvalid hhead).1
      cases renvA with
      | none =>
        obtain ⟨hrenv, hfn⟩ := trStmts_true_fn fenv env lctx rets rest sA s₁ renv htail
        have hcomplA : Completes f sA.fn := by simpa only [hfn] using hcompl
        have hcpA : CurPlaced f sA.fn := by simpa only [hfn] using hcp
        have hfinA : CurFinal f sA.fn := by simpa only [hfn] using hfin hrenv
        exact SOut.of_nonNormal hne (by rw [hfn])
          (ih1 fenv env R lctx rets s₀ sA none hfe henv huniq hfr hvalid hcomplA hcpA
            (fun _ => hfinA) hhead)
      | some envA =>
        have hgTail : SGrows sA s₁ :=
          trStmts_grows fenv envA lctx rets false rest sA renv s₁ htail
        have hcomplA : Completes f sA.fn := SGrowsAt.completes_of hgTail hcompl
        have hcpA : CurPlaced f sA.fn :=
          trStmts_curPlaced_back hvalidA hcompl hcp hfin htail
        exact SOut.of_nonNormal hne hgTail.nextVal
          (ih1 fenv env R lctx rets s₀ sA (some envA) hfe henv huniq hfr hvalid hcomplA hcpA
            (by simp) hhead)
  | loopDone => trivial
  | loopCondHalt => trivial
  | loopStep => trivial
  | loopPostHalt => trivial
  | loopBreak => trivial
  | loopLeave => trivial
  | loopBodyHalt => trivial

/--
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

One prerequisite the shell still needs, not yet built: the analogue of
`SimAsm.hoist_ok` — from `allocScope body` and the source's `hoist body`,
construct `FEnvOK P (hoist yulD body :: funs) (scope :: fenv)`. Each entry's
`FuncOK` is established when `trStmts` reaches the corresponding `funDef` and
calls `fillFunc`, so the lemma has to be proved together with the `funDef` case
rather than before it.

What remains is the `induction … with` shell itself — which for `cond`,
`switch` and the loop family is now mostly the `trStmt`/`trCases` equation
inversion feeding the edge steps above (plus `edgeArgs_ok` for the edge values,
`modStmts_sound` for the variables the join does *not* carry, and `setMany_self`
for the `if`-false and loop-exit edges, which pass a variable its own current
value) — and the user-call pair `callOk`/`callHalt` (`FMap.get_ok`, `trFunc`,
and a fresh register file for the callee).
-/
theorem trScope_sim {P : Prog} {f : Func}
    {funs : YulSemantics.FunEnv yulD} {fenv : FMap}
    {V V' : VEnv yulD} {env : VMap} {R : Regs}
    {lctx : Option LoopCtx} {rets : Option (List Ident)}
    {body : List (Stmt Op)} {s₀ s₁ : BState} {renv : Option VMap}
    {yst yst' : EvmState} {o : Outcome}
    (_hwf : P.wfCheck = true)
    (_hcompl : Completes f s₁.fn)
    (_hfe : FEnvOK (model := model) P funs fenv)
    (_henv : EnvOK (model := model) env V R)
    (_huniq : env.Unique)
    (_htr : trScope fenv env lctx rets body s₀ = some (renv, s₁))
    (_hstep : YulSemantics.ExecStmt yulD funs V yst (.block body) V' yst' o) :
    SOut (model := model) P f lctx rets s₀ s₁ R renv V' yst yst' o := by
  -- Blocked on `sim`'s `block`/`hoist_ok` case; additionally this wrapper must
  -- expose or derive the `RegsFresh`, `CurValid`, `CurPlaced`, and diverting
  -- `CurFinal` premises required by the strengthened statement motive.
  sorry

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
  obtain ⟨hwf, main, s, hbuild, hmapM, rfl⟩ := ofBlock_inv hof
  obtain ⟨renv, s₁, htr, hparams, hnrets, hentry, hfuncs, hblocks⟩ :=
    buildMain_inv hbuild
  -- the finished `main` completes the builder state the top-level scope left
  have hext : Completes P.main s₁.fn := by
    cases renv with
    | none =>
      exact ⟨fun i b _ hi => by rw [hblocks]; exact hi,
        fun i b hb => ⟨b, by rw [hblocks]; exact hb, rfl⟩,
        by rw [hblocks]⟩
    | some e =>
      obtain ⟨b, hb, hmb⟩ := hblocks
      refine ⟨fun i b' hne hi => ?_, fun i b' hb' => ?_, ?_⟩
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
  -- the top-level source derivation is one `block` rule over `prog`
  rw [YulSemantics.Run] at hrun
  cases hrun with
  | @block _ _ _ _ Vb stb o hstmts =>
    have hsim := trScope_sim (model := model) (P := P) (f := P.main)
      (funs := []) (fenv := []) (V := []) (env := []) (R := Regs.empty)
      hwf hext .nil EnvOK.nil VMap.unique_nil htr (.block hstmts)
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
      obtain ⟨env', R₁, hrenv, _hle, _hfr, _henv', _huniq, hsimS⟩ := hsim
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
