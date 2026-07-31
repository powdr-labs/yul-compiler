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
theorem simS_const {P : Prog} {f : Func} {fn : FnState} {R : Regs}
    {st : EvmState} {d : ValId} {v : U256} :
    SimS (model := model) P f fn R st
      { fn with cur := .const d v :: fn.cur } (R.set d v) st := by
  intro res h
  obtain ⟨rest, ⟨b, hb, hinstrs, hterm⟩, hexec⟩ := h
  refine ⟨⟨.const d v :: rest.instrs, rest.term⟩, ⟨b, hb, ?_, hterm⟩, .const hexec⟩
  simpa using hinstrs

/-- `emit (.op ds yop as)` on the returning path. -/
theorem simS_op {P : Prog} {f : Func} {fn : FnState} {R : Regs}
    {st st' : EvmState} {ds : List ValId} {yop : Op} {as : List ValId}
    {args rets : List U256}
    (hargs : R.getMany as = some args)
    (hb : builtinWithExternal model.calls model.creates yop args st (.ok rets st'))
    (hlen : ds.length = rets.length) :
    SimS (model := model) P f fn R st
      { fn with cur := .op ds yop as :: fn.cur } (R.setMany ds rets) st' := by
  intro res h
  obtain ⟨rest, ⟨b, hbl, hinstrs, hterm⟩, hexec⟩ := h
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
    (hlen : ds.length = rvals.length) :
    SimS (model := model) P f fn R st
      { fn with cur := .call ds fid as :: fn.cur } (R.setMany ds rvals) st' := by
  intro res h
  obtain ⟨rest, ⟨b, hbl, hinstrs, hterm⟩, hexec⟩ := h
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
      renv = some env' ∧ Regs.Le R₀ R₁
        ∧ EnvOK (model := model) env' V' R₁
        ∧ SimS (model := model) P f s₀.fn R₀ yst s₁.fn R₁ yst'
  | .halt => ExecFrom (model := model) P f s₀.fn R₀ yst (.halt yst')
  | .break => ∃ (lc : LoopCtx) (R₁ : Regs) (vals : List U256),
      lctx = some lc ∧ Regs.Le R₀ R₁
        ∧ List.Forall₂ (fun x v => YulSemantics.VEnv.get V' x = some v) lc.vars vals
        ∧ ∀ res, JumpTo (model := model) P f lc.brkTgt vals R₁ yst' res
            → ExecFrom (model := model) P f s₀.fn R₀ yst res
  | .continue => ∃ (lc : LoopCtx) (R₁ : Regs) (vals : List U256),
      lctx = some lc ∧ Regs.Le R₀ R₁
        ∧ List.Forall₂ (fun x v => YulSemantics.VEnv.get V' x = some v) lc.vars vals
        ∧ ∀ res, JumpTo (model := model) P f lc.contTgt vals R₁ yst' res
            → ExecFrom (model := model) P f s₀.fn R₀ yst res
  | .leave => ∃ (rs : List Ident) (vals : List U256),
      rets = some rs
        ∧ List.Forall₂ (fun x v => YulSemantics.VEnv.get V' x = some v) rs vals
        ∧ ExecFrom (model := model) P f s₀.fn R₀ yst (.ret vals yst')

/--
**The `modStmts` over-approximation is sound** (the remaining analysis
obligation).

A statement list only changes the *outer* bindings its `modStmts` analysis
names: if `ss`, run from `V`, ends in `V'`, then every outer variable `x` that
the analysis does not report still reads back the value it had. (`x ∉ locals`
excludes the names `ss` declares itself, which `restore` drops anyway; the
analysis reports them relative to the enclosing list, which is why `locals` is
threaded.)

This is exactly what licenses `trStmt`'s `cond`, `switch` and `forLoop` cases to
thread only `modifiedX env bodies` through their join / header / exit block
parameters and to keep the *old* `ValId` for every other variable: SSA registers
persist across blocks, so an unreported variable's existing id still holds its
value. Missing names would be unsound; extra ones are harmless, because then
both incoming edges pass the same value.

Obligation: an induction over the source `Step` derivation whose statement-class
motive is the displayed property, with `True` on the expression classes (they do
not touch `V`) and the corresponding property on the loop-iteration class. The
interesting cases are `seqCons` (compose the two `restore`s, threading `locals`
through the `letDecl` that extends it), `block`/`forLoop` (nested `restore`),
and `switchExec` (the selected body is one of the bodies `modCases` scanned, by
`List.find?_mem` on `selectSwitch`).
-/
theorem modStmts_sound {funs : YulSemantics.FunEnv yulD} {V Vb : VEnv yulD}
    {yst ystb : EvmState} {o : Outcome} {locals : List Ident}
    {ss : List (Stmt Op)}
    (_h : YulSemantics.ExecStmts yulD funs V yst ss Vb ystb o) :
    ∀ x : Ident, x ∉ locals → x ∉ modStmts locals ss →
      YulSemantics.VEnv.get (YulSemantics.restore V Vb) x
        = YulSemantics.VEnv.get V x := by
  sorry

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

What is still missing, besides the induction itself, is
`modStmts_sound` below.
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
    (_htr : trScope fenv env lctx rets body s₀ = some (renv, s₁))
    (_hstep : YulSemantics.ExecStmt yulD funs V yst (.block body) V' yst' o) :
    SOut (model := model) P f lctx rets s₀ s₁ R renv V' yst yst' o := by
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
      hwf hext .nil EnvOK.nil htr (.block hstmts)
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
      obtain ⟨env', R₁, hrenv, _hle, _henv', hsimS⟩ := hsim
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

