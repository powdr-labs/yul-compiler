import YulEvmCompiler.Optimizer.Implementation.Normalization.DisambiguateAlpha
import YulEvmCompiler.Optimizer.Implementation.Frame
import YulSemantics.Equiv
import Mathlib.Data.List.Nodup
/-!
# Disambiguation renaming — environment transport layer

The semantic foundations for the disambiguation bisimulation: renaming a
variable environment (`renVEnv`) and a function environment (`RenScopeRel`/
`RenFunsRel`), with transport lemmas showing the big-step helpers (`get`, `set`,
`setMany`, `bindZeros`, `restore`, `lookupFun`, `hoist`) commute with the
renaming under the *satisfiable* injectivity configs `RenCfg`/`RenFCfg`
(injective on the in-scope keys, identity off them, fresh `dsName` images,
`NotFresh` keys) — not global injectivity, which the pass's renaming does not
have.

Built on the purely syntactic `DisambiguateAlpha`; the `Step` simulation proper
(`DisambiguateSound`) builds on this file's olean.
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

theorem renVEnv_zip (σ : Ident → Ident) (xs : List Ident) (vals : List D.Value) :
    renVEnv σ (xs.zip vals) = (xs.map σ).zip vals := by
  induction xs generalizing vals with
  | nil => rfl
  | cons x xs ih =>
      cases vals with
      | nil => rfl
      | cons v vals => simp only [List.zip_cons_cons, renVEnv_cons, List.map_cons, ih]

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

/-- `renVEnv` depends only on the renaming's values at the present keys. -/
theorem renVEnv_congr {σ τ : Ident → Ident} {V : VEnv D} (h : ∀ p ∈ V, σ p.1 = τ p.1) :
    renVEnv σ V = renVEnv τ V :=
  List.map_congr_left (fun p hp => by simp only [h p hp])

/-! ### Renaming a function environment

The function-environment side of the bisimulation. `RenScopeRel φ BR` relates a
source scope to a target scope whose keys are `φ`-renamed and whose declarations
are related by an (abstract) body relation `BR` — instantiated later with the
syntactic translation. A single `φ` serves the whole stack: Yul forbids shadowing
a visible function, so function names across the in-scope stack are distinct and
one injective `φ` renames them all consistently. -/

/-- Source/target function scopes: `φ`-renamed keys, `BR`-related declarations. -/
def RenScopeRel (φ : Ident → Ident) (BR : FDecl D → FDecl D → Prop) (s₁ s₂ : FScope D) : Prop :=
  List.Forall₂ (fun p q => q.1 = φ p.1 ∧ BR p.2 q.2) s₁ s₂

/-- Source/target function environments: related scope-by-scope under one `φ`. -/
def RenFunsRel (φ : Ident → Ident) (BR : FDecl D → FDecl D → Prop) (f₁ f₂ : FunEnv D) : Prop :=
  List.Forall₂ (RenScopeRel φ BR) f₁ f₂

theorem RenFunsRel.cons {φ : Ident → Ident} {BR : FDecl D → FDecl D → Prop}
    {s₁ s₂ : FScope D} {f₁ f₂ : FunEnv D} (hs : RenScopeRel φ BR s₁ s₂)
    (hf : RenFunsRel φ BR f₁ f₂) : RenFunsRel φ BR (s₁ :: f₁) (s₂ :: f₂) :=
  List.Forall₂.cons hs hf

/-! ### The function-name config `RenFCfg`

The `φ`-side analog of `RenCfg`: `φ` is injective on the function names in scope
across the whole `funs` stack (Yul forbids shadowing a visible function), is the
identity off them, maps them to fresh names, and all in-scope names are source
(`NotFresh`) names. The satisfiable replacement for the (unsatisfiable) global
`Function.Injective φ`. -/

/-- All function names in scope across a function environment. -/
def funNamesOf (funs : FunEnv D) : List Ident := funs.flatMap (fun s => s.map Prod.fst)

def RenFCfg (φ : Ident → Ident) (funs : FunEnv D) (N : Nat) : Prop :=
  (∀ a ∈ funNamesOf funs, ∀ b ∈ funNamesOf funs, φ a = φ b → a = b) ∧
  (∀ z, z ∉ funNamesOf funs → φ z = z) ∧
  (∀ a ∈ funNamesOf funs, ∃ k, k < N ∧ φ a = dsName k) ∧
  (∀ a ∈ funNamesOf funs, NotFresh a)

/-- The bound only grows. -/
theorem RenFCfg.mono {φ : Ident → Ident} {funs : FunEnv D} {N M : Nat}
    (h : RenFCfg φ funs N) (hNM : N ≤ M) : RenFCfg φ funs M :=
  ⟨h.1, h.2.1,
    fun a ha => (h.2.2.1 a ha).imp (fun k hk => ⟨Nat.lt_of_lt_of_le hk.1 hNM, hk.2⟩),
    h.2.2.2⟩

/-- The `renScopeRel_find`/`lookupFun` no-merge condition for a not-fresh name `fn`:
no in-scope function name renames onto `φ fn` (within any single scope of `funs`). -/
theorem RenFCfg.no_merge_scope {φ : Ident → Ident} {funs : FunEnv D} {N : Nat}
    (h : RenFCfg φ funs N)
    {fn : Ident} (hfn : NotFresh fn) {s : FScope D} (hs : s ∈ funs) :
    ∀ p ∈ s, φ p.1 = φ fn → p.1 = fn := by
  intro p hp hpq
  have hpmem : p.1 ∈ funNamesOf funs :=
    List.mem_flatMap.mpr ⟨s, hs, List.mem_map_of_mem hp⟩
  by_cases hfmem : fn ∈ funNamesOf funs
  · exact h.1 p.1 hpmem fn hfmem hpq
  · obtain ⟨k, _, hk⟩ := h.2.2.1 p.1 hpmem
    rw [h.2.1 fn hfmem, hk] at hpq
    exact absurd hpq.symm (hfn k)

theorem funNamesOf_cons (s : FScope D) (funs : FunEnv D) :
    funNamesOf (s :: funs) = s.map Prod.fst ++ funNamesOf funs := by
  simp [funNamesOf, List.flatMap_cons]

/-- `RenScopeRel` depends only on the renaming's values at the scope's keys. -/
theorem RenScopeRel.congr_phi {φ φ' : Ident → Ident} {BR : FDecl D → FDecl D → Prop}
    {s₁ s₂ : FScope D} (h : RenScopeRel φ BR s₁ s₂) (hag : ∀ p ∈ s₁, φ' p.1 = φ p.1) :
    RenScopeRel φ' BR s₁ s₂ := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons p q u₁ u₂ hpq _ ih =>
      exact List.Forall₂.cons ⟨hpq.1.trans (hag p (List.mem_cons_self ..)).symm, hpq.2⟩
        (ih (fun p hp => hag p (List.mem_cons_of_mem _ hp)))

/-- `RenFunsRel` transports to a renaming that agrees on the in-scope function
names (used when a block extends `φ` by its own function names). -/
theorem RenFunsRel.congr_phi {φ φ' : Ident → Ident} {BR : FDecl D → FDecl D → Prop}
    {f₁ f₂ : FunEnv D} (h : RenFunsRel φ BR f₁ f₂)
    (hag : ∀ fn ∈ funNamesOf f₁, φ' fn = φ fn) : RenFunsRel φ' BR f₁ f₂ := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons s₁ s₂ t₁ t₂ hs hR ih =>
      refine List.Forall₂.cons (hs.congr_phi (fun p hp => hag p.1 ?_))
        (ih (fun fn hfn => hag fn ?_))
      · rw [funNamesOf_cons]; exact List.mem_append.mpr (Or.inl (List.mem_map_of_mem hp))
      · rw [funNamesOf_cons]; exact List.mem_append.mpr (Or.inr hfn)

/-- A scope lookup transports across `RenScopeRel`: if `φ` merges no other key of
`s₁` onto `φ fn`, then `fn` resolves in `s₁` exactly when `φ fn` resolves in `s₂`,
to `BR`-related declarations. -/
theorem renScopeRel_find {φ : Ident → Ident} {BR : FDecl D → FDecl D → Prop}
    {s₁ s₂ : FScope D} (h : RenScopeRel φ BR s₁ s₂) (fn : Ident)
    (hinj : ∀ p ∈ s₁, φ p.1 = φ fn → p.1 = fn) :
    (s₁.find? (fun p => p.1 = fn) = none ∧ s₂.find? (fun p => p.1 = φ fn) = none) ∨
    (∃ p q, s₁.find? (fun p => p.1 = fn) = some p ∧ s₂.find? (fun p => p.1 = φ fn) = some q ∧
      q.1 = φ p.1 ∧ BR p.2 q.2) := by
  induction h with
  | nil => left; simp
  | @cons p q u₁ u₂ hpq _ ih =>
      by_cases hp : p.1 = fn
      · right
        refine ⟨p, q, List.find?_cons_of_pos (by simp [hp]),
          List.find?_cons_of_pos (by simp [hpq.1, hp]), hpq.1, hpq.2⟩
      · have hφ : ¬ (q.1 = φ fn) := by
          rw [hpq.1]; exact fun hc => hp (hinj p (List.mem_cons_self ..) hc)
        rw [List.find?_cons_of_neg (by simp [hp]), List.find?_cons_of_neg (by simp [hφ])]
        exact ih (fun p hp => hinj p (List.mem_cons_of_mem _ hp))

/-- `lookupFun` transports across `RenFunsRel`, under a per-scope no-merge
condition on the queried name (provided by `RenFCfg.no_merge_scope`): a resolved
function has a `φ`-renamed counterpart with a `BR`-related declaration and a
related closure environment. -/
theorem lookupFun_renFunsRel {φ : Ident → Ident} {BR : FDecl D → FDecl D → Prop}
    {f₁ f₂ : FunEnv D} (hR : RenFunsRel φ BR f₁ f₂) :
    ∀ {fn : Ident}, (∀ s ∈ f₁, ∀ p ∈ s, φ p.1 = φ fn → p.1 = fn) →
      ∀ {decl : FDecl D} {cenv : FunEnv D}, lookupFun f₁ fn = some (decl, cenv) →
      ∃ decl' cenv', lookupFun f₂ (φ fn) = some (decl', cenv') ∧
        BR decl decl' ∧ RenFunsRel φ BR cenv cenv' := by
  induction hR with
  | nil => intro fn _ decl cenv h; simp [lookupFun] at h
  | @cons s₁ s₂ t₁ t₂ hs hR' ih =>
      intro fn hnm decl cenv h
      rcases renScopeRel_find hs fn (hnm s₁ (List.mem_cons_self ..)) with
        ⟨hn₁, hn₂⟩ | ⟨p, q, hp₁, hp₂, hkey, hd⟩
      · rw [lookupFun, hn₁] at h
        obtain ⟨decl', cenv', hl', hbody, hRc⟩ :=
          ih (fun s hs' => hnm s (List.mem_cons_of_mem _ hs')) h
        exact ⟨decl', cenv', by rw [lookupFun, hn₂]; exact hl', hbody, hRc⟩
      · rw [lookupFun, hp₁] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hd_eq, hcenv_eq⟩ := h
        subst hd_eq; subst hcenv_eq
        exact ⟨q.2, s₂ :: t₂, by rw [lookupFun, hp₂], hd, List.Forall₂.cons hs hR'⟩

/-! ### Boundary renaming: renamed inner prefix over a shared outer suffix

For an *arbitrary-context* equivalence, the target environment is the source
with only the block's own (freshly-renamed) declarations changed, over an
identical outer suffix. A reference to an outer name is left unchanged by the
renaming and falls through the fresh inner keys to the shared suffix; a reference
to an inner name is renamed and resolves in the inner prefix. (For the
whole-program `Run` equivalence the outer suffix is empty, but the lemmas hold
generally.) -/

/-- `get` distributes over `++`: the first list wins, else the second. -/
theorem VEnv.get_append (A B : VEnv D) (k : Ident) :
    VEnv.get (A ++ B) k = (VEnv.get A k).orElse (fun _ => VEnv.get B k) := by
  simp only [VEnv.get, List.find?_append]
  cases A.find? (fun p => p.1 = k) <;> simp

/-- `get` transport across a boundary renaming. A lookup of `σ x`:
* if `x` is an inner (renamed) key, resolves in the renamed prefix to `x`'s value;
* otherwise `σ x = x` (outer names unrenamed) and, the fresh inner keys being
  disjoint from `x`, falls through to the shared suffix. -/
theorem get_boundary (σ : Ident → Ident) (inner outer : VEnv D) (x : Ident)
    (hinj : ∀ p ∈ inner, σ p.1 = σ x → p.1 = x)
    (hid : VEnv.get inner x = none → σ x = x) :
    VEnv.get (renVEnv σ inner ++ outer) (σ x) = VEnv.get (inner ++ outer) x := by
  rw [VEnv.get_append, VEnv.get_append, renVEnv_get σ inner x hinj]
  cases hgi : VEnv.get inner x with
  | some v => simp
  | none => simp [hid hgi]

/-- `set` over `++`: an in-place update hits the first list if the key occurs
there, otherwise the second (mirrors `VEnv.set`'s first-match, no-op-if-absent
behavior). The building block for boundary `set` transport. -/
theorem VEnv.set_append (A B : VEnv D) (k : Ident) (v : D.Value) :
    VEnv.set (A ++ B) k v =
      if (A.find? (fun p => p.1 = k)).isSome then VEnv.set A k v ++ B else A ++ VEnv.set B k v := by
  induction A with
  | nil => simp [VEnv.set]
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      by_cases hyk : y = k
      · simp [VEnv.set, List.find?_cons, hyk]
      · simp only [List.cons_append, VEnv.set, if_neg hyk, List.find?_cons, hyk,
          decide_false, cond_false, ih]
        cases (rest.find? (fun p => p.1 = k)).isSome <;> simp

/-- `set` is a no-op when the key is absent. -/
theorem VEnv.set_of_find_none (V : VEnv D) (k : Ident) (v : D.Value)
    (h : V.find? (fun p => p.1 = k) = none) : VEnv.set V k v = V := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      rw [List.find?_cons] at h
      by_cases hyk : y = k
      · simp [hyk] at h
      · simp only [VEnv.set, if_neg hyk]
        rw [ih (by simpa only [hyk, decide_false, cond_false] using h)]

theorem VEnv.get_eq_none_iff_find (V : VEnv D) (k : Ident) :
    VEnv.get V k = none ↔ V.find? (fun p => p.1 = k) = none := by
  simp only [VEnv.get, Option.map_eq_none_iff]

/-- `set` transport across a boundary renaming when `x` is an **inner** key: the
update hits the renamed prefix (searched first), leaving the shared outer suffix
untouched — no freshness-vs-outer condition needed, since the prefix wins even if
the fresh key coincides with an outer key. -/
theorem set_boundary_hit (σ : Ident → Ident) (inner outer : VEnv D) (x : Ident) (v : D.Value)
    (hinj : ∀ p ∈ inner, σ p.1 = σ x → p.1 = x) (hx : VEnv.get inner x ≠ none) :
    VEnv.set (renVEnv σ inner ++ outer) (σ x) v = renVEnv σ (VEnv.set inner x v) ++ outer := by
  have hget : VEnv.get (renVEnv σ inner) (σ x) = VEnv.get inner x := renVEnv_get σ inner x hinj
  rw [VEnv.set_append, if_pos, renVEnv_set σ inner x v hinj]
  exact Option.isSome_iff_ne_none.mpr
    (fun hc => hx (hget ▸ (VEnv.get_eq_none_iff_find _ _).mpr hc))

/-- `set` transport when `x` is **not** an inner key: `σ x = x` and the update
falls through the fresh prefix (which lacks `x`) to the shared outer suffix. -/
theorem set_boundary_miss (σ : Ident → Ident) (inner outer : VEnv D) (x : Ident) (v : D.Value)
    (hinj : ∀ p ∈ inner, σ p.1 = σ x → p.1 = x)
    (hx : VEnv.get inner x = none) (hid : σ x = x) :
    VEnv.set (renVEnv σ inner ++ outer) (σ x) v = renVEnv σ inner ++ VEnv.set outer x v := by
  have hget : VEnv.get (renVEnv σ inner) (σ x) = VEnv.get inner x := renVEnv_get σ inner x hinj
  have hrn : (renVEnv σ inner).find? (fun p => p.1 = σ x) = none :=
    (VEnv.get_eq_none_iff_find _ _).mp (hget.trans hx)
  rw [VEnv.set_append, if_neg (by rw [hrn]; simp), hid]

/-- A block/scope exit (`restore`) drops exactly the bindings it introduced,
returning to the entry environment. -/
theorem restore_prefix (A E : VEnv D) : restore A (E ++ A) = A := by
  have hd : (E ++ A).drop E.length = A := by
    induction E with
    | nil => simp
    | cons e rest ih => simpa using ih
  simp only [restore, List.length_append, Nat.add_sub_cancel, hd]

/-! ### The renaming config `RenCfg`

`RenCfg σ inner`: the renaming `σ` is injective on the in-scope (program-declared)
keys, is the identity elsewhere, maps every key to a fresh `dsName`, and every key
is a source (`NotFresh`) name. From it we derive the per-lookup no-merge
hypotheses that the `get`/`set` transports require, for any not-fresh (source)
reference. -/

def RenCfg (σ : Ident → Ident) (inner : VEnv D) (N : Nat) : Prop :=
  (∀ p ∈ inner, ∀ q ∈ inner, σ p.1 = σ q.1 → p.1 = q.1) ∧
  (∀ z, VEnv.get inner z = none → σ z = z) ∧
  (∀ p ∈ inner, ∃ k, k < N ∧ σ p.1 = dsName k) ∧
  (∀ p ∈ inner, NotFresh p.1)

/-- The bound only grows. -/
theorem RenCfg.mono {σ : Ident → Ident} {inner : VEnv D} {N M : Nat}
    (h : RenCfg σ inner N) (hNM : N ≤ M) : RenCfg σ inner M :=
  ⟨h.1, h.2.1,
    fun p hp => (h.2.2.1 p hp).imp (fun k hk => ⟨Nat.lt_of_lt_of_le hk.1 hNM, hk.2⟩),
    h.2.2.2⟩

/-- All keys of a `RenCfg` environment are source names. -/
theorem RenCfg.keys_notFresh {σ : Ident → Ident} {inner : VEnv D} {N : Nat}
    (h : RenCfg σ inner N) :
    ∀ z ∈ inner.map Prod.fst, NotFresh z := by
  intro z hz
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hz
  exact hqe ▸ h.2.2.2 q hq

/-- The `get`/`set` no-merge condition for a not-fresh name `x`: no in-scope key
renames onto `σ x`. -/
theorem RenCfg.no_merge {σ : Ident → Ident} {inner : VEnv D} {N : Nat}
    (h : RenCfg σ inner N)
    {x : Ident} (hx : NotFresh x) : ∀ p ∈ inner, σ p.1 = σ x → p.1 = x := by
  intro p hp hpq
  by_cases hxi : VEnv.get inner x = none
  · obtain ⟨k, _, hk⟩ := h.2.2.1 p hp
    rw [h.2.1 x hxi, hk] at hpq
    exact absurd hpq.symm (hx k)
  · have hne : inner.find? (fun q => q.1 = x) ≠ none :=
      fun hc => hxi ((VEnv.get_eq_none_iff_find _ _).mpr hc)
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hne
    have hqmem : q ∈ inner := List.mem_of_find?_eq_some hq
    have hqx : q.1 = x := by simpa using List.find?_some hq
    rw [← hqx] at hpq ⊢
    exact h.1 p hp q hqmem hpq

/-- `σ x = x` for a not-fresh name absent from the inner prefix. -/
theorem RenCfg.id_at {σ : Ident → Ident} {inner : VEnv D} {N : Nat} (h : RenCfg σ inner N)
    {x : Ident} (hxi : VEnv.get inner x = none) : σ x = x := h.2.1 x hxi

/-- `get` transport at the boundary for a not-fresh name. -/
theorem RenCfg.get {σ : Ident → Ident} {inner : VEnv D} {N : Nat} (h : RenCfg σ inner N)
    (outer : VEnv D) {x : Ident} (hx : NotFresh x) :
    VEnv.get (renVEnv σ inner ++ outer) (σ x) = VEnv.get (inner ++ outer) x :=
  get_boundary σ inner outer x (h.no_merge hx) (fun hn => h.id_at hn)

/-! ### `setMany` transport under injectivity-on-keys (not global) -/

theorem VEnv.set_keys (V : VEnv D) (x : Ident) (v : D.Value) :
    (VEnv.set V x v).map Prod.fst = V.map Prod.fst := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      by_cases hyx : y = x
      · simp [VEnv.set, hyx]
      · simp only [VEnv.set, if_neg hyx, List.map_cons, ih]

theorem renVEnv_setMany_dom (σ : Ident → Ident) :
    ∀ (vars : List Ident) (vals : List D.Value) (V : VEnv D),
      (∀ x ∈ vars, ∀ k ∈ V.map Prod.fst, σ k = σ x → k = x) →
      VEnv.setMany (renVEnv σ V) (vars.map σ) vals = renVEnv σ (VEnv.setMany V vars vals) := by
  intro vars
  induction vars with
  | nil => intro vals V _; simp [VEnv.setMany]
  | cons x xs ih =>
      intro vals V hnm
      cases vals with
      | nil => simp [VEnv.setMany]
      | cons v vs =>
          have hx : ∀ p ∈ V, σ p.1 = σ x → p.1 = x := fun p hp =>
            hnm x (List.mem_cons_self ..) p.1 (List.mem_map_of_mem hp)
          rw [List.map_cons, VEnv.setMany_cons, VEnv.setMany_cons, renVEnv_set σ V x v hx]
          refine ih vs (VEnv.set V x v) (fun y hy k hk => ?_)
          rw [VEnv.set_keys] at hk
          exact hnm y (List.mem_cons_of_mem _ hy) k hk

/-! ### RenCfg preservation (keys-only dependence) -/

theorem VEnv.get_eq_none_iff_not_mem (V : VEnv D) (z : Ident) :
    VEnv.get V z = none ↔ z ∉ V.map Prod.fst := by
  induction V with
  | nil => simp [VEnv.get]
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      by_cases hyz : y = z
      · subst hyz; simp [VEnv.get]
      · have hzy : (z = y) = False := eq_false (fun h => hyz h.symm)
        simp only [VEnv.get, List.find?_cons, hyz, decide_false, cond_false, List.map_cons,
          List.mem_cons, hzy, false_or]
        exact ih

theorem VEnv.setMany_keys (V : VEnv D) (xs : List Ident) (vs : List D.Value) :
    (VEnv.setMany V xs vs).map Prod.fst = V.map Prod.fst := by
  induction xs generalizing V vs with
  | nil => simp [VEnv.setMany]
  | cons x xs ih =>
      cases vs with
      | nil => simp [VEnv.setMany]
      | cons v vs => rw [VEnv.setMany_cons, ih, VEnv.set_keys]

theorem RenCfg.of_keys {σ : Ident → Ident} {V V' : VEnv D} {N : Nat}
    (hk : V'.map Prod.fst = V.map Prod.fst) (h : RenCfg σ V N) : RenCfg σ V' N := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    have hp' : p.1 ∈ V.map Prod.fst := hk ▸ List.mem_map_of_mem hp
    have hq' : q.1 ∈ V.map Prod.fst := hk ▸ List.mem_map_of_mem hq
    obtain ⟨p₀, hp₀, hp₀e⟩ := List.mem_map.mp hp'
    obtain ⟨q₀, hq₀, hq₀e⟩ := List.mem_map.mp hq'
    rw [← hp₀e, ← hq₀e] at hpq ⊢
    exact h1 p₀ hp₀ q₀ hq₀ hpq
  · intro z hz
    exact h2 z ((VEnv.get_eq_none_iff_not_mem V z).mpr
      (fun hc => (VEnv.get_eq_none_iff_not_mem V' z).mp hz (hk ▸ hc)))
  · intro p hp
    obtain ⟨p₀, hp₀, hp₀e⟩ := List.mem_map.mp (hk ▸ List.mem_map_of_mem hp : p.1 ∈ V.map Prod.fst)
    rw [← hp₀e]; exact h3 p₀ hp₀
  · intro p hp
    obtain ⟨p₀, hp₀, hp₀e⟩ := List.mem_map.mp (hk ▸ List.mem_map_of_mem hp : p.1 ∈ V.map Prod.fst)
    rw [← hp₀e]; exact h4 p₀ hp₀

theorem RenCfg.setMany {σ : Ident → Ident} {V : VEnv D} {N : Nat} (h : RenCfg σ V N)
    (xs : List Ident) (vs : List D.Value) : RenCfg σ (VEnv.setMany V xs vs) N :=
  RenCfg.of_keys (VEnv.setMany_keys V xs vs) h

/-- **Extending `RenCfg` for a `let`.** Extending the renaming with fresh names
`vars'` (drawn from the counter range `[lo, hi)` — `RangeNodup`) for a `let`'s
distinct source variables `vars` (disjoint from the current scope) preserves
`RenCfg`, at the advanced bound `hi`. Collision-freedom is arithmetic: images of
old keys lie below `lo`, the new names at or above it. -/
theorem RenCfg.extend {σ : Ident → Ident} {V : VEnv D} {lo : Nat} (h : RenCfg σ V lo)
    {vars vars' : List Ident} {hi : Nat} (hvnd : vars.Nodup)
    (hlen : vars.length = vars'.length)
    (hvNF : ∀ x ∈ vars, NotFresh x)
    (hrn : RangeNodup vars' lo hi)
    (hsh : ∀ x ∈ vars, x ∉ V.map Prod.fst)
    {W : VEnv D} (hW : W.map Prod.fst = vars ++ V.map Prod.fst) :
    RenCfg (updRen σ (vars.zip vars')) W hi := by
  have hNFkey : ∀ z ∈ V.map Prod.fst, NotFresh z := h.keys_notFresh
  have hnd : vars'.Nodup := hrn.2.1
  have hmap : vars.map (updRen σ (vars.zip vars')) = vars' := map_updRen_zip hvnd hlen
  have hmapnd : (vars.map (updRen σ (vars.zip vars'))).Nodup := by rw [hmap]; exact hnd
  have hinj_vars : ∀ a ∈ vars, ∀ b ∈ vars,
      updRen σ (vars.zip vars') a = updRen σ (vars.zip vars') b → a = b :=
    fun a ha b hb => List.inj_on_of_nodup_map hmapnd ha hb
  have hvars_img : ∀ a ∈ vars, updRen σ (vars.zip vars') a ∈ vars' :=
    fun a ha => by have := List.mem_map_of_mem (f := updRen σ (vars.zip vars')) ha
                   rwa [hmap] at this
  have hid_off : ∀ z, z ∉ vars → updRen σ (vars.zip vars') z = σ z := fun z hz =>
    updRen_of_not_mem (fun p hp hpz => hz (hpz ▸ (List.of_mem_zip hp).1))
  -- images of old keys (below lo) never hit new names (at or above lo)
  have hsep : ∀ a ∈ vars, ∀ z ∈ V.map Prod.fst,
      updRen σ (vars.zip vars') a ≠ σ z := by
    intro a ha z hz hc
    obtain ⟨i, hi1, _, hi3⟩ := hrn.1 _ (hvars_img a ha)
    obtain ⟨z₀, hz₀, hz₀e⟩ := List.mem_map.mp hz
    obtain ⟨j, hj, hje⟩ := h.2.2.1 z₀ hz₀
    rw [hi3, ← hz₀e, hje] at hc
    have := dsName_inj hc
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    have hp1 : p.1 ∈ vars ++ V.map Prod.fst := hW ▸ List.mem_map_of_mem hp
    have hq1 : q.1 ∈ vars ++ V.map Prod.fst := hW ▸ List.mem_map_of_mem hq
    rcases List.mem_append.mp hp1 with hpv | hpV <;> rcases List.mem_append.mp hq1 with hqv | hqV
    · exact hinj_vars p.1 hpv q.1 hqv hpq
    · exact absurd (by rw [hid_off q.1 (fun hc => hsh q.1 hc hqV)] at hpq; exact hpq)
        (hsep p.1 hpv q.1 hqV)
    · exact absurd (by rw [hid_off p.1 (fun hc => hsh p.1 hc hpV)] at hpq; exact hpq.symm)
        (hsep q.1 hqv p.1 hpV)
    · rw [hid_off p.1 (fun hc => hsh p.1 hc hpV), hid_off q.1 (fun hc => hsh q.1 hc hqV)] at hpq
      obtain ⟨p₀, hp₀, hp₀e⟩ := List.mem_map.mp hpV
      obtain ⟨q₀, hq₀, hq₀e⟩ := List.mem_map.mp hqV
      rw [← hp₀e, ← hq₀e] at hpq ⊢
      exact h.1 p₀ hp₀ q₀ hq₀ hpq
  · intro z hz
    have hznk : z ∉ W.map Prod.fst := (VEnv.get_eq_none_iff_not_mem W z).mp hz
    rw [hW, List.mem_append] at hznk
    rw [hid_off z (fun hc => hznk (Or.inl hc))]
    exact h.2.1 z ((VEnv.get_eq_none_iff_not_mem V z).mpr (fun hc => hznk (Or.inr hc)))
  · intro p hp
    have hp1 : p.1 ∈ vars ++ V.map Prod.fst := hW ▸ List.mem_map_of_mem hp
    rcases List.mem_append.mp hp1 with hpv | hpV
    · obtain ⟨i, _, hi2, hi3⟩ := hrn.1 _ (hvars_img p.1 hpv)
      exact ⟨i, hi2, hi3⟩
    · rw [hid_off p.1 (fun hc => hsh p.1 hc hpV)]
      obtain ⟨p₀, hp₀, hp₀e⟩ := List.mem_map.mp hpV
      rw [← hp₀e]
      obtain ⟨j, hj, hje⟩ := h.2.2.1 p₀ hp₀
      exact ⟨j, Nat.lt_of_lt_of_le hj hrn.2.2, hje⟩
  · intro p hp
    have hp1 : p.1 ∈ vars ++ V.map Prod.fst := hW ▸ List.mem_map_of_mem hp
    rcases List.mem_append.mp hp1 with hpv | hpV
    · exact hvNF p.1 hpv
    · exact hNFkey p.1 hpV

/-- **Extending `RenFCfg` for a block's function scope.** Prepending a scope `s`
of fresh function names (`new'`, from `[lo, hi)`) for the block's source function
names (`new`), disjoint from the visible functions, preserves `RenFCfg` at the
advanced bound. The φ-analog of `RenCfg.extend`. -/
theorem RenFCfg.extend {φ : Ident → Ident} {funs : FunEnv D} {lo : Nat}
    (h : RenFCfg φ funs lo)
    {new new' : List Ident} {hi : Nat} (hvnd : new.Nodup)
    (hlen : new.length = new'.length)
    (hnewNF : ∀ x ∈ new, NotFresh x)
    (hrn : RangeNodup new' lo hi)
    (hsh : ∀ x ∈ new, x ∉ funNamesOf funs)
    {s : FScope D} (hs : s.map Prod.fst = new) :
    RenFCfg (updRen φ (new.zip new')) (s :: funs) hi := by
  have hkeys : funNamesOf (s :: funs) = new ++ funNamesOf funs := by rw [funNamesOf_cons, hs]
  have hmap : new.map (updRen φ (new.zip new')) = new' := map_updRen_zip hvnd hlen
  have hinj_new : ∀ a ∈ new, ∀ b ∈ new,
      updRen φ (new.zip new') a = updRen φ (new.zip new') b → a = b :=
    fun a ha b hb => List.inj_on_of_nodup_map (by rw [hmap]; exact hrn.2.1) ha hb
  have hnew_img : ∀ a ∈ new, updRen φ (new.zip new') a ∈ new' :=
    fun a ha => by have := List.mem_map_of_mem (f := updRen φ (new.zip new')) ha; rwa [hmap] at this
  have hid_off : ∀ z, z ∉ new → updRen φ (new.zip new') z = φ z := fun z hz =>
    updRen_of_not_mem (fun p hp hpz => hz (hpz ▸ (List.of_mem_zip hp).1))
  have hsep : ∀ a ∈ new, ∀ z ∈ funNamesOf funs, updRen φ (new.zip new') a ≠ φ z := by
    intro a ha z hz hc
    obtain ⟨i, hi1, _, hi3⟩ := hrn.1 _ (hnew_img a ha)
    obtain ⟨j, hj, hje⟩ := h.2.2.1 z hz
    rw [hi3, hje] at hc
    have := dsName_inj hc
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    rw [hkeys, List.mem_append] at ha hb
    rcases ha with hav | haf <;> rcases hb with hbv | hbf
    · exact hinj_new a hav b hbv hab
    · exact absurd (by rw [hid_off b (fun hc => hsh b hc hbf)] at hab; exact hab)
        (hsep a hav b hbf)
    · exact absurd (by rw [hid_off a (fun hc => hsh a hc haf)] at hab; exact hab.symm)
        (hsep b hbv a haf)
    · rw [hid_off a (fun hc => hsh a hc haf), hid_off b (fun hc => hsh b hc hbf)] at hab
      exact h.1 a haf b hbf hab
  · intro z hz
    simp only [hkeys, List.mem_append, not_or] at hz
    rw [hid_off z hz.1]; exact h.2.1 z hz.2
  · intro a ha
    rw [hkeys, List.mem_append] at ha
    rcases ha with hav | haf
    · obtain ⟨i, _, hi2, hi3⟩ := hrn.1 _ (hnew_img a hav)
      exact ⟨i, hi2, hi3⟩
    · rw [hid_off a (fun hc => hsh a hc haf)]
      obtain ⟨j, hj, hje⟩ := h.2.2.1 a haf
      exact ⟨j, Nat.lt_of_lt_of_le hj hrn.2.2, hje⟩
  · intro a ha
    rw [hkeys, List.mem_append] at ha
    rcases ha with hav | haf
    · exact hnewNF a hav
    · exact h.2.2.2 a haf

/-- **`RenCfg` for a fresh scope.** The identity-based renaming that sends distinct
source names `xs` to fresh names from `[lo, hi)` is a valid `RenCfg` on the scope
`xs`, at bound `hi` — used for a function's parameter/return scope (`FDeclRen`). -/
theorem RenCfg.ofFreshScope {xs ys : List Ident} {lo hi : Nat} (hxnd : xs.Nodup)
    (hlen : xs.length = ys.length)
    (hxNF : ∀ x ∈ xs, NotFresh x)
    (hrn : RangeNodup ys lo hi) :
    RenCfg (updRen id (xs.zip ys)) (bindZeros D xs) hi := by
  have hkeys : (bindZeros D xs).map Prod.fst = xs := by
    simp [bindZeros, List.map_map, Function.comp_def]
  have hmap : xs.map (updRen id (xs.zip ys)) = ys := map_updRen_zip hxnd hlen
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    exact List.inj_on_of_nodup_map (by rw [hmap]; exact hrn.2.1)
      (hkeys ▸ List.mem_map_of_mem hp) (hkeys ▸ List.mem_map_of_mem hq) hpq
  · intro z hz
    have hzx : z ∉ xs := by
      have hh := (VEnv.get_eq_none_iff_not_mem _ z).mp hz
      rwa [hkeys] at hh
    exact updRen_of_not_mem (fun p hp hpz => hzx (hpz ▸ (List.of_mem_zip hp).1))
  · intro p hp
    have himg : updRen id (xs.zip ys) p.1 ∈ ys := by
      have := List.mem_map_of_mem (f := updRen id (xs.zip ys)) (hkeys ▸ List.mem_map_of_mem hp)
      rwa [hmap] at this
    obtain ⟨i, _, hi2, hi3⟩ := hrn.1 _ himg
    exact ⟨i, hi2, hi3⟩
  · intro p hp
    exact hxNF p.1 (hkeys ▸ List.mem_map_of_mem hp)

/-! ### Scope predicates lifted to `Code` -/

/-- `FScoped` lifted to the `Code` classes. -/
def FScopedCode (fdom : List Ident) : Code D.Op → Prop
  | .expr _ => True
  | .args _ => True
  | .stmt s => FScopedStmt fdom s
  | .stmts ss => FScopedStmts fdom ss
  | .loop _ post body =>
      ((∀ fn ∈ funNames body, fn ∉ fdom) ∧ FScopedStmts (funNames body ++ fdom) body) ∧
        ((∀ fn ∈ funNames post, fn ∉ fdom) ∧ FScopedStmts (funNames post ++ fdom) post)

/-- `NormalForm` reference-scoping lifted to the `Code` classes. For the `loop`
class the condition/post/body are each checked at the current sets (post/body
extend the function set by their own hoisted names, as `ScopedStmt` does). -/
def NScopedCode (vs fs : List Ident) : Code D.Op → Prop
  | .expr e => NormalForm.ScopedExpr vs fs e
  | .args es => NormalForm.ScopedArgs vs fs es
  | .stmt s => NormalForm.ScopedStmt vs fs s
  | .stmts ss => NormalForm.ScopedStmts vs fs ss
  | .loop c post body =>
      NormalForm.ScopedExpr vs fs c ∧
      NormalForm.ScopedStmts vs (fs ++ NormalForm.funDefNames post) post ∧
      NormalForm.ScopedStmts vs (fs ++ NormalForm.funDefNames body) body

/-- `WScoped` lifted to the `Code` classes (expressions/arguments declare nothing). -/
def WScopedCode (dom : List Ident) : Code D.Op → Prop
  | .expr _ => True
  | .args _ => True
  | .stmt s => WScopedStmt dom s
  | .stmts ss => WScopedStmts dom ss
  | .loop _ post body => WScopedStmts dom body ∧ WScopedStmts dom post

/-! ### Environment-key bookkeeping across `Step` -/

/-- A block/scope statement leaves the current scope's keys unchanged (it restores
its own additions). -/
theorem block_keys {funs : FunEnv D} {V st body V1 st1 o}
    (h : Step D funs V st (.stmt (.block body)) (.sres V1 st1 o)) :
    V1.map Prod.fst = V.map Prod.fst := by
  cases h with
  | block hb => exact restore_keys (venvKeys_suffix hb rfl) (venvLen_mono hb rfl)

/-- Keys grow by exactly the statement's top-level `let`-declared variables (for a
normal outcome). This ties `WScoped`'s domain to the environment's key-set through
the `seqCons` step. -/
theorem venvKeys_stmt {funs : FunEnv D} {V st s V1 st1}
    (h : Step D funs V st (.stmt s) (.sres V1 st1 .normal)) :
    V1.map Prod.fst = declVars s ++ V.map Prod.fst := by
  cases h with
  | funDef => simp [declVars]
  | letZero => simp [declVars, bindZeros, List.map_append, List.map_map, Function.comp_def]
  | letVal hval hlen =>
      simp only [declVars, List.map_append]
      rw [List.map_fst_zip (Nat.le_of_eq hlen.symm)]
  | assignVal hval hlen => simp only [declVars, List.nil_append, VEnv.setMany_keys]
  | exprStmt => simp [declVars]
  | block hb =>
      simp only [declVars, List.nil_append]
      exact restore_keys (venvKeys_suffix hb rfl) (venvLen_mono hb rfl)
  | ifTrue hc hnz hb => simp only [declVars, List.nil_append]; exact block_keys hb
  | ifFalse hc hz => simp [declVars]
  | switchExec hc hb => simp only [declVars, List.nil_append]; exact block_keys hb
  | @forLoop funs V st init c post body Vinit stinit Vend stend o hinit hloop =>
      simp only [declVars, List.nil_append]
      exact restore_keys ((venvKeys_suffix hinit rfl).trans (venvKeys_suffix hloop rfl))
        (Nat.le_trans (venvLen_mono hinit rfl) (venvLen_mono hloop rfl))

/-! ### The function-declaration body relation -/

/-- Function-declaration renaming, at visible function set `F` (the names in
scope at the declaration's position — for a stored declaration, exactly
`funNamesOf` of the closure environment `lookupFun` returns). Params/rets are
renamed by `σc`, a valid renaming (`RenCfg`) on the fresh parameter/return
scope, bounded by the body's range start; the body is α-equivalent under `σc`
(variables) and the ambient `φ` (functions); and the source body is
reference-scoped (for the `φ`-congruence transport), variable-scope-safe and
function-scope-safe (for re-entering the simulation at a call). -/
def FDeclRen (F : List Ident) (φ : Ident → Ident) (d₁ d₂ : FDecl D) : Prop :=
  ∃ lo hi σc σc' φc',
    d₂.params = d₁.params.map σc ∧ d₂.rets = d₁.rets.map σc ∧
    RenCfg σc (bindZeros D (d₁.params ++ d₁.rets)) lo ∧
    NormalForm.ScopedStmts (d₁.params ++ d₁.rets)
      (F ++ NormalForm.funDefNames d₁.body) d₁.body ∧
    WScopedStmts (d₁.params ++ d₁.rets) d₁.body ∧
    ((∀ fn ∈ funNames d₁.body, fn ∉ F) ∧
      FScopedStmts (funNames d₁.body ++ F) d₁.body) ∧
    AlphaBlockExt lo hi σc φ d₁.body d₂.body σc' φc'

/-- Function environments related scope-by-scope, each scope's declarations at
its own visible set (its scope and everything below — exactly what `lookupFun`
returns as the closure environment). -/
def RenFunsRelF (φ : Ident → Ident) : FunEnv D → FunEnv D → Prop
  | s₁ :: r₁, s₂ :: r₂ =>
      RenScopeRel φ (FDeclRen (funNamesOf (s₁ :: r₁)) φ) s₁ s₂ ∧ RenFunsRelF φ r₁ r₂
  | [], [] => True
  | _, _ => False

theorem RenFunsRelF.cons {φ : Ident → Ident} {s₁ s₂ : FScope D} {r₁ r₂ : FunEnv D}
    (hs : RenScopeRel φ (FDeclRen (funNamesOf (s₁ :: r₁)) φ) s₁ s₂)
    (hr : RenFunsRelF φ r₁ r₂) : RenFunsRelF φ (s₁ :: r₁) (s₂ :: r₂) :=
  ⟨hs, hr⟩

/-- `lookupFun` transports across `RenFunsRelF`: the resolved declaration is
related at exactly the visible set of the returned closure environment. -/
theorem lookupFun_renFunsRelF {φ : Ident → Ident} :
    ∀ {f₁ f₂ : FunEnv D}, RenFunsRelF φ f₁ f₂ →
      ∀ {fn : Ident}, (∀ s ∈ f₁, ∀ p ∈ s, φ p.1 = φ fn → p.1 = fn) →
      ∀ {decl : FDecl D} {cenv : FunEnv D}, lookupFun f₁ fn = some (decl, cenv) →
      ∃ decl' cenv', lookupFun f₂ (φ fn) = some (decl', cenv') ∧
        FDeclRen (funNamesOf cenv) φ decl decl' ∧ RenFunsRelF φ cenv cenv'
  | [], [], _, fn, _, decl, cenv, h => by simp [lookupFun] at h
  | [], _ :: _, hR, fn, _, decl, cenv, h => hR.elim
  | _ :: _, [], hR, fn, _, decl, cenv, h => hR.elim
  | s₁ :: r₁, s₂ :: r₂, hR, fn, hnm, decl, cenv, h => by
      obtain ⟨hs, hr⟩ := hR
      rcases renScopeRel_find hs fn (hnm s₁ (List.mem_cons_self ..)) with
        ⟨hn₁, hn₂⟩ | ⟨p, q, hp₁, hp₂, hkey, hd⟩
      · rw [lookupFun, hn₁] at h
        obtain ⟨decl', cenv', hl', hbody, hRc⟩ :=
          lookupFun_renFunsRelF hr (fun s hs' => hnm s (List.mem_cons_of_mem _ hs')) h
        exact ⟨decl', cenv', by rw [lookupFun, hn₂]; exact hl', hbody, hRc⟩
      · rw [lookupFun, hp₁] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hd_eq, hcenv_eq⟩ := h
        subst hd_eq; subst hcenv_eq
        exact ⟨q.2, s₂ :: r₂, by rw [lookupFun, hp₂], hd, hs, hr⟩

/-- `FDeclRen` transports along a `φ` agreeing on the visible functions: the
stored body references only visible names (its `Scoped` field), so its
α-relation transports by congruence; nothing else mentions `φ`. -/
theorem FDeclRen.congr_phi {F : List Ident} {φ φ' : Ident → Ident} {d₁ d₂ : FDecl D}
    (h : FDeclRen F φ d₁ d₂) (hag : ∀ fn ∈ F, φ' fn = φ fn) :
    FDeclRen F φ' d₁ d₂ := by
  obtain ⟨lo, hi, σc, σc', φc', hps, hrs, hcfg, hns, hws, hfs, hbe⟩ := h
  exact ⟨lo, hi, σc, _, _, hps, hrs, hcfg, hns, hws, hfs,
    alphaBlockExt_congr_phi hbe hns hag⟩

/-- Scope-level transport at a fixed visible set: keys by agreement on the
scope's names, declarations by `FDeclRen.congr_phi`. -/
theorem RenScopeRel.congr_phi_fdecl {F : List Ident} {φ φ' : Ident → Ident}
    {s₁ s₂ : FScope D}
    (h : RenScopeRel φ (FDeclRen F φ) s₁ s₂)
    (hag : ∀ fn ∈ F, φ' fn = φ fn)
    (hkeys : ∀ p ∈ s₁, φ' p.1 = φ p.1) :
    RenScopeRel φ' (FDeclRen F φ') s₁ s₂ := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons p q u₁ u₂ hpq hrest ih =>
      exact List.Forall₂.cons
        ⟨hpq.1.trans (hkeys p (List.mem_cons_self ..)).symm, hpq.2.congr_phi hag⟩
        (ih (fun p hp => hkeys p (List.mem_cons_of_mem _ hp)))

/-- `RenFunsRelF` transports along a `φ` agreeing on all in-scope names. -/
theorem RenFunsRelF.congr_phi {φ φ' : Ident → Ident} :
    ∀ {f₁ f₂ : FunEnv D}, RenFunsRelF φ f₁ f₂ →
      (∀ fn ∈ funNamesOf f₁, φ' fn = φ fn) → RenFunsRelF φ' f₁ f₂
  | [], [], _, _ => trivial
  | [], _ :: _, hR, _ => hR.elim
  | _ :: _, [], hR, _ => hR.elim
  | s₁ :: r₁, s₂ :: r₂, hR, hag => by
      obtain ⟨hs, hr⟩ := hR
      have hsub : ∀ fn ∈ funNamesOf r₁, fn ∈ funNamesOf (s₁ :: r₁) := by
        intro fn hfn
        rw [funNamesOf_cons]
        exact List.mem_append.mpr (Or.inr hfn)
      have hkeys : ∀ p ∈ s₁, φ' p.1 = φ p.1 := fun p hp => hag p.1 (by
        rw [funNamesOf_cons]
        exact List.mem_append.mpr (Or.inl (List.mem_map_of_mem hp)))
      exact ⟨hs.congr_phi_fdecl hag hkeys,
        RenFunsRelF.congr_phi hr (fun fn hfn => hag fn (hsub fn hfn))⟩

/-- The hoisted scope's keys are the block's top-level function names. -/
theorem hoist_keys (body : List (Stmt D.Op)) : (hoist D body).map Prod.fst = funNames body := by
  induction body with
  | nil => rfl
  | cons s rest ih =>
      simp only [hoist] at ih ⊢
      cases s <;> simp only [List.filterMap_cons, List.map_cons, funNames, ih]

/-- **Hoist transport.** α-equivalent statement sequences with scope-safe,
reference-scoped source have `RenScopeRel`-related hoisted function scopes at
the block's visible set `F`: each source `funDef` is matched by a target
`funDef` with `φ`-renamed name and an `FDeclRen F φ`-related declaration. -/
theorem hoist_renScopeRel {F : List Ident} :
    ∀ {ss ss' : List (Stmt D.Op)} {lo hi} {σ φ σ' φ' : Ident → Ident}
      {dom vs : List Ident},
    AlphaSeqExt lo hi σ φ ss ss' σ' φ' →
    WScopedStmts dom ss →
    FScopedStmts F ss →
    NormalForm.ScopedStmts vs F ss →
    RenScopeRel φ (FDeclRen F φ) (hoist D ss) (hoist D ss')
  | [], _, _, _, _, _, _, _, _, _, h, _, _, _ => by cases h; exact List.Forall₂.nil
  | s :: rest, _, _, _, σ0, φ0, _, _, dom, vs, h, hws, hfs, hns => by
      obtain ⟨hws_s, hws_r⟩ := (hws : WScopedStmt dom s ∧
        WScopedStmts (declVars s ++ dom) rest)
      obtain ⟨hfs_s, hfs_r⟩ := (hfs : FScopedStmt F s ∧ FScopedStmts F rest)
      obtain ⟨hns_s, hns_r⟩ := (hns : NormalForm.ScopedStmt vs F s ∧
        NormalForm.ScopedStmts (vs ++ NormalForm.declTopVars s) F rest)
      cases h with
      | @cons _ _ _ _ _ _ s' _ rest' σm φm _ _ hs1 hrest =>
      have ih := hoist_renScopeRel hrest hws_r hfs_r hns_r
      have hpe := hs1.phi_eq; subst hpe
      cases hs1 with
      | @funD _ m _ _ _ fn ps ps' rs rs' body body' σb φb hnd hlp hlr hNF hrn hbe =>
          simp only [hoist, List.filterMap_cons]
          refine List.Forall₂.cons ⟨rfl, ?_⟩ ih
          have hpsnd : ps.Nodup := (List.nodup_append.mp hnd).1
          have hrsnd : rs.Nodup := (List.nodup_append.mp hnd).2.1
          have hdisj : ∀ x ∈ ps, x ∉ rs :=
            fun x hx hxr => (List.nodup_append.mp hnd).2.2 x hx x hxr rfl
          refine ⟨m, _, updRen id (ps.zip ps' ++ rs.zip rs'), σb, φb, ?_, ?_, ?_, ?_, ?_, ?_, hbe⟩
          · exact (map_updRen_zip_pre (rs.zip rs') hpsnd hlp).symm
          · have hc : rs.map (updRen id (ps.zip ps' ++ rs.zip rs'))
                = rs.map (updRen id (rs.zip rs')) :=
              List.map_congr_left (fun y hy => updRen_append_skip
                (fun p hp hpy => hdisj y (hpy ▸ (List.of_mem_zip hp).1) hy))
            exact (hc.trans (map_updRen_zip hrsnd hlr)).symm
          · rw [show ps.zip ps' ++ rs.zip rs' = (ps ++ rs).zip (ps' ++ rs') from
              (List.zip_append hlp).symm]
            exact RenCfg.ofFreshScope hnd (by simp only [List.length_append, hlp, hlr]) hNF hrn
          · exact hns_s
          · exact (hws_s : (ps ++ rs).Nodup ∧ WScopedStmts (ps ++ rs) body).2
          · exact hfs_s
      | _ => simp only [hoist, List.filterMap_cons]; exact ih

/-! ### Result renaming and the code-level α-relation -/

/-- Rename a result's environment by `σ'` (expression results are unchanged). -/
def renRes (σ' : Ident → Ident) : Res D → Res D
  | .eres r => .eres r
  | .sres V st o => .sres (renVEnv σ' V) st o

/-- α-relation on `Code`, carrying counter range, input and post renamings. -/
inductive AlphaCode :
    Nat → Nat → (Ident → Ident) → (Ident → Ident) → (Ident → Ident) → (Ident → Ident) →
    Code D.Op → Code D.Op → Prop
  | expr {lo hi σ φ e₁ e₂} : AlphaExpr σ φ e₁ e₂ → AlphaCode lo hi σ φ σ φ (.expr e₁) (.expr e₂)
  | args {lo hi σ φ a₁ a₂} : AlphaArgs σ φ a₁ a₂ → AlphaCode lo hi σ φ σ φ (.args a₁) (.args a₂)
  | stmt {lo hi σ φ s₁ s₂ σ' φ'} :
      AlphaStmt1 lo hi σ φ s₁ s₂ σ' φ' → AlphaCode lo hi σ φ σ' φ' (.stmt s₁) (.stmt s₂)
  | stmts {lo hi σ φ ss₁ ss₂ σ' φ'} :
      AlphaSeqExt lo hi σ φ ss₁ ss₂ σ' φ' → AlphaCode lo hi σ φ σ' φ' (.stmts ss₁) (.stmts ss₂)
  | loop {lo m hi σ φ c₁ c₂ p₁ p₂ b₁ b₂ σb φb σp φp} :
      AlphaExpr σ φ c₁ c₂ → AlphaBlockExt lo m σ φ b₁ b₂ σb φb →
      AlphaBlockExt m hi σ φ p₁ p₂ σp φp →
      AlphaCode lo hi σ φ σ φ (.loop c₁ p₁ b₁) (.loop c₂ p₂ b₂)

/-- Post-condition carried on a statement result so it threads to the
continuation: for a `normal` outcome, the reported post-renaming is a valid
`RenCfg` on the result environment, at the post-range bound. -/
def ResOK (σ' : Ident → Ident) (N : Nat) : Res D → Prop
  | .eres _ => True
  | .sres V _ .normal => RenCfg σ' V N
  | .sres _ _ _ => True

/-! ### `selectSwitch` transport

A `switch` executes the first case whose label matches, else the default, else
the empty block. Labels are preserved verbatim by the α-relation, so source and
target select *corresponding* blocks; the scope-safety and reference-scoping
predicates select through as well. -/

theorem selectSwitch_alpha {σ φ : Ident → Ident} {cv : D.Value} :
    ∀ {cs cs' : List (Literal × Block D.Op)} {lo m : Nat},
      AlphaCases lo m σ φ cs cs' →
      ∀ {dflt dflt' : Option (Block D.Op)} {hi : Nat}, AlphaDflt m hi σ φ dflt dflt' →
      ∃ lo' hi' σb φb, lo ≤ lo' ∧ hi' ≤ hi ∧
        AlphaBlockExt lo' hi' σ φ (selectSwitch D cv cs dflt)
          (selectSwitch D cv cs' dflt') σb φb
  | [], _, lo, m, hcs, dflt, dflt', hi, hd => by
      cases hcs with | nil hle =>
      cases hd with
      | none hled =>
          refine ⟨m, m, σ,
            updRen φ ((funNames ([] : Block D.Op)).zip (funNames ([] : Block D.Op))),
            hle, hled, ?_⟩
          show AlphaBlockExt m m σ φ (selectSwitch D cv [] none) (selectSwitch D cv [] none) _ _
          simp only [selectSwitch, List.find?_nil, Option.getD_none]
          exact AlphaBlockExt.mk List.nodup_nil rfl (fun x hx => absurd hx (by simp [funNames]))
            (RangeNodup.nil m) (AlphaSeqExt.nil (Nat.le_refl m))
      | some hb =>
          exact ⟨m, hi, _, _, hle, Nat.le_refl hi, hb⟩
  | (l, body) :: rest, _, lo, m, hcs, dflt, dflt', hi, hd => by
      cases hcs with | @cons _ m₀ _ _ _ _ _ body' _ rest' σb0 φb0 hb hrest =>
      by_cases hcv : cv = D.litValue l
      · refine ⟨lo, m₀, σb0, φb0, Nat.le_refl lo,
          Nat.le_trans (alphaCases_le hrest) (alphaDflt_le hd), ?_⟩
        show AlphaBlockExt lo m₀ σ φ (selectSwitch D cv ((l, body) :: rest) dflt)
          (selectSwitch D cv ((l, body') :: rest') dflt') _ _
        simp only [selectSwitch, List.find?_cons, hcv, decide_true]
        exact hb
      · obtain ⟨lo', hi', σb, φb, hlo, hhi, hsel⟩ := selectSwitch_alpha hrest hd
        refine ⟨lo', hi', σb, φb, Nat.le_trans (alphaBlockExt_le hb) hlo, hhi, ?_⟩
        show AlphaBlockExt lo' hi' σ φ (selectSwitch D cv ((l, body) :: rest) dflt)
          (selectSwitch D cv ((l, body') :: rest') dflt') σb φb
        simp only [selectSwitch, List.find?_cons, hcv, decide_false] at hsel ⊢
        exact hsel

theorem selectSwitch_wscoped {dom : List Ident} {cv : D.Value} :
    ∀ {cs : List (Literal × Block D.Op)}, WScopedCases dom cs →
      ∀ {dflt : Option (Block D.Op)}, WScopedDflt dom dflt →
      WScopedStmts dom (selectSwitch D cv cs dflt)
  | [], _, none, _ => by simp only [selectSwitch, List.find?_nil, Option.getD_none]; trivial
  | [], _, some body, hd => by
      simp only [selectSwitch, List.find?_nil, Option.getD_some]
      exact hd
  | (l, body) :: rest, hcs, dflt, hd => by
      obtain ⟨hb, hrest⟩ := (hcs : WScopedStmts dom body ∧ WScopedCases dom rest)
      by_cases hcv : cv = D.litValue l
      · simp only [selectSwitch, List.find?_cons, hcv, decide_true]
        exact hb
      · have := selectSwitch_wscoped hrest (dflt := dflt) hd (cv := cv)
        simp only [selectSwitch, List.find?_cons, hcv, decide_false] at this ⊢
        exact this

theorem selectSwitch_fscoped {F : List Ident} {cv : D.Value} :
    ∀ {cs : List (Literal × Block D.Op)}, FScopedCases F cs →
      ∀ {dflt : Option (Block D.Op)}, FScopedDflt F dflt →
      (∀ fn ∈ funNames (selectSwitch D cv cs dflt), fn ∉ F) ∧
        FScopedStmts (funNames (selectSwitch D cv cs dflt) ++ F) (selectSwitch D cv cs dflt)
  | [], _, none, _ => by
      simp only [selectSwitch, List.find?_nil, Option.getD_none]
      exact ⟨fun fn hfn => absurd hfn (by simp [funNames]), trivial⟩
  | [], _, some body, hd => by
      simp only [selectSwitch, List.find?_nil, Option.getD_some]
      exact hd
  | (l, body) :: rest, hcs, dflt, hd => by
      obtain ⟨hb, hrest⟩ := (hcs :
        ((∀ fn ∈ funNames body, fn ∉ F) ∧ FScopedStmts (funNames body ++ F) body) ∧
          FScopedCases F rest)
      by_cases hcv : cv = D.litValue l
      · simp only [selectSwitch, List.find?_cons, hcv, decide_true]
        exact hb
      · have := selectSwitch_fscoped hrest (dflt := dflt) hd (cv := cv)
        simp only [selectSwitch, List.find?_cons, hcv, decide_false] at this ⊢
        exact this

theorem selectSwitch_nscoped {vs fs : List Ident} {cv : D.Value} :
    ∀ {cs : List (Literal × Block D.Op)}, NormalForm.ScopedCases vs fs cs →
      ∀ {dflt : Option (Block D.Op)}, NormalForm.ScopedDflt vs fs dflt →
      NormalForm.ScopedStmts vs (fs ++ NormalForm.funDefNames (selectSwitch D cv cs dflt))
        (selectSwitch D cv cs dflt)
  | [], _, none, _ => by simp only [selectSwitch, List.find?_nil, Option.getD_none]; trivial
  | [], _, some body, hd => by
      simp only [selectSwitch, List.find?_nil, Option.getD_some]
      exact hd
  | (l, body) :: rest, hcs, dflt, hd => by
      obtain ⟨hb, hrest⟩ := (hcs :
        NormalForm.ScopedStmts vs (fs ++ NormalForm.funDefNames body) body ∧
          NormalForm.ScopedCases vs fs rest)
      by_cases hcv : cv = D.litValue l
      · simp only [selectSwitch, List.find?_cons, hcv, decide_true]
        exact hb
      · have := selectSwitch_nscoped hrest (dflt := dflt) hd (cv := cv)
        simp only [selectSwitch, List.find?_cons, hcv, decide_false] at this ⊢
        exact this

/-- For an abnormal outcome, a statement leaves the environment's key-set
unchanged (halts return the current environment; `break`/`continue`/`leave`
escape from inside restoring scopes). -/
theorem venvKeys_stmt_abnormal {funs : FunEnv D} {V st s V1 st1 o}
    (h : Step D funs V st (.stmt s) (.sres V1 st1 o)) (hne : o ≠ .normal) :
    V1.map Prod.fst = V.map Prod.fst := by
  cases h with
  | funDef => exact absurd rfl hne
  | letZero => exact absurd rfl hne
  | letVal _ _ => exact absurd rfl hne
  | assignVal _ _ => exact absurd rfl hne
  | exprStmt _ => exact absurd rfl hne
  | ifFalse _ _ => exact absurd rfl hne
  | letHalt _ => rfl
  | assignHalt _ => rfl
  | exprStmtHalt _ => rfl
  | ifHalt _ => rfl
  | switchHalt _ => rfl
  | «break» => rfl
  | «continue» => rfl
  | leave => rfl
  | ifTrue _ _ hb => exact block_keys hb
  | switchExec _ hb => exact block_keys hb
  | block hb => exact restore_keys (venvKeys_suffix hb rfl) (venvLen_mono hb rfl)
  | forLoop hinit hloop =>
      exact restore_keys ((venvKeys_suffix hinit rfl).trans (venvKeys_suffix hloop rfl))
        (Nat.le_trans (venvLen_mono hinit rfl) (venvLen_mono hloop rfl))
  | forInitHalt hinit =>
      exact restore_keys (venvKeys_suffix hinit rfl) (venvLen_mono hinit rfl)

/-- Key-set membership after a normally-completed statement sequence: the
sequence's declared variables plus the initial keys (as a set — sequences
prepend each `let`'s bindings, so the list order differs from `declVarsSeq`). -/
theorem venvKeys_stmts {funs : FunEnv D} :
    ∀ {ss : List (Stmt D.Op)} {V st V1 st1},
      Step D funs V st (.stmts ss) (.sres V1 st1 .normal) →
      ∀ x, x ∈ V1.map Prod.fst ↔ (x ∈ declVarsSeq ss ∨ x ∈ V.map Prod.fst)
  | [], V, st, V1, st1, h => by
      cases h with
      | seqNil => intro x; simp [declVarsSeq]
  | s :: rest, V, st, V1, st1, h => by
      cases h with
      | @seqCons _ _ _ _ _ Vm stm _ _ _ hs hrest =>
          intro x
          have h1 : Vm.map Prod.fst = declVars s ++ V.map Prod.fst := venvKeys_stmt hs
          have h2 := venvKeys_stmts hrest x
          rw [h2, h1]
          simp only [declVarsSeq, List.mem_append]
          tauto
      | seqStop hs hne => exact absurd rfl hne

end YulEvmCompiler.Optimizer.Normalize
