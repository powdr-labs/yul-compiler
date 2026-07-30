import YulEvmCompiler.Optimizer.Implementation.Frame
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.DeadStoresSound

The **value-change frame lemma**, the piece of `VEnv` meta-theory dead-store
elimination needs and `Frame.lean` does not have.

`Frame.InsAt` relates two environments differing by an *inserted* binding.
Dead-store elimination instead produces environments of the same shape whose
*values* differ, at bindings nobody reads. `VChg dead k seen V₁ V₂` says:

* `V₁` and `V₂` share a tail of length `k` (literally the same list), so a
  `restore` down to that tail equalizes them;
* above the tail they carry the same names in the same order; and
* every position whose values differ holds a name that is `dead` and is the
  **innermost** binding of that name — `seen` accumulates the names already
  passed (bound further in), and the `diff` rule forbids them.

Innermost-ness is what makes the relation survive a *write*: after both sides
store to `z`, no difference at `z` can be left, so `z` may leave the dead set
(`VChg.set_kill`). `vchgStep` is the frame lemma proper: code that mentions no
dead name runs in lock-step from `VChg`-related environments, with the relation
(and its tail index) preserved. It is symmetric in the two environments
(`VChg.symm`), so one direction suffices.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics

variable {D : Dialect}

/-! ### Environment representation facts -/

/-- Lookup on a cons cell (dialect-generic form). -/
theorem venvGet_cons (p : Ident × D.Value) (V : VEnv D) (y : Ident) :
    VEnv.get (p :: V) y = if p.1 = y then some p.2 else VEnv.get V y := by
  unfold VEnv.get
  rw [List.find?_cons]
  by_cases h : p.1 = y <;> simp [h]

/-- `set` on a cons cell. -/
theorem venvSet_cons (p : Ident × D.Value) (V : VEnv D) (z : Ident) (v : D.Value) :
    VEnv.set (p :: V) z v = if p.1 = z then (z, v) :: V else p :: VEnv.set V z v := by
  obtain ⟨y, w⟩ := p
  simp only [VEnv.set]

/-- `set` updates a value, never a key, so it preserves the length. -/
theorem venvSet_length (V : VEnv D) (z : Ident) (w : D.Value) :
    (VEnv.set V z w).length = V.length := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      rw [venvSet_cons]
      by_cases hp : p.1 = z
      · rw [if_pos hp]; simp
      · rw [if_neg hp]; simp [ih]

/-- The names bound by a zero-initialising `let`. -/
theorem bindZeros_fst (xs : List Ident) : (bindZeros D xs).map Prod.fst = xs := by
  simp [bindZeros, Function.comp_def]

/-! ### The value-change relation -/

/-- `VChg dead k seen V₁ V₂`: the two environments share a tail of length `k`,
carry the same names in the same order above it, and every position whose values
differ holds a `dead` name that no inner binding shadows (`seen` accumulates the
names already passed, i.e. bound *further in*). -/
inductive VChg (dead : Ident → Prop) (k : Nat) : (Ident → Prop) → VEnv D → VEnv D → Prop
  /-- Stop: the remaining environments are identical, of exactly the tail length. -/
  | tail {seen : Ident → Prop} {V : VEnv D} : V.length = k → VChg dead k seen V V
  /-- A position whose value agrees. -/
  | same {seen : Ident → Prop} {x : Ident} {v : D.Value} {V₁ V₂ : VEnv D} :
      VChg dead k (fun y => seen y ∨ y = x) V₁ V₂ →
      VChg dead k seen ((x, v) :: V₁) ((x, v) :: V₂)
  /-- A position whose value differs: its name is dead and unshadowed. -/
  | diff {seen : Ident → Prop} {x : Ident} {v w : D.Value} {V₁ V₂ : VEnv D} :
      dead x → ¬ seen x →
      VChg dead k (fun y => seen y ∨ y = x) V₁ V₂ →
      VChg dead k seen ((x, v) :: V₁) ((x, w) :: V₂)

namespace VChg

variable {dead dead' : Ident → Prop} {k : Nat} {seen seen' : Ident → Prop}

/-- The identity pair, with the whole environment as the shared tail. -/
theorem rfl_len (dead : Ident → Prop) (seen : Ident → Prop) (V : VEnv D) :
    VChg dead V.length seen V V := .tail rfl

/-- The relation is symmetric in its two environments. -/
theorem symm : ∀ {seen : Ident → Prop} {V₁ V₂ : VEnv D},
    VChg (D := D) dead k seen V₁ V₂ → VChg dead k seen V₂ V₁ := by
  intro seen V₁ V₂ h
  induction h with
  | tail hlen => exact .tail hlen
  | same _ ih => exact .same ih
  | diff hd hs _ ih => exact .diff hd hs ih

/-- Both sides have the same length. -/
theorem length : ∀ {seen : Ident → Prop} {V₁ V₂ : VEnv D},
    VChg (D := D) dead k seen V₁ V₂ → V₁.length = V₂.length := by
  intro seen V₁ V₂ h
  induction h with
  | tail => rfl
  | same _ ih => simp [ih]
  | diff _ _ _ ih => simp [ih]

/-- The shared tail is no longer than either side. -/
theorem tail_le : ∀ {seen : Ident → Prop} {V₁ V₂ : VEnv D},
    VChg (D := D) dead k seen V₁ V₂ → k ≤ V₁.length := by
  intro seen V₁ V₂ h
  induction h with
  | tail hlen => exact Nat.le_of_eq hlen.symm
  | same _ ih => simp only [List.length_cons]; omega
  | diff _ _ _ ih => simp only [List.length_cons]; omega

/-- Both sides carry the same names in the same order. -/
theorem keys : ∀ {seen : Ident → Prop} {V₁ V₂ : VEnv D},
    VChg (D := D) dead k seen V₁ V₂ → V₁.map Prod.fst = V₂.map Prod.fst := by
  intro seen V₁ V₂ h
  induction h with
  | tail => rfl
  | same _ ih => simp [ih]
  | diff _ _ _ ih => simp [ih]

/-- Shrinking the shadowing set weakens the `diff` side condition. -/
theorem shrink_seen : ∀ {seen : Ident → Prop} {V₁ V₂ : VEnv D},
    VChg (D := D) dead k seen V₁ V₂ → ∀ {seen' : Ident → Prop},
      (∀ x, seen' x → seen x) → VChg dead k seen' V₁ V₂ := by
  intro seen V₁ V₂ h
  induction h with
  | tail hlen => intro seen' _; exact .tail hlen
  | same _ ih =>
      intro seen' hsub
      exact .same (ih (fun z hz => hz.elim (fun hh => Or.inl (hsub z hh)) Or.inr))
  | diff hd hs _ ih =>
      intro seen' hsub
      exact .diff hd (fun hc => hs (hsub _ hc))
        (ih (fun z hz => hz.elim (fun hh => Or.inl (hsub z hh)) Or.inr))

/-- Growing the shadowing set is fine as long as no `dead` name is added. -/
theorem grow_seen : ∀ {seen : Ident → Prop} {V₁ V₂ : VEnv D},
    VChg (D := D) dead k seen V₁ V₂ → ∀ {extra : Ident → Prop},
      (∀ x, dead x → ¬ extra x) → VChg dead k (fun y => seen y ∨ extra y) V₁ V₂ := by
  intro seen V₁ V₂ h
  induction h with
  | tail hlen => intro extra _; exact .tail hlen
  | same _ ih =>
      intro extra hex
      exact .same ((ih hex).shrink_seen (fun z hz => by tauto))
  | diff hd hs _ ih =>
      intro extra hex
      exact .diff hd (fun hc => hc.elim hs (fun hc' => hex _ hd hc'))
        ((ih hex).shrink_seen (fun z hz => by tauto))

/-- Weakening the dead set: only names not shadowed by an inner binding matter. -/
theorem mono_seen : ∀ {seen : Ident → Prop} {V₁ V₂ : VEnv D},
    VChg (D := D) dead k seen V₁ V₂ → ∀ {dead' : Ident → Prop},
      (∀ x, ¬ seen x → dead x → dead' x) → VChg dead' k seen V₁ V₂ := by
  intro seen V₁ V₂ h
  induction h with
  | tail hlen => intro dead' _; exact .tail hlen
  | same _ ih =>
      intro dead' hd
      exact .same (ih (fun z hz hdz => hd z (fun hs => hz (Or.inl hs)) hdz))
  | diff hdx hs _ ih =>
      intro dead' hd
      exact .diff (hd _ hs hdx) hs (ih (fun z hz hdz => hd z (fun hs' => hz (Or.inl hs')) hdz))

/-- Weakening the dead set (unconditional form). -/
theorem mono {V₁ V₂ : VEnv D} (h : VChg (D := D) dead k seen V₁ V₂)
    (hd : ∀ x, dead x → dead' x) : VChg dead' k seen V₁ V₂ :=
  h.mono_seen (fun x _ hx => hd x hx)

/-! ### Reading and writing -/

/-- Reading a name that is not dead gives the same answer on both sides. -/
theorem get : ∀ {seen : Ident → Prop} {V₁ V₂ : VEnv D},
    VChg (D := D) dead k seen V₁ V₂ → ∀ {z : Ident}, ¬ dead z →
      VEnv.get V₁ z = VEnv.get V₂ z := by
  intro seen V₁ V₂ h
  induction h with
  | tail => intro z _; rfl
  | @same seen x v V₁ V₂ _ ih =>
      intro z hz
      rw [venvGet_cons, venvGet_cons]
      by_cases hx : x = z
      · rw [if_pos hx, if_pos hx]
      · rw [if_neg hx, if_neg hx]
        exact ih hz
  | @diff seen x v w V₁ V₂ hdx hs _ ih =>
      intro z hz
      have hx : x ≠ z := fun hc => hz (hc ▸ hdx)
      rw [venvGet_cons, venvGet_cons, if_neg hx, if_neg hx]
      exact ih hz

/-- Writing the same value on both sides preserves the relation — whatever the
target, dead or not: a dead position written on both sides simply stops
differing. -/
theorem set : ∀ {seen : Ident → Prop} {V₁ V₂ : VEnv D},
    VChg (D := D) dead k seen V₁ V₂ → ∀ (z : Ident) (v : D.Value),
      VChg dead k seen (VEnv.set V₁ z v) (VEnv.set V₂ z v) := by
  intro seen V₁ V₂ h
  induction h with
  | tail hlen => intro z v; exact .tail (by rw [venvSet_length]; exact hlen)
  | @same seen x v0 V₁ V₂ hrest ih =>
      intro z v
      rw [venvSet_cons, venvSet_cons]
      by_cases hx : x = z
      · subst hx
        rw [if_pos rfl, if_pos rfl]
        exact .same hrest
      · rw [if_neg hx, if_neg hx]
        exact .same (ih z v)
  | @diff seen x v0 w0 V₁ V₂ hdx hs hrest ih =>
      intro z v
      rw [venvSet_cons, venvSet_cons]
      by_cases hx : x = z
      · subst hx
        rw [if_pos rfl, if_pos rfl]
        exact .same hrest
      · rw [if_neg hx, if_neg hx]
        exact .diff hdx hs (ih z v)

/-- Writing to `z` on both sides removes any difference at `z`, so `z` may be
dropped from the dead set afterwards. This is where innermost-ness pays: a
`diff` at `z` deeper in the environment is impossible, because `z` is `seen`
there. -/
theorem set_kill : ∀ {seen : Ident → Prop} {V₁ V₂ : VEnv D},
    VChg (D := D) dead k seen V₁ V₂ →
    ∀ {dead' : Ident → Prop} (z : Ident) (v : D.Value),
      (∀ x, dead x → x ≠ z → dead' x) →
      VChg dead' k seen (VEnv.set V₁ z v) (VEnv.set V₂ z v) := by
  intro seen V₁ V₂ h
  induction h with
  | tail hlen => intro dead' z v _; exact .tail (by rw [venvSet_length]; exact hlen)
  | @same seen x v0 V₁ V₂ hrest ih =>
      intro dead' z v hd
      rw [venvSet_cons, venvSet_cons]
      by_cases hx : x = z
      · subst hx
        rw [if_pos rfl, if_pos rfl]
        refine .same (hrest.mono_seen ?_)
        intro y hy hdy
        exact hd y hdy (fun hc => hy (Or.inr hc))
      · rw [if_neg hx, if_neg hx]
        exact .same (ih z v hd)
  | @diff seen x v0 w0 V₁ V₂ hdx hs hrest ih =>
      intro dead' z v hd
      rw [venvSet_cons, venvSet_cons]
      by_cases hx : x = z
      · subst hx
        rw [if_pos rfl, if_pos rfl]
        refine .same (hrest.mono_seen ?_)
        intro y hy hdy
        exact hd y hdy (fun hc => hy (Or.inr hc))
      · rw [if_neg hx, if_neg hx]
        exact .diff (hd _ hdx hx) hs (ih z v hd)

/-- Multi-assignment: every written name may be dropped from the dead set. -/
theorem setMany : ∀ (xs : List Ident) (vs : List D.Value) {d₀ d₁ sn : Ident → Prop}
    {V₁ V₂ : VEnv D}, VChg (D := D) d₀ k sn V₁ V₂ →
      xs.length = vs.length → (∀ x, d₀ x → x ∉ xs → d₁ x) →
      VChg d₁ k sn (VEnv.setMany V₁ xs vs) (VEnv.setMany V₂ xs vs) := by
  intro xs
  induction xs with
  | nil =>
      intro vs d₀ d₁ sn V₁ V₂ h _ hd
      have hz : ([] : List Ident).zip vs = [] := by simp
      simp only [VEnv.setMany, hz, List.foldl_nil]
      exact h.mono (fun x hx => hd x hx (by simp))
  | cons a rest ih =>
      intro vs d₀ d₁ sn V₁ V₂ h hlen hd
      cases vs with
      | nil => simp at hlen
      | cons b vs' =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          have hstep := h.set_kill (dead' := fun y => d₀ y ∧ y ≠ a) a b
            (fun x hx hne => ⟨hx, hne⟩)
          have hres := ih vs' hstep hlen
            (fun x hx hnot => hd x hx.1 (by
              simp only [List.mem_cons, not_or]
              exact ⟨hx.2, hnot⟩))
          simpa only [VEnv.setMany, List.zip_cons_cons, List.foldl_cons] using hres

/-! ### Prepending, dropping and `restore` -/

/-- Prepending identical bindings that do not shadow a dead name. -/
theorem prepend : ∀ (pre : VEnv D) {seen : Ident → Prop} {V₁ V₂ : VEnv D},
    VChg (D := D) dead k seen V₁ V₂ → (∀ x, dead x → x ∉ pre.map Prod.fst) →
      VChg dead k seen (pre ++ V₁) (pre ++ V₂) := by
  intro pre
  induction pre with
  | nil => intro seen V₁ V₂ h _; simpa using h
  | cons p rest ih =>
      intro seen V₁ V₂ h hfresh
      have hrest : ∀ x, dead x → x ∉ rest.map Prod.fst := by
        intro x hx hc
        exact hfresh x hx (by simp only [List.map_cons, List.mem_cons]; exact Or.inr hc)
      have hgrow : VChg (D := D) dead k (fun y => seen y ∨ y = p.1) V₁ V₂ :=
        h.grow_seen (extra := fun y => y = p.1) (fun x hx hc =>
          hfresh x hx (by simp only [List.map_cons, List.mem_cons]; exact Or.inl hc))
      have hih := ih hgrow hrest
      obtain ⟨y, w⟩ := p
      exact .same hih

/-- Dropping inner bindings, as long as the shared tail survives. -/
theorem drop : ∀ {seen : Ident → Prop} {V₁ V₂ : VEnv D},
    VChg (D := D) dead k seen V₁ V₂ → ∀ (m : Nat), m + k ≤ V₁.length →
      VChg dead k seen (V₁.drop m) (V₂.drop m) := by
  intro seen V₁ V₂ h
  induction h with
  | tail hlen =>
      intro m hm
      have hm0 : m = 0 := by omega
      subst hm0
      exact .tail (by simpa using hlen)
  | @same seen x v V₁ V₂ hrest ih =>
      intro m hm
      cases m with
      | zero => simpa using VChg.same hrest
      | succ m' =>
          simp only [List.drop_succ_cons]
          simp only [List.length_cons] at hm
          exact (ih m' (by omega)).shrink_seen (fun z hz => Or.inl hz)
  | @diff seen x v w V₁ V₂ hdx hs hrest ih =>
      intro m hm
      cases m with
      | zero => simpa using VChg.diff hdx hs hrest
      | succ m' =>
          simp only [List.drop_succ_cons]
          simp only [List.length_cons] at hm
          exact (ih m' (by omega)).shrink_seen (fun z hz => Or.inl hz)

/-- **Frame + restore.** Related entry environments and related body-exit
environments restore to related environments: both sides have the same length, so
`restore` drops the same prefix, and the shared tail lies below every
difference. -/
theorem restore_congr {Ve₁ Ve₂ Vb₁ Vb₂ : VEnv D}
    (hentry : VChg (D := D) dead k seen Ve₁ Ve₂)
    (hbody : VChg (D := D) dead k seen Vb₁ Vb₂)
    (hlen : Ve₁.length ≤ Vb₁.length) :
    VChg dead k seen (restore Ve₁ Vb₁) (restore Ve₂ Vb₂) := by
  have hE := hentry.length
  have hB := hbody.length
  have hk := hentry.tail_le
  show VChg dead k seen (Vb₁.drop (Vb₁.length - Ve₁.length))
    (Vb₂.drop (Vb₂.length - Ve₂.length))
  rw [← hB, ← hE]
  exact hbody.drop _ (by omega)

/-- A relation whose shared tail is the whole left environment is equality. -/
theorem eq_of_len : ∀ {seen : Ident → Prop} {V₁ V₂ : VEnv D},
    VChg (D := D) dead k seen V₁ V₂ → V₁.length = k → V₁ = V₂ := by
  intro seen V₁ V₂ h
  induction h with
  | tail => intro _; rfl
  | same hrest _ =>
      intro hlen
      exact absurd hlen (by have := hrest.tail_le; simp only [List.length_cons]; omega)
  | diff _ _ hrest _ =>
      intro hlen
      exact absurd hlen (by have := hrest.tail_le; simp only [List.length_cons]; omega)

/-- **Equal restores.** When the shared tail is exactly the entry environment,
the two sides restore to the *same* environment — the fact that lifts the
sequence-level simulation to `EquivBlock`. -/
theorem restore_eq {Ve Vb₁ Vb₂ : VEnv D}
    (hbody : VChg (D := D) dead Ve.length seen Vb₁ Vb₂)
    (hlen : Ve.length ≤ Vb₁.length) :
    restore Ve Vb₁ = restore Ve Vb₂ := by
  have hB := hbody.length
  have hd := hbody.drop (Vb₁.length - Ve.length) (by omega)
  show Vb₁.drop (Vb₁.length - Ve.length) = Vb₂.drop (Vb₂.length - Ve.length)
  rw [← hB]
  exact hd.eq_of_len (by simp only [List.length_drop]; omega)

end VChg

/-! ### Above the shared tail

The one-sided write lemma needs to know that the written name lives *above* the
shared tail; `AboveK` records exactly that, on keys alone, so it is preserved by
everything execution does to an environment (`venvKeys_suffix`). -/

/-- `x` occurs among the bindings above a tail of length `k`. -/
def AboveK (k : Nat) (x : Ident) (V : VEnv D) : Prop :=
  ∃ A T : List Ident, V.map Prod.fst = A ++ T ∧ T.length = k ∧ x ∈ A

namespace AboveK

/-- A freshly pushed binding is above the tail. -/
theorem head {k : Nat} {x : Ident} {v : D.Value} {V : VEnv D} (h : k ≤ V.length) :
    AboveK (D := D) k x ((x, v) :: V) := by
  refine ⟨x :: (V.map Prod.fst).take (V.length - k), (V.map Prod.fst).drop (V.length - k),
    ?_, ?_, List.mem_cons_self ..⟩
  · simp
  · simp only [List.length_drop, List.length_map]; omega

/-- Prepending bindings keeps a name above the tail. -/
theorem prepend {k : Nat} {x : Ident} {pre V : VEnv D} (h : AboveK (D := D) k x V) :
    AboveK (D := D) k x (pre ++ V) := by
  obtain ⟨A, T, hV, hT, hx⟩ := h
  exact ⟨pre.map Prod.fst ++ A, T, by simp [hV], hT, List.mem_append_right _ hx⟩

/-- A name among freshly prepended bindings is above the tail. -/
theorem prepend_mem {k : Nat} {x : Ident} {pre V : VEnv D} (hk : k ≤ V.length)
    (hx : x ∈ pre.map Prod.fst) : AboveK (D := D) k x (pre ++ V) := by
  refine ⟨pre.map Prod.fst ++ (V.map Prod.fst).take (V.length - k),
    (V.map Prod.fst).drop (V.length - k), ?_, ?_, List.mem_append_left _ hx⟩
  · simp
  · simp only [List.length_drop, List.length_map]; omega

/-- Above-the-tail depends only on keys, and execution only prepends keys. -/
theorem of_keys_suffix {k : Nat} {x : Ident} {V V' : VEnv D}
    (h : AboveK (D := D) k x V) (hs : V.map Prod.fst <:+ V'.map Prod.fst) :
    AboveK (D := D) k x V' := by
  obtain ⟨A, T, hV, hT, hx⟩ := h
  obtain ⟨pre, hpre⟩ := hs
  exact ⟨pre ++ A, T, by rw [← hpre, hV, List.append_assoc], hT, List.mem_append_right _ hx⟩

/-- Peel a non-matching head. -/
theorem peel {k : Nat} {x y : Ident} {v : D.Value} {V : VEnv D}
    (h : AboveK (D := D) k x ((y, v) :: V)) (hne : x ≠ y) : AboveK (D := D) k x V := by
  obtain ⟨A, T, hV, hT, hx⟩ := h
  cases A with
  | nil => exact absurd hx (by simp)
  | cons a A' =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at hV
      obtain ⟨ha, hV'⟩ := hV
      refine ⟨A', T, hV', hT, ?_⟩
      simp only [List.mem_cons] at hx
      exact hx.elim (fun hc => absurd (hc.trans ha.symm) hne) id

/-- Nothing is above a zero-height prefix. -/
theorem not_of_len {k : Nat} {x : Ident} {V : VEnv D} (hlen : V.length = k) :
    ¬ AboveK (D := D) k x V := by
  intro h
  obtain ⟨A, T, hV, hT, hx⟩ := h
  have hsum : A.length + T.length = k := by
    have hc := congrArg List.length hV
    simp only [List.length_map, List.length_append] at hc
    omega
  have hA : A.length = 0 := by omega
  exact absurd hx (by rw [List.eq_nil_of_length_eq_zero hA]; simp)

end AboveK

/-- **One-sided write.** Writing to a dead name above the shared tail on the
left creates a difference only at that name — this is the dead-store deletion
step: the source assigns, the target does not. -/
theorem VChg.set_left {dead : Ident → Prop} {k : Nat} :
    ∀ {seen : Ident → Prop} {V₁ V₂ : VEnv D},
    VChg (D := D) dead k seen V₁ V₂ →
    ∀ {dead' : Ident → Prop} {z : Ident} (v : D.Value),
      AboveK (D := D) k z V₁ → ¬ seen z → dead' z → (∀ x, dead x → dead' x) →
      VChg dead' k seen (VEnv.set V₁ z v) V₂ := by
  intro seen V₁ V₂ h
  induction h with
  | tail hlen => intro dead' z v hab _ _ _; exact absurd hab (AboveK.not_of_len hlen)
  | @same seen x v0 V₁ V₂ hrest ih =>
      intro dead' z v hab hns hdz hmono
      rw [venvSet_cons]
      by_cases hx : x = z
      · subst hx
        rw [if_pos rfl]
        exact .diff hdz hns (hrest.mono_seen (fun y _ hy => hmono y hy))
      · rw [if_neg hx]
        exact .same (ih v (hab.peel (fun hc => hx hc.symm))
          (fun hc => hc.elim hns (fun he => hx he.symm)) hdz hmono)
  | @diff seen x v0 w0 V₁ V₂ hdx hs hrest ih =>
      intro dead' z v hab hns hdz hmono
      rw [venvSet_cons]
      by_cases hx : x = z
      · subst hx
        rw [if_pos rfl]
        exact .diff hdz hns (hrest.mono_seen (fun y _ hy => hmono y hy))
      · rw [if_neg hx]
        exact .diff (hmono _ hdx) hs
          (ih v (hab.peel (fun hc => hx hc.symm))
            (fun hc => hc.elim hns (fun he => hx he.symm)) hdz hmono)

/-! ### The frame lemma -/

/-- Result correspondence: expression classes give identical results; statement
classes give the same state and outcome with `VChg`-related environments. -/
def VChgRes (dead : Ident → Prop) (k : Nat) (seen : Ident → Prop) : Res D → Res D → Prop
  | .eres r₁, .eres r₂ => r₁ = r₂
  | .sres V₁ st₁ o₁, .sres V₂ st₂ o₂ => VChg dead k seen V₁ V₂ ∧ st₁ = st₂ ∧ o₁ = o₂
  | _, _ => False

namespace VChgRes

variable {dead : Ident → Prop} {k : Nat} {seen : Ident → Prop}

theorem eres {r : EResult D} {res₂ : Res D} (h : VChgRes (D := D) dead k seen (.eres r) res₂) :
    res₂ = .eres r := by
  cases res₂ with
  | eres r₂ => simp only [VChgRes] at h; rw [h]
  | sres => simp only [VChgRes] at h

theorem sres {V₁ : VEnv D} {st o} {res₂ : Res D}
    (h : VChgRes (D := D) dead k seen (.sres V₁ st o) res₂) :
    ∃ V₂, res₂ = .sres V₂ st o ∧ VChg dead k seen V₁ V₂ := by
  cases res₂ with
  | eres => simp only [VChgRes] at h
  | sres V₂ st₂ o₂ =>
      simp only [VChgRes] at h
      obtain ⟨hrel, rfl, rfl⟩ := h
      exact ⟨V₂, rfl, hrel⟩

end VChgRes

/-- No dead name is mentioned by the code. -/
def DeadFree (dead : Ident → Prop) (code : Code D.Op) : Prop :=
  ∀ x, dead x → codeMentions x code = false

/-- Mention-freeness is monotone along syntactic containment. -/
theorem DeadFree.mono {dead : Ident → Prop} {c₁ c₂ : Code D.Op} (h : DeadFree dead c₁)
    (hsub : ∀ x, codeMentions x c₁ = false → codeMentions x c₂ = false) : DeadFree dead c₂ :=
  fun x hx => hsub x (h x hx)

section FrameLemma

variable [DecidableEq D.Value]

/-- Transport above-the-tail along a statement's execution. -/
theorem AboveK.mono_step {k : Nat} {x : Ident} {V V' : VEnv D} {funs : FunEnv D}
    {st st' : D.State} {code : Code D.Op} {o : Outcome}
    (h : AboveK (D := D) k x V) (hstep : Step D funs V st code (.sres V' st' o)) :
    AboveK (D := D) k x V' :=
  h.of_keys_suffix (venvKeys_suffix hstep rfl)

/-- **The value-change frame lemma.** Code that mentions no dead name runs in
lock-step from `VChg`-related environments: expression results are identical and
statement results stay related at the same tail index. The relation is symmetric
(`VChg.symm`), so this single direction gives both implications. -/
theorem vchgStep {funs : FunEnv D} {V₁ : VEnv D} {st : D.State} {code : Code D.Op}
    {res₁ : Res D} (h : Step D funs V₁ st code res₁) :
    ∀ {dead : Ident → Prop} {k : Nat} {seen : Ident → Prop} {V₂ : VEnv D},
      VChg (D := D) dead k seen V₁ V₂ → DeadFree dead code →
      ∃ res₂, Step D funs V₂ st code res₂ ∧ VChgRes dead k seen res₁ res₂ := by
  induction h with
  | lit => intro dead k seen V₂ hrel hm; exact ⟨_, Step.lit, rfl⟩
  | @var _ _ _ y vv hv =>
      intro dead k seen V₂ hrel hm
      have hy : ¬ dead y := by
        intro hd
        have hc := hm y hd
        simp [codeMentions, exprMentions] at hc
      exact ⟨_, Step.var (by rw [← hrel.get hy]; exact hv), rfl⟩
  | builtinOk hargs hb iha =>
      intro dead k seen V₂ hrel hm
      obtain ⟨r, hs, hr⟩ := iha hrel (hm.mono (fun z hz => by
        simpa only [codeMentions, exprMentions] using hz))
      obtain rfl := hr.eres
      exact ⟨_, Step.builtinOk hs hb, rfl⟩
  | builtinHalt hargs hb iha =>
      intro dead k seen V₂ hrel hm
      obtain ⟨r, hs, hr⟩ := iha hrel (hm.mono (fun z hz => by
        simpa only [codeMentions, exprMentions] using hz))
      obtain rfl := hr.eres
      exact ⟨_, Step.builtinHalt hs hb, rfl⟩
  | builtinArgsHalt hargs iha =>
      intro dead k seen V₂ hrel hm
      obtain ⟨r, hs, hr⟩ := iha hrel (hm.mono (fun z hz => by
        simpa only [codeMentions, exprMentions] using hz))
      obtain rfl := hr.eres
      exact ⟨_, Step.builtinArgsHalt hs, rfl⟩
  | callOk hargs hl hlen hbody ho iha ihbody =>
      intro dead k seen V₂ hrel hm
      obtain ⟨r, hs, hr⟩ := iha hrel (hm.mono (fun z hz => by
        simpa only [codeMentions, exprMentions] using hz))
      obtain rfl := hr.eres
      exact ⟨_, Step.callOk hs hl hlen hbody ho, rfl⟩
  | callHalt hargs hl hlen hbody iha ihbody =>
      intro dead k seen V₂ hrel hm
      obtain ⟨r, hs, hr⟩ := iha hrel (hm.mono (fun z hz => by
        simpa only [codeMentions, exprMentions] using hz))
      obtain rfl := hr.eres
      exact ⟨_, Step.callHalt hs hl hlen hbody, rfl⟩
  | callArgsHalt hargs iha =>
      intro dead k seen V₂ hrel hm
      obtain ⟨r, hs, hr⟩ := iha hrel (hm.mono (fun z hz => by
        simpa only [codeMentions, exprMentions] using hz))
      obtain rfl := hr.eres
      exact ⟨_, Step.callArgsHalt hs, rfl⟩
  | argsNil => intro dead k seen V₂ hrel hm; exact ⟨_, Step.argsNil, rfl⟩
  | argsCons hrest he ihrest ihe =>
      intro dead k seen V₂ hrel hm
      obtain ⟨rr, hsr, hrr⟩ := ihrest hrel (hm.mono (fun z hz => by
        simp only [codeMentions, argsMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.2))
      obtain rfl := hrr.eres
      obtain ⟨re, hse, hre⟩ := ihe hrel (hm.mono (fun z hz => by
        simp only [codeMentions, argsMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.1))
      obtain rfl := hre.eres
      exact ⟨_, Step.argsCons hsr hse, rfl⟩
  | argsRestHalt hrest ihrest =>
      intro dead k seen V₂ hrel hm
      obtain ⟨rr, hsr, hrr⟩ := ihrest hrel (hm.mono (fun z hz => by
        simp only [codeMentions, argsMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.2))
      obtain rfl := hrr.eres
      exact ⟨_, Step.argsRestHalt hsr, rfl⟩
  | argsHeadHalt hrest he ihrest ihe =>
      intro dead k seen V₂ hrel hm
      obtain ⟨rr, hsr, hrr⟩ := ihrest hrel (hm.mono (fun z hz => by
        simp only [codeMentions, argsMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.2))
      obtain rfl := hrr.eres
      obtain ⟨re, hse, hre⟩ := ihe hrel (hm.mono (fun z hz => by
        simp only [codeMentions, argsMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.1))
      obtain rfl := hre.eres
      exact ⟨_, Step.argsHeadHalt hsr hse, rfl⟩
  | funDef => intro dead k seen V₂ hrel hm; exact ⟨_, Step.funDef, ⟨hrel, rfl, rfl⟩⟩
  | block hbody ihbody =>
      intro dead k seen V₂ hrel hm
      obtain ⟨r, hs, hr⟩ := ihbody hrel (hm.mono (fun z hz => by
        simpa only [codeMentions, stmtMentions] using hz))
      obtain ⟨Vb₂, rfl, hrel2⟩ := hr.sres
      exact ⟨_, Step.block hs,
        ⟨VChg.restore_congr hrel hrel2 (venvLen_mono hbody rfl), rfl, rfl⟩⟩
  | @letZero _ _ _ vars =>
      intro dead k seen V₂ hrel hm
      refine ⟨_, Step.letZero, ⟨?_, rfl, rfl⟩⟩
      refine hrel.prepend _ (fun x hx => ?_)
      rw [bindZeros_fst]
      have hc := hm x hx
      simp only [codeMentions, stmtMentions, optExprMentions, Bool.or_false,
        decide_eq_false_iff_not] at hc
      exact hc
  | @letVal _ _ _ vars e vals st1 he hlen ihe =>
      intro dead k seen V₂ hrel hm
      obtain ⟨r, hs, hr⟩ := ihe hrel (hm.mono (fun z hz => by
        simp only [codeMentions, stmtMentions, optExprMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.2))
      obtain rfl := hr.eres
      refine ⟨_, Step.letVal hs hlen, ⟨?_, rfl, rfl⟩⟩
      refine hrel.prepend _ (fun x hx => ?_)
      rw [List.map_fst_zip (by omega)]
      have hc := hm x hx
      simp only [codeMentions, stmtMentions, optExprMentions, Bool.or_eq_false_iff,
        decide_eq_false_iff_not] at hc
      exact hc.1
  | letHalt he ihe =>
      intro dead k seen V₂ hrel hm
      obtain ⟨r, hs, hr⟩ := ihe hrel (hm.mono (fun z hz => by
        simp only [codeMentions, stmtMentions, optExprMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.2))
      obtain rfl := hr.eres
      exact ⟨_, Step.letHalt hs, ⟨hrel, rfl, rfl⟩⟩
  | @assignVal _ _ _ vars e vals st1 he hlen ihe =>
      intro dead k seen V₂ hrel hm
      obtain ⟨r, hs, hr⟩ := ihe hrel (hm.mono (fun z hz => by
        simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.2))
      obtain rfl := hr.eres
      exact ⟨_, Step.assignVal hs hlen,
        ⟨VChg.setMany vars vals hrel hlen.symm (fun x hx _ => hx), rfl, rfl⟩⟩
  | assignHalt he ihe =>
      intro dead k seen V₂ hrel hm
      obtain ⟨r, hs, hr⟩ := ihe hrel (hm.mono (fun z hz => by
        simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.2))
      obtain rfl := hr.eres
      exact ⟨_, Step.assignHalt hs, ⟨hrel, rfl, rfl⟩⟩
  | exprStmt he ihe =>
      intro dead k seen V₂ hrel hm
      obtain ⟨r, hs, hr⟩ := ihe hrel (hm.mono (fun z hz => by
        simpa only [codeMentions, stmtMentions] using hz))
      obtain rfl := hr.eres
      exact ⟨_, Step.exprStmt hs, ⟨hrel, rfl, rfl⟩⟩
  | exprStmtHalt he ihe =>
      intro dead k seen V₂ hrel hm
      obtain ⟨r, hs, hr⟩ := ihe hrel (hm.mono (fun z hz => by
        simpa only [codeMentions, stmtMentions] using hz))
      obtain rfl := hr.eres
      exact ⟨_, Step.exprStmtHalt hs, ⟨hrel, rfl, rfl⟩⟩
  | ifTrue hc hcv hbody ihc ihbody =>
      intro dead k seen V₂ hrel hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hrel (hm.mono (fun z hz => by
        simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.1))
      obtain rfl := hrc.eres
      obtain ⟨rb, hsb, hrb⟩ := ihbody hrel (hm.mono (fun z hz => by
        simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions, stmtMentions] using hz.2))
      obtain ⟨V'₂, rfl, hrel2⟩ := hrb.sres
      exact ⟨_, Step.ifTrue hsc hcv hsb, ⟨hrel2, rfl, rfl⟩⟩
  | ifFalse hc hcv ihc =>
      intro dead k seen V₂ hrel hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hrel (hm.mono (fun z hz => by
        simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.1))
      obtain rfl := hrc.eres
      exact ⟨_, Step.ifFalse hsc hcv, ⟨hrel, rfl, rfl⟩⟩
  | ifHalt hc ihc =>
      intro dead k seen V₂ hrel hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hrel (hm.mono (fun z hz => by
        simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.1))
      obtain rfl := hrc.eres
      exact ⟨_, Step.ifHalt hsc, ⟨hrel, rfl, rfl⟩⟩
  | switchExec hc hbody ihc ihbody =>
      intro dead k seen V₂ hrel hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hrel (hm.mono (fun z hz => by
        simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.1.1))
      obtain rfl := hrc.eres
      obtain ⟨rb, hsb, hrb⟩ := ihbody hrel (hm.mono (fun z hz => by
        simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hz
        simp only [codeMentions, stmtMentions]
        exact selectSwitch_not_mentions hz.1.2 hz.2))
      obtain ⟨V'₂, rfl, hrel2⟩ := hrb.sres
      exact ⟨_, Step.switchExec hsc hsb, ⟨hrel2, rfl, rfl⟩⟩
  | switchHalt hc ihc =>
      intro dead k seen V₂ hrel hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hrel (hm.mono (fun z hz => by
        simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.1.1))
      obtain rfl := hrc.eres
      exact ⟨_, Step.switchHalt hsc, ⟨hrel, rfl, rfl⟩⟩
  | forLoop hinit hloop ihinit ihloop =>
      intro dead k seen V₂ hrel hm
      obtain ⟨ri, hsi, hri⟩ := ihinit hrel (hm.mono (fun z hz => by
        simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.1.1.1))
      obtain ⟨Vi₂, rfl, hreli⟩ := hri.sres
      obtain ⟨rl, hsl, hrl⟩ := ihloop hreli (hm.mono (fun z hz => by
        simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hz
        simp only [codeMentions, Bool.or_eq_false_iff]
        exact ⟨⟨hz.1.1.2, hz.1.2⟩, hz.2⟩))
      obtain ⟨Ve₂, rfl, hrell⟩ := hrl.sres
      exact ⟨_, Step.forLoop hsi hsl,
        ⟨VChg.restore_congr hrel hrell
          (Nat.le_trans (venvLen_mono hinit rfl) (venvLen_mono hloop rfl)), rfl, rfl⟩⟩
  | forInitHalt hinit ihinit =>
      intro dead k seen V₂ hrel hm
      obtain ⟨ri, hsi, hri⟩ := ihinit hrel (hm.mono (fun z hz => by
        simp only [codeMentions, stmtMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.1.1.1))
      obtain ⟨Vi₂, rfl, hreli⟩ := hri.sres
      exact ⟨_, Step.forInitHalt hsi,
        ⟨VChg.restore_congr hrel hreli (venvLen_mono hinit rfl), rfl, rfl⟩⟩
  | «break» => intro dead k seen V₂ hrel hm; exact ⟨_, Step.break, ⟨hrel, rfl, rfl⟩⟩
  | «continue» => intro dead k seen V₂ hrel hm; exact ⟨_, Step.continue, ⟨hrel, rfl, rfl⟩⟩
  | leave => intro dead k seen V₂ hrel hm; exact ⟨_, Step.leave, ⟨hrel, rfl, rfl⟩⟩
  | seqNil => intro dead k seen V₂ hrel hm; exact ⟨_, Step.seqNil, ⟨hrel, rfl, rfl⟩⟩
  | seqCons hs hrest ihs ihrest =>
      intro dead k seen V₂ hrel hm
      obtain ⟨rs, hss, hrs⟩ := ihs hrel (hm.mono (fun z hz => by
        simp only [codeMentions, stmtsMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.1))
      obtain ⟨V₁', rfl, hrel1⟩ := hrs.sres
      obtain ⟨rr, hsr, hrr⟩ := ihrest hrel1 (hm.mono (fun z hz => by
        simp only [codeMentions, stmtsMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.2))
      obtain ⟨V₂', rfl, hrel2⟩ := hrr.sres
      exact ⟨_, Step.seqCons hss hsr, ⟨hrel2, rfl, rfl⟩⟩
  | seqStop hs hne ihs =>
      intro dead k seen V₂ hrel hm
      obtain ⟨rs, hss, hrs⟩ := ihs hrel (hm.mono (fun z hz => by
        simp only [codeMentions, stmtsMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.1))
      obtain ⟨V₁', rfl, hrel1⟩ := hrs.sres
      exact ⟨_, Step.seqStop hss hne, ⟨hrel1, rfl, rfl⟩⟩
  | loopDone hc hcv ihc =>
      intro dead k seen V₂ hrel hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hrel (hm.mono (fun z hz => by
        simp only [codeMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.1.1))
      obtain rfl := hrc.eres
      exact ⟨_, Step.loopDone hsc hcv, ⟨hrel, rfl, rfl⟩⟩
  | loopCondHalt hc ihc =>
      intro dead k seen V₂ hrel hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hrel (hm.mono (fun z hz => by
        simp only [codeMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.1.1))
      obtain rfl := hrc.eres
      exact ⟨_, Step.loopCondHalt hsc, ⟨hrel, rfl, rfl⟩⟩
  | loopStep hc hcv hbody hob hpost hrec ihc ihbody ihpost ihrec =>
      intro dead k seen V₂ hrel hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hrel (hm.mono (fun z hz => by
        simp only [codeMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.1.1))
      obtain rfl := hrc.eres
      obtain ⟨rb, hsb, hrb⟩ := ihbody hrel (hm.mono (fun z hz => by
        simp only [codeMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions, stmtMentions] using hz.2))
      obtain ⟨Vb₂, rfl, hrelb⟩ := hrb.sres
      obtain ⟨rp, hsp, hrp⟩ := ihpost hrelb (hm.mono (fun z hz => by
        simp only [codeMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions, stmtMentions] using hz.1.2))
      obtain ⟨Vp₂, rfl, hrelp⟩ := hrp.sres
      obtain ⟨rr, hsr, hrr⟩ := ihrec hrelp hm
      obtain ⟨Ve₂, rfl, hrelr⟩ := hrr.sres
      exact ⟨_, Step.loopStep hsc hcv hsb hob hsp hsr, ⟨hrelr, rfl, rfl⟩⟩
  | loopPostHalt hc hcv hbody hob hpost ihc ihbody ihpost =>
      intro dead k seen V₂ hrel hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hrel (hm.mono (fun z hz => by
        simp only [codeMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.1.1))
      obtain rfl := hrc.eres
      obtain ⟨rb, hsb, hrb⟩ := ihbody hrel (hm.mono (fun z hz => by
        simp only [codeMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions, stmtMentions] using hz.2))
      obtain ⟨Vb₂, rfl, hrelb⟩ := hrb.sres
      obtain ⟨rp, hsp, hrp⟩ := ihpost hrelb (hm.mono (fun z hz => by
        simp only [codeMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions, stmtMentions] using hz.1.2))
      obtain ⟨Vp₂, rfl, hrelp⟩ := hrp.sres
      exact ⟨_, Step.loopPostHalt hsc hcv hsb hob hsp, ⟨hrelp, rfl, rfl⟩⟩
  | loopBreak hc hcv hbody ihc ihbody =>
      intro dead k seen V₂ hrel hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hrel (hm.mono (fun z hz => by
        simp only [codeMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.1.1))
      obtain rfl := hrc.eres
      obtain ⟨rb, hsb, hrb⟩ := ihbody hrel (hm.mono (fun z hz => by
        simp only [codeMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions, stmtMentions] using hz.2))
      obtain ⟨Vb₂, rfl, hrelb⟩ := hrb.sres
      exact ⟨_, Step.loopBreak hsc hcv hsb, ⟨hrelb, rfl, rfl⟩⟩
  | loopLeave hc hcv hbody ihc ihbody =>
      intro dead k seen V₂ hrel hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hrel (hm.mono (fun z hz => by
        simp only [codeMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.1.1))
      obtain rfl := hrc.eres
      obtain ⟨rb, hsb, hrb⟩ := ihbody hrel (hm.mono (fun z hz => by
        simp only [codeMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions, stmtMentions] using hz.2))
      obtain ⟨Vb₂, rfl, hrelb⟩ := hrb.sres
      exact ⟨_, Step.loopLeave hsc hcv hsb, ⟨hrelb, rfl, rfl⟩⟩
  | loopBodyHalt hc hcv hbody ihc ihbody =>
      intro dead k seen V₂ hrel hm
      obtain ⟨rc, hsc, hrc⟩ := ihc hrel (hm.mono (fun z hz => by
        simp only [codeMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions] using hz.1.1))
      obtain rfl := hrc.eres
      obtain ⟨rb, hsb, hrb⟩ := ihbody hrel (hm.mono (fun z hz => by
        simp only [codeMentions, Bool.or_eq_false_iff] at hz
        simpa only [codeMentions, stmtMentions] using hz.2))
      obtain ⟨Vb₂, rfl, hrelb⟩ := hrb.sres
      exact ⟨_, Step.loopBodyHalt hsc hcv hsb, ⟨hrelb, rfl, rfl⟩⟩

end FrameLemma

end YulEvmCompiler.Optimizer
