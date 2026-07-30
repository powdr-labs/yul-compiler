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

/-! ### Block equivalence relative to a bound set

`EquivBlock` quantifies over *every* variable environment. A pass whose rewrite
condition is "these names are provably bound here" cannot meet that inside a
function body — the removed right-hand side is stuck on environments where its
variables are unbound, and that stuckness is observable. `BEquivBlock bound`
restricts the quantifier to environments binding `bound`, which is exactly what
the call rule's `callOk` environment supplies for `params ++ rets`.

This is the subset-`SubBound` counterpart of `BoundFunCongr`'s exact-layout
`BoundEquivBlock`; because the passes using it keep the environment's *shape*,
the halt case needs no special treatment and the relation is a plain `Iff`. -/

/-- Every listed ident is in the environment's domain. -/
def SubBound (V : VEnv D) (bound : List Ident) : Prop :=
  ∀ x ∈ bound, x ∈ V.map Prod.fst

theorem SubBound.nil (V : VEnv D) : SubBound V ([] : List Ident) :=
  fun _ hx => absurd hx List.not_mem_nil

section BoundEquiv

variable [DecidableEq D.Value]

/-- Boundness is monotone along execution (domains only grow). -/
theorem SubBound.mono {V V' : VEnv D} {bound : List Ident} {funs st code st' o}
    (hb : SubBound V bound) (h : Step D funs V st code (.sres V' st' o)) :
    SubBound V' bound :=
  fun x hx => dom_mono h (hb x hx)

/-- Statement equivalence at environments binding `bound`. -/
def BEquivStmt (bound : List Ident) (s₁ s₂ : Stmt D.Op) : Prop :=
  ∀ funs V st V' st' o, SubBound V bound →
    (ExecStmt D funs V st s₁ V' st' o ↔ ExecStmt D funs V st s₂ V' st' o)

/-- Sequence equivalence at environments binding `bound`. -/
def BEquivStmts (bound : List Ident) (ss₁ ss₂ : List (Stmt D.Op)) : Prop :=
  ∀ funs V st V' st' o, SubBound V bound →
    (ExecStmts D funs V st ss₁ V' st' o ↔ ExecStmts D funs V st ss₂ V' st' o)

/-- Block equivalence at environments binding `bound`. -/
def BEquivBlock (bound : List Ident) (b₁ b₂ : Block D.Op) : Prop :=
  BEquivStmt (D := D) bound (.block b₁) (.block b₂)

theorem BEquivStmt.refl (bound : List Ident) (s : Stmt D.Op) :
    BEquivStmt (D := D) bound s s := fun _ _ _ _ _ _ _ => Iff.rfl

theorem BEquivStmt.symm {bound : List Ident} {s₁ s₂ : Stmt D.Op}
    (h : BEquivStmt (D := D) bound s₁ s₂) : BEquivStmt (D := D) bound s₂ s₁ :=
  fun funs V st V' st' o hb => (h funs V st V' st' o hb).symm

theorem BEquivStmt.trans {bound : List Ident} {s₁ s₂ s₃ : Stmt D.Op}
    (h₁ : BEquivStmt (D := D) bound s₁ s₂) (h₂ : BEquivStmt (D := D) bound s₂ s₃) :
    BEquivStmt (D := D) bound s₁ s₃ :=
  fun funs V st V' st' o hb =>
    (h₁ funs V st V' st' o hb).trans (h₂ funs V st V' st' o hb)

theorem BEquivStmts.refl (bound : List Ident) (ss : List (Stmt D.Op)) :
    BEquivStmts (D := D) bound ss ss := fun _ _ _ _ _ _ _ => Iff.rfl

theorem BEquivStmts.symm {bound : List Ident} {ss₁ ss₂ : List (Stmt D.Op)}
    (h : BEquivStmts (D := D) bound ss₁ ss₂) : BEquivStmts (D := D) bound ss₂ ss₁ :=
  fun funs V st V' st' o hb => (h funs V st V' st' o hb).symm

theorem BEquivStmts.trans {bound : List Ident} {ss₁ ss₂ ss₃ : List (Stmt D.Op)}
    (h₁ : BEquivStmts (D := D) bound ss₁ ss₂) (h₂ : BEquivStmts (D := D) bound ss₂ ss₃) :
    BEquivStmts (D := D) bound ss₁ ss₃ :=
  fun funs V st V' st' o hb =>
    (h₁ funs V st V' st' o hb).trans (h₂ funs V st V' st' o hb)

theorem BEquivBlock.refl (bound : List Ident) (b : Block D.Op) :
    BEquivBlock (D := D) bound b b := BEquivStmt.refl _ _

theorem BEquivBlock.symm {bound : List Ident} {b₁ b₂ : Block D.Op}
    (h : BEquivBlock (D := D) bound b₁ b₂) : BEquivBlock (D := D) bound b₂ b₁ :=
  BEquivStmt.symm h

theorem BEquivBlock.trans {bound : List Ident} {b₁ b₂ b₃ : Block D.Op}
    (h₁ : BEquivBlock (D := D) bound b₁ b₂) (h₂ : BEquivBlock (D := D) bound b₂ b₃) :
    BEquivBlock (D := D) bound b₁ b₃ := BEquivStmt.trans h₁ h₂

/-- At the empty bound set the restriction is vacuous. -/
theorem BEquivBlock.toEquiv {b₁ b₂ : Block D.Op}
    (h : BEquivBlock (D := D) [] b₁ b₂) : EquivBlock D b₁ b₂ :=
  fun funs V st V' st' o => h funs V st V' st' o (SubBound.nil V)

/-- An unrestricted equivalence is a restricted one. -/
theorem BEquivBlock.ofEquiv {bound : List Ident} {b₁ b₂ : Block D.Op}
    (h : EquivBlock D b₁ b₂) : BEquivBlock (D := D) bound b₁ b₂ :=
  fun funs V st V' st' o _ => h funs V st V' st' o

/-! #### Sequence congruence -/

private theorem bconsImp {bound : List Ident} {s₁ s₂ : Stmt D.Op} {ss₁ ss₂}
    (hs : BEquivStmt (D := D) bound s₁ s₂) (hss : BEquivStmts (D := D) bound ss₁ ss₂)
    {funs V st V' st' o} (hb : SubBound V bound)
    (h : ExecStmts D funs V st (s₁ :: ss₁) V' st' o) :
    ExecStmts D funs V st (s₂ :: ss₂) V' st' o := by
  cases h with
  | seqCons h₁ h₂ =>
      exact Step.seqCons ((hs _ _ _ _ _ _ hb).mp h₁)
        ((hss _ _ _ _ _ _ (hb.mono h₁)).mp h₂)
  | seqStop h₁ h₂ => exact Step.seqStop ((hs _ _ _ _ _ _ hb).mp h₁) h₂

/-- Congruence: sequences extend equivalences element-wise. -/
theorem BEquivStmts.cons_congr {bound : List Ident} {s₁ s₂ : Stmt D.Op} {ss₁ ss₂}
    (hs : BEquivStmt (D := D) bound s₁ s₂) (hss : BEquivStmts (D := D) bound ss₁ ss₂) :
    BEquivStmts (D := D) bound (s₁ :: ss₁) (s₂ :: ss₂) :=
  fun _ _ _ _ _ _ hb => ⟨bconsImp hs hss hb, bconsImp hs.symm hss.symm hb⟩

/-! #### Statement congruences -/

private theorem bcondImp {bound : List Ident} {c : Expr D.Op} {b₁ b₂ : Block D.Op}
    (hb2 : BEquivBlock (D := D) bound b₁ b₂) {funs V st V' st' o} (hb : SubBound V bound)
    (h : ExecStmt D funs V st (.cond c b₁) V' st' o) :
    ExecStmt D funs V st (.cond c b₂) V' st' o := by
  cases h with
  | ifTrue h₁ h₂ h₃ => exact Step.ifTrue h₁ h₂ ((hb2 _ _ _ _ _ _ hb).mp h₃)
  | ifFalse h₁ h₂ => exact Step.ifFalse h₁ h₂
  | ifHalt h₁ => exact Step.ifHalt h₁

/-- Congruence: `if` with an equivalent body. -/
theorem BEquivStmt.cond_congr {bound : List Ident} (c : Expr D.Op) {b₁ b₂ : Block D.Op}
    (hb2 : BEquivBlock (D := D) bound b₁ b₂) :
    BEquivStmt (D := D) bound (.cond c b₁) (.cond c b₂) :=
  fun _ _ _ _ _ _ hb => ⟨bcondImp hb2 hb, bcondImp hb2.symm hb⟩

/-- `selectSwitch` respects pairwise-related cases: equal labels, related blocks. -/
theorem selectSwitch_bcongr {bound : List Ident} {cv : D.Value}
    {cs₁ cs₂ : List (Literal × Block D.Op)} {dflt₁ dflt₂ : Option (Block D.Op)}
    (hcases : List.Forall₂ (fun p q => p.1 = q.1 ∧ BEquivBlock (D := D) bound p.2 q.2) cs₁ cs₂)
    (hdflt : BEquivBlock (D := D) bound (dflt₁.getD []) (dflt₂.getD [])) :
    BEquivBlock (D := D) bound (selectSwitch D cv cs₁ dflt₁) (selectSwitch D cv cs₂ dflt₂) := by
  induction hcases with
  | nil => simpa [selectSwitch] using hdflt
  | @cons p q t₁ t₂ hpq ht ih =>
      obtain ⟨hl, hbq⟩ := hpq
      by_cases hcv : cv = D.litValue p.1
      · have h₁ : List.find? (fun r => decide (cv = D.litValue r.1)) (p :: t₁) = some p :=
          List.find?_cons_of_pos (by simp [hcv])
        have h₂ : List.find? (fun r => decide (cv = D.litValue r.1)) (q :: t₂) = some q :=
          List.find?_cons_of_pos (by simp [← hl, hcv])
        simpa only [selectSwitch, h₁, h₂] using hbq
      · have h₁ : List.find? (fun r => decide (cv = D.litValue r.1)) (p :: t₁) =
            List.find? (fun r => decide (cv = D.litValue r.1)) t₁ :=
          List.find?_cons_of_neg (by simp [hcv])
        have h₂ : List.find? (fun r => decide (cv = D.litValue r.1)) (q :: t₂) =
            List.find? (fun r => decide (cv = D.litValue r.1)) t₂ :=
          List.find?_cons_of_neg (by simp [← hl, hcv])
        simpa only [selectSwitch, h₁, h₂] using ih

private theorem bswitchImp {bound : List Ident} {c : Expr D.Op} {cs₁ cs₂ dflt₁ dflt₂}
    (hsel : ∀ cv, BEquivBlock (D := D) bound
      (selectSwitch D cv cs₁ dflt₁) (selectSwitch D cv cs₂ dflt₂))
    {funs V st V' st' o} (hb : SubBound V bound)
    (h : ExecStmt D funs V st (.switch c cs₁ dflt₁) V' st' o) :
    ExecStmt D funs V st (.switch c cs₂ dflt₂) V' st' o := by
  cases h with
  | switchExec h₁ h₂ => exact Step.switchExec h₁ ((hsel _ _ _ _ _ _ _ hb).mp h₂)
  | switchHalt h₁ => exact Step.switchHalt h₁

/-- Congruence: `switch` with pairwise-related cases and defaults. -/
theorem BEquivStmt.switch_congr {bound : List Ident} (c : Expr D.Op)
    {cs₁ cs₂ : List (Literal × Block D.Op)} {dflt₁ dflt₂ : Option (Block D.Op)}
    (hcases : List.Forall₂ (fun p q => p.1 = q.1 ∧ BEquivBlock (D := D) bound p.2 q.2) cs₁ cs₂)
    (hdflt : BEquivBlock (D := D) bound (dflt₁.getD []) (dflt₂.getD [])) :
    BEquivStmt (D := D) bound (.switch c cs₁ dflt₁) (.switch c cs₂ dflt₂) := by
  have hsym : List.Forall₂
      (fun (p q : Literal × Block D.Op) => p.1 = q.1 ∧ BEquivBlock (D := D) bound p.2 q.2)
      cs₂ cs₁ := by
    induction hcases with
    | nil => exact .nil
    | cons hh _ ih => exact .cons ⟨hh.1.symm, hh.2.symm⟩ ih
  exact fun _ _ _ _ _ _ hb =>
    ⟨bswitchImp (fun cv => selectSwitch_bcongr hcases hdflt) hb,
     bswitchImp (fun cv => selectSwitch_bcongr hsym hdflt.symm) hb⟩

private theorem bloopImp {bound : List Ident} {c : Expr D.Op}
    {post₁ post₂ body₁ body₂ : Block D.Op}
    (hpost : BEquivBlock (D := D) bound post₁ post₂)
    (hbody : BEquivBlock (D := D) bound body₁ body₂) :
    ∀ {funs V st code res}, Step D funs V st code res →
      code = .loop c post₁ body₁ → SubBound V bound →
      Step D funs V st (.loop c post₂ body₂) res := by
  intro funs V st code res h
  induction h with
  | @loopDone _ _ _ _ _ _ _ _ hcv hz =>
      intro hcode _
      injection hcode with h1 h2 h3; subst h1; subst h2; subst h3
      exact Step.loopDone hcv hz
  | @loopCondHalt _ _ _ _ _ _ _ hcv =>
      intro hcode _
      injection hcode with h1 h2 h3; subst h1; subst h2; subst h3
      exact Step.loopCondHalt hcv
  | @loopStep _ _ _ _ _ _ _ _ Vb stb ob Vp stp _ _ _ hcv hnz hbd hob hp _ _ _ _ ihr =>
      intro hcode hb
      injection hcode with h1 h2 h3; subst h1; subst h2; subst h3
      exact Step.loopStep hcv hnz ((hbody _ _ _ _ _ _ hb).mp hbd) hob
        ((hpost _ _ _ _ _ _ (hb.mono hbd)).mp hp)
        (ihr rfl ((hb.mono hbd).mono hp))
  | @loopPostHalt _ _ _ _ _ _ _ _ Vb stb ob _ _ hcv hnz hbd hob hp _ _ _ =>
      intro hcode hb
      injection hcode with h1 h2 h3; subst h1; subst h2; subst h3
      exact Step.loopPostHalt hcv hnz ((hbody _ _ _ _ _ _ hb).mp hbd) hob
        ((hpost _ _ _ _ _ _ (hb.mono hbd)).mp hp)
  | @loopBreak _ _ _ _ _ _ _ _ _ _ hcv hnz hbd _ _ =>
      intro hcode hb
      injection hcode with h1 h2 h3; subst h1; subst h2; subst h3
      exact Step.loopBreak hcv hnz ((hbody _ _ _ _ _ _ hb).mp hbd)
  | @loopLeave _ _ _ _ _ _ _ _ _ _ hcv hnz hbd _ _ =>
      intro hcode hb
      injection hcode with h1 h2 h3; subst h1; subst h2; subst h3
      exact Step.loopLeave hcv hnz ((hbody _ _ _ _ _ _ hb).mp hbd)
  | @loopBodyHalt _ _ _ _ _ _ _ _ _ _ hcv hnz hbd _ _ =>
      intro hcode hb
      injection hcode with h1 h2 h3; subst h1; subst h2; subst h3
      exact Step.loopBodyHalt hcv hnz ((hbody _ _ _ _ _ _ hb).mp hbd)
  | _ => exact fun hcode _ => nomatch hcode

private theorem bforImp {bound : List Ident} {init : Block D.Op} {c : Expr D.Op}
    {post₁ post₂ body₁ body₂ : Block D.Op}
    (hpost : BEquivBlock (D := D) bound post₁ post₂)
    (hbody : BEquivBlock (D := D) bound body₁ body₂)
    {funs V st V' st' o} (hb : SubBound V bound)
    (h : ExecStmt D funs V st (.forLoop init c post₁ body₁) V' st' o) :
    ExecStmt D funs V st (.forLoop init c post₂ body₂) V' st' o := by
  cases h with
  | forLoop hinit hloop =>
      exact Step.forLoop hinit (bloopImp hpost hbody hloop rfl (hb.mono hinit))
  | forInitHalt hinit => exact Step.forInitHalt hinit

/-- Congruence: `for` with an equivalent post-block and body. -/
theorem BEquivStmt.forLoop_congr {bound : List Ident} (init : Block D.Op) (c : Expr D.Op)
    {post₁ post₂ body₁ body₂ : Block D.Op}
    (hpost : BEquivBlock (D := D) bound post₁ post₂)
    (hbody : BEquivBlock (D := D) bound body₁ body₂) :
    BEquivStmt (D := D) bound (.forLoop init c post₁ body₁) (.forLoop init c post₂ body₂) :=
  fun _ _ _ _ _ _ hb =>
    ⟨bforImp hpost hbody hb, bforImp hpost.symm hbody.symm hb⟩

/-! #### Blocks, with the hoisted scope fixed -/

private theorem bblockImp {bound : List Ident} {b₁ b₂ : Block D.Op}
    (hss : BEquivStmts (D := D) bound b₁ b₂) (hh : hoist D b₁ = hoist D b₂)
    {funs V st V' st' o} (hb : SubBound V bound)
    (h : ExecStmt D funs V st (.block b₁) V' st' o) :
    ExecStmt D funs V st (.block b₂) V' st' o := by
  cases h with
  | block hbd => exact Step.block (hh ▸ (hss _ _ _ _ _ _ hb).mp hbd)

/-- Block congruence with an unchanged hoisted scope. -/
theorem BEquivBlock.of_stmts {bound : List Ident} {b₁ b₂ : Block D.Op}
    (hss : BEquivStmts (D := D) bound b₁ b₂) (hh : hoist D b₁ = hoist D b₂) :
    BEquivBlock (D := D) bound b₁ b₂ :=
  fun _ _ _ _ _ _ hb => ⟨bblockImp hss hh hb, bblockImp hss.symm hh.symm hb⟩

/-! #### The function-environment relation

Rewriting inside a `funDef` body changes the `FDecl` a block hoists, so relating
the two programs needs a relation on function environments — the congruence
`YulSemantics.Equiv` defers. This is `FunCongr`'s development with `EquivBlock`
replaced by `BEquivBlock (params ++ rets)`, which is exactly the boundness the
call rule supplies. -/

/-- Declarations with equal signatures and `BEquivBlock (params ++ rets)` bodies. -/
def SbFDeclRel (d₁ d₂ : FDecl D) : Prop :=
  d₁.params = d₂.params ∧ d₁.rets = d₂.rets ∧
    BEquivBlock (D := D) (d₁.params ++ d₁.rets) d₁.body d₂.body

/-- Scopes related pairwise: equal names, related declarations. -/
def SbScopeRel (s₁ s₂ : FScope D) : Prop :=
  List.Forall₂ (fun p q => p.1 = q.1 ∧ SbFDeclRel (D := D) p.2 q.2) s₁ s₂

/-- Function environments related scope-by-scope. -/
def SbFunsRel (f₁ f₂ : FunEnv D) : Prop :=
  List.Forall₂ (SbScopeRel (D := D)) f₁ f₂

theorem SbFDeclRel.refl (d : FDecl D) : SbFDeclRel (D := D) d d :=
  ⟨rfl, rfl, BEquivBlock.refl _ _⟩

theorem SbFDeclRel.symm {d₁ d₂ : FDecl D} (h : SbFDeclRel (D := D) d₁ d₂) :
    SbFDeclRel (D := D) d₂ d₁ :=
  ⟨h.1.symm, h.2.1.symm, by
    have hbq := h.2.2.symm
    rw [h.1, h.2.1] at hbq
    exact hbq⟩

theorem SbScopeRel.refl (s : FScope D) : SbScopeRel (D := D) s s := by
  induction s with
  | nil => exact .nil
  | cons p t ih => exact .cons ⟨rfl, SbFDeclRel.refl _⟩ ih

theorem SbScopeRel.symm {s₁ s₂ : FScope D} (h : SbScopeRel (D := D) s₁ s₂) :
    SbScopeRel (D := D) s₂ s₁ := by
  induction h with
  | nil => exact .nil
  | cons hpq _ ih => exact .cons ⟨hpq.1.symm, hpq.2.symm⟩ ih

theorem SbFunsRel.refl (f : FunEnv D) : SbFunsRel (D := D) f f := by
  induction f with
  | nil => exact .nil
  | cons s t ih => exact .cons (SbScopeRel.refl _) ih

theorem SbFunsRel.symm {f₁ f₂ : FunEnv D} (h : SbFunsRel (D := D) f₁ f₂) :
    SbFunsRel (D := D) f₂ f₁ := by
  induction h with
  | nil => exact .nil
  | cons hs _ ih => exact .cons hs.symm ih

/-- Extend related environments by a common outer scope. -/
theorem SbFunsRel.cons_same (s : FScope D) {f₁ f₂ : FunEnv D} (h : SbFunsRel (D := D) f₁ f₂) :
    SbFunsRel (D := D) (s :: f₁) (s :: f₂) := .cons (SbScopeRel.refl s) h

/-- A scope lookup transports across `SbScopeRel`. -/
theorem sbScopeRel_find {s₁ s₂ : FScope D} (h : SbScopeRel (D := D) s₁ s₂) (fn : Ident) :
    (s₁.find? (fun p => p.1 = fn) = none ∧ s₂.find? (fun p => p.1 = fn) = none) ∨
    (∃ p q, s₁.find? (fun p => p.1 = fn) = some p ∧ s₂.find? (fun p => p.1 = fn) = some q ∧
      p.1 = q.1 ∧ SbFDeclRel (D := D) p.2 q.2) := by
  induction h with
  | nil => left; simp
  | @cons p q u₁ u₂ hpq _ ih =>
      by_cases hp : p.1 = fn
      · right
        refine ⟨p, q, ?_, ?_, hpq.1, hpq.2⟩
        · exact List.find?_cons_of_pos (by simp [hp])
        · exact List.find?_cons_of_pos (by simp [← hpq.1, hp])
      · rw [List.find?_cons_of_neg (by simp [hp]),
            List.find?_cons_of_neg (by simp [← hpq.1, hp])]
        exact ih

/-- `lookupFun` transports across `SbFunsRel`. -/
theorem sbLookupFun {f₁ f₂ : FunEnv D} (hR : SbFunsRel (D := D) f₁ f₂) :
    ∀ {fn : Ident} {decl : FDecl D} {cenv : FunEnv D},
      lookupFun f₁ fn = some (decl, cenv) →
      ∃ decl' cenv', lookupFun f₂ fn = some (decl', cenv') ∧
        decl'.params = decl.params ∧ decl'.rets = decl.rets ∧
        BEquivBlock (D := D) (decl.params ++ decl.rets) decl.body decl'.body ∧
        SbFunsRel (D := D) cenv cenv' := by
  induction hR with
  | nil => intro fn decl cenv h; simp [lookupFun] at h
  | @cons s₁ s₂ t₁ t₂ hs hR' ih =>
      intro fn decl cenv h
      rcases sbScopeRel_find hs fn with ⟨hn₁, hn₂⟩ | ⟨p, q, hp₁, hp₂, hkey, hd⟩
      · rw [lookupFun, hn₁] at h
        obtain ⟨decl', cenv', hl', hpar, hret, hbody, hRc⟩ := ih h
        exact ⟨decl', cenv', by rw [lookupFun, hn₂]; exact hl', hpar, hret, hbody, hRc⟩
      · rw [lookupFun, hp₁] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hd_eq, hcenv_eq⟩ := h
        subst hd_eq; subst hcenv_eq
        exact ⟨q.2, s₂ :: t₂, by rw [lookupFun, hp₂], hd.1.symm, hd.2.1.symm,
          hd.2.2, List.Forall₂.cons hs hR'⟩

omit [DecidableEq D.Value] in
/-- The callee environment binds exactly the callee's parameters and returns. -/
theorem subBound_callee {decl : FDecl D} {argvals : List D.Value}
    (hlen : argvals.length = decl.params.length) :
    SubBound (decl.params.zip argvals ++ bindZeros D decl.rets) (decl.params ++ decl.rets) := by
  intro y hy
  rw [List.map_append, bindZeros_fst, List.map_fst_zip (by omega)]
  exact hy

/-- **Function-environment congruence.** A `Step` derivation transports across an
`SbFunsRel`: running the *same* code under a related function environment yields
the *same* result. -/
theorem Step.sbFunsCongr {funs₁ : FunEnv D} {V st code res}
    (h : Step D funs₁ V st code res) :
    ∀ {funs₂}, SbFunsRel (D := D) funs₁ funs₂ → Step D funs₂ V st code res := by
  induction h with
  | lit => intro _ _; exact Step.lit
  | var hv => intro _ _; exact Step.var hv
  | builtinOk _ hbi iha => intro _ hR; exact Step.builtinOk (iha hR) hbi
  | builtinHalt _ hbi iha => intro _ hR; exact Step.builtinHalt (iha hR) hbi
  | builtinArgsHalt _ iha => intro _ hR; exact Step.builtinArgsHalt (iha hR)
  | @callOk funs V st fn args argvals st1 decl cenv Vend st2 o ha hl hlen hbody ho iha ihbody =>
      intro funs₂ hR
      obtain ⟨decl', cenv', hl', hpar, hret, hbodyEq, hRcenv⟩ := sbLookupFun hR hl
      have hstep : Step D cenv' (decl.params.zip argvals ++ bindZeros D decl.rets) st1
          (.stmt (.block decl.body)) (.sres Vend st2 o) := ihbody hRcenv
      have hstep' : Step D cenv' (decl.params.zip argvals ++ bindZeros D decl.rets) st1
          (.stmt (.block decl'.body)) (.sres Vend st2 o) :=
        (hbodyEq cenv' _ st1 Vend st2 o (subBound_callee hlen)).mp hstep
      have hbody' : Step D cenv' (decl'.params.zip argvals ++ bindZeros D decl'.rets) st1
          (.stmt (.block decl'.body)) (.sres Vend st2 o) := by rw [hpar, hret]; exact hstep'
      have hres := Step.callOk (iha hR) hl' (by rw [hpar]; exact hlen) hbody' ho
      rw [hret] at hres; exact hres
  | @callHalt funs V st fn args argvals st1 decl cenv Vend st2 ha hl hlen hbody iha ihbody =>
      intro funs₂ hR
      obtain ⟨decl', cenv', hl', hpar, hret, hbodyEq, hRcenv⟩ := sbLookupFun hR hl
      have hstep : Step D cenv' (decl.params.zip argvals ++ bindZeros D decl.rets) st1
          (.stmt (.block decl.body)) (.sres Vend st2 .halt) := ihbody hRcenv
      have hstep' : Step D cenv' (decl.params.zip argvals ++ bindZeros D decl.rets) st1
          (.stmt (.block decl'.body)) (.sres Vend st2 .halt) :=
        (hbodyEq cenv' _ st1 Vend st2 .halt (subBound_callee hlen)).mp hstep
      have hbody' : Step D cenv' (decl'.params.zip argvals ++ bindZeros D decl'.rets) st1
          (.stmt (.block decl'.body)) (.sres Vend st2 .halt) := by rw [hpar, hret]; exact hstep'
      exact Step.callHalt (iha hR) hl' (by rw [hpar]; exact hlen) hbody'
  | callArgsHalt _ iha => intro _ hR; exact Step.callArgsHalt (iha hR)
  | argsNil => intro _ _; exact Step.argsNil
  | argsCons _ _ iha ihe => intro _ hR; exact Step.argsCons (iha hR) (ihe hR)
  | argsRestHalt _ iha => intro _ hR; exact Step.argsRestHalt (iha hR)
  | argsHeadHalt _ _ iha ihe => intro _ hR; exact Step.argsHeadHalt (iha hR) (ihe hR)
  | funDef => intro _ _; exact Step.funDef
  | @block funs V st body Vb stb o hbody ihbody =>
      intro funs₂ hR; exact Step.block (ihbody (SbFunsRel.cons_same (hoist D body) hR))
  | letZero => intro _ _; exact Step.letZero
  | letVal _ hlen ihe => intro _ hR; exact Step.letVal (ihe hR) hlen
  | letHalt _ ihe => intro _ hR; exact Step.letHalt (ihe hR)
  | assignVal _ hlen ihe => intro _ hR; exact Step.assignVal (ihe hR) hlen
  | assignHalt _ ihe => intro _ hR; exact Step.assignHalt (ihe hR)
  | exprStmt _ ihe => intro _ hR; exact Step.exprStmt (ihe hR)
  | exprStmtHalt _ ihe => intro _ hR; exact Step.exprStmtHalt (ihe hR)
  | ifTrue _ hnz _ ihc ihb => intro _ hR; exact Step.ifTrue (ihc hR) hnz (ihb hR)
  | ifFalse _ hz ihc => intro _ hR; exact Step.ifFalse (ihc hR) hz
  | ifHalt _ ihc => intro _ hR; exact Step.ifHalt (ihc hR)
  | switchExec _ _ ihc ihb => intro _ hR; exact Step.switchExec (ihc hR) (ihb hR)
  | switchHalt _ ihc => intro _ hR; exact Step.switchHalt (ihc hR)
  | @forLoop funs V st init c post body Vinit stinit Vend stend o hinit hloop ihinit ihloop =>
      intro funs₂ hR
      exact Step.forLoop (ihinit (SbFunsRel.cons_same (hoist D init) hR))
        (ihloop (SbFunsRel.cons_same (hoist D init) hR))
  | @forInitHalt funs V st init c post body Vinit stinit hinit ihinit =>
      intro funs₂ hR
      exact Step.forInitHalt (ihinit (SbFunsRel.cons_same (hoist D init) hR))
  | «break» => intro _ _; exact Step.break
  | «continue» => intro _ _; exact Step.continue
  | leave => intro _ _; exact Step.leave
  | seqNil => intro _ _; exact Step.seqNil
  | seqCons _ _ ihs ihrest => intro _ hR; exact Step.seqCons (ihs hR) (ihrest hR)
  | seqStop _ hne ihs => intro _ hR; exact Step.seqStop (ihs hR) hne
  | loopDone _ hz ihc => intro _ hR; exact Step.loopDone (ihc hR) hz
  | loopCondHalt _ ihc => intro _ hR; exact Step.loopCondHalt (ihc hR)
  | loopStep _ hnz _ hob _ _ ihc ihb ihp ihr =>
      intro _ hR; exact Step.loopStep (ihc hR) hnz (ihb hR) hob (ihp hR) (ihr hR)
  | loopPostHalt _ hnz _ hob _ ihc ihb ihp =>
      intro _ hR; exact Step.loopPostHalt (ihc hR) hnz (ihb hR) hob (ihp hR)
  | loopBreak _ hnz _ ihc ihb => intro _ hR; exact Step.loopBreak (ihc hR) hnz (ihb hR)
  | loopLeave _ hnz _ ihc ihb => intro _ hR; exact Step.loopLeave (ihc hR) hnz (ihb hR)
  | loopBodyHalt _ hnz _ ihc ihb => intro _ hR; exact Step.loopBodyHalt (ihc hR) hnz (ihb hR)

/-- **Block congruence with a changing function scope.** Related statement lists
whose hoisted scopes are `SbScopeRel`-related form related blocks — the
generalization of `BEquivBlock.of_stmts` that permits rewriting inside `funDef`
bodies. -/
theorem BEquivBlock.of_stmts_funs {bound : List Ident} {b₁ b₂ : Block D.Op}
    (hss : BEquivStmts (D := D) bound b₁ b₂)
    (hR : SbScopeRel (D := D) (hoist D b₁) (hoist D b₂)) :
    BEquivBlock (D := D) bound b₁ b₂ := by
  intro funs V st V' st' o hb
  constructor
  · intro h
    cases h with
    | block hbd =>
        refine Step.block ?_
        have h1 := Step.sbFunsCongr hbd (List.Forall₂.cons hR (SbFunsRel.refl funs))
        exact (hss (hoist D b₂ :: funs) V st _ _ _ hb).mp h1
  · intro h
    cases h with
    | block hbd =>
        refine Step.block ?_
        have h1 := Step.sbFunsCongr hbd (List.Forall₂.cons hR.symm (SbFunsRel.refl funs))
        exact (hss (hoist D b₁ :: funs) V st _ _ _ hb).mpr h1

end BoundEquiv

end YulEvmCompiler.Optimizer
