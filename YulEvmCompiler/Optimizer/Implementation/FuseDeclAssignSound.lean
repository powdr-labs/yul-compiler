import YulEvmCompiler.Optimizer.Implementation.FuseDeclAssign
import YulEvmCompiler.Optimizer.Implementation.CoalesceCopies
set_option warningAsError true
/-!
# Soundness of declare-then-assign fusion — the environment-reorder transport

The sink rewrite moves a binding's creation point: after
`let x; mid; x := e  ↝  mid; let x := e`, the suffix executes over

* source: `C ++ A ++ (x, v) :: B` (the binding sits below `mid`'s locals `A`),
* target: `C ++ (x, v) :: A ++ B` (the binding sits on top of them),

with a common newer segment `C` for everything pushed later.  Yul variable
access is name-first (`VEnv.get`/`VEnv.set` find the first occurrence), so as
long as `A` never binds `x`, both environments agree on every read and every
update — the difference is pure stack *placement*, observable only by
`restore`, which either cuts inside `C` (both sides drop the same entries) or
at/below `B` (both sides return the same suffix of `B`).

`MvRel` packages this shape; the `Step` transport (`mv_congr`, below) carries
a derivation across it.
-/

namespace YulEvmCompiler.Optimizer.FuseDeclAssign

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-! ### `VEnv.set` distributes over append by key location -/

theorem set_append_of_found {V W : VEnv D} {y : Ident}
    (h : (V.find? (fun p => p.1 = y)).isSome)
    (w : (evmWithExternal calls creates).Value) :
    VEnv.set (V ++ W) y w = VEnv.set V y w ++ W := by
  induction V with
  | nil => simp at h
  | cons p V' ih =>
      by_cases hp : p.1 = y
      · obtain ⟨p1, p2⟩ := p
        simp only at hp
        subst hp
        simp [VEnv.set]
      · obtain ⟨p1, p2⟩ := p
        simp only at hp
        rw [List.find?_cons_of_neg (by simp [hp])] at h
        simp only [List.cons_append, VEnv.set, if_neg hp]
        rw [ih h]

theorem set_append_of_none {V W : VEnv D} {y : Ident}
    (h : V.find? (fun p => p.1 = y) = none)
    (w : (evmWithExternal calls creates).Value) :
    VEnv.set (V ++ W) y w = V ++ VEnv.set W y w := by
  induction V with
  | nil => simp
  | cons p V' ih =>
      obtain ⟨p1, p2⟩ := p
      by_cases hp : p1 = y
      · rw [List.find?_cons_of_pos (by simp [hp])] at h
        cases h
      · rw [List.find?_cons_of_neg (by simp [hp])] at h
        simp only [List.cons_append, VEnv.set, if_neg hp]
        rw [ih h]

/-- Keys of an environment survive `VEnv.set` (membership form). -/
theorem mem_set_key {V : VEnv D} {y : Ident}
    {w : (evmWithExternal calls creates).Value} {p : Ident × U256}
    (hp : p ∈ VEnv.set V y w) : ∃ q ∈ V, q.1 = p.1 := by
  induction V with
  | nil => cases hp
  | cons q V' ih =>
      obtain ⟨q1, q2⟩ := q
      by_cases hq : q1 = y
      · simp only [VEnv.set, if_pos hq] at hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact ⟨(q1, q2), List.mem_cons_self .., by simp [hq]⟩
        · exact ⟨p, List.mem_cons_of_mem _ hp', rfl⟩
      · simp only [VEnv.set, if_neg hq] at hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact ⟨(q1, q2), List.mem_cons_self .., rfl⟩
        · obtain ⟨r, hr, hre⟩ := ih hp'
          exact ⟨r, List.mem_cons_of_mem _ hr, hre⟩

/-! ### The reorder relation -/

/-- One binding moved from below `A` to above it, under a common newer
segment `C`. `x` must not be bound by `A` (reads reach the moved binding on
both sides); it may be bound by `C` (an identical shadow on both sides). -/
inductive MvRel (x : Ident) : VEnv D → VEnv D → Prop
  | mk (C A B : VEnv D) (v : (evmWithExternal calls creates).Value)
      (hA : ∀ p ∈ A, p.1 ≠ x) :
      MvRel x (C ++ (A ++ (x, v) :: B)) (C ++ ((x, v) :: (A ++ B)))

theorem MvRel.length {x : Ident} {V₁ V₂ : VEnv D} (h : MvRel x V₁ V₂) :
    V₁.length = V₂.length := by
  cases h with
  | mk C A B v hA => simp [List.length_append]; omega

/-- Push a common binding on top. -/
theorem MvRel.push {x : Ident} {V₁ V₂ : VEnv D} (h : MvRel x V₁ V₂)
    (p : Ident × (evmWithExternal calls creates).Value) :
    MvRel x (p :: V₁) (p :: V₂) := by
  cases h with
  | mk C A B v hA => exact MvRel.mk (p :: C) A B v hA

/-- Push a common list of bindings on top. -/
theorem MvRel.pushMany {x : Ident} {V₁ V₂ : VEnv D} (h : MvRel x V₁ V₂)
    (ps : VEnv D) : MvRel x (ps ++ V₁) (ps ++ V₂) := by
  cases h with
  | mk C A B v hA =>
      have := MvRel.mk (calls := calls) (creates := creates)
        (ps ++ C) A B v hA
      simpa [List.append_assoc] using this

/-- Reads agree across the relation. -/
theorem MvRel.get {x : Ident} {V₁ V₂ : VEnv D} (h : MvRel x V₁ V₂)
    (y : Ident) : VEnv.get V₁ y = VEnv.get V₂ y := by
  cases h with
  | mk C A B v hA =>
      unfold VEnv.get
      simp only [List.find?_append]
      cases hC : C.find? (fun p => p.1 = y) with
      | some p => simp
      | none =>
          simp only [Option.none_or]
          by_cases hxy : y = x
          · subst hxy
            have hAn : A.find? (fun p => p.1 = y) = none := by
              rw [List.find?_eq_none]
              intro p hp
              simp [hA p hp]
            rw [hAn,
              List.find?_cons_of_pos (by simp),
              List.find?_cons_of_pos (by simp)]
            simp
          · rw [List.find?_cons_of_neg (by simp; exact fun hc : x = y => hxy hc.symm),
              List.find?_cons_of_neg (by simp; exact fun hc : x = y => hxy hc.symm),
              List.find?_append]

/-- Updates preserve the relation. -/
theorem MvRel.set {x : Ident} {V₁ V₂ : VEnv D} (h : MvRel x V₁ V₂)
    (y : Ident) (w : (evmWithExternal calls creates).Value) :
    MvRel x (VEnv.set V₁ y w) (VEnv.set V₂ y w) := by
  cases h with
  | mk C A B v hA =>
      cases hC : C.find? (fun p => p.1 = y) with
      | some p =>
          rw [set_append_of_found (by simp [hC]) w,
            set_append_of_found (by simp [hC]) w]
          exact MvRel.mk _ A B v hA
      | none =>
          rw [set_append_of_none hC w, set_append_of_none hC w]
          by_cases hxy : y = x
          · subst hxy
            have hAn : A.find? (fun p => p.1 = y) = none := by
              rw [List.find?_eq_none]
              intro p hp
              simp [hA p hp]
            rw [set_append_of_none hAn w]
            have hset1 : VEnv.set ((y, v) :: B) y w = (y, w) :: B := by
              simp [VEnv.set]
            have hset2 : VEnv.set ((y, v) :: (A ++ B)) y w =
                (y, w) :: (A ++ B) := by
              simp [VEnv.set]
            rw [hset1, hset2]
            exact MvRel.mk C A B w hA
          · cases hA' : A.find? (fun p => p.1 = y) with
            | some q =>
                rw [set_append_of_found (by simp [hA']) w,
                  show VEnv.set ((x, v) :: (A ++ B)) y w =
                    (x, v) :: VEnv.set (A ++ B) y w from by
                      simp only [VEnv.set]
                      rw [if_neg (fun hc : x = y => hxy hc.symm)],
                  set_append_of_found (by simp [hA']) w]
                refine MvRel.mk C (VEnv.set A y w) B v ?_
                intro p hp
                obtain ⟨q', hq', hqe⟩ := mem_set_key hp
                rw [← hqe]
                exact hA q' hq'
            | none =>
                rw [set_append_of_none hA' w,
                  show VEnv.set ((x, v) :: (A ++ B)) y w =
                    (x, v) :: VEnv.set (A ++ B) y w from by
                      simp only [VEnv.set]
                      rw [if_neg (fun hc : x = y => hxy hc.symm)],
                  set_append_of_none hA' w,
                  show VEnv.set ((x, v) :: B) y w =
                    (x, v) :: VEnv.set B y w from by
                      simp only [VEnv.set]
                      rw [if_neg (fun hc : x = y => hxy hc.symm)]]
                exact MvRel.mk C A (VEnv.set B y w) v hA

/-- `setMany` preserves the relation. -/
theorem MvRel.setMany {x : Ident} {V₁ V₂ : VEnv D} (h : MvRel x V₁ V₂)
    (ys : List Ident) (ws : List (evmWithExternal calls creates).Value) :
    MvRel x (VEnv.setMany V₁ ys ws) (VEnv.setMany V₂ ys ws) := by
  unfold VEnv.setMany
  induction (ys.zip ws) generalizing V₁ V₂ with
  | nil => exact h
  | cons p rest ih => exact ih (h.set p.1 p.2)

/-! ### `restore` across the relation

`restore outer inner` keeps `inner`'s last `outer.length` entries.  A cut at
or above the moved region (both related environments share the newer segment)
yields related results; a cut at or below the fixed base `B` yields *equal*
results. -/

/-- The workable form: exits whose moved region sits below the entry cut.
`dA`/`dB` name the region lengths; the cut keeps at least the region. -/
theorem restore_mvRel {x : Ident} {Ve₁ Ve₂ : VEnv D}
    {C A B : VEnv D} {v : (evmWithExternal calls creates).Value}
    (hA : ∀ p ∈ A, p.1 ≠ x)
    (hentry_len : A.length + 1 + B.length ≤ Ve₁.length)
    (hlen : Ve₁.length = Ve₂.length)
    (hle₁ : Ve₁.length ≤ (C ++ (A ++ (x, v) :: B)).length) :
    MvRel x (restore Ve₁ (C ++ (A ++ (x, v) :: B)))
      (restore Ve₂ (C ++ ((x, v) :: (A ++ B)))) := by
  unfold restore
  have hlen₂ : (C ++ ((x, v) :: (A ++ B))).length =
      (C ++ (A ++ (x, v) :: B)).length := by
    simp [List.length_append]; omega
  rw [hlen₂, ← hlen]
  -- The drop count stays within `C`.
  have hdrop : (C ++ (A ++ (x, v) :: B)).length - Ve₁.length ≤ C.length := by
    simp only [List.length_append, List.length_cons] at hle₁ ⊢
    omega
  set k := (C ++ (A ++ (x, v) :: B)).length - Ve₁.length with hk
  rw [List.drop_append_of_le_length (by omega),
    List.drop_append_of_le_length (by omega)]
  exact MvRel.mk (C.drop k) A B v hA

/-- Dropping down to the last `n` entries ignores everything above the base. -/
theorem drop_to_base (X B : VEnv D) {n : Nat} (h : n ≤ B.length) :
    List.drop ((X ++ B).length - n) (X ++ B) = List.drop (B.length - n) B := by
  have heq : (X ++ B).length - n = X.length + (B.length - n) := by
    simp [List.length_append]; omega
  rw [heq, List.drop_append]
  rw [List.drop_eq_nil_of_le (Nat.le_add_right ..), List.nil_append]
  congr 1
  omega

/-- Restoring to a base at or below `B` yields equal environments. -/
theorem restore_mv_eq {x : Ident} {V₀ : VEnv D}
    {C A B : VEnv D} {v : (evmWithExternal calls creates).Value}
    (hbase : V₀.length ≤ B.length) :
    restore V₀ (C ++ (A ++ (x, v) :: B)) =
      restore V₀ (C ++ ((x, v) :: (A ++ B))) := by
  unfold restore
  rw [show C ++ (A ++ (x, v) :: B) = (C ++ A ++ [(x, v)]) ++ B from by simp,
    show C ++ ((x, v) :: (A ++ B)) = (C ++ [(x, v)] ++ A) ++ B from by simp,
    drop_to_base _ _ hbase, drop_to_base _ _ hbase]

end YulEvmCompiler.Optimizer.FuseDeclAssign
