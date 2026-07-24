import YulEvmCompiler.Optimizer.Implementation.Normalization.RenameNumeric
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Subperm
set_option warningAsError true
/-!
# Fresh-name foundation for `RenameNumeric`

Sorry-free proofs of the two "leaf" facts the `RenameNumeric` soundness effort
builds on (Milestone 1 of `RenameNumericSound.lean`):

* `natToString_inj` / `freshCand_inj` — decimal `toString : Nat → String` is
  injective, hence so is the candidate map `k ↦ base ++ "_" ++ toString k`;
* `freshName_not_mem` — the bounded search `freshName avoid base` always
  returns a name **outside** `avoid`: with fuel `avoid.length + 1` the search
  window contains `avoid.length + 2` pairwise-distinct candidates, which cannot
  all be members of `avoid` (pigeonhole via `Nodup`/`Subperm` cardinality).

The `toString` injectivity goes through the bridge `toDigitsCore_eq_digits`
relating core's fuel-based printer `Nat.toDigitsCore` to Mathlib's
`Nat.digits`, plus injectivity of `Nat.digitChar` on digits `< 10` (a finite
check) and `Nat.ofDigits_digits`.
-/

namespace YulEvmCompiler.Optimizer.RenameNumeric

open YulSemantics

/-! ### Decimal `toString` is injective on `Nat` -/

/-- Bridge from core's fuel-based digit printer to Mathlib's `Nat.digits`:
given enough fuel, `Nat.toDigitsCore 10 fuel n ds` prepends the (big-endian)
decimal digit characters of `n ≠ 0` onto `ds`. -/
private theorem toDigitsCore_eq_digits :
    ∀ fuel (n : Nat) (ds : List Char), n ≠ 0 → n ≤ fuel →
      Nat.toDigitsCore 10 fuel n ds
        = ((Nat.digits 10 n).map Nat.digitChar).reverse ++ ds := by
  intro fuel
  induction fuel with
  | zero => intro n ds hn hle; omega
  | succ fuel ih =>
    intro n ds hn hle
    have h10 : (1 : ℕ) < 10 := by omega
    simp only [Nat.toDigitsCore]
    rw [Nat.digits_def' h10 (Nat.pos_of_ne_zero hn)]
    by_cases h0 : n / 10 = 0
    · rw [if_pos h0, h0]
      simp
    · rw [if_neg h0]
      have hdiv : n / 10 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) h10
      rw [ih (n / 10) (Nat.digitChar (n % 10) :: ds) h0 (by omega)]
      simp

/-- `Nat.toDigits 10 n` is exactly the reversed `digitChar` image of
`Nat.digits 10 n`, for `n ≠ 0`. -/
private theorem toDigits_eq_digits {n : Nat} (hn : n ≠ 0) :
    Nat.toDigits 10 n = ((Nat.digits 10 n).map Nat.digitChar).reverse := by
  simpa [Nat.toDigits] using toDigitsCore_eq_digits (n + 1) n [] hn (Nat.le_succ n)

/-- `Nat.digitChar` is injective on digits below `10` (finite check). -/
private theorem digitChar_inj_lt :
    ∀ a < 10, ∀ b < 10, Nat.digitChar a = Nat.digitChar b → a = b := by decide

/-- `List.map Nat.digitChar` is injective on lists of digits below `10`. -/
private theorem map_digitChar_inj :
    ∀ {l₁ l₂ : List Nat}, (∀ a ∈ l₁, a < 10) → (∀ a ∈ l₂, a < 10) →
      l₁.map Nat.digitChar = l₂.map Nat.digitChar → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: l₁, b :: l₂, h₁, h₂, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      have hab : a = b :=
        digitChar_inj_lt a (h₁ a List.mem_cons_self) b (h₂ b List.mem_cons_self) h.1
      have hl : l₁ = l₂ :=
        map_digitChar_inj (fun x hx => h₁ x (List.mem_cons_of_mem a hx))
          (fun x hx => h₂ x (List.mem_cons_of_mem b hx)) h.2
      rw [hab, hl]

/-- If `n` prints (as a digit list) like `0` does, then `n = 0`. -/
private theorem eq_zero_of_toDigits_eq {n : Nat} (h : Nat.toDigits 10 n = ['0']) :
    n = 0 := by
  by_contra hn
  rw [toDigits_eq_digits hn,
    Nat.digits_def' (by omega : (1 : ℕ) < 10) (Nat.pos_of_ne_zero hn)] at h
  simp only [List.map_cons, List.reverse_cons] at h
  -- A reversed cons ends in its head: the tail's image must be empty …
  have htail : (Nat.digits 10 (n / 10)).map Nat.digitChar = [] := by
    have hlen := congrArg List.length h
    simp at hlen
    exact List.eq_nil_of_length_eq_zero (by simpa using hlen)
  rw [htail] at h
  simp only [List.reverse_nil, List.nil_append, List.cons.injEq] at h
  -- … and the head digit must be `0`, so `n % 10 = 0` and `n / 10 = 0`.
  have hmod : n % 10 = 0 :=
    digitChar_inj_lt (n % 10) (Nat.mod_lt n (by omega)) 0 (by omega) h.1
  have hdivnil : Nat.digits 10 (n / 10) = [] := by
    simpa using congrArg List.length htail
  have hdiv : n / 10 = 0 := Nat.digits_eq_nil_iff_eq_zero.mp hdivnil
  omega

/-- **Decimal `toString` is injective on `Nat`.** Distinct naturals never print
to the same string. -/
theorem natToString_inj {i j : Nat} (h : toString i = toString j) : i = j := by
  -- `toString (n : Nat)` is definitionally `String.ofList (Nat.toDigits 10 n)`.
  have h' : String.ofList (Nat.toDigits 10 i) = String.ofList (Nat.toDigits 10 j) := h
  have hd : Nat.toDigits 10 i = Nat.toDigits 10 j := String.ofList_injective h'
  by_cases hi : i = 0
  · subst hi
    exact (eq_zero_of_toDigits_eq (hd.symm.trans (by decide))).symm
  · by_cases hj : j = 0
    · subst hj
      exact absurd (eq_zero_of_toDigits_eq (hd.trans (by decide))) hi
    · rw [toDigits_eq_digits hi, toDigits_eq_digits hj, List.reverse_inj] at hd
      have hdig : Nat.digits 10 i = Nat.digits 10 j :=
        map_digitChar_inj
          (fun a ha => Nat.digits_lt_base (by omega) ha)
          (fun a ha => Nat.digits_lt_base (by omega) ha) hd
      calc i = Nat.ofDigits 10 (Nat.digits 10 i) := (Nat.ofDigits_digits 10 i).symm
        _ = Nat.ofDigits 10 (Nat.digits 10 j) := by rw [hdig]
        _ = j := Nat.ofDigits_digits 10 j

/-! ### The fresh-name candidates are pairwise distinct -/

/-- The numeric-suffix candidates are injective in the index: cancel the common
prefix `base ++ "_"` (note `++` is left-associated) and apply `toString`
injectivity. -/
theorem freshCand_inj {base : Ident} {i j : Nat}
    (h : base ++ "_" ++ toString i = base ++ "_" ++ toString j) : i = j :=
  natToString_inj ((String.append_right_inj (base ++ "_")).mp h)

/-! ### The bounded search always finds a free name -/

/-- If the bounded search *fails* (returns a member of `avoid`), then **every**
candidate in its window `[k, k + fuel]` is a member of `avoid`. -/
private theorem freshAux_spec {base : Ident} {avoid : List Ident} :
    ∀ fuel k, freshAux base avoid fuel k ∈ avoid →
      ∀ m, k ≤ m → m ≤ k + fuel → base ++ "_" ++ toString m ∈ avoid := by
  intro fuel
  induction fuel with
  | zero =>
    intro k hmem m hkm hmk
    have hm : m = k := by omega
    subst hm
    simpa [freshAux] using hmem
  | succ fuel ih =>
    intro k hmem m hkm hmk
    simp only [freshAux] at hmem
    by_cases hc : base ++ "_" ++ toString k ∈ avoid
    · rw [if_pos hc] at hmem
      rcases Nat.eq_or_lt_of_le hkm with rfl | hlt
      · exact hc
      · exact ih (k + 1) hmem m hlt (by omega)
    · rw [if_neg hc] at hmem
      exact absurd hmem hc

/-- **A generated fresh name is not in the avoidance set.** If the search
failed, all `avoid.length + 2` candidates `base_1 … base_(avoid.length + 2)`
would be members of `avoid`; they are pairwise distinct (`freshCand_inj`), so
that `Nodup` candidate list would be a subset of `avoid` longer than `avoid` —
impossible. -/
theorem freshName_not_mem (avoid : List Ident) (base : Ident) :
    freshName avoid base ∉ avoid := by
  intro hmem
  -- Every candidate in the search window `[1, avoid.length + 2]` is in `avoid`.
  have hall := freshAux_spec (avoid.length + 1) 1 hmem
  -- The candidate list is `Nodup` (injectivity), longer than `avoid`, yet ⊆ `avoid`.
  have hinj : Function.Injective (fun m : Nat => base ++ "_" ++ toString m) :=
    fun _ _ hc => freshCand_inj hc
  have hnodup :
      ((List.range' 1 (avoid.length + 2)).map
        (fun m => base ++ "_" ++ toString m)).Nodup :=
    List.Nodup.map hinj (List.nodup_range' (s := 1) (n := avoid.length + 2))
  have hsub :
      ((List.range' 1 (avoid.length + 2)).map
        (fun m => base ++ "_" ++ toString m)) ⊆ avoid := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    rw [List.mem_range'_1] at hm
    exact hall m hm.1 (by omega)
  have hle := (hnodup.subperm hsub).length_le
  simp only [List.length_map, List.length_range'] at hle
  omega

end YulEvmCompiler.Optimizer.RenameNumeric
