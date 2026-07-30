import Std.Data.HashSet.Lemmas
set_option warningAsError true
/-!
# Fast executable checks

Proof-facing propositions can have correct but unexpectedly expensive default
decision procedures.  This module provides equivalent executable checks for
hot compiler paths while keeping theorem statements in their natural form.
-/

namespace YulEvmCompiler.Optimizer

/-- Hash-based executable `Nodup`.  For long lists of string-bearing values,
the standard list decision procedure performs a quadratic sequence of equality
checks. -/
def nodupFast {α : Type} [BEq α] [Hashable α] (xs : List α) : Bool :=
  (Std.HashSet.ofList xs).size == xs.length

private theorem hashSet_ofList_cons_size {α : Type} [BEq α] [Hashable α]
    [LawfulBEq α] [LawfulHashable α] (a : α) (xs : List α) :
    (Std.HashSet.ofList (a :: xs)).size =
      ((Std.HashSet.ofList xs).insert a).size := by
  apply Std.HashSet.Equiv.size_eq
  apply Std.HashSet.Equiv.of_forall_contains_eq
  intro x
  simp
  rw [BEq.comm]

private theorem hashSet_ofList_size_eq_length_iff {α : Type}
    [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] [DecidableEq α]
    (xs : List α) :
    (Std.HashSet.ofList xs).size = xs.length ↔ xs.Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      rw [hashSet_ofList_cons_size, Std.HashSet.size_insert]
      by_cases ha : a ∈ Std.HashSet.ofList xs
      · have hmem : a ∈ xs := by
          simpa [Std.HashSet.mem_iff_contains] using ha
        have hle := Std.HashSet.size_ofList_le (l := xs)
        simp [ha, hmem]
        omega
      · have hmem : a ∉ xs := by
          simpa [Std.HashSet.mem_iff_contains] using ha
        simp [ha, hmem, ih]

@[simp] theorem nodupFast_eq_decide {α : Type} [BEq α] [Hashable α]
    [LawfulBEq α] [LawfulHashable α] [DecidableEq α] (xs : List α) :
    nodupFast xs = decide xs.Nodup := by
  rw [Bool.eq_iff_iff]
  simpa [nodupFast] using hashSet_ofList_size_eq_length_iff xs

end YulEvmCompiler.Optimizer
