import EvmSemantics.Machine.MachineState
import EvmSemantics.Data.Bytes
import YulSemantics.Dialect.EVM

set_option warningAsError true

/-!
# YulEvmCompiler.BytesLemmas

Two `ByteArray` reduction facts about `EvmSemantics.Data.Bytes.natToBytesPadded`
that are needed to verify `MSTORE` (memory writes): its size is exactly `width`,
and its `k`-th byte is the big-endian digit `n / 256^(width-1-k) % 256`. Both are
plain properties of the total `Id.run do`-loop definition, proved here directly
by unfolding the loops into `List.foldl` and characterising the two intermediate
arrays.

The companion read-after-write fact for `writeBytes` lives upstream as
`EvmSemantics.MachineState.writeBytes_getElem?_getD` and is used directly. These
lemmas are candidates to move upstream into `EvmSemantics.Data.Bytes` too (see
`notes/writeBytes-lemmas.md`); until then they live here. They are genuine
theorems, so they do **not** appear in the `#print axioms` footprint (see
`Checks.lean`).
-/

namespace YulEvmCompiler.BytesLemmas

open EvmSemantics

private theorem getD0_eq_getElemBang (c : ByteArray) (i : Nat) :
    (getElem? c i).getD 0 = getElem! c i := by
  rw [getElem!_def]
  cases getElem? c i <;> rfl

private theorem byteArray_mk_getElemBang (a : Array UInt8) (i : Nat) :
    getElem! (ByteArray.mk a) i = getElem! a i := by
  rw [getElem!_def, getElem!_def]
  rfl

private theorem div_div_pow (n b m : Nat) : n / b ^ m / b = n / b ^ (m + 1) := by
  rw [Nat.pow_succ]
  exact Nat.div_div_eq_div_mul n (b ^ m) b

private theorem second_fold_mkEmpty_size (le : Array UInt8) (width m cap : Nat) :
    ((List.range' 0 m).foldl (fun acc i => acc.push le[width - 1 - i]!)
      (Array.mkEmpty cap)).size = m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.range'_concat, List.foldl_append]
      simp only [Nat.one_mul, Nat.zero_add, List.foldl_cons, List.foldl_nil]
      rw [Array.size_push, ih]

private theorem second_fold_mkEmpty_get (le : Array UInt8) (width m cap j : Nat)
    (hj : j < m) :
    ((List.range' 0 m).foldl (fun acc i => acc.push le[width - 1 - i]!)
      (Array.mkEmpty cap))[j]! = le[width - 1 - j]! := by
  induction m with
  | zero => omega
  | succ m ih =>
      rw [List.range'_concat, List.foldl_append]
      simp only [Nat.one_mul, Nat.zero_add, List.foldl_cons, List.foldl_nil]
      by_cases h : j < m
      · rw [getElem!_pos _ j (by rw [Array.size_push, second_fold_mkEmpty_size]; omega)]
        rw [Array.getElem_push_lt (by rw [second_fold_mkEmpty_size]; exact h)]
        rw [← getElem!_pos _ j (by rw [second_fold_mkEmpty_size]; exact h)]
        exact ih h
      · have hjm : j = m := by omega
        subst j
        rw [getElem!_pos _ m (by rw [Array.size_push, second_fold_mkEmpty_size]; omega)]
        simp

private theorem first_fold_mprod_props (n m cap : Nat) :
    let s := (List.range' 0 m).foldl
      (fun (b : MProd Nat (Array UInt8)) (_a : Nat) =>
        ⟨b.fst / 256, b.snd.push (UInt8.ofNat (b.fst % 256))⟩)
      (⟨n, Array.mkEmpty cap⟩ : MProd Nat (Array UInt8))
    s.snd.size = m ∧ s.fst = n / 256 ^ m ∧
      ∀ j, j < m → s.snd[j]! = UInt8.ofNat (n / 256 ^ j % 256) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.range'_concat, List.foldl_append]
      simp only [Nat.one_mul, Nat.zero_add, List.foldl_cons, List.foldl_nil]
      rcases ih with ⟨hsz, hk, hget⟩
      constructor
      · rw [Array.size_push, hsz]
      constructor
      · rw [hk, div_div_pow]
      · intro j hj
        by_cases h : j < m
        · rw [getElem!_pos _ j (by rw [Array.size_push, hsz]; omega)]
          rw [Array.getElem_push_lt (by rw [hsz]; exact h)]
          rw [← getElem!_pos _ j (by rw [hsz]; exact h)]
          exact hget j h
        · have hjm : j = m := by omega
          subst j
          rw [getElem!_pos _ m (by rw [Array.size_push, hsz]; omega)]
          rw [hk]
          have hsz' : (List.foldl
              (fun (b : MProd Nat (Array UInt8)) (_a : Nat) =>
                ⟨b.fst / 256, b.snd.push (UInt8.ofNat (b.fst % 256))⟩)
              (⟨n, #[]⟩ : MProd Nat (Array UInt8)) (List.range' 0 m)).snd.size = m := by
            simpa using hsz
          have hpush := Array.getElem_push_eq
            (xs := (List.foldl
              (fun (b : MProd Nat (Array UInt8)) (_a : Nat) =>
                ⟨b.fst / 256, b.snd.push (UInt8.ofNat (b.fst % 256))⟩)
              (⟨n, #[]⟩ : MProd Nat (Array UInt8)) (List.range' 0 m)).snd)
            (x := UInt8.ofNat (n / 256 ^ m % 256))
          simpa [hsz'] using hpush

/-- `natToBytesPadded n width` has exactly `width` bytes. -/
theorem natToBytesPadded_size (n width : Nat) :
    (EvmSemantics.Data.Bytes.natToBytesPadded n width).size = width := by
  unfold EvmSemantics.Data.Bytes.natToBytesPadded
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    pure_bind, List.forIn_pure_yield_eq_foldl, Id.run_pure]
  dsimp only [ByteArray.size]
  simp

/-- Big-endian indexing of `natToBytesPadded`. -/
theorem natToBytesPadded_getElem?_getD (n width k : Nat) (h : k < width) :
    (EvmSemantics.Data.Bytes.natToBytesPadded n width)[k]?.getD 0
      = UInt8.ofNat (n / 256 ^ (width - 1 - k) % 256) := by
  rw [getD0_eq_getElemBang]
  unfold EvmSemantics.Data.Bytes.natToBytesPadded
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    pure_bind, List.forIn_pure_yield_eq_foldl, Id.run_pure]
  rw [byteArray_mk_getElemBang]
  rw [second_fold_mkEmpty_get _ _ _ _ _ h]
  have hidx : width - 1 - k < width := by omega
  rw [(first_fold_mprod_props n width width).2.2 (width - 1 - k) hidx]

end YulEvmCompiler.BytesLemmas
