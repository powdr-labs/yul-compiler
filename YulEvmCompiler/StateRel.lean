import YulEvmCompiler.Decode
import YulEvmCompiler.Value
import YulEvmCompiler.BytesLemmas
import EvmSemantics.EVM.BigStep

/-!
# YulEvmCompiler.StateRel

The correspondence between the two machine states:

* `MemMatch`   — yul-semantics' total `Nat → UInt8` memory vs. evm-semantics'
  `ByteArray` with zero-padded reads;
* `StateMatch` — memory contents and active size, calldata/code/returndata,
  environment data (including the hash-oracle agreement), account balances
  and external code, (transient) storage, emitted logs, and scheduled
  destructions;
* `FrameOK`    — the frame-level side conditions that hold throughout a
  straight-line execution (fixed code, Osaka fork, mutation permitted, not a
  precompile frame, no suspended callers, still running);
* `HaltMatch`  — how a yul-semantics halt payload shows up in the target
  state's `halt`/`hReturn`.

The memory representation lemmas cover word reads, writes, overlapping copies,
zero-padded copies from immutable byte regions, and active-memory expansion.
-/

namespace YulEvmCompiler

open EvmSemantics
open EvmSemantics.EVM

/-- The Yul-side memory (a total function, default `0`) agrees with the
target's `ByteArray` memory under zero-padded reads. -/
def MemMatch (ymem : Nat → UInt8) (m : ByteArray) : Prop :=
  ∀ a : Nat, ymem a = if h : a < m.size then m[a] else 0

/-- The all-zero memory matches the empty byte array (initial states). -/
theorem MemMatch.init : MemMatch (fun _ => 0) ByteArray.empty := by
  intro a
  rw [dif_neg (by rw [ByteArray.size_empty]; omega)]

/-- `mkCode` round-trips a `ByteArray` through its byte list. -/
theorem mkCode_toList (b : ByteArray) : mkCode b.toList = b := by
  rw [ByteArray.toList_eq_data]
  show ByteArray.mk b.data.toList.toArray = b
  rw [Array.toArray_toList]

/-- A concrete source-side oracle obtained from the target semantics' Keccak
primitive. This is used by executable differential tests; the correctness
theorem itself only requires the pointwise agreement recorded in `EnvMatch`. -/
def targetKeccakOracle (bytes : List UInt8) : YulSemantics.EVM.U256 :=
  BitVec.ofNat 256 (EvmSemantics.keccak256 (mkCode bytes)).toNat

theorem targetKeccakOracle_agrees (bytes : List UInt8) :
    conv (targetKeccakOracle bytes) = EvmSemantics.keccak256 (mkCode bytes) := by
  apply u256ext
  rw [conv_toNat, targetKeccakOracle, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (EvmSemantics.keccak256 (mkCode bytes)).val.isLt

/-! ### `RETURN`/`REVERT` payload agreement -/

/-- `MachineState.readPadded`, characterized pointwise against a matching
functional memory. -/
private theorem nat_min_eq (a b : Nat) : Nat.min a b = min a b := rfl

theorem MemMatch.readBytes {ymem : Nat → UInt8} {m : ByteArray}
    (h : MemMatch ymem m) (p n : Nat) :
    YulSemantics.EVM.readBytes ymem p n = (MachineState.readPadded m p n).toList := by
  unfold YulSemantics.EVM.readBytes MachineState.readPadded
  dsimp only
  rw [ByteArray.toList_eq_data, ByteArray.data_append, ByteArray.data_extract]
  rw [Array.toList_append, Array.toList_extract, List.extract_eq_take_drop]
  rw [show (ByteArray.mk (Array.replicate (n - min (m.size - min p m.size) n) 0)).data
      = Array.replicate (n - min (m.size - min p m.size) n) 0 from rfl]
  rw [Array.toList_replicate]
  simp only [nat_min_eq]
  have hlenm : m.data.toList.length = m.size := by
    rw [Array.length_toList]; rfl
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map]
  by_cases hin : i < n
  · rw [show (List.range n)[i]? = some i from by
      rw [List.getElem?_eq_getElem (by simpa using hin)]
      simp]
    show some (ymem (p + i)) = _
    rw [h (p + i)]
    by_cases hpS : p ≤ m.size
    · have hsp : min p m.size = p := min_eq_left hpS
      rw [hsp]
      by_cases hcase : i < min (m.size - p) n
      · -- inside the copied prefix
        rw [List.getElem?_append_left (by
          simp only [List.length_take, List.length_drop, hlenm]
          omega)]
        rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop]
        rw [Array.getElem?_toList]
        rw [Array.getElem?_eq_getElem (show p + i < m.data.size from by
          have : m.data.size = m.size := rfl
          omega)]
        rw [dif_pos (show p + i < m.size from by omega)]
        rfl
      · -- inside the zero padding
        rw [List.getElem?_append_right (by
          simp only [List.length_take, List.length_drop, hlenm]
          omega)]
        rw [List.getElem?_replicate]
        rw [if_pos (by
          simp only [List.length_take, List.length_drop, hlenm]
          omega)]
        rw [dif_neg (show ¬ p + i < m.size from by omega)]
    · -- read entirely past the end of memory
      have hsp : min p m.size = m.size := min_eq_right (by omega)
      rw [hsp]
      rw [List.getElem?_append_right (by
        simp only [List.length_take, List.length_drop, hlenm]
        omega)]
      rw [List.getElem?_replicate]
      rw [if_pos (by
        simp only [List.length_take, List.length_drop, hlenm]
        omega)]
      rw [dif_neg (show ¬ p + i < m.size from by omega)]
  · rw [show (List.range n)[i]? = none from
      (List.getElem?_eq_none_iff).mpr (by simpa using hin)]
    show none = _
    rw [(List.getElem?_eq_none_iff).mpr (by
      simp only [List.length_append, List.length_take, List.length_drop,
        List.length_replicate, hlenm]
      omega)]

/-- A finite source byte list whose zero-padded view matches a target byte array of the same
length is exactly that array. -/
theorem MemMatch.mkCode_eq {bytes : List UInt8} {code : ByteArray}
    (h : MemMatch (YulSemantics.EVM.byteFrom bytes) code)
    (hlen : bytes.length = code.size) : mkCode bytes = code := by
  rw [← mkCode_toList code]
  congr 1
  apply List.ext_getElem
  · simpa [ByteArray.toList_eq_data] using hlen
  · intro i hi hti
    have hci : i < code.size := by
      simpa [ByteArray.toList_eq_data] using hti
    have hm := h i
    rw [dif_pos hci] at hm
    convert hm using 1 <;>
      simp [YulSemantics.EVM.byteFrom, List.getD, hi,
        ByteArray.toList_eq_data, ByteArray.getElem_eq_getElem_data]
    all_goals
      apply congrArg (fun proof => code.data[i]'proof)
      apply Subsingleton.elim

/-! ### `MLOAD` agreement -/

private theorem natFold_lt (l : List UInt8) :
    ∀ acc k, acc < 256 ^ k →
      l.foldl (fun acc b => acc * 256 + b.toNat) acc < 256 ^ (k + l.length) := by
  induction l with
  | nil => intro acc k h; simpa using h
  | cons b l ih =>
    intro acc k h
    have hb : b.toNat < 256 := b.toNat_lt
    have hstep : acc * 256 + b.toNat < 256 ^ (k + 1) := by
      have : acc * 256 + b.toNat < (acc + 1) * 256 := by omega
      calc acc * 256 + b.toNat < (acc + 1) * 256 := this
        _ ≤ 256 ^ k * 256 := by
          have : acc + 1 ≤ 256 ^ k := h
          exact Nat.mul_le_mul_right _ this
        _ = 256 ^ (k + 1) := (Nat.pow_succ ..).symm
    have := ih (acc * 256 + b.toNat) (k + 1) hstep
    simpa [Nat.add_assoc, Nat.add_comm 1 l.length] using this

private theorem bitvec_fold_eq (l : List UInt8) :
    ∀ acc : BitVec 256, l.length ≤ 32 → acc.toNat < 256 ^ (32 - l.length) →
      (l.foldl (fun (acc : BitVec 256) b =>
          (acc <<< (8 : Nat)) ||| BitVec.ofNat 256 b.toNat) acc).toNat
        = l.foldl (fun (acc : Nat) b => acc * 256 + b.toNat) acc.toNat := by
  induction l with
  | nil => intro acc _ _; rfl
  | cons b l ih =>
    intro acc hlen hacc
    simp only [List.length_cons] at hlen hacc
    have hb : b.toNat < 256 := b.toNat_lt
    have hpowle : 256 ^ (32 - (l.length + 1)) * 256 ≤ 256 ^ (32 - l.length) := by
      rw [← Nat.pow_succ]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hpow : (256 : Nat) ^ (32 - l.length) ≤ 256 ^ 32 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h32 : (256 : Nat) ^ 32 = 2 ^ 256 := by
      have h8 : (256 : Nat) = 2 ^ 8 := by norm_num
      calc (256 : Nat) ^ 32 = (2 ^ 8) ^ 32 := by rw [h8]
        _ = 2 ^ (8 * 32) := (Nat.pow_mul 2 8 32).symm
        _ = 2 ^ 256 := by norm_num
    have hmul_lt : acc.toNat * 256 + b.toNat < 2 ^ 256 := by
      have h1 : acc.toNat * 256 + b.toNat < (acc.toNat + 1) * 256 := by omega
      have h2 : (acc.toNat + 1) * 256 ≤ 256 ^ (32 - (l.length + 1)) * 256 :=
        Nat.mul_le_mul_right 256 hacc
      omega
    have hstep : ((acc <<< (8 : Nat)) ||| BitVec.ofNat 256 b.toNat).toNat
        = acc.toNat * 256 + b.toNat := by
      have h256 : acc.toNat * 2 ^ 8 = acc.toNat * 256 := by norm_num
      rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
      rw [Nat.shiftLeft_eq]
      rw [Nat.mod_eq_of_lt (show b.toNat < 2 ^ 256 from by omega)]
      rw [Nat.mod_eq_of_lt (show acc.toNat * 2 ^ 8 < 2 ^ 256 from by
        rw [h256]
        exact lt_of_le_of_lt (Nat.le_add_right _ _) hmul_lt)]
      rw [h256, Nat.mul_comm acc.toNat 256]
      -- disjoint bits: the low 8 bits of `256 * acc` are zero
      show 2 ^ 8 * acc.toNat ||| b.toNat = 2 ^ 8 * acc.toNat + b.toNat
      exact (Nat.two_pow_add_eq_or_of_lt (show b.toNat < 2 ^ 8 from by omega)
        acc.toNat).symm
    show (l.foldl _ ((acc <<< (8 : Nat)) ||| BitVec.ofNat 256 b.toNat)).toNat = _
    rw [ih _ (by omega) (by
      rw [hstep]
      have h1 : acc.toNat * 256 + b.toNat < (acc.toNat + 1) * 256 := by omega
      have h2 : (acc.toNat + 1) * 256 ≤ 256 ^ (32 - (l.length + 1)) * 256 :=
        Nat.mul_le_mul_right 256 hacc
      omega)]
    rw [hstep, List.foldl_cons]

/-- `MLOAD` agreement: loading a word from matching memories gives the same
value (up to `conv`). -/
theorem MemMatch.loadWord {ymem : Nat → UInt8} {m : ByteArray}
    (h : MemMatch ymem m) (p : Nat) :
    conv (YulSemantics.EVM.loadWord ymem p) = MachineState.readWord m p := by
  apply u256ext
  have hlen : (YulSemantics.EVM.readBytes ymem p 32).length = 32 := by
    unfold YulSemantics.EVM.readBytes
    simp
  have hlhs : YulSemantics.EVM.loadWord ymem p
      = (YulSemantics.EVM.readBytes ymem p 32).foldl
          (fun (acc : BitVec 256) b => (acc <<< (8 : Nat)) ||| BitVec.ofNat 256 b.toNat)
          0 := by
    unfold YulSemantics.EVM.loadWord YulSemantics.EVM.readBytes
    rw [List.foldl_map]
  rw [conv_toNat, hlhs]
  rw [bitvec_fold_eq _ 0 (le_of_eq hlen) (by rw [hlen]; decide)]
  unfold MachineState.readWord Data.Bytes.bytesToBigEndianNat
  rw [toNat_u256_ofNat, ← h.readBytes p 32]
  have hlt := natFold_lt (YulSemantics.EVM.readBytes ymem p 32) 0 0 (by omega)
  rw [hlen] at hlt
  have h32 : (256 : Nat) ^ (0 + 32) = 2 ^ 256 := by
    have h8 : (256 : Nat) = 2 ^ 8 := by norm_num
    calc (256 : Nat) ^ (0 + 32) = (2 ^ 8) ^ 32 := by rw [h8]
    _ = 2 ^ (8 * 32) := (Nat.pow_mul 2 8 32).symm
    _ = 2 ^ 256 := by norm_num
  rw [Nat.mod_eq_of_lt (by rw [h32] at hlt; exact hlt)]
  rfl

/-- Zero-padded read as the `dite` form of `MemMatch`. -/
theorem getD_eq_dite (m : ByteArray) (a : Nat) :
    m[a]?.getD 0 = if h : a < m.size then m[a] else 0 := by
  rw [getElem?_def]; split <;> rfl

/-- Yul's big-endian byte extractor as a divide-mod on the underlying `Nat`. -/
theorem byteAt_eq (v : YulSemantics.EVM.U256) (j : Nat) :
    YulSemantics.EVM.byteAt v j = UInt8.ofNat (v.toNat / 256 ^ j % 256) := by
  unfold YulSemantics.EVM.byteAt
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ (8 * j) = 256 ^ j from by rw [pow_mul]; norm_num,
    UInt8.ofNat_mod_size']

/-- `MSTORE` agreement: writing a word big-endian into matching memories keeps
them matching. Yul's `storeWord` sets the 32-byte window `[p, p+32)` from the
value's big-endian bytes; the target's `writeBytes` of `natToBytesPadded` does
the same, and the two byte encoders agree (`byteAt_eq` vs.
`natToBytesPadded_getElem?_getD`). Outside the window both read the old
memory. -/
theorem MemMatch.storeWord {ymem : Nat → UInt8} {m : ByteArray}
    (h : MemMatch ymem m) (p : Nat) (v : YulSemantics.EVM.U256) :
    MemMatch (YulSemantics.EVM.storeWord ymem p v)
      (MachineState.writeBytes m
        (Data.Bytes.natToBytesPadded (conv v).toNat 32) p) := by
  intro a
  rw [← getD_eq_dite, MachineState.writeBytes_getElem?_getD,
    BytesLemmas.natToBytesPadded_size]
  simp only [YulSemantics.EVM.storeWord]
  by_cases hw : p ≤ a ∧ a < p + 32
  · rw [if_pos hw, if_pos hw]
    have hk : a - p < 32 := by omega
    rw [BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hk, byteAt_eq, conv_toNat]
  · rw [if_neg hw, if_neg hw, getD_eq_dite]
    exact h a

/-- `MSTORE8` agreement: writing the least-significant byte at `p` keeps the
functional Yul memory and the target `ByteArray` memory matching. -/
theorem MemMatch.storeByte {ymem : Nat → UInt8} {m : ByteArray}
    (h : MemMatch ymem m) (p : Nat) (v : YulSemantics.EVM.U256) :
    MemMatch (YulSemantics.EVM.storeByte ymem p v)
      (MachineState.writeBytes m
        (ByteArray.mk #[UInt8.ofNat ((conv v).toNat % 256)]) p) := by
  have hsize : (ByteArray.mk #[UInt8.ofNat ((conv v).toNat % 256)]).size = 1 := rfl
  intro a
  rw [← getD_eq_dite, MachineState.writeBytes_getElem?_getD, hsize]
  simp only [YulSemantics.EVM.storeByte]
  by_cases hw : a = p
  · subst a
    rw [if_pos rfl, if_pos (by omega)]
    simp [getElem?_def, byteAt_eq, conv_toNat]
    rw [dif_pos (by simp [ByteArray.size])]
    rfl
  · have hwindow : ¬ (p ≤ a ∧ a < p + 1) := by omega
    rw [if_neg hw, if_neg hwindow, getD_eq_dite]
    exact h a

/-- `MCOPY` agreement: reading the source range before writing the destination
matches Yul's intermediate-buffer `copyWithin`, including overlapping ranges
and zero padding past the previous end of memory. -/
theorem MemMatch.copyWithin {ymem : Nat → UInt8} {m : ByteArray}
    (hmem : MemMatch ymem m) (dst src n : Nat) :
    MemMatch (YulSemantics.EVM.copyWithin ymem dst src n)
      (MachineState.writeBytes m (MachineState.readPadded m src n) dst) := by
  have hrb := hmem.readBytes src n
  have hsz : (MachineState.readPadded m src n).size = n := by
    have h := congrArg List.length hrb
    simp only [YulSemantics.EVM.readBytes, List.length_map, List.length_range,
      ByteArray.toList_eq_data, Array.length_toList] at h
    exact h.symm
  intro a
  rw [← getD_eq_dite, MachineState.writeBytes_getElem?_getD, hsz]
  simp only [YulSemantics.EVM.copyWithin]
  by_cases hw : dst ≤ a ∧ a < dst + n
  · have hk : a - dst < (List.range n).length := by simp; omega
    rw [if_pos hw, if_pos hw,
      show (MachineState.readPadded m src n)[a - dst]? =
          (MachineState.readPadded m src n).toList[a - dst]? from by
        rw [ByteArray.toList_eq_data, Array.getElem?_toList]; rfl,
      ← hrb]
    simp only [YulSemantics.EVM.readBytes, List.getElem?_map,
      List.getElem?_eq_getElem hk, List.getElem_range, Option.map_some,
      Option.getD_some]
  · rw [if_neg hw, if_neg hw, getD_eq_dite]
    exact hmem a

/-- Copying `n` bytes from an immutable byte region to memory
(`calldatacopy`/`codecopy`/`datacopy`): Yul's `copyInto` matches the target's
`writeBytes … (readPadded data …)`, using the region's pointwise agreement.
Inside the copied window both read the same zero-padded byte; outside, both
leave memory unchanged. -/
theorem MemMatch.copyFromBytes {ymem : Nat → UInt8} {m : ByteArray}
    {ydata : List UInt8} {mdata : ByteArray}
    (hmem : MemMatch ymem m)
    (hdata : MemMatch (YulSemantics.EVM.byteFrom ydata) mdata)
    (dst src n : Nat) :
    MemMatch (YulSemantics.EVM.copyInto ymem dst src n ydata)
      (MachineState.writeBytes m (MachineState.readPadded mdata src n) dst) := by
  have hrb := hdata.readBytes src n
  have hsz : (MachineState.readPadded mdata src n).size = n := by
    have h := congrArg List.length hrb
    simp only [YulSemantics.EVM.readBytes, List.length_map, List.length_range,
      ByteArray.toList_eq_data, Array.length_toList] at h
    exact h.symm
  intro a
  rw [← getD_eq_dite, MachineState.writeBytes_getElem?_getD, hsz]
  simp only [YulSemantics.EVM.copyInto]
  by_cases hw : dst ≤ a ∧ a < dst + n
  · have hk : a - dst < (List.range n).length := by simp; omega
    rw [if_pos hw, if_pos hw,
      show (MachineState.readPadded mdata src n)[a - dst]?
          = (MachineState.readPadded mdata src n).toList[a - dst]? from by
        rw [ByteArray.toList_eq_data, Array.getElem?_toList]; rfl, ← hrb]
    simp only [YulSemantics.EVM.readBytes, List.getElem?_map,
      List.getElem?_eq_getElem hk, List.getElem_range, Option.map_some, Option.getD_some]
  · rw [if_neg hw, if_neg hw, getD_eq_dite]; exact hmem a

/-! ### Active-memory high-water-mark agreement -/

/-- A memory range whose current word count, offset, and size are words cannot
produce an active-word count outside a word. The division by 32 leaves ample
headroom even when `offset + size` itself needs 257 bits. -/
theorem activeWordsAfter_lt (curr offset size : Nat)
    (hcurr : curr < 2 ^ 256) (hoffset : offset < 2 ^ 256)
    (hsize : size < 2 ^ 256) :
    YulSemantics.EVM.activeWordsAfter curr offset size < 2 ^ 256 := by
  unfold YulSemantics.EVM.activeWordsAfter
  split
  · exact hcurr
  · rw [Nat.max_lt]
    exact ⟨hcurr, by omega⟩

/-- A source `touchMemory` and the target's one-range active-word update
produce the same wrapped word count from matching starting counts. -/
theorem activeWordsAfter_eq {yst : YulSemantics.EVM.EvmState} {s : EVM.State}
    (h : conv yst.activeWords = s.activeWords) (offset size : Nat) :
    conv (YulSemantics.EVM.touchMemory yst offset size).activeWords
      = s.activeWordsAfterUInt256 offset size := by
  have hnat : yst.activeWords.toNat = s.activeWords.toNat := by
    have := congrArg UInt256.toNat h
    simpa only [conv_toNat] using this
  unfold YulSemantics.EVM.touchMemory State.activeWordsAfterUInt256
  apply u256ext
  rw [conv_toNat, BitVec.toNat_ofNat, toNat_u256_ofNat, hnat]
  rfl

/-- Two-range active-memory agreement, used by `mcopy` for its source and
destination ranges. -/
theorem activeWordsAfter2_eq {yst : YulSemantics.EVM.EvmState} {s : EVM.State}
    (h : conv yst.activeWords = s.activeWords)
    (offset₁ size₁ offset₂ size₂ : Nat)
    (hoffset₁ : offset₁ < 2 ^ 256) (hsize₁ : size₁ < 2 ^ 256) :
    conv (YulSemantics.EVM.touchMemory2 yst offset₁ size₁ offset₂ size₂).activeWords
      = s.activeWordsAfterUInt256_2 offset₁ size₁ offset₂ size₂ := by
  have hnat : yst.activeWords.toNat = s.activeWords.toNat := by
    have := congrArg UInt256.toNat h
    simpa only [conv_toNat] using this
  have hmid : YulSemantics.EVM.activeWordsAfter
      yst.activeWords.toNat offset₁ size₁ < 2 ^ 256 :=
    activeWordsAfter_lt _ _ _ yst.activeWords.isLt hoffset₁ hsize₁
  unfold YulSemantics.EVM.touchMemory2 YulSemantics.EVM.touchMemory
    State.activeWordsAfterUInt256_2
  apply u256ext
  simp only [conv_toNat, BitVec.toNat_ofNat, toNat_u256_ofNat,
    Nat.mod_eq_of_lt hmid]
  rw [hnat]
  rfl

/-- `msize` agreement: both semantics expose 32 times the matching active-word
count, wrapped to a machine word. -/
theorem memorySize_eq {yst : YulSemantics.EVM.EvmState} {s : EVM.State}
    (h : conv yst.activeWords = s.activeWords) :
    conv (YulSemantics.EVM.memorySize yst) = MachineState.msize s.toMachineState := by
  have hnat : yst.activeWords.toNat = s.activeWords.toNat := by
    have := congrArg UInt256.toNat h
    simpa only [conv_toNat] using this
  unfold YulSemantics.EVM.memorySize MachineState.msize
  apply u256ext
  rw [conv_toNat, BitVec.toNat_ofNat, toNat_u256_ofNat, hnat]

/-- Correspondence of immutable frame environment data between the two
semantics, indexed by the *execution environments* alone (not the full state)
so it is preserved definitionally across steps that leave `executionEnv`
untouched — which is every supported op. -/
structure EnvMatch (ye : YulSemantics.EVM.ExecEnv) (se : ExecutionEnv) : Prop where
  calldataLen : ye.calldata.length = se.calldata.size
  /-- The source's abstract, configurable Keccak oracle agrees with the
  target semantics' hash primitive on the same byte sequence. -/
  keccak : ∀ bytes, conv (ye.keccakOf bytes) = EvmSemantics.keccak256 (mkCode bytes)
  address    : conv ye.address    = se.address.toUInt256
  origin     : conv ye.origin     = se.origin.toUInt256
  caller     : conv ye.caller     = se.caller.toUInt256
  callvalue  : conv ye.callvalue  = se.weiValue
  gasprice   : conv ye.gasprice   = se.gasPrice
  /-- Source static-call context agrees with the target frame's permission to
  mutate state. -/
  static     : ye.static = !se.permitStateMutation
  coinbase   : conv ye.coinbase   = se.header.coinbase.toUInt256
  timestamp  : conv ye.timestamp  = se.header.timestamp
  number     : conv ye.number     = se.header.number
  prevrandao : conv ye.prevrandao = se.header.prevRandao
  gaslimit   : conv ye.gaslimit   = se.header.gasLimit
  chainid    : conv ye.chainid    = se.header.chainId
  basefee    : conv ye.basefee    = se.header.baseFeePerGas
  blobbasefee : conv ye.blobbasefee = se.header.blobBaseFee
  /-- Blob-versioned-hash agreement, including the EVM's zero result for an
  index outside the transaction's finite hash list. -/
  blobHash : ∀ i, conv (ye.blobHashOf i)
    = se.blobVersionedHashes[(conv i).toNat]?.getD 0
  /-- Historical-block-hash agreement. Both semantics leave the validity
  window/default-zero policy to the supplied lookup function. -/
  blockHash : ∀ n, conv (ye.blockHashOf n) = se.header.blockHash (conv n)

/-- Updating the mutable global persistent-storage projection does not change
the immutable execution-environment fields related by `EnvMatch`. -/
theorem EnvMatch.setStorageOf {ye : YulSemantics.EVM.ExecEnv} {se : ExecutionEnv}
    (h : EnvMatch ye se) (storageOf : YulSemantics.EVM.U256 → YulSemantics.EVM.U256 →
      YulSemantics.EVM.U256) :
    EnvMatch { ye with storageOf := storageOf } se := by
  cases h
  constructor <;> assumption

/-- Updating the global transient-storage projection likewise preserves the
immutable frame environment relation. -/
theorem EnvMatch.setTransientOf {ye : YulSemantics.EVM.ExecEnv} {se : ExecutionEnv}
    (h : EnvMatch ye se) (transientOf : YulSemantics.EVM.U256 → YulSemantics.EVM.U256 →
      YulSemantics.EVM.U256) :
    EnvMatch { ye with transientOf := transientOf } se := by
  cases h
  constructor <;> assumption

/-- Updating mutable balance/code-hash world projections and the cached self balance preserves the
immutable frame-environment correspondence. -/
theorem EnvMatch.setBalanceWorld {ye : YulSemantics.EVM.ExecEnv} {se : ExecutionEnv}
    (h : EnvMatch ye se) (selfBalance : YulSemantics.EVM.U256)
    (balanceOf extCodeHashOf : YulSemantics.EVM.U256 → YulSemantics.EVM.U256) :
    EnvMatch
      { ye with
        selfBalance
        balanceOf
        extCodeHashOf }
      se := by
  cases h
  constructor <;> assumption

/-- Agreement between yul-semantics' global account projections and the
target's concrete account map. Besides external code, this pins every account
nonce and persistent/transient storage slot, making open-world call/create
responses stable across all matching target states. -/
structure ExternalCodeMatch (ye : YulSemantics.EVM.ExecEnv) (accounts : AccountMap) : Prop where
  bytes : ∀ a, MemMatch (YulSemantics.EVM.byteFrom (ye.extCodeOf a))
    (accounts (AccountAddress.ofUInt256 (conv a))).code
  length : ∀ a, (ye.extCodeOf a).length
    = (accounts (AccountAddress.ofUInt256 (conv a))).code.size
  hash : ∀ a, conv (YulSemantics.EVM.projectedCodeHash ye ye.balanceOf a)
    = (accounts (AccountAddress.ofUInt256 (conv a))).codeHash
  nonce : ∀ a, conv (ye.nonceOf a)
    = (accounts (AccountAddress.ofUInt256 (conv a))).nonce
  storage : ∀ a k, conv (ye.storageOf a k)
    = (accounts (AccountAddress.ofUInt256 (conv a))).storage.get (conv k)
  tstorage : ∀ a k, conv (ye.transientOf a k)
    = (accounts (AccountAddress.ofUInt256 (conv a))).tstorage.get (conv k)

/-- Source account keys and target account addresses use the same low-160-bit
projection. This is what makes all 256-bit aliases of an EVM address agree. -/
theorem accountAddress_eq_iff_accountKey (a b : YulSemantics.EVM.U256) :
    AccountAddress.ofUInt256 (conv a) = AccountAddress.ofUInt256 (conv b) ↔
      YulSemantics.EVM.accountKey a = YulSemantics.EVM.accountKey b := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    simpa [AccountAddress.ofUInt256, AccountAddress.size,
      YulSemantics.EVM.accountKey] using hv
  · intro h
    apply Fin.ext
    simpa [AccountAddress.ofUInt256, AccountAddress.size,
      YulSemantics.EVM.accountKey] using h

@[simp] theorem accountAddress_ofUInt256_toUInt256 (a : AccountAddress) :
    AccountAddress.ofUInt256 a.toUInt256 = a := by
  apply Fin.ext
  simp only [AccountAddress.ofUInt256, AccountAddress.toUInt256,
    toNat_u256_ofNat, Fin.val_ofNat]
  have h256 : a.val < 2 ^ 256 := lt_trans a.isLt (by
    unfold AccountAddress.size
    omega)
  rw [Nat.mod_eq_of_lt h256]
  calc
    a.val % AccountAddress.size % AccountAddress.size =
        a.val % AccountAddress.size := Nat.mod_eq_of_lt
          (Nat.mod_lt _ (by unfold AccountAddress.size; omega))
    _ = a.val := Nat.mod_eq_of_lt a.isLt

/-- Replacing only account balances, while recomputing the source `EXTCODEHASH` projection from
the unchanged nonce/code projections, preserves the full external-account correspondence. -/
theorem ExternalCodeMatch.rebalance
    {ye : YulSemantics.EVM.ExecEnv} {accounts accounts' : AccountMap}
    {balances : YulSemantics.EVM.U256 → YulSemantics.EVM.U256}
    (h : ExternalCodeMatch ye accounts)
    (selfBalance : YulSemantics.EVM.U256)
    (hkeccak : ∀ bytes, conv (ye.keccakOf bytes) = EvmSemantics.keccak256 (mkCode bytes))
    (hbalance : ∀ a, conv (balances a) =
      (accounts' (AccountAddress.ofUInt256 (conv a))).balance)
    (hnonce : ∀ a, (accounts' a).nonce = (accounts a).nonce)
    (hcode : ∀ a, (accounts' a).code = (accounts a).code)
    (hstorage : ∀ a, (accounts' a).storage = (accounts a).storage)
    (htstorage : ∀ a, (accounts' a).tstorage = (accounts a).tstorage) :
    ExternalCodeMatch
      { ye with
        selfBalance := selfBalance
        balanceOf := balances
        extCodeHashOf := YulSemantics.EVM.projectedCodeHash ye balances }
      accounts' := by
  constructor
  · intro a
    simpa [hcode] using h.bytes a
  · intro a
    simpa [hcode] using h.length a
  · intro a
    let addr := AccountAddress.ofUInt256 (conv a)
    have hn : (ye.nonceOf a).toNat = (accounts' addr).nonce.toNat := by
      have hold := congrArg UInt256.toNat (h.nonce a)
      rw [hnonce] at ⊢
      simpa only [conv_toNat] using hold
    have hb : (balances a).toNat = (accounts' addr).balance.toNat := by
      have hold := congrArg UInt256.toNat (hbalance a)
      simpa only [conv_toNat] using hold
    have hc : (ye.extCodeOf a).length = (accounts' addr).code.size := by
      rw [hcode]
      exact h.length a
    have hbytes : mkCode (ye.extCodeOf a) = (accounts' addr).code := by
      rw [hcode]
      exact (h.bytes a).mkCode_eq (h.length a)
    change conv (YulSemantics.EVM.projectedCodeHash ye balances a) =
      (accounts' addr).codeHash
    unfold YulSemantics.EVM.projectedCodeHash Account.codeHash Account.isEmpty
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    by_cases hz : (ye.nonceOf a).toNat = 0 ∧ (balances a).toNat = 0 ∧
        (ye.extCodeOf a).length = 0
    · rw [if_pos hz]
      have ht : ((accounts' addr).nonce.toNat = 0 ∧
          (accounts' addr).balance.toNat = 0) ∧ (accounts' addr).code.size = 0 := by
        rcases hz with ⟨hn0, hb0, hc0⟩
        exact ⟨⟨hn.symm.trans hn0, hb.symm.trans hb0⟩, hc.symm.trans hc0⟩
      rw [if_pos ht]
      exact conv_zero
    · rw [if_neg hz]
      have hne : ¬((accounts' addr).nonce.toNat = 0 ∧
          (accounts' addr).balance.toNat = 0 ∧ (accounts' addr).code.size = 0) := by
        simpa [hn, hb, hc] using hz
      have hnt : ¬(((accounts' addr).nonce.toNat = 0 ∧
          (accounts' addr).balance.toNat = 0) ∧ (accounts' addr).code.size = 0) := by
        intro ht
        exact hne ⟨ht.1.1, ht.1.2, ht.2⟩
      rw [if_neg hnt, hkeccak, hbytes]
  · intro a
    rw [hnonce]
    exact h.nonce a
  · intro a k
    rw [hstorage]
    exact h.storage a k
  · intro a k
    rw [htstorage]
    exact h.tstorage a k

/-- Updating one account's balance preserves any balance-insensitive account field. -/
theorem AccountMap.setBalance_field {α : Type} (f : Account → α)
    (hf : ∀ account balance, f { account with balance := balance } = f account)
    (accounts : AccountMap) (updated address : AccountAddress) (balance : UInt256) :
    f ((accounts.set updated { accounts updated with balance := balance }) address) =
      f (accounts address) := by
  by_cases h : address = updated
  · subst address
    simp [hf]
  · rw [AccountMap.get_set_other _ _ _ _ h]

/-- A balance transfer preserves any balance-insensitive account field at every address. -/
theorem AccountMap.transfer_field {α : Type} (f : Account → α)
    (hf : ∀ account balance, f { account with balance := balance } = f account)
    (accounts : AccountMap) (src dst address : AccountAddress) (value : UInt256) :
    f ((accounts.transfer src dst value) address) = f (accounts address) := by
  unfold AccountMap.transfer
  by_cases hd : address = dst
  · subst address
    simp only [AccountMap.get_set_same, hf]
    by_cases hds : dst = src
    · subst dst
      simp only [AccountMap.get_set_same, hf]
    · exact congrArg f (AccountMap.get_set_other accounts src dst
        { accounts src with balance := (accounts src).balance - value } hds)
  · rw [AccountMap.get_set_other _ _ _ _ hd]
    by_cases hs : address = src
    · subst address
      simp [hf]
    · rw [AccountMap.get_set_other _ _ _ _ hs]

/-- A source low-160-bit scalar update agrees with setting the corresponding concrete account's
balance. -/
theorem updAccountValue_balance_set
    {balances : YulSemantics.EVM.U256 → YulSemantics.EVM.U256}
    {accounts : AccountMap} (hbalance : ∀ a, conv (balances a) =
      (accounts (AccountAddress.ofUInt256 (conv a))).balance)
    (yaddr : YulSemantics.EVM.U256) (addr : AccountAddress)
    (haddr : AccountAddress.ofUInt256 (conv yaddr) = addr) :
    ∀ a, conv (YulSemantics.EVM.updAccountValue balances yaddr 0 a) =
      ((accounts.set addr { accounts addr with balance := 0 })
        (AccountAddress.ofUInt256 (conv a))).balance := by
  intro a
  by_cases ha : AccountAddress.ofUInt256 (conv a) = addr
  · have hkey : YulSemantics.EVM.accountKey a = YulSemantics.EVM.accountKey yaddr :=
      (accountAddress_eq_iff_accountKey a yaddr).mp (ha.trans haddr.symm)
    simp only [YulSemantics.EVM.updAccountValue, hkey, if_pos,
      ha, AccountMap.get_set_same]
    exact conv_zero
  · have hkey : YulSemantics.EVM.accountKey a ≠ YulSemantics.EVM.accountKey yaddr := by
      intro heq
      apply ha
      exact ((accountAddress_eq_iff_accountKey a yaddr).mpr heq).trans haddr
    rw [YulSemantics.EVM.updAccountValue, if_neg hkey,
      AccountMap.get_set_other _ _ _ _ ha]
    exact hbalance a

/-- The pair of source balance updates used by distinct-beneficiary `SELFDESTRUCT` agrees with the
target account-map transfer. -/
theorem updAccountValue_balance_transfer
    {balances : YulSemantics.EVM.U256 → YulSemantics.EVM.U256}
    {accounts : AccountMap} (hbalance : ∀ a, conv (balances a) =
      (accounts (AccountAddress.ofUInt256 (conv a))).balance)
    (yself ybeneficiary : YulSemantics.EVM.U256)
    (self beneficiary : AccountAddress)
    (hself : AccountAddress.ofUInt256 (conv yself) = self)
    (hbeneficiary : AccountAddress.ofUInt256 (conv ybeneficiary) = beneficiary)
    (hne : beneficiary ≠ self)
    (hselfBalance : conv (balances yself) = (accounts self).balance) :
    ∀ a,
      conv (YulSemantics.EVM.updAccountValue
        (YulSemantics.EVM.updAccountValue balances yself 0)
        ybeneficiary (balances ybeneficiary + balances yself) a) =
      ((accounts.transfer self beneficiary (accounts self).balance)
        (AccountAddress.ofUInt256 (conv a))).balance := by
  intro a
  let address := AccountAddress.ofUInt256 (conv a)
  by_cases hb : address = beneficiary
  · have hbkey : YulSemantics.EVM.accountKey a =
        YulSemantics.EVM.accountKey ybeneficiary :=
      (accountAddress_eq_iff_accountKey a ybeneficiary).mp (hb.trans hbeneficiary.symm)
    have hskey : YulSemantics.EVM.accountKey a ≠ YulSemantics.EVM.accountKey yself := by
      intro heq
      apply hne
      exact hb.symm.trans (((accountAddress_eq_iff_accountKey a yself).mpr heq).trans hself)
    subst address
    simp [YulSemantics.EVM.updAccountValue, hbkey, AccountMap.transfer, hne,
      hb, hbeneficiary, hself, conv_add, hbalance]
  · by_cases hs : address = self
    · have hskey : YulSemantics.EVM.accountKey a = YulSemantics.EVM.accountKey yself :=
        (accountAddress_eq_iff_accountKey a yself).mp (hs.trans hself.symm)
      have hbkey : YulSemantics.EVM.accountKey a ≠
          YulSemantics.EVM.accountKey ybeneficiary := by
        intro heq
        apply hb
        exact ((accountAddress_eq_iff_accountKey a ybeneficiary).mpr heq).trans hbeneficiary
      have hyne : YulSemantics.EVM.accountKey yself ≠
          YulSemantics.EVM.accountKey ybeneficiary := by
        intro heq
        apply hne
        exact hbeneficiary.symm.trans
          (((accountAddress_eq_iff_accountKey yself ybeneficiary).mpr heq).symm.trans hself)
      subst address
      simp [YulSemantics.EVM.updAccountValue, hskey, hyne,
        AccountMap.transfer, hne, hne.symm, hs]
      rw [← hselfBalance, ← conv_sub]
      simp
    · have hskey : YulSemantics.EVM.accountKey a ≠ YulSemantics.EVM.accountKey yself := by
        intro heq
        apply hs
        exact ((accountAddress_eq_iff_accountKey a yself).mpr heq).trans hself
      have hbkey : YulSemantics.EVM.accountKey a ≠
          YulSemantics.EVM.accountKey ybeneficiary := by
        intro heq
        apply hb
        exact ((accountAddress_eq_iff_accountKey a ybeneficiary).mpr heq).trans hbeneficiary
      unfold AccountMap.transfer
      rw [YulSemantics.EVM.updAccountValue, if_neg hbkey,
        YulSemantics.EVM.updAccountValue, if_neg hskey,
        AccountMap.get_set_other _ _ _ _ hb,
        AccountMap.get_set_other _ _ _ _ hs]
      exact hbalance a

/-- Updating one account while preserving the fields observed by external-code
operations preserves `ExternalCodeMatch`. Storage and transient-storage
updates satisfy these premises definitionally. -/
theorem ExternalCodeMatch.setAccount {ye : YulSemantics.EVM.ExecEnv} {accounts : AccountMap}
    (h : ExternalCodeMatch ye accounts) (addr : AccountAddress) (acc : Account)
    (hnonce : acc.nonce = (accounts addr).nonce)
    (hbalance : acc.balance = (accounts addr).balance)
    (hcode : acc.code = (accounts addr).code)
    (hstorage : acc.storage = (accounts addr).storage)
    (htstorage : acc.tstorage = (accounts addr).tstorage) :
    ExternalCodeMatch ye (accounts.set addr acc) := by
  constructor
  · intro a
    by_cases ha : AccountAddress.ofUInt256 (conv a) = addr
    · rw [ha, AccountMap.get_set_same]
      have hold := h.bytes a
      rw [ha] at hold
      simpa [hcode] using hold
    · rw [AccountMap.get_set_other _ _ _ _ ha]
      exact h.bytes a
  · intro a
    by_cases ha : AccountAddress.ofUInt256 (conv a) = addr
    · rw [ha, AccountMap.get_set_same]
      have hold := h.length a
      rw [ha] at hold
      simpa [hcode] using hold
    · rw [AccountMap.get_set_other _ _ _ _ ha]
      exact h.length a
  · intro a
    by_cases ha : AccountAddress.ofUInt256 (conv a) = addr
    · rw [ha, AccountMap.get_set_same]
      have hold := h.hash a
      rw [ha] at hold
      simpa [Account.codeHash, Account.isEmpty, hnonce, hbalance, hcode] using hold
    · rw [AccountMap.get_set_other _ _ _ _ ha]
      exact h.hash a
  · intro a
    by_cases ha : AccountAddress.ofUInt256 (conv a) = addr
    · rw [ha, AccountMap.get_set_same, hnonce]
      have hold := h.nonce a
      rwa [ha] at hold
    · rw [AccountMap.get_set_other _ _ _ _ ha]
      exact h.nonce a
  · intro a k
    by_cases ha : AccountAddress.ofUInt256 (conv a) = addr
    · rw [ha, AccountMap.get_set_same, hstorage]
      have hold := h.storage a k
      rwa [ha] at hold
    · rw [AccountMap.get_set_other _ _ _ _ ha]
      exact h.storage a k
  · intro a k
    by_cases ha : AccountAddress.ofUInt256 (conv a) = addr
    · rw [ha, AccountMap.get_set_same, htstorage]
      have hold := h.tstorage a k
      rwa [ha] at hold
    · rw [AccountMap.get_set_other _ _ _ _ ha]
      exact h.tstorage a k

/-- A local persistent-storage write preserves the global-world relation,
including every high-bit alias of the current 160-bit account address. -/
theorem ExternalCodeMatch.setStorage {ye : YulSemantics.EVM.ExecEnv}
    {accounts : AccountMap} (h : ExternalCodeMatch ye accounts)
    (yaddr : YulSemantics.EVM.U256) (addr : AccountAddress)
    (key value : YulSemantics.EVM.U256)
    (haddr : AccountAddress.ofUInt256 (conv yaddr) = addr) :
    ExternalCodeMatch
      { ye with storageOf := YulSemantics.EVM.updAccount ye.storageOf yaddr key value }
      (accounts.set addr
        { accounts addr with storage := (accounts addr).storage.set (conv key) (conv value) }) := by
  constructor
  · intro a
    by_cases ha : AccountAddress.ofUInt256 (conv a) = addr
    · rw [ha, AccountMap.get_set_same]
      have hold := h.bytes a
      rwa [ha] at hold
    · rw [AccountMap.get_set_other _ _ _ _ ha]
      exact h.bytes a
  · intro a
    by_cases ha : AccountAddress.ofUInt256 (conv a) = addr
    · rw [ha, AccountMap.get_set_same]
      have hold := h.length a
      rwa [ha] at hold
    · rw [AccountMap.get_set_other _ _ _ _ ha]
      exact h.length a
  · intro a
    by_cases ha : AccountAddress.ofUInt256 (conv a) = addr
    · rw [ha, AccountMap.get_set_same]
      have hold := h.hash a
      rwa [ha] at hold
    · rw [AccountMap.get_set_other _ _ _ _ ha]
      exact h.hash a
  · intro a
    by_cases ha : AccountAddress.ofUInt256 (conv a) = addr
    · rw [ha, AccountMap.get_set_same]
      have hold := h.nonce a
      rw [ha] at hold
      exact hold
    · rw [AccountMap.get_set_other _ _ _ _ ha]
      exact h.nonce a
  · intro a k
    change conv (YulSemantics.EVM.updAccount ye.storageOf yaddr key value a k) = _
    unfold YulSemantics.EVM.updAccount
    by_cases ha : AccountAddress.ofUInt256 (conv a) = addr
    · have hkey : YulSemantics.EVM.accountKey a = YulSemantics.EVM.accountKey yaddr :=
        (accountAddress_eq_iff_accountKey a yaddr).mp (ha.trans haddr.symm)
      rw [if_pos hkey, ha, AccountMap.get_set_same]
      by_cases hk : k = key
      · subst hk
        rw [if_pos rfl, Storage.get_set_same]
      · rw [if_neg hk, Storage.get_set_other _ _ _ _ (by simpa [conv_inj] using hk)]
        have hold := h.storage a k
        rw [ha] at hold
        exact hold
    · have hkey : YulSemantics.EVM.accountKey a ≠ YulSemantics.EVM.accountKey yaddr := by
        intro heq
        apply ha
        exact ((accountAddress_eq_iff_accountKey a yaddr).mpr heq).trans haddr
      rw [if_neg hkey, AccountMap.get_set_other _ _ _ _ ha]
      exact h.storage a k
  · intro a k
    by_cases ha : AccountAddress.ofUInt256 (conv a) = addr
    · rw [ha, AccountMap.get_set_same]
      have hold := h.tstorage a k
      rw [ha] at hold
      exact hold
    · rw [AccountMap.get_set_other _ _ _ _ ha]
      exact h.tstorage a k

/-- A local transient-storage write preserves the full global-world relation. -/
theorem ExternalCodeMatch.setTransient {ye : YulSemantics.EVM.ExecEnv}
    {accounts : AccountMap} (h : ExternalCodeMatch ye accounts)
    (yaddr : YulSemantics.EVM.U256) (addr : AccountAddress)
    (key value : YulSemantics.EVM.U256)
    (haddr : AccountAddress.ofUInt256 (conv yaddr) = addr) :
    ExternalCodeMatch
      { ye with transientOf := YulSemantics.EVM.updAccount ye.transientOf yaddr key value }
      (accounts.set addr
        { accounts addr with tstorage := (accounts addr).tstorage.set (conv key) (conv value) }) := by
  constructor
  · intro a
    by_cases ha : AccountAddress.ofUInt256 (conv a) = addr
    · rw [ha, AccountMap.get_set_same]
      have hold := h.bytes a
      rwa [ha] at hold
    · rw [AccountMap.get_set_other _ _ _ _ ha]
      exact h.bytes a
  · intro a
    by_cases ha : AccountAddress.ofUInt256 (conv a) = addr
    · rw [ha, AccountMap.get_set_same]
      have hold := h.length a
      rwa [ha] at hold
    · rw [AccountMap.get_set_other _ _ _ _ ha]
      exact h.length a
  · intro a
    by_cases ha : AccountAddress.ofUInt256 (conv a) = addr
    · rw [ha, AccountMap.get_set_same]
      have hold := h.hash a
      rwa [ha] at hold
    · rw [AccountMap.get_set_other _ _ _ _ ha]
      exact h.hash a
  · intro a
    by_cases ha : AccountAddress.ofUInt256 (conv a) = addr
    · rw [ha, AccountMap.get_set_same]
      have hold := h.nonce a
      rw [ha] at hold
      exact hold
    · rw [AccountMap.get_set_other _ _ _ _ ha]
      exact h.nonce a
  · intro a k
    by_cases ha : AccountAddress.ofUInt256 (conv a) = addr
    · rw [ha, AccountMap.get_set_same]
      have hold := h.storage a k
      rw [ha] at hold
      exact hold
    · rw [AccountMap.get_set_other _ _ _ _ ha]
      exact h.storage a k
  · intro a k
    change conv (YulSemantics.EVM.updAccount ye.transientOf yaddr key value a k) = _
    unfold YulSemantics.EVM.updAccount
    by_cases ha : AccountAddress.ofUInt256 (conv a) = addr
    · have hkey : YulSemantics.EVM.accountKey a = YulSemantics.EVM.accountKey yaddr :=
        (accountAddress_eq_iff_accountKey a yaddr).mp (ha.trans haddr.symm)
      rw [if_pos hkey, ha, AccountMap.get_set_same]
      by_cases hk : k = key
      · subst hk
        rw [if_pos rfl, Storage.get_set_same]
      · rw [if_neg hk, Storage.get_set_other _ _ _ _ (by simpa [conv_inj] using hk)]
        have hold := h.tstorage a k
        rw [ha] at hold
        exact hold
    · have hkey : YulSemantics.EVM.accountKey a ≠ YulSemantics.EVM.accountKey yaddr := by
        intro heq
        apply ha
        exact ((accountAddress_eq_iff_accountKey a yaddr).mpr heq).trans haddr
      rw [if_neg hkey, AccountMap.get_set_other _ _ _ _ ha]
      exact h.tstorage a k

/-- One source log entry agrees with one target entry, including the address
of an arbitrary caller, callee, or init-code frame that emitted it. -/
def LogEntryMatch
    (yl : YulSemantics.EVM.LogEntry) (tl : EvmSemantics.LogEntry) : Prop :=
  conv yl.address = tl.address.toUInt256 ∧
    yl.topics.map conv = tl.topics.toList ∧
    yl.data = tl.data.toList

/-- The emitted logs agree in order, including address, topics, and data. -/
def LogsMatch
    (ys : List YulSemantics.EVM.LogEntry) (ts : EvmSemantics.LogSeries) : Prop :=
  List.Forall₂ LogEntryMatch ys ts.toList

/-- Appending matching entries preserves log-series agreement. -/
theorem LogsMatch.append {ys : List YulSemantics.EVM.LogEntry} {ts : EvmSemantics.LogSeries}
    {yl : YulSemantics.EVM.LogEntry} {tl : EvmSemantics.LogEntry}
    (h : LogsMatch ys ts) (he : LogEntryMatch yl tl) :
    LogsMatch (ys ++ [yl]) (ts.push tl) := by
  unfold LogsMatch at h ⊢
  rw [Array.toList_push]
  exact List.rel_append h (.cons he .nil)

/-- One source scheduled-destruction record agrees with one concrete target
address and with the target transaction's created-this-transaction test. -/
def SelfdestructEntryMatch
    (original : AccountMap) (y : YulSemantics.EVM.U256 × Bool)
    (t : AccountAddress) : Prop :=
  conv y.1 = t.toUInt256 ∧ y.2 = !(original t).isContract

/-- Scheduled destructions agree in execution order. Actual deletion is a later transaction-level
operation in the target semantics. -/
def SelfdestructsMatch
    (ys : List (YulSemantics.EVM.U256 × Bool)) (ts : Array AccountAddress)
    (original : AccountMap) : Prop :=
  List.Forall₂ (SelfdestructEntryMatch original) ys ts.toList

/-- Appending matching scheduled destructions preserves the correspondence. -/
theorem SelfdestructsMatch.append
    {ys : List (YulSemantics.EVM.U256 × Bool)} {ts : Array AccountAddress}
    {original : AccountMap} {y : YulSemantics.EVM.U256 × Bool}
    {t : AccountAddress}
    (h : SelfdestructsMatch ys ts original)
    (he : SelfdestructEntryMatch original y t) :
    SelfdestructsMatch (ys ++ [y]) (ts.push t) original := by
  unfold SelfdestructsMatch at h ⊢
  rw [Array.toList_push]
  exact List.rel_append h (.cons he .nil)

/-- The machine-state correspondence: memory and byte regions pointwise, plus
balances, external code, the executing account's (transient) storage, ordered
logs and scheduled destructions. yul-semantics' flat `storage` is the storage
of the target's `executionEnv.address`. -/
structure StateMatch (yst : YulSemantics.EVM.EvmState) (s : EVM.State) : Prop where
  mem : MemMatch yst.memory s.memory
  stor : ∀ k, conv (yst.storage k)
    = (s.accountMap s.executionEnv.address).storage.get (conv k)
  tstor : ∀ k, conv (yst.transient k)
    = (s.accountMap s.executionEnv.address).tstorage.get (conv k)
  /-- Calldata agreement: Yul reads its `List UInt8` calldata via `byteFrom`
  (`data.getD i 0`), which is pointwise the zero-padded read of the target
  frame's `ByteArray` calldata — i.e. `MemMatch` at the `byteFrom` view. No
  supported op mutates calldata, so this is threaded unchanged. -/
  cd : MemMatch (YulSemantics.EVM.byteFrom yst.env.calldata) s.executionEnv.calldata
  /-- Immutable environment data agreement (see `EnvMatch`). -/
  env : EnvMatch yst.env s.executionEnv
  /-- Code agreement (for `codesize`/`codecopy`/`datacopy`): like calldata, a
  zero-padded pointwise read of the frame's `ByteArray` code, plus a length
  match. No supported op mutates code, so this is threaded unchanged. -/
  codeBytes : MemMatch (YulSemantics.EVM.byteFrom yst.env.code) s.executionEnv.code
  codeLen : yst.env.code.length = s.executionEnv.code.size
  /-- The source environment's immutable self-balance view agrees with the
  executing account in the target world state. -/
  selfBalance : conv yst.env.selfBalance
    = (s.accountMap s.executionEnv.address).balance
  /-- The source environment's abstract balance oracle agrees pointwise with
  target account lookup. Words are truncated to EVM addresses on both sides. -/
  balanceOf : ∀ a, conv (yst.env.balanceOf a)
    = (s.accountMap (AccountAddress.ofUInt256 (conv a))).balance
  /-- The active-memory high-water mark agrees. This is separate from
  `MemMatch`: zero-valued reads and writes still expand memory for `msize`. -/
  activeWords : conv yst.activeWords = s.activeWords
  /-- Return-data agreement: the source list and target byte array have the
  same bytes, with zero-padded reads used by the copy proof. -/
  retData : MemMatch (YulSemantics.EVM.byteFrom yst.returndata) s.returnData
  /-- Exact return-data length agreement, used by `returndatasize` and the
  in-bounds premise of `returndatacopy`. -/
  retDataLen : yst.returndata.length = s.returnData.size
  /-- External account code bytes, lengths, and hashes agree pointwise. -/
  externalCode : ExternalCodeMatch yst.env s.accountMap
  /-- Emitted logs agree in order, retaining each emitting frame's address. -/
  logs : LogsMatch yst.logs s.substate.logSeries
  /-- Scheduled destruction records agree in execution order. -/
  selfdestructs : SelfdestructsMatch yst.selfdestructs
    s.substate.selfDestructList s.substate.originalAccountMap
  /-- The source's Cancun self-beneficiary selector agrees with the pinned target semantics'
  transaction-initial-world test. -/
  createdThisTx : yst.env.createdThisTx =
    !(s.substate.originalAccountMap s.executionEnv.address).isContract

/-- Lift the balance/account-map facts specific to one `SELFDESTRUCT` branch into the complete
machine-state correspondence. -/
theorem StateMatch.finishSelfdestruct_of
    {yst : YulSemantics.EVM.EvmState} {s : EVM.State}
    (hm : StateMatch yst s) (beneficiary : YulSemantics.EVM.U256)
    (hbalance : ∀ a,
      conv ((YulSemantics.EVM.finishSelfdestruct yst beneficiary).env.balanceOf a) =
        ((s.selfDestructTo (AccountAddress.ofUInt256 (conv beneficiary))).accountMap
          (AccountAddress.ofUInt256 (conv a))).balance)
    (hselfBalance :
      conv (YulSemantics.EVM.finishSelfdestruct yst beneficiary).env.selfBalance =
        ((s.selfDestructTo (AccountAddress.ofUInt256 (conv beneficiary))).accountMap
          s.executionEnv.address).balance)
    (hnonce : ∀ a,
      ((s.selfDestructTo (AccountAddress.ofUInt256 (conv beneficiary))).accountMap a).nonce =
        (s.accountMap a).nonce)
    (hcode : ∀ a,
      ((s.selfDestructTo (AccountAddress.ofUInt256 (conv beneficiary))).accountMap a).code =
        (s.accountMap a).code)
    (hstorage : ∀ a,
      ((s.selfDestructTo (AccountAddress.ofUInt256 (conv beneficiary))).accountMap a).storage =
        (s.accountMap a).storage)
    (htstorage : ∀ a,
      ((s.selfDestructTo (AccountAddress.ofUInt256 (conv beneficiary))).accountMap a).tstorage =
        (s.accountMap a).tstorage) :
    StateMatch (YulSemantics.EVM.finishSelfdestruct yst beneficiary)
      (s.selfDestructTo (AccountAddress.ofUInt256 (conv beneficiary))) := by
  let yst' := YulSemantics.EVM.finishSelfdestruct yst beneficiary
  let s' := s.selfDestructTo (AccountAddress.ofUInt256 (conv beneficiary))
  have henv : EnvMatch yst'.env s'.executionEnv := by
    simpa [yst', s', YulSemantics.EVM.finishSelfdestruct, State.selfDestructTo] using
      hm.env.setBalanceWorld yst'.env.selfBalance yst'.env.balanceOf yst'.env.extCodeHashOf
  have hext : ExternalCodeMatch yst'.env s'.accountMap := by
    simpa [yst', YulSemantics.EVM.finishSelfdestruct] using
      hm.externalCode.rebalance yst'.env.selfBalance hm.env.keccak hbalance
        hnonce hcode hstorage htstorage
  refine {
    mem := by simpa [yst', s', YulSemantics.EVM.finishSelfdestruct,
      State.selfDestructTo] using hm.mem
    stor := ?_
    tstor := ?_
    cd := by simpa [yst', s', YulSemantics.EVM.finishSelfdestruct,
      State.selfDestructTo] using hm.cd
    env := henv
    codeBytes := by simpa [yst', s', YulSemantics.EVM.finishSelfdestruct,
      State.selfDestructTo] using hm.codeBytes
    codeLen := by simpa [yst', s', YulSemantics.EVM.finishSelfdestruct,
      State.selfDestructTo] using hm.codeLen
    selfBalance := hselfBalance
    balanceOf := hbalance
    activeWords := by simpa [yst', s', YulSemantics.EVM.finishSelfdestruct,
      State.selfDestructTo] using hm.activeWords
    retData := by simpa [yst', s', YulSemantics.EVM.finishSelfdestruct,
      State.selfDestructTo] using hm.retData
    retDataLen := by simpa [yst', s', YulSemantics.EVM.finishSelfdestruct,
      State.selfDestructTo] using hm.retDataLen
    externalCode := hext
    logs := by simpa [yst', s', YulSemantics.EVM.finishSelfdestruct,
      State.selfDestructTo] using hm.logs
    selfdestructs := ?_
    createdThisTx := by simpa [yst', s', YulSemantics.EVM.finishSelfdestruct,
      State.selfDestructTo] using hm.createdThisTx }
  · intro k
    change conv (yst.storage k) = (s'.accountMap s'.executionEnv.address).storage.get (conv k)
    rw [show s'.executionEnv.address = s.executionEnv.address by
      rfl, hstorage]
    exact hm.stor k
  · intro k
    change conv (yst.transient k) = (s'.accountMap s'.executionEnv.address).tstorage.get (conv k)
    rw [show s'.executionEnv.address = s.executionEnv.address by
      rfl, htstorage]
    exact hm.tstor k
  · simpa [yst', s', YulSemantics.EVM.finishSelfdestruct, State.selfDestructTo] using
      SelfdestructsMatch.append hm.selfdestructs
        (show SelfdestructEntryMatch s.substate.originalAccountMap
          (yst.env.address, yst.env.createdThisTx) s.executionEnv.address from
          ⟨hm.env.address, hm.createdThisTx⟩)

/-- The deterministic source `SELFDESTRUCT` transition exactly matches the target opcode's
post-gas world update, including low-160-bit aliases and the Cancun self-beneficiary rule. -/
theorem StateMatch.finishSelfdestruct
    {yst : YulSemantics.EVM.EvmState} {s : EVM.State}
    (hm : StateMatch yst s) (beneficiary : YulSemantics.EVM.U256) :
    StateMatch (YulSemantics.EVM.finishSelfdestruct yst beneficiary)
      (s.selfDestructTo (AccountAddress.ofUInt256 (conv beneficiary))) := by
  let self := s.executionEnv.address
  let ben := AccountAddress.ofUInt256 (conv beneficiary)
  have hself : AccountAddress.ofUInt256 (conv yst.env.address) = self := by
    rw [hm.env.address, accountAddress_ofUInt256_toUInt256]
  have hsameIff : ben = self ↔
      YulSemantics.EVM.accountKey beneficiary =
        YulSemantics.EVM.accountKey yst.env.address := by
    simpa [ben, self, hself] using
      accountAddress_eq_iff_accountKey beneficiary yst.env.address
  by_cases hsame : ben = self
  · have hysame := hsameIff.mp hsame
    by_cases hcreated : (s.substate.originalAccountMap self).isContract = false
    · have hycreated : yst.env.createdThisTx = true := by
        exact hm.createdThisTx.trans (by simp [self, hcreated])
      have hbalance : ∀ a,
          conv ((YulSemantics.EVM.finishSelfdestruct yst beneficiary).env.balanceOf a) =
            ((s.selfDestructTo ben).accountMap
              (AccountAddress.ofUInt256 (conv a))).balance := by
        simpa [YulSemantics.EVM.finishSelfdestruct, State.selfDestructTo,
          ben, self, hsame, hysame, hcreated, hycreated] using
          updAccountValue_balance_set hm.balanceOf yst.env.address self hself
      apply hm.finishSelfdestruct_of beneficiary hbalance
      · simpa [YulSemantics.EVM.finishSelfdestruct,
          YulSemantics.EVM.updAccountValue, hysame, hself, hycreated] using
          hbalance yst.env.address
      · intro a
        simpa [State.selfDestructTo, ben, self, hsame, hcreated] using
          AccountMap.setBalance_field (·.nonce) (by intros; rfl)
            s.accountMap self a 0
      · intro a
        simpa [State.selfDestructTo, ben, self, hsame, hcreated] using
          AccountMap.setBalance_field (·.code) (by intros; rfl)
            s.accountMap self a 0
      · intro a
        simpa [State.selfDestructTo, ben, self, hsame, hcreated] using
          AccountMap.setBalance_field (·.storage) (by intros; rfl)
            s.accountMap self a 0
      · intro a
        simpa [State.selfDestructTo, ben, self, hsame, hcreated] using
          AccountMap.setBalance_field (·.tstorage) (by intros; rfl)
            s.accountMap self a 0
    · have hcontract : (s.substate.originalAccountMap self).isContract = true := by
        cases h : (s.substate.originalAccountMap self).isContract <;> simp_all
      have hycreated : yst.env.createdThisTx = false := by
        exact hm.createdThisTx.trans (by simp [self, hcontract])
      apply hm.finishSelfdestruct_of beneficiary
      · intro a
        simpa [YulSemantics.EVM.finishSelfdestruct, State.selfDestructTo,
          ben, self, hsame, hysame, hcontract, hycreated] using hm.balanceOf a
      · simpa [YulSemantics.EVM.finishSelfdestruct, State.selfDestructTo,
          ben, self, hsame, hysame, hcontract, hycreated] using hm.selfBalance
      · intro a
        simp [State.selfDestructTo, ben, self, hsame, hcontract]
      · intro a
        simp [State.selfDestructTo, ben, self, hsame, hcontract]
      · intro a
        simp [State.selfDestructTo, ben, self, hsame, hcontract]
      · intro a
        simp [State.selfDestructTo, ben, self, hsame, hcontract]
  · have hyne : YulSemantics.EVM.accountKey beneficiary ≠
        YulSemantics.EVM.accountKey yst.env.address := by
      exact fun h => hsame (hsameIff.mpr h)
    have hynesym : YulSemantics.EVM.accountKey yst.env.address ≠
        YulSemantics.EVM.accountKey beneficiary := Ne.symm hyne
    have hselfBalanceOf : conv (yst.env.balanceOf yst.env.address) =
        (s.accountMap self).balance := by
      simpa [self, hself] using hm.balanceOf yst.env.address
    have hysb : yst.env.selfBalance = yst.env.balanceOf yst.env.address := by
      apply conv_inj.mp
      exact hm.selfBalance.trans hselfBalanceOf.symm
    have hbalance : ∀ a,
        conv ((YulSemantics.EVM.finishSelfdestruct yst beneficiary).env.balanceOf a) =
          ((s.selfDestructTo ben).accountMap
            (AccountAddress.ofUInt256 (conv a))).balance := by
      simpa [YulSemantics.EVM.finishSelfdestruct, State.selfDestructTo,
        ben, self, hsame, hyne, hysb] using
        updAccountValue_balance_transfer hm.balanceOf yst.env.address beneficiary
          self ben hself rfl hsame hselfBalanceOf
    apply hm.finishSelfdestruct_of beneficiary hbalance
    · have hyselfzero :
          (YulSemantics.EVM.finishSelfdestruct yst beneficiary).env.selfBalance = 0 := by
        simp [YulSemantics.EVM.finishSelfdestruct, hyne]
      rw [hyselfzero]
      simpa [YulSemantics.EVM.finishSelfdestruct,
        YulSemantics.EVM.updAccountValue, hyne, hynesym, hself] using
        hbalance yst.env.address
    · intro a
      simpa [State.selfDestructTo, ben, self, hsame] using
        AccountMap.transfer_field (·.nonce) (by intros; rfl)
          s.accountMap self ben a (s.accountMap self).balance
    · intro a
      simpa [State.selfDestructTo, ben, self, hsame] using
        AccountMap.transfer_field (·.code) (by intros; rfl)
          s.accountMap self ben a (s.accountMap self).balance
    · intro a
      simpa [State.selfDestructTo, ben, self, hsame] using
        AccountMap.transfer_field (·.storage) (by intros; rfl)
          s.accountMap self ben a (s.accountMap self).balance
    · intro a
      simpa [State.selfDestructTo, ben, self, hsame] using
        AccountMap.transfer_field (·.tstorage) (by intros; rfl)
          s.accountMap self ben a (s.accountMap self).balance

/-- Frame-level side conditions preserved by every step of a straight-line
execution. `code` is the full assembled program. -/
structure FrameOK (code : ByteArray) (s : EVM.State) : Prop where
  hcode : s.executionEnv.code = code
  /-- Positions in the code fit in a word, so `pc` arithmetic never wraps. -/
  codeSmall : code.size < 2 ^ 256
  fork : s.executionEnv.fork = .Osaka
  perm : s.executionEnv.permitStateMutation = true
  noPrecompile : Precompile.isPrecompile s.executionEnv.fork s.executionEnv.codeAddr
    = false
  callStack : s.callStack = []
  running : s.halt = .Running

/-- How a yul-semantics halt payload (`halted = some hk`) appears in the
target state. -/
def HaltMatch (hk : YulSemantics.EVM.HaltKind × List UInt8) (s : EVM.State) : Prop :=
  match hk.1 with
  | .stop    => s.halt = .Success
  | .ret     => s.halt = .Returned ∧ s.hReturn.toList = hk.2
  | .revert  => s.halt = .Reverted ∧ s.hReturn.toList = hk.2
  | .invalid => s.halt = .Exception .InvalidInstruction
  | .invalidMemoryAccess => s.halt = .Exception .InvalidMemoryAccess
  | .selfdestruct => s.halt = .Success ∧ s.hReturn = .empty

/-- The `ExecutionResult` a yul-semantics halt corresponds to. -/
def resultOf (hk : YulSemantics.EVM.HaltKind × List UInt8) : ExecutionResult :=
  match hk.1 with
  | .stop    => .success
  | .ret     => .returned (mkCode hk.2)
  | .revert  => .reverted (mkCode hk.2)
  | .invalid => .exception .InvalidInstruction
  | .invalidMemoryAccess => .exception .InvalidMemoryAccess
  | .selfdestruct => .success

end YulEvmCompiler
