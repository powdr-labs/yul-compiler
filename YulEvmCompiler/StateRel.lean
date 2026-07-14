import YulEvmCompiler.Decode
import YulEvmCompiler.Value
import YulEvmCompiler.BytesLemmas
import EvmSemantics.EVM.BigStep

/-!
# YulEvmCompiler.StateRel

The correspondence between the two machine states:

* `MemMatch`   — yul-semantics' total `Nat → UInt8` memory vs. evm-semantics'
  `ByteArray` with zero-padded reads;
* `StateMatch` — memory contents and active size, calldata/environment data,
  account balances, and (transient) storage of the executing account;
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
  address    : conv ye.address    = se.address.toUInt256
  origin     : conv ye.origin     = se.origin.toUInt256
  caller     : conv ye.caller     = se.caller.toUInt256
  callvalue  : conv ye.callvalue  = se.weiValue
  gasprice   : conv ye.gasprice   = se.gasPrice
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

/-- The machine-state correspondence: memory and balances pointwise, plus the
executing account's (transient) storage. yul-semantics' flat `storage` is the
storage of the target's `executionEnv.address`. The returndata/logs components
are unconstrained until the corresponding ops enter the supported set. -/
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

/-- The `ExecutionResult` a yul-semantics halt corresponds to. -/
def resultOf (hk : YulSemantics.EVM.HaltKind × List UInt8) : ExecutionResult :=
  match hk.1 with
  | .stop    => .success
  | .ret     => .returned (mkCode hk.2)
  | .revert  => .reverted (mkCode hk.2)
  | .invalid => .exception .InvalidInstruction

end YulEvmCompiler
