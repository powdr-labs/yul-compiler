import YulEvmCompiler.Decode
import YulEvmCompiler.Value
import EvmSemantics.EVM.BigStep

/-!
# YulEvmCompiler.StateRel

The correspondence between the two machine states:

* `MemMatch`   — yul-semantics' total `Nat → UInt8` memory vs. evm-semantics'
  `ByteArray` with zero-padded reads;
* `StateMatch` — memory + (transient) storage of the executing account;
* `FrameOK`    — the frame-level side conditions that hold throughout a
  straight-line execution (fixed code, Osaka fork, mutation permitted, not a
  precompile frame, no suspended callers, still running);
* `HaltMatch`  — how a yul-semantics halt payload shows up in the target
  state's `halt`/`hReturn`.

Plus the two memory read-agreement lemmas (`MLOAD`, and the `RETURN`/`REVERT`
payloads), which are the only place the two memory representations meet.
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
        mul_le_mul_right' hacc 256
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
        mul_le_mul_right' hacc 256
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

/-- The machine-state correspondence: memory pointwise, and the executing
account's (transient) storage pointwise. yul-semantics' flat `storage` is the
storage of the target's `executionEnv.address`. The environment/returndata/
logs components are unconstrained until the corresponding ops enter the
supported set. -/
structure StateMatch (yst : YulSemantics.EVM.EvmState) (s : EVM.State) : Prop where
  mem : MemMatch yst.memory s.memory
  stor : ∀ k, conv (yst.storage k)
    = (s.accountMap s.executionEnv.address).storage.get (conv k)
  tstor : ∀ k, conv (yst.transient k)
    = (s.accountMap s.executionEnv.address).tstorage.get (conv k)

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
