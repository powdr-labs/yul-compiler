import YulEvmCompiler.Optimizer.Spec.MemoryGuard
set_option warningAsError true
set_option maxHeartbeats 2000000
/-!
# State-level soundness lemmas for memory spilling

This module contains the representation-independent bottom layer of the spill
simulation.  It proves that compiler-owned word loads and stores are confined
to the reserved interval, and that ordinary EVM built-ins transport across
`ScratchRel` when their dynamic memory footprint satisfies `OpMemorySafe`.

The lexical environment and call-path allocation simulations live above this
file; none of their policy definitions are needed here.
-/

namespace YulEvmCompiler.Optimizer.MemorySpillStateSound

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer

/-! ## Range and byte-array facts -/

theorem rangeOutside_point {base reserved p n i : Nat}
    (h : RangeOutside base reserved p n) (hi : i < n) :
    p + i < base ∨ reserved ≤ p + i := by
  rcases h with hbelow | habove
  · left; omega
  · right; omega

def ReservedUnchanged (base reserved : Nat) (before after : EvmState) : Prop :=
  ∀ i, base ≤ i → i < reserved → after.memory i = before.memory i

theorem ReservedUnchanged.refl (base reserved : Nat) (st : EvmState) :
    ReservedUnchanged base reserved st st := by
  intro i _ _
  rfl

theorem storeWord_reserved {base reserved p : Nat} {v : U256}
    (memory : Nat → UInt8) (hsafe : RangeOutside base reserved p 32) :
    ∀ i, base ≤ i → i < reserved →
      storeWord memory p v i = memory i := by
  intro i hbase hreserved
  simp only [storeWord]
  split
  · rename_i hin
    rcases hsafe with hbelow | habove <;> omega
  · rfl

theorem storeByte_reserved {base reserved p : Nat} {v : U256}
    (memory : Nat → UInt8) (hsafe : RangeOutside base reserved p 1) :
    ∀ i, base ≤ i → i < reserved →
      storeByte memory p v i = memory i := by
  intro i hbase hreserved
  simp only [storeByte]
  split
  · rename_i heq
    rcases hsafe with hbelow | habove <;> omega
  · rfl

theorem copyInto_reserved {base reserved dst src n : Nat} {data : List UInt8}
    (memory : Nat → UInt8) (hsafe : RangeOutside base reserved dst n) :
    ∀ i, base ≤ i → i < reserved →
      copyInto memory dst src n data i = memory i := by
  intro i hbase hreserved
  simp only [copyInto]
  split
  · rename_i hin
    rcases hsafe with hbelow | habove <;> omega
  · rfl

theorem copyWithin_reserved {base reserved dst src n : Nat}
    (memory : Nat → UInt8) (hsafe : RangeOutside base reserved dst n) :
    ∀ i, base ≤ i → i < reserved →
      copyWithin memory dst src n i = memory i := by
  intro i hbase hreserved
  simp only [copyWithin]
  split
  · rename_i hin
    rcases hsafe with hbelow | habove <;> omega
  · rfl

theorem copyReturn_reserved {base reserved dst size : Nat} {data : List UInt8}
    (memory : Nat → UInt8) (hsafe : RangeOutside base reserved dst size) :
    ∀ i, base ≤ i → i < reserved →
      copyReturn memory dst size data i = memory i := by
  intro i hbase hreserved
  simp only [copyReturn]
  split
  · rename_i hin
    have hfull : dst ≤ i ∧ i < dst + size := by omega
    rcases hsafe with hbelow | habove <;> omega
  · rfl

theorem readBytes_eq {base reserved p n : Nat} {left right : EvmState}
    (hrel : ScratchRel base reserved left right)
    (hsafe : RangeOutside base reserved p n) :
    readBytes left.memory p n = readBytes right.memory p n := by
  unfold readBytes
  apply List.map_congr_left
  intro i hi
  exact hrel.memory_eq (p + i)
    (rangeOutside_point hsafe (by simpa using hi))

theorem loadWord_eq {base reserved p : Nat} {left right : EvmState}
    (hrel : ScratchRel base reserved left right)
    (hsafe : RangeOutside base reserved p 32) :
    loadWord left.memory p = loadWord right.memory p := by
  have hread := readBytes_eq hrel hsafe
  have hform (mem : Nat → UInt8) :
      loadWord mem p = (readBytes mem p 32).foldl
        (fun (acc : U256) b => (acc <<< (8 : Nat)) ||| BitVec.ofNat 256 b.toNat) 0 := by
    unfold loadWord readBytes
    rw [List.foldl_map]
  rw [hform left.memory, hform right.memory, hread]

theorem copyInto_memory_eq {base reserved dst src n : Nat}
    {data : List UInt8} {left right : EvmState}
    (hrel : ScratchRel base reserved left right) :
    ∀ i, i < base ∨ reserved ≤ i →
      copyInto left.memory dst src n data i =
        copyInto right.memory dst src n data i := by
  intro i hi
  simp only [copyInto]
  split
  · rfl
  · exact hrel.memory_eq i hi

theorem storeWord_memory_eq {base reserved p : Nat} {v : U256}
    {left right : EvmState} (hrel : ScratchRel base reserved left right) :
    ∀ i, i < base ∨ reserved ≤ i →
      storeWord left.memory p v i = storeWord right.memory p v i := by
  intro i hi
  simp only [storeWord]
  split
  · rfl
  · exact hrel.memory_eq i hi

theorem storeByte_memory_eq {base reserved p : Nat} {v : U256}
    {left right : EvmState} (hrel : ScratchRel base reserved left right) :
    ∀ i, i < base ∨ reserved ≤ i →
      storeByte left.memory p v i = storeByte right.memory p v i := by
  intro i hi
  simp only [storeByte]
  split
  · rfl
  · exact hrel.memory_eq i hi

theorem copyWithin_memory_eq {base reserved dst src n : Nat}
    {left right : EvmState} (hrel : ScratchRel base reserved left right)
    (hsrc : RangeOutside base reserved src n) :
    ∀ i, i < base ∨ reserved ≤ i →
      copyWithin left.memory dst src n i =
        copyWithin right.memory dst src n i := by
  intro i hi
  simp only [copyWithin]
  split
  · rename_i hdst
    apply hrel.memory_eq
    apply rangeOutside_point hsrc
    omega
  · exact hrel.memory_eq i hi

theorem copyReturn_memory_eq {base reserved dst size : Nat}
    {data : List UInt8} {left right : EvmState}
    (hrel : ScratchRel base reserved left right) :
    ∀ i, i < base ∨ reserved ≤ i →
      copyReturn left.memory dst size data i =
        copyReturn right.memory dst size data i := by
  intro i hi
  simp only [copyReturn]
  split
  · rfl
  · exact hrel.memory_eq i hi

/-! ## State constructors that preserve the scratch relation -/

theorem touchMemory_rel {base reserved offset size : Nat} {left right : EvmState}
    (hrel : ScratchRel base reserved left right) :
    ScratchRel base reserved (touchMemory left offset size)
      (touchMemory right offset size) := by
  refine ⟨?_, ?_⟩
  · simpa [touchMemory, observables] using hrel.observables_eq
  · intro i hi
    simpa [touchMemory] using hrel.memory_eq i hi

theorem touchMemory2_rel {base reserved o₁ n₁ o₂ n₂ : Nat}
    {left right : EvmState} (hrel : ScratchRel base reserved left right) :
    ScratchRel base reserved (touchMemory2 left o₁ n₁ o₂ n₂)
      (touchMemory2 right o₁ n₁ o₂ n₂) := by
  exact touchMemory_rel (touchMemory_rel hrel)

theorem mstore_pair_rel {base reserved p : Nat} {v : U256}
    {left right : EvmState} (hrel : ScratchRel base reserved left right) :
    ScratchRel base reserved
      { touchMemory left p 32 with memory := storeWord left.memory p v }
      { touchMemory right p 32 with memory := storeWord right.memory p v } := by
  refine ⟨?_, ?_⟩
  · simpa [touchMemory, observables] using hrel.observables_eq
  · exact storeWord_memory_eq hrel

theorem mstore8_pair_rel {base reserved p : Nat} {v : U256}
    {left right : EvmState} (hrel : ScratchRel base reserved left right) :
    ScratchRel base reserved
      { touchMemory left p 1 with memory := storeByte left.memory p v }
      { touchMemory right p 1 with memory := storeByte right.memory p v } := by
  refine ⟨?_, ?_⟩
  · simpa [touchMemory, observables] using hrel.observables_eq
  · exact storeByte_memory_eq hrel

theorem copyInto_pair_rel {base reserved dst src n : Nat} {data : List UInt8}
    {left right : EvmState} (hrel : ScratchRel base reserved left right) :
    ScratchRel base reserved
      { touchMemory left dst n with memory := copyInto left.memory dst src n data }
      { touchMemory right dst n with memory := copyInto right.memory dst src n data } := by
  refine ⟨?_, ?_⟩
  · simpa [touchMemory, observables] using hrel.observables_eq
  · exact copyInto_memory_eq hrel

theorem copyWithin_pair_rel {base reserved dst src n : Nat}
    {left right : EvmState} (hrel : ScratchRel base reserved left right)
    (hsrc : RangeOutside base reserved src n) :
    ScratchRel base reserved
      { touchMemory2 left dst n src n with memory := copyWithin left.memory dst src n }
      { touchMemory2 right dst n src n with memory := copyWithin right.memory dst src n } := by
  refine ⟨?_, ?_⟩
  · simpa [touchMemory2, touchMemory, observables] using hrel.observables_eq
  · exact copyWithin_memory_eq hrel hsrc

/-! ## Compiler-owned slot operations -/

def slotState (st : EvmState) (slot : Nat) (value : U256) : EvmState :=
  { touchMemory st slot 32 with memory := storeWord st.memory slot value }

theorem slotState_scratch_rel {base reserved slot : Nat} {value : U256}
    (hslot : base ≤ slot ∧ slot + 32 ≤ reserved) (st : EvmState) :
    ScratchRel base reserved st (slotState st slot value) := by
  refine ⟨?_, ?_⟩
  · rfl
  · intro i hi
    simp only [slotState, storeWord]
    split
    · rename_i hin
      rcases hi with hbelow | habove <;> omega
    · rfl

/-- A compiler-owned spill store is read back exactly, with the EVM's
big-endian word encoding. -/
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

private theorem byteAt_eq (value : U256) (i : Nat) :
    byteAt value i = UInt8.ofNat (value.toNat / 256 ^ i % 256) := by
  unfold byteAt
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ (8 * i) = 256 ^ i from by rw [pow_mul]; norm_num,
    UInt8.ofNat_mod_size']

private theorem readBytes_storeWord (memory : Nat → UInt8) (slot : Nat)
    (value : U256) :
    readBytes (storeWord memory slot value) slot 32 =
      (List.range 32).map (fun i => byteAt value (31 - i)) := by
  unfold readBytes
  apply List.map_congr_left
  intro i hi
  have hi' : i < 32 := by simpa using hi
  simp only [storeWord]
  rw [if_pos]
  · congr 1
    omega
  · constructor <;> omega

private theorem decode_prefix (value : U256) : ∀ n, n ≤ 32 →
    ((List.range n).map (fun i => byteAt value (31 - i))).foldl
        (fun acc b => acc * 256 + b.toNat) 0 =
      value.toNat / 256 ^ (32 - n) := by
  intro n hn
  induction n with
  | zero =>
    simp
    symm
    apply Nat.div_eq_of_lt
    simpa [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul] using value.isLt
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_singleton, List.foldl_cons, List.foldl_nil]
    rw [ih (by omega), byteAt_eq]
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))]
    have hsub : 31 - n = 32 - (n + 1) := by omega
    rw [hsub]
    have hpow : 256 ^ (32 - n) = 256 ^ (32 - (n + 1)) * 256 := by
      rw [← Nat.pow_succ]
      congr 1
      omega
    rw [hpow, ← Nat.div_div_eq_div_mul]
    have hdiv := Nat.mod_add_div
      (value.toNat / 256 ^ (32 - (n + 1))) 256
    omega

theorem loadWord_storeWord (memory : Nat → UInt8) (slot : Nat) (value : U256) :
    loadWord (storeWord memory slot value) slot = value := by
  apply BitVec.eq_of_toNat_eq
  have hform (mem : Nat → UInt8) :
      loadWord mem slot = (readBytes mem slot 32).foldl
        (fun (acc : U256) b =>
          (acc <<< (8 : Nat)) ||| BitVec.ofNat 256 b.toNat) 0 := by
    unfold loadWord readBytes
    rw [List.foldl_map]
  rw [hform, readBytes_storeWord]
  rw [bitvec_fold_eq _ 0 (by simp) (by simp)]
  change ((List.range 32).map (fun i => byteAt value (31 - i))).foldl
      (fun acc b => acc * 256 + b.toNat) 0 = value.toNat
  rw [decode_prefix value 32 (by omega)]
  simp

/-- Storing one compiler-owned word leaves a disjoint word load unchanged. -/
theorem loadWord_storeWord_other (memory : Nat → UInt8)
    (writtenSlot untouchedSlot : Nat) (value : U256)
    (hdisjoint : writtenSlot + 32 ≤ untouchedSlot ∨
      untouchedSlot + 32 ≤ writtenSlot) :
    loadWord (storeWord memory writtenSlot value) untouchedSlot =
      loadWord memory untouchedSlot := by
  have hread :
      readBytes (storeWord memory writtenSlot value) untouchedSlot 32 =
        readBytes memory untouchedSlot 32 := by
    unfold readBytes
    apply List.map_congr_left
    intro i hi
    have hi' : i < 32 := by simpa using hi
    simp only [storeWord]
    split
    · rename_i hin
      rcases hdisjoint with hbefore | hafter <;> omega
    · rfl
  have hform (mem : Nat → UInt8) :
      loadWord mem untouchedSlot = (readBytes mem untouchedSlot 32).foldl
        (fun (acc : U256) b =>
          (acc <<< (8 : Nat)) ||| BitVec.ofNat 256 b.toNat) 0 := by
    unfold loadWord readBytes
    rw [List.foldl_map]
  rw [hform, hform, hread]

theorem slotState_load (st : EvmState) (slot : Nat) (value : U256) :
    loadWord (slotState st slot value).memory slot = value := by
  exact loadWord_storeWord st.memory slot value

/-! ## Built-in result relation -/

def ResultRel (base reserved : Nat) :
    BuiltinResult U256 EvmState → BuiltinResult U256 EvmState → Prop
  | .ok xs left, .ok ys right => xs = ys ∧ ScratchRel base reserved left right
  | .halt left, .halt right => ScratchRel base reserved left right
  | _, _ => False

def ResultReservedUnchanged (base reserved : Nat) (before : EvmState) :
    BuiltinResult U256 EvmState → Prop
  | .ok _ after | .halt after => ReservedUnchanged base reserved before after

@[simp] theorem resultReservedUnchanged_ok {base reserved : Nat}
    {before after : EvmState} {values : List U256} :
    ResultReservedUnchanged base reserved before (.ok values after) ↔
      ReservedUnchanged base reserved before after := Iff.rfl

@[simp] theorem resultReservedUnchanged_halt {base reserved : Nat}
    {before after : EvmState} :
    ResultReservedUnchanged base reserved before (.halt after) ↔
      ReservedUnchanged base reserved before after := Iff.rfl

@[simp] theorem resultRel_ok {base reserved : Nat} {xs ys : List U256}
    {left right : EvmState} :
    ResultRel base reserved (.ok xs left) (.ok ys right) ↔
      xs = ys ∧ ScratchRel base reserved left right := Iff.rfl

@[simp] theorem resultRel_halt {base reserved : Nat} {left right : EvmState} :
    ResultRel base reserved (.halt left) (.halt right) ↔
      ScratchRel base reserved left right := Iff.rfl

theorem ResultRel.ok_refl_values {base reserved : Nat} {values : List U256}
    {left right : EvmState} (hrel : ScratchRel base reserved left right) :
    ResultRel base reserved (.ok values left) (.ok values right) :=
  ⟨rfl, hrel⟩

theorem ResultRel.halt_of_rel {base reserved : Nat} {left right : EvmState}
    (hrel : ScratchRel base reserved left right) :
    ResultRel base reserved (.halt left) (.halt right) := hrel

namespace ScratchRel

theorem storage_eq {base reserved : Nat} {left right : EvmState}
    (h : ScratchRel base reserved left right) : left.storage = right.storage := by
  exact congrArg Obs.storage h.observables_eq

theorem transient_eq {base reserved : Nat} {left right : EvmState}
    (h : ScratchRel base reserved left right) : left.transient = right.transient := by
  exact congrArg Obs.transient h.observables_eq

theorem env_eq {base reserved : Nat} {left right : EvmState}
    (h : ScratchRel base reserved left right) : left.env = right.env := by
  exact congrArg Obs.env h.observables_eq

theorem returndata_eq {base reserved : Nat} {left right : EvmState}
    (h : ScratchRel base reserved left right) : left.returndata = right.returndata := by
  exact congrArg Obs.returndata h.observables_eq

theorem logs_eq {base reserved : Nat} {left right : EvmState}
    (h : ScratchRel base reserved left right) : left.logs = right.logs := by
  exact congrArg Obs.logs h.observables_eq

theorem selfdestructs_eq {base reserved : Nat} {left right : EvmState}
    (h : ScratchRel base reserved left right) : left.selfdestructs = right.selfdestructs := by
  exact congrArg Obs.selfdestructs h.observables_eq

theorem halted_eq {base reserved : Nat} {left right : EvmState}
    (h : ScratchRel base reserved left right) : left.halted = right.halted := by
  exact congrArg Obs.halted h.observables_eq

end ScratchRel

theorem finishCall_rel {base reserved : Nat} {left right : EvmState}
    (hrel : ScratchRel base reserved left right) (kind : CallKind)
    (response : CallResponse) (inputOffset inputSize outputOffset outputSize : Nat) :
    ScratchRel base reserved
      (finishCall kind left response inputOffset inputSize outputOffset outputSize)
      (finishCall kind right response inputOffset inputSize outputOffset outputSize) := by
  refine ⟨?_, copyReturn_memory_eq hrel⟩
  unfold finishCall
  split <;>
    simp only [CallWorld.install, touchMemory2, touchMemory, observables] <;>
    simp only [MemorySpillStateSound.ScratchRel.storage_eq hrel,
      MemorySpillStateSound.ScratchRel.transient_eq hrel,
      MemorySpillStateSound.ScratchRel.env_eq hrel,
      MemorySpillStateSound.ScratchRel.logs_eq hrel,
      MemorySpillStateSound.ScratchRel.selfdestructs_eq hrel,
      MemorySpillStateSound.ScratchRel.halted_eq hrel]

theorem finishCall_reserved {base reserved : Nat} (st : EvmState)
    (kind : CallKind) (response : CallResponse)
    (inputOffset inputSize outputOffset outputSize : Nat)
    (houtput : RangeOutside base reserved outputOffset outputSize) :
    ReservedUnchanged base reserved st
      (finishCall kind st response inputOffset inputSize outputOffset outputSize) := by
  intro i hbase hreserved
  exact copyReturn_reserved st.memory houtput i hbase hreserved

theorem finishCreate_rel {base reserved : Nat} {left right : EvmState}
    (hrel : ScratchRel base reserved left right) (response : CreateResponse)
    (offset size : Nat) :
    ScratchRel base reserved (finishCreate left response offset size)
      (finishCreate right response offset size) := by
  refine ⟨?_, ?_⟩
  · unfold finishCreate
    split <;>
      simp only [CallWorld.install, touchMemory, observables] <;>
      simp only [MemorySpillStateSound.ScratchRel.storage_eq hrel,
        MemorySpillStateSound.ScratchRel.transient_eq hrel,
        MemorySpillStateSound.ScratchRel.env_eq hrel,
        MemorySpillStateSound.ScratchRel.logs_eq hrel,
        MemorySpillStateSound.ScratchRel.selfdestructs_eq hrel,
        MemorySpillStateSound.ScratchRel.halted_eq hrel]
  · intro i hi
    unfold finishCreate
    split <;> simp only [CallWorld.install, touchMemory]
    · exact hrel.memory_eq i hi
    · exact hrel.memory_eq i hi

theorem finishCreate_reserved {base reserved : Nat} (st : EvmState)
    (response : CreateResponse) (offset size : Nat) :
    ReservedUnchanged base reserved st (finishCreate st response offset size) := by
  intro i _ _
  unfold finishCreate
  split <;> simp only [CallWorld.install, touchMemory]

theorem externalCall_transport {calls : ExternalCalls} {base reserved : Nat}
    (hinsensitive : CallsScratchInsensitive calls base reserved)
    {left right : EvmState} (hrel : ScratchRel base reserved left right)
    (kind : CallKind) (gas target value inputOffset inputSize outputOffset outputSize : U256)
    {leftResult : BuiltinResult U256 EvmState}
    (hinput : RangeOutside base reserved inputOffset.toNat inputSize.toNat)
    (hcall : externalCall calls kind gas target value inputOffset inputSize
      outputOffset outputSize left leftResult) :
    ∃ rightResult,
      externalCall calls kind gas target value inputOffset inputSize
        outputOffset outputSize right rightResult ∧
      ResultRel base reserved leftResult rightResult := by
  rcases hcall with ⟨response, hresponse, rfl⟩
  have hbytes := readBytes_eq hrel hinput
  rw [hbytes] at hresponse
  have hresponse' := (hinsensitive _ _ _ response hrel).mp hresponse
  refine ⟨.ok [response.flag]
      (finishCall kind right response inputOffset.toNat inputSize.toNat
        outputOffset.toNat outputSize.toNat), ?_, ?_⟩
  · exact ⟨response, hresponse', rfl⟩
  · exact ResultRel.ok_refl_values (finishCall_rel hrel kind response
      inputOffset.toNat inputSize.toNat outputOffset.toNat outputSize.toNat)

theorem externalCall_reserved {calls : ExternalCalls} {base reserved : Nat}
    {st : EvmState} (kind : CallKind)
    (gas target value inputOffset inputSize outputOffset outputSize : U256)
    {result : BuiltinResult U256 EvmState}
    (houtput : RangeOutside base reserved outputOffset.toNat outputSize.toNat)
    (hcall : externalCall calls kind gas target value inputOffset inputSize
      outputOffset outputSize st result) :
    ResultReservedUnchanged base reserved st result := by
  rcases hcall with ⟨response, _, rfl⟩
  exact finishCall_reserved st kind response inputOffset.toNat inputSize.toNat
    outputOffset.toNat outputSize.toNat houtput

theorem externalCreate_transport {creates : ExternalCreates} {base reserved : Nat}
    (hinsensitive : CreatesScratchInsensitive creates base reserved)
    {left right : EvmState} (hrel : ScratchRel base reserved left right)
    (kind : CreateKind) (value offset size : U256) (salt : Option U256)
    {leftResult : BuiltinResult U256 EvmState}
    (hinput : RangeOutside base reserved offset.toNat size.toNat)
    (hcreate : externalCreate creates kind value offset size salt left leftResult) :
    ∃ rightResult,
      externalCreate creates kind value offset size salt right rightResult ∧
      ResultRel base reserved leftResult rightResult := by
  rcases hcreate with ⟨response, hresponse, rfl⟩
  have hbytes := readBytes_eq hrel hinput
  rw [hbytes] at hresponse
  have hresponse' := (hinsensitive _ _ _ response hrel).mp hresponse
  refine ⟨.ok [response.result]
      (finishCreate right response offset.toNat size.toNat), ?_, ?_⟩
  · exact ⟨response, hresponse', rfl⟩
  · exact ResultRel.ok_refl_values
      (finishCreate_rel hrel response offset.toNat size.toNat)

theorem externalCreate_reserved {creates : ExternalCreates} {base reserved : Nat}
    {st : EvmState} (kind : CreateKind) (value offset size : U256)
    (salt : Option U256) {result : BuiltinResult U256 EvmState}
    (hcreate : externalCreate creates kind value offset size salt st result) :
    ResultReservedUnchanged base reserved st result := by
  rcases hcreate with ⟨response, _, rfl⟩
  exact finishCreate_reserved st response offset.toNat size.toNat

theorem halted_rel {base reserved : Nat} {left right : EvmState}
    (hrel : ScratchRel base reserved left right) (kind : HaltKind)
    {leftData rightData : List UInt8} (hdata : leftData = rightData) :
    ScratchRel base reserved
      { left with halted := some (kind, leftData) }
      { right with halted := some (kind, rightData) } := by
  refine ⟨?_, ?_⟩
  · simp only [observables]
    rw [MemorySpillStateSound.ScratchRel.storage_eq hrel,
      MemorySpillStateSound.ScratchRel.transient_eq hrel,
      MemorySpillStateSound.ScratchRel.env_eq hrel,
      MemorySpillStateSound.ScratchRel.returndata_eq hrel,
      MemorySpillStateSound.ScratchRel.logs_eq hrel,
      MemorySpillStateSound.ScratchRel.selfdestructs_eq hrel, hdata]
  · intro i hi
    exact hrel.memory_eq i hi

theorem sstore_rel {base reserved : Nat} {left right : EvmState}
    (hrel : ScratchRel base reserved left right) (key value : U256) :
    ScratchRel base reserved
      { left with
        storage := upd left.storage key value
        env := { left.env with
          storageOf := updAccount left.env.storageOf left.env.address key value } }
      { right with
        storage := upd right.storage key value
        env := { right.env with
          storageOf := updAccount right.env.storageOf right.env.address key value } } := by
  refine ⟨?_, ?_⟩
  · simp only [observables]
    rw [MemorySpillStateSound.ScratchRel.storage_eq hrel,
      MemorySpillStateSound.ScratchRel.transient_eq hrel,
      MemorySpillStateSound.ScratchRel.env_eq hrel,
      MemorySpillStateSound.ScratchRel.returndata_eq hrel,
      MemorySpillStateSound.ScratchRel.logs_eq hrel,
      MemorySpillStateSound.ScratchRel.selfdestructs_eq hrel,
      MemorySpillStateSound.ScratchRel.halted_eq hrel]
  · intro i hi
    exact hrel.memory_eq i hi

theorem tstore_rel {base reserved : Nat} {left right : EvmState}
    (hrel : ScratchRel base reserved left right) (key value : U256) :
    ScratchRel base reserved
      { left with
        transient := upd left.transient key value
        env := { left.env with
          transientOf := updAccount left.env.transientOf left.env.address key value } }
      { right with
        transient := upd right.transient key value
        env := { right.env with
          transientOf := updAccount right.env.transientOf right.env.address key value } } := by
  refine ⟨?_, ?_⟩
  · simp only [observables]
    rw [MemorySpillStateSound.ScratchRel.storage_eq hrel,
      MemorySpillStateSound.ScratchRel.transient_eq hrel,
      MemorySpillStateSound.ScratchRel.env_eq hrel,
      MemorySpillStateSound.ScratchRel.returndata_eq hrel,
      MemorySpillStateSound.ScratchRel.logs_eq hrel,
      MemorySpillStateSound.ScratchRel.selfdestructs_eq hrel,
      MemorySpillStateSound.ScratchRel.halted_eq hrel]
  · intro i hi
    exact hrel.memory_eq i hi

theorem appendLog_rel {base reserved : Nat} {left right : EvmState}
    (hrel : ScratchRel base reserved left right) (topics : List U256) (p n : U256)
    (hsafe : RangeOutside base reserved p.toNat n.toNat) :
    ScratchRel base reserved (appendLog left topics p n) (appendLog right topics p n) := by
  have hbytes := readBytes_eq hrel hsafe
  refine ⟨?_, ?_⟩
  · simp only [appendLog, touchMemory, observables]
    rw [MemorySpillStateSound.ScratchRel.storage_eq hrel,
      MemorySpillStateSound.ScratchRel.transient_eq hrel,
      MemorySpillStateSound.ScratchRel.env_eq hrel,
      MemorySpillStateSound.ScratchRel.returndata_eq hrel,
      MemorySpillStateSound.ScratchRel.logs_eq hrel,
      MemorySpillStateSound.ScratchRel.selfdestructs_eq hrel,
      MemorySpillStateSound.ScratchRel.halted_eq hrel, hbytes]
  · intro i hi
    exact hrel.memory_eq i hi

theorem finishSelfdestruct_rel {base reserved : Nat} {left right : EvmState}
    (hrel : ScratchRel base reserved left right) (beneficiary : U256) :
    ScratchRel base reserved (finishSelfdestruct left beneficiary)
      (finishSelfdestruct right beneficiary) := by
  refine ⟨?_, ?_⟩
  · unfold finishSelfdestruct
    simp only [observables]
    rw [MemorySpillStateSound.ScratchRel.storage_eq hrel,
      MemorySpillStateSound.ScratchRel.transient_eq hrel,
      MemorySpillStateSound.ScratchRel.env_eq hrel,
      MemorySpillStateSound.ScratchRel.returndata_eq hrel,
      MemorySpillStateSound.ScratchRel.logs_eq hrel,
      MemorySpillStateSound.ScratchRel.selfdestructs_eq hrel]
  · intro i hi
    exact hrel.memory_eq i hi

theorem guardStatic_transport {base reserved : Nat} {left right : EvmState}
    {leftAct rightAct leftResult : BuiltinResult U256 EvmState}
    (hrel : ScratchRel base reserved left right)
    (hact : ResultRel base reserved leftAct rightAct)
    (hguard : guardStatic left leftAct = some leftResult) :
    ∃ rightResult, guardStatic right rightAct = some rightResult ∧
      ResultRel base reserved leftResult rightResult := by
  have hstatic := congrArg ExecEnv.static
    (MemorySpillStateSound.ScratchRel.env_eq hrel)
  unfold guardStatic at hguard ⊢
  cases hs : left.env.static
  · have hrs : right.env.static = false := by
      rw [← hstatic]
      exact hs
    simp only [hs, hrs, Bool.false_eq_true, ↓reduceIte,
      Option.some.injEq] at hguard ⊢
    subst leftResult
    exact ⟨rightAct, rfl, hact⟩
  · have hrs : right.env.static = true := by
      rw [← hstatic]
      exact hs
    simp only [hs, hrs, ↓reduceIte, Option.some.injEq] at hguard ⊢
    subst leftResult
    exact ⟨_, rfl, halted_rel hrel .staticViolation rfl⟩

/-! ## Transport of ordinary local built-ins -/

/-- `stepOp` is the ordinary deterministic part of the open-world dialect.
Under a safe dynamic footprint it produces the same values/halt kind and
states related by `ScratchRel`.  Call/create/gas cases are impossible because
they are deliberately absent from `stepOp`. -/
theorem stepOp_transport {base reserved : Nat} {op : Op} {args : List U256}
    {left right : EvmState} {leftResult : BuiltinResult U256 EvmState}
    (hrel : ScratchRel base reserved left right)
    (hsafe : OpMemorySafe base reserved op args)
    (hstep : stepOp op args left = some leftResult) :
    ∃ rightResult, stepOp op args right = some rightResult ∧
      ResultRel base reserved leftResult rightResult := by
  have hstorage := MemorySpillStateSound.ScratchRel.storage_eq hrel
  have htransient := MemorySpillStateSound.ScratchRel.transient_eq hrel
  have henv := MemorySpillStateSound.ScratchRel.env_eq hrel
  have hreturndata := MemorySpillStateSound.ScratchRel.returndata_eq hrel
  have hlogs := MemorySpillStateSound.ScratchRel.logs_eq hrel
  have hselfdestructs := MemorySpillStateSound.ScratchRel.selfdestructs_eq hrel
  have hhalted := MemorySpillStateSound.ScratchRel.halted_eq hrel
  cases op <;>
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, rest⟩⟩⟩⟩⟩⟩⟩ <;>
    simp_all [stepOp, un, bin, ter, rd0, rd1, OpMemorySafe]
  all_goals try { exact hstep ▸ ResultRel.ok_refl_values hrel }
  case keccak256.cons.cons.nil =>
    rw [← hstep]
    exact ⟨congrArg (fun bytes => [right.env.keccakOf bytes])
        (readBytes_eq hrel hsafe),
      touchMemory_rel hrel⟩
  case mload.cons.nil =>
    rw [← hstep]
    exact ⟨congrArg (fun word => [word]) (loadWord_eq hrel hsafe),
      touchMemory_rel hrel⟩
  case mstore.cons.cons.nil =>
    rw [← hstep]
    exact ResultRel.ok_refl_values (mstore_pair_rel hrel)
  case mstore8.cons.cons.nil =>
    rw [← hstep]
    exact ResultRel.ok_refl_values (mstore8_pair_rel hrel)
  case mcopy.cons.cons.cons.nil =>
    rw [← hstep]
    exact ResultRel.ok_refl_values (copyWithin_pair_rel hrel hsafe.2)
  case sstore.cons.cons.nil =>
    rw [← hstorage, ← htransient, ← henv, ← hreturndata, ← hlogs,
      ← hselfdestructs, ← hhalted] at hstep
    exact guardStatic_transport hrel
      (ResultRel.ok_refl_values (sstore_rel hrel a b)) hstep
  case tstore.cons.cons.nil =>
    rw [← hstorage, ← htransient, ← henv, ← hreturndata, ← hlogs,
      ← hselfdestructs, ← hhalted] at hstep
    exact guardStatic_transport hrel
      (ResultRel.ok_refl_values (tstore_rel hrel a b)) hstep
  case calldatacopy.cons.cons.cons.nil =>
    rw [← hstep]
    exact ResultRel.ok_refl_values (copyInto_pair_rel hrel)
  case codecopy.cons.cons.cons.nil =>
    rw [← hstep]
    exact ResultRel.ok_refl_values (copyInto_pair_rel hrel)
  case returndatacopy.cons.cons.cons.nil =>
    by_cases hbound : b.toNat + c.toNat ≤ right.returndata.length
    · simp only [hbound, ↓reduceIte, Option.some.injEq] at hstep ⊢
      subst leftResult
      exact ⟨_, rfl, ResultRel.ok_refl_values (copyInto_pair_rel hrel)⟩
    · simp only [hbound, ↓reduceIte, Option.some.injEq] at hstep ⊢
      subst leftResult
      exact ⟨_, rfl, ⟨rfl, hrel.memory_eq⟩⟩
  case datacopy.cons.cons.cons.nil =>
    rw [← hstep]
    exact ResultRel.ok_refl_values (copyInto_pair_rel hrel)
  case extcodecopy.cons.cons.cons.cons.nil =>
    rw [← hstep]
    exact ResultRel.ok_refl_values (copyInto_pair_rel hrel)
  case log0.cons.cons.nil =>
    exact guardStatic_transport hrel
      (ResultRel.ok_refl_values (appendLog_rel hrel [] a b hsafe)) hstep
  case log1.cons.cons.cons.nil =>
    exact guardStatic_transport hrel
      (ResultRel.ok_refl_values (appendLog_rel hrel [c] a b hsafe)) hstep
  case log2.cons.cons.cons.cons.nil =>
    exact guardStatic_transport hrel
      (ResultRel.ok_refl_values (appendLog_rel hrel [c, d] a b hsafe)) hstep
  case log3.cons.cons.cons.cons.cons.nil =>
    exact guardStatic_transport hrel
      (ResultRel.ok_refl_values (appendLog_rel hrel [c, d, e] a b hsafe)) hstep
  case log4.cons.cons.cons.cons.cons.cons.nil =>
    exact guardStatic_transport hrel
      (ResultRel.ok_refl_values (appendLog_rel hrel [c, d, e, f] a b hsafe)) hstep
  case selfdestruct.cons.nil =>
    exact guardStatic_transport hrel
      (ResultRel.halt_of_rel (finishSelfdestruct_rel hrel a)) hstep
  case stop.nil =>
    rw [← hstep]
    exact ResultRel.halt_of_rel ⟨rfl, hrel.memory_eq⟩
  case ret.cons.cons.nil =>
    rw [← hstep]
    exact ResultRel.halt_of_rel
      (halted_rel (touchMemory_rel hrel) .ret (readBytes_eq hrel hsafe))
  case revert.cons.cons.nil =>
    rw [← hstep]
    exact ResultRel.halt_of_rel
      (halted_rel (touchMemory_rel hrel) .revert (readBytes_eq hrel hsafe))
  case invalid.nil =>
    rw [← hstep]
    exact ResultRel.halt_of_rel ⟨rfl, hrel.memory_eq⟩

theorem stepOp_reserved {base reserved : Nat} {op : Op} {args : List U256}
    {st : EvmState} {result : BuiltinResult U256 EvmState}
    (hsafe : OpMemorySafe base reserved op args)
    (hstep : stepOp op args st = some result) :
    ResultReservedUnchanged base reserved st result := by
  cases result <;> cases op <;>
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, rest⟩⟩⟩⟩⟩⟩⟩ <;>
    simp_all [stepOp, un, bin, ter, rd0, rd1, OpMemorySafe,
      ResultReservedUnchanged, ReservedUnchanged]
  case ok.keccak256.cons.cons.nil =>
    rw [← hstep.2]
    intro i _ _
    rfl
  case ok.mload.cons.nil =>
    rw [← hstep.2]
    intro i _ _
    rfl
  case ok.mstore.cons.cons.nil =>
    rw [← hstep.2]
    exact storeWord_reserved st.memory hsafe
  case ok.mstore8.cons.cons.nil =>
    rw [← hstep.2]
    exact storeByte_reserved st.memory hsafe
  case ok.mcopy.cons.cons.cons.nil =>
    rw [← hstep.2]
    exact copyWithin_reserved st.memory hsafe.1
  case ok.calldatacopy.cons.cons.cons.nil =>
    rw [← hstep.2]
    exact copyInto_reserved st.memory hsafe
  case ok.codecopy.cons.cons.cons.nil =>
    rw [← hstep.2]
    exact copyInto_reserved st.memory hsafe
  case ok.datacopy.cons.cons.cons.nil =>
    rw [← hstep.2]
    exact copyInto_reserved st.memory hsafe
  case ok.extcodecopy.cons.cons.cons.cons.nil =>
    rw [← hstep.2]
    exact copyInto_reserved st.memory hsafe
  case ok.returndatacopy.cons.cons.cons.nil =>
    split at hstep <;> simp_all
    rw [← hstep.2]
    exact copyInto_reserved st.memory hsafe
  case halt.returndatacopy.cons.cons.cons.nil =>
    split at hstep <;> simp_all
    rw [← hstep]
    intro i _ _
    rfl
  case ok.sstore.cons.cons.nil | ok.tstore.cons.cons.nil |
      halt.sstore.cons.cons.nil | halt.tstore.cons.cons.nil =>
    simp only [guardStatic] at hstep
    split at hstep <;> simp_all
    all_goals try { rw [← hstep.2]; intro i _ _; rfl }
    all_goals try { rw [← hstep]; intro i _ _; rfl }
  case ok.log0.cons.cons.nil | ok.log1.cons.cons.cons.nil |
      ok.log2.cons.cons.cons.cons.nil | ok.log3.cons.cons.cons.cons.cons.nil |
      ok.log4.cons.cons.cons.cons.cons.cons.nil |
      halt.log0.cons.cons.nil | halt.log1.cons.cons.cons.nil |
      halt.log2.cons.cons.cons.cons.nil | halt.log3.cons.cons.cons.cons.cons.nil |
      halt.log4.cons.cons.cons.cons.cons.cons.nil =>
    simp only [guardStatic] at hstep
    split at hstep <;> simp_all [appendLog, touchMemory]
    all_goals try { rw [← hstep.2]; intro i _ _; rfl }
    all_goals try { rw [← hstep]; intro i _ _; rfl }
  case halt.selfdestruct.cons.nil =>
    simp only [guardStatic] at hstep
    split at hstep <;> simp_all [finishSelfdestruct]
    all_goals try { rw [← hstep]; intro i _ _; rfl }
  case ok.selfdestruct.cons.nil =>
    simp only [guardStatic] at hstep
    split at hstep <;> simp_all
  case halt.stop.nil | halt.ret.cons.cons.nil | halt.revert.cons.cons.nil |
      halt.invalid.nil =>
    rw [← hstep]
    intro i _ _
    rfl

/-- The deterministic local portion of `builtinWithExternal`. -/
def OrdinaryLocal : Op → Prop
  | .gas | .call | .callcode | .delegatecall | .staticcall | .create | .create2 => False
  | _ => True

theorem builtinWithExternal_local_iff {calls : ExternalCalls}
    {creates : ExternalCreates} {op : Op} {args : List U256} {st : EvmState}
    {result : BuiltinResult U256 EvmState} (hlocal : OrdinaryLocal op) :
    builtinWithExternal calls creates op args st result ↔
      stepOp op args st = some result := by
  cases op <;> simp_all [OrdinaryLocal, builtinWithExternal]

/-- Transport for a guarded ordinary local built-in.  The guarded relation on
the right retains the same dynamically checked `OpMemorySafe` witness. -/
theorem guarded_local_builtin_transport {calls : ExternalCalls}
    {creates : ExternalCreates} {base reserved : Nat} {op : Op}
    {args : List U256} {left right : EvmState}
    {leftResult : BuiltinResult U256 EvmState}
    (hlocal : OrdinaryLocal op)
    (hrel : ScratchRel base reserved left right)
    (hleft : (guardedEvm calls creates base reserved).Builtin
      op args left leftResult) :
    ∃ rightResult,
      (guardedEvm calls creates base reserved).Builtin op args right rightResult ∧
        ResultRel base reserved leftResult rightResult := by
  rcases hleft with ⟨hbuiltin, hsafe⟩
  have hstep : stepOp op args left = some leftResult :=
    (builtinWithExternal_local_iff hlocal).mp hbuiltin
  obtain ⟨rightResult, hright, hresult⟩ :=
    stepOp_transport hrel hsafe hstep
  refine ⟨rightResult, ⟨?_, hsafe⟩, hresult⟩
  exact (builtinWithExternal_local_iff hlocal).mpr hright

/-- Every guarded built-in transports across scratch-equivalent states when
the external call/create relations cannot inspect compiler-owned bytes.  The
`gas()` oracle is matched by choosing the same arbitrary word. -/
theorem guarded_builtin_transport {calls : ExternalCalls}
    {creates : ExternalCreates} {base reserved : Nat} {op : Op}
    {args : List U256} {left right : EvmState}
    {leftResult : BuiltinResult U256 EvmState}
    (hexternals : GuardedExternals calls creates base reserved)
    (hrel : ScratchRel base reserved left right)
    (hleft : (guardedEvm calls creates base reserved).Builtin
      op args left leftResult) :
    ∃ rightResult,
      (guardedEvm calls creates base reserved).Builtin op args right rightResult ∧
        ResultRel base reserved leftResult rightResult := by
  rcases hleft with ⟨hbuiltin, hsafe⟩
  by_cases hlocal : OrdinaryLocal op
  · exact guarded_local_builtin_transport hlocal hrel ⟨hbuiltin, hsafe⟩
  · cases op <;>
      rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, rest⟩⟩⟩⟩⟩⟩⟩ <;>
      simp_all [OrdinaryLocal, builtinWithExternal, OpMemorySafe]
    case neg.gas.nil =>
      rcases hbuiltin with ⟨gas, rfl⟩
      exact ⟨gas, ResultRel.ok_refl_values hrel⟩
    case neg.call.cons.cons.cons.cons.cons.cons.cons =>
      cases rest <;> simp_all
      have hstatic : left.env.static = right.env.static :=
        congrArg ExecEnv.static (ScratchRel.env_eq hrel)
      split at hbuiltin
      · rename_i hl
        have hr : right.env.static = true ∧ ¬c = (0 : U256) := by
          rw [← hstatic]
          exact hl
        subst leftResult
        refine ⟨.halt { right with halted := some (.staticViolation, []) }, ?_, ?_⟩
        split
        · rfl
        · contradiction
        exact ResultRel.halt_of_rel (halted_rel hrel .staticViolation rfl)
      · rename_i hl
        have hr : ¬(right.env.static = true ∧ ¬c = (0 : U256)) := by
          rw [← hstatic]
          exact hl
        obtain ⟨rightResult, hcall, hresult⟩ :=
          externalCall_transport hexternals.calls_insensitive hrel
            .call a b c d e f g hsafe.1 hbuiltin
        refine ⟨rightResult, ?_, hresult⟩
        split
        · contradiction
        · exact hcall
    case neg.callcode.cons.cons.cons.cons.cons.cons.cons =>
      cases rest <;> simp_all
      exact externalCall_transport hexternals.calls_insensitive hrel
        .callcode a b c d e f g hsafe.1 hbuiltin
    case neg.delegatecall.cons.cons.cons.cons.cons.cons.nil =>
      simpa [ScratchRel.env_eq hrel] using
        externalCall_transport hexternals.calls_insensitive hrel
          .delegatecall a b left.env.callvalue c d e f hsafe.1 hbuiltin
    case neg.staticcall.cons.cons.cons.cons.cons.cons.nil =>
      exact externalCall_transport hexternals.calls_insensitive hrel
        .staticcall a b 0 c d e f hsafe.1 hbuiltin
    case neg.create.cons.cons.cons.nil =>
      have hstatic : left.env.static = right.env.static :=
        congrArg ExecEnv.static (ScratchRel.env_eq hrel)
      by_cases h : left.env.static = true
      · have hr : right.env.static = true := by simpa [← hstatic] using h
        rw [if_pos h] at hbuiltin
        simp only [if_pos hr]
        subst leftResult
        exact ⟨_, rfl, halted_rel hrel .staticViolation rfl⟩
      · have hr : ¬right.env.static = true := by simpa [← hstatic] using h
        rw [if_neg h] at hbuiltin
        simp only [if_neg hr]
        exact externalCreate_transport hexternals.creates_insensitive hrel
          .create a b c none hsafe hbuiltin
    case neg.create2.cons.cons.cons.cons.nil =>
      have hstatic : left.env.static = right.env.static :=
        congrArg ExecEnv.static (ScratchRel.env_eq hrel)
      by_cases h : left.env.static = true
      · have hr : right.env.static = true := by simpa [← hstatic] using h
        rw [if_pos h] at hbuiltin
        simp only [if_pos hr]
        subst leftResult
        exact ⟨_, rfl, halted_rel hrel .staticViolation rfl⟩
      · have hr : ¬right.env.static = true := by simpa [← hstatic] using h
        rw [if_neg h] at hbuiltin
        simp only [if_neg hr]
        exact externalCreate_transport hexternals.creates_insensitive hrel
          .create2 a b c (some d) hsafe hbuiltin

theorem guarded_builtin_reserved {calls : ExternalCalls}
    {creates : ExternalCreates} {base reserved : Nat} {op : Op}
    {args : List U256} {st : EvmState}
    {result : BuiltinResult U256 EvmState}
    (hbuiltin : (guardedEvm calls creates base reserved).Builtin op args st result) :
    ResultReservedUnchanged base reserved st result := by
  rcases hbuiltin with ⟨hbuiltin, hsafe⟩
  by_cases hlocal : OrdinaryLocal op
  · exact stepOp_reserved hsafe
      ((builtinWithExternal_local_iff hlocal).mp hbuiltin)
  · cases op <;>
      rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, rest⟩⟩⟩⟩⟩⟩⟩ <;>
      simp_all [OrdinaryLocal, builtinWithExternal, OpMemorySafe]
    case neg.gas.nil =>
      rcases hbuiltin with ⟨gas, rfl⟩
      exact ReservedUnchanged.refl base reserved st
    case neg.call.cons.cons.cons.cons.cons.cons.cons =>
      cases rest <;> simp_all
      split at hbuiltin
      ·
        subst result
        exact ReservedUnchanged.refl base reserved st
      ·
        exact externalCall_reserved .call a b c d e f g hsafe.2 hbuiltin
    case neg.callcode.cons.cons.cons.cons.cons.cons.cons =>
      cases rest <;> simp_all
      exact externalCall_reserved .callcode a b c d e f g hsafe.2 hbuiltin
    case neg.delegatecall.cons.cons.cons.cons.cons.cons.nil =>
      exact externalCall_reserved .delegatecall a b st.env.callvalue c d e f
        hsafe.2 hbuiltin
    case neg.staticcall.cons.cons.cons.cons.cons.cons.nil =>
      exact externalCall_reserved .staticcall a b 0 c d e f hsafe.2 hbuiltin
    case neg.create.cons.cons.cons.nil =>
      split at hbuiltin
      ·
        subst result
        exact ReservedUnchanged.refl base reserved st
      ·
        exact externalCreate_reserved .create a b c none hbuiltin
    case neg.create2.cons.cons.cons.cons.nil =>
      split at hbuiltin
      ·
        subst result
        exact ReservedUnchanged.refl base reserved st
      ·
        exact externalCreate_reserved .create2 a b c (some d) hbuiltin

end YulEvmCompiler.Optimizer.MemorySpillStateSound
