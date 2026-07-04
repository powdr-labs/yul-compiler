import YulEvmCompiler.OpTable
import Batteries.Data.ByteArray

/-!
# YulEvmCompiler.Decode

Layout lemmas: decoding assembled code at instruction boundaries.

All `ByteArray` index arithmetic of the compiler proof is isolated here. The
two main lemmas say that at position `pre.length` of
`mkCode (pre ++ i.bytes ++ post)`, `Decode.decodeAt` returns exactly
instruction `i`'s operation (and immediate, for `push`); a third gives the
implicit `STOP` past the end of the code.
-/

namespace YulEvmCompiler

open EvmSemantics
open EvmSemantics.EVM

/-- Build the executable `ByteArray` from a byte list. -/
def mkCode (l : List UInt8) : ByteArray := ⟨l.toArray⟩

@[simp] theorem size_mkCode (l : List UInt8) : (mkCode l).size = l.length := by
  simp [mkCode, ByteArray.size]

/-! ### `ByteArray.toList` bridge

Core's `ByteArray.toList` is a tail-recursive loop; we relate it to
`b.data.toList` once and never look at the loop again. -/

private theorem get!_eq (bs : Array UInt8) (i : Nat) (hi : i < bs.toList.length) :
    ByteArray.get! ⟨bs⟩ i = bs.toList[i] := by
  show bs[i]!  = _
  have hib : i < bs.size := by simpa using hi
  rw [getElem!_pos bs i hib]
  exact (Array.getElem_toList hib).symm

private theorem toList_loop_eq (bs : Array UInt8) :
    ∀ n i r, bs.size - i ≤ n →
      ByteArray.toList.loop ⟨bs⟩ i r = r.reverse ++ bs.toList.drop i := by
  intro n
  induction n with
  | zero =>
    intro i r h
    unfold ByteArray.toList.loop
    rw [if_neg (by show ¬ i < bs.size; omega)]
    rw [List.drop_eq_nil_of_le (by rw [Array.length_toList]; omega)]
    rw [List.append_nil]
  | succ n ih =>
    intro i r h
    unfold ByteArray.toList.loop
    by_cases hi : (⟨bs⟩ : ByteArray).size > i
    · rw [if_pos hi]
      rw [ih (i + 1) _ (by show bs.size - (i+1) ≤ n; have : bs.size > i := hi; omega)]
      have hi' : i < bs.toList.length := by
        rw [Array.length_toList]; exact hi
      rw [List.drop_eq_getElem_cons hi', get!_eq bs i hi']
      simp
    · rw [if_neg hi]
      have hle : bs.toList.length ≤ i := by
        rw [Array.length_toList]
        exact Nat.le_of_not_lt hi
      rw [List.drop_eq_nil_of_le hle, List.append_nil]

theorem ByteArray.toList_eq_data (b : ByteArray) : b.toList = b.data.toList := by
  obtain ⟨bs⟩ := b
  show ByteArray.toList.loop ⟨bs⟩ 0 [] = _
  rw [toList_loop_eq bs bs.size 0 [] (by omega)]
  simp

@[simp] theorem toList_mkCode (l : List UInt8) : (mkCode l).toList = l := by
  rw [ByteArray.toList_eq_data]
  simp [mkCode]

theorem getElem_mkCode (l : List UInt8) (i : Nat) (h : i < (mkCode l).size) :
    (mkCode l)[i] = l[i]'(by simpa using h) := by
  simp [mkCode, ByteArray.getElem_eq_data_getElem]

/-- Operations that carry no immediate bytes and are not one of the
immediate-decoding constructor groups (`Push`/`DupN`/`SwapN`/`Exchange`). -/
def plainOp : Operation → Prop
  | .Push _ | .DupN _ | .SwapN _ | .Exchange _ => False
  | _ => True

/-- Reading past the end of the code decodes as the implicit `STOP`. -/
theorem decodeAt_past_end (l : List UInt8) (pc : Nat) (h : l.length ≤ pc) :
    Decode.decodeAt (mkCode l) pc = some (.STOP, none) := by
  unfold Decode.decodeAt
  rw [dif_neg (by simpa using Nat.not_lt.mpr h)]

/-- The byte at the start of an embedded instruction. -/
private theorem getElem_boundary (pre post : List UInt8) (b : UInt8) (rest : List UInt8)
    (h : pre.length < (mkCode (pre ++ (b :: rest) ++ post)).size) :
    (mkCode (pre ++ (b :: rest) ++ post))[pre.length] = b := by
  have hlen : pre.length < (pre ++ (b :: rest) ++ post).length := by simp
  have h? : (pre ++ (b :: rest) ++ post)[pre.length]? = some b := by
    rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]
    simp
  have hL : (pre ++ (b :: rest) ++ post)[pre.length]'hlen = b := by
    have h1 : (pre ++ (b :: rest) ++ post)[pre.length]?
        = some ((pre ++ (b :: rest) ++ post)[pre.length]'hlen) :=
      List.getElem?_eq_getElem hlen
    exact Option.some.inj (h1.symm.trans h?)
  simp only [mkCode, ByteArray.getElem_eq_getElem_data, List.getElem_toArray]
  exact hL

/-- Decoding at the start of an embedded single-byte instruction. -/
theorem decodeAt_op (pre post : List UInt8) (o : Operation)
    (hb : Decode.opcodeOf (Instr.opByte o) = some o) (hp : plainOp o) :
    Decode.decodeAt (mkCode (pre ++ (Instr.op o).bytes ++ post)) pre.length
      = some (o, none) := by
  show Decode.decodeAt (mkCode (pre ++ (Instr.opByte o :: []) ++ post)) pre.length = _
  have hsz : pre.length < (mkCode (pre ++ (Instr.opByte o :: []) ++ post)).size := by
    simp
  unfold Decode.decodeAt
  rw [dif_pos hsz]
  rw [getElem_boundary pre post (Instr.opByte o) [] hsz, hb]
  cases o with
  | Push p => exact absurd hp (by simp [plainOp])
  | DupN d => exact absurd hp (by simp [plainOp])
  | SwapN d => exact absurd hp (by simp [plainOp])
  | Exchange e => exact absurd hp (by simp [plainOp])
  | _ => rfl

/-! ### PUSH32 decoding -/

/-- Folding the big-endian digits back into a number. -/
private theorem foldl_natToBE (w : Nat) :
    ∀ n acc : Nat, n < 256 ^ w →
      (natToBE n w).foldl (fun acc b => acc * 256 + b.toNat) acc = acc * 256 ^ w + n := by
  induction w with
  | zero =>
    intro n acc h
    interval_cases n
    simp [natToBE]
  | succ w ih =>
    intro n acc h
    rw [natToBE, List.foldl_append]
    have hdiv : n / 256 < 256 ^ w := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      calc n < 256 ^ (w + 1) := h
        _ = 256 ^ w * 256 := by rw [Nat.pow_succ]
    rw [ih (n / 256) acc hdiv]
    have hmod : (UInt8.ofNat (n % 256)).toNat = n % 256 := by
      simp
    simp only [List.foldl_cons, List.foldl_nil, hmod]
    have := Nat.div_add_mod n 256
    rw [Nat.pow_succ]
    ring_nf
    omega

private theorem pow_256_32 : (256 : Nat) ^ 32 = 2 ^ 256 := by
  have h8 : (256 : Nat) = 2 ^ 8 := by norm_num
  calc (256 : Nat) ^ 32 = (2 ^ 8) ^ 32 := by rw [h8]
    _ = 2 ^ (8 * 32) := (Nat.pow_mul 2 8 32).symm
    _ = 2 ^ 256 := by norm_num

private theorem u256_lt_pow : ∀ v : UInt256, v.toNat < 256 ^ 32 := by
  intro v
  have h : v.toNat < 2 ^ 256 := v.val.isLt
  rw [pow_256_32]
  exact h

private theorem u256_ofNat_toNat (v : UInt256) : UInt256.ofNat v.toNat = v := by
  cases v with
  | mk f =>
    unfold UInt256.ofNat
    apply congrArg
    apply Fin.ext
    show _ % _ = _
    exact Nat.mod_eq_of_lt f.isLt

/-- The extracted immediate of an embedded `PUSH32` is its 32-byte payload. -/
private theorem extract_push_imm (pre post : List UInt8) (v : UInt256) :
    ((mkCode (pre ++ (Instr.push v).bytes ++ post)).extract
        (pre.length + 1) (pre.length + 1 + 32)).data.toList
      = natToBE v.toNat 32 := by
  show ((mkCode (pre ++ (0x7f :: natToBE v.toNat 32) ++ post)).extract
      (pre.length + 1) (pre.length + 1 + 32)).data.toList = _
  rw [ByteArray.data_extract]
  show ((pre ++ (0x7f :: natToBE v.toNat 32) ++ post).toArray.extract
      (pre.length + 1) (pre.length + 1 + 32)).toList = _
  rw [Array.toList_extract]
  rw [show (pre ++ 0x7f :: natToBE v.toNat 32 ++ post).toArray.toList
      = pre ++ 0x7f :: natToBE v.toNat 32 ++ post from by simp]
  rw [List.extract_eq_take_drop]
  rw [show pre.length + 1 + 32 - (pre.length + 1) = 32 from by omega]
  have hL : pre ++ (0x7f :: natToBE v.toNat 32) ++ post
      = (pre ++ [0x7f]) ++ (natToBE v.toNat 32 ++ post) := by simp
  rw [hL, List.drop_left' (by simp), List.take_left' (length_natToBE _ _)]

/-- Decoding at the start of an embedded `PUSH32`. -/
theorem decodeAt_push (pre post : List UInt8) (v : UInt256) :
    Decode.decodeAt (mkCode (pre ++ (Instr.push v).bytes ++ post)) pre.length
      = some (.Push ⟨32, by decide⟩, some (v, 32)) := by
  show Decode.decodeAt (mkCode (pre ++ (0x7f :: natToBE v.toNat 32) ++ post)) pre.length = _
  have hsz : pre.length < (mkCode (pre ++ (0x7f :: natToBE v.toNat 32) ++ post)).size := by
    simp
  unfold Decode.decodeAt
  rw [dif_pos hsz]
  rw [getElem_boundary pre post 0x7f (natToBE v.toNat 32) hsz]
  rw [show Decode.opcodeOf 0x7f = some (.Push ⟨32, by decide⟩) from by decide]
  have himm : UInt256.ofNat (Data.Bytes.bytesToBigEndianNat
      ((mkCode (pre ++ (0x7f :: natToBE v.toNat 32) ++ post)).extract
        (pre.length + 1) (pre.length + 1 + 32))) = v := by
    unfold Data.Bytes.bytesToBigEndianNat
    rw [ByteArray.toList_eq_data]
    rw [show (0x7f :: natToBE v.toNat 32) = (Instr.push v).bytes from rfl]
    rw [extract_push_imm pre post v]
    rw [foldl_natToBE 32 v.toNat 0 (u256_lt_pow v)]
    rw [Nat.zero_mul, Nat.zero_add]
    exact u256_ofNat_toNat v
  show some ((Operation.Push ⟨32, by decide⟩ : Operation),
      some (UInt256.ofNat (Data.Bytes.bytesToBigEndianNat
        ((mkCode (pre ++ 0x7f :: natToBE v.toNat 32 ++ post)).extract
          (pre.length + 1) (pre.length + 1 + 32))), 32)) = _
  rw [himm]

/-- Every operation in the compiler's table round-trips through its byte and
is immediate-free. Proved once by cases over the (finite) `Op` enum; this is
what lets the simulation apply `decodeAt_op` without per-op byte lemmas. -/
theorem opTable_roundtrip {yop : YulSemantics.EVM.Op} {o : Operation}
    (h : opTable yop = some o) :
    Decode.opcodeOf (Instr.opByte o) = some o ∧ plainOp o := by
  cases yop <;> simp only [opTable, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> exact ⟨by decide, trivial⟩

/-- Every operation in the compiler's table is activated on the Osaka fork
(the fork the correctness theorem fixes). -/
theorem opTable_available {yop : YulSemantics.EVM.Op} {o : Operation}
    (h : opTable yop = some o) :
    o.availableInFork .Osaka = true := by
  cases yop <;> simp only [opTable, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> decide

@[simp] theorem push32_available :
    (Operation.Push ⟨32, by decide⟩).availableInFork .Osaka = true := by
  decide

/-- `DUP1..DUP16` round-trip through their bytes (they are classic opcodes,
available on every fork — no EIP-8024 dependency). -/
theorem dup_roundtrip (n : Fin 16) :
    Decode.opcodeOf (Instr.opByte (.Dup ⟨n⟩)) = some (.Dup ⟨n⟩) ∧
      plainOp (Operation.Dup ⟨n⟩) ∧
      (Operation.Dup ⟨n⟩).availableInFork .Osaka = true := by
  refine ⟨?_, trivial, ?_⟩ <;> revert n <;> decide

/-- `SWAP1..SWAP16` round-trip through their bytes. -/
theorem swap_roundtrip (n : Fin 16) :
    Decode.opcodeOf (Instr.opByte (.Swap ⟨n⟩)) = some (.Swap ⟨n⟩) ∧
      plainOp (Operation.Swap ⟨n⟩) ∧
      (Operation.Swap ⟨n⟩).availableInFork .Osaka = true := by
  refine ⟨?_, trivial, ?_⟩ <;> revert n <;> decide

/-- `POP` round-trips (needed for direct emission by `assign`/block exits,
independently of the Yul `pop` built-in). -/
theorem pop_roundtrip :
    Decode.opcodeOf (Instr.opByte .POP) = some .POP ∧ plainOp Operation.POP ∧
      Operation.POP.availableInFork .Osaka = true :=
  ⟨by decide, trivial, by decide⟩

/-! ### Jumpdest analysis

The analysis walk (`Decode.validJumpDestFrom`) advances one instruction at a
time over our assembled code: every emitted instruction is either a single
byte or `PUSH32`, whose immediate the walk skips. So instruction boundaries
are exactly the walk's footprints, and a `JUMPDEST` we emit at a boundary is
accepted. -/

private theorem bytes_pos (i : Instr) : 1 ≤ i.bytes.length := by
  cases i <;> simp

private theorem length_le_assembleBytes (is : List Instr) :
    is.length ≤ (assembleBytes is).length := by
  induction is with
  | nil => simp
  | cons i is ih =>
    have := bytes_pos i
    simp
    omega

/-- No emitted opcode byte decodes as a `PUSH` (so the walk never skips over
parts of our single-byte instructions). -/
private theorem opcodeOf_opByte_not_push (o : Operation) :
    (match Decode.opcodeOf (Instr.opByte o) with
     | some (.Push p) => p.width.val
     | _ => 0) = 0 := by
  cases o with
  | StopArith op => cases op <;> rfl
  | CompBit op => cases op <;> rfl
  | Keccak op => cases op <;> rfl
  | Env op => cases op <;> rfl
  | Block op => cases op <;> rfl
  | StackMemFlow op => cases op <;> rfl
  | Push p => rfl
  | Dup d =>
    obtain ⟨⟨n, hn⟩⟩ := d
    rw [(dup_roundtrip ⟨n, hn⟩).1]
  | Swap s =>
    obtain ⟨⟨n, hn⟩⟩ := s
    rw [(swap_roundtrip ⟨n, hn⟩).1]
  | DupN d => rfl
  | SwapN s => rfl
  | Exchange e => rfl
  | Log l => rfl
  | System op => cases op <;> rfl

/-- The walk's step at an instruction boundary is the instruction's width. -/
private theorem pushDataSize_at (i : Instr) (pre rest : List UInt8) :
    Decode.pushDataSize (mkCode (pre ++ i.bytes ++ rest)) pre.length
      = i.bytes.length - 1 := by
  have hsz : pre.length < (mkCode (pre ++ i.bytes ++ rest)).size := by
    have := bytes_pos i
    simp
    omega
  unfold Decode.pushDataSize
  rw [dif_pos hsz]
  cases i with
  | push v =>
    have hb : (mkCode (pre ++ (Instr.push v).bytes ++ rest))[pre.length]'hsz = 0x7f :=
      getElem_boundary pre rest 0x7f (natToBE v.toNat 32) hsz
    rw [hb, show Decode.opcodeOf 0x7f = some (.Push ⟨32, by decide⟩) from by decide]
    simp
  | op o =>
    have hb : (mkCode (pre ++ (Instr.op o).bytes ++ rest))[pre.length]'hsz
        = Instr.opByte o :=
      getElem_boundary pre rest (Instr.opByte o) [] hsz
    rw [hb]
    exact opcodeOf_opByte_not_push o

private theorem walk_through :
    ∀ (is : List Instr) (pre rest : List UInt8) (fuel : Nat),
      is.length + 1 ≤ fuel →
      Decode.validJumpDestFrom (mkCode (pre ++ assembleBytes is ++ 0x5b :: rest))
        (pre.length + (assembleBytes is).length) pre.length fuel = true := by
  intro is
  induction is with
  | nil =>
    intro pre rest fuel hfuel
    cases fuel with
    | zero => omega
    | succ f =>
      unfold Decode.validJumpDestFrom
      rw [if_pos (by simp)]
      have hsz : pre.length
          < (mkCode (pre ++ assembleBytes ([] : List Instr) ++ 0x5b :: rest)).size := by
        simp
      rw [dif_pos hsz]
      have hb : (mkCode (pre ++ assembleBytes ([] : List Instr)
          ++ 0x5b :: rest))[pre.length]'hsz = 0x5b := by
        have := getElem_boundary pre rest 0x5b [] (by simpa using hsz)
        simpa using this
      simp only [decide_eq_true_eq]
      simpa using hb
  | cons i is ih =>
    intro pre rest fuel hfuel
    cases fuel with
    | zero => omega
    | succ f =>
      have hpos := bytes_pos i
      have hlist : pre ++ assembleBytes (i :: is) ++ 0x5b :: rest
          = (pre ++ i.bytes) ++ assembleBytes is ++ 0x5b :: rest := by
        simp
      have hlen1 : (assembleBytes (i :: is)).length
          = i.bytes.length + (assembleBytes is).length := by simp
      have hsz1 : pre.length + (assembleBytes (i :: is)).length
          < (mkCode (pre ++ assembleBytes (i :: is) ++ 0x5b :: rest)).size := by
        rw [size_mkCode]
        simp
      unfold Decode.validJumpDestFrom
      rw [if_neg (by omega)]
      rw [if_neg (by
        rw [not_or]
        exact ⟨by omega, by omega⟩)]
      have hstep : Decode.pushDataSize
          (mkCode (pre ++ assembleBytes (i :: is) ++ 0x5b :: rest)) pre.length
          = i.bytes.length - 1 := by
        rw [show pre ++ assembleBytes (i :: is) ++ 0x5b :: rest
            = pre ++ i.bytes ++ (assembleBytes is ++ 0x5b :: rest) from by simp]
        exact pushDataSize_at i pre _
      rw [hstep]
      rw [show pre.length + 1 + (i.bytes.length - 1) = (pre ++ i.bytes).length from by
        simp
        omega]
      rw [show pre.length + (assembleBytes (i :: is)).length
          = (pre ++ i.bytes).length + (assembleBytes is).length from by
        simp
        omega]
      rw [show mkCode (pre ++ assembleBytes (i :: is) ++ 0x5b :: rest)
          = mkCode ((pre ++ i.bytes) ++ assembleBytes is ++ 0x5b :: rest) from by
        rw [hlist]]
      exact ih (pre ++ i.bytes) rest f (by
        have hl : (i :: is).length = is.length + 1 := rfl
        omega)

/-- A `JUMPDEST` we emit at an instruction boundary passes the jumpdest
analysis, regardless of the (unreached) bytes after it. -/
theorem isValidJumpDest_boundary (isPre : List Instr) (rest : List UInt8) :
    Decode.isValidJumpDest
      (mkCode (assembleBytes isPre ++ (Instr.op .JUMPDEST).bytes ++ rest))
      (assembleBytes isPre).length = true := by
  unfold Decode.isValidJumpDest
  have hcode : assembleBytes isPre ++ (Instr.op .JUMPDEST).bytes ++ rest
      = [] ++ assembleBytes isPre ++ 0x5b :: rest := by
    show _ ++ (0x5b :: []) ++ _ = _
    simp
  rw [hcode]
  have h := walk_through isPre [] rest
    ((mkCode ([] ++ assembleBytes isPre ++ 0x5b :: rest)).size + 1)
    (by
      have h1 := length_le_assembleBytes isPre
      simp
      omega)
  simpa using h

end YulEvmCompiler
