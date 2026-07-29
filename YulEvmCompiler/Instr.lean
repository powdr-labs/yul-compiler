import EvmSemantics.EVM.Decode
set_option warningAsError true
/-!
# YulEvmCompiler.Instr

The compiler's tiny instruction IR and its assembler.

Each constructor assembles to a byte sequence whose length is a function of the
constructor's fields alone (never of any external layout), so the decode lemmas
(`YulEvmCompiler.Decode`) are one small proof per constructor:

* `push w v` — `PUSHk` for `k = w.val` (`PUSH0 = 0x5f` … `PUSH32 = 0x7f`)
  followed by the `w.val`-byte big-endian immediate. The width is carried
  explicitly so the assembler can emit the minimal encoding of a constant
  (`pushMin`, `byteWidth`), while the decode round-trip stays a one-liner: it
  holds under the well-formedness side condition `v.toNat < 256 ^ w.val`
  (`|push w v| = 1 + w.val`).
* `op o`    — a single-byte opcode (an `EvmSemantics.Operation` with no
  immediate bytes, e.g. `ADD`, `SLOAD`, `RETURN`).
-/

namespace YulEvmCompiler

open EvmSemantics

/-- Big-endian, fixed-width byte encoding of `n` (most-significant byte
first). `natToBE n w` has length `w` and round-trips through
`Data.Bytes.bytesToBigEndianNat` whenever `n < 256 ^ w`. -/
def natToBE (n : Nat) : Nat → List UInt8
  | 0 => []
  | w + 1 => natToBE (n / 256) w ++ [UInt8.ofNat (n % 256)]

@[simp] theorem length_natToBE (n w : Nat) : (natToBE n w).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [natToBE, ih]

/-- The compiler IR. -/
inductive Instr
  /-- `PUSHk v` with `k = w.val`: opcode `0x5f + w.val` + `w.val` immediate
  bytes. `w = 0` is `PUSH0` (no immediate); `w = 32` is the full-width
  `PUSH32`. -/
  | push  (w : Fin 33) (v : UInt256)
  /-- A single-byte operation (no immediate). Every emitted instruction is
  immediate-free or a `PUSHk`, so instruction boundaries coincide with the
  jumpdest analysis' walk — see `Decode.isValidJumpDest_boundary`. -/
  | op    (o : Operation)
  deriving Repr

namespace Instr

/-- The opcode byte of a zero-immediate operation. Total for convenience;
only the entries the compiler actually emits matter (each use site proves
`Decode.opcodeOf (opByte o) = some o` for its concrete `o`). Unlisted
operations map to `0xfe` (`INVALID`). -/
def opByte : Operation → UInt8
  | .STOP => 0x00 | .ADD => 0x01 | .MUL => 0x02 | .SUB => 0x03
  | .DIV => 0x04 | .SDIV => 0x05 | .MOD => 0x06 | .SMOD => 0x07
  | .ADDMOD => 0x08 | .MULMOD => 0x09 | .EXP => 0x0a | .SIGNEXTEND => 0x0b
  | .LT => 0x10 | .GT => 0x11 | .SLT => 0x12 | .SGT => 0x13
  | .EQ => 0x14 | .ISZERO => 0x15 | .AND => 0x16 | .OR => 0x17
  | .XOR => 0x18 | .NOT => 0x19 | .BYTE => 0x1a
  | .SHL => 0x1b | .SHR => 0x1c | .SAR => 0x1d | .CLZ => 0x1e
  | .KECCAK256 => 0x20
  | .ADDRESS => 0x30 | .BALANCE => 0x31 | .ORIGIN => 0x32 | .CALLER => 0x33
  | .CALLVALUE => 0x34 | .CALLDATALOAD => 0x35 | .CALLDATASIZE => 0x36
  | .CALLDATACOPY => 0x37 | .CODESIZE => 0x38 | .CODECOPY => 0x39
  | .GASPRICE => 0x3a | .EXTCODESIZE => 0x3b | .EXTCODECOPY => 0x3c
  | .RETURNDATASIZE => 0x3d | .RETURNDATACOPY => 0x3e | .EXTCODEHASH => 0x3f
  | .BLOCKHASH => 0x40 | .COINBASE => 0x41 | .TIMESTAMP => 0x42
  | .NUMBER => 0x43 | .PREVRANDAO => 0x44 | .GASLIMIT => 0x45
  | .CHAINID => 0x46 | .SELFBALANCE => 0x47 | .BASEFEE => 0x48
  | .BLOBHASH => 0x49 | .BLOBBASEFEE => 0x4a
  | .POP => 0x50 | .MLOAD => 0x51 | .MSTORE => 0x52 | .MSTORE8 => 0x53
  | .SLOAD => 0x54 | .SSTORE => 0x55
  | .JUMP => 0x56 | .JUMPI => 0x57 | .MSIZE => 0x59 | .JUMPDEST => 0x5b
  | .TLOAD => 0x5c | .TSTORE => 0x5d | .MCOPY => 0x5e
  | .Dup d => UInt8.ofNat (0x80 + d.idx.val)
  | .Swap s => UInt8.ofNat (0x90 + s.idx.val)
  | .Log l => UInt8.ofNat (0xa0 + l.topics.val)
  | .CREATE => 0xf0 | .CALL => 0xf1 | .CALLCODE => 0xf2 | .RETURN => 0xf3
  | .DELEGATECALL => 0xf4 | .CREATE2 => 0xf5 | .STATICCALL => 0xfa
  | .REVERT => 0xfd | .INVALID => 0xfe | .SELFDESTRUCT => 0xff
  | _ => 0xfe

/-- The bytes an instruction assembles to. -/
def bytes : Instr → List UInt8
  | .push w v => UInt8.ofNat (0x5f + w.val) :: natToBE v.toNat w.val
  | .op o     => [opByte o]

/-- The byte length of an instruction. -/
def size (i : Instr) : Nat := i.bytes.length

@[simp] theorem size_push (w : Fin 33) (v : UInt256) : (Instr.push w v).size = 1 + w.val := by
  simp only [size, bytes, List.length_cons, length_natToBE]; omega
@[simp] theorem size_op (o : Operation) : (Instr.op o).size = 1 := rfl

@[simp] theorem length_bytes_op (o : Operation) : (Instr.op o).bytes.length = 1 := rfl

@[simp] theorem length_bytes_push (w : Fin 33) (v : UInt256) :
    (Instr.push w v).bytes.length = 1 + w.val := by
  simp only [bytes, List.length_cons, length_natToBE]; omega

/-! ### Minimal-width pushes

`byteWidth n` is the least `w` with `n < 256 ^ w` (so `byteWidth 0 = 0`, giving
`PUSH0`). `pushMin v` emits the shortest `PUSHk` encoding of `v`. -/

/-- The least width `w` such that `n < 256 ^ w`. -/
def byteWidth (n : Nat) : Nat := if n = 0 then 0 else byteWidth (n / 256) + 1
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- `byteWidth n` bytes are enough to hold `n`. -/
theorem lt_pow_byteWidth (n : Nat) : n < 256 ^ byteWidth n := by
  induction n using byteWidth.induct with
  | case1 => simp [byteWidth]
  | case2 n hn ih =>
    rw [byteWidth, if_neg hn, Nat.pow_succ]
    have hdm := Nat.div_add_mod n 256
    have hmod : n % 256 < 256 := Nat.mod_lt _ (by omega)
    have hle : n / 256 + 1 ≤ 256 ^ byteWidth (n / 256) := ih
    omega

/-- `byteWidth` is minimal: any width that fits `n` is at least `byteWidth n`. -/
theorem byteWidth_le_of_lt_pow (n w : Nat) (h : n < 256 ^ w) : byteWidth n ≤ w := by
  induction w generalizing n with
  | zero => simp only [Nat.pow_zero] at h; simp [byteWidth, Nat.lt_one_iff.mp h]
  | succ w ih =>
    rw [byteWidth]
    split
    · exact Nat.zero_le _
    · next hn =>
      have hdiv : n / 256 < 256 ^ w := by
        rw [Nat.div_lt_iff_lt_mul (by omega), ← Nat.pow_succ]
        exact h
      exact Nat.succ_le_succ (ih _ hdiv)

private theorem pow_256_32' : (256 : Nat) ^ 32 = 2 ^ 256 := by
  have h8 : (256 : Nat) = 2 ^ 8 := by decide
  calc (256 : Nat) ^ 32 = (2 ^ 8) ^ 32 := by rw [h8]
    _ = 2 ^ (8 * 32) := (Nat.pow_mul 2 8 32).symm
    _ = 2 ^ 256 := rfl

/-- For any word, `byteWidth v.toNat ≤ 32` (since `256 ^ 32 = 2 ^ 256`). -/
theorem byteWidth_le_32 (v : UInt256) : byteWidth v.toNat ≤ 32 := by
  apply byteWidth_le_of_lt_pow
  rw [pow_256_32']
  exact v.val.isLt

/-- The minimal width (as a `Fin 33`) that encodes `v`. -/
def widthOf (v : UInt256) : Fin 33 := ⟨byteWidth v.toNat, by have := byteWidth_le_32 v; omega⟩

/-- `widthOf`'s underlying width is `byteWidth` (definitional; a `simp`
handle so byte arithmetic can drop the `Fin` wrapper). -/
@[simp] theorem widthOf_val (v : UInt256) : (widthOf v).val = byteWidth v.toNat := rfl

/-- The shortest `PUSHk` that pushes `v` (`PUSH0` when `v = 0`). -/
def pushMin (v : UInt256) : Instr := .push (widthOf v) v

/-- `pushMin`'s width fits `v` — the decode round-trip side condition. -/
theorem pushMin_wf (v : UInt256) : v.toNat < 256 ^ (widthOf v).val :=
  lt_pow_byteWidth v.toNat

/-- The byte length of a minimal-width push: `1 + byteWidth v.toNat`. -/
@[simp] theorem length_bytes_pushMin (v : UInt256) :
    (pushMin v).bytes.length = 1 + byteWidth v.toNat := by
  rw [pushMin, length_bytes_push, widthOf_val]

@[simp] theorem size_pushMin_le (v : UInt256) : (pushMin v).size ≤ 33 := by
  rw [pushMin, size_push]
  have : (widthOf v).val ≤ 32 := byteWidth_le_32 v
  omega

end Instr

/-- The bytes a whole instruction sequence assembles to. -/
def assembleBytes (is : List Instr) : List UInt8 := is.flatMap Instr.bytes

@[simp] theorem assembleBytes_nil : assembleBytes [] = [] := rfl

@[simp] theorem assembleBytes_cons (i : Instr) (is : List Instr) :
    assembleBytes (i :: is) = i.bytes ++ assembleBytes is := rfl

theorem assembleBytes_append (is js : List Instr) :
    assembleBytes (is ++ js) = assembleBytes is ++ assembleBytes js := by
  simp [assembleBytes]

/-- Assemble to the `ByteArray` the EVM semantics executes. -/
def assemble (is : List Instr) : ByteArray := ⟨(assembleBytes is).toArray⟩

end YulEvmCompiler
