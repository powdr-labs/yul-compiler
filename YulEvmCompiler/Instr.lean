import EvmSemantics.EVM.Decode
set_option warningAsError true
/-!
# YulEvmCompiler.Instr

The compiler's tiny instruction IR and its assembler.

Each constructor assembles to a *fixed* byte sequence, so the decode lemmas
(`YulEvmCompiler.Decode`) are one small proof per constructor:

* `push v`  — `PUSH32` (`0x7f`) followed by the 32-byte big-endian immediate.
  Non-optimizing: every pushed word uses the full width, which keeps the
  layout arithmetic trivial (`|push v| = 33`).
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
  /-- `PUSH32 v`: `0x7f` + 32 immediate bytes. -/
  | push  (v : UInt256)
  /-- A single-byte operation (no immediate). Every emitted instruction is
  immediate-free or `PUSH32`, so instruction boundaries coincide with the
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
  | .push v  => 0x7f :: natToBE v.toNat 32
  | .op o    => [opByte o]

/-- The byte length of an instruction. -/
def size (i : Instr) : Nat := i.bytes.length

@[simp] theorem size_push (v : UInt256) : (Instr.push v).size = 33 := by
  simp [size, bytes]
@[simp] theorem size_op (o : Operation) : (Instr.op o).size = 1 := rfl

@[simp] theorem length_bytes_op (o : Operation) : (Instr.op o).bytes.length = 1 := rfl

@[simp] theorem length_bytes_push (v : UInt256) : (Instr.push v).bytes.length = 33 := by
  simp [bytes]

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
