import YulEvmCompiler.Instr
import YulEvmCompiler.Value

/-!
# YulEvmCompiler.OpTable

The single-opcode translation of each supported Yul built-in, shared by the
compiler and the lowering/decoding proofs. `opTable`'s domain is the *single
source of truth* for the verified built-in fragment — a built-in is added
here exactly when its correctness lemma lands in `YulEvmCompiler.Value` /
`OpStep`.
-/

namespace YulEvmCompiler

open YulSemantics.EVM (Op)
open EvmSemantics (Operation)

/-- The single-opcode translation of each supported Yul built-in. `none` means
the built-in is not (yet) in the verified fragment.

Deliberately *not* covered so far:
* `signextend` — plain proof debt: needs an all-ones-xor / complement fact
  (`(2^n-1) ^^^ m = 2^n-1-m`) on `Nat` that isn't in the pinned Mathlib;
  `sdiv`/`smod`/`sar` are *now covered* (their two's-complement `conv_*`
  agreement lemmas live in `Value.lean`);
* `mstore8`/`mcopy` and the calldata/code copy family — further memory writers
  (`mstore` itself *is* covered, via the `writeBytes` read-after-write lemma
  and the `natToBytesPadded` byte lemmas in `BytesLemmas.lean`; the others just
  need their own byte-layout lemmas);
* `keccak256` — the two repos each declare their own unrelated `opaque` hash;
* `log0`–`log4` — need a log-series correspondence (mechanical, later);
* `msize`, `gas`, calls/creates, `selfdestruct` — unmodeled in yul-semantics
  (`stepOp` returns `none`), so no source derivation exists to preserve. -/
def opTable : Op → Option Operation
  -- arithmetic
  | .add => some .ADD | .sub => some .SUB | .mul => some .MUL | .div => some .DIV
  | .sdiv => some .SDIV
  | .mod => some .MOD | .smod => some .SMOD
  | .addmod => some .ADDMOD | .mulmod => some .MULMOD | .exp => some .EXP
  | .clz => some .CLZ
  -- comparison
  | .lt => some .LT | .gt => some .GT | .slt => some .SLT | .sgt => some .SGT
  | .eq => some .EQ | .iszero => some .ISZERO
  -- bitwise / shifts
  | .and => some .AND | .or => some .OR | .xor => some .XOR | .not => some .NOT
  | .byte => some .BYTE | .shl => some .SHL | .shr => some .SHR
  | .sar => some .SAR
  -- value discard
  | .pop => some .POP
  -- memory read
  | .mload => some .MLOAD
  -- memory write
  | .mstore => some .MSTORE
  -- calldata read
  | .calldataload => some .CALLDATALOAD
  -- scalar environment / block readers
  | .address => some .ADDRESS | .origin => some .ORIGIN | .caller => some .CALLER
  | .callvalue => some .CALLVALUE | .gasprice => some .GASPRICE
  | .coinbase => some .COINBASE | .timestamp => some .TIMESTAMP
  | .number => some .NUMBER | .prevrandao => some .PREVRANDAO
  | .gaslimit => some .GASLIMIT | .chainid => some .CHAINID
  | .basefee => some .BASEFEE | .blobbasefee => some .BLOBBASEFEE
  -- storage / transient storage
  | .sload => some .SLOAD | .sstore => some .SSTORE
  | .tload => some .TLOAD | .tstore => some .TSTORE
  -- halting
  | .stop => some .STOP | .ret => some .RETURN | .revert => some .REVERT
  | .invalid => some .INVALID
  -- everything else: not yet in the verified fragment
  | _ => none

end YulEvmCompiler
