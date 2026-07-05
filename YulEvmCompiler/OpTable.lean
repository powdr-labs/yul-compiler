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
* `sdiv`/`smod`/`signextend`/`sar` — plain proof debt: their two's-complement
  `BitVec` ↔ `UInt256` agreement lemmas (`conv_*` in `Value.lean`) are still
  open; each is enabled by adding its lemma, its row here, and its `opStep`
  case;
* memory/state writers that go through evm-semantics' `partial def writeBytes`
  (`mstore`, `mstore8`, `mcopy`, the copy family) — nothing about them is
  provable until `writeBytes` is totalized upstream;
* `keccak256` — the two repos each declare their own unrelated `opaque` hash;
* `log0`–`log4` — need a log-series correspondence (mechanical, later);
* `msize`, `gas`, calls/creates, `selfdestruct` — unmodeled in yul-semantics
  (`stepOp` returns `none`), so no source derivation exists to preserve. -/
def opTable : Op → Option Operation
  -- arithmetic
  | .add => some .ADD | .sub => some .SUB | .mul => some .MUL | .div => some .DIV
  | .mod => some .MOD
  | .addmod => some .ADDMOD | .mulmod => some .MULMOD | .exp => some .EXP
  | .clz => some .CLZ
  -- comparison
  | .lt => some .LT | .gt => some .GT | .slt => some .SLT | .sgt => some .SGT
  | .eq => some .EQ | .iszero => some .ISZERO
  -- bitwise / shifts
  | .and => some .AND | .or => some .OR | .xor => some .XOR | .not => some .NOT
  | .byte => some .BYTE | .shl => some .SHL | .shr => some .SHR
  -- value discard
  | .pop => some .POP
  -- memory read
  | .mload => some .MLOAD
  -- storage / transient storage
  | .sload => some .SLOAD | .sstore => some .SSTORE
  | .tload => some .TLOAD | .tstore => some .TSTORE
  -- halting
  | .stop => some .STOP | .ret => some .RETURN | .revert => some .REVERT
  | .invalid => some .INVALID
  -- everything else: not yet in the verified fragment
  | _ => none

end YulEvmCompiler
