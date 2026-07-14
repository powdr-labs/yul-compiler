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
* returndata and external-code copies — calldata, code, and object-data copies
  are covered by `MemMatch.copyFromBytes`, while the remaining sources still
  need their own state correspondence;
* `keccak256` — the two repos each declare their own unrelated `opaque` hash;
* `log0`–`log4` — need a log-series correspondence (mechanical, later);
* remaining world-state readers (`extcode*`, `blockhash`) — need their
  account/code/header map correspondences;
* `gas`, calls/creates, `selfdestruct` — unmodeled in yul-semantics
  (`stepOp` returns `none`), so no source derivation exists to preserve. -/
def opTable : Op → Option Operation
  -- arithmetic
  | .add => some .ADD | .sub => some .SUB | .mul => some .MUL | .div => some .DIV
  | .sdiv => some .SDIV
  | .mod => some .MOD | .smod => some .SMOD
  | .addmod => some .ADDMOD | .mulmod => some .MULMOD | .exp => some .EXP
  | .signextend => some .SIGNEXTEND | .clz => some .CLZ
  -- comparison
  | .lt => some .LT | .gt => some .GT | .slt => some .SLT | .sgt => some .SGT
  | .eq => some .EQ | .iszero => some .ISZERO
  -- bitwise / shifts
  | .and => some .AND | .or => some .OR | .xor => some .XOR | .not => some .NOT
  | .byte => some .BYTE | .shl => some .SHL | .shr => some .SHR
  | .sar => some .SAR
  -- value discard
  | .pop => some .POP
  -- memory read / active-size read
  | .mload => some .MLOAD | .msize => some .MSIZE
  -- memory write / copy
  | .mstore => some .MSTORE | .mstore8 => some .MSTORE8
  | .mcopy => some .MCOPY
  -- calldata read / copy
  | .calldataload => some .CALLDATALOAD | .calldatasize => some .CALLDATASIZE
  | .calldatacopy => some .CALLDATACOPY
  -- code (own account): size and copy-to-memory; `datacopy` is `codecopy`
  -- (deployed bytecode carries data segments appended to the code)
  | .codesize => some .CODESIZE
  | .codecopy => some .CODECOPY
  | .datacopy => some .CODECOPY
  -- scalar environment / block readers
  | .address => some .ADDRESS | .origin => some .ORIGIN | .caller => some .CALLER
  | .callvalue => some .CALLVALUE | .gasprice => some .GASPRICE
  | .selfbalance => some .SELFBALANCE
  | .coinbase => some .COINBASE | .timestamp => some .TIMESTAMP
  | .number => some .NUMBER | .prevrandao => some .PREVRANDAO
  | .gaslimit => some .GASLIMIT | .chainid => some .CHAINID
  | .basefee => some .BASEFEE | .blobbasefee => some .BLOBBASEFEE
  -- account / transaction readers
  | .balance => some .BALANCE | .blobhash => some .BLOBHASH
  -- storage / transient storage
  | .sload => some .SLOAD | .sstore => some .SSTORE
  | .tload => some .TLOAD | .tstore => some .TSTORE
  -- halting
  | .stop => some .STOP | .ret => some .RETURN | .revert => some .REVERT
  | .invalid => some .INVALID
  -- everything else: not yet in the verified fragment
  | _ => none

end YulEvmCompiler
