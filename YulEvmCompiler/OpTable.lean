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
* `gas`, creates, `selfdestruct` — still unmodeled in yul-semantics;
* calls are relational and are discharged by `CallsRealized`, rather than by
  the deterministic single-step proof used for local built-ins. -/
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
  -- hashing / value discard
  | .keccak256 => some .KECCAK256 | .pop => some .POP
  -- memory read / active-size read
  | .mload => some .MLOAD | .msize => some .MSIZE
  -- memory write / copy
  | .mstore => some .MSTORE | .mstore8 => some .MSTORE8
  | .mcopy => some .MCOPY
  -- calldata read / copy
  | .calldataload => some .CALLDATALOAD | .calldatasize => some .CALLDATASIZE
  | .calldatacopy => some .CALLDATACOPY
  -- returndata read / copy
  | .returndatasize => some .RETURNDATASIZE
  | .returndatacopy => some .RETURNDATACOPY
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
  -- account / transaction / historical-block readers
  | .balance => some .BALANCE
  | .extcodesize => some .EXTCODESIZE | .extcodecopy => some .EXTCODECOPY
  | .extcodehash => some .EXTCODEHASH | .blockhash => some .BLOCKHASH
  | .blobhash => some .BLOBHASH
  -- event logs
  | .log0 => some (.Log ⟨0⟩) | .log1 => some (.Log ⟨1⟩)
  | .log2 => some (.Log ⟨2⟩) | .log3 => some (.Log ⟨3⟩)
  | .log4 => some (.Log ⟨4⟩)
  -- storage / transient storage
  | .sload => some .SLOAD | .sstore => some .SSTORE
  | .tload => some .TLOAD | .tstore => some .TSTORE
  -- open-world calls (proved by a complete call/return macro step)
  | .call => some .CALL | .callcode => some .CALLCODE
  | .delegatecall => some .DELEGATECALL | .staticcall => some .STATICCALL
  -- halting
  | .stop => some .STOP | .ret => some .RETURN | .revert => some .REVERT
  | .invalid => some .INVALID
  -- everything else: not yet in the verified fragment
  | _ => none

/-- The source operations whose execution crosses an external call boundary. -/
def IsCallOp : Op → Prop
  | .call | .callcode | .delegatecall | .staticcall => True
  | _ => False

instance (op : Op) : Decidable (IsCallOp op) := by
  cases op <;> simp [IsCallOp] <;> infer_instance

/-- Away from the four call-family operations, the relational built-in graph
is exactly the old executable `stepOp` graph. -/
theorem builtin_iff_stepOp_of_not_call {external : YulSemantics.EVM.ExternalCalls}
    {op : Op} (hlocal : ¬ IsCallOp op) {args : List YulSemantics.EVM.U256}
    {st : YulSemantics.EVM.EvmState}
    {r : YulSemantics.BuiltinResult YulSemantics.EVM.U256 YulSemantics.EVM.EvmState} :
    YulSemantics.EVM.builtin external op args st r ↔
      YulSemantics.EVM.stepOp op args st = some r := by
  cases op <;> simp_all [IsCallOp, YulSemantics.EVM.builtin]

/-- Call-family built-ins only return normally; every relational halt is
therefore a halt of the executable local semantics. -/
theorem builtin_halt_iff_stepOp {external : YulSemantics.EVM.ExternalCalls}
    {op : Op} {args : List YulSemantics.EVM.U256}
    {st st' : YulSemantics.EVM.EvmState} :
    YulSemantics.EVM.builtin external op args st (.halt st') ↔
      YulSemantics.EVM.stepOp op args st = some (.halt st') := by
  cases op <;>
    simp [YulSemantics.EVM.builtin, YulSemantics.EVM.externalCall,
      YulSemantics.EVM.stepOp]
  all_goals
    intro h
    split at h <;> contradiction

/-- With the empty external relation, the relational dialect is propositionally
the original executable EVM dialect. -/
theorem evmWithCalls_none_eq_evm :
    YulSemantics.EVM.evmWithCalls YulSemantics.EVM.ExternalCalls.none =
      YulSemantics.EVM.evm := by
  unfold YulSemantics.EVM.evmWithCalls YulSemantics.EVM.evm
  congr 1
  funext op args st r
  apply propext
  cases op <;>
    simp [YulSemantics.EVM.builtin, YulSemantics.EVM.externalCall,
      YulSemantics.EVM.ExternalCalls.none, YulSemantics.EVM.stepOp]
  all_goals
    intro h
    split at h <;> contradiction

end YulEvmCompiler
