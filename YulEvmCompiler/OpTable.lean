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
* `gas` — still unmodeled in yul-semantics;
* calls and creations are relational and are discharged by endpoint-realization
  assumptions rather than the deterministic single-step proof for local built-ins. -/
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
  -- open-world contract creation (proved by a complete init-code macro step)
  | .create => some .CREATE | .create2 => some .CREATE2
  -- halting
  | .stop => some .STOP | .ret => some .RETURN | .revert => some .REVERT
  | .invalid => some .INVALID | .selfdestruct => some .SELFDESTRUCT
  -- everything else: not yet in the verified fragment
  | _ => none

/-- The source operations whose execution crosses an external call boundary. -/
def IsCallOp : Op → Prop
  | .call | .callcode | .delegatecall | .staticcall => True
  | _ => False

instance (op : Op) : Decidable (IsCallOp op) := by
  cases op <;> simp [IsCallOp] <;> infer_instance

/-- The source operations whose execution crosses a contract-creation boundary. -/
def IsCreateOp : Op → Prop
  | .create | .create2 => True
  | _ => False

instance (op : Op) : Decidable (IsCreateOp op) := by
  cases op <;> simp [IsCreateOp] <;> infer_instance

/-- All operations implemented by an unrestricted target macro trace. -/
def IsExternalOp (op : Op) : Prop := IsCallOp op ∨ IsCreateOp op

instance (op : Op) : Decidable (IsExternalOp op) := by
  unfold IsExternalOp
  infer_instance

/-- Away from calls and creations, the combined relation is exactly `stepOp`. -/
theorem builtinWithExternal_iff_stepOp_of_not_external
    {calls : YulSemantics.EVM.ExternalCalls}
    {creates : YulSemantics.EVM.ExternalCreates}
    {op : Op} (hlocal : ¬ IsExternalOp op) {args : List YulSemantics.EVM.U256}
    {st : YulSemantics.EVM.EvmState}
    {r : YulSemantics.BuiltinResult YulSemantics.EVM.U256 YulSemantics.EVM.EvmState} :
    YulSemantics.EVM.builtinWithExternal calls creates op args st r ↔
      YulSemantics.EVM.stepOp op args st = some r := by
  cases op <;> simp_all [IsExternalOp, IsCallOp, IsCreateOp,
    YulSemantics.EVM.builtinWithExternal]

/-- The combined relation agrees with the compatibility call-only relation on call operations. -/
theorem builtinWithExternal_iff_builtin_of_call
    {calls : YulSemantics.EVM.ExternalCalls}
    {creates : YulSemantics.EVM.ExternalCreates}
    {op : Op} (hcall : IsCallOp op) {args : List YulSemantics.EVM.U256}
    {st : YulSemantics.EVM.EvmState}
    {r : YulSemantics.BuiltinResult YulSemantics.EVM.U256 YulSemantics.EVM.EvmState} :
    YulSemantics.EVM.builtinWithExternal calls creates op args st r ↔
      YulSemantics.EVM.builtin calls op args st r := by
  cases op <;> simp_all [IsCallOp, YulSemantics.EVM.builtin,
    YulSemantics.EVM.builtinWithExternal]

/-- On CREATE-family operations, calls are irrelevant. -/
theorem builtinWithExternal_iff_createOnly_of_create
    {calls : YulSemantics.EVM.ExternalCalls}
    {creates : YulSemantics.EVM.ExternalCreates}
    {op : Op} (hcreate : IsCreateOp op) {args : List YulSemantics.EVM.U256}
    {st : YulSemantics.EVM.EvmState}
    {r : YulSemantics.BuiltinResult YulSemantics.EVM.U256 YulSemantics.EVM.EvmState} :
    YulSemantics.EVM.builtinWithExternal calls creates op args st r ↔
      YulSemantics.EVM.builtinWithExternal YulSemantics.EVM.ExternalCalls.none
        creates op args st r := by
  cases op <;> simp_all [IsCreateOp, YulSemantics.EVM.builtinWithExternal]

/-- Away from the four call-family operations, the relational built-in graph
is exactly the old executable `stepOp` graph. -/
theorem builtin_iff_stepOp_of_not_call {external : YulSemantics.EVM.ExternalCalls}
    {op : Op} (hlocal : ¬ IsCallOp op) {args : List YulSemantics.EVM.U256}
    {st : YulSemantics.EVM.EvmState}
    {r : YulSemantics.BuiltinResult YulSemantics.EVM.U256 YulSemantics.EVM.EvmState} :
    YulSemantics.EVM.builtin external op args st r ↔
      YulSemantics.EVM.stepOp op args st = some r := by
  cases op <;> simp_all [IsCallOp, YulSemantics.EVM.builtin,
    YulSemantics.EVM.builtinWithExternal, YulSemantics.EVM.externalCreate,
    YulSemantics.EVM.ExternalCreates.none]
  all_goals
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩⟩⟩ <;>
      simp [YulSemantics.EVM.stepOp]

/-- Call/create built-ins only return normally; every relational halt is a local `stepOp` halt. -/
theorem builtinWithExternal_halt_iff_stepOp
    {calls : YulSemantics.EVM.ExternalCalls}
    {creates : YulSemantics.EVM.ExternalCreates}
    {op : Op} {args : List YulSemantics.EVM.U256}
    {st st' : YulSemantics.EVM.EvmState} :
    YulSemantics.EVM.builtinWithExternal calls creates op args st (.halt st') ↔
      YulSemantics.EVM.stepOp op args st = some (.halt st') := by
  cases op <;>
    simp [YulSemantics.EVM.builtinWithExternal, YulSemantics.EVM.externalCall,
      YulSemantics.EVM.externalCreate, YulSemantics.EVM.stepOp]
  all_goals
    intro h
    split at h <;> contradiction

/-- Compatibility specialization for the call-only relation. -/
theorem builtin_halt_iff_stepOp {external : YulSemantics.EVM.ExternalCalls}
    {op : Op} {args : List YulSemantics.EVM.U256}
    {st st' : YulSemantics.EVM.EvmState} :
    YulSemantics.EVM.builtin external op args st (.halt st') ↔
      YulSemantics.EVM.stepOp op args st = some (.halt st') := by
  simpa [YulSemantics.EVM.builtin] using
    (builtinWithExternal_halt_iff_stepOp
      (calls := external) (creates := YulSemantics.EVM.ExternalCreates.none)
      (op := op) (args := args) (st := st) (st' := st'))

/-- With no external calls or creations, the combined dialect is the executable dialect. -/
theorem evmWithExternal_none_eq_evm :
    YulSemantics.EVM.evmWithExternal YulSemantics.EVM.ExternalCalls.none
        YulSemantics.EVM.ExternalCreates.none = YulSemantics.EVM.evm := by
  unfold YulSemantics.EVM.evmWithExternal YulSemantics.EVM.evm
  congr 1
  funext op args st r
  apply propext
  cases op <;>
    simp [YulSemantics.EVM.builtinWithExternal, YulSemantics.EVM.externalCall,
      YulSemantics.EVM.externalCreate, YulSemantics.EVM.ExternalCalls.none,
      YulSemantics.EVM.ExternalCreates.none, YulSemantics.EVM.stepOp]
  all_goals
    intro h
    split at h <;> contradiction

/-- With the empty external relation, the relational dialect is propositionally
the original executable EVM dialect. -/
theorem evmWithCalls_none_eq_evm :
    YulSemantics.EVM.evmWithCalls YulSemantics.EVM.ExternalCalls.none =
      YulSemantics.EVM.evm := by
  exact evmWithExternal_none_eq_evm

end YulEvmCompiler
