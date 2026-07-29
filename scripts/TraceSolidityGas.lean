import YulParser.Compile
import YulEvmCompilerTests.Solc
import YulEvmCompilerTests.SolcDifferential
import YulEvmCompilerTests.SolidityCorpus
import YulEvmCompilerTests.InterpreterFixture
set_option warningAsError true

/-!
# TraceSolidityGas — opcode-level gas attribution vs solc

Where `checkSolidityGas` answers *"how much more gas does this compiler's
bytecode spend than solc's?"*, this tool answers *"on what?"*. For one
Solidity fixture it compiles both toolchains exactly like the gas harness
(this compiler from solc's unoptimized `--ir` Yul; solc fully optimized
`--bin --optimize --via-ir`), deploys both runtimes, replays one call per
requested selector on each, and records every executed instruction.

Per call it prints, for each side:

* total executed steps and gas;
* gas and instruction count aggregated by opcode group (`PUSH*`/`DUP*`/
  `SWAP*` collapsed, everything else by name), sorted by gas — the
  side-by-side diff of these tables is what localizes a gas gap
  (e.g. "all the excess is DUP/SWAP/POP shuffle" vs "we execute more
  ISZEROs per branch"); and
* the top `--top=N` (default 25) program counters by attributed gas —
  `count=100` rows expose a hot loop body, and the PC range immediately
  gives the region to disassemble.

Calls use the selector plus eight synthetic `0x…123` argument words (the
gasTests convention) — value-typed arguments exercise real work; a fixture
needing specific arguments can be probed with `--calldata=<hex>` instead,
which overrides the whole calldata for every requested run.

Usage:

    traceSolidityGas <fixture.sol> <solc-path> [<8-hex-digit selector> ...]
        [--top=N] [--calldata=<hex>]

With no explicit selectors, every external function reported by
`solc --hashes` is traced. Built natively for the same interpreter
stack-depth reason as `checkSolidityGas`.
-/

open System YulParser
open EvmSemantics
open YulEvmCompilerTests.Solc
open YulEvmCompilerTests.SolidityCorpus
open YulEvmCompilerTests.InterpreterFixture
open YulEvmCompilerTests.SolcDifferential (gasUsed)

private def opName (b : UInt8) : String :=
  match b.toNat with
  | 0x00 => "STOP" | 0x01 => "ADD" | 0x02 => "MUL" | 0x03 => "SUB"
  | 0x04 => "DIV" | 0x05 => "SDIV" | 0x06 => "MOD" | 0x07 => "SMOD"
  | 0x08 => "ADDMOD" | 0x09 => "MULMOD" | 0x0a => "EXP" | 0x0b => "SIGNEXTEND"
  | 0x10 => "LT" | 0x11 => "GT" | 0x12 => "SLT" | 0x13 => "SGT"
  | 0x14 => "EQ" | 0x15 => "ISZERO" | 0x16 => "AND" | 0x17 => "OR"
  | 0x18 => "XOR" | 0x19 => "NOT" | 0x1a => "BYTE" | 0x1b => "SHL"
  | 0x1c => "SHR" | 0x1d => "SAR" | 0x20 => "KECCAK256"
  | 0x30 => "ADDRESS" | 0x31 => "BALANCE" | 0x32 => "ORIGIN" | 0x33 => "CALLER"
  | 0x34 => "CALLVALUE" | 0x35 => "CALLDATALOAD" | 0x36 => "CALLDATASIZE"
  | 0x37 => "CALLDATACOPY" | 0x38 => "CODESIZE" | 0x39 => "CODECOPY"
  | 0x3a => "GASPRICE" | 0x3b => "EXTCODESIZE" | 0x3c => "EXTCODECOPY"
  | 0x3d => "RETURNDATASIZE" | 0x3e => "RETURNDATACOPY" | 0x3f => "EXTCODEHASH"
  | 0x40 => "BLOCKHASH" | 0x41 => "COINBASE" | 0x42 => "TIMESTAMP"
  | 0x43 => "NUMBER" | 0x44 => "PREVRANDAO" | 0x45 => "GASLIMIT"
  | 0x46 => "CHAINID" | 0x47 => "SELFBALANCE" | 0x48 => "BASEFEE"
  | 0x49 => "BLOBHASH" | 0x4a => "BLOBBASEFEE"
  | 0x50 => "POP" | 0x51 => "MLOAD" | 0x52 => "MSTORE" | 0x53 => "MSTORE8"
  | 0x54 => "SLOAD" | 0x55 => "SSTORE" | 0x56 => "JUMP" | 0x57 => "JUMPI"
  | 0x58 => "PC" | 0x59 => "MSIZE" | 0x5a => "GAS" | 0x5b => "JUMPDEST"
  | 0x5c => "TLOAD" | 0x5d => "TSTORE" | 0x5e => "MCOPY" | 0x5f => "PUSH0"
  | 0xa0 => "LOG0" | 0xa1 => "LOG1" | 0xa2 => "LOG2" | 0xa3 => "LOG3"
  | 0xa4 => "LOG4" | 0xf0 => "CREATE" | 0xf1 => "CALL" | 0xf2 => "CALLCODE"
  | 0xf3 => "RETURN" | 0xf4 => "DELEGATECALL" | 0xf5 => "CREATE2"
  | 0xfa => "STATICCALL" | 0xfd => "REVERT" | 0xfe => "INVALID"
  | 0xff => "SELFDESTRUCT"
  | n =>
    if 0x60 ≤ n && n ≤ 0x7f then s!"PUSH{n - 0x5f}"
    else if 0x80 ≤ n && n ≤ 0x8f then s!"DUP{n - 0x7f}"
    else if 0x90 ≤ n && n ≤ 0x9f then s!"SWAP{n - 0x8f}"
    else s!"OP_{n}"

/-- Aggregation key: immediate-width and index variants collapse, so the
table stays readable and the stack-shuffle overhead (`DUP*`/`SWAP*`) is one
row per family. -/
private def opGroup (b : UInt8) : String :=
  let n := b.toNat
  if n == 0x5f || (0x60 ≤ n && n ≤ 0x7f) then "PUSH*"
  else if 0x80 ≤ n && n ≤ 0x8f then "DUP*"
  else if 0x90 ≤ n && n ≤ 0x9f then "SWAP*"
  else opName b

/-- Execute creation bytecode and return a state ready for calls, exactly as
the gas harness does (`CheckSolidityGas.deployForCalls`, without constructor
arguments). `initialState` carries Solidity's fixed nonzero call value, which
would trip the standard `if callvalue() { revert }` prologue — deployment and
calls both run with call value 0. -/
private def deployForCalls (creation : ByteArray) : Option EVM.State :=
  let base0 := initialState creation
  let base := { base0 with
    executionEnv := { base0.executionEnv with weiValue := UInt256.ofNat 0 } }
  let fin := runEvm 3000000 base
  if !fin.isDone || fin.hReturn.size == 0 then none
  else
    let rtBase := initialState fin.hReturn
    let addr := rtBase.executionEnv.address
    let deployed := { (fin.accountMap addr) with
      code := (rtBase.accountMap addr).code }
    let accounts := fin.accountMap.set addr deployed
    some { rtBase with
      accountMap := accounts
      substate := { rtBase.substate with originalAccountMap := accounts } }

private structure Trace where
  steps : Nat := 0
  gas : Nat := 0
  /-- opcode byte → (executed count, attributed gas). -/
  byOp : Array (Nat × Nat) := .replicate 256 (0, 0)
  /-- top-frame pc → (executed count, attributed gas, opcode byte). -/
  byPc : Std.HashMap Nat (Nat × Nat × UInt8) := {}
  halted : Bool := false

/-- Step the EVM one instruction at a time, attributing each step's
top-frame gas drop to the instruction byte at the current pc. Inner-frame
costs of a CALL-family instruction are attributed to that instruction when
the frame resumes. -/
private partial def traceRun (s : EVM.State) (fuel : Nat) (t : Trace) : Trace :=
  if fuel == 0 then t
  else if s.isDone then { t with halted := true }
  else
    let pc := s.pc.toNat
    let op := if pc < s.executionEnv.code.size then s.executionEnv.code.get! pc else 0
    let g0 := s.gasAvailable
    let s' := EVM.stepF s
    let dg := g0 - s'.gasAvailable
    let (c, g) := t.byOp[op.toNat]!
    let (pcC, pcG, _) := t.byPc.getD pc (0, 0, op)
    traceRun s' (fuel - 1)
      { t with
        steps := t.steps + 1
        gas := t.gas + dg
        byOp := t.byOp.set! op.toNat (c + 1, g + dg)
        byPc := t.byPc.insert pc (pcC + 1, pcG + dg, op) }

private def report (label : String) (t : Trace) (topPcs : Nat) : IO Unit := do
  IO.println s!"== {label}: steps={t.steps} gas={t.gas} halted={t.halted}"
  let mut groups : Std.HashMap String (Nat × Nat) := {}
  for i in [0:256] do
    let (c, g) := t.byOp[i]!
    if c > 0 then
      let key := opGroup (UInt8.ofNat i)
      let (c0, g0) := groups.getD key (0, 0)
      groups := groups.insert key (c0 + c, g0 + g)
  for (name, (c, g)) in groups.toArray.qsort (fun a b => a.2.2 > b.2.2) do
    IO.println s!"  {name}\tcount={c}\tgas={g}"
  if topPcs > 0 then
    let pcRows := t.byPc.toArray.qsort (fun a b => a.2.2.1 > b.2.2.1)
    IO.println s!"  -- top {min topPcs pcRows.size} PCs by gas:"
    for (pc, (c, g, op)) in pcRows.extract 0 topPcs do
      IO.println s!"  pc={pc}\t{opName op}\tcount={c}\tgas={g}"

private def usage : String :=
  "usage: TraceSolidityGas <fixture.sol> <solc-path> [<8-hex-digit selector> ...] " ++
    "[--top=N] [--calldata=<hex>]"

private def synthArgWords : String :=
  String.join (List.replicate 8
    "0000000000000000000000000000000000000000000000000000000000000123")

private def isHexDigit (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def main (args : List String) : IO UInt32 := do
  let (flags, positional) := args.partition (·.startsWith "--")
  let mut topPcs := 25
  let mut calldataOverride : Option String := none
  for flag in flags do
    if flag.startsWith "--top=" then
      match (flag.drop "--top=".length).copy.toNat? with
      | some n => topPcs := n
      | none => IO.eprintln usage; return 64
    else if flag.startsWith "--calldata=" then
      calldataOverride := some (flag.drop "--calldata=".length).copy
    else
      IO.eprintln s!"unknown flag {flag}"; IO.eprintln usage; return 64
  match positional with
  | fixture :: solcPath :: sels => do
    unless sels.all (fun s => s.length == 8 && s.all isHexDigit) do
      IO.eprintln "selectors must be 8 hex digits (as printed by solc --hashes)"
      return 64
    let contents ← IO.FS.readFile fixture
    let source := fixtureSource contents
    let selectors ← do
      if sels.isEmpty then
        match ← solcFunctionSelectors solcPath source with
        | .ok found =>
            if found.isEmpty then
              IO.eprintln "fixture declares no external functions"; return 1
            pure found
        | .error e => IO.eprintln e; return 1
      else pure sels
    let ir ← do
      match ← solcUnoptimizedIR solcPath source with
      | .ok ir => pure ir
      | .error e => IO.eprintln e; return 1
    let some ourCreation := compileSource ir
      | do IO.eprintln "this compiler rejected solc's unoptimized IR"; return 1
    let solcCreation ← do
      match ← solcCreationBytecode solcPath source with
      | .ok b => pure b
      | .error e => IO.eprintln e; return 1
    let some ourBase := deployForCalls ourCreation
      | do IO.eprintln "this compiler's deployment did not produce a runtime"; return 1
    let some solcBase := deployForCalls solcCreation
      | do IO.eprintln "solc's deployment did not produce a runtime"; return 1
    IO.println s!"runtime size: ours={ourBase.executionEnv.code.size} \
      solc={solcBase.executionEnv.code.size}"
    for sel in selectors do
      let calldata := Hex.hexToBytes (calldataOverride.getD (sel ++ synthArgWords))
      let mkCall (base : EVM.State) : EVM.State :=
        let env := { base.executionEnv with
          calldata := calldata
          weiValue := UInt256.ofNat 0 }
        { base with
          executionEnv := env
          substate := { base.substate with originalAccountMap := base.accountMap } }
      IO.println s!"\n### selector {sel}"
      let ourT := traceRun (mkCall ourBase) 3000000 {}
      let solcT := traceRun (mkCall solcBase) 3000000 {}
      report "ours" ourT topPcs
      report "solc" solcT topPcs
      if ourT.halted && solcT.halted then
        IO.println s!"-- ours {ourT.gas} vs solc {solcT.gas} \
          ({if solcT.gas == 0 then "n/a" else toString ((ourT.gas * 100) / solcT.gas)}% of solc)"
    return 0
  | _ => do IO.eprintln usage; return 64
