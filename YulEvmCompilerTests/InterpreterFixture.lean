import YulParser.Compile
import EvmSemantics.EVM.StepF
import EvmSemantics.Data.Hex

/-!
# Solidity Yul interpreter fixtures

Compile a brace-delimited Yul source file, execute its bytecode with
`evm-semantics`, and compare the resulting memory, storage, and transient
storage with the dumps embedded after the fixture's `// ----` marker.

The initial environment mirrors Solidity's `YulInterpreterTest` defaults.
Only nonzero values appear in Solidity's dumps, so comparison is exact after
zero-valued entries have been removed from both sides.
-/

namespace YulEvmCompilerTests.InterpreterFixture

open YulEvmCompiler YulParser
open EvmSemantics

structure Entry where
  key : UInt256
  value : UInt256
  deriving BEq, Repr

structure ExpectedState where
  memory : Array Entry
  storage : Array Entry
  transientStorage : Array Entry
  deriving BEq, Repr

private inductive Section where
  | none
  | trace
  | memory
  | storage
  | transientStorage

private structure ExpectationBuilder where
  currentSection : Section := .none
  sawMarker : Bool := false
  sawMemory : Bool := false
  sawStorage : Bool := false
  sawTransientStorage : Bool := false
  memory : Array Entry := #[]
  storage : Array Entry := #[]
  transientStorage : Array Entry := #[]

private def isHexDigit (char : Char) : Bool :=
  ('0' <= char && char <= '9') ||
    ('a' <= char && char <= 'f') ||
    ('A' <= char && char <= 'F')

private def isHexString (text : String) : Bool :=
  !text.isEmpty && text.all isHexDigit

private def parseEntry (line : String) : Except String Entry :=
  match line.splitOn ":" with
  | [key, value] =>
      let key := key.trimAscii.copy
      let value := value.trimAscii.copy
      if !isHexString key || !isHexString value then
        .error s!"malformed state entry: {line}"
      else
        .ok { key := Hex.hexToUInt256 key, value := Hex.hexToUInt256 value }
  | _ => .error s!"malformed state entry: {line}"

private def parseExpectationLine
    (builder : ExpectationBuilder) (rawLine : String) : Except String ExpectationBuilder := do
  let line := rawLine.trimAscii.copy
  if !builder.sawMarker then
    if line == "// ----" then
      return { builder with sawMarker := true }
    return builder
  if !line.startsWith "//" then
    return builder
  let text := (line.drop 2).trimAscii.copy
  match text with
  | "Trace:" => return { builder with currentSection := .trace }
  | "Memory dump:" =>
      return { builder with currentSection := .memory, sawMemory := true }
  | "Storage dump:" =>
      return { builder with currentSection := .storage, sawStorage := true }
  | "Transient storage dump:" =>
      return { builder with
        currentSection := .transientStorage, sawTransientStorage := true }
  | "" => return builder
  | _ =>
      match builder.currentSection with
      | .memory =>
          return { builder with memory := builder.memory.push (← parseEntry text) }
      | .storage =>
          return { builder with storage := builder.storage.push (← parseEntry text) }
      | .transientStorage =>
          return { builder with
            transientStorage := builder.transientStorage.push (← parseEntry text) }
      | .trace | .none => return builder

private def sortEntries (entries : Array Entry) : Array Entry :=
  entries.qsort (fun a b => a.key.toNat < b.key.toNat)

/-- Parse the three post-state dumps embedded in a Solidity Yul interpreter fixture. -/
def parseExpectedState (source : String) : Except String ExpectedState := do
  let builder ← source.splitOn "\n" |>.foldlM parseExpectationLine {}
  if !builder.sawMarker then
    throw "missing // ---- expectation marker"
  if !builder.sawMemory then
    throw "missing Memory dump expectation"
  if !builder.sawStorage then
    throw "missing Storage dump expectation"
  if !builder.sawTransientStorage then
    throw "missing Transient storage dump expectation"
  return {
    memory := sortEntries builder.memory
    storage := sortEntries builder.storage
    transientStorage := sortEntries builder.transientStorage
  }

private def word (n : Nat) : UInt256 := UInt256.ofNat n

private def solidityBlockHash (number : UInt256) : UInt256 :=
  if number.toNat >= 1024 || number.toNat + 256 < 1024 then
    0
  else
    word 0xaaaaaaaa + (number - word 1024 - word 256)

/-- Solidity's fixed environment for `YulInterpreterTest`. -/
def initialState (code : ByteArray) : EVM.State :=
  let address := Hex.hexToAddress "11111111"
  let otherAddress := AccountAddress.ofNat (address.val + 1)
  let header : BlockHeader := {
    coinbase := Hex.hexToAddress "77777777"
    timestamp := Hex.hexToUInt256 "88888888"
    number := word 1024
    prevRandao := word (2 ^ 64 + 1)
    gasLimit := word 4000000
    baseFeePerGas := word 7
    chainId := word 1
    blockHash := solidityBlockHash
    blobBaseFee := word 1
  }
  let env : ExecutionEnv := {
    address
    origin := Hex.hexToAddress "33333333"
    caller := Hex.hexToAddress "44444444"
    weiValue := Hex.hexToUInt256 "55555555"
    calldata := .empty
    code
    codeAddr := address
    gasPrice := Hex.hexToUInt256 "66666666"
    header
    depth := 0
    permitStateMutation := true
    blobVersionedHashes := #[]
    fork := .Osaka
  }
  let selfAccount : Account := {
    Account.empty with
    balance := Hex.hexToUInt256 "22223333"
    code
  }
  -- Solidity's abstract interpreter returns 0x22222222 for non-self
  -- balances. The corpus currently probes `address() + 1`, so seed that
  -- concrete account in the finite EVM world map as well.
  let otherAccount : Account := {
    Account.empty with balance := Hex.hexToUInt256 "22222222"
  }
  let accounts := AccountMap.empty.set address selfAccount
    |>.set otherAddress otherAccount
  let substate := { Substate.empty with originalAccountMap := accounts }
  let state : EVM.State := Inhabited.default
  { state with
    pc := 0
    stack := []
    execLength := 0
    halt := .Running
    callStack := []
    gasAvailable := 100000000
    activeWords := 0
    memory := .empty
    returnData := .empty
    hReturn := .empty
    accountMap := accounts
    substate
    executionEnv := env
  }

/-- Drive the executable EVM semantics until it halts or exhausts the test fuel. -/
def runEvm : Nat → EVM.State → EVM.State
  | 0, state => state
  | fuel + 1, state =>
      if state.isDone then state else runEvm fuel (EVM.stepF state)

private def memoryEntries (memory : ByteArray) : Array Entry := Id.run do
  let mut entries := #[]
  let wordCount := (memory.size + 31) / 32
  for index in [:wordCount] do
    let offset := index * 32
    let value := MachineState.readWord memory offset
    if value.toNat != 0 then
      entries := entries.push { key := word offset, value }
  return entries

private def storageEntries (storage : Storage) : Array Entry :=
  storage.toList.foldl (init := #[]) fun entries (key, value) =>
    if value.toNat == 0 then entries else entries.push { key, value }
  |> sortEntries

def actualState (state : EVM.State) : ExpectedState :=
  let account := state.accountMap state.executionEnv.address
  {
    memory := memoryEntries state.memory
    storage := storageEntries account.storage
    transientStorage := storageEntries account.tstorage
  }

private def describeEntries (entries : Array Entry) : String :=
  if entries.isEmpty then "[]"
  else String.intercalate ", " (entries.toList.map fun entry =>
    s!"({entry.key.toNat}: {entry.value.toNat})")

private def compareSection (name : String) (expected actual : Array Entry) : Except String Unit :=
  if expected == actual then
    .ok ()
  else
    .error (s!"{name} mismatch\n  expected: {describeEntries expected}" ++
      s!"\n  actual:   {describeEntries actual}")

/-- Compile, execute, and check one complete Solidity Yul interpreter fixture. -/
def checkFixture (source : String) (fuel : Nat := 100000) : Except String Unit := do
  let expected ← parseExpectedState source
  let instructions ← match compileSource source with
    | some instructions => pure instructions
    | none => throw "Yul parsing or compilation failed"
  let state := runEvm fuel (initialState (assemble instructions))
  if !state.isDone then
    throw s!"EVM execution did not halt within {fuel} steps"
  match state.halt with
  | .Exception exception => throw s!"EVM execution failed: {repr exception}"
  | .Running => throw "EVM execution is still running"
  | .Success | .Returned | .Reverted => pure ()
  let actual := actualState state
  compareSection "memory" expected.memory actual.memory
  compareSection "storage" expected.storage actual.storage
  compareSection "transient storage" expected.transientStorage actual.transientStorage

end YulEvmCompilerTests.InterpreterFixture
