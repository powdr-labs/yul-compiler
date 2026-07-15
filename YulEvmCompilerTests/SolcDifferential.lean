import YulEvmCompilerTests.InterpreterFixture

/-!
# Differential execution against solc

Execute bytecode emitted for the same Yul source by this compiler and by solc
inside the same `evm-semantics` environment. The observation deliberately
ignores bytecode, program counters, operand stacks, remaining gas, and zero-only
memory expansion: those may differ between correct compilers. It compares
termination, returned/revert bytes, returndata, nonzero memory, account
existence/nonces/balances/storage, logs, self-destructs, and storage refunds.

Each program runs both from Solidity's interpreter-test default environment and
from a second state with patterned calldata plus pre-populated persistent and
transient storage. This exercises input-dependent branches without assuming a
particular source fixture format beyond valid Yul.
-/

namespace YulEvmCompilerTests.SolcDifferential

open EvmSemantics
open YulEvmCompilerTests.InterpreterFixture

structure ObservedLog where
  address : AccountAddress
  topics : Array UInt256
  payload : ByteArray
  deriving BEq

structure ObservedAccount where
  address : AccountAddress
  nonce : UInt256
  balance : UInt256
  hasCode : Bool
  storage : Array Entry
  transientStorage : Array Entry
  deriving BEq, Repr

structure Observation where
  halt : HaltKind
  output : ByteArray
  returnData : ByteArray
  memory : Array Entry
  accounts : Array ObservedAccount
  logs : Array ObservedLog
  selfDestructs : Array AccountAddress
  refund : UInt256
  deriving BEq

private def word (n : Nat) : UInt256 := UInt256.ofNat n

private def sortEntries (entries : Array Entry) : Array Entry :=
  entries.qsort (fun a b => a.key.toNat < b.key.toNat)

private def storageEntries (storage : Storage) : Array Entry :=
  storage.toList.foldl (init := #[]) fun entries (key, value) =>
    if value.toNat == 0 then entries else entries.push { key, value }
  |> sortEntries

private def accountObservation
    (executingAddress address : AccountAddress) (account : Account) : ObservedAccount :=
  {
    address
    nonce := account.nonce
    balance := account.balance
    -- The executing account necessarily contains the compiler output, whose
    -- encoding and even empty-program representation may differ. Code created
    -- at other addresses is still observed by presence, but not by exact bytes.
    hasCode := address != executingAddress && account.code.size != 0
    storage := storageEntries account.storage
    transientStorage := storageEntries account.tstorage
  }

private def accountIsObservable (account : ObservedAccount) : Bool :=
  account.nonce.toNat != 0 || account.balance.toNat != 0 || account.hasCode ||
    !account.storage.isEmpty || !account.transientStorage.isEmpty

private def observedAccounts (state : EVM.State) : Array ObservedAccount :=
  let accounts := state.accountMap.toList.foldl (init := #[]) fun accounts (address, account) =>
    let observed := accountObservation state.executionEnv.address address account
    if accountIsObservable observed then accounts.push observed else accounts
  accounts.qsort (fun a b => a.address.val < b.address.val)

private def observedLogs (state : EVM.State) : Array ObservedLog :=
  state.substate.logSeries.map fun entry =>
    { address := entry.address, topics := entry.topics, payload := entry.data }

def observe (state : EVM.State) : Observation :=
  let localState := actualState state
  {
    halt := state.halt
    output := state.hReturn
    returnData := state.returnData
    memory := localState.memory
    accounts := observedAccounts state
    logs := observedLogs state
    selfDestructs := state.substate.selfDestructList
    refund := state.substate.refundBalance
  }

private def patternedCalldata : ByteArray :=
  Hex.hexToBytes
    "000102030405060708090a0b0c0d0e0f" ++
  Hex.hexToBytes
    "fffefdfcfbfaf9f8f7f6f5f4f3f2f1f0" ++
  Hex.hexToBytes
    "112233445566778899aabbccddeeff00"

/-- Add nontrivial calldata and storage while keeping the code-dependent parts
of `initialState` intact. `originalAccountMap` is updated with the same seeded
world so SSTORE gas/refund behavior starts from the correct original values. -/
private def patternedState (code : ByteArray) : EVM.State :=
  let state := initialState code
  let address := state.executionEnv.address
  let account := state.accountMap address
  let storage := account.storage
    |>.set (word 0) (word 7)
    |>.set (word 1) (word (2 ^ 255 + 19))
    |>.set (word 0x40) (word 0xdeadbeef)
  let tstorage := account.tstorage
    |>.set (word 0) (word 11)
    |>.set (word 2) (word 0xcafebabe)
  let accounts := state.accountMap.set address { account with storage, tstorage }
  {
    state with
    accountMap := accounts
    substate := { state.substate with originalAccountMap := accounts }
    executionEnv := {
      state.executionEnv with
      calldata := patternedCalldata
      weiValue := word 0x123456
      gasPrice := word 0xabcdef
    }
  }

private def scenarios : Array (String × (ByteArray → EVM.State)) := #[
  ("default", initialState),
  ("patterned-input", patternedState)
]

private inductive RunResult where
  | timedOut
  | halted (observation : Observation)

private def runToResult
    (scenario : ByteArray → EVM.State) (code : ByteArray) (fuel : Nat) : RunResult :=
  let state := runEvm fuel (scenario code)
  if state.isDone then .halted (observe state) else .timedOut

private def mismatchSection (ours solc : Observation) : String :=
  if ours.halt != solc.halt then "halt kind"
  else if ours.output != solc.output then "return/revert output"
  else if ours.returnData != solc.returnData then "returndata"
  else if ours.memory != solc.memory then "nonzero memory"
  else if ours.accounts != solc.accounts then "accounts/storage"
  else if ours.logs != solc.logs then "logs"
  else if ours.selfDestructs != solc.selfDestructs then "self-destruct list"
  else if ours.refund != solc.refund then "storage refund"
  else "unknown observation"

/-- Compare the observable behavior of two bytecode sequences under every
fixed scenario. The first bytecode is conventionally this compiler's output
and the second is solc's output. -/
def compareBytecode
    (ours solc : ByteArray) (fuel : Nat := 100000) : Except String Unit := do
  for (name, scenario) in scenarios do
    match runToResult scenario ours fuel, runToResult scenario solc fuel with
    | .timedOut, .timedOut => pure ()
    | .timedOut, .halted solcObservation =>
        throw (s!"{name}: Yul compiler did not halt within {fuel} steps, " ++
          s!"but solc halted with {repr solcObservation.halt}")
    | .halted oursObservation, .timedOut =>
        throw (s!"{name}: solc did not halt within {fuel} steps, " ++
          s!"but Yul compiler halted with {repr oursObservation.halt}")
    | .halted oursObservation, .halted solcObservation =>
        if oursObservation != solcObservation then
          throw (s!"{name} observable-state mismatch: " ++
            mismatchSection oursObservation solcObservation)

/-- Empty bytecode and an explicit STOP are behaviorally equivalent even
though the executing account's code representation differs. -/
example : compareBytecode .empty (Hex.hexToBytes "00") 10 = .ok () := by
  native_decide

end YulEvmCompilerTests.SolcDifferential
