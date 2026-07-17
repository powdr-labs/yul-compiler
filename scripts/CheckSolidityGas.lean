import YulParser.Compile
import YulEvmCompilerTests.Solc
import YulEvmCompilerTests.SolcDifferential
import YulEvmCompilerTests.CorpusGas
import YulEvmCompilerTests.SolidityCorpus
import YulEvmCompilerTests.InterpreterFixture
import YulEvmCompilerTests.SolTest

/-!
Compile and gas-check Solidity's `libsolidity/gasTests` fixtures.

Each fixture is a full Solidity contract. This compiler only accepts Yul, so we
route through solc's `--via-ir` lowering — but with the Yul optimizer OFF: solc
lowers the contract to *fully unoptimized* Yul (`--ir`), and this compiler
compiles that. So the pipeline uses only solc's Solidity→Yul front-end and none
of solc's Yul optimizer. Compiling it is the *correctness* check.

For *gas*, both this compiler's and solc's *fully optimized* creation bytecode
(`--bin --optimize --via-ir`) are deployed in the executable EVM (running the
constructor), and the contract's calls are replayed on each. semanticTests
fixtures specify their own calls in the `// ----` section (`f(uint256): 42 ->
42`); those exact calls — arguments already in flattened ABI form — are used, so
real work is exercised, state persists across the sequence, and outputs are
cross-checked. gasTests have no call spec, so each external function is called
once with synthetic argument words. Over the calls that reach identical
observable behavior, the gas each spends is summed and this compiler's total is
checked against a pinned baseline (fail if it rises while solc's is unchanged —
solc's total fingerprints the fixture; see CorpusGas).
-/

open System YulParser
open EvmSemantics
open YulEvmCompilerTests.Solc
open YulEvmCompilerTests.CorpusGas
open YulEvmCompilerTests.SolidityCorpus
open YulEvmCompilerTests.InterpreterFixture
open YulEvmCompilerTests.SolcDifferential (observe gasUsed fixtureSeed)
open YulEvmCompilerTests.SolTest (Call parseSpec)

/-- Optional sharding by the same stable fixture-name hash the differential uses,
so the large semanticTests corpus can be split across CI jobs and its baseline
filtered per shard. -/
private structure Shard where
  index : Nat
  count : Nat

private def selected (shard : Option Shard) (name : String) : Bool :=
  match shard with
  | none => true
  | some s => fixtureSeed name % s.count == s.index

/-- Eight nonzero argument words appended after a selector, used only for the
gasTests corpus (which specifies gas per function but no call arguments). It
decodes as value-typed arguments so real work is charged; functions taking
dynamic-typed arguments revert on both sides, which stays gas-comparable. -/
private def argWords : String :=
  String.join (List.replicate 8 "0000000000000000000000000000000000000000000000000000000000000123")

/-- STOP and an empty RETURN are the same successful outcome, but our compiler
emits RETURN where solc's optimizer emits STOP for void functions. Normalize the
two so such calls stay gas-comparable; the returned bytes are still compared
(via the output field), so a real difference is not hidden. -/
private def normHalt : HaltKind → HaltKind
  | .Success => .Returned
  | h => h

/-- Behavioral equality for a call, tolerant of the STOP/RETURN distinction. -/
private def sameOutcome (a b : EVM.State) : Bool :=
  normHalt a.halt == normHalt b.halt &&
    { observe a with halt := .Returned } == { observe b with halt := .Returned }

/-- Deploy creation bytecode (with constructor arguments appended) and return a
state ready for calls: the returned runtime installed as the account's code, and
the storage the constructor wrote kept in place. `none` if the constructor does
not cleanly return runtime code. -/
private def deployForCalls (creation ctorArgs : ByteArray) (ctorValue : Nat) : Option EVM.State :=
  let base := initialState (creation ++ ctorArgs)
  let start := { base with
    executionEnv := { base.executionEnv with weiValue := UInt256.ofNat ctorValue } }
  let fin := runEvm 3000000 start
  if !fin.isDone || fin.hReturn.size == 0 then none
  else
    let rtBase := initialState fin.hReturn
    let addr := rtBase.executionEnv.address
    let deployed := { (rtBase.accountMap addr) with
      storage := (fin.accountMap addr).storage
      tstorage := (fin.accountMap addr).tstorage }
    let accounts := rtBase.accountMap.set addr deployed
    some { rtBase with
      accountMap := accounts
      substate := { rtBase.substate with originalAccountMap := accounts } }

private def withCall (state : EVM.State) (call : Call) : EVM.State :=
  { state with
    executionEnv := { state.executionEnv with
      calldata := call.calldata, weiValue := UInt256.ofNat call.value }
    substate := { state.substate with originalAccountMap := state.accountMap } }

/-- Replay a call sequence on both deployments, summing per-call gas over the
leading run of behaviorally-identical calls. State persists across calls (as in
a real test), so a divergence or non-halt ends the sequence — the two worlds
would part after it. `none` if no call was comparable. -/
private def replayCalls (ourBase solcBase : EVM.State) (calls : Array Call) : Option (Nat × Nat) := Id.run do
  let mut ourState := ourBase
  let mut solcState := solcBase
  let mut total : Option (Nat × Nat) := none
  for call in calls do
    let os := withCall ourState call
    let ss := withCall solcState call
    let ourFinal := runEvm 3000000 os
    let solcFinal := runEvm 3000000 ss
    if !(ourFinal.isDone && solcFinal.isDone && sameOutcome ourFinal solcFinal) then break
    total := match total with
      | none => some (gasUsed os ourFinal, gasUsed ss solcFinal)
      | some (ao, as) => some (ao + gasUsed os ourFinal, as + gasUsed ss solcFinal)
    ourState := { ourState with accountMap := ourFinal.accountMap }
    solcState := { solcState with accountMap := solcFinal.accountMap }
  return total

private def usage : String :=
  "usage: CheckSolidityGas <contracts-dir> <gas-baseline.txt> " ++
    "<solc-path> <expected-solc-version> [--lenient] [--update]"

/-- `lenient`: treat contracts this compiler cannot handle as skips rather than
failures. Off for the curated gasTests (every contract must compile); on for the
broad semanticTests corpus, where many contracts use unsupported features and
only the gas of the compilable subset is pinned. -/
private def run (dir baselineFile : FilePath)
    (solcPath expectedSolcVersion : String) (lenient update : Bool)
    (shard : Option Shard) : IO UInt32 := do
  match ← checkSolcVersion solcPath expectedSolcVersion with
  | .error message => IO.eprintln message; return 1
  | .ok () => pure ()
  let paths ← dir.walkDir
  let files := paths.filter (fun p => p.extension == some "sol")
    |>.qsort (fun a b => relativeName dir a < relativeName dir b)
    |>.filter (fun p => selected shard (relativeName dir p))
  if files.isEmpty then
    IO.eprintln s!"{dir}: found no .sol fixtures"
    return 1
  let mut measured : Array GasRow := #[]
  let mut compileFailures : Array (String × String) := #[]
  let mut skipped := 0
  for path in files do
    let name := relativeName dir path
    let contents ← IO.FS.readFile path
    match runsOnLatestFork contents with
    | .error message => compileFailures := compileFailures.push (name, s!"metadata: {message}")
    | .ok false => skipped := skipped + 1
    | .ok true =>
        let source := fixtureSource contents
        match ← solcUnoptimizedIR solcPath source with
        | .error message => compileFailures := compileFailures.push (name, message)
        | .ok ir =>
            match compileSource ir with
            | none =>
                compileFailures := compileFailures.push (name, "this compiler rejected solc's optimized IR")
            | some creation =>
                match ← solcCreationBytecode solcPath source with
                | .error message => compileFailures := compileFailures.push (name, message)
                | .ok solcCreation =>
                    -- Replay the fixture's own specified calls (semanticTests).
                    -- With no call spec (gasTests) fall back to one synthetic
                    -- call per external function selector.
                    let spec := parseSpec contents
                    let calls ← do
                      if spec.calls.isEmpty then
                        match ← solcFunctionSelectors solcPath source with
                        | .error _ => pure #[]
                        | .ok sels => pure (sels.toArray.map fun s =>
                            ({ sig := s, value := 0,
                               calldata := Hex.hexToBytes (s ++ argWords) } : Call))
                      else pure spec.calls
                    match deployForCalls creation spec.ctorArgs spec.ctorValue,
                          deployForCalls solcCreation spec.ctorArgs spec.ctorValue with
                    | some ourBase, some solcBase =>
                        match replayCalls ourBase solcBase calls with
                        | some (ours, solc) => measured := measured.push { fixture := name, ours, solc }
                        | none => pure ()   -- compiled, but no comparable call
                    | _, _ => pure ()       -- deployment did not produce runtime
  let compiled := files.size - skipped - compileFailures.size

  if update then
    IO.FS.writeFile baselineFile (render "solidity-gas" expectedSolcVersion measured)
    IO.println s!"Compiled {compiled} contracts; re-pinned {measured.size} gas rows in {baselineFile}."
    unless lenient || compileFailures.isEmpty do
      IO.eprintln "Contracts that failed to compile (fix before pinning):"
      for (name, message) in compileFailures do IO.eprintln s!"  {name}: {message}"
      return 1
    return 0

  let baseline ← match ← readBaseline baselineFile with
    | .ok rows => pure (rows.filter (fun r => selected shard r.fixture))
    | .error message => IO.eprintln s!"{baselineFile}: {message}"; return 1
  let mut gasRegressions : Array String := #[]
  let mut gasImproved : Array String := #[]
  let mut gasChanged : Array String := #[]
  let mut gasUnpinned : Array String := #[]
  for row in measured do
    match find baseline row.fixture with
    | none => gasUnpinned := gasUnpinned.push row.fixture
    | some pinned =>
        let detail := s!"{row.fixture}: ours {row.ours} vs pinned {pinned.ours} (solc {row.solc})"
        match classify row pinned with
        | .regression => gasRegressions := gasRegressions.push detail
        | .improved => gasImproved := gasImproved.push detail
        | .changed => gasChanged := gasChanged.push s!"{row.fixture}: solc {row.solc} vs pinned {pinned.solc}"
        | .ok => pure ()
  let measuredNames := measured.map (·.fixture)
  let gasStale := (baseline.filter (fun r => !measuredNames.contains r.fixture)).map (·.fixture)

  let unsupported := if lenient then compileFailures.size else 0
  IO.println s!"Compiled {compiled}/{files.size - skipped} latest-fork contracts via solc {expectedSolcVersion} --via-ir (skipped {skipped}, unsupported {unsupported})."
  IO.println s!"Gas: {measured.size} comparable, {gasRegressions.size} regressions, {gasImproved.size} improved, {gasChanged.size} changed, {gasUnpinned.size} unpinned, {gasStale.size} stale."
  unless lenient || compileFailures.isEmpty do
    IO.eprintln "Contracts this compiler failed to compile:"
    for (name, message) in compileFailures do IO.eprintln s!"  {name}: {message}"
  printNames "Gas improved — re-pin with scripts/update-gas.sh to tighten:" gasImproved
  printNames "Fixtures changed upstream/solc — re-pin with scripts/update-gas.sh:" gasChanged
  printNames "Gas-unpinned fixtures — re-pin with scripts/update-gas.sh:" gasUnpinned
  printNames "Stale gas entries — re-pin with scripts/update-gas.sh:" gasStale
  unless gasRegressions.isEmpty do
    IO.eprintln "GAS REGRESSIONS (this compiler now spends more gas):"
    for detail in gasRegressions do IO.eprintln s!"  {detail}"
  return if (lenient || compileFailures.isEmpty) && gasRegressions.isEmpty then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | dir :: baselineFile :: solcPath :: expectedSolcVersion :: rest =>
      let flags := rest.filter (·.startsWith "--")
      let nums := rest.filter (fun s => !s.startsWith "--")
      if !flags.all (fun f => f == "--update" || f == "--lenient") then
        IO.eprintln usage; return 64
      else
        let shard ← match nums with
          | [] => pure none
          | [rawIndex, rawCount] =>
              match rawIndex.toNat?, rawCount.toNat? with
              | some index, some count =>
                  if count == 0 || index >= count then
                    IO.eprintln "invalid shard"; return 64
                  else pure (some { index, count })
              | _, _ => IO.eprintln usage; return 64
          | _ => IO.eprintln usage; return 64
        run dir baselineFile solcPath expectedSolcVersion
          (flags.contains "--lenient") (flags.contains "--update") shard
  | _ => IO.eprintln usage; return 64
