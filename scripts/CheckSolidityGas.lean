import YulParser.Compile
import YulEvmCompilerTests.Solc
import YulEvmCompilerTests.SolcDifferential
import YulEvmCompilerTests.CorpusGas
import YulEvmCompilerTests.SolidityCorpus
import YulEvmCompilerTests.InterpreterFixture

/-!
Compile and gas-check Solidity's `libsolidity/gasTests` fixtures.

Each fixture is a full Solidity contract. This compiler only accepts Yul, so we
route through solc's `--via-ir` lowering — but with the Yul optimizer OFF: solc
lowers the contract to *fully unoptimized* Yul (`--ir`), and this compiler
compiles that. So the pipeline uses only solc's Solidity→Yul front-end and none
of solc's Yul optimizer. Compiling it is the *correctness* check.

For *gas*, our runtime bytecode is compared against solc's own *fully optimized*
runtime (`--bin-runtime --optimize --via-ir`): our non-optimizing compiler on
unoptimized IR versus solc's best. Our runtime is obtained by deploying our
creation bytecode in the executable EVM and taking the code it returns. Both
runtimes then run under the shared deterministic scenarios; where they reach
identical observable behavior, the total gas each spends is summed and this
compiler's total is checked against a pinned baseline (fail if it rises while
solc's is unchanged — solc's total fingerprints the fixture; see CorpusGas).
-/

open System YulParser
open EvmSemantics
open YulEvmCompilerTests.Solc
open YulEvmCompilerTests.CorpusGas
open YulEvmCompilerTests.SolidityCorpus
open YulEvmCompilerTests.InterpreterFixture

/-- Runtime bytecode this compiler produces for a contract: deploy the creation
bytecode in the executable EVM and take the code it returns. Deployment uses a
zero call value, since non-payable constructors revert on value. -/
private def deployRuntime (creation : ByteArray) : ByteArray :=
  let base := initialState creation
  let state := { base with
    executionEnv := { base.executionEnv with weiValue := UInt256.ofNat 0 } }
  (runEvm 100000 state).hReturn

private def usage : String :=
  "usage: CheckSolidityGas <gasTests-dir> <gas-baseline.txt> " ++
    "<solc-path> <expected-solc-version> [--update]"

private def run (dir baselineFile : FilePath)
    (solcPath expectedSolcVersion : String) (update : Bool) : IO UInt32 := do
  match ← checkSolcVersion solcPath expectedSolcVersion with
  | .error message => IO.eprintln message; return 1
  | .ok () => pure ()
  let paths ← dir.walkDir
  let files := paths.filter (fun p => p.extension == some "sol")
    |>.qsort (fun a b => relativeName dir a < relativeName dir b)
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
                match ← solcRuntimeBytecode solcPath source with
                | .error message => compileFailures := compileFailures.push (name, message)
                | .ok solcRuntime =>
                    match fixtureTotalGas name (deployRuntime creation) solcRuntime with
                    | some (ours, solc) => measured := measured.push { fixture := name, ours, solc }
                    | none => pure ()   -- compiled, but not behaviorally gas-comparable
  let compiled := files.size - skipped - compileFailures.size

  if update then
    IO.FS.writeFile baselineFile (render "solidity-gas" expectedSolcVersion measured)
    IO.println s!"Compiled {compiled} contracts; re-pinned {measured.size} gas rows in {baselineFile}."
    unless compileFailures.isEmpty do
      IO.eprintln "Contracts that failed to compile (fix before pinning):"
      for (name, message) in compileFailures do IO.eprintln s!"  {name}: {message}"
      return 1
    return 0

  let baseline ← match ← readBaseline baselineFile with
    | .ok rows => pure rows
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

  IO.println s!"Compiled {compiled}/{files.size - skipped} latest-fork gasTests contracts via solc {expectedSolcVersion} --via-ir (skipped {skipped})."
  IO.println s!"Gas: {measured.size} comparable, {gasRegressions.size} regressions, {gasImproved.size} improved, {gasChanged.size} changed, {gasUnpinned.size} unpinned, {gasStale.size} stale."
  unless compileFailures.isEmpty do
    IO.eprintln "Contracts this compiler failed to compile:"
    for (name, message) in compileFailures do IO.eprintln s!"  {name}: {message}"
  printNames "Gas improved — re-pin with scripts/update-gas.sh to tighten:" gasImproved
  printNames "Fixtures changed upstream/solc — re-pin with scripts/update-gas.sh:" gasChanged
  printNames "Gas-unpinned fixtures — re-pin with scripts/update-gas.sh:" gasUnpinned
  printNames "Stale gas entries — re-pin with scripts/update-gas.sh:" gasStale
  unless gasRegressions.isEmpty do
    IO.eprintln "GAS REGRESSIONS (this compiler now spends more gas):"
    for detail in gasRegressions do IO.eprintln s!"  {detail}"
  return if compileFailures.isEmpty && gasRegressions.isEmpty then 0 else 1

def main (args : List String) : IO UInt32 :=
  match args with
  | [dir, baselineFile, solcPath, expectedSolcVersion] =>
      run dir baselineFile solcPath expectedSolcVersion false
  | [dir, baselineFile, solcPath, expectedSolcVersion, "--update"] =>
      run dir baselineFile solcPath expectedSolcVersion true
  | _ => do IO.eprintln usage; return 64
