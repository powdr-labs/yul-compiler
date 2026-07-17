import YulParser.Compile
import YulEvmCompilerTests.Solc
import YulEvmCompilerTests.SolcDifferential
import YulEvmCompilerTests.CorpusGas
import YulEvmCompilerTests.SolidityCorpus
import YulEvmCompilerTests.Parallel

/-!
Compile each applicable fixture with both this compiler and a pinned solc,
execute both bytecode sequences under the same deterministic environments, and
compare observable behavior. The exact failure set is checked against a text
baseline: new failures and stale entries both fail the run.

This runner intentionally compares behavior rather than bytecode. solc uses
different PUSH widths, labels, stack allocation, object layout, and optional
normalization while remaining semantically equivalent.

The optional shard arguments select fixtures by the same stable fixture-name
hash that seeds generated EVM states. Known failures are filtered by that hash
too, so every shard independently rejects new and stale baseline entries.
-/

open System YulParser
open EvmSemantics
open YulEvmCompilerTests.Solc
open YulEvmCompilerTests.SolcDifferential
open YulEvmCompilerTests.CorpusGas
open YulEvmCompilerTests.SolidityCorpus
open YulEvmCompilerTests.Parallel (detectJobs parMap)

private structure Shard where
  index : Nat
  count : Nat

private def Shard.contains (shard : Shard) (name : String) : Bool :=
  fixtureSeed name % shard.count == shard.index

private def selected (shard : Option Shard) (name : String) : Bool :=
  match shard with
  | none => true
  | some shard => shard.contains name

private def shardDescription : Option Shard → String
  | none => ""
  | some shard => s!" shard {shard.index + 1}/{shard.count}"

/-- The per-fixture verdict, accumulated identically to the original sequential
loop but computed independently so fixtures can be processed concurrently. -/
private structure FileOutcome where
  metadataError : Option (String × String) := none
  skipped : Bool := false
  checked : Bool := false
  failure : Option (String × String) := none
  gas : Option GasRow := none

/-- Compile one fixture with both compilers and compare — the body of the old
loop, extracted so it is a pure `IO` unit of work with no shared mutable state. -/
private def processFile (corpusDir : FilePath) (solcPath : String)
    (path : FilePath) : IO FileOutcome := do
  let name := relativeName corpusDir path
  let contents ← IO.FS.readFile path
  match runsOnLatestFork contents with
  | .error message => return { metadataError := some (name, message) }
  | .ok false => return { skipped := true }
  | .ok true =>
      let source := fixtureSource contents
      match compileSource source with
      | none => return { checked := true, failure := some (name, "Yul compiler failed") }
      | some ours =>
          match ← compileWithSolc solcPath source with
          | .error message => return { checked := true, failure := some (name, message) }
          | .ok solc =>
              match compareBytecode ours solc (scenarioSeed := fixtureSeed name) with
              | .error message => return { checked := true, failure := some (name, message) }
              | .ok () =>
                  match fixtureTotalGas name ours solc with
                  | some (ours, solc) =>
                      return { checked := true, gas := some { fixture := name, ours, solc } }
                  | none => return { checked := true }

private def run (suiteName : String) (corpusDir knownFailuresFile gasBaselineFile : FilePath)
    (solcPath expectedSolcVersion : String) (shard : Option Shard) : IO UInt32 := do
  match ← checkSolcVersion solcPath expectedSolcVersion with
  | .error message =>
      IO.eprintln message
      return 1
  | .ok () => pure ()
  let gasBaseline ← match ← readBaseline gasBaselineFile with
    | .ok rows => pure (rows.filter (fun row => selected shard row.fixture))
    | .error message => IO.eprintln s!"{gasBaselineFile}: {message}"; return 1
  let paths ← corpusDir.walkDir
  let allFiles := paths.filter (fun path => path.extension == some "yul")
    |>.qsort (fun a b => relativeName corpusDir a < relativeName corpusDir b)
  if allFiles.isEmpty then
    IO.eprintln s!"{corpusDir}: found no .yul fixtures"
    return 1
  let files := allFiles.filter (fun path => selected shard (relativeName corpusDir path))
  let allowed := (← readKnownFailures knownFailuresFile).filter (selected shard)
  let mut failures : Array (String × String) := #[]
  let mut metadataErrors : Array (String × String) := #[]
  let mut measuredGas : Array GasRow := #[]
  let mut checked := 0
  let mut skipped := 0
  let jobs ← detectJobs
  let outcomes : Array FileOutcome ← parMap jobs files (processFile corpusDir solcPath)
  for outcome in outcomes do
    if let some entry := outcome.metadataError then metadataErrors := metadataErrors.push entry
    if outcome.skipped then skipped := skipped + 1
    if outcome.checked then checked := checked + 1
    if let some entry := outcome.failure then failures := failures.push entry
    if let some row := outcome.gas then measuredGas := measuredGas.push row

  let failureNames := failures.map (·.1)
  let unexpected := failures.filter (fun failure => !allowed.contains failure.1)
  let stale := allowed.filter (!failureNames.contains ·)
  let knownFailureCount := failures.size - unexpected.size

  -- Gas dimension: classify each measured fixture against its pinned row. Only
  -- a genuine regression (ours above the pin while solc is unchanged) fails;
  -- upstream/solc changes and new fixtures are re-pin notices, not failures.
  let mut gasRegressions : Array String := #[]
  let mut gasImproved : Array String := #[]
  let mut gasChanged : Array String := #[]
  let mut gasUnpinned : Array String := #[]
  for row in measuredGas do
    match find gasBaseline row.fixture with
    | none => gasUnpinned := gasUnpinned.push row.fixture
    | some pinned =>
        let detail := s!"{row.fixture}: ours {row.ours} vs pinned {pinned.ours} (solc {row.solc})"
        let changed := s!"{row.fixture}: solc {row.solc} vs pinned {pinned.solc}"
        match classify row pinned with
        | .regression => gasRegressions := gasRegressions.push detail
        | .improved => gasImproved := gasImproved.push detail
        | .changed => gasChanged := gasChanged.push changed
        | .ok => pure ()
  let measuredNames := measuredGas.map (·.fixture)
  let gasStale := (gasBaseline.filter (fun row => !measuredNames.contains row.fixture)).map (·.fixture)

  IO.println (s!"Differentially checked {checked} latest-fork Solidity {suiteName}" ++
    s!"{shardDescription shard} tests " ++
    s!"against solc {expectedSolcVersion}: {checked - failures.size} matched, " ++
    s!"{failures.size} failed ({knownFailureCount} known); " ++
    s!"skipped {skipped} outside Osaka.")
  IO.println (s!"Gas: {measuredGas.size} comparable, {gasRegressions.size} regressions, " ++
    s!"{gasImproved.size} improved, {gasChanged.size} changed upstream, " ++
    s!"{gasUnpinned.size} unpinned, {gasStale.size} stale.")
  -- Machine-readable aggregate for the PR summary comment. `mode=codegen`: both
  -- sides assemble the *same* Yul with no optimizer (solc here is
  -- `--strict-assembly` without `--optimize`), so this measures backend codegen
  -- parity, NOT this compiler against solc's Yul optimizer.
  IO.println (s!"Gas totals: suite={suiteName} mode=codegen " ++
    s!"ours={measuredGas.foldl (fun a r => a + r.ours) 0} " ++
    s!"solc={measuredGas.foldl (fun a r => a + r.solc) 0} comparable={measuredGas.size}")
  unless metadataErrors.isEmpty do
    IO.eprintln s!"Invalid {suiteName} EVMVersion metadata:"
    for (name, message) in metadataErrors do
      IO.eprintln s!"  {name}: {message}"
  unless unexpected.isEmpty do
    IO.eprintln s!"Unexpected {suiteName} solc differential failures:"
    for (name, message) in unexpected do
      IO.eprintln s!"  {name}: {message}"
  printNames s!"Stale {suiteName} solc-differential entries (remove after review):" stale
  printNames s!"{suiteName} gas improved — re-pin with scripts/update-gas.sh to tighten:" gasImproved
  printNames s!"{suiteName} fixtures changed upstream — re-pin with scripts/update-gas.sh:" gasChanged
  printNames s!"{suiteName} gas-unpinned fixtures — re-pin with scripts/update-gas.sh:" gasUnpinned
  printNames s!"Stale {suiteName} gas entries — re-pin with scripts/update-gas.sh:" gasStale
  unless gasRegressions.isEmpty do
    IO.eprintln s!"{suiteName} GAS REGRESSIONS (this compiler now spends more gas):"
    for detail in gasRegressions do
      IO.eprintln s!"  {detail}"
  return if unexpected.isEmpty && stale.isEmpty && metadataErrors.isEmpty
    && gasRegressions.isEmpty then 0 else 1

private def usage : String :=
  "usage: CheckSoliditySolcDifferential <suite-name> <corpus-dir> " ++
    "<known-failures.txt> <gas-baseline.txt> <solc-path> <expected-solc-version> " ++
    "[<shard-index> <shard-count>]"

private def parseShard (rawIndex rawCount : String) : Except String Shard := do
  let index ← match rawIndex.toNat? with
    | some index => pure index
    | none => throw s!"invalid shard index: {rawIndex}"
  let count ← match rawCount.toNat? with
    | some count => pure count
    | none => throw s!"invalid shard count: {rawCount}"
  if count == 0 then throw "shard count must be positive"
  if index >= count then throw s!"shard index {index} is outside count {count}"
  return { index, count }

def main (args : List String) : IO UInt32 :=
  match args with
  | [suiteName, corpusDir, knownFailuresFile, gasBaselineFile, solcPath, expectedSolcVersion] =>
      run suiteName corpusDir knownFailuresFile gasBaselineFile solcPath expectedSolcVersion none
  | [suiteName, corpusDir, knownFailuresFile, gasBaselineFile, solcPath, expectedSolcVersion,
      rawShardIndex, rawShardCount] => do
      match parseShard rawShardIndex rawShardCount with
      | .ok shard =>
          run suiteName corpusDir knownFailuresFile gasBaselineFile solcPath expectedSolcVersion
            (some shard)
      | .error message =>
          IO.eprintln message
          IO.eprintln usage
          return 64
  | _ => do
      IO.eprintln usage
      return 64
