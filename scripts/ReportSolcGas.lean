import YulParser.Compile
import YulEvmCompilerTests.Solc
import YulEvmCompilerTests.SolcDifferential
import YulEvmCompilerTests.SolidityCorpus

/-!
Tier B gas report: measure execution-gas overhead of this compiler against solc
across a whole Solidity Yul corpus, and print an aggregate summary.

This is deliberately informational and non-gating. Upstream fixtures churn and
solc bumps shift every number, so — unlike the pinned Tier A benchmarks — there
is no checked-in baseline to match. It reuses the same deterministic scenarios
and the same behavior gate as the differential runner: a fixture contributes gas
only where both compilers reach identical observable behavior. Fixtures listed
in the differential known-failures baseline are skipped, since their behavior is
not comparable and their gas would be meaningless.

The headline is the overhead ratio ours/solc — a non-optimizing compiler is
expected to be above parity; the point is to track the gap and surface the
worst offenders, not to assert a bound.
-/

open System YulParser
open EvmSemantics
open YulEvmCompilerTests.Solc
open YulEvmCompilerTests.SolcDifferential
open YulEvmCompilerTests.SolidityCorpus

private structure FixtureGas where
  name : String
  ours : Nat
  solc : Nat

private def overheadPercent (ours solc : Nat) : Nat :=
  if solc == 0 then 0 else ours * 100 / solc

/-- Sum the comparable scenarios of one fixture into a single (ours, solc) pair,
or `none` if no scenario was gas-comparable. -/
private def foldFixture (name : String) (ours solc : ByteArray) : Option FixtureGas :=
  let measured := measureGas ours solc (scenarioSeed := fixtureSeed name)
  measured.foldl (init := none) fun acc (_, gas) =>
    match gas with
    | none => acc
    | some (o, s) =>
        match acc with
        | none => some { name, ours := o, solc := s }
        | some fixture => some { fixture with ours := fixture.ours + o, solc := fixture.solc + s }

private def median (values : Array Nat) : Nat :=
  if values.isEmpty then 0
  else (values.qsort (· < ·))[values.size / 2]!

private def usage : String :=
  "usage: ReportSolcGas <suite-name> <corpus-dir> <known-failures.txt> " ++
    "<solc-path> <expected-solc-version>"

private def run (suiteName : String) (corpusDir knownFailuresFile : FilePath)
    (solcPath expectedSolcVersion : String) : IO UInt32 := do
  match ← checkSolcVersion solcPath expectedSolcVersion with
  | .error message => IO.eprintln message; return 1
  | .ok () => pure ()
  let paths ← corpusDir.walkDir
  let files := paths.filter (fun path => path.extension == some "yul")
    |>.qsort (fun a b => relativeName corpusDir a < relativeName corpusDir b)
  if files.isEmpty then
    IO.eprintln s!"{corpusDir}: found no .yul fixtures"
    return 1
  let knownFailures ← readKnownFailures knownFailuresFile
  let mut measured : Array FixtureGas := #[]
  let mut skipped := 0
  for path in files do
    let name := relativeName corpusDir path
    let contents ← IO.FS.readFile path
    match runsOnLatestFork contents with
    | .ok true =>
        if knownFailures.contains name then
          skipped := skipped + 1
        else
          match compileSource (fixtureSource contents) with
          | none => skipped := skipped + 1
          | some ours =>
              match ← compileWithSolc solcPath (fixtureSource contents) with
              | .error _ => skipped := skipped + 1
              | .ok solc =>
                  match foldFixture name ours solc with
                  | some fixture => measured := measured.push fixture
                  | none => skipped := skipped + 1
    | _ => skipped := skipped + 1
  let totalOurs := measured.foldl (fun acc fixture => acc + fixture.ours) 0
  let totalSolc := measured.foldl (fun acc fixture => acc + fixture.solc) 0
  let overheads := measured.map (fun fixture => overheadPercent fixture.ours fixture.solc)
  IO.println s!"Gas report for {suiteName} (solc {expectedSolcVersion}, EVM osaka):"
  IO.println s!"  comparable fixtures: {measured.size}; skipped: {skipped}"
  if measured.isEmpty then
    IO.println "  no comparable fixtures — nothing to report"
    return 0
  IO.println s!"  aggregate overhead (total ours/total solc): {overheadPercent totalOurs totalSolc}%"
  IO.println s!"  median per-fixture overhead: {median overheads}%"
  let worst := measured.qsort
    (fun a b => overheadPercent a.ours a.solc > overheadPercent b.ours b.solc)
  IO.println "  worst 10 fixtures by overhead:"
  for fixture in worst.toList.take 10 do
    IO.println s!"    {fixture.name}: {fixture.ours} vs {fixture.solc} ({overheadPercent fixture.ours fixture.solc}%)"
  return 0

def main (args : List String) : IO UInt32 :=
  match args with
  | [suiteName, corpusDir, knownFailuresFile, solcPath, expectedSolcVersion] =>
      run suiteName corpusDir knownFailuresFile solcPath expectedSolcVersion
  | _ => do IO.eprintln usage; return 64
