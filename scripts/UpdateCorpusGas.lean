import YulParser.Compile
import YulEvmCompilerTests.Solc
import YulEvmCompilerTests.CorpusGas
import YulEvmCompilerTests.SolidityCorpus

/-!
Regenerate a per-suite gas baseline for the solc differential.

Walks a whole corpus (unsharded), and for every latest-fork fixture that is not
a known differential failure and that compiles on both toolchains, records the
total execution gas this compiler and the pinned solc spend across the
gas-comparable scenarios. The differential runner then checks these figures and
fails on a genuine regression (see YulEvmCompilerTests.CorpusGas).

This is the write side of the gas baseline; the differential is the read side.
Run it through scripts/update-gas.sh after an intended codegen or solc change,
and review the diff.
-/

open System YulParser
open EvmSemantics
open YulEvmCompilerTests.Solc
open YulEvmCompilerTests.CorpusGas
open YulEvmCompilerTests.SolidityCorpus

private def usage : String :=
  "usage: UpdateCorpusGas <suite-name> <corpus-dir> <known-failures.txt> " ++
    "<gas-baseline.txt> <solc-path> <expected-solc-version>"

private def run (suiteName : String) (corpusDir knownFailuresFile gasBaselineFile : FilePath)
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
  let mut rows : Array GasRow := #[]
  let mut skipped := 0
  for path in files do
    let name := relativeName corpusDir path
    let contents ← IO.FS.readFile path
    match runsOnLatestFork contents with
    | .ok true =>
        if knownFailures.contains name then
          skipped := skipped + 1
        else
          let source := fixtureSource contents
          match compileSource source with
          | none => skipped := skipped + 1
          | some ours =>
              match ← compileWithSolc solcPath source with
              | .error _ => skipped := skipped + 1
              | .ok solc =>
                  match fixtureTotalGas name ours solc with
                  | some (o, s) => rows := rows.push { fixture := name, ours := o, solc := s }
                  | none => skipped := skipped + 1
    | _ => skipped := skipped + 1
  IO.FS.writeFile gasBaselineFile (render suiteName expectedSolcVersion rows)
  IO.println s!"Re-pinned {rows.size} {suiteName} gas rows in {gasBaselineFile} (skipped {skipped})."
  return 0

def main (args : List String) : IO UInt32 :=
  match args with
  | [suiteName, corpusDir, knownFailuresFile, gasBaselineFile, solcPath, expectedSolcVersion] =>
      run suiteName corpusDir knownFailuresFile gasBaselineFile solcPath expectedSolcVersion
  | _ => do IO.eprintln usage; return 64
