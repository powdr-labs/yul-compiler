import YulEvmCompilerTests.InterpreterFixture
import YulEvmCompilerTests.SolidityCorpus

/-!
Run every Solidity `yulInterpreterTests` fixture and compare the failures with
a checked-in baseline. Each baseline entry is a path relative to the upstream
corpus directory. Fixtures whose `EVMVersion` range excludes the latest fork
(Osaka) are skipped. A new failure and a stale failure entry both fail the run.
-/

open System
open YulEvmCompilerTests.InterpreterFixture
open YulEvmCompilerTests.SolidityCorpus

private def run (corpusDir knownFailuresFile : FilePath) : IO UInt32 := do
  let paths ← corpusDir.walkDir
  let files := paths.filter (fun path => path.extension == some "yul")
    |>.qsort (fun a b => relativeName corpusDir a < relativeName corpusDir b)
  if files.isEmpty then
    IO.eprintln s!"{corpusDir}: found no .yul fixtures"
    return 1
  let allowed ← readKnownFailures knownFailuresFile
  let mut failures : Array (String × String) := #[]
  let mut metadataErrors : Array (String × String) := #[]
  let mut checked := 0
  let mut skipped := 0
  for path in files do
    let name := relativeName corpusDir path
    let source ← IO.FS.readFile path
    match runsOnLatestFork source with
    | .error message => metadataErrors := metadataErrors.push (name, message)
    | .ok false => skipped := skipped + 1
    | .ok true =>
        checked := checked + 1
        match checkFixture source with
        | .ok () => pure ()
        | .error message => failures := failures.push (name, message)

  let failureNames := failures.map (·.1)
  let unexpected := failures.filter (fun failure => !allowed.contains failure.1)
  let stale := allowed.filter (!failureNames.contains ·)
  let knownFailureCount := failures.size - unexpected.size
  IO.println (s!"Checked {checked} latest-fork Solidity Yul interpreter tests: " ++
    s!"{checked - failures.size} passed, {failures.size} failed " ++
    s!"({knownFailureCount} known); skipped {skipped} outside Osaka.")
  unless metadataErrors.isEmpty do
    IO.eprintln "Invalid interpreter-test EVMVersion metadata:"
    for (name, message) in metadataErrors do
      IO.eprintln s!"  {name}: {message}"
  unless unexpected.isEmpty do
    IO.eprintln "Unexpected interpreter-test failures (add only after review):"
    for (name, message) in unexpected do
      IO.eprintln s!"  {name}: {message}"
  printNames "Stale known-failure entries (remove after review):" stale
  return if unexpected.isEmpty && stale.isEmpty && metadataErrors.isEmpty then 0 else 1

private def usage : String :=
  "usage: CheckSolidityInterpreterTests <yulInterpreterTests-dir> <known-failures.txt>"

def main (args : List String) : IO UInt32 :=
  match args with
  | [corpusDir, knownFailuresFile] => run corpusDir knownFailuresFile
  | _ => do
      IO.eprintln usage
      return 64
