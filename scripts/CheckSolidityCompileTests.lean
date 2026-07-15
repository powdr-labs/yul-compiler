import YulParser.Compile
import YulEvmCompilerTests.SolidityCorpus

/-!
Compile every accepted Yul fixture in one of Solidity's positive compiler
corpora and compare the failures with a checked-in baseline. Each baseline
entry is a path relative to the supplied corpus directory. Fixtures whose
`EVMVersion` range excludes the latest fork (Osaka) are skipped. A new failure,
a stale failure entry, malformed version metadata, or an empty corpus all fail
the run.

The source is the part before Solidity's `// ====` settings delimiter or
`// ----` expectation delimiter. Golden optimizer output, assembly, and
bytecode are deliberately ignored: this check is about accepting and compiling
the same source programs, not reproducing solc's optimizer or encoding choices.
-/

open System YulParser
open YulEvmCompilerTests.SolidityCorpus

private def run (suiteName : String) (corpusDir knownFailuresFile : FilePath) : IO UInt32 := do
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
    let contents ← IO.FS.readFile path
    match runsOnLatestFork contents with
    | .error message => metadataErrors := metadataErrors.push (name, message)
    | .ok false => skipped := skipped + 1
    | .ok true =>
        checked := checked + 1
        let source := fixtureSource contents
        if (compileSource source).isNone then
          let reason := if (parseSource source).isNone then "parse failed" else "compilation failed"
          failures := failures.push (name, reason)

  let failureNames := failures.map (·.1)
  let unexpected := failures.filter (fun failure => !allowed.contains failure.1)
  let stale := allowed.filter (!failureNames.contains ·)
  let knownFailureCount := failures.size - unexpected.size
  IO.println (s!"Checked {checked} latest-fork Solidity {suiteName} tests: " ++
    s!"{checked - failures.size} compiled, {failures.size} failed " ++
    s!"({knownFailureCount} known); skipped {skipped} outside Osaka.")
  unless metadataErrors.isEmpty do
    IO.eprintln s!"Invalid {suiteName} EVMVersion metadata:"
    for (name, message) in metadataErrors do
      IO.eprintln s!"  {name}: {message}"
  unless unexpected.isEmpty do
    IO.eprintln s!"Unexpected {suiteName} compilation failures (add only after review):"
    for (name, message) in unexpected do
      IO.eprintln s!"  {name}: {message}"
  printNames s!"Stale {suiteName} known-failure entries (remove after review):" stale
  return if unexpected.isEmpty && stale.isEmpty && metadataErrors.isEmpty then 0 else 1

private def usage : String :=
  "usage: CheckSolidityCompileTests <suite-name> <corpus-dir> <known-failures.txt>"

def main (args : List String) : IO UInt32 :=
  match args with
  | [suiteName, corpusDir, knownFailuresFile] => run suiteName corpusDir knownFailuresFile
  | _ => do
      IO.eprintln usage
      return 64
