import YulParser.Compile
import YulEvmCompilerTests.SolcDifferential
import YulEvmCompilerTests.SolidityCorpus

/-!
Compile each applicable fixture with both this compiler and a pinned solc,
execute both bytecode sequences under the same deterministic environments, and
compare observable behavior. The exact failure set is checked against a text
baseline: new failures and stale entries both fail the run.

This runner intentionally compares behavior rather than bytecode. solc uses
different PUSH widths, labels, stack allocation, object layout, and optional
normalization while remaining semantically equivalent.
-/

open System YulParser
open EvmSemantics
open YulEvmCompilerTests.SolcDifferential
open YulEvmCompilerTests.SolidityCorpus

private def isHexDigit (char : Char) : Bool :=
  ('0' <= char && char <= '9') ||
    ('a' <= char && char <= 'f') ||
    ('A' <= char && char <= 'F')

private def findBinary (afterMarker : Bool) : List String → Option String
  | [] => none
  | rawLine :: lines =>
      let line := rawLine.trimAscii.copy
      if afterMarker && !line.isEmpty then some line
      else findBinary (afterMarker || line == "Binary representation:") lines

private def parseSolcBinary (stdout : String) : Except String ByteArray := do
  let encoded ← match findBinary false (stdout.splitOn "\n") with
    | some encoded => pure encoded
    | none => throw "solc output did not contain Binary representation"
  if encoded.isEmpty || !encoded.all isHexDigit || encoded.length % 2 != 0 then
    throw s!"solc returned malformed bytecode: {encoded}"
  return Hex.hexToBytes encoded

private def compileWithSolc (solcPath source : String) : IO (Except String ByteArray) := do
  let output ← IO.Process.output {
    cmd := solcPath
    args := #["--strict-assembly", "--bin", "--evm-version", "osaka", "-"]
  } (some source)
  if output.exitCode != 0 then
    return .error s!"solc compilation failed: {output.stderr.trimAscii.copy}"
  return parseSolcBinary output.stdout

private def checkSolcVersion (solcPath expectedVersion : String) : IO (Except String Unit) := do
  let output ← IO.Process.output { cmd := solcPath, args := #["--version"] }
  if output.exitCode != 0 then
    return .error s!"solc --version failed: {output.stderr.trimAscii.copy}"
  let marker := s!"Version: {expectedVersion}+"
  if !output.stdout.contains marker then
    return .error (s!"expected solc {expectedVersion}, got:\n" ++ output.stdout.trimAscii.copy)
  return .ok ()

private def run (suiteName : String) (corpusDir knownFailuresFile : FilePath)
    (solcPath expectedSolcVersion : String) : IO UInt32 := do
  match ← checkSolcVersion solcPath expectedSolcVersion with
  | .error message =>
      IO.eprintln message
      return 1
  | .ok () => pure ()
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
        match compileSource source with
        | none => failures := failures.push (name, "Yul compiler failed")
        | some ours =>
            match ← compileWithSolc solcPath source with
            | .error message => failures := failures.push (name, message)
            | .ok solc =>
                match compareBytecode ours solc with
                | .ok () => pure ()
                | .error message => failures := failures.push (name, message)

  let failureNames := failures.map (·.1)
  let unexpected := failures.filter (fun failure => !allowed.contains failure.1)
  let stale := allowed.filter (!failureNames.contains ·)
  let knownFailureCount := failures.size - unexpected.size
  IO.println (s!"Differentially checked {checked} latest-fork Solidity {suiteName} tests " ++
    s!"against solc {expectedSolcVersion}: {checked - failures.size} matched, " ++
    s!"{failures.size} failed ({knownFailureCount} known); " ++
    s!"skipped {skipped} outside Osaka.")
  unless metadataErrors.isEmpty do
    IO.eprintln s!"Invalid {suiteName} EVMVersion metadata:"
    for (name, message) in metadataErrors do
      IO.eprintln s!"  {name}: {message}"
  unless unexpected.isEmpty do
    IO.eprintln s!"Unexpected {suiteName} solc differential failures:"
    for (name, message) in unexpected do
      IO.eprintln s!"  {name}: {message}"
  printNames s!"Stale {suiteName} solc-differential entries (remove after review):" stale
  return if unexpected.isEmpty && stale.isEmpty && metadataErrors.isEmpty then 0 else 1

private def usage : String :=
  "usage: CheckSoliditySolcDifferential <suite-name> <corpus-dir> " ++
    "<known-failures.txt> <solc-path> <expected-solc-version>"

def main (args : List String) : IO UInt32 :=
  match args with
  | [suiteName, corpusDir, knownFailuresFile, solcPath, expectedSolcVersion] =>
      run suiteName corpusDir knownFailuresFile solcPath expectedSolcVersion
  | _ => do
      IO.eprintln usage
      return 64
