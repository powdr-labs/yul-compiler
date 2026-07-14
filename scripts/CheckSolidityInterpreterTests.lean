import YulEvmCompilerTests.InterpreterFixture

/-!
Run every Solidity `yulInterpreterTests` fixture and compare the failures with
a checked-in baseline. Each baseline entry is a path relative to the upstream
corpus directory. Fixtures whose `EVMVersion` range excludes the latest fork
(Osaka) are skipped. A new failure and a stale failure entry both fail the run.
-/

open System
open YulEvmCompilerTests.InterpreterFixture

private def relativeName (root path : FilePath) : String :=
  String.intercalate "/" (path.components.drop root.components.length)

private def readKnownFailures (path : FilePath) : IO (Array String) := do
  let contents ← IO.FS.readFile path
  return (contents.splitOn "\n").foldl (init := #[]) fun names line =>
    let line := line.trimAscii.copy
    if line.isEmpty || line.startsWith "#" then names else names.push line

private def printNames (heading : String) (names : Array String) : IO Unit := do
  unless names.isEmpty do
    IO.eprintln heading
    for name in names do
      IO.eprintln s!"  {name}"

/-! Solidity's test metadata names forks rather than assigning numeric
versions. The order below follows Solidity's `EVMVersion` order through the
latest fork exercised by this repository's concrete EVM runner. -/

private def evmVersionRank : String → Option Nat
  | "frontier" => some 0
  | "homestead" => some 1
  | "tangerinewhistle" => some 2
  | "spuriousdragon" => some 3
  | "byzantium" => some 4
  | "constantinople" => some 5
  | "petersburg" => some 6
  | "istanbul" => some 7
  | "berlin" => some 8
  | "london" => some 9
  | "paris" => some 10
  | "shanghai" => some 11
  | "cancun" => some 12
  | "prague" => some 13
  | "osaka" => some 14
  | _ => none

private def latestEvmVersionRank : Nat := 14

private def parseVersionConstraint (raw : String) : Except String Bool := do
  let constraint := raw.trimAscii.copy
  let (operator, version) :=
    if constraint.startsWith ">=" then (">=", constraint.drop 2)
    else if constraint.startsWith "<=" then ("<=", constraint.drop 2)
    else if constraint.startsWith ">" then (">", constraint.drop 1)
    else if constraint.startsWith "<" then ("<", constraint.drop 1)
    else if constraint.startsWith "=" then ("=", constraint.drop 1)
    else ("=", constraint)
  let versionName := version.trimAscii.copy.toLower
  let rank ← match evmVersionRank versionName with
    | some rank => pure rank
    | none => throw s!"unknown EVM version in constraint: {constraint}"
  return match operator with
    | ">=" => latestEvmVersionRank >= rank
    | "<=" => latestEvmVersionRank <= rank
    | ">" => latestEvmVersionRank > rank
    | "<" => latestEvmVersionRank < rank
    | _ => latestEvmVersionRank == rank

/-- Whether the fixture's declared EVM-version range contains Osaka. Missing
metadata means the fixture applies to every fork. Malformed or duplicate
metadata is an error rather than a silent skip. -/
private def runsOnLatestFork (source : String) : Except String Bool := do
  let directivePrefix := "// EVMVersion:"
  let directives := source.splitOn "\n" |>.foldl (init := []) fun found rawLine =>
    let line := rawLine.trimAscii.copy
    if line.startsWith directivePrefix then (line.drop directivePrefix.length).copy :: found
    else found
  match directives with
  | [] => pure true
  | [constraint] => parseVersionConstraint constraint
  | _ => throw "multiple EVMVersion directives"

example : runsOnLatestFork "// EVMVersion: <paris" = .ok false := by native_decide
example : runsOnLatestFork "// EVMVersion: >=cancun" = .ok true := by native_decide
example : runsOnLatestFork "// EVMVersion: >=osaka" = .ok true := by native_decide

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
