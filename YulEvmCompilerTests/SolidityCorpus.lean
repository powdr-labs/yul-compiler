import YulParser.Source

/-!
Shared helpers for runners over Solidity's moving Yul test corpora: relative
fixture names, exact text baselines, source-section extraction, and filtering
to the latest EVM fork supported by this repository (currently Osaka).
-/

namespace YulEvmCompilerTests.SolidityCorpus

open System

def relativeName (root path : FilePath) : String :=
  String.intercalate "/" (path.components.drop root.components.length)

def readKnownFailures (path : FilePath) : IO (Array String) := do
  let contents ← IO.FS.readFile path
  return (contents.splitOn "\n").foldl (init := #[]) fun names line =>
    let line := line.trimAscii.copy
    if line.isEmpty || line.startsWith "#" then names else names.push line

def printNames (heading : String) (names : Array String) : IO Unit := do
  unless names.isEmpty do
    IO.eprintln heading
    for name in names do
      IO.eprintln s!"  {name}"

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
  | "osaka" | "current" => some 14
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

/-- Whether a fixture's declared EVM-version range contains Osaka. Missing
metadata applies to every fork; malformed or duplicate metadata is an error. -/
def runsOnLatestFork (contents : String) : Except String Bool := do
  let directivePrefix := "// EVMVersion:"
  let directives := contents.splitOn "\n" |>.foldl (init := []) fun found rawLine =>
    let line := rawLine.trimAscii.copy
    if line.startsWith directivePrefix then (line.drop directivePrefix.length).copy :: found
    else found
  match directives with
  | [] => pure true
  | [constraint] => parseVersionConstraint constraint
  | _ => throw "multiple EVMVersion directives"

/-- Return the portion Solidity's test reader treats as source, before either
the settings delimiter or the golden-expectation delimiter. -/
def fixtureSource (contents : String) : String :=
  String.intercalate "\n" <| (contents.splitOn "\n").takeWhile fun rawLine =>
    let line := rawLine.trimAscii.copy
    line != "// ====" && line != "// ----"

example : runsOnLatestFork "// EVMVersion: <paris" = .ok false := by native_decide
example : runsOnLatestFork "// EVMVersion: >=cancun" = .ok true := by native_decide
example : runsOnLatestFork "// EVMVersion: =current" = .ok true := by native_decide
example : fixtureSource "{}\n// ====\n// EVMVersion: =current\n// ----\n// stop" = "{}" := by
  native_decide

end YulEvmCompilerTests.SolidityCorpus
