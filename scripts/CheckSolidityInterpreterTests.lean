import YulEvmCompilerTests.InterpreterFixture

/-!
Run every Solidity `yulInterpreterTests` fixture and compare the failures with
a checked-in baseline. Each baseline entry is a path relative to the upstream
corpus directory. A new failure and a stale failure entry both fail the run.
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

private def run (corpusDir knownFailuresFile : FilePath) : IO UInt32 := do
  let paths ← corpusDir.walkDir
  let files := paths.filter (fun path => path.extension == some "yul")
    |>.qsort (fun a b => relativeName corpusDir a < relativeName corpusDir b)
  if files.isEmpty then
    IO.eprintln s!"{corpusDir}: found no .yul fixtures"
    return 1
  let allowed ← readKnownFailures knownFailuresFile
  let mut failures : Array (String × String) := #[]
  for path in files do
    let name := relativeName corpusDir path
    let source ← IO.FS.readFile path
    match checkFixture source with
    | .ok () => pure ()
    | .error message =>
        failures := failures.push (name, message)

  let failureNames := failures.map (·.1)
  let unexpected := failures.filter (fun failure => !allowed.contains failure.1)
  let stale := allowed.filter (!failureNames.contains ·)
  let knownFailureCount := failures.size - unexpected.size
  IO.println (s!"Checked {files.size} Solidity Yul interpreter tests: " ++
    s!"{files.size - failures.size} passed, {failures.size} failed " ++
    s!"({knownFailureCount} known).")
  unless unexpected.isEmpty do
    IO.eprintln "Unexpected interpreter-test failures (add only after review):"
    for (name, message) in unexpected do
      IO.eprintln s!"  {name}: {message}"
  printNames "Stale known-failure entries (remove after review):" stale
  return if unexpected.isEmpty && stale.isEmpty then 0 else 1

private def usage : String :=
  "usage: CheckSolidityInterpreterTests <yulInterpreterTests-dir> <known-failures.txt>"

def main (args : List String) : IO UInt32 :=
  match args with
  | [corpusDir, knownFailuresFile] => run corpusDir knownFailuresFile
  | _ => do
      IO.eprintln usage
      return 64
