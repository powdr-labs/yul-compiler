import YulEvmCompilerTests.InterpreterFixture

/-!
Run a checked-in selection of Solidity `yulInterpreterTests`. Each manifest
entry is a path relative to the upstream corpus directory.
-/

open System
open YulEvmCompilerTests.InterpreterFixture

private def readManifest (path : FilePath) : IO (Array String) := do
  let contents ← IO.FS.readFile path
  return (contents.splitOn "\n").foldl (init := #[]) fun names line =>
    let line := line.trimAscii.copy
    if line.isEmpty || line.startsWith "#" then names else names.push line

private def run (corpusDir manifestFile : FilePath) : IO UInt32 := do
  let names ← readManifest manifestFile
  if names.isEmpty then
    IO.eprintln s!"{manifestFile}: manifest contains no fixtures"
    return 1
  let mut failures := 0
  for name in names do
    let path := corpusDir / name
    if !(← path.pathExists) then
      IO.eprintln s!"FAIL {name}: fixture not found"
      failures := failures + 1
      continue
    let source ← IO.FS.readFile path
    match checkFixture source with
    | .ok () => IO.println s!"PASS {name}"
    | .error message =>
        IO.eprintln s!"FAIL {name}: {message}"
        failures := failures + 1
  IO.println s!"Checked {names.size} Solidity Yul interpreter fixture(s); {failures} failed."
  return if failures == 0 then 0 else 1

private def usage : String :=
  "usage: CheckSolidityInterpreterTests <yulInterpreterTests-dir> <manifest.txt>"

def main (args : List String) : IO UInt32 :=
  match args with
  | [corpusDir, manifestFile] => run corpusDir manifestFile
  | _ => do
      IO.eprintln usage
      return 64
