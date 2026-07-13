import YulParser.Source

/-!
Run the parser over Solidity's `test/libyul/yulSyntaxTests` corpus and compare
its disagreements with Solidity's expected result against a checked-in list.

A fixture is expected to fail when its expectation section (after `// ----`)
contains an `*Error` diagnostic. Warnings do not make a fixture an expected
failure. This intentionally treats Solidity's semantic errors as failures too:
the mismatch list documents the present boundary of our syntax-only parser.
-/

open System YulParser

private def relativeName (root path : FilePath) : String :=
  String.intercalate "/" (path.components.drop root.components.length)

private def expectedToParse (source : String) : Bool :=
  let rec loop (inExpectations : Bool) : List String → Bool
    | [] => true
    | line :: lines =>
        let line := line.trimAscii.copy
        if line == "// ----" then
          loop true lines
        else if inExpectations && line.startsWith "// " && line.contains "Error " then
          false
        else
          loop inExpectations lines
  loop false (source.splitOn "\n")

private def readMismatchList (path : FilePath) : IO (Array String) := do
  let contents ← IO.FS.readFile path
  return (contents.splitOn "\n").foldl (init := #[]) fun names line =>
    let line := line.trimAscii.copy
    if line.isEmpty || line.startsWith "#" then names else names.push line

private def printNames (heading : String) (names : Array String) : IO Unit := do
  unless names.isEmpty do
    IO.eprintln heading
    for name in names do
      IO.eprintln s!"  {name}"

private def run (corpusDir mismatchFile : FilePath) : IO UInt32 := do
  let paths ← corpusDir.walkDir
  let files := paths.filter (fun path => path.extension == some "yul")
    |>.qsort (fun a b => relativeName corpusDir a < relativeName corpusDir b)
  let allowed ← readMismatchList mismatchFile
  let mut mismatches := #[]
  let mut expectedSuccesses := 0
  let mut expectedFailures := 0
  let mut falseAccepts := 0
  let mut falseRejects := 0
  for path in files do
    let source ← IO.FS.readFile path
    let expected := expectedToParse source
    let actual := (parseSource source).isSome
    if expected then
      expectedSuccesses := expectedSuccesses + 1
    else
      expectedFailures := expectedFailures + 1
    if expected != actual then
      mismatches := mismatches.push (relativeName corpusDir path)
      if actual then falseAccepts := falseAccepts + 1 else falseRejects := falseRejects + 1

  let unexpected := mismatches.filter (!allowed.contains ·)
  let stale := allowed.filter (!mismatches.contains ·)
  IO.println (s!"Checked {files.size} Solidity Yul syntax tests: " ++
    s!"{expectedSuccesses} expected successes, {expectedFailures} expected failures, " ++
    s!"{mismatches.size} known parser mismatches " ++
    s!"({falseAccepts} false accepts, {falseRejects} false rejects).")
  printNames "Unexpected parser mismatches (add only after review):" unexpected
  printNames "Stale mismatch entries (remove after review):" stale
  if unexpected.isEmpty && stale.isEmpty then return 0 else return 1

private def usage : String :=
  "usage: CheckSoliditySyntaxTests <yulSyntaxTests-dir> <known-mismatches.txt>"

def main (args : List String) : IO UInt32 :=
  match args with
  | [corpusDir, mismatchFile] => run corpusDir mismatchFile
  | _ => do
      IO.eprintln usage
      return 64
