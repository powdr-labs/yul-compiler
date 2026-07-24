import YulIR.Check
import YulIR.Corpus

/-!
# YulIR.CheckBaseline — CI gate for the IR baseline

    lake env lean YulIR/CheckBaseline.lean

Two checks, both fail the process (non-zero exit) on regression:

1. **Semantic round-trip (hard).** Every program must agree with its `toYul ∘ ofYul`
   round-trip under the interpreter, on every scenario. A failure here is a translation
   bug and always fails, independent of the pinned numbers.
2. **Baseline snapshot.** The recomputed report must match the committed
   `YulIR/baseline.txt` exactly (code sizes + gas totals). On drift it prints a
   line-by-line diff; re-run `UpdateBaseline` if the change is intended.
-/

open YulIR

/-- Print a line-by-line diff of expected vs actual report. -/
def printDiff (expected actual : String) : IO Unit := do
  let exp := expected.splitOn "\n"
  let act := actual.splitOn "\n"
  let n := max exp.length act.length
  for i in [0:n] do
    let e := exp.getD i ""
    let a := act.getD i ""
    if e != a then
      IO.eprintln s!"- expected: {e}"
      IO.eprintln s!"+ actual:   {a}"

#eval do
  -- 1. Hard semantic gate.
  let failures := Check.roundTripFailures Corpus.corpus
  unless failures.isEmpty do
    throw (IO.userError s!"semantic round-trip FAILED for: {failures}")
  -- 2. Baseline snapshot.
  let actual := Check.fullReport Corpus.corpus
  let expected ←
    try IO.FS.readFile "YulIR/baseline.txt"
    catch _ => pure ""
  if expected.isEmpty then
    throw (IO.userError "YulIR/baseline.txt missing; run `lake env lean YulIR/UpdateBaseline.lean`")
  if actual == expected then
    IO.println s!"YulIR baseline OK: {Corpus.corpus.length} programs, round-trip + snapshot match."
  else
    IO.eprintln "YulIR baseline MISMATCH (re-run UpdateBaseline if intended):"
    printDiff expected actual
    throw (IO.userError "YulIR baseline snapshot mismatch")
