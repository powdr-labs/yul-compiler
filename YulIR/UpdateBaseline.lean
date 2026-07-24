import YulIR.Check
import YulIR.Corpus

/-!
# YulIR.UpdateBaseline — (re)generate the committed baseline

Run this to write `YulIR/baseline.txt` from the current corpus + translations:

    lake env lean YulIR/UpdateBaseline.lean

Do this deliberately whenever the corpus, the translation, or the backend changes the
numbers, and review the diff — `CheckBaseline` fails in CI until the committed file matches.
-/

open YulIR

#eval do
  let report := Check.fullReport Corpus.corpus
  IO.FS.writeFile "YulIR/baseline.txt" report
  IO.println s!"Wrote YulIR/baseline.txt ({Corpus.corpus.length} programs)."
  let failures := Check.roundTripFailures Corpus.corpus
  unless failures.isEmpty do
    IO.println s!"WARNING: semantic round-trip FAILED for: {failures}"
