import YulIR.Check
import YulIR.Corpus

/-!
# YulIR.CheckBaseline — translation-correctness gate

    lake env lean YulIR/CheckBaseline.lean

Every program in `YulIR.Corpus` must agree with its `toYul ∘ ofYul` round-trip under the
interpreter, on every scenario (same status and, when `ok`, identical observable
fingerprint). A failure here is a translation bug and fails the process.

These programs are a deliberate *feature-coverage* set for the translation (arithmetic,
memory, storage, control flow, functions, halting) — **not** an optimization benchmark.
Optimization effectiveness is tracked over Solidity's real `yulOptimizerTests` corpus by
`scripts/YulIRCorpus.lean` against `test/yulir-corpus-size-baseline.txt`.
-/

open YulIR

#eval do
  let rtFail := Check.roundTripFailures Corpus.corpus
  unless rtFail.isEmpty do
    throw (IO.userError s!"Yul→IR→Yul round-trip changed behaviour for: {rtFail}")
  let optFail := Check.optimizeFailures Corpus.corpus
  unless optFail.isEmpty do
    throw (IO.userError s!"YulIR.optimize changed behaviour for: {optFail}")
  IO.println s!"YulIR OK: {Corpus.corpus.length} programs — round-trip and optimize both behaviour-preserving."
