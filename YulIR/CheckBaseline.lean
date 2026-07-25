import YulIR.Check
import YulIR.Corpus

set_option warningAsError true
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

private def warningPolicyExempt : List String :=
  ["Checks.lean", "SpecClosure.lean"]

/-- Keep the per-module warning policy from silently missing newly added Lean sources. -/
private def checkWarningPolicy : IO Unit := do
  let tracked ← IO.Process.output { cmd := "git", args := #["ls-files", "*.lean"] }
  if tracked.exitCode != 0 then
    throw (IO.userError s!"failed to list tracked Lean sources:\n{tracked.stderr}")
  let mut missing : List String := []
  for file in tracked.stdout.splitOn "\n" do
    if !file.isEmpty && !warningPolicyExempt.contains file then
      let source ← IO.FS.readFile file
      if !(source.splitOn "\n").contains "set_option warningAsError true" then
        missing := file :: missing
  if !missing.isEmpty then
    throw (IO.userError s!"tracked Lean sources missing `set_option warningAsError true`:\n{String.intercalate "\n" missing.reverse}")

open YulIR

#eval do
  checkWarningPolicy
  let failures := Check.roundTripFailures Corpus.corpus
  if failures.isEmpty then
    IO.println s!"YulIR round-trip OK: {Corpus.corpus.length} programs agree with their IR round-trip."
  else
    throw (IO.userError s!"semantic round-trip FAILED for: {failures}")
