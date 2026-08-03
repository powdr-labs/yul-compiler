import YulParser.Compile
import YulEvmCompilerTests.SolidityCorpus
import YulEvmCompilerTests.Solc

set_option warningAsError true
/-!
# scripts.CheckSolidityCompileGate

A **compiled, compile-only** corpus checker. For each Solidity fixture it runs
`solc --ir` (solc's unoptimized Yul front-end) and then this compiler's front
end (`YulParser.compileSource` = parse → optimizer → backend, *including the
stack-overflow gate* whenever the branch has one), and reports which contracts
the compiler **rejects** — with **no EVM gas execution at all**.

## Why this exists
`checkSolidityGas` answers "how much gas does each contract use", which means
deploying and running every contract in the EVM semantics: slow, and
occasionally non-terminating on pathological corpus contracts (unbounded loops
under unoptimized codegen). But a very common maintenance question is far
narrower:

> *Which fixtures does the compiler now reject?*

For example, after adding or changing the stack-overflow gate
(`StackScalable.stackOK2`), the newly-rejected contracts make their pinned gas
rows **stale**, and those rows must be dropped from the gas baselines
(`solidity-semantic-gas-baseline.txt`, `uniswap-v4-gas-baseline.txt`, …).
Finding that set previously meant a full ~24-min-per-shard `checkSolidityGas`
run just to read its "stale" list — or, worse, running the checker interpreted
(`lake env lean --run`), which overflows the interpreter stack on large
contracts and runs the optimizer ~100× slower.

This tool answers the narrow question directly: it does only the compile zeroImmutables phase,
compiled natively (hence a `lean_exe`, exactly like `checkSolidityGas` — see the
note in `lakefile.toml`). Most contracts compile zeroImmutables in well under 0.1 s; only a
handful of large ones cost a few seconds each (the optimizer's multi-strategy
retries), so shard 8-way and union the `REJECT` lines to cover all of
semanticTests in a few minutes — versus ~24 min *per shard* for the gas runner,
and with none of its gas execution (which can hang on pathological contracts)
nor the interpreter's stack overflow.

## Usage
```
checkCompileGate <corpus-dir> <solc-path> [--shard=I/N] [--baseline=<file>]
```
* Default: walk `<corpus-dir>` for `*.sol`, compile-check each, print one
  `OK`/`REJECT`/`SOLCFAIL`/`SKIP`/`META` line per fixture plus a summary.
* `--baseline=<file>`: instead of walking the directory, check exactly the
  fixtures pinned in a gas baseline (tab-separated; the first field is
  `path/to/Fixture.sol` optionally followed by `:<scenario-signature>`). Prints
  the **stale set** — baseline fixtures the compiler now rejects, i.e. precisely
  the rows to delete after a gate change.
* `--shard=I/N`: process only shard `I` of `N` (0-based, by position) for coarse
  parallelism. Launch `N` copies and union their `REJECT` lines.

`SOLCFAIL` (solc could not produce IR) and `SKIP` (fixture excludes the latest
fork) and `META` (bad version metadata) are *not* compiler rejections and are
never counted as stale.
-/

open System YulParser
open YulEvmCompilerTests.SolidityCorpus
open YulEvmCompilerTests.Solc

/-- The `.sol` fixture paths pinned in a gas baseline: first tab field with any
`:<scenario>` suffix stripped, comments/blank lines skipped, first-seen dedup. -/
def baselineFixtures (contents : String) : Array String := Id.run do
  let mut seen : Array String := #[]
  for line in contents.splitOn "\n" do
    if line.startsWith "#" || line.trimAscii.copy.isEmpty then continue
    let field := (line.splitOn "\t").headD ""
    let fx := (field.splitOn ":").headD field  -- corpus paths never contain ':'
    if !fx.isEmpty && !seen.contains fx then seen := seen.push fx
  return seen

/-- Compile-only classification of a single fixture. Never executes gas. -/
def classify (solcPath : String) (path : FilePath) : IO String := do
  let contents ← IO.FS.readFile path
  match runsOnLatestFork contents with
  | .error _ => return "META"
  | .ok false => return "SKIP"
  | .ok true =>
    match ← solcUnoptimizedIR solcPath (fixtureSource contents) with
    | .error _ => return "SOLCFAIL"
    | .ok ir => return (if (compileSource ir).isNone then "REJECT" else "OK")

/-- Parse `--shard=I/N` into `(I, N)`. -/
def parseShard (flags : List String) : Option (Nat × Nat) :=
  flags.filterMap (fun f =>
    if f.startsWith "--shard=" then
      match (f.drop "--shard=".length).copy.splitOn "/" with
      | [i, n] => match i.toNat?, n.toNat? with
                  | some i, some n => if n > 0 && i < n then some (i, n) else none
                  | _, _ => none
      | _ => none
    else none) |>.head?

def main (args : List String) : IO UInt32 := do
  let positional := args.filter (fun a => !a.startsWith "--")
  let flags := args.filter (fun a => a.startsWith "--")
  match positional with
  | [dirArg, solcPath] =>
    let corpusDir : FilePath := ⟨dirArg⟩
    let shard := parseShard flags
    let baselineFile := (flags.filterMap (fun f =>
      if f.startsWith "--baseline=" then some (f.drop "--baseline=".length).copy else none)).head?
    -- Build the fixture worklist (relative names), sorted for determinism.
    let names ← match baselineFile with
      | some bf => do
          let c ← IO.FS.readFile ⟨bf⟩
          pure (baselineFixtures c)
      | none => do
          let paths ← corpusDir.walkDir
          pure ((paths.filter (fun p => p.extension == some "sol")).map (relativeName corpusDir))
    let names := names.qsort (· < ·)
    let mut idx := 0
    let mut checked := 0
    let mut rejects : Array String := #[]
    for name in names do
      let mine := match shard with | some (i, n) => idx % n == i | none => true
      idx := idx + 1
      if !mine then continue
      checked := checked + 1
      let r ← classify solcPath (corpusDir / name)
      if r == "REJECT" then rejects := rejects.push name
      IO.println s!"{r}\t{name}"
    IO.eprintln s!"compile-gate: checked {checked}, rejected {rejects.size} (no gas execution)."
    if baselineFile.isSome then
      printNames "Baseline fixtures the compiler now REJECTS — drop these gas rows:" rejects
    return 0
  | _ =>
    IO.eprintln "usage: checkCompileGate <corpus-dir> <solc-path> [--shard=I/N] [--baseline=<file>]"
    return 64
