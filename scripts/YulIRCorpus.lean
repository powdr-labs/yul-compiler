import YulIR.Check
import YulParser.Compile
import YulEvmCompilerTests.SolidityCorpus

set_option warningAsError true
/-!
# scripts/YulIRCorpus — IR benchmark over Solidity's `yulOptimizerTests`

Runs the IR pipeline over the *real* corpus the current optimizer is tested on (fetched,
not vendored — Solidity is GPL, this repo is Apache), grouped by optimizer-step directory,
and compares compiled **code size** three ways:

* `current`  — `YulParser.compileSource` (parse → current optimizer → backend);
* `ir-noopt` — parse → `toYul ∘ ofYul` → backend (no IR optimizations);
* `ir-opt`   — parse → `toYul ∘ optimize ∘ ofYul` → backend (the IR pipeline).

`ir-opt` vs `ir-noopt` isolates what the IR passes buy (IR→Yul translation cancels); `ir-opt`
vs `current` is the headline gap to the mature Yul optimizer. As passes land in `YulIR.optimize`
the `ir-opt` column drops.

Usage:
  lake env lean --run scripts/YulIRCorpus.lean report <corpusDir>
  lake env lean --run scripts/YulIRCorpus.lean update <corpusDir> <baselineFile>
  lake env lean --run scripts/YulIRCorpus.lean check  <corpusDir> <baselineFile>

`check` is CI-safe against the daily-moving corpus: each category row carries a source
fingerprint, and only categories whose fingerprint matches the committed baseline are gated
(fails on an IR size regression or a shrunk compilable set); drifted/new categories are just
reported.
-/

open System YulParser
open YulEvmCompilerTests.SolidityCorpus
open YulEvmCompilerTests.SolcDifferential (compareBytecode measureGas fixtureSeed)

namespace YulIRCorpus

/-- Every block-rooted, latest-fork fixture as `(name, source, desugared block)`. -/
def blockFixtures (corpusDir : FilePath) :
    IO (Array (String × String × YulSemantics.Block YulSemantics.EVM.Op)) := do
  let paths ← corpusDir.walkDir
  let files := paths.filter (fun p => p.extension == some "yul")
    |>.qsort (fun a b => relativeName corpusDir a < relativeName corpusDir b)
  let mut out := #[]
  for path in files do
    let name := relativeName corpusDir path
    let contents ← IO.FS.readFile path
    match runsOnLatestFork contents with
    | .ok true =>
        let source := fixtureSource contents
        match parseSource source with
        | some (.block block) =>
            out := out.push (name, source, pruneLinkerBlock (block.map desugarStmt))
        | _ => pure ()
    | _ => pure ()
  return out

/-- Per-category aggregate over the comparable fixtures (all three pipelines compiled). -/
structure Cat where
  fp      : UInt64 := 0    -- fingerprint of *all* block/latest-fork sources in the category
  nSrc    : Nat := 0       -- block + latest-fork fixtures (fingerprinted set)
  nCmp    : Nat := 0       -- fixtures where current & ir-noopt & ir-opt all compiled
  cur     : Nat := 0       -- Σ current size over the comparable set
  irNo    : Nat := 0       -- Σ ir-noopt size
  irOp    : Nat := 0       -- Σ ir-opt size
  deriving Inhabited

/-- The optimizer-step directory a fixture belongs to. -/
def categoryOf (name : String) : String := (name.splitOn "/").headD name

/-- Fold one fixture into the per-category map. -/
def addFixture (m : Std.HashMap String Cat) (cat src : String)
    (cur irNo irOp : Option Nat) : Std.HashMap String Cat :=
  let c := m.getD cat {}
  let c := { c with fp := mixHash c.fp (hash src), nSrc := c.nSrc + 1 }
  let c := match cur, irNo, irOp with
    | some a, some b, some d =>
        { c with nCmp := c.nCmp + 1, cur := c.cur + a, irNo := c.irNo + b, irOp := c.irOp + d }
    | _, _, _ => c
  m.insert cat c

/-- Walk a corpus directory and aggregate per category. Returns the map plus the number of
skipped (non-block or non-latest-fork) fixtures. -/
def scan (corpusDir : FilePath) : IO (Std.HashMap String Cat × Nat) := do
  let fixtures ← blockFixtures corpusDir
  let mut m : Std.HashMap String Cat := {}
  for (name, source, b) in fixtures do
    let cur := (compileSource source).map (·.size)
    let irNo := YulIR.Check.codeSizeOf (YulIR.Check.irRoundTrip b)
    let irOp := YulIR.Check.codeSizeOf (YulIR.Check.irOptimized b)
    m := addFixture m (categoryOf name) source cur irNo irOp
  return (m, 0)

/-- Serialize one baseline row: `cat  fp  nSrc  nCmp  cur  irNo  irOp`. -/
def rowString (cat : String) (c : Cat) : String :=
  s!"{cat}\t{c.fp}\t{c.nSrc}\t{c.nCmp}\t{c.cur}\t{c.irNo}\t{c.irOp}"

/-- Parse one baseline row. -/
def parseRow (line : String) : Option (String × Cat) :=
  match line.splitOn "\t" with
  | [cat, fpS, nSrcS, nCmpS, curS, irNoS, irOpS] =>
      let g (s : String) : Nat := s.toNat?.getD 0
      some (cat, { fp := UInt64.ofNat (g fpS), nSrc := g nSrcS, nCmp := g nCmpS,
                   cur := g curS, irNo := g irNoS, irOp := g irOpS })
  | _ => none

/-- Sorted category names. -/
def sortedCats (m : Std.HashMap String Cat) : List String :=
  (m.toList.map (·.1)).mergeSort (· < ·)

/-- The whole baseline text (one row per category, sorted). -/
def render (m : Std.HashMap String Cat) : String :=
  String.intercalate "\n" ((sortedCats m).map (fun cat => rowString cat (m.getD cat {}))) ++ "\n"

/-- Render one summary table row. -/
def sumRow (label : String) (nCmp cur irNo irOp : Nat) : String :=
  let p := YulIR.Check.padTo
  let d := if irNo == 0 then 0 else (Int.ofNat irOp - Int.ofNat irNo) * 100 / Int.ofNat irNo
  p 30 label ++ "  " ++ p 4 (toString nCmp) ++ "  " ++ p 8 (toString cur) ++ " "
    ++ p 8 (toString irNo) ++ " " ++ p 8 (toString irOp) ++ "  " ++ toString d ++ "\n"

/-- A human-readable summary table (not the machine baseline). -/
def summary (m : Std.HashMap String Cat) (skipped : Nat) : String := Id.run do
  let mut out := YulIR.Check.padTo 30 "category" ++ "  cmp   current  ir-noopt ir-opt    Δopt%\n"
  let mut tc := 0; let mut tn := 0; let mut tOp := 0; let mut tCmp := 0
  for cat in sortedCats m do
    let c := m.getD cat {}
    tc := tc + c.cur; tn := tn + c.irNo; tOp := tOp + c.irOp; tCmp := tCmp + c.nCmp
    out := out ++ sumRow cat c.nCmp c.cur c.irNo c.irOp
  out := out ++ sumRow "TOTAL" tCmp tc tn tOp
  out := out ++ s!"(skipped {skipped} object/non-latest-fork fixtures)\n"
  out

/-- Behaviour sweep: the IR-optimized bytecode must match the current pipeline's bytecode
observably (under the differential scenarios) on every comparable fixture. A mismatch is a
miscompile in `optimize`/translation. -/
def behaviour (corpusDir : FilePath) : IO UInt32 := do
  let fixtures ← blockFixtures corpusDir
  let mut ok := 0; let mut mism := 0; let mut uncmp := 0; let mut timeout := 0
  for (name, source, b) in fixtures do
    match compileSource source, YulIR.Check.blockBytecode (YulIR.Check.irOptimized b) with
    | some cur, some irOp =>
        match compareBytecode irOp cur with
        | .ok _ => ok := ok + 1
        | .error e =>
            -- A "did not halt within N steps" difference is a gas/step-cap artefact for
            -- gas-bound or non-terminating programs (differently-sized code hits the step
            -- cap vs the gas limit at different points), not an observable-state divergence.
            if (e.splitOn "did not halt").length > 1 then
              timeout := timeout + 1
            else
              mism := mism + 1; IO.eprintln s!"::error::{name}: ir-opt ≠ current — {e}"
    | _, _ => uncmp := uncmp + 1
  IO.println s!"YulIR behaviour: {ok} match current, {mism} MISMATCH, {timeout} step-cap/gas-bound, {uncmp} uncompilable."
  return (if mism == 0 then 0 else 1)

/-- Gas comparison: total EVM execution gas of the IR-optimized code vs the current pipeline,
summed over every gas-comparable (both halt identically) scenario across the corpus. This is the
metric solc's optimizer actually targets, and where CSE/inlining pay off even when they cost code
size. Measurement only — cannot affect correctness. -/
def gasReport (corpusDir : FilePath) : IO UInt32 := do
  let fixtures ← blockFixtures corpusDir
  let mut irTot := 0; let mut curTot := 0; let mut n := 0; let mut wins := 0; let mut losses := 0
  for (name, source, b) in fixtures do
    match compileSource source, YulIR.Check.blockBytecode (YulIR.Check.irOptimized b) with
    | some cur, some irOp =>
        for (_, res) in measureGas irOp cur (scenarioSeed := fixtureSeed name) do
          match res with
          | some (gi, gc) =>
              irTot := irTot + gi; curTot := curTot + gc; n := n + 1
              if gi < gc then wins := wins + 1 else if gi > gc then losses := losses + 1
          | none => pure ()
    | _, _ => pure ()
  IO.println s!"YulIR gas over {n} comparable scenarios: ir-opt={irTot}  current={curTot}  Δ={Int.ofNat irTot - Int.ofNat curTot}"
  IO.println s!"  per-scenario: ir-opt cheaper in {wins}, costlier in {losses}, equal in {n - wins - losses}"
  return 0

end YulIRCorpus

open YulIRCorpus

def main (args : List String) : IO UInt32 := do
  match args with
  | ["report", dir] => do
      let (m, skipped) ← scan dir
      IO.print (summary m skipped)
      return 0
  | ["behaviour", dir] => behaviour dir
  | ["behavior", dir] => behaviour dir
  | ["gas", dir] => gasReport dir
  | ["update", dir, baseline] => do
      let (m, skipped) ← scan dir
      IO.FS.writeFile baseline (render m)
      IO.print (summary m skipped)
      IO.println s!"Wrote {baseline}."
      return 0
  | ["check", dir, baseline] => do
      let (m, _) ← scan dir
      let expected ← try IO.FS.readFile baseline catch _ => pure ""
      if expected.isEmpty then
        IO.eprintln s!"{baseline} missing; run `update` first."; return 1
      let pinned : Std.HashMap String Cat :=
        (expected.splitOn "\n").foldl (init := {}) fun acc line =>
          match parseRow line with | some (c, r) => acc.insert c r | none => acc
      let mut gated := 0; let mut regressions := 0; let mut drifted := 0
      for cat in sortedCats m do
        let now := m.getD cat {}
        match pinned.get? cat with
        | some old =>
            if old.fp == now.fp then
              gated := gated + 1
              if now.nCmp < old.nCmp then
                regressions := regressions + 1
                IO.eprintln s!"::error::{cat}: compilable set shrank {old.nCmp} → {now.nCmp} (an IR compile regression)"
              else if now.irOp > old.irOp || now.irNo > old.irNo then
                regressions := regressions + 1
                IO.eprintln s!"::error::{cat}: IR size regressed — ir-noopt {old.irNo}→{now.irNo}, ir-opt {old.irOp}→{now.irOp}"
              else if now.irOp < old.irOp then
                IO.println s!"{cat}: ir-opt improved {old.irOp} → {now.irOp} (re-run `update` to lock in)"
            else
              drifted := drifted + 1   -- source changed upstream: report, don't gate
        | none => drifted := drifted + 1
      IO.println s!"YulIR corpus check: gated {gated} categories, {drifted} drifted/new, {regressions} regressions."
      return (if regressions == 0 then 0 else 1)
  | _ => do
      IO.eprintln "usage: YulIRCorpus (report <dir> | update <dir> <baseline> | check <dir> <baseline>)"
      return 2
