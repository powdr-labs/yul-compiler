import YulParser.Compile
import YulEvmCompilerTests.Solc
import YulEvmCompilerTests.SolidityCorpus
import YulSemantics.PrettyPrint
set_option warningAsError true

/-!
# DumpYul — debugging aid: print the optimized Yul we feed to the backend.

Reproduces the object-path optimization in `compileSource` (including the
memory-spill fallback that PoolSwap-class objects reach) and pretty-prints the
resulting optimized Yul so residual `mload`/`mstore` shapes can be inspected.
-/

open System YulParser
open YulSemantics
open YulEvmCompilerTests.Solc
open YulEvmCompilerTests.SolidityCorpus

private def NC := YulSemantics.EVM.ExternalCalls.none
private def NR := YulSemantics.EVM.ExternalCreates.none

/-- Optimized object tree exactly as `compileSource` would compile it (primary
candidate, then spill fallback). Returns the object whose code we actually feed
to the backend, along with a tag. -/
private def optimizedObject (o0 : Object YulSemantics.EVM.Op) :
    Object YulSemantics.EVM.Op × String :=
  let raw := pruneLinkerObjectTree (decodeValueObject o0)
  let o := YulEvmCompiler.Optimizer.Normalize.normalizeObject
    (D := YulSemantics.EVM.evmWithExternal NC NR) (desugarObject raw)
  let optimized := YulEvmCompiler.Optimizer.optimizerPipelineObject
    (calls := NC) (creates := NR) o
  match YulEvmCompiler.compileObject optimized with
  | some _ => (optimized, "primary")
  | none =>
    match YulEvmCompiler.Optimizer.MemorySpillSelect.spillObjectWithFallback raw optimized with
    | some spilled =>
        let spilledOptBase := YulEvmCompiler.Optimizer.optimizerPipelineObject
          (calls := NC) (creates := NR)
          (YulEvmCompiler.Optimizer.Normalize.normalizeObject
            (D := YulSemantics.EVM.evmWithExternal NC NR) spilled.object)
        let spilledOpt := YulEvmCompiler.Optimizer.optimizerPipelineObject
          (calls := NC) (creates := NR)
          (YulEvmCompiler.Optimizer.MemoryForward.memoryForwardObject spilledOptBase)
        (spilledOpt, s!"spilled(selected={spilled.selected})")
    | none => (optimized, "primary(uncompilable)")

def main (args : List String) : IO UInt32 := do
  match args with
  | fixture :: solcPath :: rest => do
    let contents ← IO.FS.readFile fixture
    let source := fixtureSource contents
    let ir ← do
      match ← solcUnoptimizedIR solcPath source with
      | .ok ir => pure ir
      | .error e => IO.eprintln e; return 1
    match parseSource ir with
    | some (.object o) =>
        let (opt, tag) := optimizedObject o
        IO.println s!"-- optimized object path: {tag}"
        -- Dump only the deepest runtime code block unless --full given.
        if rest.contains "--full" then
          IO.println (EVM.printObject opt)
        else
          -- Find the runtime sub-object code (the one whose name ends in "_deployed").
          let rec findDeployed : Object YulSemantics.EVM.Op → Option (Object YulSemantics.EVM.Op)
            | o@(.mk n _ subs _) =>
                if n.endsWith "_deployed" then some o
                else subs.foldl (fun acc s => acc <|> findDeployed s) none
          match findDeployed opt with
          | some d => IO.println (EVM.printObject d)
          | none => IO.println (EVM.printObject opt)
        return 0
    | _ => IO.eprintln "expected an object"; return 1
  | _ => IO.eprintln "usage: dumpYul <fixture.sol> <solc> [--full]"; return 64
