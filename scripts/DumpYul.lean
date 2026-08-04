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
    let rematRaw := YulEvmCompiler.Optimizer.RematSpill.rematObject raw
    match YulEvmCompiler.Optimizer.MemorySpillSelect.spillObjectWithFallback rematRaw rematRaw with
    | some spilled =>
        let spilledOptBase := YulEvmCompiler.Optimizer.optimizerPipelineObject
          (calls := NC) (creates := NR)
          (YulEvmCompiler.Optimizer.Normalize.normalizeObject
            (D := YulSemantics.EVM.evmWithExternal NC NR) spilled.object)
        (spilledOptBase, s!"remat-spilled(selected={spilled.selected})")
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
        if rest.contains "--spillcount" then
          let raw := pruneLinkerObjectTree (decodeValueObject o)
          let on := YulEvmCompiler.Optimizer.Normalize.normalizeObject
            (D := YulSemantics.EVM.evmWithExternal NC NR) (desugarObject raw)
          let optimized := YulEvmCompiler.Optimizer.optimizerPipelineObject
            (calls := NC) (creates := NR) on
          let selOf := fun ob =>
            match YulEvmCompiler.Optimizer.MemorySpillSelect.spillObjectWithFallback ob ob with
            | some r => r.selected | none => 0
          let rec declCount : Object YulSemantics.EVM.Op → Nat
            | .mk _ code subs _ =>
                (YulEvmCompiler.Optimizer.MemorySpill.declaredStmts code).length +
                  subs.foldl (fun a s => a + declCount s) 0
          let rematRaw := YulEvmCompiler.Optimizer.RematSpill.rematObject raw
          -- Mirror compileSource's spillCompile: spill `base` (fallback
          -- `optimized`), re-optimize, store-elim, compile; report code size.
          let spillCompile := fun (base : Object YulSemantics.EVM.Op) =>
            (match YulEvmCompiler.Optimizer.MemorySpillSelect.spillObjectWithFallback
              base optimized with
            | some spilled =>
                if spilled.selected = 0 then none
                else match YulEvmCompiler.compileObject spilled.object with
                  | none => none
                  | some plainLayout =>
                      let sOpt := YulEvmCompiler.Optimizer.SpillStoreElim.elimObject
                        (YulEvmCompiler.Optimizer.optimizerPipelineObject (calls := NC)
                          (creates := NR) (YulEvmCompiler.Optimizer.Normalize.normalizeObject
                            (D := YulSemantics.EVM.evmWithExternal NC NR) spilled.object))
                      YulEvmCompiler.compileObject sOpt
                        <|> YulEvmCompiler.compileObject
                          (YulEvmCompiler.Optimizer.stackLayoutObject sOpt)
                        <|> some plainLayout
            | none => none : Option YulSemantics.EVM.Layout)
          let szOf := fun (l : Option YulSemantics.EVM.Layout) =>
            match l with | some x => x.code.length | none => 0
          IO.println s!"raw:   spillCount={selOf raw}   codeSize={szOf (spillCompile raw)}"
          IO.println s!"remat: spillCount={selOf rematRaw}   codeSize={szOf (spillCompile rematRaw)}"
          return 0
        let (opt, tag) :=
          if rest.contains "--prespill" then
            let raw := pruneLinkerObjectTree (decodeValueObject o)
            let on := YulEvmCompiler.Optimizer.Normalize.normalizeObject
              (D := YulSemantics.EVM.evmWithExternal NC NR) (desugarObject raw)
            (YulEvmCompiler.Optimizer.optimizerPipelineObject (calls := NC) (creates := NR) on,
             "prespill-optimized")
          else optimizedObject o
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
