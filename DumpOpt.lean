/-
DumpOpt.lean — dump this compiler's optimized Yul for a solc `--ir` file.

Usage: lake env lean --run DumpOpt.lean <file.yul>

Mirrors `YulParser.compileSource`'s candidate order, and prints the Yul of the
first candidate whose backend accepts, so the dump is what actually executes.
-/
import YulParser.Compile
import YulParser.Obj

open YulSemantics (Expr Stmt Object)
open YulEvmCompiler
open YulEvmCompiler.Optimizer

abbrev Op := YulSemantics.EVM.Op
abbrev DD := YulSemantics.EVM.evmWithExternal YulSemantics.EVM.ExternalCalls.none
  YulSemantics.EVM.ExternalCreates.none

def pipeBlock (n : Nat) (b : List (Stmt Op)) : List (Stmt Op) :=
  (optimizerPipelineRounds (calls := YulSemantics.EVM.ExternalCalls.none)
    (creates := YulSemantics.EVM.ExternalCreates.none) n).run b

def pipeObj (n : Nat) (o : Object Op) : Object Op :=
  optimizerPipelineObjectRounds (calls := YulSemantics.EVM.ExternalCalls.none)
    (creates := YulSemantics.EVM.ExternalCreates.none) n o

def main (args : List String) : IO Unit := do
  let path : String := (args[0]?).getD ""
  if path == "" then
    IO.eprintln "usage: DumpOpt <file.yul>"
    return
  let src ← IO.FS.readFile (System.FilePath.mk path)
  let stage := (args[1]?).getD "opt"
  match YulParser.parseSource src with
  | none => IO.eprintln "parse failed"
  | some (.block block) =>
      let raw := YulParser.pruneLinkerBlock (YulParser.decodeValueStmts block)
      let b := Normalize.normalize (D := DD) (raw.map YulParser.desugarStmt)
      let out :=
        if stage == "norm" then b
        else if stage == "raw" then raw
        else pipeBlock 6 b
      IO.println (String.ofList (YulParser.printStmtsC out))
  | some (.object o) =>
      let raw := YulParser.pruneLinkerObjectTree (YulParser.decodeValueObject o)
      let no := Normalize.normalizeObject (D := DD) (YulParser.desugarObject raw)
      let out :=
        if stage == "norm" then no
        else if stage == "raw" then raw
        else pipeObj 6 no
      IO.println (String.ofList (YulParser.printObjC out))
