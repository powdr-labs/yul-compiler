import YulParser.Source
import YulEvmCompiler.ObjectCompile
import YulEvmCompiler.Optimizer.Implementation.Simplify

/-!
# YulParser.Compile

The source-text entry point for the compiler. Brace-delimited programs assemble
directly. Object-rooted programs are recursively laid out with their child
objects and data bytes, and `dataoffset`/`datasize` are resolved to constants
in that concrete layout.
-/

namespace YulParser

open YulSemantics (Expr Stmt Object)

/-- Desugar solc-IR hint builtins that have no EVM value effect into core Yul,
before compilation. `memoryguard(e)` is a Yul optimizer hint whose value is
just its argument, so it lowers to `e`; the verified compiler then handles the
result unchanged. Every other node is rebuilt structurally, so programs that do
not use such hints are unaffected. -/
partial def desugarExpr {Op : Type} : Expr Op → Expr Op
  | .call "memoryguard" [arg] => desugarExpr arg
  | .call fn args => .call fn (args.map desugarExpr)
  | .builtin op args => .builtin op (args.map desugarExpr)
  | e => e

partial def desugarStmt {Op : Type} : Stmt Op → Stmt Op
  | .block body => .block (body.map desugarStmt)
  | .funDef name params rets body => .funDef name params rets (body.map desugarStmt)
  | .letDecl vars val => .letDecl vars (val.map desugarExpr)
  | .assign vars val => .assign vars (desugarExpr val)
  | .cond c body => .cond (desugarExpr c) (body.map desugarStmt)
  | .switch c cases dflt =>
      .switch (desugarExpr c) (cases.map (fun cb => (cb.1, cb.2.map desugarStmt)))
        (dflt.map (fun b => b.map desugarStmt))
  | .forLoop init c post body =>
      .forLoop (init.map desugarStmt) (desugarExpr c) (post.map desugarStmt) (body.map desugarStmt)
  | .exprStmt e => .exprStmt (desugarExpr e)
  | s => s

partial def desugarObject {Op : Type} : Object Op → Object Op
  | .mk name code subs segs => .mk name (code.map desugarStmt) (subs.map desugarObject) segs

/-- Parse and compile a complete Yul source program to executable EVM bytecode,
using the documented compatibility parser when the verified parser does not
apply. Hint builtins (`memoryguard`) are desugared before compilation.

Block-rooted programs are run through the verified `Optimizer.simplify` pass
(constant folding + neutral-element identities) before the backend; soundness of
this composition is `Optimizer.Pass.optimize_then_compile_correct`. -/
def compileSource (source : String) : Option ByteArray := do
  match parseSource source with
  | some (.block block) =>
      return YulEvmCompiler.assemble
        (← YulEvmCompiler.compile (YulEvmCompiler.Optimizer.simplifyStmts (block.map desugarStmt)))
  | some (.object o) =>
      let layout ← YulEvmCompiler.compileObject (desugarObject o)
      return ByteArray.mk layout.code.toArray
  | none => none

end YulParser
