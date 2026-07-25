import YulIR.Ast
import YulSemantics.Ast

/-!
# YulIR.ToYul — erase the IR back to Yul

The IR is a named, structured, ANF rewriting of Yul, so lowering back is a plain
structural erasure (no fresh state, no synthesis):

* atoms/`Rhs` become the corresponding `YulSemantics.Expr`;
* `loop post body` becomes `for {} 1 { post } { body }` (the condition already lives
  inside `body` as an `if iszero(c) { break }`, see `YulIR.OfYul`).

The emitted Yul feeds the existing verified `YulEvmCompiler` backend, so IR
optimizations are measured as real EVM-level (gas) changes with no new lowering to
trust.
-/

namespace YulIR

open YulSemantics

/-- Erase an atom. -/
def Atom.toYul : Atom → Expr Op
  | .lit l => .lit l
  | .var x => .var x

/-- Erase a right-hand side to a Yul expression. -/
def Rhs.toYul : Rhs → Expr Op
  | .atom a       => a.toYul
  | .builtin op a => .builtin op (a.map Atom.toYul)
  | .call fn a    => .call fn (a.map Atom.toYul)

/-- The literal `1`, used as the always-true condition of a lowered `loop`. -/
private def trueLit : Expr Op := .lit (.number 1)

mutual
/-- Erase an IR statement to a Yul statement. -/
partial def Stmt.toYul : Stmt → YulSemantics.Stmt Op
  | .block body        => .block (Stmt.toYulBlock body)
  | .letD vars rhs     => .letDecl vars (some rhs.toYul)
  | .assign vars rhs   => .assign vars rhs.toYul
  | .effect rhs        => .exprStmt rhs.toYul
  | .cond c body       => .cond c.toYul (Stmt.toYulBlock body)
  | .switch c cs dflt  =>
      .switch c.toYul (cs.map (fun p => (p.1, Stmt.toYulBlock p.2)))
        (dflt.map Stmt.toYulBlock)
  | .loop post body    => .forLoop [] trueLit (Stmt.toYulBlock post) (Stmt.toYulBlock body)
  | .«break»           => .«break»
  | .«continue»        => .«continue»
  | .leave             => .leave

/-- Erase a block. -/
partial def Stmt.toYulBlock : Block → YulSemantics.Block Op
  | []      => []
  | s :: ss => s.toYul :: Stmt.toYulBlock ss
end

/-- Erase a named function to a Yul `funDef` statement. -/
def Function.toYul (name : Ident) (f : Function) : YulSemantics.Stmt Op :=
  .funDef name f.params f.rets (Stmt.toYulBlock f.body)

/-- Erase a whole IR `Program` to a Yul block: emit the functions — **sorted by name**, so the
`HashMap`'s nondeterministic iteration order cannot affect output — at the top of the block, where
Yul's hoisting makes them mutually visible throughout, then the `main` statements. -/
def toYul (p : Program) : YulSemantics.Block Op :=
  let sorted := p.funList.mergeSort (fun a b => a.1 ≤ b.1)
  sorted.map (fun (n, f) => Function.toYul n f) ++ Stmt.toYulBlock p.main

end YulIR
