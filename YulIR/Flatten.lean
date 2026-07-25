import YulIR.Ast

set_option warningAsError true
/-!
# YulIR.Flatten — dissolve unnecessary nested blocks

A standalone `.block` statement exists only to **scope its variable declarations**. Once `uniquify`
has made every variable name globally unique, a nested block's `let`s can never collide with the
enclosing scope, so the block carries no meaning — its statements can be spliced directly into the
parent sequence.

This pass removes every standalone `.block`, keeping blocks only where they are *syntactically
needed*: as the body of an `if` / `switch` case / `loop` / function. Those bodies are `List Stmt`
positions in the grammar, not `.block` statements, so they inherently remain.

**Soundness** (validated by the round-trip/behaviour checks): only sound under unique names, so this
runs after `uniquify`. Splicing a block extends the lifetime of its bindings to the end of the
parent scope, but with unique names nothing later resolves to those names, so the machine's
observable state is unchanged (only the otherwise-unobservable variable environment differs).
-/

namespace YulIR

mutual
/-- Flatten a statement into a list of statements: a standalone `.block` becomes its (flattened)
contents spliced in place; control-flow constructs keep their bodies but flatten within them. -/
partial def flattenStmt : Stmt → List Stmt
  | .block body       => flattenBlock body
  | .cond c body      => [.cond c (flattenBlock body)]
  | .switch c cs dflt => [.switch c (cs.map (fun p => (p.1, flattenBlock p.2))) (dflt.map flattenBlock)]
  | .loop post body   => [.loop (flattenBlock post) (flattenBlock body)]
  | s                 => [s]

/-- Flatten every statement in a block, splicing dissolved sub-blocks into the sequence. -/
partial def flattenBlock : Block → Block
  | []      => []
  | s :: ss => flattenStmt s ++ flattenBlock ss
end

/-- Dissolve unnecessary nested blocks throughout a program — every function body and `main`.
Assumes unique names (run after `uniquify`). -/
def flatten (p : Program) : Program := p.mapBodies flattenBlock

end YulIR
