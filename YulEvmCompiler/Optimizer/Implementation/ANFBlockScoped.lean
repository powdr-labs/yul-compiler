import YulEvmCompiler.Optimizer.Implementation.ANF
/-!
# ANF pass 1 — block-scoped operand flattening

The first of two passes (see `ANFFlattenBlocks` for pass 2). This pass flattens
each **straight-line** statement's operands into atoms, scoping the introduced
temporaries in a fresh sub-block so the enclosing `restore` discharges them
locally (no persistent-temp frame invariant needed):

```text
sstore(add(a,b), c)  ⟶  { let t := add(a,b); sstore(t, c) }
x := f(g(y))         ⟶  { let t := g(y); x := f(t) }        -- x is outer, assigned inside
let x := f(g(y))     ⟶  let x; { let t := g(y); x := f(t) } -- x declared out, assigned in
```

It is the identity on control-flow statements and function definitions; pass 2
(block flattening / inlining) then lifts the sub-blocks back out, and the two
compose to the persistent-temporary form. Soundness of each per-statement
rewrite is a local `EquivStmt` (via `restore_prefix`), composed with
`EquivStmts.cons_congr` and `EquivBlock.of_stmts`.

This file: the transform and its structural (form) correctness. The `EquivStmt`
soundness (needing the reverse-flatten direction) follows.
-/

namespace YulEvmCompiler.Optimizer.ANF

open YulSemantics YulSemantics.EVM

/-- Block-scoped flattening of one statement. Straight-line statements get their
operands flattened inside a fresh sub-block (`let`s + a `let x`/`assign`/`exprStmt`
using the atoms); everything else is unchanged. -/
def bsStmt (P : String) : Stmt Op → Stmt Op
  | .letDecl vars (some e) =>
      let (_, pre, e') := flattenTop P 0 e
      if pre.isEmpty then .letDecl vars (some e')
      else .block ([.letDecl vars none] ++ pre ++ [.assign vars e'])
  | .assign vars e =>
      let (_, pre, e') := flattenTop P 0 e
      if pre.isEmpty then .assign vars e'
      else .block (pre ++ [.assign vars e'])
  | .exprStmt e =>
      let (_, pre, e') := flattenTop P 0 e
      if pre.isEmpty then .exprStmt e'
      else .block (pre ++ [.exprStmt e'])
  | s => s

/-- Block-scoped flattening of a statement list. -/
def bsStmts (P : String) : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest => bsStmt P s :: bsStmts P rest

end YulEvmCompiler.Optimizer.ANF
