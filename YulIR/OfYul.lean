import YulIR.Ast
import YulSemantics.Ast

/-!
# YulIR.OfYul — translate Yul into the IR

This is the *trusted* front-end translation (no soundness proof yet). It performs:

* **ANF flattening** (`ExpressionSplitter`-style): nested built-in/call arguments are
  lifted into fresh `let`-temporaries. Arguments are flattened **right-to-left**, so the
  emitted `let`-sequence reproduces Yul's observable right-to-left argument-evaluation
  order (the order `solc` has historically miscompiled by breaking).
* **`for`-init removal**: `for { init } c { post } { body }` becomes
  `{ init ; loop post body }` (a wrapping block preserves the init variables' scope),
  with the condition moved to the top of the loop body as `if iszero(c) { break }`.

Fresh temporaries are named `_ir_<n>`; a later uniqueness/renaming pass can canonicalise
them. Multi-result expressions (user calls) are kept at statement level and are never
lifted into a temporary, matching Yul's rule that *nested* expressions are single-valued.
-/

namespace YulIR

open YulSemantics (Ident Literal)

/-- Yul expressions/statements over the EVM dialect. -/
abbrev YExpr := YulSemantics.Expr Op
abbrev YStmt := YulSemantics.Stmt Op

/-- Translation state: a fresh-name counter plus the accumulating function table (keyed by name)
of functions lifted out of the statement stream. -/
abbrev OfM := StateM (Nat × Std.HashMap Ident Function)

/-- Allocate a fresh temporary name. -/
def fresh : OfM Ident := fun (n, fs) => (s!"_ir_{n}", (n + 1, fs))

/-- Record a function (keyed by name) lifted to the top level. Assumes distinct source names; a
collision would overwrite (see `YulIR.OfYul` module note / `uniquify`). -/
def emitFn (name : Ident) (f : Function) : OfM Unit := fun (n, fs) => ((), (n, fs.insert name f))

mutual

/-- Flatten a Yul expression used in **argument position** (must be single-valued):
returns the `let`-temporaries to emit (in evaluation order) and the resulting atom. -/
partial def flattenExpr : YExpr → OfM (Block × Atom)
  | .lit l => pure ([], .lit l)
  | .var x => pure ([], .var x)
  | .builtin op args => do
      let (binds, atoms) ← flattenArgs args
      let t ← fresh
      pure (binds ++ [Stmt.letD [t] (.builtin op atoms)], .var t)
  | .call fn args => do
      let (binds, atoms) ← flattenArgs args
      let t ← fresh
      pure (binds ++ [Stmt.letD [t] (.call fn atoms)], .var t)

/-- Flatten an argument list right-to-left. The emitted bindings are in evaluation
order (rightmost argument first); the returned atoms are in source (left-to-right) order. -/
partial def flattenArgs : List YExpr → OfM (Block × List Atom)
  | [] => pure ([], [])
  | e :: rest => do
      let (restBinds, restAtoms) ← flattenArgs rest
      let (eBinds, eAtom) ← flattenExpr e
      pure (restBinds ++ eBinds, eAtom :: restAtoms)

/-- Flatten an expression in **rhs position** (`let`/`assign`/`exprStmt`), where a
multi-result user call is allowed and must *not* be lifted into a temporary. -/
partial def rhsOfExpr : YExpr → OfM (Block × Rhs)
  | .lit l => pure ([], .atom (.lit l))
  | .var x => pure ([], .atom (.var x))
  | .builtin op args => do
      let (binds, atoms) ← flattenArgs args
      pure (binds, .builtin op atoms)
  | .call fn args => do
      let (binds, atoms) ← flattenArgs args
      pure (binds, .call fn atoms)

/-- Translate one Yul statement into a sequence of IR statements. -/
partial def stmtOfYul : YStmt → OfM Block
  | .block body => do
      let b ← blockOfYul body
      pure [Stmt.block b]
  | .funDef n ps rs body => do
      -- lift the function to the top level; it leaves no statement behind. Nested `funDef`s in
      -- `body` are lifted too (recursively, by `blockOfYul`). Sound because Yul functions capture
      -- no enclosing variables, so flattening to one scope changes no call resolution.
      let b ← blockOfYul body
      emitFn n { params := ps, rets := rs, body := b }
      pure []
  | .letDecl vars none =>
      -- zero-initialise each declared variable
      pure (vars.map (fun v => Stmt.letD [v] (.atom (.lit (.number 0)))))
  | .letDecl vars (some e) => do
      let (binds, rhs) ← rhsOfExpr e
      pure (binds ++ [Stmt.letD vars rhs])
  | .assign vars e => do
      let (binds, rhs) ← rhsOfExpr e
      pure (binds ++ [Stmt.assign vars rhs])
  | .exprStmt e => do
      let (binds, rhs) ← rhsOfExpr e
      pure (binds ++ [Stmt.effect rhs])
  | .cond c body => do
      let (cb, ca) ← flattenExpr c
      let b ← blockOfYul body
      pure (cb ++ [Stmt.cond ca b])
  | .switch c cases dflt => do
      let (cb, ca) ← flattenExpr c
      let cs ← casesOfYul cases
      let d ← dfltOfYul dflt
      pure (cb ++ [Stmt.switch ca cs d])
  | .forLoop init c post body => do
      let initIR ← blockOfYul init
      let (cb, ca) ← flattenExpr c
      let t ← fresh
      -- condition check at the top of the loop body: `if iszero(c) { break }`
      let condCheck : Block :=
        cb ++ [Stmt.letD [t] (.builtin .iszero [ca]), Stmt.cond (.var t) [Stmt.«break»]]
      let bodyIR ← blockOfYul body
      let postIR ← blockOfYul post
      let loopStmt := Stmt.loop postIR (condCheck ++ bodyIR)
      -- a wrapping block keeps init-declared variables scoped to the loop
      if initIR.isEmpty then
        pure [loopStmt]
      else
        pure [Stmt.block (initIR ++ [loopStmt])]
  | .«break» => pure [Stmt.«break»]
  | .«continue» => pure [Stmt.«continue»]
  | .leave => pure [Stmt.leave]

/-- Translate a Yul block. -/
partial def blockOfYul : List YStmt → OfM Block
  | [] => pure []
  | s :: ss => do
      let a ← stmtOfYul s
      let b ← blockOfYul ss
      pure (a ++ b)

/-- Translate `switch` cases. -/
partial def casesOfYul : List (Literal × List YStmt) → OfM (List (Literal × Block))
  | [] => pure []
  | (l, b) :: rest => do
      let b' ← blockOfYul b
      let rest' ← casesOfYul rest
      pure ((l, b') :: rest')

/-- Translate an optional `default` block. -/
partial def dfltOfYul : Option (List YStmt) → OfM (Option Block)
  | none => pure none
  | some b => do
      let b' ← blockOfYul b
      pure (some b')

end

/-- Translate a whole Yul program (top-level block) into the IR `Program`: functions are lifted
into a flat top-level list; the remaining statements form `main`. -/
def ofYul (b : YulSemantics.Block Op) : Program :=
  let (main, (_, fs)) := (blockOfYul b).run (0, ∅)
  { functions := fs, main := main }

end YulIR
