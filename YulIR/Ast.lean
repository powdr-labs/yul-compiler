import YulSemantics.Dialect.EVM

/-!
# YulIR.Ast — the experimental optimizer IR

A small A-normal-form (ANF) intermediate representation for the Yul→EVM optimizer.
The point of this IR (vs. optimizing Yul directly) is to make the *optimizations*
and, later, their *proofs* tractable:

* **ANF.** Every built-in / call argument is an `Atom` (a literal or a variable);
  nested expressions are lifted into explicit `let`-temporaries. This removes the
  entanglement between expression evaluation, side effects, and halting that makes
  the Yul big-step judgment hard to reason about, and it fixes evaluation order
  syntactically (the `let`-sequence *is* the order).
* **Pure / effect split available.** Built-ins carry the dialect `Op`; purity is
  read off `YulSemantics.EVM.effects` (see `YulIR.Effects`).
* **Structured control, no `for`-init.** A Yul `for { init } c { post } { body }`
  is translated to `{ init ; loop post body }` with the condition moved into the
  body as `… ; if iszero(c) { break }`. So the IR `loop` carries no init and no
  separate condition — it denotes `for {} 1 { post } { body }`.

The IR is deliberately *named* (variables are `Ident`s), so erasing back to Yul is a
structural rewrite. The intrinsically-scoped (`Var Γ`) refinement is left for when we
start proving things, mirroring `YulEvmCompiler.Optimizer.Core.Term`.

No semantics or proofs live here yet — this module is pure syntax plus the two
translations (`YulIR.OfYul`, `YulIR.ToYul`).
-/

namespace YulIR

/-- The IR is specialised to the EVM dialect's built-in operations. -/
abbrev Op := YulSemantics.EVM.Op

open YulSemantics (Ident Literal)

/-- An ANF operand: the only thing accepted in argument position. -/
inductive Atom
  | lit (l : Literal)
  | var (x : Ident)
  deriving Repr, Inhabited, DecidableEq

/-- A right-hand side: a single operation applied to atoms.

* `atom`    — a bare operand (a copy `x := y` or a constant);
* `builtin` — a dialect built-in `op(atoms…)` (pure or effectful — see `YulIR.Effects`);
* `call`    — a user-defined function call `fn(atoms…)` (may be multi-result). -/
inductive Rhs
  | atom    (a : Atom)
  | builtin (op : Op) (args : List Atom)
  | call    (fn : Ident) (args : List Atom)
  deriving Repr, Inhabited

/-- An IR statement. Blocks are `List Stmt`. -/
inductive Stmt
  /-- `{ body }` — a nested block (a new scope; its `funDef`s hoist within it). -/
  | block   (body : List Stmt)
  /-- `function name(params) -> rets { body }`. -/
  | funDef  (name : Ident) (params rets : List Ident) (body : List Stmt)
  /-- `let vars := rhs`. `vars.length` matches the number of values `rhs` produces. -/
  | letD    (vars : List Ident) (rhs : Rhs)
  /-- `vars := rhs`. -/
  | assign  (vars : List Ident) (rhs : Rhs)
  /-- An effectful rhs evaluated for its side effects, producing no values (`exprStmt`). -/
  | effect  (rhs : Rhs)
  /-- `if c { body }` — the condition is already an atom. -/
  | cond    (c : Atom) (body : List Stmt)
  /-- `switch c (case lit { … })* (default { … })?` — condition already an atom. -/
  | switch  (c : Atom) (cases : List (Literal × List Stmt)) (dflt : Option (List Stmt))
  /-- `for {} 1 { post } { body }` — no init, condition folded into `body`. -/
  | loop    (post body : List Stmt)
  /-- `break`. -/
  | «break»
  /-- `continue`. -/
  | «continue»
  /-- `leave`. -/
  | leave
  deriving Repr, Inhabited

/-- A block of IR statements. -/
abbrev Block := List Stmt

end YulIR
