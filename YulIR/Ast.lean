import YulSemantics.Dialect.EVM
import Std.Data.HashMap

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
  deriving Repr, Inhabited, DecidableEq, BEq

/-- An IR statement. Blocks are `List Stmt`.

Note there is **no `funDef` constructor**: unlike Yul (and unlike this IR's earlier form),
functions are not statements. They are collected into a flat, top-level `List Function` on the
enclosing `Program`/`Object` (see `YulIR.OfYul`, which lifts every `funDef` out during
translation). Yul functions capture no enclosing *variables* — only their parameters, returns,
locals, and the functions in scope — so hoisting them all to one flat scope with unique names is
behaviour-preserving, and it takes the whole `funDef`-hoisting/scoping tangle out of every pass. -/
inductive Stmt
  /-- `{ body }` — a nested block (a new variable scope). -/
  | block   (body : List Stmt)
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

/-- A user-defined function's signature and body, lifted out of the statement stream to the top
level. The function's **name is the key** in `Program.functions`, so it is not stored here. -/
structure Function where
  params : List Ident
  rets   : List Ident
  body   : Block
  deriving Repr, Inhabited

/-- A translation/optimization unit: a table of functions keyed by name, plus a `main` block.

Keying by name in a `HashMap` makes function-name **uniqueness structural** (no duplicate keys) and
gives O(1) call-target lookup. Iteration order of a `HashMap` is not deterministic, so `YulIR.toYul`
**sorts by name** when erasing, keeping compiled output stable. Erasing emits the functions at the
top of the `main` block, where Yul's hoisting makes them mutually visible throughout it. -/
structure Program where
  functions : Std.HashMap Ident Function
  main      : Block
  deriving Inhabited

namespace Program

/-- The functions as a name→function list (unspecified order; sort by key when order matters). -/
def funList (p : Program) : List (Ident × Function) := p.functions.toList

/-- Rebuild the function table by transforming each function (its name is available). Keys are
preserved, so uniqueness is maintained. -/
def mapFunctions (f : Ident → Function → Function) (p : Program) : Program :=
  { p with functions := Std.HashMap.ofList (p.funList.map (fun (n, fn) => (n, f n fn))) }

/-- Transform every function body and `main` by the same block transformation. -/
def mapBodies (g : Block → Block) (p : Program) : Program :=
  { functions := Std.HashMap.ofList (p.funList.map (fun (n, fn) => (n, { fn with body := g fn.body })))
    main := g p.main }

end Program

end YulIR
