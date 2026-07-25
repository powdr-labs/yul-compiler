import YulIR.Ast
import YulSemantics.Ast

set_option warningAsError true
/-!
# YulIR.OfYul — translate Yul into the IR

The *trusted* front-end translation (no soundness proof yet). It performs, in one pass:

* **ANF flattening** (`ExpressionSplitter`-style): nested built-in/call arguments are lifted into
  fresh `let`-temporaries. Arguments are flattened **right-to-left**, reproducing Yul's observable
  right-to-left argument-evaluation order.
* **Variable disambiguation**: every declared variable (and every function parameter/return) is
  α-renamed to a globally fresh name `_ir_<n>`, references resolved through a scoped renaming
  environment. This removes shadowing, so the IR's later value passes can key on names globally.
* **Block flattening**: because names are now globally unique, a Yul `{ … }` block no longer needs
  to exist for scoping — its statements are spliced directly into the parent sequence. The IR
  `Stmt` therefore has **no `block` constructor**; block-freeness is a type-level invariant. Only
  the grammatically-required blocks remain (the `List Stmt` bodies of `if`/`switch`/`loop`/functions).
* **Function lifting**: every `funDef` (at any depth) is lifted into `Program.functions`; a Yul
  `for { init } c { post } { body }` becomes `init ; loop post body` (init spliced, its variables
  freshly named), with the condition folded into the body as `if iszero(c) { break }`.

Absorbing disambiguation here (rather than a separate `uniquify` pass) is what makes removing the
`block` constructor sound: splicing is only behaviour-preserving under unique names.
-/

namespace YulIR

open YulSemantics (Ident Literal)

/-- Yul expressions/statements over the EVM dialect. -/
abbrev YExpr := YulSemantics.Expr Op
abbrev YStmt := YulSemantics.Stmt Op

/-- Translation state: a fresh-name counter plus the accumulating function table (keyed by name). -/
abbrev OfM := StateM (Nat × Std.HashMap Ident Function)

/-- A scoped renaming: source name → fresh name, innermost first. -/
abbrev Ren := List (Ident × Ident)

/-- Allocate a fresh name `_ir_<n>` (used for both ANF temporaries and renamed variables). -/
def fresh : OfM Ident := fun (n, fs) => (s!"_ir_{n}", (n + 1, fs))

/-- Fresh names for a list of binders (one per element). -/
def freshNames : List Ident → OfM (List Ident)
  | []      => pure []
  | _ :: xs => do let f ← fresh; let rest ← freshNames xs; pure (f :: rest)

/-- Record a function (keyed by name) lifted to the top level. Assumes distinct source names; a
collision would overwrite (see the module note). -/
def emitFn (name : Ident) (f : Function) : OfM Unit := fun (n, fs) => ((), (n, fs.insert name f))

/-- Resolve a source variable through the renaming (unchanged if unbound — a stray global). -/
def renVar (σ : Ren) (x : Ident) : Ident :=
  match σ.find? (fun p => p.1 == x) with
  | some p => p.2
  | none   => x

mutual

/-- Flatten a Yul expression in **argument position** (must be single-valued): returns the
`let`-temporaries to emit (in evaluation order) and the resulting atom, references renamed. -/
partial def flattenExpr (σ : Ren) : YExpr → OfM (Block × Atom)
  | .lit l => pure ([], .lit l)
  | .var x => pure ([], .var (renVar σ x))
  | .builtin op args => do
      let (binds, atoms) ← flattenArgs σ args
      let t ← fresh
      pure (binds ++ [Stmt.letD [t] (.builtin op atoms)], .var t)
  | .call fn args => do
      let (binds, atoms) ← flattenArgs σ args
      let t ← fresh
      pure (binds ++ [Stmt.letD [t] (.call fn atoms)], .var t)

/-- Flatten an argument list right-to-left; emitted bindings are in evaluation order (rightmost
first), returned atoms in source order. -/
partial def flattenArgs (σ : Ren) : List YExpr → OfM (Block × List Atom)
  | [] => pure ([], [])
  | e :: rest => do
      let (restBinds, restAtoms) ← flattenArgs σ rest
      let (eBinds, eAtom) ← flattenExpr σ e
      pure (restBinds ++ eBinds, eAtom :: restAtoms)

/-- Flatten an expression in **rhs position** (`let`/`assign`/`exprStmt`), where a multi-result
user call is allowed and must *not* be lifted into a temporary. -/
partial def rhsOfExpr (σ : Ren) : YExpr → OfM (Block × Rhs)
  | .lit l => pure ([], .atom (.lit l))
  | .var x => pure ([], .atom (.var (renVar σ x)))
  | .builtin op args => do
      let (binds, atoms) ← flattenArgs σ args
      pure (binds, .builtin op atoms)
  | .call fn args => do
      let (binds, atoms) ← flattenArgs σ args
      pure (binds, .call fn atoms)

/-- Translate one Yul statement into a sequence of IR statements and the renaming extended with any
binders it introduces (for subsequent statements in the *same* scope). -/
partial def stmtOfYul (σ : Ren) : YStmt → OfM (Block × Ren)
  | .block body => do
      -- a new scope; its inner declarations are freshly named, so splice inline (no `block`) and
      -- discard the inner renaming on exit.
      let b ← blockOfYul σ body
      pure (b, σ)
  | .funDef n ps rs body => do
      -- lift the function; a callee sees only its own (freshly named) params/rets.
      let ps' ← freshNames ps
      let rs' ← freshNames rs
      let b ← blockOfYul ((ps.zip ps') ++ (rs.zip rs')) body
      emitFn n { params := ps', rets := rs', body := b }
      pure ([], σ)
  | .letDecl vars none => do
      let vs' ← freshNames vars                     -- zero-initialise each declared variable
      pure (vs'.map (fun v => Stmt.letD [v] (.atom (.lit (.number 0)))), (vars.zip vs') ++ σ)
  | .letDecl vars (some e) => do
      let (binds, rhs) ← rhsOfExpr σ e              -- rhs evaluated before the binders exist
      let vs' ← freshNames vars
      pure (binds ++ [Stmt.letD vs' rhs], (vars.zip vs') ++ σ)
  | .assign vars e => do
      let (binds, rhs) ← rhsOfExpr σ e
      pure (binds ++ [Stmt.assign (vars.map (renVar σ)) rhs], σ)
  | .exprStmt e => do
      let (binds, rhs) ← rhsOfExpr σ e
      pure (binds ++ [Stmt.effect rhs], σ)
  | .cond c body => do
      let (cb, ca) ← flattenExpr σ c
      let b ← blockOfYul σ body
      pure (cb ++ [Stmt.cond ca b], σ)
  | .switch c cases dflt => do
      let (cb, ca) ← flattenExpr σ c
      let cs ← casesOfYul σ cases
      let d ← dfltOfYul σ dflt
      pure (cb ++ [Stmt.switch ca cs d], σ)
  | .forLoop init c post body => do
      -- `init` variables are scoped to the loop: thread the renaming through `init` into
      -- cond/post/body, then drop it. `init` is spliced before the loop (freshly named ⇒ safe).
      let (initIR, σ') ← seqOfYul σ init
      let (cb, ca) ← flattenExpr σ' c
      let t ← fresh
      let condCheck : Block :=
        cb ++ [Stmt.letD [t] (.builtin .iszero [ca]), Stmt.cond (.var t) [Stmt.«break»]]
      let bodyIR ← blockOfYul σ' body
      let postIR ← blockOfYul σ' post
      pure (initIR ++ [Stmt.loop postIR (condCheck ++ bodyIR)], σ)
  | .«break» => pure ([Stmt.«break»], σ)
  | .«continue» => pure ([Stmt.«continue»], σ)
  | .leave => pure ([Stmt.leave], σ)

/-- Translate a statement sequence, threading the renaming; returns the spliced statements and the
final renaming (used by `for`-init, whose bindings extend to the loop). -/
partial def seqOfYul (σ : Ren) : List YStmt → OfM (Block × Ren)
  | [] => pure ([], σ)
  | s :: ss => do
      let (a, σ') ← stmtOfYul σ s
      let (b, σ'') ← seqOfYul σ' ss
      pure (a ++ b, σ'')

/-- Translate a Yul block as a fresh scope (renaming changes discarded on exit). -/
partial def blockOfYul (σ : Ren) (body : List YStmt) : OfM Block := do
  let (b, _) ← seqOfYul σ body
  pure b

/-- Translate `switch` cases. -/
partial def casesOfYul (σ : Ren) : List (Literal × List YStmt) → OfM (List (Literal × Block))
  | [] => pure []
  | (l, b) :: rest => do
      let b' ← blockOfYul σ b
      let rest' ← casesOfYul σ rest
      pure ((l, b') :: rest')

/-- Translate an optional `default` block. -/
partial def dfltOfYul (σ : Ren) : Option (List YStmt) → OfM (Option Block)
  | none => pure none
  | some b => do
      let b' ← blockOfYul σ b
      pure (some b')

end

/-- Translate a whole Yul program (top-level block) into the IR `Program`: functions lifted into a
flat table, the remaining statements (block-free, uniquely named) forming `main`. -/
def ofYul (b : YulSemantics.Block Op) : Program :=
  let (main, (_, fs)) := (seqOfYul [] b).run (0, ∅)
  { functions := fs, main := main.1 }

end YulIR
