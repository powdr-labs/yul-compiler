import YulIR.Analysis
import YulIR.Effects
import YulIR.Simplify

/-!
# YulIR.ValueNumber — constant/copy propagation, folding, and CSE

A forward pass over unique-named IR that, in one sweep, does:

* **constant propagation** — a `let v := <lit>` records `v ↦ lit`, substituted into later rhs;
* **copy propagation** — `let v := w` (w immutable) records `v ↦ w`;
* **constant folding / identities** — after substitution, `simplifyRhs` folds (so folding now
  works *across* `let`s, which plain `Simplify` could not);
* **common-subexpression elimination** — a pure builtin with all-immutable operands is memoized;
  a later identical expression becomes a copy of the first result.

**Soundness by construction.** It tracks *only immutable values*: entries map an immutable
variable (never an `assign` target — see `mutatedVars`) to a literal or another immutable
variable, and CSE only memoizes pure expressions whose operands are all immutable. Such values
never change, so no entry ever needs invalidation — not across `assign`, effects, calls, or
control flow. Nested scopes are processed with a copy of the current maps and their additions are
discarded on exit (so an inner binder never escapes its scope). Function bodies start fresh
(callees cannot see caller variables).

Redundant `let v := w` copies it introduces are removed by `YulIR.DeadCode`.
-/

namespace YulIR

open YulSemantics (Ident Literal)

/-- Value environment: immutable variable → its known canonical atom. -/
abbrev VEnv := List (Ident × Atom)

/-- Available pure expressions: canonical rhs → the (immutable) variable holding it. -/
abbrev Avail := List (Rhs × Ident)

/-- Resolve an atom through the value environment. -/
def resolveAtom (env : VEnv) : Atom → Atom
  | .lit l => .lit l
  | .var x => match env.find? (fun p => p.1 == x) with
              | some p => p.2
              | none   => .var x

/-- Resolve an rhs's operands. -/
def resolveRhs (env : VEnv) : Rhs → Rhs
  | .atom a        => .atom (resolveAtom env a)
  | .builtin op as => .builtin op (as.map (resolveAtom env))
  | .call fn as    => .call fn (as.map (resolveAtom env))

/-- Is an atom immutable (a literal, or a variable never reassigned)? -/
def isImm (mutated : List Ident) : Atom → Bool
  | .lit _ => true
  | .var x => ! mutated.contains x

/-- Record a `let v := rhs'` (rhs' already resolved+simplified): returns the updated maps and
the rhs to emit (a copy `.atom w` when `v` becomes a constant/known variable or a CSE hit). -/
def recordLet (mutated : List Ident) (env : VEnv) (avail : Avail) (v : Ident) (rhs' : Rhs) :
    VEnv × Avail × Rhs :=
  if mutated.contains v then (env, avail, rhs')   -- v is reassigned later: don't track it
  else match rhs' with
    | .atom a =>
        if isImm mutated a then ((v, a) :: env, avail, .atom a) else (env, avail, .atom a)
    | .builtin op as =>
        -- CSE. NOTE: on a stack machine this can *grow* bytecode by extending a value's live
        -- range (more DUP/SWAP) more than recomputing a cheap pure op saves; a later
        -- rematerialization / cost model is expected to turn this net-positive (esp. gas-weighted
        -- on expensive reused ops). Kept on deliberately.
        if Op.isPure op && as.all (isImm mutated) then
          match avail.find? (fun p => p.1 == rhs') with
          | some (_, w) => ((v, .var w) :: env, avail, .atom (.var w))   -- reuse the earlier result
          | none        => (env, (rhs', v) :: avail, rhs')               -- memoize
        else (env, avail, rhs')
    | .call _ _ => (env, avail, rhs')

mutual
/-- Optimize a straight-line block, threading the value environment and available expressions.
Nested scopes receive the current maps but their changes are discarded on exit. -/
partial def vnBlock (mutated : List Ident) (env : VEnv) (avail : Avail) : Block → Block
  | [] => []
  | s :: rest =>
    match s with
    | .letD [v] rhs =>
        let rhs' := simplifyRhs (resolveRhs env rhs)
        let (env', avail', out) := recordLet mutated env avail v rhs'
        .letD [v] out :: vnBlock mutated env' avail' rest
    | .letD vars rhs =>
        .letD vars (resolveRhs env rhs) :: vnBlock mutated env avail rest
    | .assign vars rhs =>
        .assign vars (simplifyRhs (resolveRhs env rhs)) :: vnBlock mutated env avail rest
    | .effect rhs =>
        .effect (simplifyRhs (resolveRhs env rhs)) :: vnBlock mutated env avail rest
    | .cond c body =>
        .cond (resolveAtom env c) (vnBlock mutated env avail body) :: vnBlock mutated env avail rest
    | .switch c cases dflt =>
        .switch (resolveAtom env c)
          (cases.map (fun p => (p.1, vnBlock mutated env avail p.2)))
          (dflt.map (vnBlock mutated env avail)) :: vnBlock mutated env avail rest
    | .loop post body =>
        .loop (vnBlock mutated env avail post) (vnBlock mutated env avail body)
          :: vnBlock mutated env avail rest
    | .block body =>
        .block (vnBlock mutated env avail body) :: vnBlock mutated env avail rest
    | s => s :: vnBlock mutated env avail rest
end

/-- Value numbering over a block, given the program-wide mutated-variable set. -/
def valueNumberWith (mutated : List Ident) (b : Block) : Block := vnBlock mutated [] [] b

/-- Value numbering over a block (self-contained; assumes unique names). -/
def valueNumber (b : Block) : Block := vnBlock (mutatedVars b) [] [] b

/-- Value numbering over a whole program (assumes unique names — run `uniquify` first). Each
function body and `main` is a fresh scope; immutability is judged program-wide. -/
def valueNumberProgram (p : Program) : Program :=
  p.mapBodies (valueNumberWith (mutatedVarsProgram p))

end YulIR
