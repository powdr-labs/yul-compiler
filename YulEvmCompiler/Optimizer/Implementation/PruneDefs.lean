import YulEvmCompiler.Optimizer.Implementation.FreshenCalls
/-!
# Unreachable function-definition pruning

Full normalization hoists every function definition to the root, and the
backend emits each definition as its own `PUSH32 skip; JUMP; …; JUMPDEST`
island — roughly 12 gas per retained definition on *every* call into the
contract, plus the dead bytecode.  After six inlining rounds the artifacts
retain nearly every definition while calling almost none of them
(`PositionStatusMap` 150 defs vs solc's 19, TickMath 177 vs 2, SafeCast ~68
vs 0); for the small Uniswap library rows the dead-island tax is over half
the measured row.

This pass computes the transitive call-reachability of root-level function
definitions from the root's non-definition statements and drops the unreached
definitions.  Yul has no first-class functions, so a definition is referenced
only by `.call` expressions; a root definition whose name appears in no
reachable call position can never execute.

Only root-level definitions are pruned (post-normalization there are no
others); nested definitions are left alone, and their bodies' calls keep
their callees alive.

Soundness (deferred to `PruneDefsSound.lean`): a hoist-shrinking congruence —
execution under a function environment extended with entries whose names
occur in no call position of the executing program (nor of any reachable
body) is pointwise equivalent to execution without them; the `funDef`
statements themselves are execution no-ops.  Resolution closure is syntactic
(layout resolution rewrites `dataoffset`/`datasize` builtins to literals and
never creates or renames `.call`s).
-/

namespace YulEvmCompiler.Optimizer.PruneDefs

open YulSemantics
open YulSemantics.EVM

/-! ### Call-name collection -/

mutual
def callNamesExpr : Expr Op → List Ident
  | .lit _ | .var _ => []
  | .builtin _ args => callNamesArgs args
  | .call f args => f :: callNamesArgs args

def callNamesArgs : List (Expr Op) → List Ident
  | [] => []
  | e :: rest => callNamesExpr e ++ callNamesArgs rest
end

mutual
/-- Call names in a statement, including nested definitions' bodies (a nested
definition is kept, so its calls keep their callees alive). -/
def callNamesStmt : Stmt Op → List Ident
  | .block body => callNamesStmts body
  | .funDef _ _ _ body => callNamesStmts body
  | .letDecl _ none => []
  | .letDecl _ (some e) => callNamesExpr e
  | .assign _ e => callNamesExpr e
  | .exprStmt e => callNamesExpr e
  | .cond e body => callNamesExpr e ++ callNamesStmts body
  | .switch e cases dflt =>
      callNamesExpr e ++ callNamesCases cases ++ callNamesDflt dflt
  | .forLoop init e post body =>
      callNamesStmts init ++ callNamesExpr e ++ callNamesStmts post ++
        callNamesStmts body
  | _ => []

def callNamesStmts : List (Stmt Op) → List Ident
  | [] => []
  | s :: rest => callNamesStmt s ++ callNamesStmts rest

def callNamesCases : List (Literal × Block Op) → List Ident
  | [] => []
  | (_, b) :: rest => callNamesStmts b ++ callNamesCases rest

def callNamesDflt : Option (Block Op) → List Ident
  | none => []
  | some b => callNamesStmts b
end

/-! ### Reachability -/

/-- The root-level definitions, as `(name, body call names)`. -/
def rootDefs : List (Stmt Op) → List (Ident × List Ident)
  | [] => []
  | .funDef n _ _ body :: rest => (n, callNamesStmts body) :: rootDefs rest
  | _ :: rest => rootDefs rest

/-- Call names of the root's non-definition statements (the entry code). -/
def rootCalls : List (Stmt Op) → List Ident
  | [] => []
  | .funDef _ _ _ _ :: rest => rootCalls rest
  | s :: rest => callNamesStmt s ++ rootCalls rest

/-- Worklist closure: repeatedly add the call names of live definitions'
bodies. Fuel `defs.length + 1` suffices — each productive round marks at
least one further definition live. On (impossible) fuel exhaustion every
definition is declared live, so the closure property holds unconditionally
and pruning degrades to the identity rather than to unsoundness. -/
def reachNew (defs : List (Ident × List Ident)) (live : List Ident) :
    List Ident :=
  ((defs.filter (fun d => live.contains d.1)).flatMap (·.2)).filter
    (fun n => !live.contains n && defs.any (fun d => d.1 = n))

def reachFuel (defs : List (Ident × List Ident)) :
    Nat → List Ident → List Ident
  | 0, live => defs.map (·.1) ++ live
  | fuel + 1, live =>
      match reachNew defs live with
      | [] => live
      | new => reachFuel defs fuel (live ++ new.eraseDups)

/-- The live definition names of a root sequence. -/
def liveDefs (body : List (Stmt Op)) : List Ident :=
  let defs := rootDefs body
  reachFuel defs (defs.length + 1) (rootCalls body).eraseDups

/-- Drop root-level definitions not in `live`. -/
def pruneRoot (live : List Ident) : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | .funDef n ps rs b :: rest =>
      if live.contains n then .funDef n ps rs b :: pruneRoot live rest
      else pruneRoot live rest
  | s :: rest => s :: pruneRoot live rest

/-- The public transform: reachability from the root's entry code, then prune
root-level definitions. -/
def pruneDefsBlock (body : Block Op) : Block Op :=
  pruneRoot (liveDefs body) body

end YulEvmCompiler.Optimizer.PruneDefs
