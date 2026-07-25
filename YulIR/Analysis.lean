import YulIR.Ast

set_option warningAsError true
/-!
# YulIR.Analysis — small syntactic analyses over the IR

Helpers shared by the optimization passes:

* `Rhs.vars` — the variables an rhs *reads*;
* `mutatedVars` — variables that are ever an `assign` target (so, given unique names, the
  variables that are **not** single-assignment / immutable);
* `usedIdents` — every variable that is read or assigned (used by dead-code elimination);
* `allIdents` — every identifier occurring anywhere (used to pick collision-free fresh names).

All are conservative over-approximations computed structurally over the whole program (so,
under unique names, each name's classification is global and unambiguous).
-/

namespace YulIR

open YulSemantics (Ident Literal)

/-- The variable named by an atom, if any. -/
def Atom.var? : Atom → Option Ident
  | .var x => some x
  | .lit _ => none

/-- Variables read by an rhs (its operand variables). -/
def Rhs.vars : Rhs → List Ident
  | .atom a        => a.var?.toList
  | .builtin _ as  => as.filterMap Atom.var?
  | .call _ as     => as.filterMap Atom.var?

mutual
/-- Variables that appear as an `assign` target anywhere in a statement. -/
partial def stmtMutated : Stmt → List Ident
  | .assign vars _      => vars
  | .block b            => blockMutated b
  | .cond _ b           => blockMutated b
  | .switch _ cs d      => cs.flatMap (fun p => blockMutated p.2) ++ (d.map blockMutated).getD []
  | .loop post body     => blockMutated post ++ blockMutated body
  | _                   => []
partial def blockMutated : Block → List Ident
  | []      => []
  | s :: r  => stmtMutated s ++ blockMutated r
end

/-- Variables ever reassigned (⇒ not immutable), over the whole program. -/
def mutatedVars (b : Block) : List Ident := blockMutated b

mutual
/-- Identifiers read or assigned by a statement (targets counted, to keep DCE safe). -/
partial def stmtUsed : Stmt → List Ident
  | .letD _ rhs         => rhs.vars
  | .assign vars rhs    => vars ++ rhs.vars
  | .effect rhs         => rhs.vars
  | .cond c b           => c.var?.toList ++ blockUsed b
  | .switch c cs d      => c.var?.toList ++ cs.flatMap (fun p => blockUsed p.2) ++ (d.map blockUsed).getD []
  | .loop post body     => blockUsed post ++ blockUsed body
  | .block b            => blockUsed b
  | _                   => []
partial def blockUsed : Block → List Ident
  | []      => []
  | s :: r  => stmtUsed s ++ blockUsed r
end

/-- Identifiers read or assigned anywhere (dead bindings are those with none). -/
def usedIdents (b : Block) : List Ident := blockUsed b

mutual
/-- Every identifier occurring anywhere (binders, references, params/rets, function names). -/
partial def stmtIdents : Stmt → List Ident
  | .letD vars rhs      => vars ++ rhs.vars
  | .assign vars rhs    => vars ++ rhs.vars
  | .effect rhs         => rhs.vars
  | .cond c b           => c.var?.toList ++ blockIdents b
  | .switch c cs d      => c.var?.toList ++ cs.flatMap (fun p => blockIdents p.2) ++ (d.map blockIdents).getD []
  | .loop post body     => blockIdents post ++ blockIdents body
  | .block b            => blockIdents b
  | _                   => []
partial def blockIdents : Block → List Ident
  | []      => []
  | s :: r  => stmtIdents s ++ blockIdents r
end

/-- Every identifier in the program (used to choose fresh, collision-free names). -/
def allIdents (b : Block) : List Ident := blockIdents b

/-- Variables ever reassigned anywhere in a whole `Program` (all function bodies + `main`). -/
def mutatedVarsProgram (p : Program) : List Ident :=
  (p.funList.flatMap (fun (_, fn) => blockMutated fn.body)) ++ blockMutated p.main

/-- Every identifier occurring anywhere in a whole `Program` — function names, params, rets, and
all body/main identifiers (used to pick program-wide collision-free fresh names). -/
def allIdentsProgram (p : Program) : List Ident :=
  (p.funList.flatMap (fun (n, fn) => n :: (fn.params ++ fn.rets ++ blockIdents fn.body)))
    ++ blockIdents p.main

mutual
/-- Variables *read* by a statement (its rhs/condition operands only — not assign targets or
binders). This is the liveness "gen" set. -/
partial def stmtReads : Stmt → List Ident
  | .letD _ rhs         => rhs.vars
  | .assign _ rhs       => rhs.vars
  | .effect rhs         => rhs.vars
  | .cond c b           => c.var?.toList ++ blockReads b
  | .switch c cs d      => c.var?.toList ++ cs.flatMap (fun p => blockReads p.2) ++ (d.map blockReads).getD []
  | .loop post body     => blockReads post ++ blockReads body
  | .block b            => blockReads b
  | _                   => []
partial def blockReads : Block → List Ident
  | []      => []
  | s :: r  => stmtReads s ++ blockReads r
end

/-- Variables read anywhere in a block (liveness gen set). -/
def readVars (b : Block) : List Ident := blockReads b

end YulIR
