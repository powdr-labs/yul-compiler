import YulIR.Analysis
import YulIR.Effects

set_option warningAsError true
/-!
# YulIR.DeadCode — dead pure-binding elimination

Removes `let v := <pure rhs>` when `v` is never read or assigned anywhere in the program.
Under unique names this is a sound global check: a pure rhs has no observable effect, so if its
result is unused the binding can go. Impure bindings (`sload`, `mload`, keccak, calls, …) and
multi-result calls are always kept. Iterated to a fixpoint (removing one binding can make its
operands dead), bounded to avoid any pathological non-termination.

This is what makes value numbering pay off: the copies (`let v := w`) and folded temporaries it
leaves behind become dead once their uses were rewritten, and are collected here.
-/

namespace YulIR

open YulSemantics (Ident Literal)

/-- Is this statement dead — a pure binding whose result is unused, or a pure statement
(e.g. `pop(x)`) that has no observable effect at all? -/
def isDeadLet (used : List Ident) : Stmt → Bool
  | .letD [v] rhs => Rhs.isPure rhs && ! used.contains v
  | .effect rhs   => Rhs.isPure rhs          -- a pure op evaluated for effect does nothing
  | _             => false

mutual
/-- Drop dead pure bindings in a block, given the program's used-identifier set. -/
partial def dceBlock (used : List Ident) : Block → Block
  | [] => []
  | s :: rest =>
    if isDeadLet used s then dceBlock used rest
    else dceStmt used s :: dceBlock used rest

/-- Recurse into a statement's sub-blocks. -/
partial def dceStmt (used : List Ident) : Stmt → Stmt
  | .cond c b          => .cond c (dceBlock used b)
  | .switch c cs d     => .switch c (cs.map (fun p => (p.1, dceBlock used p.2))) (d.map (dceBlock used))
  | .loop post body    => .loop (dceBlock used post) (dceBlock used body)
  | s                  => s
end

/-- One dead-code pass: recompute the used set, then drop dead pure bindings. -/
def dcePass (b : Block) : Block := dceBlock (usedIdents b) b

mutual
/-- Total (recursive) statement count, for fixpoint detection. -/
partial def stmtCount : Stmt → Nat
  | .cond _ b         => 1 + blockCount b
  | .switch _ cs d    => 1 + cs.foldl (fun a p => a + blockCount p.2) 0 + (d.map blockCount).getD 0
  | .loop post body   => 1 + blockCount post + blockCount body
  | _                 => 1
partial def blockCount : Block → Nat
  | []     => 0
  | s :: r => stmtCount s + blockCount r
end

/-- Iterate `dcePass` to a fixpoint (bounded). -/
partial def dceFuel : Nat → Block → Block
  | 0, b => b
  | n + 1, b =>
    let b' := dcePass b
    if blockCount b' == blockCount b then b' else dceFuel n b'

/-- Dead pure-binding elimination to a fixpoint. -/
def deadCode (b : Block) : Block := dceFuel 8 b

/-- Dead pure-binding elimination over a whole program: every function body and `main`. -/
def deadCodeProgram (p : Program) : Program := p.mapBodies deadCode

end YulIR
