import YulIR.Analysis
import YulIR.Effects

/-!
# YulIR.DeadStore — dead-store (unused-assignment) elimination

A backward liveness pass that removes `x := <pure rhs>` when `x`'s value is never observed
afterwards (not read before its next reassignment / the end of its scope). Removing it is
sound: `x` is dead and the rhs is pure, so nothing observable changes. Impure rhs (`sload`,
calls, …) and multi-result assigns are kept.

Liveness is computed structurally, backward:

* straight-line and `if`/`switch` are handled precisely (conditionals never *kill*, since the
  branch may not run — we union the branch's live-in with the fall-through live-out);
* **loops** are handled conservatively: the body/post are analysed with everything read
  anywhere in the loop forced live, which also makes `break`/`continue` sound without tracking
  their non-local successors (over-approximating liveness only ever *keeps* stores);
* **function returns**: a function body is analysed with its return variables live at the end,
  and return variables are never eliminated (`leave` observes them).

Only ever removing a *provably dead* pure store, so any imprecision costs an opportunity, never
correctness.
-/

namespace YulIR

open YulSemantics (Ident Literal)

/-- Add variables to a live set. -/
def addLive (s xs : List Ident) : List Ident := xs ++ s

/-- Remove variables from a live set. -/
def killLive (s xs : List Ident) : List Ident := s.filter (fun v => ! xs.contains v)

mutual
/-- Transfer function for one statement: given what's live *after* it (and the enclosing
function's protected return vars), return the rewritten statement (or `none` if removed) and
what's live *before* it. -/
partial def liveStmt (prot : List Ident) (liveOut : List Ident) : Stmt → (Option Stmt × List Ident)
  | .assign [x] rhs =>
      if Rhs.isPure rhs && ! liveOut.contains x && ! prot.contains x then
        (none, liveOut)                                        -- dead store: drop
      else
        (some (.assign [x] rhs), addLive (killLive liveOut [x]) rhs.vars)
  | .assign xs rhs =>
      (some (.assign xs rhs), addLive (killLive liveOut xs) rhs.vars)
  | .letD xs rhs =>
      (some (.letD xs rhs), addLive (killLive liveOut xs) rhs.vars)
  | .effect rhs =>
      (some (.effect rhs), addLive liveOut rhs.vars)
  | .cond c body =>
      let (body', liveBody) := liveBlock prot liveOut body
      (some (.cond c body'), addLive (liveOut ++ liveBody) c.var?.toList)
  | .switch c cases dflt =>
      let cases' := cases.map (fun p => let (b', lb) := liveBlock prot liveOut p.2; ((p.1, b'), lb))
      let dfltRes := dflt.map (fun b => liveBlock prot liveOut b)
      let liveCases := cases'.flatMap (fun p => p.2)
      let liveDflt := (dfltRes.map (·.2)).getD []
      (some (.switch c (cases'.map (·.1)) (dfltRes.map (·.1))),
        addLive (liveOut ++ liveCases ++ liveDflt) c.var?.toList)
  | .loop post body =>
      let liveOut' := liveOut ++ readVars post ++ readVars body   -- force loop reads live
      let (post', _) := liveBlock prot liveOut' post
      let (body', _) := liveBlock prot liveOut' body
      (some (.loop post' body'), liveOut')
  | .block body =>
      let (body', liveBody) := liveBlock prot liveOut body
      (some (.block body'), liveBody)
  | .funDef n ps rs body =>
      let (body', _) := liveBlock rs rs body        -- rets live at end and protected
      (some (.funDef n ps rs body'), liveOut)         -- defining a function changes no caller var
  | .leave =>
      (some .leave, addLive liveOut prot)             -- `leave` observes the return vars
  | s => (some s, liveOut)

/-- Backward liveness over a block: returns the rewritten block and its live-in set. -/
partial def liveBlock (prot : List Ident) (liveOut : List Ident) : Block → (Block × List Ident)
  | []      => ([], liveOut)
  | s :: rest =>
      let (rest', liveMid) := liveBlock prot liveOut rest
      let (s', liveIn) := liveStmt prot liveMid s
      match s' with
      | some st => (st :: rest', liveIn)
      | none    => (rest', liveIn)
end

/-- Dead-store elimination over a whole program (top level observes no variables). -/
def deadStore (b : Block) : Block := (liveBlock [] [] b).1

end YulIR
