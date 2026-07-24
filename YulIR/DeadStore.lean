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

/-- Live-set context threaded through the backward pass:
* `prot` — the enclosing function's return variables (observed at `leave`/end; never eliminated);
* `brk`  — variables live at the target of a `break` (i.e. *after* the enclosing loop);
* `cont` — variables live at the target of a `continue` (i.e. the enclosing loop's head).

`break`/`continue`/`leave` transfer control non-locally, so they must use these targets, not
the textually-following statement's live set. -/
structure LCtx where
  prot : List Ident
  brk  : List Ident
  cont : List Ident

mutual
/-- Transfer function for one statement: given the context and what's live *after* it, return the
rewritten statement (or `none` if removed) and what's live *before* it. -/
partial def liveStmt (c : LCtx) (liveOut : List Ident) : Stmt → (Option Stmt × List Ident)
  | .assign [x] rhs =>
      if Rhs.isPure rhs && ! liveOut.contains x && ! c.prot.contains x then
        (none, liveOut)                                        -- dead store: drop
      else
        (some (.assign [x] rhs), addLive (killLive liveOut [x]) rhs.vars)
  | .assign xs rhs =>
      (some (.assign xs rhs), addLive (killLive liveOut xs) rhs.vars)
  | .letD xs rhs =>
      (some (.letD xs rhs), addLive (killLive liveOut xs) rhs.vars)
  | .effect rhs =>
      (some (.effect rhs), addLive liveOut rhs.vars)
  | .cond cnd body =>
      let (body', liveBody) := liveBlock c liveOut body
      (some (.cond cnd body'), addLive (liveOut ++ liveBody) cnd.var?.toList)
  | .switch cnd cases dflt =>
      let cases' := cases.map (fun p => let (b', lb) := liveBlock c liveOut p.2; ((p.1, b'), lb))
      let dfltRes := dflt.map (fun b => liveBlock c liveOut b)
      let liveCases := cases'.flatMap (fun p => p.2)
      let liveDflt := (dfltRes.map (·.2)).getD []
      (some (.switch cnd (cases'.map (·.1)) (dfltRes.map (·.1))),
        addLive (liveOut ++ liveCases ++ liveDflt) cnd.var?.toList)
  | .loop post body =>
      -- `break` exits to after the loop (`liveOut`); `continue`/back-edge reach the loop head,
      -- conservatively everything read in the loop plus what's live after it.
      let headLive := liveOut ++ readVars post ++ readVars body
      let cInner : LCtx := { prot := c.prot, brk := liveOut, cont := headLive }
      let (post', _) := liveBlock cInner headLive post
      let (body', _) := liveBlock cInner headLive body
      (some (.loop post' body'), headLive)
  | .block body =>
      let (body', liveBody) := liveBlock c liveOut body
      (some (.block body'), liveBody)
  | .funDef n ps rs body =>
      -- a fresh scope: rets live at the end and protected; can't break/continue across it
      let (body', _) := liveBlock { prot := rs, brk := [], cont := [] } rs body
      (some (.funDef n ps rs body'), liveOut)         -- defining a function changes no caller var
  | .«break»    => (some .«break», c.brk)              -- successor is after the loop
  | .«continue» => (some .«continue», c.cont)          -- successor is the loop head
  | .leave      => (some .leave, c.prot)               -- successor is function end (rets observed)

/-- Backward liveness over a block: returns the rewritten block and its live-in set. -/
partial def liveBlock (c : LCtx) (liveOut : List Ident) : Block → (Block × List Ident)
  | []      => ([], liveOut)
  | s :: rest =>
      let (rest', liveMid) := liveBlock c liveOut rest
      let (s', liveIn) := liveStmt c liveMid s
      match s' with
      | some st => (st :: rest', liveIn)
      | none    => (rest', liveIn)
end

/-- Dead-store elimination over a whole program (top level observes no variables). -/
def deadStore (b : Block) : Block := (liveBlock { prot := [], brk := [], cont := [] } [] b).1

end YulIR
