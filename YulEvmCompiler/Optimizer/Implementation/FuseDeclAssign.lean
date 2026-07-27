import YulEvmCompiler.Optimizer.Implementation.DeadPure
import YulEvmCompiler.Optimizer.Implementation.FreshenCalls
/-!
# Declare-then-assign fusion (binding sinking)

The statement inliner's zero-initialized results and `Flatten`'s splicing
leave the dominant residue shape

```yul
let x            // zero-init
...              // statements that never mention x
x := e           // first mention of x, same level
```

plus the adjacent literal variant `let x := 0; x := e`.  Each such pair pays a
zero push at the declaration and keeps a live stack slot across the
intervening statements; worse, the *assign*-form chains hide from
`CoalesceCopies` and `RejoinPairs`, which pace the whole cleanup cascade on
`let`-form pairs.

Two rewrites, one left-to-right sweep per sequence:

* **Sink**: an uninitialized singleton `let x` whose first mention in the
  remainder of its sequence is a same-level singleton `x := e` is deleted, and
  that assignment becomes `let x := e`.  Later statements read the same value
  from the same binder; the intervening statements never mention `x`.
* **Fuse**: `let x := <literal>` immediately followed by `x := e` with `x` not
  read by `e` becomes `let x := e`.

Soundness (deferred): both rewrites are the `CoalesceCopies`/`InsAt` frame
argument — between the old and new binding points the source carries one extra
dead binding (`x ↦ 0` or the literal) through a mention-free region, and both
sides bind `x` to `e`'s value afterwards; the enclosing block's `restore`
erases the difference, halts included.  If `e` halts, the target leaves `x`
unbound where the source bound it — the same one-insertion asymmetry those
passes already transport.
-/

namespace YulEvmCompiler.Optimizer.FuseDeclAssign

open YulSemantics
open YulSemantics.EVM

/-- Does the statement mention `x` at all (read, write, or declare, at any
depth — declarations count so that shadowing regions block the sink)? -/
def mentionsStmt (x : Ident) (s : Stmt Op) : Bool :=
  (YulEvmCompiler.Optimizer.stmtIdents s).contains x

/-- Walk the remainder of the sequence looking for the first mention of `x`.
If it is a same-level singleton assignment `x := e`, return the sequence with
that assignment converted to `let x := e`. -/
def sink (x : Ident) : List (Stmt Op) → Option (List (Stmt Op))
  | [] => none
  | .assign [y] e :: rest =>
      if y = x then
        if (YulEvmCompiler.Optimizer.exprIdents e).contains x then none
        else some (.letDecl [x] (some e) :: rest)
      else if mentionsStmt x (.assign [y] e) then none
      else (sink x rest).map (.assign [y] e :: ·)
  | s :: rest =>
      if mentionsStmt x s then none
      else (sink x rest).map (s :: ·)

/-- The sequence-level sweep (elements already processed recursively).
`sink` preserves list length, so `fuel := length + 1` always suffices; on
(impossible) fuel exhaustion the remainder is emitted unchanged. -/
def fuseSeqFuel : Nat → List (Stmt Op) → List (Stmt Op)
  | 0, ss => ss
  | _ + 1, [] => []
  | fuel + 1, .letDecl [x] none :: rest =>
      (match sink x rest with
       | some rest' => fuseSeqFuel fuel rest'
       | none => .letDecl [x] none :: fuseSeqFuel fuel rest)
  | fuel + 1, .letDecl [x] (some (.lit l)) :: .assign [y] e :: rest =>
      if x = y && !(YulEvmCompiler.Optimizer.exprIdents e).contains x then
        fuseSeqFuel fuel (.letDecl [x] (some e) :: rest)
      else
        .letDecl [x] (some (.lit l)) :: fuseSeqFuel fuel (.assign [y] e :: rest)
  | fuel + 1, s :: rest => s :: fuseSeqFuel fuel rest

def fuseSeq (ss : List (Stmt Op)) : List (Stmt Op) :=
  fuseSeqFuel (ss.length + 1) ss

mutual

def fdStmt : Stmt Op → Stmt Op
  | .block body => .block (fdStmts body)
  | .funDef n ps rs body => .funDef n ps rs (fdStmts body)
  | .cond c body => .cond c (fdStmts body)
  | .switch c cases dflt => .switch c (fdCases cases) (fdDflt dflt)
  | .forLoop init c post body =>
      .forLoop init c (fdStmts post) (fdStmts body)
  | s => s

def fdStmts (body : List (Stmt Op)) : List (Stmt Op) :=
  fuseSeq (fdEach body)

def fdEach : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest => fdStmt s :: fdEach rest

def fdCases : List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, b) :: rest => (l, fdStmts b) :: fdCases rest

def fdDflt : Option (Block Op) → Option (Block Op)
  | none => none
  | some b => some (fdStmts b)

end

def fuseDeclAssignBlock (body : Block Op) : Block Op := fdStmts body

end YulEvmCompiler.Optimizer.FuseDeclAssign
