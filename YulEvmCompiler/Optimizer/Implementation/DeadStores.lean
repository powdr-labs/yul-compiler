import YulEvmCompiler.Optimizer.Implementation.DeadPure
import YulEvmCompiler.Optimizer.Implementation.StorageForwardResolve
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.DeadStores

**Dead-store elimination** — the write-side complement of `DeadPure`.

`DeadPure` removes a *binding* whose name is never mentioned again. The
dominant residue in the Yul that actually reaches the backend is the opposite
shape: a name that **is** mentioned again, but whose next occurrence is a
*write*. Two rewrites, on a name declared by an earlier `let` of the very same
statement sequence:

* **R1 (dead assignment)** `x := e` is deleted when `x` is dead from there on
  and `e` is total and state-preserving (`alwaysEval`);
* **R2 (dead initialiser)** `let x := e` becomes `let x` under the same
  conditions — the binder has to survive, because a later assignment refers to
  it. That is exactly the case `DeadPure` cannot take.

## Why this is where the gas is

`compileStmt` charges `compileAssigns`' `swap_k; pop` for every `.assign`, so a
dead `x := <lit>` is `push; swap; pop` = 7-8 gas and a dead `x := <var>` is
`dup; swap; pop` = 8 gas. Opcode attribution against solc (`traceSolidityGas`)
puts `POP` at 70-78% of the two largest Aave v4 gaps, and a backward liveness
over the Yul that actually compiles traces most of it to dead stores
**created by `stackLayoutBlock`**: `iterateStackLayout`'s slot reuse and
`StackV2`'s live-range splitting introduce `x := y` copies and shared slots,
and — because the layout pass runs *after* the whole optimizer pipeline, inside
`compileSource`'s `tryLayouts` — nothing runs behind them. 43 of the surviving
dead stores in `PositionStatusMap` sit inside its 10,000-trip loops.

## The deadness test, and why scope exit is free

`dsDead x rest` walks the *remainder of the current sequence* forward and
answers "is `x`'s value here unobservable?":

* a write to `x` (`.assign` targets, before any read) ⇒ dead;
* any read of `x` ⇒ not dead;
* end of the sequence, or a `break`/`continue`/`leave` ⇒ **dead**;
* a compound statement mentioning `x` at all ⇒ not dead (conservative: the
  branch may or may not run, so a write inside it cannot kill `x`).

The third clause is the reason this pass needs no escape-set bookkeeping. Both
rewrites fire only on a name in `owned` — declared by an earlier `letDecl` of
this same sequence — and such a name is removed by the sequence's `restore` at
*every* exit, normal or non-local. So a value that survives to the end of the
sequence is not observable, and the `EquivBlock` tier stays reachable for the
same reason it does in `DeadPure`: the difference is confined to bindings the
enclosing block erases.

Requiring `owned` also protects exactly the names that must be protected:
function returns and parameters, `for`-init declarations (loop-carried across
iterations), and anything bound in an ambient environment `EquivBlock`
quantifies over. None of them is declared by a `letDecl` of the sequence being
rewritten.

`for`-`init` sequences are left untouched, mirroring `DeadPure` and `DeadLits`:
their scope spans the whole loop, so the "dies at the end of the sequence"
argument does not apply to them.

Shadowing is treated as a hard stop (a re-declaration of `x` in `rest` makes
`x` not dead) rather than tracked, so the pass is correct without
`NormalForm.UniqueNames`; on normalized input the case never arises.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### The deadness test -/

/-- Is `x`'s current value unobservable over the rest of this sequence? See
the module docstring for the four clauses. -/
def dsDead (x : Ident) : List (Stmt Op) → Bool
  | [] => true
  | .assign ys e :: rest =>
      if exprMentions x e then false
      else if ys.contains x then true
      else dsDead x rest
  | .letDecl ys none :: rest =>
      if ys.contains x then false else dsDead x rest
  | .letDecl ys (some e) :: rest =>
      if exprMentions x e then false
      else if ys.contains x then false
      else dsDead x rest
  | .exprStmt e :: rest =>
      if exprMentions x e then false else dsDead x rest
  | .«break» :: _ => true
  | .«continue» :: _ => true
  | .leave :: _ => true
  | .block body :: rest =>
      if stmtsMentions x body then false else dsDead x rest
  | .cond c body :: rest =>
      if exprMentions x c || stmtsMentions x body then false else dsDead x rest
  | .switch c cases dflt :: rest =>
      if exprMentions x c || casesMentions x cases || optBlockMentions x dflt
      then false else dsDead x rest
  | .forLoop init c post body :: rest =>
      if stmtsMentions x init || exprMentions x c || stmtsMentions x post ||
        stmtsMentions x body then false else dsDead x rest
  | .funDef _ ps rs body :: rest =>
      if ps.contains x || rs.contains x || stmtsMentions x body then false
      else dsDead x rest

/-! ### The sequence sweep

`bound` is `DeadPure`'s provably-bound set, threaded along the sequence so
`alwaysEval` can certify variable leaves. `owned` is the set of names declared
by earlier `letDecl`s of *this* sequence — the only names either rewrite may
touch. Compound statements are passed through untouched here; `dsStmt` below
does the recursion. -/
def dsSweep (bound owned : List Ident) : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | .assign [x] e :: rest =>
      if owned.contains x && alwaysEval bound e && dsDead x rest then
        dsSweep bound owned rest
      else .assign [x] e :: dsSweep bound owned rest
  | .letDecl [x] (some e) :: rest =>
      if alwaysEval bound e && dsDead x rest then
        .letDecl [x] none :: dsSweep (x :: bound) (x :: owned) rest
      else .letDecl [x] (some e) :: dsSweep (x :: bound) (x :: owned) rest
  | .letDecl xs v :: rest =>
      .letDecl xs v :: dsSweep (xs ++ bound) (xs ++ owned) rest
  | s :: rest => s :: dsSweep bound owned rest

/-! ### Recursion into every sequence

Each nested sequence is first rewritten recursively, then swept from an
**empty** `owned` (only its own declarations are erased by its own `restore`).
A function body additionally restarts `bound` at the callee's parameters and
returns, which is exactly what the call rule's `callOk` environment binds. -/

mutual

/-- Rewrite a compound statement's sub-sequences, then sweep each of them. -/
def dsStmt (bound : List Ident) : Stmt Op → Stmt Op
  | .block body => .block (dsSweep bound [] (dsStmts bound body))
  | .funDef f ps rs body =>
      .funDef f ps rs (dsSweep (ps ++ rs) [] (dsStmts (ps ++ rs) body))
  | .cond c body => .cond c (dsSweep bound [] (dsStmts bound body))
  | .switch c cases dflt => .switch c (dsCases bound cases) (dsDflt bound dflt)
  | .forLoop init c post body =>
      .forLoop init c
        (dsSweep (blockDecls init ++ bound) [] (dsStmts (blockDecls init ++ bound) post))
        (dsSweep (blockDecls init ++ bound) [] (dsStmts (blockDecls init ++ bound) body))
  | s => s

/-- Rewrite each statement of a sequence. -/
def dsStmts (bound : List Ident) : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest => dsStmt bound s :: dsStmts bound rest

/-- Rewrite every `switch` case body. -/
def dsCases (bound : List Ident) : List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, b) :: rest => (l, dsSweep bound [] (dsStmts bound b)) :: dsCases bound rest

/-- Rewrite a `switch` default body. -/
def dsDflt (bound : List Ident) : Option (Block Op) → Option (Block Op)
  | none => none
  | some b => some (dsSweep bound [] (dsStmts bound b))

end

/-- One dead-store sweep over a whole block. -/
def dsOnce (b : Block Op) : Block Op :=
  dsSweep [] [] (dsStmts [] b)

/-- `dsDead` deliberately consults the **unrewritten** remainder: then a name
whose store this sweep drops was already unread on both sides, which keeps the
soundness relation to "the two environments differ only on names neither side
reads". The price is that store *chains* need more than one sweep — `y := f(x)`
keeps `x` alive until that store itself goes — so the pass is simply iterated,
which is sound by composition. Three rounds drain the chains measured on
`PositionStatusMap` and `TickMath`, and the fixed bound keeps the
quadratic-per-sequence scan off generated multi-megabyte objects. -/
def dsIterate : Nat → Block Op → Block Op
  | 0, b => b
  | n + 1, b => dsIterate n (dsOnce b)

/-- The iteration budget. -/
def dsRounds : Nat := 3

/-- Eliminate dead stores in a top-level block. The whole block must be free
of unresolved `dataoffset`/`datasize` so that layout resolution is the
identity on input and output alike; that is what makes this an object-path
stage (the `StorageForward`/`RejoinPairs` recipe). -/
def deadStoresBlock (b : Block Op) : Block Op :=
  if storageLayoutFreeStmts b then dsIterate dsRounds b else b

/-! ### Object trees -/

mutual
  /-- Eliminate dead stores in every code block of an object tree. -/
  def deadStoresObject : Object Op → Object Op
    | .mk name code subs segs =>
        .mk name (deadStoresBlock code) (deadStoresObjects subs) segs

  def deadStoresObjects : List (Object Op) → List (Object Op)
    | [] => []
    | o :: os => deadStoresObject o :: deadStoresObjects os
end

/-! ### Soundness -/

set_option warningAsError false in
/-- **Soundness — PROOF PENDING.** Both rewrites only change the value bound to
a name that (a) is declared by a `letDecl` of the sequence being rewritten, so
the sequence's `restore` erases it at every exit, and (b) is not read before
its next write or that exit. `alwaysEval` makes the dropped right-hand side
total and state-preserving, so no halt or `EvmState` change is lost. The proof
follows `DeadPure`'s `DcRel` architecture with the desync relation weakened
from "extra dead bindings" to "agrees except on names dead from here on". -/
theorem deadStoresBlock_equiv (b : Block Op) :
    EquivBlock D b (deadStoresBlock b) := by
  sorry

set_option warningAsError false in
/-- **Resolution congruence — PROOF PENDING.** `deadStoresBlock` guards on
`storageLayoutFreeStmts`, so on layout-free input resolution is the identity on
both sides and the congruence is the pass's own soundness; off the guard the
transform is the identity. -/
theorem resolveDeadStoresBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (deadStoresBlock b)) := by
  sorry

/-! ### The pass -/

/-- The **DeadStores pass**: dead assignment and dead initialiser elimination. -/
def deadStores : LocalPass D where
  run := deadStoresBlock
  sound := fun b => deadStoresBlock_equiv (calls := calls) (creates := creates) b

@[simp] theorem deadStores_run (b : Block Op) :
    (deadStores (calls := calls) (creates := creates)).run b = deadStoresBlock b := rfl

/-! ### Regression examples (checked at build time) -/

-- R1: a dead assignment to a sequence-local name goes; so does the last store
-- before the end of the sequence, whose value the `restore` discards.
example : dsSweep [] [] [.letDecl ["x"] (some (.lit (.number 1))),
    .assign ["x"] (.lit (.number 2)),
    .exprStmt (.builtin .sstore [.lit (.number 0), .var "x"]),
    .assign ["x"] (.lit (.number 3))]
  = [.letDecl ["x"] none,
     .assign ["x"] (.lit (.number 2)),
     .exprStmt (.builtin .sstore [.lit (.number 0), .var "x"])] := rfl

-- An assignment to a name this sequence does not declare stays: it may be
-- observable in the ambient environment `EquivBlock` quantifies over.
example : dsSweep [] [] [.assign ["x"] (.lit (.number 2)),
    .assign ["x"] (.lit (.number 3))]
  = [.assign ["x"] (.lit (.number 2)), .assign ["x"] (.lit (.number 3))] := rfl

-- An effectful right-hand side is never dropped, dead or not.
example : dsSweep [] [] [.letDecl ["x"] (some (.lit (.number 1))),
    .assign ["x"] (.builtin .mload [.lit (.number 0)]),
    .exprStmt (.builtin .sstore [.lit (.number 0), .var "x"])]
  = [.letDecl ["x"] none,
     .assign ["x"] (.builtin .mload [.lit (.number 0)]),
     .exprStmt (.builtin .sstore [.lit (.number 0), .var "x"])] := rfl

-- A conditional that mentions the name blocks the rewrite (the branch may not
-- run, so a write inside it cannot kill the outer value).
example : dsSweep [] [] [.letDecl ["x"] (some (.lit (.number 1))),
    .assign ["x"] (.lit (.number 2)),
    .cond (.lit (.number 1)) [.exprStmt (.builtin .sstore [.lit (.number 0), .var "x"])]]
  = [.letDecl ["x"] none,
     .assign ["x"] (.lit (.number 2)),
     .cond (.lit (.number 1)) [.exprStmt (.builtin .sstore [.lit (.number 0), .var "x"])]] := rfl

-- A `break` ends the sequence's scope, so the store before it is dead.
example : dsSweep [] [] [.letDecl ["x"] (some (.lit (.number 1))),
    .assign ["x"] (.lit (.number 2)), .«break»]
  = [.letDecl ["x"] none, .«break»] := rfl

-- Function returns are not `owned`, so a store to one survives.
example : dsStmt [] (.funDef "f" [] ["r"] [.assign ["r"] (.lit (.number 1))])
  = .funDef "f" [] ["r"] [.assign ["r"] (.lit (.number 1))] := rfl

-- A `for`-init declaration is loop-carried and not `owned` by the body.
example : dsStmt [] (.forLoop [.letDecl ["i"] (some (.lit (.number 0)))]
    (.lit (.number 1)) [] [.assign ["i"] (.lit (.number 2))])
  = .forLoop [.letDecl ["i"] (some (.lit (.number 0)))]
      (.lit (.number 1)) [] [.assign ["i"] (.lit (.number 2))] := rfl

-- The measured `stackLayout` residue: a body-local slot written twice with a
-- `break` test between, and an initialiser whose value is overwritten.
example : dsSweep ["v19"] []
    [.letDecl ["v20"] (some (.var "v19")),
     .assign ["v20"] (.var "v19"),
     .cond (.builtin .iszero [.var "v19"]) [.«break»],
     .assign ["v20"] (.var "v19"),
     .exprStmt (.builtin .sstore [.lit (.number 0), .var "v20"])]
  = [.letDecl ["v20"] none,
     .cond (.builtin .iszero [.var "v19"]) [.«break»],
     .assign ["v20"] (.var "v19"),
     .exprStmt (.builtin .sstore [.lit (.number 0), .var "v20"])] := rfl

end YulEvmCompiler.Optimizer
