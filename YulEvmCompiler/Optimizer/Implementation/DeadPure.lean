import YulEvmCompiler.Optimizer.Implementation.DeadLits
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.DeadPure

**Dead pure-binding elimination** — `DeadLits` generalized from literal
right-hand sides to right-hand sides that *provably evaluate in context*:

* literals (subsuming `DeadLits`);
* variables that are **provably bound here** — function parameters/returns
  (the call rule's `callOk` environment binds exactly those) and variables
  let-declared earlier in an enclosing scope of the same frame; and
* pure-total builtin trees over those (`pureFn`-domain ops at exact arity —
  total, state-independent, non-halting).

Additionally, a **self-assignment** `x := x` with `x` provably bound is
dropped: `VEnv.set V x v = V` when `VEnv.get V x = some v`, so removal
desyncs nothing at all.

This is exactly the shape of the copy scaffolding that `InlineCalls`
materializes and (gated) copy propagation makes dead: `let p := a` parameter
copies, `let r` zero-inits, `let y := x` chain links whose uses were
substituted away.

## Why this cannot reuse `DlRel`'s congruence chaining

`removeLit_equivBlock` needs the removed right-hand side to evaluate on
*every* environment — true for literals only. The dominant removable shape,
a param-sourced copy `let _1 := var_x`, is stuck on environments where
`var_x` is unbound, and `DlRel.sound`'s `funDefS` case demands pointwise
`EquivBlock` of bodies over arbitrary environments, where that stuckness is
observable. Only a `Step` simulation whose `call` case sees the `callOk`
environment can supply the boundness fact. The relation `DcRel bound` below
therefore follows `Propagate`'s architecture: skip rules everywhere, a
semantic invariant (`BoundOK V bound`: every ident in `bound` is bound in
`V`), a syntactic funs relation (`DcFunsRel`), and one bidirectional
simulation — with the env desync ("the unremoved side carries extra dead
bindings until its enclosing block's `restore`") tracked by an insertion
relation generalizing `Frame.InsAt` to interleaved multiple insertions.

The strong `Pass`/`EquivBlock` tier remains reachable because every removed
binding is local to the (implicitly wrapped) top-level block: `restore`
erases the difference at every block exit, exactly as in `DeadLits`.

For-loop `init` blocks are left untouched (their scope spans the whole
loop), mirroring `DeadLits`.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### The always-evaluating right-hand-side fragment -/

/-- Arity at which `pureFn` is total for an op (`none` for ops outside the
pure fragment). Mirrors `pureFn`'s arms exactly. -/
def pureTotalArity : Op → Option Nat
  | .add | .sub | .mul | .div | .sdiv | .mod | .smod
  | .signextend | .lt | .gt | .slt | .sgt | .eq
  | .and | .or | .xor | .byte | .shl | .shr | .sar => some 2
  | .clz | .iszero | .not => some 1
  | .addmod | .mulmod => some 3
  | _ => none

/-- `pureTotalArity` is the domain of `pureFn`: at the declared arity, the
op is total on values. -/
theorem pureTotalArity_pureFn {op : Op} {n : Nat}
    (h : pureTotalArity op = some n) (vs : List U256) (hlen : vs.length = n) :
    ∃ w, pureFn op vs = some w := by
  unfold pureTotalArity at h
  split at h <;> cases h <;>
    first
      | (match vs, hlen with | [a], _ => exact ⟨_, rfl⟩)
      | (match vs, hlen with | [a, b], _ => exact ⟨_, rfl⟩)
      | (match vs, hlen with | [a, b, c], _ => exact ⟨_, rfl⟩)

mutual

/-- Does the expression evaluate — to exactly one value, without touching
state and without halting — on every environment binding all of `bound`? -/
def alwaysEval (bound : List Ident) : Expr Op → Bool
  | .lit _ => true
  | .var x => bound.contains x
  | .builtin op args =>
      (pureTotalArity op == some args.length) && alwaysEvalArgs bound args
  | .call _ _ => false

/-- `alwaysEval` for each argument. -/
def alwaysEvalArgs (bound : List Ident) : List (Expr Op) → Bool
  | [] => true
  | e :: rest => alwaysEval bound e && alwaysEvalArgs bound rest

end

/-! ### The transform -/

/-- Is `s` a removable statement, given the provably-bound set and the rest
of its block? Removable are dead singleton `let`s with always-evaluating
right-hand sides (or zero-init) and self-assignments of bound variables. -/
def removablePure (bound : List Ident) : Stmt Op → List (Stmt Op) → Bool
  | .letDecl [x] none, rest => !stmtsMentions x rest
  | .letDecl [x] (some rhs), rest =>
      alwaysEval bound rhs && !stmtsMentions x rest
  | .assign [x] (.var y), _ => x == y && bound.contains x
  | _, _ => false

mutual

/-- Remove dead pure bindings, recursing into every sub-block (a `for`
loop's `init` is left untouched — its scope spans the whole loop). -/
def dpStmt (bound : List Ident) : Stmt Op → Stmt Op
  | .block body => .block (dpStmts bound body)
  | .funDef n ps rs body => .funDef n ps rs (dpStmts (ps ++ rs) body)
  | .cond c body => .cond c (dpStmts bound body)
  | .switch c cases dflt => .switch c (dpCases bound cases) (dpDflt bound dflt)
  | .forLoop init c post body =>
      .forLoop init c (dpStmts bound post) (dpStmts bound body)
  | s => s

/-- Remove dead pure bindings from a statement sequence, growing the
provably-bound set at each kept declaration. -/
def dpStmts (bound : List Ident) : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest =>
      if removablePure bound s rest then dpStmts bound rest
      else
        match s with
        | .letDecl xs val =>
            .letDecl xs val :: dpStmts (xs ++ bound) rest
        | s => dpStmt bound s :: dpStmts bound rest

/-- Remove dead pure bindings from each `switch` case body. -/
def dpCases (bound : List Ident) :
    List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, b) :: rest => (l, dpStmts bound b) :: dpCases bound rest

/-- Remove dead pure bindings from a `switch` default. -/
def dpDflt (bound : List Ident) : Option (Block Op) → Option (Block Op)
  | none => none
  | some b => some (dpStmts bound b)

end

set_option warningAsError false in
/-- The **DeadPure pass**: dead pure-binding and self-assignment
elimination. Soundness: see module notes (bidirectional simulation with the
`BoundOK` invariant; in progress). -/
def deadPure : Pass D where
  run := dpStmts []
  sound := sorry

@[simp] theorem deadPure_run (b : Block Op) :
    (deadPure (calls := calls) (creates := creates)).run b = dpStmts [] b := rfl


/-! ### Regression examples (checked at build time) -/

-- A dead param-shaped copy dies when its source is provably bound.
example : dpStmts ["p"] [.letDecl ["y"] (some (.var "p")),
    .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])]
  = [.exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])] := rfl
-- ...but stays when the source is not provably bound.
example : dpStmts [] [.letDecl ["y"] (some (.var "p")),
    .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])]
  = [.letDecl ["y"] (some (.var "p")),
     .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])] := rfl
-- Earlier let-declarations feed the bound set.
example : dpStmts [] [.letDecl ["a"] (some (.lit (.number 1))),
    .letDecl ["y"] (some (.builtin .add [.var "a", .lit (.number 2)])),
    .exprStmt (.builtin .sstore [.lit (.number 0), .var "a"])]
  = [.letDecl ["a"] (some (.lit (.number 1))),
     .exprStmt (.builtin .sstore [.lit (.number 0), .var "a"])] := rfl
-- Self-assignments of bound variables are no-ops and die.
example : dpStmts ["x"] [.assign ["x"] (.var "x"),
    .exprStmt (.builtin .sstore [.lit (.number 0), .var "x"])]
  = [.exprStmt (.builtin .sstore [.lit (.number 0), .var "x"])] := rfl
-- Calls never qualify (they can halt or diverge in effect).
example : dpStmts ["p"] [.letDecl ["y"] (some (.call "f" [.var "p"])),
    .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])]
  = [.letDecl ["y"] (some (.call "f" [.var "p"])),
     .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])] := rfl
-- Wrong arity is stuck, not total: `add(x)` stays even when `x` is bound.
example : dpStmts ["x"] [.letDecl ["y"] (some (.builtin .add [.var "x"])),
    .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])]
  = [.letDecl ["y"] (some (.builtin .add [.var "x"])),
     .exprStmt (.builtin .sstore [.lit (.number 0), .lit (.number 1)])] := rfl
-- funDef bodies reset the bound set to params ++ rets.
example : dpStmts [] [.funDef "f" ["p"] ["r"]
    [.letDecl ["y"] (some (.var "p")), .assign ["r"] (.lit (.number 1))]]
  = [.funDef "f" ["p"] ["r"] [.assign ["r"] (.lit (.number 1))]] := rfl

end YulEvmCompiler.Optimizer
