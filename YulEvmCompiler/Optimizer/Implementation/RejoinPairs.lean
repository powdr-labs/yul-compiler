import YulEvmCompiler.Optimizer.Spec.LocalPass
import YulEvmCompiler.Optimizer.Implementation.Frame
import YulEvmCompiler.Optimizer.Implementation.FunCongr
import YulEvmCompiler.Optimizer.Implementation.StorageForward
import YulSemantics.Dialect.EVM
set_option warningAsError false -- TEMP: measurement build, proof in progress
/-!
# YulEvmCompiler.Optimizer.Implementation.RejoinPairs

**Adjacent single-use expression rejoining** — the "expression rejoining" half
of issue #65's recommendation 3. After inlining and copy coalescing, the hot
loops are full of adjacent pairs

```yul
let x := and(w, 1)
let y := iszero(eq(x, 0))
```

whose intermediate `x` is consumed exactly once by the very next binder and
never again. The producer must be call-free: nesting a call back under an
expression would undo `HoistCalls`/`FreshenCalls` and hide the site from
`InlineCalls` (measured: the `fls` fixtures regressed when calls rejoined). Each such binder costs a live operand-stack slot and a `DUP`,
and the accumulated slots hold helper bodies above the `liveMax` inlining
gates. The rewrite merges the pair:

```yul
let y := iszero(eq(and(w, 1), 0))
```

Guards: the consumer's right-hand side is a **pure-total tree** (builtins
with `pureTotalArity`, leaves that are literals or bound variables) with
exactly one occurrence of `x`; `x` is dead afterwards; the producer `e` is
arbitrary (it may read or write state or even halt). Moving `e` from its own
statement into `x`'s leaf position only commutes it past pure, total,
state-independent leaf/op evaluations, so the evaluation is unchanged; the
depth story matches `CoalesceCopies` (a live slot is removed, and `e`'s reads
happen at the same depth one statement later with nothing declared between).

The layout-free guards on `e` and the consumer keep the transform the
identity on unresolved `dataoffset`/`datasize` regions, which makes it
commute syntactically with object-layout resolution.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### The consumer-tree classifier -/

mutual

/-- Count occurrences of `x` in a pure-total consumer tree whose other leaves
are literals or `bound` variables; `none` marks an unusable tree. -/
def rjTree (bound : List Ident) (x : Ident) : Expr Op → Option Nat
  | .lit _ => some 0
  | .var z =>
      if z = x then some 1
      else if bound.contains z then some 0 else none
  | .builtin op args =>
      if pureTotalArity op == some args.length then rjTreeArgs bound x args
      else none
  | .call _ _ => none

def rjTreeArgs (bound : List Ident) (x : Ident) : List (Expr Op) → Option Nat
  | [] => some 0
  | a :: rest => do
      let n ← rjTree bound x a
      let m ← rjTreeArgs bound x rest
      pure (n + m)

end

mutual

/-- Substitute `e` for the `.var x` leaves (the guard ensures there is
exactly one). -/
def rjSubst (x : Ident) (e : Expr Op) : Expr Op → Expr Op
  | .var z => if z = x then e else .var z
  | .builtin op args => .builtin op (rjSubstArgs x e args)
  | t => t

def rjSubstArgs (x : Ident) (e : Expr Op) : List (Expr Op) → List (Expr Op)
  | [] => []
  | a :: rest => rjSubst x e a :: rjSubstArgs x e rest

end

mutual

/-- Operand-stack pressure of evaluating an expression: the maximum number of
pending values while it evaluates (arguments right-to-left). Rejoining must
keep this bounded — a deep merged tree makes every local read from inside it
a deeper `DUP`, which pushed `PoolLiquidity` past the stack-layout rescue when
unbounded (measured). -/
def rjDepth : Expr Op → Nat
  | .lit _ => 1
  | .var _ => 1
  | .builtin _ args => max 1 (rjDepthArgs args)
  | .call _ args => max 1 (rjDepthArgs args)

/-- Arguments evaluate right-to-left, so while argument `a` evaluates, the
arguments after it in source order are already on the stack. -/
def rjDepthArgs : List (Expr Op) → Nat
  | [] => 0
  | a :: rest => max (rest.length + rjDepth a) (rjDepthArgs rest)

end

/-- The rejoin depth budget (measured: unbounded rejoining broke
`PoolLiquidity`'s stack-layout rescue). -/
def rjDepthLimit : Nat := 8

/-- The pair guard. -/
def rjPair (bound : List Ident) (x y : Ident) (e f : Expr Op)
    (rest : List (Stmt Op)) : Prop :=
  x ≠ y ∧ rjTree bound x f = some 1 ∧ stmtsMentions x rest = false ∧
    exprHasCall e = false ∧ rjDepth (rjSubst x e f) ≤ rjDepthLimit

instance (bound : List Ident) (x y : Ident) (e f : Expr Op)
    (rest : List (Stmt Op)) : Decidable (rjPair bound x y e f rest) := by
  unfold rjPair; infer_instance

/-! ### The transform -/

/-- One-level left-to-right rejoining; the merged binder is re-examined
against the next statement, so producer chains fold into one tree. -/
def rjPairs (bound : List Ident) : List (Stmt Op) → List (Stmt Op)
  | .letDecl [x] (some e) :: .letDecl [y] (some f) :: rest =>
      if rjPair bound x y e f rest then
        rjPairs bound (.letDecl [y] (some (rjSubst x e f)) :: rest)
      else
        .letDecl [x] (some e) ::
          rjPairs (x :: bound) (.letDecl [y] (some f) :: rest)
  | .letDecl xs v :: rest => .letDecl xs v :: rjPairs (xs ++ bound) rest
  | s :: rest => s :: rjPairs bound rest
  | [] => []
  termination_by ss => ss.length
  decreasing_by all_goals simp +arith

mutual

/-- Recurse into every sub-block, rejoining at each sequence level. Each
sequence starts from an **empty** bound set — only variables declared by
earlier `let`s of the same sequence count as safe sibling leaves, because
those are bound in every execution that reaches the pair, no matter how
ill-scoped the ambient environment is (the pointwise spec quantifies over
arbitrary environments). A `for` loop's `init` is left untouched. -/
def rjStmt : Stmt Op → Stmt Op
  | .block body => .block (rjPairs [] (rjStmts body))
  | .funDef n ps rs body => .funDef n ps rs (rjPairs [] (rjStmts body))
  | .cond c body => .cond c (rjPairs [] (rjStmts body))
  | .switch c cases dflt => .switch c (rjCases cases) (rjDflt dflt)
  | .forLoop init c post body =>
      .forLoop init c (rjPairs [] (rjStmts post)) (rjPairs [] (rjStmts body))
  | s => s

def rjStmts : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest => rjStmt s :: rjStmts rest

def rjCases : List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, b) :: rest => (l, rjPairs [] (rjStmts b)) :: rjCases rest

def rjDflt : Option (Block Op) → Option (Block Op)
  | none => none
  | some b => some (rjPairs [] (rjStmts b))

end

/-- Rejoin adjacent single-use pure pairs in a top-level block. The whole
block must be free of unresolved `dataoffset`/`datasize`: layout resolution
is then the identity on both the input and the output, which is what makes
the pass an object-path stage (the `StorageForward` recipe). -/
def rejoinPairsBlock (b : Block Op) : Block Op :=
  if storageLayoutFreeStmts b then rjPairs [] (rjStmts b) else b

/-- The verified pass (proof under construction). -/
def rejoinPairs : LocalPass D where
  run := rejoinPairsBlock
  sound := sorry

end YulEvmCompiler.Optimizer
