import YulEvmCompiler.Optimizer.Implementation.ReuseValues
set_option warningAsError true
/-!
# Literal-slot memory value forwarding

Solc's unoptimized IR — and, far more heavily, our own `MemorySpill` pass —
round-trip locals through fixed literal memory slots: `mstore(k, v)` followed
by later `mload(k)` reads, and memory-to-memory copies `mstore(d, mload(s))`.
`ReuseValues` forwards only *whole-rhs* literal loads (`let x := mload(k)`); the
overwhelming majority of the residual loads are **nested** inside pure
arithmetic (`shr(128, mul(mload(224), c))`, `add(mload(448), 3)`) or inside an
`mstore` value (`mstore(288, mload(256))`), which nothing rewrites.

This pass forwards the value known to live at a literal slot into every nested
`mload` occurrence, **evaluation-order aware**: `mfE` threads a per-slot cache
through the left-to-right evaluation of each expression, forwarding an
`mload(k)` leaf to the cell value while the cell is live, and clearing the cache
the instant a subexpression may write memory (the `call`/`create` family, a
stray `mstore`/`mstore8`/`*copy`). Reads (`mload`/`sload`/`keccak256`/`log`/
`sstore`/`tstore`) do not clear cells. So each rewritten `mload` reads exactly
the word the establishing `mstore` wrote, at that evaluation point.

It never deletes a store (memory content is preserved exactly — the
differential harness compares final nonzero memory). Its value is that the
forwarded loads become plain stack values, and `DeadPure`/`CoalesceCopies`/the
smart layout then drop the load, its address push, and the surrounding shuffle.

Facts:
* `mstore(<lit k>, v)` records `k ↦ classify(rewrite v)` (a `lit`/`var`/
  `add(var,lit)`), first killing every overlapping cell; if `v` is a call the
  cache is cleared first, then `k` re-established.
* `let x := mload(<lit k>)` with no live cell at `k` records `k ↦ x` (so a
  later `mload(k)` with no intervening write forwards to `x` — free-pointer
  churn).
* Assignments kill the cells whose value mentions the target. Control-flow
  joins clear the cache (a conditional whose body cannot complete normally may
  retain the post-condition cache, because only the unselected branch reaches
  the tail); function/loop bodies are independent regions. This mirrors
  `StorageForward`/`ReuseValues`.

Soundness proof (EquivBlock-style, as for `StorageForward`/`ReuseValues`) and
proper pipeline wiring are **not yet done**: the transform is currently applied
in `compileSource` as an experimental step (forward, then re-optimize). See the
task report for the proof plan (reuse `ReuseValuesSound`'s `RvOk` cell-validity
machinery; the new obligation is an expression-tree Step simulation for `mfE`
that threads cell validity through evaluation and every `Op`, clearing at
memory writers).
-/

namespace YulEvmCompiler.Optimizer.MemoryForward

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer (StorageVal classifyStorageVal blockDecls
  stmtsNoNormal storageLayoutFreeStmts cacheKill)
open YulEvmCompiler.Optimizer.ReuseValues (mloadLit mstoreLit cellsOverlap)

/-- Number-literal memory-word key and its known cheap value. -/
abbrev MemCache := List (Nat × StorageVal)

def memLookup (k : Nat) (C : MemCache) : Option StorageVal :=
  (C.find? (fun p => p.1 = k)).map (·.2)

/-- Drop every cell whose 32-byte word overlaps `[k, k+32)`. -/
def memKillOverlap (k : Nat) (C : MemCache) : MemCache :=
  C.filter (fun p => !cellsOverlap p.1 k)

/-- Record a cheap value at literal word `k`, killing overlapping cells. -/
def memPut (k : Nat) (v : StorageVal) (C : MemCache) : MemCache :=
  (k, v) :: memKillOverlap k C

/-! ### Nested-load rewriting, evaluation-order aware

`mfE` rewrites an expression while **threading** the cache through the
left-to-right evaluation order. A literal `mload(k)` leaf with a live cell fact
is forwarded to the cell value; a subexpression that may write memory (the
`call`/`create` family, or a stray copy/`mstore` builtin) clears the cache for
everything evaluated after it, so no fact is used past a write. Reads
(`mload`/`sload`/`keccak256`/`log`/`sstore`/`tstore`) do not clear cells. -/

/-- Value-returning (or statement-form) built-ins that write EVM memory, after
which cell facts no longer describe current memory. -/
def opWritesMemory : Op → Bool
  | .mstore | .mstore8 | .mcopy | .calldatacopy | .returndatacopy
  | .codecopy | .extcodecopy | .datacopy
  | .call | .callcode | .delegatecall | .staticcall | .create | .create2 => true
  | _ => false

mutual
/-- Rewrite `e`, returning the rewritten expression and the cache valid
immediately after `e` is evaluated. -/
def mfE (C : MemCache) : Expr Op → Expr Op × MemCache
  | .lit l => (.lit l, C)
  | .var x => (.var x, C)
  | .builtin .mload [.lit (.number k)] =>
      match memLookup k C with
      | some v => (v.toExpr, C)
      | none => (.builtin .mload [.lit (.number k)], C)
  | .builtin op args =>
      let (args', C') := mfEArgs C args
      (.builtin op args', if opWritesMemory op then [] else C')
  | .call f args =>
      let (args', _) := mfEArgs C args
      -- An unknown callee may write memory arbitrarily.
      (.call f args', [])

def mfEArgs (C : MemCache) : List (Expr Op) → List (Expr Op) × MemCache
  | [] => ([], C)
  | e :: rest =>
      let (e', C') := mfE C e
      let (rest', C'') := mfEArgs C' rest
      (e' :: rest', C'')
end

/-! ### The statement sweep -/

mutual

def mfLet (C : MemCache) : List Ident → Option (Expr Op) →
    Option (Expr Op) × MemCache
  | [x], some e =>
      let (e', C') := mfE C e
      let C1 := cacheKill [x] C'
      -- Record a load-content fact when the rewrite did not fire (no live
      -- cell): `let x := mload(k)` means the word at `k` now denotes `x`.
      let C2 := match mloadLit e' with
        | some k => memPut k (.var x) C1
        | none => C1
      (some e', C2)
  | xs, some e =>
      let (e', C') := mfE C e
      (some e', cacheKill xs C')
  | xs, none => (none, cacheKill xs C)

def mfAssign (C : MemCache) :
    List Ident → Expr Op → Expr Op × MemCache
  | [x], e =>
      let (e', C') := mfE C e
      (e', cacheKill [x] C')
  | xs, e =>
      let (e', C') := mfE C e
      (e', cacheKill xs C')

def mfExprStmt (C : MemCache) (e : Expr Op) : Expr Op × MemCache :=
  match mstoreLit e with
  | some (k, v) =>
      let (v', Cv) := mfE C v
      let C1 := memKillOverlap k Cv
      let C2 := match classifyStorageVal v' with
        | some cv => memPut k cv C1
        | none => C1
      (.builtin .mstore [.lit (.number k), v'], C2)
  | none =>
      -- `mfE` threads memory-write effects (mstore8/mcopy/copy/call clear the
      -- cache); pure/read statements keep it.
      let (e', C') := mfE C e
      (e', C')

def mfStmt (C : MemCache) : Stmt Op → Stmt Op × MemCache
  | .letDecl xs rhs => let p := mfLet C xs rhs; (.letDecl xs p.1, p.2)
  | .assign xs e => let p := mfAssign C xs e; (.assign xs p.1, p.2)
  | .exprStmt e => let p := mfExprStmt C e; (.exprStmt p.1, p.2)
  | .block body =>
      let (body', C') := mfStmts C body
      (.block body', cacheKill (blockDecls body) C')
  | s@(.funDef _ _ _ _) => (s, C)
  | .cond c body =>
      let (c', Cc) := mfE C c
      let (body', _) := mfStmts Cc body
      let C' := if stmtsNoNormal body then Cc else []
      (.cond c' body', C')
  | s@(.switch _ _ _) => (s, [])
  | s@(.forLoop _ _ _ _) => (s, [])
  | s => (s, C)

def mfStmts (C : MemCache) :
    List (Stmt Op) → List (Stmt Op) × MemCache
  | [] => ([], C)
  | s :: rest =>
      let (s', C') := mfStmt C s
      let (rest', C'') := mfStmts C' rest
      (s' :: rest', C'')

end

/-! ### Function-body lifting (independent regions), mirroring `StorageForward`. -/

def memoryForwardShallowBlock (body : Block Op) : Block Op :=
  if storageLayoutFreeStmts body then (mfStmts [] body).1 else body

mutual
def mfFunStmt : Stmt Op → Stmt Op
  | .block body => .block (mfFunStmts body)
  | .funDef n ps rs body =>
      .funDef n ps rs (memoryForwardShallowBlock (mfFunStmts body))
  | .cond c body => .cond c (mfFunStmts body)
  | .switch c cases dflt => .switch c (mfFunCases cases) (mfFunDflt dflt)
  | .forLoop init c post body =>
      .forLoop init c
        (memoryForwardShallowBlock (mfFunStmts post))
        (memoryForwardShallowBlock (mfFunStmts body))
  | s => s

def mfFunStmts : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest => mfFunStmt s :: mfFunStmts rest

def mfFunCases : List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, body) :: rest => (l, mfFunStmts body) :: mfFunCases rest

def mfFunDflt : Option (Block Op) → Option (Block Op)
  | none => none
  | some body => some (mfFunStmts body)
end

def memoryForwardBlock (body : Block Op) : Block Op :=
  if storageLayoutFreeStmts body then
    let out := memoryForwardShallowBlock (mfFunStmts body)
    if storageLayoutFreeStmts out then out else body
  else body

/-! ### Correctness spot-checks

These lock in the invalidation obligations (`Stmt` has no `DecidableEq`, so we
match on the rewritten shape). -/

section Tests
open YulEvmCompiler.Optimizer.ReuseValues (exprBeq)
private def mL (k : Nat) : Expr Op := .builtin .mload [.lit (.number k)]
private def mS (k : Nat) (v : Expr Op) : Stmt Op :=
  .exprStmt (.builtin .mstore [.lit (.number k), v])

/-- The rewritten rhs of the `n`th statement, if it is a singleton `let`. -/
private def rhsOf (b : Block Op) (n : Nat) : Option (Expr Op) :=
  match b[n]? with
  | some (.letDecl _ (some e)) => some e
  | _ => none

private def run (b : Block Op) : Block Op := (mfStmts [] b).1

/-- Straight-line store→load forwards the stored value. -/
private def testForward : Block Op :=
  [mS 0 (.var "a"), .letDecl ["y"] (some (mL 0))]
#guard (rhsOf (run testForward) 1).any (exprBeq · (.var "a"))

/-- Reassigning the mentioned variable invalidates the fact: `mstore(0, x);
x := add(x,1); let y := mload(0)` must NOT forward `mload(0)` to `x`. -/
private def testReassign : Block Op :=
  [mS 0 (.var "x"),
   .assign ["x"] (.builtin .add [.var "x", .lit (.number 1)]),
   .letDecl ["y"] (some (mL 0))]
#guard (rhsOf (run testReassign) 2).any (exprBeq · (mL 0))

/-- An intervening memory write (`mstore8` to an unknown address) clears the
cache, so the later `mload(0)` is not forwarded. -/
private def testClobber : Block Op :=
  [mS 0 (.var "a"),
   .exprStmt (.builtin .mstore8 [.var "p", .var "q"]),
   .letDecl ["y"] (some (mL 0))]
#guard (rhsOf (run testClobber) 2).any (exprBeq · (mL 0))

/-- An `mload` evaluated *before* an effectful sibling in the same expression is
still forwarded (arg order): `mstore(0, a); let y := add(mload(0), f())`. -/
private def testArgOrder : Block Op :=
  [mS 0 (.var "a"),
   .letDecl ["y"] (some (.builtin .add [mL 0, .call "f" []]))]
#guard (rhsOf (run testArgOrder) 1).any
  (exprBeq · (.builtin .add [.var "a", .call "f" []]))
end Tests

mutual
/-- Apply `memoryForwardBlock` to every code block in an object tree. -/
def memoryForwardObject : Object Op → Object Op
  | .mk name code subs segs =>
      .mk name (memoryForwardBlock code) (memoryForwardObjects subs) segs

def memoryForwardObjects : List (Object Op) → List (Object Op)
  | [] => []
  | o :: rest => memoryForwardObject o :: memoryForwardObjects rest
end

end YulEvmCompiler.Optimizer.MemoryForward
