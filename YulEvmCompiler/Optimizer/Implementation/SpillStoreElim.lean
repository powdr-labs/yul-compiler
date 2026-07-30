import YulEvmCompiler.Optimizer.Implementation.StorageForward
set_option warningAsError true
/-!
# Covered-before-read spill-slot store elimination (EXPERIMENTAL, def-only)

The memory-spill backend writes each spilled binding to a fixed literal slot at
every (re)definition. When a slot is written twice with no intervening memory
*read*, the first write is dead: the covering write fixes the final value, and
nothing observed the earlier one. Deleting it is exact-state-preserving, so the
differential's final-memory comparison is safe by construction.

This is a backward dead-store scan over straight-line statement runs:

* `dead` is the set of literal slots that will be overwritten before any read
  downstream. Scanning right-to-left, a clean literal `mstore(k, v)` — `v`
  pure-total (`storageStableExpr`: no `mload`/`sload`/`keccak`/call, so deleting
  it drops no observable effect) — is **dropped** when `k ∈ dead`, and
  otherwise adds `k` to `dead`.
* Any statement that may read memory or transfer control (calls, `mload`,
  `keccak`, logs, copies, `sstore`, control flow, a non-literal/`mstore8`
  write, or an impure store value) clears `dead` — conservatively assuming it
  observes every slot.
* Nested blocks/bodies are scanned as independent runs.

Restricted to straight-line runs (control flow clears `dead`), so no
cross-block reasoning is needed. Wired as untrusted glue in `compileSource`
after the spill arm; a soundness proof is deferred.
-/

namespace YulEvmCompiler.Optimizer.SpillStoreElim

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer (storageStableExpr)

/-- A statement that is exactly `mstore(<lit k>, v)`. -/
def litMstore : Stmt Op → Option (Nat × Expr Op)
  | .exprStmt (.builtin .mstore [.lit (.number k), v]) => some (k, v)
  | _ => none

/-- Statements safe to scan across without disturbing `dead`: they neither read
nor write memory nor transfer control. A pure-total rhs excludes `mload`/
`keccak`/`sload`/calls. -/
def scanTransparent : Stmt Op → Bool
  | .letDecl _ (some e) => storageStableExpr e
  | .letDecl _ none => true
  | .assign _ e => storageStableExpr e
  | .break | .continue | .leave => true
  | _ => false

/-- One right-to-left step: thread the dead-slot set and emit kept statements. -/
def elimStep (s : Stmt Op) (acc : List Nat × List (Stmt Op)) :
    List Nat × List (Stmt Op) :=
  let (dead, out) := acc
  match litMstore s with
  | some (k, v) =>
      if storageStableExpr v then
        if dead.contains k then (dead, out)          -- covered: drop
        else (k :: dead, s :: out)                   -- keep, now covers earlier
      else (dead, s :: out)   -- value is state-neutral-but... impure value keeps
  | none =>
      if scanTransparent s then (dead, s :: out)     -- pure, memory-inert
      else ([], s :: out)                            -- may read/branch: reset

/-- The dead-store scan over one straight-line run (recursion into nested
bodies is done by `elimStmt` first). -/
def deadStoreScan (ss : List (Stmt Op)) : List (Stmt Op) :=
  (ss.foldr elimStep ([], [])).2

mutual
/-- Recurse into nested bodies (each an independent run), then leave the leaf
statement for the run-level scan. -/
def elimStmt : Stmt Op → Stmt Op
  | .block body => .block (elimRun body)
  | .cond c body => .cond c (elimRun body)
  | .switch c cases dflt => .switch c (elimCases cases) (elimDflt dflt)
  | .forLoop init c post body =>
      .forLoop (elimRun init) c (elimRun post) (elimRun body)
  | .funDef f ps rs body => .funDef f ps rs (elimRun body)
  | s => s

def elimList : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest => elimStmt s :: elimList rest

/-- Recurse, then scan the run for covered stores. -/
def elimRun (ss : List (Stmt Op)) : List (Stmt Op) :=
  deadStoreScan (elimList ss)

def elimCases : List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, b) :: rest => (l, elimRun b) :: elimCases rest

def elimDflt : Option (Block Op) → Option (Block Op)
  | none => none
  | some b => some (elimRun b)
end

def elimBlock (body : Block Op) : Block Op := elimRun body

mutual
def elimObject : Object Op → Object Op
  | .mk name code subs segs =>
      .mk name (elimBlock code) (elimObjects subs) segs

def elimObjects : List (Object Op) → List (Object Op)
  | [] => []
  | o :: rest => elimObject o :: elimObjects rest
end

end YulEvmCompiler.Optimizer.SpillStoreElim
