import YulEvmCompiler.Optimizer.Implementation.ReuseValues
set_option warningAsError true
/-!
# Equal-store elimination (EXPERIMENTAL, def-only)

Drops `mstore(k, v)` / `sstore(k, v)` when the value provably already at `k`
equals `v` — a store of the value already present is the identity, so deleting
it is exact-state-preserving. For `sstore` it is also **refund-neutral**:
`Gas.sstoreRefund` returns `0` whenever `current = new`, and the semantics use
warm SSTORE prices throughout (no cold/warm access list), so the redundant write
changes neither storage nor the refund counter; deleting it only saves gas.

A content fact `k ↦ e` (pure-total `e`, syntactic key `k` a literal) holds after
`mstore(k, e)` / `sstore(k, e)`, or after `let x := mload(k)` / `sload(k)`
(recording `k ↦ x`). It is invalidated by: a clobbering write to `k` with a
different value; a write that may alias (non-literal / `mstore8` / copy family
for memory, non-literal `sstore` for storage); reassignment or shadowing of a
variable the value mentions; a user/CALL-family expression (may write anything);
and control flow (facts do not cross basic blocks — bodies are scanned as
independent runs). A later `mstore(k, e')`/`sstore(k, e')` with `e'` syntactically
equal to the live fact is deleted.
-/

namespace YulEvmCompiler.Optimizer.EqualStoreElim

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer (storageStableExpr)
open YulEvmCompiler.Optimizer.ReuseValues (exprBeq exprVarsRv cellsOverlap)

/-! Does an expression evaluate a user call or a memory/storage-writing
built-in (the value-returning `call`/`create` family)? Such a value may modify
arbitrary memory and storage, so it invalidates all content facts. -/
mutual
def exprMayWrite : Expr Op → Bool
  | .lit _ | .var _ => false
  | .call _ _ => true
  | .builtin op args =>
      (match op with
       | .call | .callcode | .delegatecall | .staticcall | .create | .create2 => true
       | _ => false) || argsMayWrite args
def argsMayWrite : List (Expr Op) → Bool
  | [] => false
  | e :: rest => exprMayWrite e || argsMayWrite rest
end

structure EqCache where
  mem : List (Nat × Expr Op) := []
  sto : List (Nat × Expr Op) := []

def EqCache.killAll : EqCache := {}

/-- Drop facts whose value mentions any reassigned/shadowed variable. -/
def EqCache.killVars (xs : List Ident) (C : EqCache) : EqCache where
  mem := C.mem.filter (fun p => !xs.any ((exprVarsRv p.2).contains ·))
  sto := C.sto.filter (fun p => !xs.any ((exprVarsRv p.2).contains ·))

def EqCache.putMem (k : Nat) (v : Expr Op) (C : EqCache) : EqCache :=
  { C with mem := (k, v) :: C.mem.filter (fun p => !cellsOverlap p.1 k) }

def EqCache.putSto (k : Nat) (v : Expr Op) (C : EqCache) : EqCache :=
  { C with sto := (k, v) :: C.sto.filter (fun p => p.1 != k) }

def memLit : Expr Op → Option (Nat × Expr Op)
  | .builtin .mstore [.lit (.number k), v] => some (k, v)
  | _ => none

def stoLit : Expr Op → Option (Nat × Expr Op)
  | .builtin .sstore [.lit (.number k), v] => some (k, v)
  | _ => none

def mloadLitArg : Expr Op → Option Nat
  | .builtin .mload [.lit (.number k)] => some k
  | _ => none

def sloadLitArg : Expr Op → Option Nat
  | .builtin .sload [.lit (.number k)] => some k
  | _ => none

/-- Is a live fact `k ↦ e` present with `e` syntactically equal to `v`? -/
def hasFact (facts : List (Nat × Expr Op)) (k : Nat) (v : Expr Op) : Bool :=
  match facts.find? (fun p => p.1 = k) with
  | some p => exprBeq p.2 v
  | none => false

/-! Process one statement: returns the kept statement list (`[]` = deleted) and
the updated cache. -/
mutual
def eqStmt (C : EqCache) : Stmt Op → List (Stmt Op) × EqCache
  | .exprStmt e =>
      match memLit e with
      | some (k, v) =>
          if hasFact C.mem k v then ([], C)                       -- identity mstore: drop
          else if storageStableExpr v then ([.exprStmt e], C.putMem k v)
          else ([.exprStmt e], { C with mem := C.mem.filter (fun p => !cellsOverlap p.1 k) })
      | none =>
      match stoLit e with
      | some (k, v) =>
          if hasFact C.sto k v then ([], C)                       -- identity sstore: drop
          else if storageStableExpr v then ([.exprStmt e], C.putSto k v)
          else ([.exprStmt e], { C with sto := C.sto.filter (fun p => p.1 != k) })
      | none =>
          -- Any other expression statement: a memory/storage write of unknown
          -- shape, an aliasing write, a call, sstore/mstore to a non-literal,
          -- mstore8, the copy family, logs — clear conservatively by class.
          match e with
          | .builtin .mstore _ | .builtin .mstore8 _ | .builtin .mcopy _
          | .builtin .calldatacopy _ | .builtin .returndatacopy _
          | .builtin .codecopy _ | .builtin .extcodecopy _ | .builtin .datacopy _ =>
              ([.exprStmt e], { C with mem := [] })
          | .builtin .sstore _ | .builtin .tstore _ =>
              ([.exprStmt e], { C with sto := [] })
          | _ => if exprMayWrite e then ([.exprStmt e], EqCache.killAll)
                 else ([.exprStmt e], C)
  | .letDecl [x] (some rhs) =>
      let C := C.killVars [x]
      match mloadLitArg rhs with
      | some k => ([.letDecl [x] (some rhs)], C.putMem k (.var x))
      | none =>
      match sloadLitArg rhs with
      | some k => ([.letDecl [x] (some rhs)], C.putSto k (.var x))
      | none =>
          if exprMayWrite rhs then ([.letDecl [x] (some rhs)], EqCache.killAll)
          else ([.letDecl [x] (some rhs)], C)
  | .letDecl xs val =>
      let C := C.killVars xs
      match val with
      | some rhs => if exprMayWrite rhs then ([.letDecl xs val], EqCache.killAll)
                    else ([.letDecl xs val], C)
      | none => ([.letDecl xs none], C)
  | .assign xs e =>
      let C := C.killVars xs
      if exprMayWrite e then ([.assign xs e], EqCache.killAll)
      else ([.assign xs e], C)
  | .block body => ([.block (eqStmts C body).1], EqCache.killAll)
  | .cond c body =>
      if exprMayWrite c then ([.cond c (eqStmts EqCache.killAll body).1], EqCache.killAll)
      else ([.cond c (eqStmts C body).1], EqCache.killAll)
  | .switch c cases dflt =>
      ([.switch c (eqCases cases) (eqDflt dflt)], EqCache.killAll)
  | .forLoop init c post body =>
      ([.forLoop (eqStmts EqCache.killAll init).1 c
        (eqStmts EqCache.killAll post).1 (eqStmts EqCache.killAll body).1],
       EqCache.killAll)
  | .funDef f ps rs body =>
      ([.funDef f ps rs (eqStmts EqCache.killAll body).1], C)
  | s => ([s], C)

def eqStmts (C : EqCache) : List (Stmt Op) → List (Stmt Op) × EqCache
  | [] => ([], C)
  | s :: rest =>
      let (keep, C') := eqStmt C s
      let (rest', C'') := eqStmts C' rest
      (keep ++ rest', C'')

def eqCases : List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, b) :: rest => (l, (eqStmts EqCache.killAll b).1) :: eqCases rest

def eqDflt : Option (Block Op) → Option (Block Op)
  | none => none
  | some b => some (eqStmts EqCache.killAll b).1
end

def eqBlock (body : Block Op) : Block Op := (eqStmts {} body).1

mutual
def eqObject : Object Op → Object Op
  | .mk name code subs segs =>
      .mk name (eqBlock code) (eqObjects subs) segs

def eqObjects : List (Object Op) → List (Object Op)
  | [] => []
  | o :: rest => eqObject o :: eqObjects rest
end

end YulEvmCompiler.Optimizer.EqualStoreElim
