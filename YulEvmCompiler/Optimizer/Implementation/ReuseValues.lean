import YulEvmCompiler.Optimizer.Implementation.StorageForward
set_option warningAsError true
/-!
# Scoped available-value reuse (state-read and pure CSE)

After `InlineCalls` + `Flatten` + `FuseDeclAssign`, the hottest loops repeat
whole value-computation groups per iteration at one statement level.  The
dominant Aave shape is the fully inlined mapping-address computation,
duplicated with identical operands:

```yul
mstore(0, key) mstore(0x20, slot) let h := keccak256(0, 0x40) let w := sload(h)
...  // pure checks on w
mstore(0, key) mstore(0x20, slot) let h2 := keccak256(0, 0x40) let w2 := sload(h2)
```

solc's optimizer CSEs the second group away; ours re-pays the hash plus a warm
`sload` every iteration.  This pass forwards available *values* (it never
deletes a store — redundant-store elimination is a separate concern):

* **Pure facts** — `x := e` with `e` a small total pure tree records the
  canonicalized `e ↦ x`; a later occurrence of the same canonical tree
  rewrites to `x`.
* **Scratch-cell facts** — `mstore(<literal k>, e)` with `e` canonicalizable
  records "the word at `k` denotes `e`", killing only overlapping cells.
  Cell facts describe memory *content*; reads never kill them.
* **Available keccaks, keyed by content** — `x := keccak256(a, b)` with
  literal `a, b` (`b` a positive multiple of 32) and every covered cell known
  records `(a, b, content-signature) ↦ x`.  A later hash whose current
  signature is identical rewrites to `x`.  Content-keyed facts are
  memory-independent: they die only when a signature variable is killed.
* **Available storage reads** — `x := sload(k)` records canonical `k ↦ x`;
  killed by any `sstore` or unknown/effectful statement.
* **Available memory reads** — `x := mload(<literal k>)` with a cell fact for
  `k` rewrites to the cell's value; otherwise records the cell.
* **Aliases** — `x := y` canonicalizes `x` to `y`'s representative so copies
  do not break matching (`CoalesceCopies`/`DeadPure` clean the copies up).

Facts are established by `let` and by singleton assignment; assignment first
kills every fact mentioning the target.  Unknown or effectful expressions
clear everything except what provably survives: external calls clear cells and
storage facts but not pure/keccak facts (their denotations only mention local
variables, which no call changes) — conservatively we clear everything at
calls in v1.  `switch`/`forLoop` clear the cache and are optimized as
independent regions by the function-body wrapper; a conditional preserves
facts only when its condition is state-neutral and its body cannot complete
normally.  Nested blocks export facts that do not mention block locals.

Soundness (deferred to `ReuseValuesSound.lean`): the
`StorageForward`/scoped-export architecture — a bidirectional `Step`
simulation carrying cache validity: every fact's denotation holds in the
current state, every fact variable is bound, and for keccak/mload facts the
touched range is already within active memory (the recording read touched it
and `activeWords` is monotone), so the skipped re-evaluation is
state-preserving.  The transform is guarded by whole-block
`storageLayoutFreeStmts` and preserves it, so layout resolution is the
identity on both input and output and the object-path congruence is the
pass's own soundness (the `RejoinPairs` recipe).
-/

namespace YulEvmCompiler.Optimizer.ReuseValues

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer (pureTotalArity classifyStorageVal cacheLookup
  blockDecls stmtsNoNormal storageLayoutFreeStmts)

/-! ### Canonical pure expressions -/

mutual
/-- Syntactic equality of expressions (no `DecidableEq` derivation exists for
the recursive `Expr`). -/
def exprBeq : Expr Op → Expr Op → Bool
  | .lit (.number a), .lit (.number b) => a == b
  | .lit (.string a), .lit (.string b) => a == b
  | .var x, .var y => x == y
  | .builtin o1 a1, .builtin o2 a2 => o1 == o2 && argsBeq a1 a2
  | .call f1 a1, .call f2 a2 => f1 == f2 && argsBeq a1 a2
  | _, _ => false

def argsBeq : List (Expr Op) → List (Expr Op) → Bool
  | [], [] => true
  | e1 :: r1, e2 :: r2 => exprBeq e1 e2 && argsBeq r1 r2
  | _, _ => false
end

mutual
/-- Node count, to cap fact sizes. -/
def exprSize : Expr Op → Nat
  | .lit _ | .var _ => 1
  | .builtin _ args => 1 + argsSize args
  | .call _ args => 1 + argsSize args

def argsSize : List (Expr Op) → Nat
  | [] => 0
  | e :: rest => exprSize e + argsSize rest
end

mutual
/-- Variables of an expression. -/
def exprVarsRv : Expr Op → List Ident
  | .lit _ => []
  | .var x => [x]
  | .builtin _ args | .call _ args => argsVarsRv args

def argsVarsRv : List (Expr Op) → List Ident
  | [] => []
  | e :: rest => exprVarsRv e ++ argsVarsRv rest
end

/-- The size cap for canonical keys. -/
def rvSizeLimit : Nat := 16

/-! ### The cache -/

/-- One keccak content-signature entry: word index within the hashed range
and the canonical value the cell held. -/
abbrev CellSig := List (Nat × Expr Op)

structure RvCache where
  /-- `x ↦ r`: `x` currently holds the same value as canonical `r`. -/
  aliases : List (Ident × Ident)
  /-- `k ↦ e`: the 32-byte word at literal address `k` denotes canonical `e`. -/
  cells : List (Nat × Expr Op)
  /-- `e ↦ x`: canonical total pure `e` evaluates to `x`'s value. -/
  pures : List (Expr Op × Ident)
  /-- `(base, size, sig) ↦ x`: hashing `size` bytes at `base` while the
  covered cells denote `sig` produced `x`'s value. -/
  kecs : List ((Nat × Nat × CellSig) × Ident)
  /-- `k ↦ x`: `sload(k)` (canonical `k`) produced `x`'s value. -/
  slds : List (Expr Op × Ident)

def RvCache.empty : RvCache := ⟨[], [], [], [], []⟩

def canonVar (C : RvCache) (x : Ident) : Ident :=
  ((C.aliases.find? (fun p => p.1 = x)).map (·.2)).getD x

mutual
/-- Canonicalize a total pure expression: alias-resolve every variable.
`none` for anything outside the pure-total fragment. -/
def canonPureGo (C : RvCache) : Expr Op → Option (Expr Op)
  | .lit (.number n) => some (.lit (.number n))
  | .lit _ => none
  | .var x => some (.var (canonVar C x))
  | .builtin op args =>
      if pureTotalArity op == some args.length then
        (canonPureArgs C args).map (.builtin op)
      else none
  | .call _ _ => none

def canonPureArgs (C : RvCache) : List (Expr Op) → Option (List (Expr Op))
  | [] => some []
  | e :: rest => do pure ((← canonPureGo C e) :: (← canonPureArgs C rest))
end

/-- `canonPureGo` under the size cap. -/
def canonPure (C : RvCache) (e : Expr Op) : Option (Expr Op) :=
  if exprSize e > rvSizeLimit then none else canonPureGo C e

def sigBeq : CellSig → CellSig → Bool
  | [], [] => true
  | (i1, e1) :: r1, (i2, e2) :: r2 => i1 == i2 && exprBeq e1 e2 && sigBeq r1 r2
  | _, _ => false

def sigMentions (x : Ident) (sig : CellSig) : Bool :=
  sig.any (fun p => (exprVarsRv p.2).contains x)

/-- Remove every fact that mentions any of `xs`. -/
def RvCache.kill (xs : List Ident) (C : RvCache) : RvCache where
  aliases := C.aliases.filter (fun p => !xs.contains p.1 && !xs.contains p.2)
  cells := C.cells.filter (fun p => !xs.any ((exprVarsRv p.2).contains ·))
  pures := C.pures.filter (fun p =>
    !xs.contains p.2 && !xs.any ((exprVarsRv p.1).contains ·))
  kecs := C.kecs.filter (fun p =>
    !xs.contains p.2 && !xs.any (sigMentions · p.1.2.2))
  slds := C.slds.filter (fun p =>
    !xs.contains p.2 && !xs.any ((exprVarsRv p.1).contains ·))

def RvCache.killCells (C : RvCache) : RvCache := { C with cells := [] }
def RvCache.killSlds (C : RvCache) : RvCache := { C with slds := [] }

def cellsOverlap (a b : Nat) : Bool := a < b + 32 && b < a + 32

/-- Record a store to literal cell `k` of canonical value `v` (`none` clears
just the overlapping cells). -/
def RvCache.putCell (k : Nat) (v : Option (Expr Op)) (C : RvCache) : RvCache :=
  let kept := C.cells.filter (fun p => !cellsOverlap p.1 k)
  { C with cells := match v with | some v => (k, v) :: kept | none => kept }

/-- The content signature covering `[base, base+size)`, when every covered
32-byte word has a cell fact. -/
def coverageSig (C : RvCache) (base size : Nat) : Option CellSig :=
  if size == 0 || size % 32 != 0 then none
  else go (size / 32) 0
where
  go : Nat → Nat → Option CellSig
    | 0, _ => some []
    | n + 1, i => do
        let v ← (C.cells.find? (fun p => p.1 = base + 32 * i)).map (·.2)
        let rest ← go n (i + 1)
        pure ((i, v) :: rest)

/-! ### Expression classification -/

/-- Literal keccak range, bounded so the raw naturals coincide with the
semantic (`toNat`-of-`litValue`) addresses. -/
def keccakLits : Expr Op → Option (Nat × Nat)
  | .builtin .keccak256 [.lit (.number a), .lit (.number b)] =>
      if a + b ≤ 2 ^ 256 ∧ b < 2 ^ 256 then some (a, b) else none
  | _ => none

def sloadArg : Expr Op → Option (Expr Op)
  | .builtin .sload [k] => some k
  | _ => none

def mloadLit : Expr Op → Option Nat
  | .builtin .mload [.lit (.number k)] =>
      if k + 32 ≤ 2 ^ 256 then some k else none
  | _ => none

def mstoreLit : Expr Op → Option (Nat × Expr Op)
  | .builtin .mstore [.lit (.number k), e] =>
      if k + 32 ≤ 2 ^ 256 then some (k, e) else none
  | _ => none

mutual
/-- State-neutral expressions: total pure trees plus the read-only state ops.
`sload` never changes state; `mload`/`keccak256` only extend active memory
monotonically, which cannot invalidate a tracked fact. -/
def rvNeutralExpr : Expr Op → Bool
  | .lit _ | .var _ => true
  | .builtin .sload args | .builtin .mload args =>
      args.length == 1 && rvNeutralArgs args
  | .builtin .keccak256 args => args.length == 2 && rvNeutralArgs args
  | .builtin op args =>
      (pureTotalArity op == some args.length) && rvNeutralArgs args
  | .call _ _ => false

def rvNeutralArgs : List (Expr Op) → Bool
  | [] => true
  | e :: rest => rvNeutralExpr e && rvNeutralArgs rest
end

/-! ### Forwarding one right-hand side

Given the rhs of a singleton `let`/assignment for target `x` (already killed
from `C`), return the (possibly rewritten) rhs and the cache extended with the
fact this binding establishes. -/

def rvRhs (C : RvCache) (x : Ident) (e : Expr Op) : Expr Op × RvCache :=
  match e with
  | .var y =>
      (.var y, { C with aliases := (x, canonVar C y) :: C.aliases })
  | _ =>
    match keccakLits e with
    | some (a, b) =>
        (match coverageSig C a b with
         | some sig =>
             match C.kecs.find? (fun p =>
                 p.1.1 == a && p.1.2.1 == b && sigBeq p.1.2.2 sig) with
             | some (_, h) =>
                 (.var h, { C with aliases := (x, canonVar C h) :: C.aliases })
             | none => (e, { C with kecs := ((a, b, sig), x) :: C.kecs })
         | none => (e, C))
    | none =>
      match sloadArg e with
      | some k =>
          (match canonPure C k with
           | some ck =>
               (match C.slds.find? (fun p => exprBeq p.1 ck) with
                | some (_, w) =>
                    (.var w, { C with aliases := (x, canonVar C w) :: C.aliases })
                | none =>
                    -- A self-referential binding (`let x := sload(x)`) would
                    -- record a key whose `x` re-reads the *new* binding.
                    if (exprVarsRv ck).contains x then (e, C)
                    else (e, { C with slds := (ck, x) :: C.slds }))
           | none =>
               -- A non-canonicalizable key may hide arbitrary effects.
               if rvNeutralExpr e then (e, C) else (e, RvCache.empty))
      | none =>
        match mloadLit e with
        | some k =>
            (match C.cells.find? (fun p => p.1 = k) with
             | some (_, Expr.var v) =>
                 -- The cell's value replays the load (cheap shapes only).
                 (.var v, { C with aliases := (x, canonVar C v) :: C.aliases })
             | some (_, Expr.lit l) => (.lit l, C)
             | _ => (e, C))
        | none =>
            match canonPure C e with
            | some ce =>
                -- Bare literals/variables are cheaper re-pushed than reused.
                if exprSize ce ≤ 1 then (e, C)
                else
                  (match C.pures.find? (fun p => exprBeq p.1 ce) with
                   | some (_, w) =>
                       (.var w,
                        { C with aliases := (x, canonVar C w) :: C.aliases })
                   | none =>
                       if (exprVarsRv ce).contains x then (e, C)
                       else (e, { C with pures := (ce, x) :: C.pures }))
            | none =>
                if rvNeutralExpr e then (e, C) else (e, RvCache.empty)

/-! ### The sweep -/

/-- Names visibly bound after a statement (`StorageForward`'s threading). -/
def rvNextBound (bound : List Ident) : Stmt Op → List Ident
  | .letDecl xs _ => xs ++ bound
  | _ => bound

mutual

def rvLet (C : RvCache) : List Ident → Option (Expr Op) →
    Option (Expr Op) × RvCache
  | [x], some e =>
      let p := rvRhs (C.kill [x]) x e
      (some p.1, p.2)
  | xs, rhs =>
      let C' := C.kill xs
      match rhs with
      | none => (none, C')
      | some e => if rvNeutralExpr e then (some e, C') else (some e, RvCache.empty)

def rvAssign (bound : List Ident) (C : RvCache) :
    List Ident → Expr Op → Expr Op × RvCache
  | [x], e =>
      -- Assignment to an unbound name is a semantic no-op, so a fact
      -- recorded for it would be baseless; `bound` mirrors `StorageForward`.
      if bound.contains x then rvRhs (C.kill [x]) x e
      else
        let C' := C.kill [x]
        if rvNeutralExpr e then (e, C') else (e, RvCache.empty)
  | xs, e =>
      let C' := C.kill xs
      if rvNeutralExpr e then (e, C') else (e, RvCache.empty)

def rvExprStmt (C : RvCache) (e : Expr Op) : Expr Op × RvCache :=
  match mstoreLit e with
  | some (k, v) =>
      if rvNeutralExpr v then (e, C.putCell k (canonPure C v))
      else (e, RvCache.empty)
  | none =>
      match e with
      | .builtin .sstore args =>
          if args.length == 2 && rvNeutralArgs args then (e, C.killSlds)
          else (e, RvCache.empty)
      | .builtin .mstore _ =>
          if rvNeutralExpr e then (e, C.killCells) else (e, RvCache.empty)
      | _ => if rvNeutralExpr e then (e, C) else (e, RvCache.empty)

def rvStmt (bound : List Ident) (C : RvCache) : Stmt Op → Stmt Op × RvCache
  | .letDecl xs rhs => let p := rvLet C xs rhs; (.letDecl xs p.1, p.2)
  | .assign xs e => let p := rvAssign bound C xs e; (.assign xs p.1, p.2)
  | .exprStmt e => let p := rvExprStmt C e; (.exprStmt p.1, p.2)
  | .block body =>
      let (body', C') := rvStmts bound C body
      (.block body', C'.kill (blockDecls body))
  | s@(.funDef _ _ _ _) => (s, C)
  | .cond c body =>
      let (body', _) := rvStmts bound RvCache.empty body
      let C' := if rvNeutralExpr c && stmtsNoNormal body then C
                else RvCache.empty
      (.cond c body', C')
  | s@(.switch _ _ _) => (s, RvCache.empty)
  | s@(.forLoop _ _ _ _) => (s, RvCache.empty)
  | s => (s, C)

def rvStmts (bound : List Ident) (C : RvCache) :
    List (Stmt Op) → List (Stmt Op) × RvCache
  | [] => ([], C)
  | s :: rest =>
      let (s', C') := rvStmt bound C s
      let (rest', C'') := rvStmts (rvNextBound bound s) C' rest
      (s' :: rest', C'')

end

/-- The shallow pass: one linear sweep, function bodies untouched. Guarded by
whole-block layout-freedom (see the module notes). -/
def reuseValuesShallowBlock (body : Block Op) : Block Op :=
  if storageLayoutFreeStmts body then (rvStmts [] RvCache.empty body).1
  else body

mutual
/-- Recursively apply the shallow pass at each function-body, loop-post, and
loop-body boundary (each is an independent region). -/
def rvFunStmt : Stmt Op → Stmt Op
  | .block body => .block (rvFunStmts body)
  | .funDef n ps rs body =>
      .funDef n ps rs (reuseValuesShallowBlock (rvFunStmts body))
  | .cond c body => .cond c (rvFunStmts body)
  | .switch c cases dflt => .switch c (rvFunCases cases) (rvFunDflt dflt)
  | .forLoop init c post body =>
      .forLoop init c
        (reuseValuesShallowBlock (rvFunStmts post))
        (reuseValuesShallowBlock (rvFunStmts body))
  | s => s

def rvFunStmts : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest => rvFunStmt s :: rvFunStmts rest

def rvFunCases : List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, body) :: rest => (l, rvFunStmts body) :: rvFunCases rest

def rvFunDflt : Option (Block Op) → Option (Block Op)
  | none => none
  | some body => some (rvFunStmts body)
end

def reuseValuesBlock (body : Block Op) : Block Op :=
  if storageLayoutFreeStmts body then
    let out := reuseValuesShallowBlock (rvFunStmts body)
    if storageLayoutFreeStmts out then out else body
  else body

end YulEvmCompiler.Optimizer.ReuseValues
