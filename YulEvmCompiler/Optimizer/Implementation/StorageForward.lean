import YulEvmCompiler.Optimizer.Implementation.DeadPure
set_option warningAsError true
/-!
# Literal-slot storage value forwarding

Solidity's unoptimized IR repeatedly reloads the same literal storage slot
through nested helper scaffolding. This pass forwards only three cheap value
shapes: a number, a variable, and `add(variable, number)`. Every store clears
the cache before establishing one new fact, so syntactically different keys
can alias without jeopardizing soundness. Unknown/stateful expressions and
control-flow joins clear the cache; a conditional whose body cannot complete
normally may retain it, because only the unselected branch reaches the tail.
Assignments to known-bound variables establish or rebind facts, and nested
blocks export facts whose representatives survive removal of direct locals.
Function bodies and loop post/body blocks are optimized as independent
regions, so facts never cross a call or loop-iteration boundary.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-- Cheap values worth replaying instead of a warm `SLOAD`. -/
inductive StorageVal
  | lit (n : Nat)
  | var (x : Ident)
  | add (x : Ident) (n : Nat)
  deriving Repr, DecidableEq

def StorageVal.toExpr : StorageVal → Expr Op
  | .lit n => .lit (.number n)
  | .var x => .var x
  | .add x n => .builtin .add [.var x, .lit (.number n)]

def StorageVal.dep : StorageVal → Option Ident
  | .lit _ => none
  | .var x | .add x _ => some x

def classifyStorageVal : Expr Op → Option StorageVal
  | .lit (.number n) => some (.lit n)
  | .var x => some (.var x)
  | .builtin .add [.var x, .lit (.number n)] => some (.add x n)
  | _ => none

def literalSloadKey : Expr Op → Option Nat
  | .builtin .sload [.lit (.number k)] => some k
  | _ => none

def literalStore : Expr Op → Option (Nat × StorageVal)
  | .builtin .sstore [.lit (.number k), rhs] =>
      (classifyStorageVal rhs).map (fun v => (k, v))
  | _ => none

/- Persistent-storage-neutral, total expression fragment. -/
mutual
def storageStableExpr : Expr Op → Bool
  | .lit _ | .var _ => true
  | .builtin op args =>
      (pureTotalArity op == some args.length) && storageStableArgs args
  | .call _ _ => false

def storageStableArgs : List (Expr Op) → Bool
  | [] => true
  | e :: rest => storageStableExpr e && storageStableArgs rest
end

mutual
/-- True when layout resolution is syntactically the identity on an expression. -/
def storageLayoutFreeExpr : Expr Op → Bool
  | .lit _ | .var _ => true
  | .builtin op args => op != .dataoffset && op != .datasize && storageLayoutFreeArgs args
  | .call _ args => storageLayoutFreeArgs args

def storageLayoutFreeArgs : List (Expr Op) → Bool
  | [] => true
  | e :: rest => storageLayoutFreeExpr e && storageLayoutFreeArgs rest

def storageLayoutFreeStmt : Stmt Op → Bool
  | .block body | .funDef _ _ _ body => storageLayoutFreeStmts body
  | .letDecl _ rhs => rhs.all storageLayoutFreeExpr
  | .assign _ rhs | .exprStmt rhs => storageLayoutFreeExpr rhs
  | .cond c body => storageLayoutFreeExpr c && storageLayoutFreeStmts body
  | .switch c cases dflt => storageLayoutFreeExpr c && storageLayoutFreeCases cases &&
      storageLayoutFreeDflt dflt
  | .forLoop init c post body => storageLayoutFreeStmts init && storageLayoutFreeExpr c &&
      storageLayoutFreeStmts post && storageLayoutFreeStmts body
  | .break | .continue | .leave => true

def storageLayoutFreeStmts : List (Stmt Op) → Bool
  | [] => true
  | s :: rest => storageLayoutFreeStmt s && storageLayoutFreeStmts rest

def storageLayoutFreeCases : List (Literal × Block Op) → Bool
  | [] => true
  | (_, body) :: rest => storageLayoutFreeStmts body && storageLayoutFreeCases rest

def storageLayoutFreeDflt : Option (Block Op) → Bool
  | none => true
  | some body => storageLayoutFreeStmts body
end

/-- Number-literal storage key and its known cheap value. -/
abbrev StorageCache := List (Nat × StorageVal)

def cacheLookup (k : Nat) (C : StorageCache) : Option StorageVal :=
  (C.find? (fun p => p.1 = k)).map (·.2)

def cacheKill (xs : List Ident) (C : StorageCache) : StorageCache :=
  C.filter (fun p => match p.2.dep with | none => true | some x => !xs.contains x)

def cachePut (k : Nat) (v : StorageVal) (C : StorageCache) : StorageCache :=
  (k, v) :: C.filter (fun p => p.1 != k)

/-- After assigning the value denoted by `rhs` to `x`, prefer `x` as the
replayable representative of every matching non-literal storage fact. Matching
is checked before invalidating facts that depended on the old value of `x`, so
`x := add(x, 1)` may safely retain a matching pre-assignment fact. Literal
facts remain literals because they are cheaper and do not depend on a binding. -/
def cacheAssign (x : Ident) (rhs : StorageVal) : StorageCache → StorageCache
  | [] => []
  | (k, v) :: rest =>
      let rest' := cacheAssign x rhs rest
      match rhs with
      | .lit _ =>
          if v.dep = some x then rest' else (k, v) :: rest'
      | _ =>
          if v = rhs then (k, .var x) :: rest'
          else if v.dep = some x then rest'
          else (k, v) :: rest'

mutual
/-- Syntactic proof search that a statement cannot yield `.normal`. -/
def stmtNoNormal : Stmt Op → Bool
  | .break | .continue | .leave => true
  | .block body => stmtsNoNormal body
  | .exprStmt (.builtin op _) => op == .revert
  | _ => false

def stmtsNoNormal : List (Stmt Op) → Bool
  | [] => false
  | s :: rest => stmtNoNormal s || stmtsNoNormal rest
end

/-- Bindings introduced at this block level and removed by `restore`. -/
def declaredStmts : List (Stmt Op) → List Ident
  | [] => []
  | .letDecl xs _ :: rest => xs ++ declaredStmts rest
  | _ :: rest => declaredStmts rest

mutual

def sfLet (C : StorageCache) : List Ident → Option (Expr Op) → Option (Expr Op) × StorageCache
  | [x], some e =>
      match literalSloadKey e with
      | some k =>
          let rhs := (cacheLookup k C).map StorageVal.toExpr |>.getD e
          (some rhs, cachePut k (.var x) (cacheKill [x] C))
      | none =>
          let C' := cacheKill [x] C
          if storageStableExpr e then (some e, C') else (some e, [])
  | xs, rhs =>
      let C' := cacheKill xs C
      match rhs with
      | none => (none, C')
      | some e =>
          if storageStableExpr e then (some e, C') else (some e, [])

def sfAssign (bound : List Ident) (C : StorageCache) :
    List Ident → Expr Op → Expr Op × StorageCache
  | [x], e =>
      match literalSloadKey e with
      | some k =>
          let rhs := (cacheLookup k C).map StorageVal.toExpr |>.getD e
          let C' := cacheKill [x] C
          let C' := if bound.contains x then cachePut k (.var x) C' else C'
          (rhs, C')
      | none =>
          if storageStableExpr e then
            match classifyStorageVal e with
            | some v =>
                let C' := if bound.contains x then cacheAssign x v C else cacheKill [x] C
                (e, C')
            | none => (e, cacheKill [x] C)
          else (e, [])
  | xs, e =>
      let C' := cacheKill xs C
      if storageStableExpr e then (e, C') else (e, [])

def sfExprStmt (C : StorageCache) : Expr Op → Expr Op × StorageCache
  | e =>
      match literalStore e with
      | some (k, v) => (e, cachePut k v [])
      | none => if storageStableExpr e then (e, C) else (e, [])

def sfStmt (bound : List Ident) (C : StorageCache) : Stmt Op → Stmt Op × StorageCache
  | .letDecl xs rhs => let p := sfLet C xs rhs; (.letDecl xs p.1, p.2)
  | .assign xs e => let p := sfAssign bound C xs e; (.assign xs p.1, p.2)
  | .exprStmt e => let p := sfExprStmt C e; (.exprStmt p.1, p.2)
  | .block body =>
      let (body', C') := sfStmts bound C body
      (.block body', cacheKill (declaredStmts body) C')
  | s@(.funDef _ _ _ _) => (s, C)
  | .cond c body =>
      let (body', _) := sfStmts bound [] body
      let C' := if storageStableExpr c && stmtsNoNormal body then C else []
      (.cond c body', C')
  | s@(.switch _ _ _) => (s, [])
  | s@(.forLoop _ _ _ _) => (s, [])
  | s => (s, C)

def sfNextBound (bound : List Ident) : Stmt Op → List Ident
  | .letDecl xs _ => xs ++ bound
  | _ => bound

def sfStmts (bound : List Ident) (C : StorageCache) :
    List (Stmt Op) → List (Stmt Op) × StorageCache
  | [] => ([], C)
  | s :: rest =>
      let (s', C') := sfStmt bound C s
      let bound' := sfNextBound bound s
      let (rest', C'') := sfStmts bound' C' rest
      (s' :: rest', C'')

def sfCases (bound : List Ident) :
    List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, body) :: rest =>
      (l, (sfStmts bound [] body).1) :: sfCases bound rest

def sfDflt (bound : List Ident) : Option (Block Op) → Option (Block Op)
  | none => none
  | some body => some (sfStmts bound [] body).1

end


/-! `storageForwardShallow` leaves function bodies unchanged. A generic
function-body lifting pass below applies it recursively after its local proof. -/

def storageForwardShallowBlock (body : Block Op) : Block Op :=
  if storageLayoutFreeStmts body then (sfStmts [] [] body).1 else body

mutual
/-- Recursively apply the shallow pass at each function-body boundary. -/
def sfFunStmt : Stmt Op → Stmt Op
  | .block body => .block (sfFunStmts body)
  | .funDef n ps rs body =>
      .funDef n ps rs (storageForwardShallowBlock (sfFunStmts body))
  | .cond c body => .cond c (sfFunStmts body)
  | .switch c cases dflt => .switch c (sfFunCases cases) (sfFunDflt dflt)
  | .forLoop init c post body =>
      .forLoop init c
        (storageForwardShallowBlock (sfFunStmts post))
        (storageForwardShallowBlock (sfFunStmts body))
  | s => s

def sfFunStmts : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: rest => sfFunStmt s :: sfFunStmts rest

def sfFunCases : List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, body) :: rest => (l, sfFunStmts body) :: sfFunCases rest

def sfFunDflt : Option (Block Op) → Option (Block Op)
  | none => none
  | some body => some (sfFunStmts body)
end

def storageForwardBlock (body : Block Op) : Block Op :=
  storageForwardShallowBlock (sfFunStmts body)

end YulEvmCompiler.Optimizer
