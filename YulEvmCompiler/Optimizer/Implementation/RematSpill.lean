import YulEvmCompiler.Optimizer.Implementation.StorageForward
set_option warningAsError true
/-!
# Rematerialize-before-spill (EXPERIMENTAL, transform-only prototype)

The Pool* fixtures spill ~637 bindings because a single function body carries
too many simultaneously-live locals (measured: reducing inlining does not change
the spill count — the locals are the main body's own). This pass shrinks the
live-local set by *rematerializing* cheap pure single-def bindings at their use
sites: `let x := add(a, 32); … use(x) …` → `… use(add(a, 32)) …`, dropping the
binding. A binding recomputed at each use is no longer live across statements,
freeing a stack slot with no memory round-trip.

Legality (prototype — validated empirically, proof pending):
* the producer is **pure-total** (`storageStableExpr`: lit/var/total arith, no
  `sload`/`mload`/`keccak`/calls), so duplicating its evaluation preserves value
  and state and cannot get stuck;
* the bound variable is **single-def** — never an assignment target anywhere in
  the region (so dropping its `let` cannot orphan a later `x := …`);
* every free variable of the producer is **stable** — never an assignment target
  in the region (so recomputation at any later point yields the same value).

Under the unique-name invariant that `Normalize` establishes, "assignment
target" is the only way a name's value changes after its single declaration, so
the region's assign-target set is a sufficient stability oracle. Producer chains
compose: a candidate's rhs is substituted through the running map before it is
recorded, so `let a := add(b,1); let x := add(a,1)` remats `x ↦ add(add(b,1),1)`.

Wired only as a pre-spill ladder arm in `compileSource`, so objects that compile
without spilling are untouched.
-/

namespace YulEvmCompiler.Optimizer.RematSpill

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer (storageStableExpr)

/-! Free variables of an expression (reads). -/
mutual
def exprVarsR : Expr Op → List Ident
  | .lit _ => []
  | .var x => [x]
  | .builtin _ args | .call _ args => argsVarsR args
def argsVarsR : List (Expr Op) → List Ident
  | [] => []
  | e :: rest => exprVarsR e ++ argsVarsR rest
end

/-! Builtin-op count of an expression (leaves are free stack reads/pushes). A
candidate producer is bounded by this so a large tree cannot be duplicated into
many uses even when it happens to relieve pressure. -/
mutual
def opCountR : Expr Op → Nat
  | .lit _ | .var _ => 0
  | .builtin _ args => 1 + opCountArgsR args
  | .call _ args => 1 + opCountArgsR args
def opCountArgsR : List (Expr Op) → Nat
  | [] => 0
  | e :: rest => opCountR e + opCountArgsR rest
end

/-- Max ops in a rematerializable producer (`add(a,32)`, `and(x,mask)`,
`signextend(k,x)`, and short chains). -/
def rematOpLimit : Nat := 3

/-! ### Assignment-target set of a region (the stability oracle) -/

mutual
def assignTargetsStmt : Stmt Op → List Ident
  | .assign xs _ => xs
  | .block body | .funDef _ _ _ body => assignTargetsStmts body
  | .cond _ body => assignTargetsStmts body
  | .switch _ cases dflt => assignTargetsCases cases ++ assignTargetsDflt dflt
  | .forLoop init _ post body =>
      assignTargetsStmts init ++ assignTargetsStmts post ++ assignTargetsStmts body
  | _ => []
  termination_by s => sizeOf s

def assignTargetsStmts : List (Stmt Op) → List Ident
  | [] => []
  | s :: rest => assignTargetsStmt s ++ assignTargetsStmts rest
  termination_by ss => sizeOf ss

def assignTargetsCases : List (Literal × Block Op) → List Ident
  | [] => []
  | (_, b) :: rest => assignTargetsStmts b ++ assignTargetsCases rest
  termination_by cs => sizeOf cs

def assignTargetsDflt : Option (Block Op) → List Ident
  | none => []
  | some b => assignTargetsStmts b
  termination_by d => sizeOf d
end

/-! ### Substitution of remat bindings into reads -/

abbrev RematMap := List (Ident × Expr Op)

mutual
def substExprR (σ : RematMap) : Expr Op → Expr Op
  | .lit l => .lit l
  | .var x => match σ.find? (fun p => p.1 = x) with
      | some p => p.2
      | none => .var x
  | .builtin op args => .builtin op (substArgsR σ args)
  | .call f args => .call f (substArgsR σ args)

def substArgsR (σ : RematMap) : List (Expr Op) → List (Expr Op)
  | [] => []
  | e :: rest => substExprR σ e :: substArgsR σ rest
end

/-- Substitute `σ` into a statement's own expressions (NOT recursing into nested
bodies — the sweep does that, threading scope). -/
def substShallow (σ : RematMap) : Stmt Op → Stmt Op
  | .letDecl xs (some e) => .letDecl xs (some (substExprR σ e))
  | .letDecl xs none => .letDecl xs none
  | .assign xs e => .assign xs (substExprR σ e)
  | .exprStmt e => .exprStmt (substExprR σ e)
  | .cond c body => .cond (substExprR σ c) body
  | .switch c cases dflt => .switch (substExprR σ c) cases dflt
  | s => s

/-! ### The sweep -/

/-! `A` is the region's assignment-target set (stability oracle). `σ` threads
left-to-right through a statement sequence; nested bodies are swept with the
current `σ` but their internal extensions do not leak to later siblings. -/
mutual
def rematStmts (A : List Ident) (σ : RematMap) :
    List (Stmt Op) → List (Stmt Op) × RematMap
  | [] => ([], σ)
  | s :: rest =>
      let (s', σ') := rematStmt A σ s
      let (rest', σ'') := rematStmts A σ' rest
      (s' ++ rest', σ'')

def rematStmt (A : List Ident) (σ : RematMap) : Stmt Op → List (Stmt Op) × RematMap
  | .letDecl [x] (some e) =>
      let e' := substExprR σ e
      if storageStableExpr e' && opCountR e' ≤ rematOpLimit && !A.contains x
          && (exprVarsR e').all (fun v => !A.contains v)
          && !(exprVarsR e').contains x then
        -- Rematerialize: drop the binding, record x ↦ e'.
        ([], (x, e') :: σ)
      else
        ([.letDecl [x] (some e')], σ)
  | .letDecl xs val =>
      ([.letDecl xs (val.map (substExprR σ))], σ)
  | .assign xs e => ([.assign xs (substExprR σ e)], σ)
  | .exprStmt e => ([.exprStmt (substExprR σ e)], σ)
  | .block body => ([.block (rematStmts A σ body).1], σ)
  | .cond c body => ([.cond (substExprR σ c) (rematStmts A σ body).1], σ)
  | .switch c cases dflt =>
      ([.switch (substExprR σ c) (rematCases A σ cases) (rematDflt A σ dflt)], σ)
  | .forLoop init c post body =>
      -- `init` may declare loop locals visible in cond/post/body; sweep it
      -- threading σ, then use the post-init σ for the rest.
      let (init', σ') := rematStmts A σ init
      ([.forLoop init' (substExprR σ' c) (rematStmts A σ' post).1
        (rematStmts A σ' body).1], σ)
  | .funDef f ps rs body =>
      -- Independent scope: fresh σ, its own assign-target oracle.
      ([.funDef f ps rs (rematStmts (assignTargetsStmts body) [] body).1], σ)
  | s => ([s], σ)

def rematCases (A : List Ident) (σ : RematMap) :
    List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, b) :: rest => (l, (rematStmts A σ b).1) :: rematCases A σ rest

def rematDflt (A : List Ident) (σ : RematMap) : Option (Block Op) → Option (Block Op)
  | none => none
  | some b => some (rematStmts A σ b).1
end

def rematBlock (body : Block Op) : Block Op :=
  (rematStmts (assignTargetsStmts body) [] body).1

mutual
def rematObject : Object Op → Object Op
  | .mk name code subs segs =>
      .mk name (rematBlock code) (rematObjects subs) segs

def rematObjects : List (Object Op) → List (Object Op)
  | [] => []
  | o :: rest => rematObject o :: rematObjects rest
end

end YulEvmCompiler.Optimizer.RematSpill
