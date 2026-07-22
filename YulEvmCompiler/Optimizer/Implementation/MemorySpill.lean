import YulEvmCompiler.Optimizer.Implementation.StackLayout
import YulEvmCompiler.Optimizer.Spec.MemoryGuard
set_option warningAsError true
/-!
# Guarded memory-spill primitives

Shared syntax helpers for the pressure-selected spiller.  The spilling path
retains Solidity's literal `memoryguard(k)` marker instead of inferring a
promise from an ordinary `mstore(64, k)`: only the marker grants the compiler
ownership of memory beginning at `k`.

Blocks containing `msize`, malformed guards, inconsistent guard bases, or an
address reservation that reaches `2^256` are rejected by the policy module.
-/

namespace YulEvmCompiler.Optimizer.MemorySpill

open YulSemantics
open YulSemantics.EVM

def word (n : Nat) : Expr Op := .lit (.number n)

def load (slot : Nat) : Expr Op := .builtin .mload [word slot]

def store (slot : Nat) (e : Expr Op) : Stmt Op :=
  .exprStmt (.builtin .mstore [word slot, e])

def distributeTemps (targets : List Nat) (temps : List Ident) : Block Op :=
  (targets.zip temps).map fun p => store p.1 (.var p.2)

/-! ### Ordinary memoryguard erasure

Ordinary compilation candidates interpret `memoryguard(e)` as its argument.
Keep that structural erasure beside the guarded resolver so the parser path
and the object-level soundness theorem refer to exactly the same transform.
-/

mutual
  def eraseMemoryGuardExpr {Op : Type} : Expr Op → Expr Op
    | .call "memoryguard" [arg] => eraseMemoryGuardExpr arg
    | .call name args => .call name (eraseMemoryGuardArgs args)
    | .builtin op args => .builtin op (eraseMemoryGuardArgs args)
    | .lit literal => .lit literal
    | .var name => .var name

  def eraseMemoryGuardArgs {Op : Type} : List (Expr Op) → List (Expr Op)
    | [] => []
    | expression :: rest =>
        eraseMemoryGuardExpr expression :: eraseMemoryGuardArgs rest
end

mutual
  def eraseMemoryGuardStmt {Op : Type} : Stmt Op → Stmt Op
    | .block body => .block (eraseMemoryGuardStmts body)
    | .funDef name params returns body =>
        .funDef name params returns (eraseMemoryGuardStmts body)
    | .letDecl names value => .letDecl names (value.map eraseMemoryGuardExpr)
    | .assign names value => .assign names (eraseMemoryGuardExpr value)
    | .cond condition body =>
        .cond (eraseMemoryGuardExpr condition) (eraseMemoryGuardStmts body)
    | .switch condition cases default =>
        .switch (eraseMemoryGuardExpr condition) (eraseMemoryGuardCases cases)
          (match default with
          | some body => some (eraseMemoryGuardStmts body)
          | none => none)
    | .forLoop init condition post body =>
        .forLoop (eraseMemoryGuardStmts init) (eraseMemoryGuardExpr condition)
          (eraseMemoryGuardStmts post) (eraseMemoryGuardStmts body)
    | .exprStmt expression => .exprStmt (eraseMemoryGuardExpr expression)
    | .break => .break
    | .continue => .continue
    | .leave => .leave
    termination_by statement => 2 * sizeOf statement

  def eraseMemoryGuardStmts {Op : Type} : Block Op → Block Op
    | [] => []
    | statement :: rest =>
        eraseMemoryGuardStmt statement :: eraseMemoryGuardStmts rest
    termination_by statements => 2 * sizeOf statements + 1

  def eraseMemoryGuardCases {Op : Type} : List (Literal × Block Op) →
      List (Literal × Block Op)
    | [] => []
    | (literal, body) :: rest =>
        (literal, eraseMemoryGuardStmts body) :: eraseMemoryGuardCases rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

mutual
  def eraseMemoryGuardObject {Op : Type} : Object Op → Object Op
    | .mk name code children data =>
        .mk name (eraseMemoryGuardStmts code)
          (eraseMemoryGuardObjects children) data

  def eraseMemoryGuardObjects {Op : Type} : List (Object Op) → List (Object Op)
    | [] => []
    | object :: rest =>
        eraseMemoryGuardObject object :: eraseMemoryGuardObjects rest
end

mutual
  def containsMsizeExpr : Expr Op → Bool
    | .lit _ | .var _ => false
    | .builtin op args => op == .msize || containsMsizeArgs args
    | .call _ args => containsMsizeArgs args

  def containsMsizeArgs : List (Expr Op) → Bool
    | [] => false
    | e :: rest => containsMsizeExpr e || containsMsizeArgs rest
end

mutual
  def containsMsizeStmt : Stmt Op → Bool
    | .block body | .funDef _ _ _ body =>
        containsMsizeStmts body
    | .cond condition body =>
        containsMsizeExpr condition || containsMsizeStmts body
    | .letDecl _ val => val.any containsMsizeExpr
    | .assign _ e | .exprStmt e => containsMsizeExpr e
    | .switch e cases dflt =>
        containsMsizeExpr e || containsMsizeCases cases ||
          match dflt with
          | some body => containsMsizeStmts body
          | none => false
    | .forLoop init c post body =>
        containsMsizeStmts init || containsMsizeExpr c ||
          containsMsizeStmts post || containsMsizeStmts body
    | .break | .continue | .leave => false
    termination_by s => 2 * sizeOf s

  def containsMsizeStmts : Block Op → Bool
    | [] => false
    | s :: rest => containsMsizeStmt s || containsMsizeStmts rest
    termination_by ss => 2 * sizeOf ss + 1

  def containsMsizeCases : List (Literal × Block Op) → Bool
    | [] => false
    | (_, body) :: rest => containsMsizeStmts body || containsMsizeCases rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

/-! ### Literal `memoryguard` markers

Collection is `Option`-valued so a malformed marker cannot be silently ignored
while another well-formed marker authorizes spilling.  After slot allocation,
all consistent markers are replaced by the raised reserved address.
-/

mutual
  def collectMemoryGuardsExpr? : Expr Op → Option (List Nat)
    | .lit _ | .var _ => some []
    | .call "memoryguard" [.lit (.number k)] => some [k]
    | .call "memoryguard" _ => none
    | .call _ args | .builtin _ args => collectMemoryGuardsArgs? args

  def collectMemoryGuardsArgs? : List (Expr Op) → Option (List Nat)
    | [] => some []
    | e :: rest => do
        let head ← collectMemoryGuardsExpr? e
        let tail ← collectMemoryGuardsArgs? rest
        some (head ++ tail)
end

mutual
  def collectMemoryGuardsStmt? : Stmt Op → Option (List Nat)
    | .block body | .funDef _ _ _ body => collectMemoryGuardsStmts? body
    | .letDecl _ val =>
        match val with
        | some e => collectMemoryGuardsExpr? e
        | none => some []
    | .assign _ e | .exprStmt e => collectMemoryGuardsExpr? e
    | .cond c body => do
        let head ← collectMemoryGuardsExpr? c
        let tail ← collectMemoryGuardsStmts? body
        some (head ++ tail)
    | .switch e cases dflt => do
        let head ← collectMemoryGuardsExpr? e
        let branches ← collectMemoryGuardsCases? cases
        let tail ← match dflt with
          | some body => collectMemoryGuardsStmts? body
          | none => some []
        some (head ++ branches ++ tail)
    | .forLoop init c post body => do
        let initGuards ← collectMemoryGuardsStmts? init
        let condGuards ← collectMemoryGuardsExpr? c
        let postGuards ← collectMemoryGuardsStmts? post
        let bodyGuards ← collectMemoryGuardsStmts? body
        some (initGuards ++ condGuards ++ postGuards ++ bodyGuards)
    | .break | .continue | .leave => some []
    termination_by s => 2 * sizeOf s

  def collectMemoryGuardsStmts? : Block Op → Option (List Nat)
    | [] => some []
    | s :: rest => do
        let head ← collectMemoryGuardsStmt? s
        let tail ← collectMemoryGuardsStmts? rest
        some (head ++ tail)
    termination_by ss => 2 * sizeOf ss + 1

  def collectMemoryGuardsCases? : List (Literal × Block Op) → Option (List Nat)
    | [] => some []
    | (_, body) :: rest => do
        let head ← collectMemoryGuardsStmts? body
        let tail ← collectMemoryGuardsCases? rest
        some (head ++ tail)
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

mutual
  def declaredStmt : Stmt Op → List Ident
    | .block body => declaredStmts body
    | .funDef _ ps rs body => ps ++ rs ++ declaredStmts body
    | .letDecl xs _ => xs
    | .cond _ body => declaredStmts body
    | .switch _ cases dflt => declaredCases cases ++
        match dflt with
        | some body => declaredStmts body
        | none => []
    | .forLoop init _ post body =>
        declaredStmts init ++ declaredStmts post ++ declaredStmts body
    | _ => []
    termination_by s => 2 * sizeOf s

  def declaredStmts : Block Op → List Ident
    | [] => []
    | s :: rest => declaredStmt s ++ declaredStmts rest
    termination_by ss => 2 * sizeOf ss + 1

  def declaredCases : List (Literal × Block Op) → List Ident
    | [] => []
    | (_, body) :: rest => declaredStmts body ++ declaredCases rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

end YulEvmCompiler.Optimizer.MemorySpill
