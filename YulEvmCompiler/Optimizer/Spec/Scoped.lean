import YulSemantics.Equiv

/-!
# YulEvmCompiler.Optimizer.Spec.Scoped

**Well-scopedness** of a Yul program: every *variable read* refers to a variable
that is in scope at that point. This is the precondition under which the optimizer
passes are certified (`Spec/Pass.lean`'s `Sound`).

Why it is part of the spec. Binding-removing rewrites (dead-`let` elimination,
copy-propagation-then-drop) are unsound against *arbitrary* variable
environments: the pointwise `EquivBlock` `↔` quantifies over environments where a
read is unbound, in which the original program is stuck but the reduced one runs —
so the two are not equivalent. Restricting to **well-scoped** programs removes
exactly that pathology (a read of an in-scope variable always succeeds), which is
what makes aggressive dead-code elimination sound. Every real Yul program — and
in particular everything the frontend/`solc` emits — is well-scoped, so the
precondition costs no real coverage.

The judgment tracks only *variables* (the `VEnv`), which is all a binding-removing
pass needs; it deliberately does not check that called functions are declared
(function calls are never removed, and are side-effecting, so the passes never
rely on them succeeding). Scoping follows Yul's rules exactly:

* a `let` extends the scope for the *rest of its block* (`declVars`);
* `block`/`if`/`switch`/`for` bodies are inner scopes that do not leak;
* a `for`-loop's `init` declarations are visible in its `cond`/`post`/`body`;
* a `funDef` body sees only its `params`/`rets` (Yul functions do not close over
  enclosing variables — the semantics runs a call in `params ++ rets` only).
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics

variable {Op : Type}

/-- The variables a statement declares in its *enclosing* scope. Only `let` leaks
its variables to the rest of the block; blocks/loops/switch introduce inner scopes
that do not leak, and a `funDef` introduces a function, not a variable. -/
def declVars : Stmt Op → List Ident
  | .letDecl vars _ => vars
  | _ => []

/-- All variables declared at the top level of a statement sequence. -/
def declVarsList (ss : List (Stmt Op)) : List Ident := ss.flatMap declVars

/-! ### The scoping judgment -/

mutual
/-- Every variable read in `e` is in scope (`∈ Γ`). -/
def ScopedExpr (Γ : List Ident) : Expr Op → Prop
  | .lit _ => True
  | .var x => x ∈ Γ
  | .builtin _ args => ScopedArgs Γ args
  | .call _ args => ScopedArgs Γ args
/-- Every variable read in an argument list is in scope. -/
def ScopedArgs (Γ : List Ident) : List (Expr Op) → Prop
  | [] => True
  | e :: rest => ScopedExpr Γ e ∧ ScopedArgs Γ rest
end

mutual
/-- The statement is well-scoped with in-scope variables `Γ`. -/
def ScopedStmt (Γ : List Ident) : Stmt Op → Prop
  | .block body => ScopedStmts Γ body
  | .funDef _ ps rs body => ScopedStmts (rs ++ ps) body
  | .letDecl _ val => ScopedOptExpr Γ val
  | .assign vars val => (∀ x ∈ vars, x ∈ Γ) ∧ ScopedExpr Γ val
  | .cond c body => ScopedExpr Γ c ∧ ScopedStmts Γ body
  | .switch c cases dflt => ScopedExpr Γ c ∧ ScopedCases Γ cases ∧ ScopedOptBlock Γ dflt
  | .forLoop init c post body =>
      ScopedStmts Γ init ∧ ScopedExpr (declVarsList init ++ Γ) c ∧
        ScopedStmts (declVarsList init ++ Γ) post ∧ ScopedStmts (declVarsList init ++ Γ) body
  | .exprStmt e => ScopedExpr Γ e
  | .«break» => True
  | .«continue» => True
  | .leave => True
/-- The statement sequence is well-scoped, threading each `let`'s declarations
into the scope of the rest. -/
def ScopedStmts (Γ : List Ident) : List (Stmt Op) → Prop
  | [] => True
  | s :: rest => ScopedStmt Γ s ∧ ScopedStmts (declVars s ++ Γ) rest
/-- Every `switch` case body is well-scoped. -/
def ScopedCases (Γ : List Ident) : List (Literal × List (Stmt Op)) → Prop
  | [] => True
  | (_, b) :: rest => ScopedStmts Γ b ∧ ScopedCases Γ rest
/-- An optional initialiser expression is well-scoped. -/
def ScopedOptExpr (Γ : List Ident) : Option (Expr Op) → Prop
  | none => True
  | some e => ScopedExpr Γ e
/-- An optional block (a `switch` default) is well-scoped. -/
def ScopedOptBlock (Γ : List Ident) : Option (List (Stmt Op)) → Prop
  | none => True
  | some b => ScopedStmts Γ b
end

/-- A top-level program (block) is **well-scoped**: it reads only variables it
declares, starting from the empty environment `Run` executes it in. -/
def WellScoped (b : Block Op) : Prop := ScopedStmts [] b

end YulEvmCompiler.Optimizer
