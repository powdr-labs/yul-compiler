import YulEvmCompiler.Optimizer.Implementation.InlineIdentity
import YulEvmCompiler.ObjectResolve

set_option warningAsError true

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

def resolveIdentityDecl (L : Layout) (decl : FDecl D) : FDecl D :=
  { decl with body := resolveForLayoutStmts L decl.body }

def resolveIdentityScope (L : Layout) (scope : FScope D) : FScope D :=
  scope.map fun entry => (entry.1, resolveIdentityDecl L entry.2)

def resolveIdentityFuns (L : Layout) (funs : FunEnv D) : FunEnv D :=
  funs.map (resolveIdentityScope L)

private theorem resolveForLayoutExpr_eq_var_iff (L : Layout) (e : Expr Op)
    (x : Ident) : resolveForLayoutExpr L e = .var x ↔ e = .var x := by
  cases e <;> simp only [resolveForLayoutExpr, Expr.var.injEq, reduceCtorEq];
    split <;> simp_all

private theorem exactIdentity_iff_shape (decl : FDecl D) :
    ExactIdentity decl ↔ ∃ param ret, decl =
      { params := [param], rets := [ret],
        body := [.assign [ret] (.var param)] } := by
  constructor
  · intro h
    exact exactIdentity_shape (exactIdentity?_eq_true.mpr h)
  · rintro ⟨param, ret, rfl⟩
    simp [ExactIdentity]

private theorem resolveForLayoutStmts_eq_identity_iff (L : Layout)
    (body : Block Op) (param ret : Ident) :
    resolveForLayoutStmts L body = [.assign [ret] (.var param)] ↔
      body = [.assign [ret] (.var param)] := by
  cases body with
  | nil => simp
  | cons stmt rest =>
      cases rest with
      | cons => simp
      | nil =>
          cases stmt <;> simp [resolveForLayoutExpr_eq_var_iff]

private theorem resolveIdentityDecl_eq_identity_iff (L : Layout)
    (decl : FDecl D) (param ret : Ident) :
    resolveIdentityDecl L decl =
        { params := [param], rets := [ret], body := [.assign [ret] (.var param)] } ↔
      decl =
        { params := [param], rets := [ret], body := [.assign [ret] (.var param)] } := by
  rcases decl with ⟨params, rets, body⟩
  simp only [resolveIdentityDecl, FDecl.mk.injEq]
  rw [resolveForLayoutStmts_eq_identity_iff]

theorem exactIdentity_resolveIdentityDecl (L : Layout) (decl : FDecl D) :
    exactIdentity? (resolveIdentityDecl L decl) = exactIdentity? decl := by
  rw [Bool.eq_iff_iff]
  simp only [exactIdentity?_eq_true, exactIdentity_iff_shape]
  constructor
  · rintro ⟨param, ret, h⟩
    exact ⟨param, ret, (resolveIdentityDecl_eq_identity_iff L decl param ret).mp h⟩
  · rintro ⟨param, ret, h⟩
    exact ⟨param, ret, (resolveIdentityDecl_eq_identity_iff L decl param ret).mpr h⟩

private theorem find?_resolveIdentityScope (L : Layout) (scope : FScope D)
    (fn : Ident) :
    (resolveIdentityScope L scope).find? (fun entry => entry.1 = fn) =
      (scope.find? (fun entry => entry.1 = fn)).map
        (fun entry => (entry.1, resolveIdentityDecl L entry.2)) := by
  rw [resolveIdentityScope, List.find?_map]
  rfl

theorem lookupFun_resolveIdentityFuns (L : Layout) (static : FunEnv D)
    (fn : Ident) :
    lookupFun (resolveIdentityFuns L static) fn =
      (lookupFun static fn).map fun found =>
        (resolveIdentityDecl L found.1, resolveIdentityFuns L found.2) := by
  induction static with
  | nil => rfl
  | cons scope outer ih =>
      simp only [resolveIdentityFuns, List.map_cons, lookupFun]
      rw [find?_resolveIdentityScope]
      cases h : scope.find? (fun entry => entry.1 = fn) with
      | none =>
          simp only [Option.map_none]
          simpa only [resolveIdentityFuns] using ih
      | some found =>
          rcases found with ⟨name, decl⟩
          simp

theorem resolvesIdentity_resolveIdentityFuns (L : Layout) (static : FunEnv D)
    (fn : Ident) :
    resolvesIdentity (resolveIdentityFuns L static) fn =
      resolvesIdentity static fn := by
  unfold resolvesIdentity
  rw [lookupFun_resolveIdentityFuns]
  cases lookupFun static fn with
  | none => rfl
  | some found =>
      rcases found with ⟨decl, closure⟩
      exact exactIdentity_resolveIdentityDecl L decl

theorem hoist_resolveIdentity (L : Layout) (body : Block Op) :
    hoist D (resolveForLayoutStmts L body) =
      resolveIdentityScope L (hoist D body) := by
  induction body with
  | nil => simp [hoist, resolveIdentityScope]
  | cons stmt rest ih =>
      rw [resolveForLayoutStmts]
      cases stmt <;>
        rw [resolveForLayoutStmt.eq_def] <;>
        simp only [hoist, List.filterMap_cons, resolveIdentityScope,
          List.map_cons, resolveIdentityDecl] <;>
        simpa [hoist, resolveIdentityScope, resolveIdentityDecl] using ih

private theorem inlineIdentityExpr_eq_lit_iff (static : FunEnv D)
    (e : Expr Op) (l : Literal) :
    inlineIdentityExpr static e = .lit l ↔ e = .lit l := by
  cases e with
  | lit => simp [inlineIdentityExpr]
  | var => simp [inlineIdentityExpr]
  | builtin => simp [inlineIdentityExpr]
  | call fn args =>
      rw [inlineIdentityExpr]
      cases inlineIdentityArgs static args with
      | nil => simp
      | cons arg rest =>
          cases rest with
          | cons => simp
          | nil =>
              by_cases h : resolvesIdentity static fn = true <;> simp [h]

private theorem inlineIdentityArgs_eq_string_iff (static : FunEnv D)
    (args : List (Expr Op)) (name : String) :
    inlineIdentityArgs static args = [.lit (.string name)] ↔
      args = [.lit (.string name)] := by
  cases args with
  | nil => simp [inlineIdentityArgs]
  | cons e rest =>
      cases rest with
      | cons => simp [inlineIdentityArgs]
      | nil => simp [inlineIdentityArgs, inlineIdentityExpr_eq_lit_iff]

private theorem resolveForLayoutExpr_builtin_ordinary (L : Layout) (op : Op)
    (args : List (Expr Op)) (h : ∀ name, args ≠ [.lit (.string name)]) :
    resolveForLayoutExpr L (.builtin op args) =
      .builtin op (resolveForLayoutExprs L args) := by
  unfold resolveForLayoutExpr
  split <;> simp_all

mutual
  theorem resolve_inlineIdentityExpr (L : Layout) (static : FunEnv D)
      (e : Expr Op) :
      resolveForLayoutExpr L (inlineIdentityExpr static e) =
        inlineIdentityExpr (resolveIdentityFuns L static)
          (resolveForLayoutExpr L e) := by
    cases e with
    | lit l => rfl
    | var x => rfl
    | call fn args =>
        have hargs := resolve_inlineIdentityArgs L static args
        rw [inlineIdentityExpr, resolveForLayoutExpr, inlineIdentityExpr,
          resolvesIdentity_resolveIdentityFuns]
        cases ha : inlineIdentityArgs static args with
        | nil =>
            rw [ha] at hargs
            rw [← hargs]
            rfl
        | cons arg rest =>
            cases rest with
            | nil =>
                rw [ha] at hargs
                rw [← hargs]
                by_cases hid : resolvesIdentity static fn = true <;>
                  simp [hid, resolveForLayoutExpr, resolveForLayoutExprs]
            | cons arg' rest =>
                rw [ha] at hargs
                rw [← hargs]
                rfl
    | builtin op args =>
        by_cases hspecial : ∃ name, args = [.lit (.string name)]
        · rcases hspecial with ⟨name, rfl⟩
          cases op <;> rfl
        · have hargs : ∀ name, args ≠ [.lit (.string name)] := by
            intro name heq
            exact hspecial ⟨name, heq⟩
          have hargs' : ∀ name,
              inlineIdentityArgs static args ≠ [.lit (.string name)] := by
            intro name heq
            exact hargs name ((inlineIdentityArgs_eq_string_iff static args name).mp heq)
          rw [inlineIdentityExpr,
            resolveForLayoutExpr_builtin_ordinary L op _ hargs',
            resolve_inlineIdentityArgs,
            resolveForLayoutExpr_builtin_ordinary L op _ hargs,
            inlineIdentityExpr]

  theorem resolve_inlineIdentityArgs (L : Layout) (static : FunEnv D)
      (args : List (Expr Op)) :
      resolveForLayoutExprs L (inlineIdentityArgs static args) =
        inlineIdentityArgs (resolveIdentityFuns L static)
          (resolveForLayoutExprs L args) := by
    cases args with
    | nil => rfl
    | cons e rest =>
        rw [inlineIdentityArgs, resolveForLayoutExprs,
          resolveForLayoutExprs, inlineIdentityArgs,
          resolve_inlineIdentityExpr, resolve_inlineIdentityArgs]
end

mutual
  theorem resolve_inlineIdentityStmt (L : Layout) (static : FunEnv D)
      (stmt : Stmt Op) :
      resolveForLayoutStmt L (inlineIdentityStmt static stmt) =
        inlineIdentityStmt (resolveIdentityFuns L static)
          (resolveForLayoutStmt L stmt) := by
    cases stmt with
    | block body =>
        rw [inlineIdentityStmt, resolveForLayoutStmt,
          resolveForLayoutStmt, inlineIdentityStmt,
          resolve_inlineIdentityStmts]
        simp only [resolveIdentityFuns, List.map_cons, hoist_resolveIdentity]
    | funDef fn params rets body =>
        rw [inlineIdentityStmt, resolveForLayoutStmt,
          resolveForLayoutStmt, inlineIdentityStmt,
          resolve_inlineIdentityStmts]
        simp only [resolveIdentityFuns, List.map_cons, hoist_resolveIdentity]
    | letDecl vars value =>
        cases value <;>
          simp [inlineIdentityStmt, resolve_inlineIdentityExpr]
    | assign vars value =>
        simp [inlineIdentityStmt, resolve_inlineIdentityExpr]
    | cond c body =>
        rw [inlineIdentityStmt, resolveForLayoutStmt,
          resolveForLayoutStmt, inlineIdentityStmt,
          resolve_inlineIdentityExpr, resolve_inlineIdentityStmts]
        simp only [resolveIdentityFuns, List.map_cons, hoist_resolveIdentity]
    | «switch» c cases dflt =>
        cases dflt with
        | none =>
            simp only [inlineIdentityStmt, resolveForLayoutStmt,
              resolve_inlineIdentityExpr,
              resolve_inlineIdentityCases]
        | some body =>
            rw [inlineIdentityStmt, resolveForLayoutStmt,
              resolveForLayoutStmt, inlineIdentityStmt,
              resolve_inlineIdentityExpr, resolve_inlineIdentityCases,
              resolve_inlineIdentityStmts]
            simp only [resolveIdentityFuns, List.map_cons, hoist_resolveIdentity]
    | forLoop init c post body =>
        simp only [inlineIdentityStmt, resolveForLayoutStmt]
        rw [resolve_inlineIdentityStmts, resolve_inlineIdentityExpr,
          resolve_inlineIdentityStmts, resolve_inlineIdentityStmts]
        simp only [resolveIdentityFuns, List.map_cons, hoist_resolveIdentity]
    | exprStmt e =>
        simp [inlineIdentityStmt, resolve_inlineIdentityExpr]
    | «break» => simp [inlineIdentityStmt]
    | «continue» => simp [inlineIdentityStmt]
    | «leave» => simp [inlineIdentityStmt]

  theorem resolve_inlineIdentityStmts (L : Layout) (static : FunEnv D)
      (stmts : Block Op) :
      resolveForLayoutStmts L (inlineIdentityStmts static stmts) =
        inlineIdentityStmts (resolveIdentityFuns L static)
          (resolveForLayoutStmts L stmts) := by
    cases stmts with
    | nil => simp [inlineIdentityStmts]
    | cons stmt rest =>
        rw [inlineIdentityStmts, resolveForLayoutStmts,
          resolve_inlineIdentityStmt, resolve_inlineIdentityStmts,
          resolveForLayoutStmts, inlineIdentityStmts]

  theorem resolve_inlineIdentityCases (L : Layout) (static : FunEnv D)
      (cases : List (Literal × Block Op)) :
      resolveForLayoutCases L (inlineIdentityCases static cases) =
        inlineIdentityCases (resolveIdentityFuns L static)
          (resolveForLayoutCases L cases) := by
    cases cases with
    | nil => simp [inlineIdentityCases, resolveForLayoutCases]
    | cons head rest =>
        rcases head with ⟨lit, body⟩
        rw [inlineIdentityCases, resolveForLayoutCases,
          resolve_inlineIdentityStmts, resolve_inlineIdentityCases,
          resolveForLayoutCases, inlineIdentityCases]
        simp only [resolveIdentityFuns, List.map_cons, hoist_resolveIdentity]
end

theorem resolve_inlineIdentityBlock (L : Layout) (outer : FunEnv D)
    (body : Block Op) :
    resolveForLayoutStmts L (inlineIdentityBlock outer body) =
      inlineIdentityBlock (resolveIdentityFuns L outer)
        (resolveForLayoutStmts L body) := by
  rw [inlineIdentityBlock, resolve_inlineIdentityStmts, inlineIdentityBlock]
  simp only [resolveIdentityFuns, List.map_cons, hoist_resolveIdentity]

theorem resolve_inlineIdentityBlock_nil (L : Layout) (body : Block Op) :
    resolveForLayoutStmts L (inlineIdentityBlock ([] : FunEnv D) body) =
      inlineIdentityBlock ([] : FunEnv D) (resolveForLayoutStmts L body) := by
  simpa [resolveIdentityFuns] using resolve_inlineIdentityBlock L ([] : FunEnv D) body

end YulEvmCompiler.Optimizer
