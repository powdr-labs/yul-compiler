import YulEvmCompiler.Optimizer.Implementation.InlineHelpers
import YulEvmCompiler.ObjectResolve
set_option warningAsError true
/-!
# Resolution congruence for the Core-backed helper inliner

Object-layout resolution (`resolveForLayoutStmts`) rewrites
`dataoffset`/`datasize` applications into number literals. The inliner's
resolution-stable mode (`litOK := false`) classifies only helpers whose bodies
read variables and accepts only variable arguments — shapes resolution can
neither create nor destroy — so the transform *commutes* with resolution:

```
resolveForLayoutStmts L (inlineHelpersStmts false static b) =
  inlineHelpersStmts false (resolveLayoutFuns L static) (resolveForLayoutStmts L b)
```

This is the bridge the object pipeline needs: soundness of the pass on the
*resolved* program transports across this equality to the run of the resolved
*optimized* program under the same layout.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open YulEvmCompiler.Optimizer.Core (Ctx Term Value Var Args PureOp
  isValueExpr isVarExpr)

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-! ## Resolving declarations and scope stacks -/

def resolveLayoutDecl (L : Layout) (decl : FDecl D) : FDecl D :=
  { decl with body := resolveForLayoutStmts L decl.body }

def resolveLayoutScope (L : Layout) (scope : FScope D) : FScope D :=
  scope.map fun entry => (entry.1, resolveLayoutDecl L entry.2)

def resolveLayoutFuns (L : Layout) (funs : FunEnv D) : FunEnv D :=
  funs.map (resolveLayoutScope L)

/-! ## Resolution's image on the variable fragment -/

private theorem resolveForLayoutExpr_eq_var_iff (L : Layout) (e : Expr Op)
    (x : Ident) : resolveForLayoutExpr L e = .var x ↔ e = .var x := by
  cases e <;> simp only [resolveForLayoutExpr, Expr.var.injEq, reduceCtorEq];
    split <;> simp_all

/-- A builtin in resolution's image comes from the same builtin ordinarily
resolved (the special `dataoffset`/`datasize` arms produce literals). -/
private theorem resolveForLayoutExpr_eq_builtin_inv (L : Layout) {e : Expr Op}
    {op : Op} {es' : List (Expr Op)}
    (h : resolveForLayoutExpr L e = .builtin op es') :
    ∃ es, e = .builtin op es ∧ es' = resolveForLayoutExprs L es := by
  cases e with
  | lit l => simp [resolveForLayoutExpr] at h
  | var x => simp [resolveForLayoutExpr] at h
  | call fn args => simp [resolveForLayoutExpr] at h
  | builtin op0 args0 =>
      simp only [resolveForLayoutExpr] at h
      split at h
      · cases h
      · cases h
      · injection h with hop hargs
        subst hop
        exact ⟨args0, rfl, hargs.symm⟩

private theorem resolveForLayoutExpr_builtin_ordinary (L : Layout) (op : Op)
    (args : List (Expr Op)) (h : ∀ name, args ≠ [.lit (.string name)]) :
    resolveForLayoutExpr L (.builtin op args) =
      .builtin op (resolveForLayoutExprs L args) := by
  unfold resolveForLayoutExpr
  split <;> simp_all

/-- Resolution preserves var-shapedness in both directions. -/
private theorem isVarExpr_resolve (L : Layout) (e : Expr Op) :
    isVarExpr (resolveForLayoutExpr L e) = isVarExpr e := by
  cases e with
  | lit l => rfl
  | var x => rfl
  | call fn args => rfl
  | builtin op args =>
      simp only [resolveForLayoutExpr]
      split <;> rfl

/-- Resolution preserves list length. -/
private theorem resolveForLayoutExprs_length (L : Layout) (es : List (Expr Op)) :
    (resolveForLayoutExprs L es).length = es.length := by
  induction es with
  | nil => rfl
  | cons e rest ih => simp [resolveForLayoutExprs, ih]

/-- Variables are fixed by resolution, elementwise. -/
private theorem resolveForLayoutExprs_vars_fixed (L : Layout) {es : List (Expr Op)}
    (h : ∀ e ∈ es, isVarExpr e = true) : resolveForLayoutExprs L es = es := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
      have he := h e (by simp)
      have hee : resolveForLayoutExpr L e = e := by
        cases e <;> simp [isVarExpr] at he ⊢
        rfl
      rw [resolveForLayoutExprs, hee, ih (fun e' h' => h e' (by simp [h']))]

/-- A var-only list in resolution's image equals its pre-image. -/
private theorem resolveForLayoutExprs_eq_vars_inv (L : Layout)
    {es es' : List (Expr Op)}
    (h : resolveForLayoutExprs L es = es') (hvars : ∀ e ∈ es', isVarExpr e = true) :
    es = es' := by
  induction es generalizing es' with
  | nil => rw [← h]; rfl
  | cons e rest ih =>
      rw [resolveForLayoutExprs] at h
      subst h
      have hv := hvars (resolveForLayoutExpr L e) (by simp)
      rw [isVarExpr_resolve] at hv
      have he : resolveForLayoutExpr L e = e := by
        cases e <;> simp [isVarExpr] at hv ⊢
        rfl
      rw [he]
      have := ih (es' := resolveForLayoutExprs L rest) rfl
        (fun e' h' => hvars e' (by simp [h']))
      rw [← this]

/-! ## Classified bodies are resolution-fixed -/

/-- The emitted body of a vars-only term is fixed by resolution. -/
theorem emit_resolve_fixed (L : Layout) {Γ : Ctx} {tm : Term Γ 1}
    (hvars : tm.argsVarsOnly = true) :
    resolveForLayoutExpr L tm.emit = tm.emit := by
  cases tm with
  | atom value =>
      cases value with
      | var ref => rfl
      | lit l => simp [Core.Term.argsVarsOnly, Core.Value.isVar] at hvars
  | builtin op targs =>
      have hall : ∀ e ∈ targs.emit, isVarExpr e = true := by
        intro e he
        rw [Core.Args.emit] at he
        obtain ⟨value, hvmem, rfl⟩ := List.mem_map.mp he
        rw [Core.Term.argsVarsOnly] at hvars
        have := List.all_eq_true.mp hvars value hvmem
        cases value with
        | var ref => rfl
        | lit l => simp [Core.Value.isVar] at this
      have hnostr : ∀ name, targs.emit ≠ [.lit (.string name)] := by
        intro name heq
        have := hall (.lit (.string name)) (by rw [heq]; simp)
        simp [isVarExpr] at this
      show resolveForLayoutExpr L (.builtin op.toOp targs.emit) =
        Expr.builtin op.toOp targs.emit
      rw [resolveForLayoutExpr_builtin_ordinary L _ _ hnostr,
        resolveForLayoutExprs_vars_fixed L hall]

/-- A vars-only emitted body in resolution's image equals its pre-image. -/
theorem emit_resolve_inv (L : Layout) {Γ : Ctx} {tm : Term Γ 1}
    (hvars : tm.argsVarsOnly = true) {e : Expr Op}
    (h : resolveForLayoutExpr L e = tm.emit) : e = tm.emit := by
  cases tm with
  | atom value =>
      cases value with
      | var ref => exact (resolveForLayoutExpr_eq_var_iff L e ref.name).mp h
      | lit l => simp [Core.Term.argsVarsOnly, Core.Value.isVar] at hvars
  | builtin op targs =>
      have hall : ∀ e' ∈ targs.emit, isVarExpr e' = true := by
        intro e' he'
        rw [Core.Args.emit] at he'
        obtain ⟨value, hvmem, rfl⟩ := List.mem_map.mp he'
        rw [Core.Term.argsVarsOnly] at hvars
        have := List.all_eq_true.mp hvars value hvmem
        cases value with
        | var ref => rfl
        | lit l => simp [Core.Value.isVar] at this
      obtain ⟨es, rfl, hes⟩ := resolveForLayoutExpr_eq_builtin_inv L h
      have hes' : es = targs.emit := resolveForLayoutExprs_eq_vars_inv L hes.symm hall
      rw [hes']
      rfl

/-! ## Classification is resolution-stable -/

private theorem resolveForLayoutStmts_eq_assign_iff (L : Layout)
    (body : Block Op) (vars : List Ident) (e' : Expr Op) :
    resolveForLayoutStmts L body = [.assign vars e'] ↔
      ∃ e, body = [.assign vars e] ∧ resolveForLayoutExpr L e = e' := by
  cases body with
  | nil => simp
  | cons stmt rest =>
      cases rest with
      | cons s2 r2 =>
          simp
      | nil =>
          cases stmt <;> simp [eq_comm]

/-- Helper classification (resolution-stable mode) commutes with resolving
the declaration body. -/
theorem helper?_resolve (L : Layout) (decl : FDecl D) :
    helper? (calls := calls) (creates := creates) false (resolveLayoutDecl L decl) =
      helper? (calls := calls) (creates := creates) false decl := by
  cases hcl : helper? (calls := calls) (creates := creates) false decl with
  | some h =>
      obtain ⟨hdecl, hvars⟩ := helper?_shape hcl
      have hvars' : h.term.argsVarsOnly = true := by simpa using hvars
      have hfix : resolveLayoutDecl L decl = decl := by
        rw [hdecl]
        unfold resolveLayoutDecl
        simp only [FDecl.mk.injEq, true_and]
        show resolveForLayoutStmts L [.assign [h.ret] h.term.emit] =
          [Stmt.assign [h.ret] h.term.emit]
        rw [(resolveForLayoutStmts_eq_assign_iff L _ _ _).mpr
          ⟨h.term.emit, rfl, emit_resolve_fixed L hvars'⟩]
      rw [hfix, hcl]
  | none =>
      cases hcl' : helper? (calls := calls) (creates := creates) false
          (resolveLayoutDecl L decl) with
      | none => rfl
      | some h' =>
          obtain ⟨hdecl', hvars'⟩ := helper?_shape hcl'
          have hvars'' : h'.term.argsVarsOnly = true := by simpa using hvars'
          rcases decl with ⟨params0, rets0, body0⟩
          unfold resolveLayoutDecl at hdecl'
          injection hdecl' with hp hr hb
          have hp' : params0 = h'.params := hp
          have hr' : rets0 = [h'.ret] := hr
          have hb' : resolveForLayoutStmts L body0 =
              [.assign [h'.ret] h'.term.emit] := hb
          obtain ⟨e0, hbody0, he0⟩ :=
            (resolveForLayoutStmts_eq_assign_iff L body0 [h'.ret] h'.term.emit).mp hb'
          have he0' : e0 = h'.term.emit := emit_resolve_inv L hvars'' he0
          have hdecl0 : (⟨params0, rets0, body0⟩ : FDecl D) =
              ⟨h'.params, [h'.ret], [.assign [h'.ret] h'.term.emit]⟩ := by
            rw [hp', hr', hbody0, he0']
          rw [hdecl0] at hcl
          have hres : resolveLayoutDecl L
              (⟨h'.params, [h'.ret], [.assign [h'.ret] h'.term.emit]⟩ : FDecl D) =
              ⟨h'.params, [h'.ret], [.assign [h'.ret] h'.term.emit]⟩ := by
            unfold resolveLayoutDecl
            simp only [FDecl.mk.injEq, true_and]
            show resolveForLayoutStmts L [.assign [h'.ret] h'.term.emit] =
              [Stmt.assign [h'.ret] h'.term.emit]
            rw [(resolveForLayoutStmts_eq_assign_iff L _ _ _).mpr
              ⟨h'.term.emit, rfl, emit_resolve_fixed L hvars''⟩]
          rw [hdecl0, hres] at hcl'
          rw [hcl'] at hcl
          cases hcl

/-! ## Lexical lookup through the resolved scope stack -/

private theorem find?_resolveLayoutScope (L : Layout) (scope : FScope D)
    (fn : Ident) :
    (resolveLayoutScope L scope).find? (fun entry => entry.1 = fn) =
      (scope.find? (fun entry => entry.1 = fn)).map
        (fun entry => (entry.1, resolveLayoutDecl L entry.2)) := by
  rw [resolveLayoutScope, List.find?_map]
  rfl

theorem lookupFun_resolveLayoutFuns (L : Layout) (static : FunEnv D)
    (fn : Ident) :
    lookupFun (resolveLayoutFuns L static) fn =
      (lookupFun static fn).map fun found =>
        (resolveLayoutDecl L found.1, resolveLayoutFuns L found.2) := by
  induction static with
  | nil => rfl
  | cons scope outer ih =>
      simp only [resolveLayoutFuns, List.map_cons, lookupFun]
      rw [find?_resolveLayoutScope]
      cases h : scope.find? (fun entry => entry.1 = fn) with
      | none =>
          simp only [Option.map_none]
          simpa only [resolveLayoutFuns] using ih
      | some found =>
          rcases found with ⟨name, decl⟩
          simp

theorem resolveHelper_resolveLayoutFuns (L : Layout) (static : FunEnv D)
    (fn : Ident) :
    resolveHelper (calls := calls) (creates := creates) false
        (resolveLayoutFuns L static) fn =
      resolveHelper (calls := calls) (creates := creates) false static fn := by
  unfold resolveHelper
  rw [lookupFun_resolveLayoutFuns]
  cases lookupFun static fn with
  | none => rfl
  | some found =>
      rcases found with ⟨decl, closure⟩
      exact helper?_resolve L decl

theorem hoist_resolveLayout (L : Layout) (body : Block Op) :
    hoist D (resolveForLayoutStmts L body) =
      resolveLayoutScope L (hoist D body) := by
  induction body with
  | nil => simp [hoist, resolveLayoutScope]
  | cons stmt rest ih =>
      rw [resolveForLayoutStmts]
      cases stmt <;>
        rw [resolveForLayoutStmt.eq_def] <;>
        simp only [hoist, List.filterMap_cons, resolveLayoutScope,
          List.map_cons, resolveLayoutDecl] <;>
        simpa [hoist, resolveLayoutScope, resolveLayoutDecl] using ih

/-! ## The rewrite commutes with resolution -/

/-- The `argOK` condition in resolution-stable mode is var-shapedness. -/
private theorem argOK_false_iff (e : Expr Op) :
    argOK false e ↔ isVarExpr e = true := by
  unfold argOK
  constructor
  · rintro ⟨-, h⟩
    simpa using h
  · intro h
    exact ⟨Core.isVarExpr_value h, Or.inr h⟩

/-- First-occurrence lookup transports along elementwise resolution. -/
private theorem zip_find_resolve (L : Layout) (params : Ctx)
    (args : List (Expr Op)) (x : Ident) :
    (params.zip (resolveForLayoutExprs L args)).find? (fun entry => entry.1 = x) =
      ((params.zip args).find? (fun entry => entry.1 = x)).map
        (fun entry => (entry.1, resolveForLayoutExpr L entry.2)) := by
  induction params generalizing args with
  | nil => rfl
  | cons p rest ih =>
      cases args with
      | nil => rfl
      | cons a arest =>
          rw [resolveForLayoutExprs]
          by_cases hpx : p = x
          · subst hpx
            rw [List.zip_cons_cons, List.zip_cons_cons,
              List.find?_cons_of_pos (by simp), List.find?_cons_of_pos (by simp)]
            rfl
          · rw [List.zip_cons_cons, List.zip_cons_cons,
              List.find?_cons_of_neg (by simp [hpx]),
              List.find?_cons_of_neg (by simp [hpx])]
            exact ih arest

/-- Substitution commutes with resolution: substituting resolved arguments
equals resolving the substituted value. -/
private theorem substEmit_resolve (L : Layout) {params : Ctx}
    (args : List (Expr Op)) (value : Value params) :
    resolveForLayoutExpr L (Value.substEmit args value) =
      Value.substEmit (resolveForLayoutExprs L args) value := by
  cases value with
  | lit literal =>
      show resolveForLayoutExpr L (.lit literal) = Expr.lit literal
      rfl
  | var ref =>
      rw [Value.substEmit, Value.substEmit, zip_find_resolve]
      cases hfind : (params.zip args).find? (fun entry => entry.1 = ref.name) with
      | none => rfl
      | some entry => rfl

/-- The whole rewrite commutes with resolution, given resolved arguments. -/
private theorem rewriteCall_resolve (L : Layout) (h : Helper) (fn : Ident)
    (args : List (Expr Op)) :
    resolveForLayoutExpr L (rewriteCall false h fn args) =
      rewriteCall false h fn (resolveForLayoutExprs L args) := by
  rcases h.term_cases with ⟨ref, hterm⟩ | ⟨tarity, top, ttargs, hterm⟩
  · rw [rewriteCall_atom hterm, rewriteCall_atom hterm]
    cases args with
    | nil => rfl
    | cons a arest =>
        cases arest with
        | nil =>
            show resolveForLayoutExpr L (.builtin .add [a, .lit (.number 0)]) = _
            rw [resolveForLayoutExpr_builtin_ordinary L _ _ (by simp)]
            rfl
        | cons a2 arest2 => rfl
  · have hcondiff : (args.length = h.params.length ∧ (∀ e ∈ args, argOK false e)) ↔
        ((resolveForLayoutExprs L args).length = h.params.length ∧
          (∀ e ∈ resolveForLayoutExprs L args, argOK false e)) := by
      rw [resolveForLayoutExprs_length]
      constructor
      · rintro ⟨hlen, hargs⟩
        refine ⟨hlen, ?_⟩
        have hfix := resolveForLayoutExprs_vars_fixed L
          (fun e he => (argOK_false_iff e).mp (hargs e he))
        rw [hfix]
        exact hargs
      · rintro ⟨hlen, hargs⟩
        have hvars : ∀ e' ∈ resolveForLayoutExprs L args, isVarExpr e' = true :=
          fun e' he' => (argOK_false_iff e').mp (hargs e' he')
        have heq := resolveForLayoutExprs_eq_vars_inv L rfl hvars
        refine ⟨hlen, fun e he => hargs e ?_⟩
        rw [← heq]
        exact he
    by_cases hcond : args.length = h.params.length ∧ (∀ e ∈ args, argOK false e)
    · rw [rewriteCall_builtin_pos hterm hcond,
        rewriteCall_builtin_pos hterm (hcondiff.mp hcond)]
      have hfix := resolveForLayoutExprs_vars_fixed L
        (fun e he => (argOK_false_iff e).mp (hcond.2 e he))
      rw [hfix]
      have hsf := hterm ▸ h.stringFree
      have hnostr : ∀ name,
          ttargs.values.map (Core.Value.substEmit args) ≠ [.lit (.string name)] := by
        intro name heq
        have hmem : Expr.lit (.string name) ∈
            ttargs.values.map (Core.Value.substEmit args) := by
          rw [heq]; simp
        obtain ⟨value, hvmem, hveq⟩ := List.mem_map.mp hmem
        have hvsf : value.stringFree = true := by
          rw [Core.Term.stringFree] at hsf
          exact List.all_eq_true.mp hsf value hvmem
        have hval : isValueExpr (Core.Value.substEmit args value) = true :=
          Core.substEmit_isValue
            (fun e he => (hcond.2 e he).1) hvsf
        rw [hveq] at hval
        simp [isValueExpr] at hval
      show resolveForLayoutExpr L
          (.builtin top.toOp (ttargs.values.map (Core.Value.substEmit args))) = _
      rw [resolveForLayoutExpr_builtin_ordinary L _ _ hnostr]
      show Expr.builtin top.toOp
          (resolveForLayoutExprs L (ttargs.values.map (Core.Value.substEmit args))) = _
      congr 1
      have hmap : ∀ (values : List (Value h.params)),
          resolveForLayoutExprs L (values.map (Core.Value.substEmit args)) =
            values.map (Core.Value.substEmit args) := by
        intro values
        induction values with
        | nil => rfl
        | cons v rest ih =>
            rw [List.map_cons, resolveForLayoutExprs, ih,
              substEmit_resolve L args v, hfix]
      rw [hmap]
    · rw [rewriteCall_builtin_neg hterm hcond,
        rewriteCall_builtin_neg hterm (fun hc => hcond (hcondiff.mpr hc))]
      rfl

/-! ## The transform commutes with resolution -/

private theorem inlineHelpersExpr_eq_lit_iff {litOK : Bool} (static : FunEnv D)
    (e : Expr Op) (l : Literal) :
    inlineHelpersExpr litOK static e = .lit l ↔ e = .lit l := by
  constructor
  · exact inlineHelpersExpr_eq_lit
  · rintro rfl
    rfl

private theorem inlineHelpersArgs_eq_string_iff {litOK : Bool} (static : FunEnv D)
    (args : List (Expr Op)) (name : String) :
    inlineHelpersArgs litOK static args = [.lit (.string name)] ↔
      args = [.lit (.string name)] := by
  cases args with
  | nil => simp [inlineHelpersArgs]
  | cons e rest =>
      cases rest with
      | cons e2 r2 => simp [inlineHelpersArgs]
      | nil => simp [inlineHelpersArgs, inlineHelpersExpr_eq_lit_iff]

mutual
  theorem resolve_inlineHelpersExpr (L : Layout) (static : FunEnv D)
      (e : Expr Op) :
      resolveForLayoutExpr L (inlineHelpersExpr false static e) =
        inlineHelpersExpr false (resolveLayoutFuns L static)
          (resolveForLayoutExpr L e) := by
    cases e with
    | lit l => rfl
    | var x => rfl
    | call fn args =>
        have hargs := resolve_inlineHelpersArgs L static args
        rw [inlineHelpersExpr, resolveForLayoutExpr, inlineHelpersExpr,
          resolveHelper_resolveLayoutFuns]
        cases hres : resolveHelper (calls := calls) (creates := creates)
            false static fn with
        | none =>
            show resolveForLayoutExpr L
                (.call fn (inlineHelpersArgs false static args)) = _
            rw [resolveForLayoutExpr, hargs]
        | some hp =>
            show resolveForLayoutExpr L
                (rewriteCall false hp fn (inlineHelpersArgs false static args)) = _
            rw [rewriteCall_resolve, hargs]
    | builtin op args =>
        by_cases hspecial : ∃ name, args = [.lit (.string name)]
        · rcases hspecial with ⟨name, rfl⟩
          cases op <;> rfl
        · have hargs : ∀ name, args ≠ [.lit (.string name)] := by
            intro name heq
            exact hspecial ⟨name, heq⟩
          have hargs' : ∀ name,
              inlineHelpersArgs false static args ≠ [.lit (.string name)] := by
            intro name heq
            exact hargs name ((inlineHelpersArgs_eq_string_iff static args name).mp heq)
          rw [inlineHelpersExpr,
            resolveForLayoutExpr_builtin_ordinary L op _ hargs',
            resolve_inlineHelpersArgs,
            resolveForLayoutExpr_builtin_ordinary L op _ hargs,
            inlineHelpersExpr]

  theorem resolve_inlineHelpersArgs (L : Layout) (static : FunEnv D)
      (args : List (Expr Op)) :
      resolveForLayoutExprs L (inlineHelpersArgs false static args) =
        inlineHelpersArgs false (resolveLayoutFuns L static)
          (resolveForLayoutExprs L args) := by
    cases args with
    | nil => rfl
    | cons e rest =>
        rw [inlineHelpersArgs, resolveForLayoutExprs,
          resolveForLayoutExprs, inlineHelpersArgs,
          resolve_inlineHelpersExpr, resolve_inlineHelpersArgs]
end

mutual
  theorem resolve_inlineHelpersStmt (L : Layout) (static : FunEnv D)
      (stmt : Stmt Op) :
      resolveForLayoutStmt L (inlineHelpersStmt false static stmt) =
        inlineHelpersStmt false (resolveLayoutFuns L static)
          (resolveForLayoutStmt L stmt) := by
    cases stmt with
    | block body =>
        rw [inlineHelpersStmt, resolveForLayoutStmt,
          resolveForLayoutStmt, inlineHelpersStmt,
          resolve_inlineHelpersStmts]
        simp only [resolveLayoutFuns, List.map_cons, hoist_resolveLayout]
    | funDef fn params rets body =>
        rw [inlineHelpersStmt, resolveForLayoutStmt,
          resolveForLayoutStmt, inlineHelpersStmt,
          resolve_inlineHelpersStmts]
        simp only [resolveLayoutFuns, List.map_cons, hoist_resolveLayout]
    | letDecl vars value =>
        cases value <;>
          simp [inlineHelpersStmt, resolve_inlineHelpersExpr]
    | assign vars value =>
        simp [inlineHelpersStmt, resolve_inlineHelpersExpr]
    | cond c body =>
        rw [inlineHelpersStmt, resolveForLayoutStmt,
          resolveForLayoutStmt, inlineHelpersStmt,
          resolve_inlineHelpersExpr, resolve_inlineHelpersStmts]
        simp only [resolveLayoutFuns, List.map_cons, hoist_resolveLayout]
    | «switch» c cases dflt =>
        cases dflt with
        | none =>
            simp only [inlineHelpersStmt, resolveForLayoutStmt,
              resolve_inlineHelpersExpr,
              resolve_inlineHelpersCases]
        | some body =>
            rw [inlineHelpersStmt, resolveForLayoutStmt,
              resolveForLayoutStmt, inlineHelpersStmt,
              resolve_inlineHelpersExpr, resolve_inlineHelpersCases,
              resolve_inlineHelpersStmts]
            simp only [resolveLayoutFuns, List.map_cons, hoist_resolveLayout]
    | forLoop init c post body =>
        simp only [inlineHelpersStmt, resolveForLayoutStmt]
        rw [resolve_inlineHelpersStmts, resolve_inlineHelpersExpr,
          resolve_inlineHelpersStmts, resolve_inlineHelpersStmts]
        simp only [resolveLayoutFuns, List.map_cons, hoist_resolveLayout]
    | exprStmt e =>
        simp [inlineHelpersStmt, resolve_inlineHelpersExpr]
    | «break» => simp [inlineHelpersStmt]
    | «continue» => simp [inlineHelpersStmt]
    | «leave» => simp [inlineHelpersStmt]

  theorem resolve_inlineHelpersStmts (L : Layout) (static : FunEnv D)
      (stmts : Block Op) :
      resolveForLayoutStmts L (inlineHelpersStmts false static stmts) =
        inlineHelpersStmts false (resolveLayoutFuns L static)
          (resolveForLayoutStmts L stmts) := by
    cases stmts with
    | nil => simp [inlineHelpersStmts]
    | cons stmt rest =>
        rw [inlineHelpersStmts, resolveForLayoutStmts,
          resolve_inlineHelpersStmt, resolve_inlineHelpersStmts,
          resolveForLayoutStmts, inlineHelpersStmts]

  theorem resolve_inlineHelpersCases (L : Layout) (static : FunEnv D)
      (cases : List (Literal × Block Op)) :
      resolveForLayoutCases L (inlineHelpersCases false static cases) =
        inlineHelpersCases false (resolveLayoutFuns L static)
          (resolveForLayoutCases L cases) := by
    cases cases with
    | nil => simp [inlineHelpersCases, resolveForLayoutCases]
    | cons head rest =>
        rcases head with ⟨lit, body⟩
        rw [inlineHelpersCases, resolveForLayoutCases,
          resolve_inlineHelpersStmts, resolve_inlineHelpersCases,
          resolveForLayoutCases, inlineHelpersCases]
        simp only [resolveLayoutFuns, List.map_cons, hoist_resolveLayout]
end

theorem resolve_inlineHelpersBlock (L : Layout) (outer : FunEnv D)
    (body : Block Op) :
    resolveForLayoutStmts L (inlineHelpersBlock false outer body) =
      inlineHelpersBlock false (resolveLayoutFuns L outer)
        (resolveForLayoutStmts L body) := by
  rw [inlineHelpersBlock, resolve_inlineHelpersStmts, inlineHelpersBlock]
  simp only [resolveLayoutFuns, List.map_cons, hoist_resolveLayout]

theorem resolve_inlineHelpersBlock_nil (L : Layout) (body : Block Op) :
    resolveForLayoutStmts L (inlineHelpersBlock false ([] : FunEnv D) body) =
      inlineHelpersBlock false ([] : FunEnv D) (resolveForLayoutStmts L body) := by
  simpa [resolveLayoutFuns] using resolve_inlineHelpersBlock L ([] : FunEnv D) body

end YulEvmCompiler.Optimizer
