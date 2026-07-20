import YulEvmCompiler.Optimizer.Implementation.InlineCallsSound
import YulEvmCompiler.Optimizer.Implementation.PropagateResolve
import YulEvmCompiler.Optimizer.Implementation.ResolveCongr
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
/-!
# YulEvmCompiler.Optimizer.Implementation.InlineCallsResolve

**Closure of the inlining relation under layout resolution** — the
object-path bridge for `InlineCalls`, in the `PropagateResolve` style: layout
resolution rewrites `dataoffset`/`datasize` *builtins* (never `.call` nodes)
into number literals, so every classification and side condition of the pass
is resolution-invariant — variables, call occurrences, scopedness, arities,
and the shadow checks are all untouched — and resolving both sides of an
`IcRel` pair (with the declaration context resolved pointwise) stays related.
The payoff is `resolveInlineCallsBlock_equiv`, the per-stage congruence the
iterated object pipeline composes.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### Resolution invariance of the syntactic conditions -/

/-- Resolve a tracked declaration. -/
def resolveIDecl (L : Layout) (d : IDecl) : IDecl :=
  ⟨d.ps, d.rs, resolveForLayoutStmts L d.ss⟩

/-- Resolve a declaration context pointwise. -/
def resolveDelta (L : Layout) (Δ : DEnv) : DEnv :=
  Δ.map (fun p => (p.1, resolveIDecl L p.2))

mutual

/-- Resolution never changes the variables an expression reads. -/
theorem exprVars_resolve (L : Layout) : ∀ e : Expr Op,
    exprVars (resolveForLayoutExpr L e) = exprVars e
  | .lit l => rfl
  | .var x => rfl
  | .builtin op args => by
      simp only [resolveForLayoutExpr]
      split
      · simp [exprVars, varsList]
      · simp [exprVars, varsList]
      · show varsList (resolveForLayoutExprs L args) = varsList args
        exact varsList_resolve L args
  | .call f args => by
      show varsList (resolveForLayoutExprs L args) = varsList args
      exact varsList_resolve L args

/-- Resolution never changes the variables an argument list reads. -/
theorem varsList_resolve (L : Layout) : ∀ es : List (Expr Op),
    varsList (resolveForLayoutExprs L es) = varsList es
  | [] => rfl
  | e :: rest => by
      show exprVars (resolveForLayoutExpr L e) ++ _ = _
      rw [exprVars_resolve L e, varsList_resolve L rest]
      rfl

end

mutual

/-- Resolution never creates or removes a `.call`. -/
theorem exprHasCall_resolve (L : Layout) : ∀ e : Expr Op,
    exprHasCall (resolveForLayoutExpr L e) = exprHasCall e
  | .lit l => rfl
  | .var x => rfl
  | .builtin op args => by
      simp only [resolveForLayoutExpr]
      split
      · simp [exprHasCall, argsHaveCall]
      · simp [exprHasCall, argsHaveCall]
      · show argsHaveCall (resolveForLayoutExprs L args) = argsHaveCall args
        exact argsHaveCall_resolve L args
  | .call f args => rfl

/-- Resolution never creates or removes a `.call` in an argument list. -/
theorem argsHaveCall_resolve (L : Layout) : ∀ es : List (Expr Op),
    argsHaveCall (resolveForLayoutExprs L es) = argsHaveCall es
  | [] => rfl
  | e :: rest => by
      show (exprHasCall (resolveForLayoutExpr L e) || _) = _
      rw [exprHasCall_resolve L e, argsHaveCall_resolve L rest]
      rfl

end

/-- Resolution preserves the scoped-expression check. -/
theorem scopedExpr_resolve (L : Layout) (bound : List Ident) (e : Expr Op) :
    scopedExpr bound (resolveForLayoutExpr L e) = scopedExpr bound e := by
  unfold scopedExpr
  rw [exprHasCall_resolve, exprVars_resolve]

mutual

/-- Resolution preserves the scoped-statement check (and its binding context). -/
theorem scopedStmt_resolve (L : Layout) (bound : List Ident) :
    ∀ s : Stmt Op, scopedStmt bound (resolveForLayoutStmt L s) = scopedStmt bound s
  | .letDecl xs none => by
      simp only [resolveForLayoutStmt, Option.map_none, scopedStmt]
  | .letDecl xs (some e) => by
      simp only [resolveForLayoutStmt, Option.map_some, scopedStmt,
        scopedExpr_resolve]
  | .assign xs e => by
      simp only [resolveForLayoutStmt, scopedStmt, scopedExpr_resolve]
  | .exprStmt e => by
      simp only [resolveForLayoutStmt, scopedStmt, scopedExpr_resolve]
  | .block body => by
      simp only [resolveForLayoutStmt, scopedStmt,
        scopedStmts_resolve L bound body]
  | .cond c body => by
      simp only [resolveForLayoutStmt, scopedStmt, scopedExpr_resolve,
        scopedStmts_resolve L bound body]
  | .switch c cases dflt => by
      cases dflt with
      | none =>
          simp only [resolveForLayoutStmt, scopedStmt, scopedExpr_resolve,
            scopedCases_resolve L bound cases]
      | some body =>
          simp only [resolveForLayoutStmt, scopedStmt, scopedExpr_resolve,
            scopedCases_resolve L bound cases, scopedDflt,
            scopedStmts_resolve L bound body]
          rfl
  | .funDef n ps rs body => by simp only [resolveForLayoutStmt, scopedStmt]
  | .forLoop init c post body => by simp only [resolveForLayoutStmt, scopedStmt]
  | .break => by simp only [resolveForLayoutStmt, scopedStmt]
  | .continue => by simp only [resolveForLayoutStmt, scopedStmt]
  | .leave => by simp only [resolveForLayoutStmt, scopedStmt]

/-- Resolution preserves the scoped-sequence check. -/
theorem scopedStmts_resolve (L : Layout) (bound : List Ident) :
    ∀ ss : List (Stmt Op),
      scopedStmts bound (resolveForLayoutStmts L ss) = scopedStmts bound ss
  | [] => by simp only [resolveForLayoutStmts, scopedStmts]
  | s :: rest => by
      rw [show resolveForLayoutStmts L (s :: rest) =
        resolveForLayoutStmt L s :: resolveForLayoutStmts L rest from by
          simp only [resolveForLayoutStmts]]
      simp only [scopedStmts]
      rw [scopedStmt_resolve L bound s]
      cases scopedStmt bound s with
      | none => rfl
      | some bound' =>
          show scopedStmts bound' (resolveForLayoutStmts L rest) = _
          rw [scopedStmts_resolve L bound' rest]

/-- Resolution preserves the scoped-cases check. -/
theorem scopedCases_resolve (L : Layout) (bound : List Ident) :
    ∀ cs : List (Literal × Block Op),
      scopedCases bound (resolveForLayoutCases L cs) = scopedCases bound cs
  | [] => by simp only [resolveForLayoutCases, scopedCases]
  | (l, b) :: rest => by
      rw [show resolveForLayoutCases L ((l, b) :: rest) =
        (l, resolveForLayoutStmts L b) :: resolveForLayoutCases L rest from by
          simp only [resolveForLayoutCases]]
      simp only [scopedCases]
      rw [scopedStmts_resolve L bound b, scopedCases_resolve L bound rest]

end

/-- Resolution of statement sequences distributes over append. -/
theorem resolveForLayoutStmts_append (L : Layout) : ∀ a b : List (Stmt Op),
    resolveForLayoutStmts L (a ++ b) =
      resolveForLayoutStmts L a ++ resolveForLayoutStmts L b
  | [], b => by simp only [resolveForLayoutStmts, List.nil_append]
  | s :: rest, b => by
      rw [show (s :: rest) ++ b = s :: (rest ++ b) from rfl]
      simp only [resolveForLayoutStmts]
      rw [resolveForLayoutStmts_append L rest b]
      rfl

/-- Resolution of a cons. -/
theorem resolveForLayoutStmts_cons (L : Layout) (s : Stmt Op)
    (rest : List (Stmt Op)) :
    resolveForLayoutStmts L (s :: rest) =
      resolveForLayoutStmt L s :: resolveForLayoutStmts L rest := by
  simp only [resolveForLayoutStmts]

/-- Resolution keeps argument-list length. -/
theorem resolveForLayoutExprs_len (L : Layout) : ∀ es : List (Expr Op),
    (resolveForLayoutExprs L es).length = es.length
  | [] => rfl
  | e :: rest => by
      show _ + 1 = _ + 1
      rw [resolveForLayoutExprs_len L rest]

/-- Dropping a trailing `leave`, concat forms. -/
theorem dropTrailingLeave_concat_leave (ss : List (Stmt Op)) :
    dropTrailingLeave (ss ++ [.leave]) = ss := by
  unfold dropTrailingLeave
  rw [List.getLast?_concat]
  exact List.dropLast_concat

/-- A non-`leave` last statement keeps the body intact. -/
theorem dropTrailingLeave_concat_other {s : Stmt Op} (h : ¬s = .leave)
    (ss : List (Stmt Op)) :
    dropTrailingLeave (ss ++ [s]) = ss ++ [s] := by
  unfold dropTrailingLeave
  rw [List.getLast?_concat]
  cases s with
  | «leave» => exact absurd rfl h
  | block b => rfl
  | funDef n ps rs b => rfl
  | letDecl xs v => rfl
  | assign xs e => rfl
  | exprStmt e => rfl
  | cond c b => rfl
  | «switch» c cs dl => rfl
  | forLoop i c p b => rfl
  | «break» => rfl
  | «continue» => rfl

/-- Resolution maps `leave` and only `leave` to `leave`. -/
theorem resolveForLayoutStmt_ne_leave (L : Layout) {s : Stmt Op}
    (h : ¬s = .leave) : ¬resolveForLayoutStmt L s = .leave := by
  intro hcontra
  cases s with
  | «leave» => exact h rfl
  | «switch» c cs dl =>
      cases dl with
      | none => simp [resolveForLayoutStmt] at hcontra
      | some b => simp [resolveForLayoutStmt] at hcontra
  | block b => simp [resolveForLayoutStmt] at hcontra
  | funDef n ps rs b => simp [resolveForLayoutStmt] at hcontra
  | letDecl xs v => simp [resolveForLayoutStmt] at hcontra
  | assign xs e => simp [resolveForLayoutStmt] at hcontra
  | exprStmt e => simp [resolveForLayoutStmt] at hcontra
  | cond c b => simp [resolveForLayoutStmt] at hcontra
  | forLoop i c p b => simp [resolveForLayoutStmt] at hcontra
  | «break» => simp [resolveForLayoutStmt] at hcontra
  | «continue» => simp [resolveForLayoutStmt] at hcontra

/-- Resolution of a singleton. -/
theorem resolveForLayoutStmts_singleton (L : Layout) (s : Stmt Op) :
    resolveForLayoutStmts L [s] = [resolveForLayoutStmt L s] := by
  simp only [resolveForLayoutStmts]

/-- Resolution commutes with dropping a trailing `leave`. -/
theorem dropTrailingLeave_resolve (L : Layout) (body : Block Op) :
    dropTrailingLeave (resolveForLayoutStmts L body) =
      resolveForLayoutStmts L (dropTrailingLeave body) := by
  rcases List.eq_nil_or_concat body with rfl | ⟨ss, last, rfl⟩
  · rw [show dropTrailingLeave (resolveForLayoutStmts L ([] : List (Stmt Op))) =
      dropTrailingLeave ([] : List (Stmt Op)) from by
        rw [show resolveForLayoutStmts L ([] : List (Stmt Op)) = [] from by
          simp only [resolveForLayoutStmts]]]
    rw [show dropTrailingLeave ([] : List (Stmt Op)) = [] from rfl]
    rw [show resolveForLayoutStmts L ([] : List (Stmt Op)) = [] from by
      simp only [resolveForLayoutStmts]]
  · rw [show ss.concat last = ss ++ [last] from List.concat_eq_append ..,
      resolveForLayoutStmts_append, resolveForLayoutStmts_singleton]
    by_cases hlv : last = Stmt.leave (Op := Op)
    · subst hlv
      rw [show resolveForLayoutStmt L (Stmt.leave (Op := Op)) = .leave from by
        simp only [resolveForLayoutStmt]]
      rw [dropTrailingLeave_concat_leave, dropTrailingLeave_concat_leave]
    · rw [dropTrailingLeave_concat_other (resolveForLayoutStmt_ne_leave L hlv),
        dropTrailingLeave_concat_other hlv,
        resolveForLayoutStmts_append, resolveForLayoutStmts_singleton]

/-! ### Classification commutes with resolution -/

/-- `classifyDecl` commutes with resolution. -/
theorem classifyDecl_resolve (L : Layout) (ps rs : List Ident) (body : Block Op) :
    classifyDecl ps rs (resolveForLayoutStmts L body) =
      (classifyDecl ps rs body).map (resolveIDecl L) := by
  unfold classifyDecl
  rw [dropTrailingLeave_resolve, scopedStmts_resolve]
  split
  · next hc => rfl
  · next hc => rfl

/-- `definedFuns` is resolution-invariant. -/
theorem definedFuns_resolve (L : Layout) : ∀ body : List (Stmt Op),
    definedFuns (resolveForLayoutStmts L body) = definedFuns body
  | [] => by simp only [resolveForLayoutStmts, definedFuns]
  | s :: rest => by
      rw [show resolveForLayoutStmts L (s :: rest) =
        resolveForLayoutStmt L s :: resolveForLayoutStmts L rest from by
          simp only [resolveForLayoutStmts]]
      cases s with
      | funDef n psf rsf b =>
          rw [show resolveForLayoutStmt L (.funDef n psf rsf b) =
            .funDef n psf rsf (resolveForLayoutStmts L b) from by
              simp only [resolveForLayoutStmt]]
          show n :: definedFuns (resolveForLayoutStmts L rest) = _
          rw [definedFuns_resolve L rest]
          simp only [definedFuns]
      | block b =>
          rw [show resolveForLayoutStmt L (.block b) =
            .block (resolveForLayoutStmts L b) from by
              simp only [resolveForLayoutStmt]]
          show definedFuns (resolveForLayoutStmts L rest) = _
          rw [definedFuns_resolve L rest]
          simp only [definedFuns]
      | letDecl xs v =>
          rw [show resolveForLayoutStmt L (.letDecl xs v) =
            .letDecl xs (v.map (resolveForLayoutExpr L)) from by
              simp only [resolveForLayoutStmt]]
          show definedFuns (resolveForLayoutStmts L rest) = _
          rw [definedFuns_resolve L rest]
          simp only [definedFuns]
      | assign xs e =>
          rw [show resolveForLayoutStmt L (.assign xs e) =
            .assign xs (resolveForLayoutExpr L e) from by
              simp only [resolveForLayoutStmt]]
          show definedFuns (resolveForLayoutStmts L rest) = _
          rw [definedFuns_resolve L rest]
          simp only [definedFuns]
      | exprStmt e =>
          rw [show resolveForLayoutStmt L (.exprStmt e) =
            .exprStmt (resolveForLayoutExpr L e) from by
              simp only [resolveForLayoutStmt]]
          show definedFuns (resolveForLayoutStmts L rest) = _
          rw [definedFuns_resolve L rest]
          simp only [definedFuns]
      | cond c b =>
          rw [show resolveForLayoutStmt L (.cond c b) =
            .cond (resolveForLayoutExpr L c) (resolveForLayoutStmts L b) from by
              simp only [resolveForLayoutStmt]]
          show definedFuns (resolveForLayoutStmts L rest) = _
          rw [definedFuns_resolve L rest]
          simp only [definedFuns]
      | «switch» c cs dl =>
          cases dl with
          | none =>
              rw [show resolveForLayoutStmt L (.switch c cs none) =
                .switch (resolveForLayoutExpr L c) (resolveForLayoutCases L cs)
                  none from by simp only [resolveForLayoutStmt]]
              show definedFuns (resolveForLayoutStmts L rest) = _
              rw [definedFuns_resolve L rest]
              rfl
          | some b =>
              rw [show resolveForLayoutStmt L (.switch c cs (some b)) =
                .switch (resolveForLayoutExpr L c) (resolveForLayoutCases L cs)
                  (some (resolveForLayoutStmts L b)) from by
                    simp only [resolveForLayoutStmt]]
              show definedFuns (resolveForLayoutStmts L rest) = _
              rw [definedFuns_resolve L rest]
              rfl
      | forLoop i c po b =>
          rw [show resolveForLayoutStmt L (.forLoop i c po b) =
            .forLoop (resolveForLayoutStmts L i) (resolveForLayoutExpr L c)
              (resolveForLayoutStmts L po) (resolveForLayoutStmts L b) from by
              simp only [resolveForLayoutStmt]]
          show definedFuns (resolveForLayoutStmts L rest) = _
          rw [definedFuns_resolve L rest]
          simp only [definedFuns]
      | «break» =>
          rw [show resolveForLayoutStmt L .break = .break from by
            simp only [resolveForLayoutStmt]]
          show definedFuns (resolveForLayoutStmts L rest) = _
          rw [definedFuns_resolve L rest]
          simp only [definedFuns]
      | «continue» =>
          rw [show resolveForLayoutStmt L .continue = .continue from by
            simp only [resolveForLayoutStmt]]
          show definedFuns (resolveForLayoutStmts L rest) = _
          rw [definedFuns_resolve L rest]
          simp only [definedFuns]
      | «leave» =>
          rw [show resolveForLayoutStmt L .leave = .leave from by
            simp only [resolveForLayoutStmt]]
          show definedFuns (resolveForLayoutStmts L rest) = _
          rw [definedFuns_resolve L rest]
          simp only [definedFuns]

/-- `hoistDecls` commutes with resolution. -/
theorem hoistDecls_resolve (L : Layout) : ∀ (body : List (Stmt Op))
    (seen : List Ident),
    hoistDecls seen (resolveForLayoutStmts L body) =
      (hoistDecls seen body).map (fun p => (p.1, resolveIDecl L p.2))
  | [], seen => by simp only [resolveForLayoutStmts, hoistDecls, List.map_nil]
  | s :: rest, seen => by
      rw [show resolveForLayoutStmts L (s :: rest) =
        resolveForLayoutStmt L s :: resolveForLayoutStmts L rest from by
          simp only [resolveForLayoutStmts]]
      cases s with
      | funDef f psf rsf b =>
          rw [show resolveForLayoutStmt L (.funDef f psf rsf b) =
            .funDef f psf rsf (resolveForLayoutStmts L b) from by
              simp only [resolveForLayoutStmt]]
          unfold hoistDecls
          split
          · exact hoistDecls_resolve L rest seen
          · rw [classifyDecl_resolve]
            cases hcl : classifyDecl psf rsf b with
            | none =>
                simp only [Option.map_none]
                exact hoistDecls_resolve L rest (f :: seen)
            | some d =>
                simp only [Option.map_some]
                rw [hoistDecls_resolve L rest (f :: seen)]
                rfl
      | block b =>
          rw [show resolveForLayoutStmt L (.block b) =
            .block (resolveForLayoutStmts L b) from by
              simp only [resolveForLayoutStmt]]
          exact hoistDecls_resolve L rest seen
      | letDecl xs v =>
          rw [show resolveForLayoutStmt L (.letDecl xs v) =
            .letDecl xs (v.map (resolveForLayoutExpr L)) from by
              simp only [resolveForLayoutStmt]]
          exact hoistDecls_resolve L rest seen
      | assign xs e =>
          rw [show resolveForLayoutStmt L (.assign xs e) =
            .assign xs (resolveForLayoutExpr L e) from by
              simp only [resolveForLayoutStmt]]
          exact hoistDecls_resolve L rest seen
      | exprStmt e =>
          rw [show resolveForLayoutStmt L (.exprStmt e) =
            .exprStmt (resolveForLayoutExpr L e) from by
              simp only [resolveForLayoutStmt]]
          exact hoistDecls_resolve L rest seen
      | cond c b =>
          rw [show resolveForLayoutStmt L (.cond c b) =
            .cond (resolveForLayoutExpr L c) (resolveForLayoutStmts L b) from by
              simp only [resolveForLayoutStmt]]
          exact hoistDecls_resolve L rest seen
      | «switch» c cs dl =>
          cases dl with
          | none =>
              rw [show resolveForLayoutStmt L (.switch c cs none) =
                .switch (resolveForLayoutExpr L c) (resolveForLayoutCases L cs)
                  none from by simp only [resolveForLayoutStmt]]
              exact hoistDecls_resolve L rest seen
          | some b =>
              rw [show resolveForLayoutStmt L (.switch c cs (some b)) =
                .switch (resolveForLayoutExpr L c) (resolveForLayoutCases L cs)
                  (some (resolveForLayoutStmts L b)) from by
                    simp only [resolveForLayoutStmt]]
              exact hoistDecls_resolve L rest seen
      | forLoop i c po b =>
          rw [show resolveForLayoutStmt L (.forLoop i c po b) =
            .forLoop (resolveForLayoutStmts L i) (resolveForLayoutExpr L c)
              (resolveForLayoutStmts L po) (resolveForLayoutStmts L b) from by
              simp only [resolveForLayoutStmt]]
          exact hoistDecls_resolve L rest seen
      | «break» =>
          rw [show resolveForLayoutStmt L .break = .break from by
            simp only [resolveForLayoutStmt]]
          exact hoistDecls_resolve L rest seen
      | «continue» =>
          rw [show resolveForLayoutStmt L .continue = .continue from by
            simp only [resolveForLayoutStmt]]
          exact hoistDecls_resolve L rest seen
      | «leave» =>
          rw [show resolveForLayoutStmt L .leave = .leave from by
            simp only [resolveForLayoutStmt]]
          exact hoistDecls_resolve L rest seen

/-- Filtering by name commutes with resolving declarations. -/
theorem resolveDelta_filter (L : Layout) (Δ : DEnv) (q : Ident → Bool) :
    (resolveDelta L Δ).filter (fun p => q p.1) =
      resolveDelta L (Δ.filter (fun p => q p.1)) := by
  unfold resolveDelta
  induction Δ with
  | nil => rfl
  | cons p rest ih =>
      rw [List.map_cons, List.filter_cons, List.filter_cons]
      by_cases hq : q p.1
      · simp only [hq, if_true, List.map_cons]
        rw [ih]
      · simp only [hq, if_false]
        exact ih

/-- `deltaExtend` commutes with resolution. -/
theorem deltaExtend_resolve (L : Layout) (Δ : DEnv) (body : List (Stmt Op)) :
    deltaExtend (resolveDelta L Δ) (resolveForLayoutStmts L body) =
      resolveDelta L (deltaExtend Δ body) := by
  unfold deltaExtend
  rw [hoistDecls_resolve, definedFuns_resolve,
    resolveDelta_filter L Δ (fun x => !(definedFuns body).contains x)]
  show _ ++ _ = resolveDelta L (_ ++ _)
  unfold resolveDelta
  rw [List.map_append]

/-- `lookupDelta` commutes with resolution. -/
theorem lookupDelta_resolve (L : Layout) (Δ : DEnv) (f : Ident) :
    lookupDelta (resolveDelta L Δ) f = (lookupDelta Δ f).map (resolveIDecl L) := by
  unfold lookupDelta resolveDelta
  induction Δ with
  | nil => rfl
  | cons p rest ih =>
      by_cases hp : p.1 = f
      · rw [List.map_cons,
          List.find?_cons_of_pos (by simp [hp]),
          List.find?_cons_of_pos (by simp [hp])]
        rfl
      · rw [List.map_cons,
          List.find?_cons_of_neg (by simp [hp]),
          List.find?_cons_of_neg (by simp [hp])]
        exact ih

/-- The pruning filter commutes with resolution. -/
theorem filter_resolve (L : Layout) (Δ : DEnv) (init : List (Stmt Op)) :
    (resolveDelta L Δ).filter
        (fun p => !(definedFuns (resolveForLayoutStmts L init)).contains p.1) =
      resolveDelta L (Δ.filter (fun p => !(definedFuns init).contains p.1)) := by
  rw [definedFuns_resolve]
  exact resolveDelta_filter L Δ (fun x => !(definedFuns init).contains x)

/-! ### Site conditions commute with resolution -/

/-- Zipping with resolved arguments resolves the zipped pairs. -/
theorem zip_resolve (L : Layout) : ∀ (ps : List Ident) (as : List (Expr Op)),
    ps.zip (resolveForLayoutExprs L as) =
      (ps.zip as).map (fun pa => (pa.1, resolveForLayoutExpr L pa.2))
  | [], as => by simp
  | p :: ps', [] => by
      rw [show resolveForLayoutExprs L [] = [] from by
        simp only [resolveForLayoutExprs]]
      simp
  | p :: ps', a :: as' => by
      rw [show resolveForLayoutExprs L (a :: as') =
        resolveForLayoutExpr L a :: resolveForLayoutExprs L as' from by
          simp only [resolveForLayoutExprs]]
      rw [List.zip_cons_cons, List.zip_cons_cons, List.map_cons,
        zip_resolve L ps' as']

/-- The shadow check is resolution-invariant. -/
theorem argsShadowOK_resolve (L : Layout) (rs : List Ident) :
    ∀ pairs : List (Ident × Expr Op),
      argsShadowOK rs (pairs.map (fun pa => (pa.1, resolveForLayoutExpr L pa.2))) =
        argsShadowOK rs pairs
  | [] => rfl
  | (p, a) :: rest => by
      rw [List.map_cons]
      unfold argsShadowOK
      rw [exprVars_resolve, argsShadowOK_resolve L rs rest]
      have hfst : (rest.map (fun pa =>
          ((pa : Ident × Expr Op).1, resolveForLayoutExpr L pa.2))).map Prod.fst =
          rest.map Prod.fst := by
        rw [List.map_map]
        rfl
      rw [hfst]

/-- `siteOK` is resolution-invariant. -/
theorem siteOK_resolve (L : Layout) (d : IDecl) (xs : List Ident)
    (as : List (Expr Op)) (isLet : Bool) :
    siteOK (resolveIDecl L d) xs (resolveForLayoutExprs L as) isLet =
      siteOK d xs as isLet := by
  unfold siteOK
  rw [show (resolveIDecl L d).ps = d.ps from rfl,
    show (resolveIDecl L d).rs = d.rs from rfl,
    resolveForLayoutExprs_len, argsHaveCall_resolve, varsList_resolve,
    zip_resolve, argsShadowOK_resolve]

/-- Resolving the parameter bindings. -/
theorem resolve_paramLets (L : Layout) : ∀ l : List (Ident × Expr Op),
    resolveForLayoutStmts L (l.map (fun pa => Stmt.letDecl [pa.1] (some pa.2))) =
      (l.map (fun pa => (pa.1, resolveForLayoutExpr L pa.2))).map
        (fun pa => Stmt.letDecl [pa.1] (some pa.2))
  | [] => by simp only [List.map_nil, resolveForLayoutStmts]
  | pa :: rest => by
      rw [List.map_cons, List.map_cons, List.map_cons,
        resolveForLayoutStmts_cons,
        resolve_paramLets L rest,
        show resolveForLayoutStmt L (Stmt.letDecl [pa.1] (some pa.2)) =
          Stmt.letDecl [pa.1] (some (resolveForLayoutExpr L pa.2)) from by
            simp only [resolveForLayoutStmt, Option.map_some]]

/-- The read-out assignments are resolution-fixed. -/
theorem resolve_assigns (L : Layout) : ∀ l : List (Ident × Ident),
    resolveForLayoutStmts L (l.map (fun xr => Stmt.assign [xr.1] (Expr.var xr.2))) =
      l.map (fun xr => Stmt.assign [xr.1] (Expr.var xr.2))
  | [] => by simp only [List.map_nil, resolveForLayoutStmts]
  | xr :: rest => by
      rw [List.map_cons,
        resolveForLayoutStmts_cons,
        resolve_assigns L rest,
        show resolveForLayoutStmt L (Stmt.assign [xr.1] (Expr.var xr.2)) =
          Stmt.assign [xr.1] (Expr.var xr.2) from by
            simp only [resolveForLayoutStmt, resolveForLayoutExpr]]

/-- The inlined core commutes with resolution. -/
theorem inlineCore_resolve (L : Layout) (d : IDecl) (xs : List Ident)
    (as : List (Expr Op)) :
    resolveForLayoutStmt L (inlineCore d xs as) =
      inlineCore (resolveIDecl L d) xs (resolveForLayoutExprs L as) := by
  unfold inlineCore
  rw [show resolveForLayoutStmt L (.block
      ([Stmt.letDecl d.rs none]
        ++ ((d.ps.zip as).reverse.map (fun pa => Stmt.letDecl [pa.1] (some pa.2)))
        ++ [Stmt.block d.ss]
        ++ (xs.zip d.rs).map (fun xr => Stmt.assign [xr.1] (Expr.var xr.2)))) =
    .block (resolveForLayoutStmts L
      ([Stmt.letDecl d.rs none]
        ++ ((d.ps.zip as).reverse.map (fun pa => Stmt.letDecl [pa.1] (some pa.2)))
        ++ [Stmt.block d.ss]
        ++ (xs.zip d.rs).map (fun xr => Stmt.assign [xr.1] (Expr.var xr.2))))
    from by simp only [resolveForLayoutStmt]]
  congr 1
  rw [resolveForLayoutStmts_append, resolveForLayoutStmts_append,
    resolveForLayoutStmts_append]
  have h1 : resolveForLayoutStmts L [Stmt.letDecl d.rs none] =
      [Stmt.letDecl (resolveIDecl L d).rs none] := by
    rw [resolveForLayoutStmts_singleton]
    rw [show resolveForLayoutStmt L (Stmt.letDecl d.rs none) =
      Stmt.letDecl d.rs none from by
        simp only [resolveForLayoutStmt, Option.map_none]]
    rfl
  have h2 : resolveForLayoutStmts L
      ((d.ps.zip as).reverse.map (fun pa => Stmt.letDecl [pa.1] (some pa.2))) =
      ((resolveIDecl L d).ps.zip (resolveForLayoutExprs L as)).reverse.map
        (fun pa => Stmt.letDecl [pa.1] (some pa.2)) := by
    rw [resolve_paramLets, show (resolveIDecl L d).ps = d.ps from rfl,
      zip_resolve, List.map_reverse]
  have h3 : resolveForLayoutStmts L [Stmt.block d.ss] =
      [Stmt.block (resolveIDecl L d).ss] := by
    rw [resolveForLayoutStmts_singleton]
    rw [show resolveForLayoutStmt L (.block d.ss) =
      .block (resolveForLayoutStmts L d.ss) from by
        simp only [resolveForLayoutStmt]]
    rfl
  have h4 : resolveForLayoutStmts L
      ((xs.zip d.rs).map (fun xr => Stmt.assign [xr.1] (Expr.var xr.2))) =
      (xs.zip (resolveIDecl L d).rs).map
        (fun xr => Stmt.assign [xr.1] (Expr.var xr.2)) := by
    rw [resolve_assigns]
    rfl
  rw [h1, h2, h3, h4]

/-! ### Closure of the relation under resolution -/

/-- **Closure under resolution**: resolving both sides of a related pair (and
the declaration context pointwise) stays related. -/
theorem IcRel.resolve {Δ : DEnv} {pc pc' : PCode Op}
    (h : IcRel Δ pc pc') (L : Layout) :
    IcRel (resolveDelta L Δ) (resolvePCode L pc) (resolvePCode L pc') := by
  induction h with
  | expr => exact .expr
  | args => exact .args
  | @blockS Δ body body' _ ih =>
      show IcRel _ (.stmt (resolveForLayoutStmt L (.block body)))
        (.stmt (resolveForLayoutStmt L (.block body')))
      rw [show resolveForLayoutStmt L (.block body) =
        .block (resolveForLayoutStmts L body) from by
          simp only [resolveForLayoutStmt],
        show resolveForLayoutStmt L (.block body') =
          .block (resolveForLayoutStmts L body') from by
          simp only [resolveForLayoutStmt]]
      refine .blockS ?_
      rw [deltaExtend_resolve]
      exact ih
  | @funDefS Δ n ps rs body body' _ ih =>
      show IcRel _ (.stmt (resolveForLayoutStmt L (.funDef n ps rs body)))
        (.stmt (resolveForLayoutStmt L (.funDef n ps rs body')))
      rw [show resolveForLayoutStmt L (.funDef n ps rs body) =
        .funDef n ps rs (resolveForLayoutStmts L body) from by
          simp only [resolveForLayoutStmt],
        show resolveForLayoutStmt L (.funDef n ps rs body') =
          .funDef n ps rs (resolveForLayoutStmts L body') from by
          simp only [resolveForLayoutStmt]]
      refine .funDefS ?_
      rw [deltaExtend_resolve]
      exact ih
  | @letS Δ xs v =>
      show IcRel _ (.stmt (resolveForLayoutStmt L (.letDecl xs v)))
        (.stmt (resolveForLayoutStmt L (.letDecl xs v)))
      rw [show resolveForLayoutStmt L (.letDecl xs v) =
        .letDecl xs (v.map (resolveForLayoutExpr L)) from by
          simp only [resolveForLayoutStmt]]
      exact .letS
  | @assignS Δ xs e =>
      show IcRel _ (.stmt (resolveForLayoutStmt L (.assign xs e)))
        (.stmt (resolveForLayoutStmt L (.assign xs e)))
      rw [show resolveForLayoutStmt L (.assign xs e) =
        .assign xs (resolveForLayoutExpr L e) from by
          simp only [resolveForLayoutStmt]]
      exact .assignS
  | @exprStmtS Δ e =>
      show IcRel _ (.stmt (resolveForLayoutStmt L (.exprStmt e)))
        (.stmt (resolveForLayoutStmt L (.exprStmt e)))
      rw [show resolveForLayoutStmt L (.exprStmt e) =
        .exprStmt (resolveForLayoutExpr L e) from by
          simp only [resolveForLayoutStmt]]
      exact .exprStmtS
  | @condS Δ c body body' _ ih =>
      show IcRel _ (.stmt (resolveForLayoutStmt L (.cond c body)))
        (.stmt (resolveForLayoutStmt L (.cond c body')))
      rw [show resolveForLayoutStmt L (.cond c body) =
        .cond (resolveForLayoutExpr L c) (resolveForLayoutStmts L body) from by
          simp only [resolveForLayoutStmt],
        show resolveForLayoutStmt L (.cond c body') =
          .cond (resolveForLayoutExpr L c) (resolveForLayoutStmts L body') from by
          simp only [resolveForLayoutStmt]]
      refine .condS ?_
      rw [deltaExtend_resolve]
      exact ih
  | @switchS Δ c cases cases' dflt dflt' _ _ ihc ihd =>
      cases dflt <;> cases dflt' <;>
        (first
          | (show IcRel _
              (.stmt (resolveForLayoutStmt L (.switch c cases _)))
              (.stmt (resolveForLayoutStmt L (.switch c cases' _)))
             simp only [resolveForLayoutStmt]
             exact .switchS ihc ihd))
  | forS hpost hbody ihpost ihbody =>
      show IcRel _ (.stmt (resolveForLayoutStmt L (.forLoop _ _ _ _)))
        (.stmt (resolveForLayoutStmt L (.forLoop _ _ _ _)))
      simp only [resolveForLayoutStmt]
      refine .forS ?_ ?_
      · rw [filter_resolve, deltaExtend_resolve]
        exact ihpost
      · rw [filter_resolve, deltaExtend_resolve]
        exact ihbody
  | breakS =>
      show IcRel _ (.stmt (resolveForLayoutStmt L .break))
        (.stmt (resolveForLayoutStmt L .break))
      rw [show resolveForLayoutStmt L .break = .break from by
        simp only [resolveForLayoutStmt]]
      exact .breakS
  | continueS =>
      show IcRel _ (.stmt (resolveForLayoutStmt L .continue))
        (.stmt (resolveForLayoutStmt L .continue))
      rw [show resolveForLayoutStmt L .continue = .continue from by
        simp only [resolveForLayoutStmt]]
      exact .continueS
  | leaveS =>
      show IcRel _ (.stmt (resolveForLayoutStmt L .leave))
        (.stmt (resolveForLayoutStmt L .leave))
      rw [show resolveForLayoutStmt L .leave = .leave from by
        simp only [resolveForLayoutStmt]]
      exact .leaveS
  | nilSS =>
      show IcRel _ (.stmts (resolveForLayoutStmts L []))
        (.stmts (resolveForLayoutStmts L []))
      simp only [resolveForLayoutStmts]
      exact .nilSS
  | @consSS Δ s s' rest rest' _ _ ihs ihrest =>
      show IcRel _ (.stmts (resolveForLayoutStmts L (s :: rest)))
        (.stmts (resolveForLayoutStmts L (s' :: rest')))
      rw [show resolveForLayoutStmts L (s :: rest) =
        resolveForLayoutStmt L s :: resolveForLayoutStmts L rest from by
          simp only [resolveForLayoutStmts],
        show resolveForLayoutStmts L (s' :: rest') =
          resolveForLayoutStmt L s' :: resolveForLayoutStmts L rest' from by
          simp only [resolveForLayoutStmts]]
      exact .consSS ihs ihrest
  | @siteLet Δ f d xs as rest rest' hld hnd hsc hok _ ihrest =>
      show IcRel _ (.stmts (resolveForLayoutStmts L
          (.letDecl xs (some (.call f as)) :: rest)))
        (.stmts (resolveForLayoutStmts L
          (.letDecl xs none :: inlineCore d xs as :: rest')))
      rw [show resolveForLayoutStmts L (.letDecl xs (some (.call f as)) :: rest) =
        .letDecl xs (some (.call f (resolveForLayoutExprs L as))) ::
          resolveForLayoutStmts L rest from by
          simp only [resolveForLayoutStmts, resolveForLayoutStmt,
            Option.map_some, resolveForLayoutExpr],
        show resolveForLayoutStmts L
            (.letDecl xs none :: inlineCore d xs as :: rest') =
          .letDecl xs none :: resolveForLayoutStmt L (inlineCore d xs as) ::
            resolveForLayoutStmts L rest' from by
          simp only [resolveForLayoutStmts, resolveForLayoutStmt, Option.map_none]]
      rw [inlineCore_resolve]
      refine .siteLet ?_ hnd ?_ ?_ ihrest
      · rw [lookupDelta_resolve, hld]
        rfl
      · show scopedStmts (d.ps ++ d.rs) (resolveForLayoutStmts L d.ss) = true
        rw [scopedStmts_resolve]
        exact hsc
      · rw [siteOK_resolve]
        exact hok
  | @siteAssign Δ f d xs as rest rest' hld hnd hsc hok _ ihrest =>
      show IcRel _ (.stmts (resolveForLayoutStmts L
          (.assign xs (.call f as) :: rest)))
        (.stmts (resolveForLayoutStmts L (inlineCore d xs as :: rest')))
      rw [show resolveForLayoutStmts L (.assign xs (.call f as) :: rest) =
        .assign xs (.call f (resolveForLayoutExprs L as)) ::
          resolveForLayoutStmts L rest from by
          simp only [resolveForLayoutStmts, resolveForLayoutStmt,
            resolveForLayoutExpr],
        show resolveForLayoutStmts L (inlineCore d xs as :: rest') =
          resolveForLayoutStmt L (inlineCore d xs as) ::
            resolveForLayoutStmts L rest' from by
          simp only [resolveForLayoutStmts]]
      rw [inlineCore_resolve]
      refine .siteAssign ?_ hnd ?_ ?_ ihrest
      · rw [lookupDelta_resolve, hld]
        rfl
      · show scopedStmts (d.ps ++ d.rs) (resolveForLayoutStmts L d.ss) = true
        rw [scopedStmts_resolve]
        exact hsc
      · rw [siteOK_resolve]
        exact hok
  | @siteExpr Δ f d as rest rest' hld hnd hsc hok _ ihrest =>
      show IcRel _ (.stmts (resolveForLayoutStmts L
          (.exprStmt (.call f as) :: rest)))
        (.stmts (resolveForLayoutStmts L (inlineCore d [] as :: rest')))
      rw [show resolveForLayoutStmts L (.exprStmt (.call f as) :: rest) =
        .exprStmt (.call f (resolveForLayoutExprs L as)) ::
          resolveForLayoutStmts L rest from by
          simp only [resolveForLayoutStmts, resolveForLayoutStmt,
            resolveForLayoutExpr],
        show resolveForLayoutStmts L (inlineCore d [] as :: rest') =
          resolveForLayoutStmt L (inlineCore d [] as) ::
            resolveForLayoutStmts L rest' from by
          simp only [resolveForLayoutStmts]]
      rw [inlineCore_resolve]
      refine .siteExpr ?_ hnd ?_ ?_ ihrest
      · rw [lookupDelta_resolve, hld]
        rfl
      · show scopedStmts (d.ps ++ d.rs) (resolveForLayoutStmts L d.ss) = true
        rw [scopedStmts_resolve]
        exact hsc
      · rw [siteOK_resolve]
        exact hok
  | @loopL Δ c post post' body body' _ _ ihpost ihbody =>
      refine .loopL ?_ ?_
      · rw [deltaExtend_resolve]
        exact ihpost
      · rw [deltaExtend_resolve]
        exact ihbody
  | casesNil =>
      show IcRel _ (.cases (resolveForLayoutCases L []))
        (.cases (resolveForLayoutCases L []))
      simp only [resolveForLayoutCases]
      exact .casesNil
  | @casesCons Δ l b b' rest rest' _ _ ihb ihrest =>
      show IcRel _ (.cases (resolveForLayoutCases L ((l, b) :: rest)))
        (.cases (resolveForLayoutCases L ((l, b') :: rest')))
      rw [show resolveForLayoutCases L ((l, b) :: rest) =
        (l, resolveForLayoutStmts L b) :: resolveForLayoutCases L rest from by
          simp only [resolveForLayoutCases],
        show resolveForLayoutCases L ((l, b') :: rest') =
          (l, resolveForLayoutStmts L b') :: resolveForLayoutCases L rest' from by
          simp only [resolveForLayoutCases]]
      refine .casesCons ?_ ihrest
      rw [deltaExtend_resolve]
      exact ihb
  | odfltNone => exact .odfltNone
  | @odfltSome Δ b b' _ ih =>
      show IcRel _ (.odflt ((some b).map (resolveForLayoutStmts L)))
        (.odflt ((some b').map (resolveForLayoutStmts L)))
      simp only [Option.map_some]
      refine .odfltSome ?_
      rw [deltaExtend_resolve]
      exact ih

/-! ### The payoff -/

/-- Resolving the source and resolving the inlined program are semantically
equivalent — the object-path bridge, with the full pass. -/
theorem resolveInlineCallsBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (inlineCallsBlock b)) := by
  have h := (icStmts_rel (deltaExtend [] b) (DeltaWF.nil.extend b) b).resolve L
  apply IcRel.equivBlock (calls := calls) (creates := creates)
  rw [show deltaExtend [] (resolveForLayoutStmts L b) =
    resolveDelta L (deltaExtend [] b) from deltaExtend_resolve L [] b]
  rw [show resolveForLayoutStmts L (inlineCallsBlock b) =
    resolveForLayoutStmts L (icStmts (deltaExtend [] b) b) from by
      rw [inlineCallsBlock, icBlock]]
  exact h

end YulEvmCompiler.Optimizer
