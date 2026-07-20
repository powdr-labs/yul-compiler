import YulEvmCompiler.Optimizer.Implementation.InlineCallsSound
import YulEvmCompiler.Optimizer.Implementation.ResolveCongr
set_option warningAsError true
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

end YulEvmCompiler.Optimizer
