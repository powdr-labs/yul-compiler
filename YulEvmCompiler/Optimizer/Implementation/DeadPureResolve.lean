import YulEvmCompiler.Optimizer.Implementation.DeadPure
import YulEvmCompiler.Optimizer.Implementation.DeadLitsResolve
import YulEvmCompiler.Optimizer.Implementation.InlineCallsResolve
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.DeadPureResolve

Resolution congruence for the `DeadPure` pass (object path): mirrors
`DeadLitsResolve` — the removal relation is closed under layout resolution
(`mentions_resolve*` invariance; `alwaysEval` is resolution-stable in the
transported direction since `dataoffset`/`datasize` are outside the total
state-preserving fragment and resolution preserves literals, variables, and
statement structure).
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### `alwaysEval` is resolution-stable -/

/-- Ops in the pure fragment are not layout reads. -/
theorem pureTotalArity_not_data {op : Op} {n : Nat}
    (h : pureTotalArity op = some n) :
    op ≠ .dataoffset ∧ op ≠ .datasize := by
  constructor <;> (rintro rfl; simp [pureTotalArity] at h)

/-- Stable-total operations, including `sload`, are not layout reads. -/
theorem stableTotalArity_not_data {op : Op} {n : Nat}
    (h : stableTotalArity op = some n) :
    op ≠ .dataoffset ∧ op ≠ .datasize := by
  constructor <;> (rintro rfl; simp [stableTotalArity, pureTotalArity] at h)

/-- Resolution preserves argument-list lengths. -/
theorem resolveForLayoutExprs_length (L : Layout) :
    ∀ es : List (Expr Op), (resolveForLayoutExprs L es).length = es.length
  | [] => rfl
  | e :: rest => by
      show (resolveForLayoutExpr L e :: resolveForLayoutExprs L rest).length
        = _
      simp [resolveForLayoutExprs_length L rest]

mutual

/-- Resolution preserves the always-evaluating fragment: layout reads
(`dataoffset`/`datasize`) are outside the pure fragment, so resolution only
recurses through it, preserving literals, variables, ops, and arities. -/
theorem alwaysEval_resolve (L : Layout) (bound : List Ident) :
    ∀ e : Expr Op, alwaysEval bound e = true →
      alwaysEval bound (resolveForLayoutExpr L e) = true
  | .lit _, h => h
  | .var _, h => h
  | .builtin op args, h => by
      rw [alwaysEval, Bool.and_eq_true] at h
      have har : stableTotalArity op = some args.length := by simpa using h.1
      obtain ⟨h1, h2⟩ := stableTotalArity_not_data har
      rw [resolve_builtin_nondata L args h1 h2, alwaysEval, Bool.and_eq_true]
      refine ⟨?_, alwaysEvalArgs_resolve L bound args h.2⟩
      simp [resolveForLayoutExprs_length, har]
  | .call _ _, h => by rw [alwaysEval] at h; cases h

/-- `alwaysEval_resolve`, per argument. -/
theorem alwaysEvalArgs_resolve (L : Layout) (bound : List Ident) :
    ∀ es : List (Expr Op), alwaysEvalArgs bound es = true →
      alwaysEvalArgs bound (resolveForLayoutExprs L es) = true
  | [], _ => rfl
  | e :: rest, h => by
      rw [alwaysEvalArgs, Bool.and_eq_true] at h
      show alwaysEvalArgs bound
        (resolveForLayoutExpr L e :: resolveForLayoutExprs L rest) = true
      rw [alwaysEvalArgs, Bool.and_eq_true]
      exact ⟨alwaysEval_resolve L bound e h.1,
        alwaysEvalArgs_resolve L bound rest h.2⟩

end

/-! ### Region-checker stability -/

mutual

theorem discardStmt_resolve (L : Layout) {sink : Ident} : ∀
    (ctx : DrCtx) (s : Stmt Op) (ctx' : DrCtx),
    discardStmt sink ctx s = some ctx' →
    discardStmt sink ctx (resolveForLayoutStmt L s) = some ctx'
  | ctx, .block body, ctx', h => by
      cases hb : discardStmts sink ctx body with
      | none => simp [discardStmt, hb] at h
      | some out =>
          simp [discardStmt, hb] at h
          subst ctx'
          simp [resolveForLayoutStmt_block, discardStmt,
            discardStmts_resolve L ctx body out hb]
  | _, .letDecl [] _, _, h => by simp [discardStmt] at h
  | ctx, .letDecl [x] none, ctx', h => by
      simpa [discardStmt, resolveForLayoutStmt_letDecl] using h
  | ctx, .letDecl [x] (some rhs), ctx', h => by
      simp [discardStmt] at h
      rcases h with ⟨⟨hx, hae⟩, rfl⟩
      simp [resolveForLayoutStmt_letDecl, discardStmt, hx,
        alwaysEval_resolve L ctx.bound rhs hae]
  | _, .letDecl (_ :: _ :: _) _, _, h => by simp [discardStmt] at h
  | _, .assign [] _, _, h => by simp [discardStmt] at h
  | ctx, .assign [x] rhs, ctx', h => by
      simp [discardStmt] at h
      rcases h with ⟨⟨hx, hae⟩, rfl⟩
      simp [resolveForLayoutStmt_assign, discardStmt, hx,
        alwaysEval_resolve L ctx.bound rhs hae]
  | _, .assign (_ :: _ :: _) _, _, h => by simp [discardStmt] at h
  | _, .cond _ _, _, h => by simp [discardStmt] at h
  | _, .switch _ _ _, _, h => by simp [discardStmt] at h
  | _, .forLoop _ _ _ _, _, h => by simp [discardStmt] at h
  | _, .funDef _ _ _ _, _, h => by simp [discardStmt] at h
  | _, .exprStmt _, _, h => by simp [discardStmt] at h
  | _, .break, _, h => by simp [discardStmt] at h
  | _, .continue, _, h => by simp [discardStmt] at h
  | _, .leave, _, h => by simp [discardStmt] at h
  termination_by _ s _ _ => 2 * sizeOf s + 1
  decreasing_by all_goals simp_wf

theorem discardStmts_resolve (L : Layout) {sink : Ident} : ∀
    (ctx : DrCtx) (ss : Block Op) (ctx' : DrCtx),
    discardStmts sink ctx ss = some ctx' →
    discardStmts sink ctx (resolveForLayoutStmts L ss) = some ctx'
  | ctx, [], ctx', h => by simpa [discardStmts] using h
  | ctx, s :: rest, ctx', h => by
      cases hs : discardStmt sink ctx s with
      | none => simp [discardStmts, hs] at h
      | some ctx₁ =>
          have htail : discardStmts sink ctx₁ rest = some ctx' := by
            simpa [discardStmts, hs] using h
          simp [discardStmts,
            discardStmt_resolve L ctx s ctx₁ hs,
            discardStmts_resolve L ctx₁ rest ctx' htail]
  termination_by _ ss _ _ => 2 * sizeOf ss
  decreasing_by all_goals simp_wf <;> omega

end

mutual

theorem stmtCallFree_resolve (L : Layout) : ∀ s : Stmt Op,
    stmtCallFree (resolveForLayoutStmt L s) = stmtCallFree s
  | .block body => by simp [resolveForLayoutStmt_block, stmtCallFree,
      stmtsCallFree_resolve L body]
  | .funDef n ps rs body => by simp [resolveForLayoutStmt_funDef, stmtCallFree]
  | .letDecl xs none => by simp [resolveForLayoutStmt_letDecl, stmtCallFree]
  | .letDecl xs (some e) => by simp [resolveForLayoutStmt_letDecl, stmtCallFree,
      exprHasCall_resolve]
  | .assign xs e => by simp [resolveForLayoutStmt_assign, stmtCallFree,
      exprHasCall_resolve]
  | .cond c body => by simp [resolveForLayoutStmt_cond, stmtCallFree,
      exprHasCall_resolve, stmtsCallFree_resolve L body]
  | .switch c cases dflt => by simp [resolveForLayoutStmt_switch, stmtCallFree,
      exprHasCall_resolve, casesCallFree_resolve L cases, dfltCallFree_resolve L dflt]
  | .forLoop init c post body => by simp [resolveForLayoutStmt_forLoop, stmtCallFree,
      exprHasCall_resolve, stmtsCallFree_resolve L init,
      stmtsCallFree_resolve L post, stmtsCallFree_resolve L body]
  | .exprStmt e => by simp [resolveForLayoutStmt_exprStmt, stmtCallFree,
      exprHasCall_resolve]
  | .break => by simp [resolveForLayoutStmt_break, stmtCallFree]
  | .continue => by simp [resolveForLayoutStmt_continue, stmtCallFree]
  | .leave => by simp [resolveForLayoutStmt_leave, stmtCallFree]

theorem stmtsCallFree_resolve (L : Layout) : ∀ ss : Block Op,
    stmtsCallFree (resolveForLayoutStmts L ss) = stmtsCallFree ss
  | [] => by simp [resolveForLayoutStmts_nil, stmtsCallFree]
  | s :: rest => by simp [stmtsCallFree,
      stmtCallFree_resolve L s, stmtsCallFree_resolve L rest]

theorem casesCallFree_resolve (L : Layout) : ∀ cs : List (Literal × Block Op),
    casesCallFree (resolveForLayoutCases L cs) = casesCallFree cs
  | [] => by simp [resolveForLayoutCases, casesCallFree]
  | (lit, body) :: rest => by simp [resolveForLayoutCases, casesCallFree,
      stmtsCallFree_resolve L body, casesCallFree_resolve L rest]

theorem dfltCallFree_resolve (L : Layout) : ∀ d : Option (Block Op),
    dfltCallFree (d.map (resolveForLayoutStmts L)) = dfltCallFree d
  | none => rfl
  | some body => by simp [dfltCallFree,
      stmtsCallFree_resolve L body]

end


theorem dpOut_resolve (L : Layout) (bound : List Ident) (s : Stmt Op) :
    dpOut bound (resolveForLayoutStmt L s) = dpOut bound s := by
  cases s <;> simp [dpOut, resolveForLayoutStmt.eq_def]

theorem dpOutStmts_resolve (L : Layout) (bound : List Ident) : ∀ ss : Block Op,
    dpOutStmts bound (resolveForLayoutStmts L ss) = dpOutStmts bound ss
  | [] => by simp [resolveForLayoutStmts_nil, dpOutStmts]
  | s :: rest => by simp [dpOutStmts,
      dpOut_resolve L bound s, dpOutStmts_resolve L (dpOut bound s) rest]

/-! ### The relation is closed under resolution -/

/-- **Closure under resolution**: resolving both sides of a removal-related
pair yields a removal-related pair, with the same bound sets. -/
theorem DcRel.resolve {bound bound' : List Ident} {pc pc' : PCode Op}
    (h : DcRel bound bound' pc pc') (L : Layout) :
    DcRel bound bound' (resolvePCode L pc) (resolvePCode L pc') := by
  induction h with
  | exprE => exact .exprE
  | argsE => exact .argsE
  | @blockS bound bx body body' _ ih =>
      show DcRel bound bound (.stmt (resolveForLayoutStmt L (.block body)))
        (.stmt (resolveForLayoutStmt L (.block body')))
      rw [resolveForLayoutStmt_block, resolveForLayoutStmt_block]
      exact .blockS ih
  | @funDefS bound bx n ps rs body body' _ ih =>
      show DcRel bound bound
        (.stmt (resolveForLayoutStmt L (.funDef n ps rs body)))
        (.stmt (resolveForLayoutStmt L (.funDef n ps rs body')))
      rw [resolveForLayoutStmt_funDef, resolveForLayoutStmt_funDef]
      exact .funDefS ih
  | @letS bound xs val =>
      show DcRel bound (xs ++ bound)
        (.stmt (resolveForLayoutStmt L (.letDecl xs val)))
        (.stmt (resolveForLayoutStmt L (.letDecl xs val)))
      rw [resolveForLayoutStmt_letDecl]
      exact .letS
  | @assignS bound xs e =>
      show DcRel bound bound (.stmt (resolveForLayoutStmt L (.assign xs e)))
        (.stmt (resolveForLayoutStmt L (.assign xs e)))
      rw [resolveForLayoutStmt_assign]
      exact .assignS
  | @condS bound bx c body body' _ ih =>
      show DcRel bound bound (.stmt (resolveForLayoutStmt L (.cond c body)))
        (.stmt (resolveForLayoutStmt L (.cond c body')))
      rw [resolveForLayoutStmt_cond, resolveForLayoutStmt_cond]
      exact .condS ih
  | @switchS bound c cases cases' dflt dflt' _ _ ihc ihd =>
      show DcRel bound bound
        (.stmt (resolveForLayoutStmt L (.switch c cases dflt)))
        (.stmt (resolveForLayoutStmt L (.switch c cases' dflt')))
      rw [resolveForLayoutStmt_switch, resolveForLayoutStmt_switch]
      exact .switchS ihc ihd
  | @forS bound bp bb init c post post' body body' _ _ ihp ihb =>
      show DcRel bound bound
        (.stmt (resolveForLayoutStmt L (.forLoop init c post body)))
        (.stmt (resolveForLayoutStmt L (.forLoop init c post' body')))
      rw [resolveForLayoutStmt_forLoop, resolveForLayoutStmt_forLoop]
      exact .forS ihp ihb
  | @exprStmtS bound e =>
      show DcRel bound bound (.stmt (resolveForLayoutStmt L (.exprStmt e)))
        (.stmt (resolveForLayoutStmt L (.exprStmt e)))
      rw [resolveForLayoutStmt_exprStmt]
      exact .exprStmtS
  | @breakS bound =>
      show DcRel bound bound (.stmt (resolveForLayoutStmt L .break))
        (.stmt (resolveForLayoutStmt L .break))
      rw [resolveForLayoutStmt_break]
      exact .breakS
  | @continueS bound =>
      show DcRel bound bound (.stmt (resolveForLayoutStmt L .continue))
        (.stmt (resolveForLayoutStmt L .continue))
      rw [resolveForLayoutStmt_continue]
      exact .continueS
  | @leaveS bound =>
      show DcRel bound bound (.stmt (resolveForLayoutStmt L .leave))
        (.stmt (resolveForLayoutStmt L .leave))
      rw [resolveForLayoutStmt_leave]
      exact .leaveS
  | nilSS =>
      show DcRel _ _ (.stmts (resolveForLayoutStmts L []))
        (.stmts (resolveForLayoutStmts L []))
      rw [resolveForLayoutStmts_nil]
      exact .nilSS
  | @consSS bound b1 b2 s s' rest rest' _ _ ihs ihrest =>
      show DcRel bound b2 (.stmts (resolveForLayoutStmts L (s :: rest)))
        (.stmts (resolveForLayoutStmts L (s' :: rest')))
      rw [resolveForLayoutStmts_cons, resolveForLayoutStmts_cons]
      exact .consSS ihs ihrest
  | @dropSS bound b2 x val rest rest' hval hm _ ihrest =>
      show DcRel bound b2
        (.stmts (resolveForLayoutStmts L (.letDecl [x] val :: rest)))
        (.stmts (resolveForLayoutStmts L rest'))
      rw [resolveForLayoutStmts_cons, resolveForLayoutStmt_letDecl]
      refine .dropSS ?_ ?_ ihrest
      · rcases hval with rfl | ⟨rhs, rfl, hae⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨resolveForLayoutExpr L rhs, rfl,
            alwaysEval_resolve L bound rhs hae⟩
      · rw [mentions_resolveStmts L x rest]
        exact hm
  | @dropSelfSS bound b2 x rest rest' hx _ ihrest =>
      show DcRel bound b2
        (.stmts (resolveForLayoutStmts L (.assign [x] (.var x) :: rest)))
        (.stmts (resolveForLayoutStmts L rest'))
      rw [resolveForLayoutStmts_cons, resolveForLayoutStmt_assign]
      exact .dropSelfSS hx ihrest
  | @dropRegionSS bound sink body rest hcheck hm hcf =>
      rw [← dpOutStmts_resolve L bound rest]
      show DcRel bound (dpOutStmts bound (resolveForLayoutStmts L rest))
        (.stmts (resolveForLayoutStmts L
          (.letDecl [sink] none :: .block body :: rest)))
        (.stmts (resolveForLayoutStmts L rest))
      rw [resolveForLayoutStmts_cons, resolveForLayoutStmt_letDecl,
        resolveForLayoutStmts_cons, resolveForLayoutStmt_block]
      refine .dropRegionSS ?_ ?_ ?_
      · cases hc : discardStmts sink
          { bound := sink :: bound, owned := [sink] } body with
        | none => simp [hc] at hcheck
        | some out =>
            simp [discardStmts_resolve L
              { bound := sink :: bound, owned := [sink] } body out hc] at hcheck ⊢
      · rw [mentions_resolveStmts L sink rest]
        exact hm
      · rw [stmtsCallFree_resolve L rest]
        exact hcf
  | @loopL bound bp bb c post post' body body' _ _ ihp ihb =>
      exact .loopL ihp ihb
  | casesNil =>
      show DcRel _ _ (.cases (resolveForLayoutCases L []))
        (.cases (resolveForLayoutCases L []))
      rw [resolveForLayoutCases]
      exact .casesNil
  | @casesCons bound bx l b b' rest rest' _ _ ihb ihrest =>
      show DcRel bound bound
        (.cases (resolveForLayoutCases L ((l, b) :: rest)))
        (.cases (resolveForLayoutCases L ((l, b') :: rest')))
      rw [resolveForLayoutCases, resolveForLayoutCases]
      exact .casesCons ihb ihrest
  | odfltNone => exact .odfltNone
  | @odfltSome bound bx b b' _ ih => exact .odfltSome ih

/-! ### The payoff: the resolution congruence for the pass -/

/-- Resolving the source and resolving the pruned program are semantically
equivalent — the object-path bridge for `DeadPure`, full pass, no
restriction. -/
theorem resolveDeadPureBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (dpStmts [] b)) := by
  obtain ⟨b2, hrel⟩ := dpStmts_rel [] b
  exact (hrel.resolve L).equivBlock

end YulEvmCompiler.Optimizer
