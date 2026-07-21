import YulEvmCompiler.Optimizer.Implementation.DeadPure
import YulEvmCompiler.Optimizer.Implementation.DeadLitsResolve
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.DeadPureResolve

Resolution congruence for the `DeadPure` pass (object path): mirrors
`DeadLitsResolve` — the removal relation is closed under layout resolution
(`mentions_resolve*` invariance; `alwaysEval` is resolution-stable in the
transported direction since `dataoffset`/`datasize` are outside the pure
fragment and resolution preserves literals, variables, and statement
structure).
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
      have har : pureTotalArity op = some args.length := by simpa using h.1
      obtain ⟨h1, h2⟩ := pureTotalArity_not_data har
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
