import YulEvmCompiler.Optimizer.Implementation.DeadLits
import YulEvmCompiler.Optimizer.Implementation.PropagateResolve
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.DeadLitsResolve

**The removal relation is closed under object-layout resolution.** Resolution
creates literal bindings out of `dataoffset`/`datasize` lets, so the removal
*function* deletes more on resolved code and no syntactic commutation exists —
the `DlRel` skip rules (`sameS`, `consSS`) absorb exactly that mismatch. The
guards transport verbatim: a literal right-hand side is a resolution fixed
point, and resolution never changes which identifiers occur (`mentions` is
invariant), so a `dropSS` step on the source is a valid `dropSS` step on the
resolved pair. The payoff `resolveDeadLitsBlock_equiv` is the object-path
congruence composed into the pipeline theorem.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### Resolution never changes which identifiers occur -/

mutual

theorem mentions_resolveExpr (L : Layout) (x : Ident) :
    ∀ e : Expr Op, exprMentions x (resolveForLayoutExpr L e) = exprMentions x e
  | .lit l => rfl
  | .var y => rfl
  | .builtin op args => by
      by_cases hop : op = .dataoffset ∨ op = .datasize
      · by_cases hstr : ∃ n, args = [.lit (.string n)]
        · obtain ⟨n, rfl⟩ := hstr
          have hshape : resolveForLayoutExpr L (.builtin op [.lit (.string n)]) =
              .lit (.number ((L.dataOffset (litValue (.string n))).toNat)) ∨
              resolveForLayoutExpr L (.builtin op [.lit (.string n)]) =
              .lit (.number ((L.dataSize (litValue (.string n))).toNat)) := by
            rcases hop with rfl | rfl
            · left; rfl
            · right; rfl
          rcases hshape with hshape | hshape <;>
            rw [hshape] <;>
            simp [exprMentions, argsMentions]
        · rw [not_exists] at hstr
          rw [resolveForLayoutExpr_builtin_other L op _ hstr]
          simp only [exprMentions]
          exact mentions_resolveArgs L x args
      · rw [not_or] at hop
        rw [resolve_builtin_nondata L _ hop.1 hop.2]
        simp only [exprMentions]
        exact mentions_resolveArgs L x args
  | .call f args => by
      show exprMentions x (.call f (resolveForLayoutExprs L args)) = _
      simp only [exprMentions]
      exact mentions_resolveArgs L x args

theorem mentions_resolveArgs (L : Layout) (x : Ident) :
    ∀ es : List (Expr Op), argsMentions x (resolveForLayoutExprs L es) = argsMentions x es
  | [] => rfl
  | e :: rest => by
      show argsMentions x
        (resolveForLayoutExpr L e :: resolveForLayoutExprs L rest) = _
      simp only [argsMentions]
      rw [mentions_resolveExpr L x e, mentions_resolveArgs L x rest]

end

mutual

theorem mentions_resolveStmt (L : Layout) (x : Ident) :
    ∀ s : Stmt Op, stmtMentions x (resolveForLayoutStmt L s) = stmtMentions x s
  | .block body => by
      rw [resolveForLayoutStmt_block]
      simp only [stmtMentions]
      exact mentions_resolveStmts L x body
  | .funDef n ps rs body => by
      rw [resolveForLayoutStmt_funDef]
      simp only [stmtMentions]
      rw [mentions_resolveStmts L x body]
  | .letDecl xs v => by
      rw [resolveForLayoutStmt_letDecl]
      simp only [stmtMentions]
      cases v with
      | none => rfl
      | some e =>
          simp only [Option.map_some, optExprMentions]
          rw [mentions_resolveExpr L x e]
  | .assign xs e => by
      rw [resolveForLayoutStmt_assign]
      simp only [stmtMentions]
      rw [mentions_resolveExpr L x e]
  | .cond c body => by
      rw [resolveForLayoutStmt_cond]
      simp only [stmtMentions]
      rw [mentions_resolveExpr L x c, mentions_resolveStmts L x body]
  | .switch c cases dflt => by
      rw [resolveForLayoutStmt_switch]
      simp only [stmtMentions]
      rw [mentions_resolveExpr L x c, mentions_resolveCases L x cases]
      cases dflt with
      | none => rfl
      | some b =>
          simp only [Option.map_some, optBlockMentions]
          rw [mentions_resolveStmts L x b]
  | .forLoop init c post body => by
      rw [resolveForLayoutStmt_forLoop]
      simp only [stmtMentions]
      rw [mentions_resolveStmts L x init, mentions_resolveExpr L x c,
          mentions_resolveStmts L x post, mentions_resolveStmts L x body]
  | .exprStmt e => by
      rw [resolveForLayoutStmt_exprStmt]
      simp only [stmtMentions]
      rw [mentions_resolveExpr L x e]
  | .break => by rw [resolveForLayoutStmt_break]
  | .continue => by rw [resolveForLayoutStmt_continue]
  | .leave => by rw [resolveForLayoutStmt_leave]

theorem mentions_resolveStmts (L : Layout) (x : Ident) :
    ∀ ss : List (Stmt Op),
      stmtsMentions x (resolveForLayoutStmts L ss) = stmtsMentions x ss
  | [] => by rw [resolveForLayoutStmts_nil]
  | s :: rest => by
      rw [resolveForLayoutStmts_cons]
      simp only [stmtsMentions]
      rw [mentions_resolveStmt L x s, mentions_resolveStmts L x rest]

theorem mentions_resolveCases (L : Layout) (x : Ident) :
    ∀ cs : List (Literal × Block Op),
      casesMentions x (resolveForLayoutCases L cs) = casesMentions x cs
  | [] => by rw [resolveForLayoutCases]
  | (l, b) :: rest => by
      rw [resolveForLayoutCases]
      simp only [casesMentions]
      rw [mentions_resolveStmts L x b, mentions_resolveCases L x rest]

end

/-! ### The relation is closed under resolution -/

/-- **Closure under resolution**: resolving both sides of a removal-related
pair yields a removal-related pair. -/
theorem DlRel.resolve {pc pc' : PCode Op} (h : DlRel pc pc') (L : Layout) :
    DlRel (resolvePCode L pc) (resolvePCode L pc') := by
  induction h with
  | sameS => exact .sameS
  | @blockS body body' _ ih =>
      show DlRel (.stmt (resolveForLayoutStmt L (.block body)))
        (.stmt (resolveForLayoutStmt L (.block body')))
      rw [resolveForLayoutStmt_block, resolveForLayoutStmt_block]
      exact .blockS ih
  | @funDefS n ps rs body body' _ ih =>
      show DlRel (.stmt (resolveForLayoutStmt L (.funDef n ps rs body)))
        (.stmt (resolveForLayoutStmt L (.funDef n ps rs body')))
      rw [resolveForLayoutStmt_funDef, resolveForLayoutStmt_funDef]
      exact .funDefS ih
  | @condS c body body' _ ih =>
      show DlRel (.stmt (resolveForLayoutStmt L (.cond c body)))
        (.stmt (resolveForLayoutStmt L (.cond c body')))
      rw [resolveForLayoutStmt_cond, resolveForLayoutStmt_cond]
      exact .condS ih
  | @switchS c cases cases' dflt dflt' _ _ ihc ihd =>
      show DlRel (.stmt (resolveForLayoutStmt L (.switch c cases dflt)))
        (.stmt (resolveForLayoutStmt L (.switch c cases' dflt')))
      rw [resolveForLayoutStmt_switch, resolveForLayoutStmt_switch]
      exact .switchS ihc ihd
  | @forS init c post post' body body' _ _ ihp ihb =>
      show DlRel (.stmt (resolveForLayoutStmt L (.forLoop init c post body)))
        (.stmt (resolveForLayoutStmt L (.forLoop init c post' body')))
      rw [resolveForLayoutStmt_forLoop, resolveForLayoutStmt_forLoop]
      exact .forS ihp ihb
  | nilSS =>
      show DlRel (.stmts (resolveForLayoutStmts L [])) (.stmts (resolveForLayoutStmts L []))
      rw [resolveForLayoutStmts_nil]
      exact .nilSS
  | @consSS s s' rest rest' _ _ ihs ihrest =>
      show DlRel (.stmts (resolveForLayoutStmts L (s :: rest)))
        (.stmts (resolveForLayoutStmts L (s' :: rest')))
      rw [resolveForLayoutStmts_cons, resolveForLayoutStmts_cons]
      exact .consSS ihs ihrest
  | @dropSS x val rest rest' hval hm _ ihrest =>
      show DlRel (.stmts (resolveForLayoutStmts L (.letDecl [x] val :: rest)))
        (.stmts (resolveForLayoutStmts L rest'))
      rw [resolveForLayoutStmts_cons, resolveForLayoutStmt_letDecl]
      have hval' : val.map (resolveForLayoutExpr L) = none ∨
          ∃ l, val.map (resolveForLayoutExpr L) = some (.lit l) := by
        rcases hval with rfl | ⟨l, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨l, rfl⟩
      have hm' : stmtsMentions x (resolveForLayoutStmts L rest) = false := by
        rw [mentions_resolveStmts L x rest]
        exact hm
      exact .dropSS hval' hm' ihrest
  | casesNil =>
      show DlRel (.cases (resolveForLayoutCases L [])) (.cases (resolveForLayoutCases L []))
      rw [resolveForLayoutCases]
      exact .casesNil
  | @casesCons l b b' rest rest' _ _ ihb ihrest =>
      show DlRel (.cases (resolveForLayoutCases L ((l, b) :: rest)))
        (.cases (resolveForLayoutCases L ((l, b') :: rest')))
      rw [resolveForLayoutCases, resolveForLayoutCases]
      exact .casesCons ihb ihrest
  | odfltNone => exact .odfltNone
  | @odfltSome b b' _ ih => exact .odfltSome ih

/-! ### The payoff: the resolution congruence for the pass -/

/-- Resolving the source and resolving the pruned program are semantically
equivalent — the object-path bridge for `DeadLits`, full pass, no restriction. -/
theorem resolveDeadLitsBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (dlStmts b)) :=
  DlRel.equivBlock ((dlStmts_rel b).resolve L)

end YulEvmCompiler.Optimizer
