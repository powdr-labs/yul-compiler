import YulEvmCompiler.Optimizer.Implementation.FreshenCalls
import YulEvmCompiler.Optimizer.Implementation.InlineCallsResolve
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.FreshenCallsResolve

Resolution congruence for `FreshenCalls` (object path). The pass commutes
with layout resolution syntactically: its decisions read only identifier
sets, statement structure, and call shapes — all invariant under
`resolveForLayout*` — and the rewrite maps hoisted arguments through
resolution pointwise.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### Resolution of one freshened site -/

private theorem resolve_readouts (L : Layout) : ∀ pairs : List (Ident × Ident),
    resolveForLayoutStmts L
      (pairs.map (fun xr => Stmt.assign [xr.1] (.var xr.2))) =
      pairs.map (fun xr => Stmt.assign [xr.1] (.var xr.2))
  | [] => by rw [List.map_nil, resolveForLayoutStmts]
  | pair :: rest => by
      rw [List.map_cons, resolveForLayoutStmts, resolveForLayoutStmt_assign,
        resolveForLayoutExpr, resolve_readouts L rest]

private theorem resolve_freshenCore (L : Layout) (P : String) (xs : List Ident)
    (f : Ident) (as : List (Expr Op)) :
    resolveForLayoutStmt L (freshenCore P xs f as) =
      freshenCore P xs f (resolveForLayoutExprs L as) := by
  simp only [freshenCore, List.singleton_append, resolveForLayoutStmt_block,
    resolveForLayoutStmts_cons, resolveForLayoutStmt_letDecl, Option.map_some,
    resolveForLayoutExpr]
  rw [resolve_readouts]

/-! ### Traversal congruence -/

mutual

private theorem resolveFcStmt_equiv (L : Layout) (P : String) (Δ : DEnv) :
    ∀ s : Stmt Op,
      EquivStmt D (resolveForLayoutStmt L s)
        (resolveForLayoutStmt L (fcStmt P Δ s))
  | .block body => by
      rw [fcStmt, resolveForLayoutStmt_block, resolveForLayoutStmt_block]
      change EquivBlock D (resolveForLayoutStmts L body)
        (resolveForLayoutStmts L (fcBlock P Δ body))
      simpa [fcBlock] using
        (EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂
            (resolveFcStmts_forall2 L P (deltaExtend Δ body) body))
          (resolveFcScopeRel L P (deltaExtend Δ body) body))
  | .funDef n ps rs body => by
      rw [fcStmt, resolveForLayoutStmt_funDef, resolveForLayoutStmt_funDef]
      intro funs V st V' st' o
      constructor <;> intro h <;> cases h <;> exact Step.funDef
  | .letDecl xs v => by simp only [fcStmt]; exact EquivStmt.refl _
  | .assign xs (.call f as) => by
      simp only [fcStmt]
      split
      · next d hd =>
          split
          · next hw =>
              obtain ⟨hlen, hnd, hdisj, hnc⟩ := freshenWanted_inv hw
              rw [resolveForLayoutStmt_assign, resolve_freshenCore]
              apply freshenCore_equiv_of P xs f (resolveForLayoutExprs L as)
                hlen hnd hdisj
              rw [argsHaveCall_resolve]
              exact hnc
          · rw [resolveForLayoutStmt_assign]
            exact EquivStmt.refl _
      · rw [resolveForLayoutStmt_assign]
        exact EquivStmt.refl _
  | .assign xs (.lit l) => by simp only [fcStmt]; exact EquivStmt.refl _
  | .assign xs (.var x) => by simp only [fcStmt]; exact EquivStmt.refl _
  | .assign xs (.builtin op as) => by simp only [fcStmt]; exact EquivStmt.refl _
  | .cond c body => by
      rw [fcStmt, resolveForLayoutStmt_cond, resolveForLayoutStmt_cond]
      exact EquivStmt.cond_congr (EquivExpr.refl _)
        (by simpa [fcBlock] using
          (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂
              (resolveFcStmts_forall2 L P (deltaExtend Δ body) body))
            (resolveFcScopeRel L P (deltaExtend Δ body) body)))
  | .switch c cases dflt => by
      rw [fcStmt, resolveForLayoutStmt_switch, resolveForLayoutStmt_switch]
      exact EquivStmt.switch_congr (EquivExpr.refl _)
        (resolveFcCases_forall2 L P Δ cases) (resolveFcDflt_equiv L P Δ dflt)
  | .forLoop init c post body => by
      let ΔL := Δ.filter (fun p => !(definedFuns init).contains p.1)
      rw [fcStmt, resolveForLayoutStmt_forLoop, resolveForLayoutStmt_forLoop]
      simpa [fcBlock, ΔL] using
        (EquivStmt.forLoop_congr (resolveForLayoutStmts L init)
          (EquivExpr.refl (resolveForLayoutExpr L c))
          (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂
              (resolveFcStmts_forall2 L P (deltaExtend ΔL post) post))
            (resolveFcScopeRel L P (deltaExtend ΔL post) post))
          (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂
              (resolveFcStmts_forall2 L P (deltaExtend ΔL body) body))
            (resolveFcScopeRel L P (deltaExtend ΔL body) body)))
  | .exprStmt e => by simp only [fcStmt]; exact EquivStmt.refl _
  | .break => by simp only [fcStmt]; exact EquivStmt.refl _
  | .continue => by simp only [fcStmt]; exact EquivStmt.refl _
  | .leave => by simp only [fcStmt]; exact EquivStmt.refl _

private theorem resolveFcStmts_forall2 (L : Layout) (P : String) (Δ : DEnv) :
    ∀ ss : List (Stmt Op),
      List.Forall₂ (EquivStmt D) (resolveForLayoutStmts L ss)
        (resolveForLayoutStmts L (fcStmts P Δ ss))
  | [] => by rw [resolveForLayoutStmts, fcStmts, resolveForLayoutStmts]; exact .nil
  | s :: rest => by
      rw [resolveForLayoutStmts, fcStmts, resolveForLayoutStmts]
      exact .cons (resolveFcStmt_equiv L P Δ s)
        (resolveFcStmts_forall2 L P Δ rest)

private theorem resolveFcCases_forall2 (L : Layout) (P : String) (Δ : DEnv) :
    ∀ cs : List (Literal × Block Op),
      List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2)
        (resolveForLayoutCases L cs) (resolveForLayoutCases L (fcCases P Δ cs))
  | [] => by rw [resolveForLayoutCases, fcCases, resolveForLayoutCases]; exact .nil
  | (l, b) :: rest => by
      rw [resolveForLayoutCases, fcCases, resolveForLayoutCases]
      have hb : EquivBlock D (resolveForLayoutStmts L b)
          (resolveForLayoutStmts L (fcBlock P Δ b)) := by
        simpa [fcBlock] using
          (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂
              (resolveFcStmts_forall2 L P (deltaExtend Δ b) b))
            (resolveFcScopeRel L P (deltaExtend Δ b) b))
      exact .cons ⟨rfl, hb⟩ (resolveFcCases_forall2 L P Δ rest)

private theorem resolveFcDflt_equiv (L : Layout) (P : String) (Δ : DEnv) :
    ∀ dflt : Option (Block Op),
      EquivBlock D ((dflt.map (resolveForLayoutStmts L)).getD [])
        (((fcDflt P Δ dflt).map (resolveForLayoutStmts L)).getD [])
  | none => by simp [fcDflt]; exact EquivBlock.refl _
  | some b => by
      simp only [fcDflt, Option.map_some, Option.getD_some]
      simpa [fcBlock] using
        (EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂
            (resolveFcStmts_forall2 L P (deltaExtend Δ b) b))
          (resolveFcScopeRel L P (deltaExtend Δ b) b))

private theorem resolveFcScopeRel (L : Layout) (P : String) (Δ : DEnv) :
    ∀ ss : List (Stmt Op),
      ScopeRel D (hoist D (resolveForLayoutStmts L ss))
        (hoist D (resolveForLayoutStmts L (fcStmts P Δ ss)))
  | [] => by simp [fcStmts, hoist]; exact .nil
  | .funDef n ps rs body :: rest => by
      rw [fcStmts, fcStmt, resolveForLayoutStmts, resolveForLayoutStmt_funDef,
        resolveForLayoutStmts, resolveForLayoutStmt_funDef]
      simp only [hoist, List.filterMap_cons]
      have hb : EquivBlock D (resolveForLayoutStmts L body)
          (resolveForLayoutStmts L (fcBlock P Δ body)) := by
        simpa [fcBlock] using
          (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂
              (resolveFcStmts_forall2 L P (deltaExtend Δ body) body))
            (resolveFcScopeRel L P (deltaExtend Δ body) body))
      exact .cons ⟨rfl, rfl, rfl, hb⟩ (resolveFcScopeRel L P Δ rest)
  | .block _ :: rest => by
      simpa [fcStmts, fcStmt, resolveForLayoutStmts, resolveForLayoutStmt, hoist]
        using resolveFcScopeRel L P Δ rest
  | .letDecl _ _ :: rest => by
      simpa [fcStmts, fcStmt, resolveForLayoutStmts, resolveForLayoutStmt, hoist]
        using resolveFcScopeRel L P Δ rest
  | .assign xs (.call f as) :: rest => by
      simp only [fcStmts, fcStmt]
      split
      · split <;>
          simpa [freshenCore, resolveForLayoutStmts, resolveForLayoutStmt, hoist]
            using resolveFcScopeRel L P Δ rest
      · simpa [resolveForLayoutStmts, resolveForLayoutStmt, hoist]
          using resolveFcScopeRel L P Δ rest
  | .assign _ (.lit _) :: rest => by
      simpa [fcStmts, fcStmt, resolveForLayoutStmts, resolveForLayoutStmt, hoist]
        using resolveFcScopeRel L P Δ rest
  | .assign _ (.var _) :: rest => by
      simpa [fcStmts, fcStmt, resolveForLayoutStmts, resolveForLayoutStmt, hoist]
        using resolveFcScopeRel L P Δ rest
  | .assign _ (.builtin _ _) :: rest => by
      simpa [fcStmts, fcStmt, resolveForLayoutStmts, resolveForLayoutStmt, hoist]
        using resolveFcScopeRel L P Δ rest
  | .cond _ _ :: rest => by
      simpa [fcStmts, fcStmt, resolveForLayoutStmts, resolveForLayoutStmt, hoist]
        using resolveFcScopeRel L P Δ rest
  | .switch _ _ _ :: rest => by
      simpa [fcStmts, fcStmt, resolveForLayoutStmts, resolveForLayoutStmt, hoist]
        using resolveFcScopeRel L P Δ rest
  | .forLoop _ _ _ _ :: rest => by
      simpa [fcStmts, fcStmt, resolveForLayoutStmts, resolveForLayoutStmt, hoist]
        using resolveFcScopeRel L P Δ rest
  | .exprStmt _ :: rest => by
      simpa [fcStmts, fcStmt, resolveForLayoutStmts, resolveForLayoutStmt, hoist]
        using resolveFcScopeRel L P Δ rest
  | .break :: rest => by
      simpa [fcStmts, fcStmt, resolveForLayoutStmts, resolveForLayoutStmt, hoist]
        using resolveFcScopeRel L P Δ rest
  | .continue :: rest => by
      simpa [fcStmts, fcStmt, resolveForLayoutStmts, resolveForLayoutStmt, hoist]
        using resolveFcScopeRel L P Δ rest
  | .leave :: rest => by
      simpa [fcStmts, fcStmt, resolveForLayoutStmts, resolveForLayoutStmt, hoist]
        using resolveFcScopeRel L P Δ rest

end

/-- Resolution congruence for `FreshenCalls`. -/
theorem resolveFreshenCallsBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (freshenCallsBlock b)) := by
  unfold freshenCallsBlock
  split
  · next p hp =>
      simpa [fcBlock] using
        (EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂
            (resolveFcStmts_forall2 L p (deltaExtend [] b) b))
          (resolveFcScopeRel L p (deltaExtend [] b) b))
  · exact EquivBlock.refl _

end YulEvmCompiler.Optimizer
