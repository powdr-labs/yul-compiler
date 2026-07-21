import YulEvmCompiler.Optimizer.Implementation.HoistCalls
import YulEvmCompiler.Optimizer.Implementation.FreshenCallsResolve
set_option warningAsError true

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

private theorem resolve_hoistUnaryCore (L : Layout) (P : String)
    (xs : List Ident) (f g : Ident) (gas : List (Expr Op)) :
    resolveForLayoutStmt L (hoistUnaryCore P xs f g gas) =
      hoistUnaryCore P xs f g (resolveForLayoutExprs L gas) := by
  simp [hoistUnaryCore, resolveForLayoutStmt_block,
    resolveForLayoutStmt_letDecl, resolveForLayoutStmt_assign,
    resolveForLayoutExpr, resolveForLayoutExprs]

mutual

private theorem resolveHcStmt_equiv (L : Layout) (P : String) (Δ : DEnv) :
    ∀ s : Stmt Op,
      EquivStmt D (resolveForLayoutStmt L s)
        (resolveForLayoutStmt L (hcStmt P Δ s))
  | .block body => by
      rw [hcStmt, resolveForLayoutStmt_block, resolveForLayoutStmt_block]
      change EquivBlock D (resolveForLayoutStmts L body)
        (resolveForLayoutStmts L (hcBlock P Δ body))
      simpa [hcBlock] using
        (EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂
            (resolveHcStmts_forall2 L P (deltaExtend Δ body) body))
          (resolveHcScopeRel L P (deltaExtend Δ body) body))
  | .funDef n ps rs body => by
      rw [hcStmt, resolveForLayoutStmt_funDef, resolveForLayoutStmt_funDef]
      intro funs V st V' st' o
      constructor <;> intro h <;> cases h <;> exact Step.funDef
  | .assign xs (.call f [.call g gas]) => by
      simp only [hcStmt]
      split
      · next outer inner hlookup =>
        split
        · next hw =>
          obtain ⟨hnc, htx⟩ := hoistUnaryWanted_inv hw
          rw [resolveForLayoutStmt_assign, resolveForLayoutExpr,
            resolveForLayoutExprs, resolve_hoistUnaryCore]
          apply hoistUnaryCore_equiv_of P xs f g (resolveForLayoutExprs L gas)
          · rw [argsHaveCall_resolve]
            exact hnc
          · exact htx
        · rw [resolveForLayoutStmt_assign, resolveForLayoutExpr,
            resolveForLayoutExprs]
          exact EquivStmt.refl _
      · rw [resolveForLayoutStmt_assign, resolveForLayoutExpr,
          resolveForLayoutExprs]
        exact EquivStmt.refl _
  | .cond c body => by
      rw [hcStmt, resolveForLayoutStmt_cond, resolveForLayoutStmt_cond]
      exact EquivStmt.cond_congr (EquivExpr.refl _)
        (by simpa [hcBlock] using
          (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂
              (resolveHcStmts_forall2 L P (deltaExtend Δ body) body))
            (resolveHcScopeRel L P (deltaExtend Δ body) body)))
  | .switch c cases dflt => by
      rw [hcStmt, resolveForLayoutStmt_switch, resolveForLayoutStmt_switch]
      exact EquivStmt.switch_congr (EquivExpr.refl _)
        (resolveHcCases_forall2 L P Δ cases) (resolveHcDflt_equiv L P Δ dflt)
  | .forLoop init c post body => by
      let ΔL := Δ.filter (fun p => !(definedFuns init).contains p.1)
      rw [hcStmt, resolveForLayoutStmt_forLoop, resolveForLayoutStmt_forLoop]
      simpa [hcBlock, ΔL] using
        (EquivStmt.forLoop_congr (resolveForLayoutStmts L init)
          (EquivExpr.refl (resolveForLayoutExpr L c))
          (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂
              (resolveHcStmts_forall2 L P (deltaExtend ΔL post) post))
            (resolveHcScopeRel L P (deltaExtend ΔL post) post))
          (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂
              (resolveHcStmts_forall2 L P (deltaExtend ΔL body) body))
            (resolveHcScopeRel L P (deltaExtend ΔL body) body)))
  | .letDecl xs val => by simp only [hcStmt]; exact EquivStmt.refl _
  | .assign xs (.lit l) => by simp only [hcStmt]; exact EquivStmt.refl _
  | .assign xs (.var x) => by simp only [hcStmt]; exact EquivStmt.refl _
  | .assign xs (.builtin op args) => by simp only [hcStmt]; exact EquivStmt.refl _
  | .assign xs (.call f []) => by simp only [hcStmt]; exact EquivStmt.refl _
  | .assign xs (.call f [.lit l]) => by simp only [hcStmt]; exact EquivStmt.refl _
  | .assign xs (.call f [.var x]) => by simp only [hcStmt]; exact EquivStmt.refl _
  | .assign xs (.call f [.builtin op args]) => by simp only [hcStmt]; exact EquivStmt.refl _
  | .assign xs (.call f (a :: b :: rest)) => by simp only [hcStmt]; exact EquivStmt.refl _
  | .exprStmt e => by simp only [hcStmt]; exact EquivStmt.refl _
  | .break => by simp only [hcStmt]; exact EquivStmt.refl _
  | .continue => by simp only [hcStmt]; exact EquivStmt.refl _
  | .leave => by simp only [hcStmt]; exact EquivStmt.refl _

private theorem resolveHcStmts_forall2 (L : Layout) (P : String) (Δ : DEnv) :
    ∀ ss : List (Stmt Op),
      List.Forall₂ (EquivStmt D) (resolveForLayoutStmts L ss)
        (resolveForLayoutStmts L (hcStmts P Δ ss))
  | [] => by rw [resolveForLayoutStmts, hcStmts, resolveForLayoutStmts]; exact .nil
  | s :: rest => by
      rw [resolveForLayoutStmts, hcStmts, resolveForLayoutStmts]
      exact .cons (resolveHcStmt_equiv L P Δ s)
        (resolveHcStmts_forall2 L P Δ rest)

private theorem resolveHcCases_forall2 (L : Layout) (P : String) (Δ : DEnv) :
    ∀ cs : List (Literal × Block Op),
      List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2)
        (resolveForLayoutCases L cs) (resolveForLayoutCases L (hcCases P Δ cs))
  | [] => by rw [resolveForLayoutCases, hcCases, resolveForLayoutCases]; exact .nil
  | (l, b) :: rest => by
      rw [resolveForLayoutCases, hcCases, resolveForLayoutCases]
      have hb : EquivBlock D (resolveForLayoutStmts L b)
          (resolveForLayoutStmts L (hcBlock P Δ b)) := by
        simpa [hcBlock] using
          (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂
              (resolveHcStmts_forall2 L P (deltaExtend Δ b) b))
            (resolveHcScopeRel L P (deltaExtend Δ b) b))
      exact .cons ⟨rfl, hb⟩ (resolveHcCases_forall2 L P Δ rest)

private theorem resolveHcDflt_equiv (L : Layout) (P : String) (Δ : DEnv) :
    ∀ dflt : Option (Block Op),
      EquivBlock D ((dflt.map (resolveForLayoutStmts L)).getD [])
        (((hcDflt P Δ dflt).map (resolveForLayoutStmts L)).getD [])
  | none => by simp [hcDflt]; exact EquivBlock.refl _
  | some b => by
      simp only [hcDflt, Option.map_some, Option.getD_some]
      simpa [hcBlock] using
        (EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂
            (resolveHcStmts_forall2 L P (deltaExtend Δ b) b))
          (resolveHcScopeRel L P (deltaExtend Δ b) b))

private theorem resolveHcScopeRel (L : Layout) (P : String) (Δ : DEnv) :
    ∀ ss : List (Stmt Op),
      ScopeRel D (hoist D (resolveForLayoutStmts L ss))
        (hoist D (resolveForLayoutStmts L (hcStmts P Δ ss)))
  | [] => by simp [hcStmts, hoist]; exact .nil
  | .funDef n ps rs body :: rest => by
      rw [hcStmts, hcStmt, resolveForLayoutStmts, resolveForLayoutStmt_funDef,
        resolveForLayoutStmts, resolveForLayoutStmt_funDef]
      simp only [hoist, List.filterMap_cons]
      have hb : EquivBlock D (resolveForLayoutStmts L body)
          (resolveForLayoutStmts L (hcBlock P Δ body)) := by
        simpa [hcBlock] using
          (EquivBlock.of_stmts_funs
            (EquivStmts.of_forall₂
              (resolveHcStmts_forall2 L P (deltaExtend Δ body) body))
            (resolveHcScopeRel L P (deltaExtend Δ body) body))
      exact .cons ⟨rfl, rfl, rfl, hb⟩ (resolveHcScopeRel L P Δ rest)
  | .block _ :: rest => by simpa [hcStmts, hcStmt, resolveForLayoutStmts,
      resolveForLayoutStmt, hoist] using resolveHcScopeRel L P Δ rest
  | .letDecl _ _ :: rest => by simpa [hcStmts, hcStmt, resolveForLayoutStmts,
      resolveForLayoutStmt, hoist] using resolveHcScopeRel L P Δ rest
  | .assign vars val :: rest => by
      cases val with
      | lit l => simpa [hcStmts, hcStmt, resolveForLayoutStmts,
          resolveForLayoutStmt, hoist] using resolveHcScopeRel L P Δ rest
      | var x => simpa [hcStmts, hcStmt, resolveForLayoutStmts,
          resolveForLayoutStmt, hoist] using resolveHcScopeRel L P Δ rest
      | builtin op args => simpa [hcStmts, hcStmt, resolveForLayoutStmts,
          resolveForLayoutStmt, hoist] using resolveHcScopeRel L P Δ rest
      | call f args =>
        cases args with
        | nil => simpa [hcStmts, hcStmt, resolveForLayoutStmts,
            resolveForLayoutStmt, hoist] using resolveHcScopeRel L P Δ rest
        | cons a tail =>
          cases tail with
          | cons b tail => simpa [hcStmts, hcStmt, resolveForLayoutStmts,
              resolveForLayoutStmt, hoist] using resolveHcScopeRel L P Δ rest
          | nil =>
            cases a with
            | lit l => simpa [hcStmts, hcStmt, resolveForLayoutStmts,
                resolveForLayoutStmt, hoist] using resolveHcScopeRel L P Δ rest
            | var x => simpa [hcStmts, hcStmt, resolveForLayoutStmts,
                resolveForLayoutStmt, hoist] using resolveHcScopeRel L P Δ rest
            | builtin op gas => simpa [hcStmts, hcStmt, resolveForLayoutStmts,
                resolveForLayoutStmt, hoist] using resolveHcScopeRel L P Δ rest
            | call g gas =>
              simp only [hcStmts, hcStmt]
              split
              · split <;> simpa [hoistUnaryCore, resolveForLayoutStmts,
                  resolveForLayoutStmt, hoist] using resolveHcScopeRel L P Δ rest
              · simpa [resolveForLayoutStmts, resolveForLayoutStmt, hoist]
                  using resolveHcScopeRel L P Δ rest
  | .cond _ _ :: rest => by simpa [hcStmts, hcStmt, resolveForLayoutStmts,
      resolveForLayoutStmt, hoist] using resolveHcScopeRel L P Δ rest
  | .switch _ _ _ :: rest => by simpa [hcStmts, hcStmt, resolveForLayoutStmts,
      resolveForLayoutStmt, hoist] using resolveHcScopeRel L P Δ rest
  | .forLoop _ _ _ _ :: rest => by simpa [hcStmts, hcStmt, resolveForLayoutStmts,
      resolveForLayoutStmt, hoist] using resolveHcScopeRel L P Δ rest
  | .exprStmt _ :: rest => by simpa [hcStmts, hcStmt, resolveForLayoutStmts,
      resolveForLayoutStmt, hoist] using resolveHcScopeRel L P Δ rest
  | .break :: rest => by simpa [hcStmts, hcStmt, resolveForLayoutStmts,
      resolveForLayoutStmt, hoist] using resolveHcScopeRel L P Δ rest
  | .continue :: rest => by simpa [hcStmts, hcStmt, resolveForLayoutStmts,
      resolveForLayoutStmt, hoist] using resolveHcScopeRel L P Δ rest
  | .leave :: rest => by simpa [hcStmts, hcStmt, resolveForLayoutStmts,
      resolveForLayoutStmt, hoist] using resolveHcScopeRel L P Δ rest

end

theorem resolveHoistCallsBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (hoistCallsBlock b)) := by
  unfold hoistCallsBlock
  split
  · next p hp =>
    simpa [hcBlock] using
      (EquivBlock.of_stmts_funs
        (EquivStmts.of_forall₂
          (resolveHcStmts_forall2 L p (deltaExtend [] b) b))
        (resolveHcScopeRel L p (deltaExtend [] b) b))
  · exact EquivBlock.refl _

end YulEvmCompiler.Optimizer
