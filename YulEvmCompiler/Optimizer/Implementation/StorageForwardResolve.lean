import YulEvmCompiler.Optimizer.Implementation.StorageForwardSound
import YulEvmCompiler.Optimizer.Implementation.ResolveCongr
set_option warningAsError true
/-!
# Layout-resolution congruence for storage forwarding

Storage forwarding is restricted to regions on which object-layout resolution
is syntactically the identity. The shallow proof can therefore reuse the pass's
semantic theorem after resolution; structural congruence lifts it through
nested functions and loop post/body regions.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

set_option linter.unusedSimpArgs false in
mutual

theorem resolve_storageLayoutFreeExpr (L : Layout) : ∀ e : Expr Op,
    storageLayoutFreeExpr e = true → resolveForLayoutExpr L e = e
  | .lit _, _ => rfl
  | .var _, _ => rfl
  | .builtin op args, h => by
      simp only [storageLayoutFreeExpr, Bool.and_eq_true] at h
      have hop1 : op ≠ .dataoffset := by
        simpa using h.1.1
      have hop2 : op ≠ .datasize := by
        simpa using h.1.2
      rw [resolve_builtin_nondata L args hop1 hop2]
      congr 1
      exact resolve_storageLayoutFreeArgs L args h.2
  | .call fn args, h => by
      simp only [storageLayoutFreeExpr] at h
      simp only [resolveForLayoutExpr]
      congr 1
      exact resolve_storageLayoutFreeArgs L args h

theorem resolve_storageLayoutFreeArgs (L : Layout) : ∀ es : List (Expr Op),
    storageLayoutFreeArgs es = true → resolveForLayoutExprs L es = es
  | [], _ => rfl
  | e :: rest, h => by
      simp only [storageLayoutFreeArgs, Bool.and_eq_true] at h
      simp only [resolveForLayoutExprs]
      rw [resolve_storageLayoutFreeExpr L e h.1,
        resolve_storageLayoutFreeArgs L rest h.2]

end

set_option linter.unusedSimpArgs false in
mutual

theorem resolve_storageLayoutFreeStmt (L : Layout) : ∀ s : Stmt Op,
    storageLayoutFreeStmt s = true → resolveForLayoutStmt L s = s
  | .block body, h => by
      simp only [storageLayoutFreeStmt] at h
      simp [resolve_storageLayoutFreeStmts L body h]
  | .funDef n ps rs body, h => by
      simp only [storageLayoutFreeStmt] at h
      simp [resolve_storageLayoutFreeStmts L body h]
  | .letDecl xs rhs, h => by
      cases rhs <;> simp_all [storageLayoutFreeStmt,
        resolve_storageLayoutFreeExpr]
  | .assign xs rhs, h => by
      simp_all [storageLayoutFreeStmt, resolve_storageLayoutFreeExpr]
  | .cond c body, h => by
      simp only [storageLayoutFreeStmt, Bool.and_eq_true] at h
      simp [resolve_storageLayoutFreeExpr L c h.1,
        resolve_storageLayoutFreeStmts L body h.2]
  | .switch c cases dflt, h => by
      simp only [storageLayoutFreeStmt, Bool.and_eq_true] at h
      simp [resolve_storageLayoutFreeExpr L c h.1.1,
        resolve_storageLayoutFreeCases L cases h.1.2,
        resolve_storageLayoutFreeDflt L dflt h.2]
  | .forLoop init c post body, h => by
      simp only [storageLayoutFreeStmt, Bool.and_eq_true] at h
      simp [resolve_storageLayoutFreeStmts L init h.1.1.1,
        resolve_storageLayoutFreeExpr L c h.1.1.2,
        resolve_storageLayoutFreeStmts L post h.1.2,
        resolve_storageLayoutFreeStmts L body h.2]
  | .exprStmt e, h => by
      simp [resolve_storageLayoutFreeExpr L e h]
  | .break, _ => by simp
  | .continue, _ => by simp
  | .leave, _ => by simp

theorem resolve_storageLayoutFreeStmts (L : Layout) : ∀ ss : List (Stmt Op),
    storageLayoutFreeStmts ss = true → resolveForLayoutStmts L ss = ss
  | [], _ => by rw [resolveForLayoutStmts_nil]
  | s :: rest, h => by
      simp only [storageLayoutFreeStmts, Bool.and_eq_true] at h
      simp [resolve_storageLayoutFreeStmt L s h.1,
        resolve_storageLayoutFreeStmts L rest h.2]

theorem resolve_storageLayoutFreeCases (L : Layout) :
    ∀ cs : List (Literal × Block Op), storageLayoutFreeCases cs = true →
      resolveForLayoutCases L cs = cs
  | [], _ => by rw [resolveForLayoutCases]
  | (l, body) :: rest, h => by
      simp only [storageLayoutFreeCases, Bool.and_eq_true] at h
      simp [resolveForLayoutCases, resolve_storageLayoutFreeStmts L body h.1,
        resolve_storageLayoutFreeCases L rest h.2]

theorem resolve_storageLayoutFreeDflt (L : Layout) : ∀ dflt : Option (Block Op),
    storageLayoutFreeDflt dflt = true →
      dflt.map (resolveForLayoutStmts L) = dflt
  | none, _ => rfl
  | some body, h => by
      simp [storageLayoutFreeDflt] at h
      simp [resolve_storageLayoutFreeStmts L body h]

end

set_option linter.unusedSimpArgs false in
mutual

theorem sfStmt_storageLayoutFree {bound : List Ident} {C : StorageCache} :
    ∀ s : Stmt Op, storageLayoutFreeStmt s = true →
      storageLayoutFreeStmt (sfStmt bound C s).1 = true
  | .block body, h => by
      simp_all [sfStmt, storageLayoutFreeStmt, sfStmts_storageLayoutFree]
  | .funDef n ps rs body, h => h
  | .letDecl xs rhs, h => by
      cases rhs with
      | none => simp [sfStmt, sfLet, storageLayoutFreeStmt]
      | some e =>
          cases xs with
          | nil => simp_all [sfStmt, sfLet, storageLayoutFreeStmt]; split <;> simp_all
          | cons x rest =>
              cases rest with
              | nil =>
                  simp only [sfStmt, sfLet]
                  split
                  · rename_i k hk
                    cases hc : cacheLookup k C with
                    | none => simp_all [storageLayoutFreeStmt]
                    | some v =>
                        cases v <;> simp_all [storageLayoutFreeStmt, StorageVal.toExpr,
                          storageLayoutFreeExpr, storageLayoutFreeArgs]
                  · split <;> simp_all [storageLayoutFreeStmt]
              | cons y tail =>
                  simp_all [sfStmt, sfLet, storageLayoutFreeStmt]
                  split <;> simp_all
  | .assign xs e, h => by
      cases xs with
      | nil => simp_all [sfStmt, sfAssign, storageLayoutFreeStmt]; split <;> simp_all
      | cons x rest =>
          cases rest with
          | nil =>
              simp only [sfStmt, sfAssign]
              split
              · rename_i k hk
                cases hc : cacheLookup k C with
                | none => simp_all [storageLayoutFreeStmt]
                | some v =>
                    cases v <;> simp_all [storageLayoutFreeStmt, StorageVal.toExpr,
                      storageLayoutFreeExpr, storageLayoutFreeArgs]
              · split
                · split <;> simp_all [storageLayoutFreeStmt]
                · simp_all [storageLayoutFreeStmt]
          | cons y tail =>
              simp_all [sfStmt, sfAssign, storageLayoutFreeStmt]
              split <;> simp_all
  | .exprStmt e, h => by
      rw [show (sfStmt bound C (.exprStmt e)).1 = .exprStmt e by
        simp [sfStmt, sfExprStmt_fst]]
      exact h
  | .cond c body, h => by
      simp only [storageLayoutFreeStmt, Bool.and_eq_true] at h
      simp [sfStmt, storageLayoutFreeStmt, h.1,
        sfStmts_storageLayoutFree body h.2]
  | .switch c cases dflt, h => h
  | .forLoop init c post body, h => h
  | .break, _ => rfl
  | .continue, _ => rfl
  | .leave, _ => rfl

theorem sfStmts_storageLayoutFree {bound : List Ident} {C : StorageCache} :
    ∀ ss : List (Stmt Op), storageLayoutFreeStmts ss = true →
      storageLayoutFreeStmts (sfStmts bound C ss).1 = true
  | [], _ => rfl
  | s :: rest, h => by
      simp only [storageLayoutFreeStmts, Bool.and_eq_true] at h
      simp only [sfStmts, storageLayoutFreeStmts, Bool.and_eq_true]
      exact ⟨sfStmt_storageLayoutFree s h.1,
        sfStmts_storageLayoutFree rest h.2⟩

end

theorem resolveStorageForwardShallowBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (storageForwardShallowBlock b)) := by
  by_cases hfree : storageLayoutFreeStmts b = true
  · have hin := resolve_storageLayoutFreeStmts L b hfree
    have hout := resolve_storageLayoutFreeStmts L (sfStmts [] [] b).1
      (sfStmts_storageLayoutFree b hfree)
    have hs : EquivBlock D b (storageForwardShallowBlock b) :=
      storageForwardShallow.sound b
    rw [storageForwardShallowBlock, if_pos hfree] at hs
    rw [hin, storageForwardShallowBlock, if_pos hfree, hout]
    exact hs
  · have hfalse := Bool.eq_false_of_not_eq_true hfree
    simpa [storageForwardShallowBlock, hfalse] using
      (EquivBlock.refl (resolveForLayoutStmts L b) : EquivBlock D _ _)

set_option linter.unusedVariables false in
mutual

theorem resolveSfFunStmt_equiv (L : Layout) : ∀ s : Stmt Op,
    EquivStmt D (resolveForLayoutStmt L s)
      (resolveForLayoutStmt L (sfFunStmt s))
  | .block body => by
      rw [sfFunStmt, resolveForLayoutStmt_block, resolveForLayoutStmt_block]
      exact EquivBlock.of_stmts_funs
        (EquivStmts.of_forall₂ (resolveSfFunStmts_forall2 L body))
        (resolveSfFunScopeRel L body)
  | .funDef n ps rs body => by
      rw [sfFunStmt, resolveForLayoutStmt_funDef, resolveForLayoutStmt_funDef]
      exact funDef_equiv n ps rs _ _
  | .cond c body => by
      rw [sfFunStmt, resolveForLayoutStmt_cond, resolveForLayoutStmt_cond]
      exact EquivStmt.cond_congr (EquivExpr.refl _)
        (EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂ (resolveSfFunStmts_forall2 L body))
          (resolveSfFunScopeRel L body))
  | .switch c cases dflt => by
      rw [sfFunStmt, resolveForLayoutStmt_switch, resolveForLayoutStmt_switch]
      exact EquivStmt.switch_congr (EquivExpr.refl _)
        (resolveSfFunCases_forall2 L cases) (resolveSfFunDflt_equiv L dflt)
  | .forLoop init c post body => by
      rw [sfFunStmt, resolveForLayoutStmt_forLoop, resolveForLayoutStmt_forLoop]
      exact EquivStmt.forLoop_congr (resolveForLayoutStmts L init)
        (EquivExpr.refl _)
        ((EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂ (resolveSfFunStmts_forall2 L post))
          (resolveSfFunScopeRel L post)).trans
            (resolveStorageForwardShallowBlock_equiv L (sfFunStmts post)))
        ((EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂ (resolveSfFunStmts_forall2 L body))
          (resolveSfFunScopeRel L body)).trans
            (resolveStorageForwardShallowBlock_equiv L (sfFunStmts body)))
  | .letDecl xs rhs => EquivStmt.refl _
  | .assign xs rhs => EquivStmt.refl _
  | .exprStmt e => EquivStmt.refl _
  | .break => EquivStmt.refl _
  | .continue => EquivStmt.refl _
  | .leave => EquivStmt.refl _

theorem resolveSfFunStmts_forall2 (L : Layout) : ∀ ss : List (Stmt Op),
    List.Forall₂ (EquivStmt D) (resolveForLayoutStmts L ss)
      (resolveForLayoutStmts L (sfFunStmts ss))
  | [] => by
      rw [resolveForLayoutStmts_nil, sfFunStmts, resolveForLayoutStmts_nil]
      exact .nil
  | s :: rest => by
      rw [resolveForLayoutStmts_cons, sfFunStmts, resolveForLayoutStmts_cons]
      exact .cons (resolveSfFunStmt_equiv L s)
        (resolveSfFunStmts_forall2 L rest)

theorem resolveSfFunCases_forall2 (L : Layout) : ∀ cs : List (Literal × Block Op),
    List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2)
      (resolveForLayoutCases L cs) (resolveForLayoutCases L (sfFunCases cs))
  | [] => by
      rw [resolveForLayoutCases, sfFunCases, resolveForLayoutCases]
      exact .nil
  | (l, body) :: rest => by
      rw [resolveForLayoutCases, sfFunCases, resolveForLayoutCases]
      exact .cons ⟨rfl, EquivBlock.of_stmts_funs
        (EquivStmts.of_forall₂ (resolveSfFunStmts_forall2 L body))
        (resolveSfFunScopeRel L body)⟩
        (resolveSfFunCases_forall2 L rest)

theorem resolveSfFunDflt_equiv (L : Layout) : ∀ dflt : Option (Block Op),
    EquivBlock D ((dflt.map (resolveForLayoutStmts L)).getD [])
      (((sfFunDflt dflt).map (resolveForLayoutStmts L)).getD [])
  | none => EquivBlock.refl _
  | some body => by
      simpa [sfFunDflt] using EquivBlock.of_stmts_funs
        (EquivStmts.of_forall₂ (resolveSfFunStmts_forall2 L body))
        (resolveSfFunScopeRel L body)

theorem resolveSfFunScopeRel (L : Layout) : ∀ ss : List (Stmt Op),
    ScopeRel D (hoist D (resolveForLayoutStmts L ss))
      (hoist D (resolveForLayoutStmts L (sfFunStmts ss)))
  | [] => by
      rw [resolveForLayoutStmts_nil, sfFunStmts, resolveForLayoutStmts_nil]
      exact .nil
  | .funDef n ps rs body :: rest => by
      rw [resolveForLayoutStmts_cons, resolveForLayoutStmt_funDef, sfFunStmts,
        sfFunStmt, resolveForLayoutStmts_cons, resolveForLayoutStmt_funDef]
      exact .cons ⟨rfl, rfl, rfl,
        (EquivBlock.of_stmts_funs
          (EquivStmts.of_forall₂ (resolveSfFunStmts_forall2 L body))
          (resolveSfFunScopeRel L body)).trans
            (resolveStorageForwardShallowBlock_equiv L (sfFunStmts body))⟩
        (resolveSfFunScopeRel L rest)
  | .block body :: rest => by
      rw [resolveForLayoutStmts_cons, resolveForLayoutStmt_block, sfFunStmts,
        sfFunStmt, resolveForLayoutStmts_cons, resolveForLayoutStmt_block]
      exact resolveSfFunScopeRel L rest
  | .letDecl xs rhs :: rest => by
      simpa [resolveForLayoutStmts_cons, sfFunStmts, sfFunStmt, hoist] using
        resolveSfFunScopeRel L rest
  | .assign xs rhs :: rest => by
      simpa [resolveForLayoutStmts_cons, sfFunStmts, sfFunStmt, hoist] using
        resolveSfFunScopeRel L rest
  | .cond c body :: rest => by
      rw [resolveForLayoutStmts_cons, resolveForLayoutStmt_cond, sfFunStmts,
        sfFunStmt, resolveForLayoutStmts_cons, resolveForLayoutStmt_cond]
      exact resolveSfFunScopeRel L rest
  | .switch c cases dflt :: rest => by
      rw [resolveForLayoutStmts_cons, resolveForLayoutStmt_switch, sfFunStmts,
        sfFunStmt, resolveForLayoutStmts_cons, resolveForLayoutStmt_switch]
      exact resolveSfFunScopeRel L rest
  | .forLoop init c post body :: rest => by
      rw [resolveForLayoutStmts_cons, resolveForLayoutStmt_forLoop, sfFunStmts,
        sfFunStmt, resolveForLayoutStmts_cons, resolveForLayoutStmt_forLoop]
      exact resolveSfFunScopeRel L rest
  | .exprStmt e :: rest => by
      simpa [resolveForLayoutStmts_cons, sfFunStmts, sfFunStmt, hoist] using
        resolveSfFunScopeRel L rest
  | .break :: rest => by
      simpa [resolveForLayoutStmts_cons, sfFunStmts, sfFunStmt, hoist] using
        resolveSfFunScopeRel L rest
  | .continue :: rest => by
      simpa [resolveForLayoutStmts_cons, sfFunStmts, sfFunStmt, hoist] using
        resolveSfFunScopeRel L rest
  | .leave :: rest => by
      simpa [resolveForLayoutStmts_cons, sfFunStmts, sfFunStmt, hoist] using
        resolveSfFunScopeRel L rest

end

theorem resolveStorageForwardBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (storageForwardBlock b)) := by
  exact (EquivBlock.of_stmts_funs
    (EquivStmts.of_forall₂ (resolveSfFunStmts_forall2 L b))
    (resolveSfFunScopeRel L b)).trans
      (by simpa [storageForwardBlock] using
        (resolveStorageForwardShallowBlock_equiv (calls := calls) (creates := creates)
          L (sfFunStmts b)))

end YulEvmCompiler.Optimizer
