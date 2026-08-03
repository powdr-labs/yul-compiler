import YulEvmCompiler.Optimizer.Implementation.InlineCallsCarrySound
set_option warningAsError false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-- A carry-leave body hoists nothing (its carry part has no top-level `funDef`,
and a trailing `leave` is not one either). -/
theorem carryLeaveStmts_hoist_nil {bound : List Ident} {body : List (Stmt Op)}
    (h : carryLeaveStmts bound body) : hoist D body = [] := by
  rcases h with h | ⟨pre, rfl, hpre⟩
  · exact carryStmts_hoist_nil h
  · rw [hoist_append, carryStmts_hoist_nil hpre]; rfl

/-- `carryPostBound` of a (possibly leave-bearing) block body is `bound`. -/
theorem carryPostBound_block (bound : List Ident) (body : List (Stmt Op)) :
    carryPostBound bound (Code.stmt (.block body)) = bound := by
  simp only [carryPostBound, carryStmt]; split <;> rfl

/-- A carry-classified statement gives `carryBodyCode` for its `.stmt` code. -/
theorem carryBodyCode_of_stmt {bound bound₁ : List Ident} {s : Stmt Op}
    (h : carryStmt bound s = some bound₁) : carryBodyCode bound (.stmt s) := by
  match s with
  | .block body =>
      refine Or.inl ?_
      simp only [carryStmt] at h
      split at h
      · assumption
      · exact absurd h (by simp)
  | .letDecl xs v => show (carryStmt bound (.letDecl xs v)).isSome = true; rw [h]; rfl
  | .assign xs e => show (carryStmt bound (.assign xs e)).isSome = true; rw [h]; rfl
  | .exprStmt e => show (carryStmt bound (.exprStmt e)).isSome = true; rw [h]; rfl
  | .cond c b => show (carryStmt bound (.cond c b)).isSome = true; rw [h]; rfl
  | .switch c cs d => show (carryStmt bound (.switch c cs d)).isSome = true; rw [h]; rfl
  | .funDef n ps rs b => simp [carryStmt] at h
  | .forLoop i cc p b => simp [carryStmt] at h
  | .«break» => simp [carryStmt] at h
  | .«continue» => simp [carryStmt] at h
  | .«leave» => simp [carryStmt] at h

/-- The statement list an `inlineCore` block wraps contains no `funDef`, so it
hoists nothing. -/
theorem inlineStmts_hoist_nil (d : IDecl) (xs : List Ident) (as : List (Expr Op)) :
    hoist D ([Stmt.letDecl d.rs none]
      ++ (d.ps.zip as).reverse.map (fun pa => Stmt.letDecl [pa.1] (some pa.2))
      ++ [Stmt.block d.ss]
      ++ (xs.zip d.rs).map (fun xr => Stmt.assign [xr.1] (Expr.var xr.2))) = [] := by
  rw [hoist_append, hoist_append, hoist_append]
  have h1 : hoist D [Stmt.letDecl d.rs none] = [] := rfl
  have h2 : hoist D ((d.ps.zip as).reverse.map
      (fun pa => Stmt.letDecl [pa.1] (some pa.2))) = [] := by
    unfold hoist
    rw [List.filterMap_map]
    apply List.filterMap_eq_nil_iff.mpr
    intro a _; rfl
  have h3 : hoist D [Stmt.block d.ss] = [] := rfl
  have h4 : hoist D ((xs.zip d.rs).map
      (fun xr => Stmt.assign [xr.1] (Expr.var xr.2))) = [] := by
    unfold hoist
    rw [List.filterMap_map]
    apply List.filterMap_eq_nil_iff.mpr
    intro a _; rfl
  rw [h1, h2, h3, h4]; rfl

mutual

/-- **Forward simulation** across `CyRel`. -/
theorem cy_fwd {funs₁ : FunEnv D} {V : VEnv D} {st : EvmState}
    {code : Code Op} {res : Res D} (h : Step D funs₁ V st code res) :
    ∀ {funs₂ : FunEnv D} {Δ : DEnv} {pc' : PCode Op},
      CyFunsRel (calls := calls) (creates := creates) funs₁ funs₂ →
      CarryCompat (calls := calls) (creates := creates) Δ funs₁ →
      CyRel Δ (toPCode code) pc' →
      ∃ res₂, Step D funs₂ V st (ofPCode pc') res₂ ∧
        cyResOK (calls := calls) (creates := creates) code res res₂ := by
  match h with
  | .lit =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | expr => exact ⟨_, Step.lit, rfl⟩
  | .var hv =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | expr => exact ⟨_, Step.var hv, rfl⟩
  | .builtinOk ha hbi =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | expr =>
          obtain ⟨res₂, hs, heq⟩ := cy_fwd ha hR hΔ CyRel.args
          rw [show res₂ = _ from heq] at hs
          exact ⟨_, Step.builtinOk hs hbi, rfl⟩
  | .builtinHalt ha hbi =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | expr =>
          obtain ⟨res₂, hs, heq⟩ := cy_fwd ha hR hΔ CyRel.args
          rw [show res₂ = _ from heq] at hs
          exact ⟨_, Step.builtinHalt hs hbi, rfl⟩
  | .builtinArgsHalt ha =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | expr =>
          obtain ⟨res₂, hs, heq⟩ := cy_fwd ha hR hΔ CyRel.args
          rw [show res₂ = _ from heq] at hs
          exact ⟨_, Step.builtinArgsHalt hs, rfl⟩
  | @Step.callOk _ _ funs V st fn args argvals st1 decl cenv Vend st2 o ha hlk harity hbody ho =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | expr =>
          obtain ⟨resa, hs, heqa⟩ := cy_fwd ha hR hΔ CyRel.args
          rw [show resa = _ from heqa] at hs
          obtain ⟨decl₂, cenv₂, hlk₂, hdecl, hcenvR⟩ := lookupFun_cyFunsRel hR hlk
          obtain ⟨hps, hrs, Δf, hΔf, hbrel⟩ := hdecl
          obtain ⟨resb, hsb, heqb⟩ := cy_fwd hbody hcenvR hΔf (CyRel.blockS hbrel)
          rw [show resb = _ from heqb] at hsb
          have hsb' : Step D cenv₂ (decl₂.params.zip argvals ++ bindZeros D decl₂.rets)
              st1 (.stmt (.block decl₂.body)) (.sres Vend st2 o) := by
            rw [← hps, ← hrs]; exact hsb
          have harity' : argvals.length = decl₂.params.length := by rw [← hps]; exact harity
          refine ⟨_, Step.callOk hs hlk₂ harity' hsb' ho, ?_⟩
          show Res.eres (.vals (decl₂.rets.map _) st2) = Res.eres (.vals (decl.rets.map _) st2)
          rw [← hrs]
  | @Step.callHalt _ _ funs V st fn args argvals st1 decl cenv Vend st2 ha hlk harity hbody =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | expr =>
          obtain ⟨resa, hs, heqa⟩ := cy_fwd ha hR hΔ CyRel.args
          rw [show resa = _ from heqa] at hs
          obtain ⟨decl₂, cenv₂, hlk₂, hdecl, hcenvR⟩ := lookupFun_cyFunsRel hR hlk
          obtain ⟨hps, hrs, Δf, hΔf, hbrel⟩ := hdecl
          obtain ⟨resb, hsb, heqb⟩ := cy_fwd hbody hcenvR hΔf (CyRel.blockS hbrel)
          rw [show resb = _ from heqb] at hsb
          have hsb' : Step D cenv₂ (decl₂.params.zip argvals ++ bindZeros D decl₂.rets)
              st1 (.stmt (.block decl₂.body)) (.sres Vend st2 .halt) := by
            rw [← hps, ← hrs]; exact hsb
          have harity' : argvals.length = decl₂.params.length := by rw [← hps]; exact harity
          exact ⟨_, Step.callHalt hs hlk₂ harity' hsb', rfl⟩
  | .callArgsHalt ha =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | expr =>
          obtain ⟨resa, hs, heqa⟩ := cy_fwd ha hR hΔ CyRel.args
          rw [show resa = _ from heqa] at hs
          exact ⟨_, Step.callArgsHalt hs, rfl⟩
  | .argsNil =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | args => exact ⟨_, Step.argsNil, rfl⟩
  | .argsCons hrest he =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | args =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_fwd hrest hR hΔ CyRel.args
          rw [show res₁ = _ from heq₁] at hs₁
          obtain ⟨res₂, hs₂, heq₂⟩ := cy_fwd he hR hΔ CyRel.expr
          rw [show res₂ = _ from heq₂] at hs₂
          exact ⟨_, Step.argsCons hs₁ hs₂, rfl⟩
  | .argsRestHalt hrest =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | args =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_fwd hrest hR hΔ CyRel.args
          rw [show res₁ = _ from heq₁] at hs₁
          exact ⟨_, Step.argsRestHalt hs₁, rfl⟩
  | .argsHeadHalt hrest he =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | args =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_fwd hrest hR hΔ CyRel.args
          rw [show res₁ = _ from heq₁] at hs₁
          obtain ⟨res₂, hs₂, heq₂⟩ := cy_fwd he hR hΔ CyRel.expr
          rw [show res₂ = _ from heq₂] at hs₂
          exact ⟨_, Step.argsHeadHalt hs₁ hs₂, rfl⟩
  | .funDef =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | funDefS hbrel => exact ⟨_, Step.funDef, rfl⟩
  | @Step.block _ _ funs V st body Vb stb o hb =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | @blockS _ _ body' hbrel =>
          have hcompat := CarryCompat.extend (calls := calls) (creates := creates) hΔ body
          have hfr := CyFunsRel.cons (calls := calls) (creates := creates)
            (cyScopeRel_of_block hbrel hcompat) hR
          obtain ⟨res₂, hs, hres⟩ := cy_fwd hb hfr hcompat hbrel
          cases hres with
          | refl => exact ⟨_, Step.block hs, rfl⟩
          | haltIns Zp =>
              have hb2 := Step.block hs
              rw [restore_prefix_le (venvLen_mono hb rfl)] at hb2
              exact ⟨_, hb2, rfl⟩
  | .letZero =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | letS => exact ⟨_, Step.letZero, rfl⟩
  | .letVal he hlen =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | letS =>
          obtain ⟨res₂, hs, heq⟩ := cy_fwd he hR hΔ CyRel.expr
          rw [show res₂ = _ from heq] at hs
          exact ⟨_, Step.letVal hs hlen, rfl⟩
  | .letHalt he =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | letS =>
          obtain ⟨res₂, hs, heq⟩ := cy_fwd he hR hΔ CyRel.expr
          rw [show res₂ = _ from heq] at hs
          exact ⟨_, Step.letHalt hs, rfl⟩
  | .assignVal he hlen =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | assignS =>
          obtain ⟨res₂, hs, heq⟩ := cy_fwd he hR hΔ CyRel.expr
          rw [show res₂ = _ from heq] at hs
          exact ⟨_, Step.assignVal hs hlen, rfl⟩
  | .assignHalt he =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | assignS =>
          obtain ⟨res₂, hs, heq⟩ := cy_fwd he hR hΔ CyRel.expr
          rw [show res₂ = _ from heq] at hs
          exact ⟨_, Step.assignHalt hs, rfl⟩
  | .exprStmt he =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | exprStmtS =>
          obtain ⟨res₂, hs, heq⟩ := cy_fwd he hR hΔ CyRel.expr
          rw [show res₂ = _ from heq] at hs
          exact ⟨_, Step.exprStmt hs, rfl⟩
  | .exprStmtHalt he =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | exprStmtS =>
          obtain ⟨res₂, hs, heq⟩ := cy_fwd he hR hΔ CyRel.expr
          rw [show res₂ = _ from heq] at hs
          exact ⟨_, Step.exprStmtHalt hs, rfl⟩
  | .ifTrue hc hcv hbody =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | @condS _ _ _ body' hbrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_fwd hc hR hΔ CyRel.expr
          rw [show res₁ = _ from heq₁] at hs₁
          obtain ⟨res₂, hs₂, heq₂⟩ := cy_fwd hbody hR hΔ (CyRel.blockS hbrel)
          rw [show res₂ = _ from heq₂] at hs₂
          exact ⟨_, Step.ifTrue hs₁ hcv hs₂, rfl⟩
  | .ifFalse hc hcv =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | condS hbrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_fwd hc hR hΔ CyRel.expr
          rw [show res₁ = _ from heq₁] at hs₁
          exact ⟨_, Step.ifFalse hs₁ hcv, rfl⟩
  | .ifHalt hc =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | condS hbrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_fwd hc hR hΔ CyRel.expr
          rw [show res₁ = _ from heq₁] at hs₁
          exact ⟨_, Step.ifHalt hs₁, rfl⟩
  | .switchExec hc hsel =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | switchS hcs hd =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_fwd hc hR hΔ CyRel.expr
          rw [show res₁ = _ from heq₁] at hs₁
          obtain ⟨res₂, hs₂, heq₂⟩ := cy_fwd hsel hR hΔ (CyRel.selectRel hcs hd _)
          rw [show res₂ = _ from heq₂] at hs₂
          exact ⟨_, Step.switchExec hs₁ hs₂, rfl⟩
  | .switchHalt hc =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | switchS hcs hd =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_fwd hc hR hΔ CyRel.expr
          rw [show res₁ = _ from heq₁] at hs₁
          exact ⟨_, Step.switchHalt hs₁, rfl⟩
  | @Step.forLoop _ _ funs V st init c post body Vinit stinit Vend stend o hinit hloop =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | @forS _ _ _ _ post' _ body' hpost hbody =>
          have hfr := CyFunsRel.cons (calls := calls) (creates := creates)
            (cyScopeRel_refl (hoist D init :: funs) (hoist D init)) hR
          obtain ⟨res₁, hs₁, hres₁⟩ := cy_fwd hinit hfr (CarryCompat.nil _)
            (CyRel.reflStmts [] init)
          cases hres₁ with
          | refl =>
              obtain ⟨res₂, hs₂, heq₂⟩ := cy_fwd hloop hfr (CarryCompat.pruneInit hΔ init)
                (CyRel.loopL hpost hbody)
              rw [show res₂ = _ from heq₂] at hs₂
              exact ⟨_, Step.forLoop hs₁ hs₂, rfl⟩
  | @Step.forInitHalt _ _ funs V st init c post body Vinit stinit hinit =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | @forS _ _ _ _ post' _ body' hpost hbody =>
          have hfr := CyFunsRel.cons (calls := calls) (creates := creates)
            (cyScopeRel_refl (hoist D init :: funs) (hoist D init)) hR
          obtain ⟨res₁, hs₁, hres₁⟩ := cy_fwd hinit hfr (CarryCompat.nil _)
            (CyRel.reflStmts [] init)
          cases hres₁ with
          | refl => exact ⟨_, Step.forInitHalt hs₁, rfl⟩
          | haltIns Zp =>
              have hb2 := Step.forInitHalt (c := c) (post := post') (body := body') hs₁
              rw [restore_prefix_le (venvLen_mono hinit rfl)] at hb2
              exact ⟨_, hb2, rfl⟩
  | .«break» =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | breakS => exact ⟨_, Step.break, rfl⟩
  | .«continue» =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | continueS => exact ⟨_, Step.continue, rfl⟩
  | .«leave» =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | leaveS => exact ⟨_, Step.leave, rfl⟩
  | .seqNil =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | nilSS => exact ⟨_, Step.seqNil, .refl _⟩
  | @Step.seqCons _ _ _ V st s rest V1 st1 V2 st2 o hs hrest =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | consSS hsrel hrestrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_fwd hs hR hΔ hsrel
          rw [show res₁ = _ from heq₁] at hs₁
          obtain ⟨res₂, hs₂, hres₂⟩ := cy_fwd hrest hR hΔ hrestrel
          cases hres₂ with
          | refl => exact ⟨_, Step.seqCons hs₁ hs₂, .refl _⟩
          | haltIns Zp => exact ⟨_, Step.seqCons hs₁ hs₂, .haltIns _ _ _⟩
      | @siteLet _ f d xs as _ rest' hld hnd hsc hok hrestrel =>
          obtain ⟨hlen_as, hlen_xs, hxnd, hnc, hsh, hxout, hxlet⟩ := siteOK_inv hok
          obtain ⟨body₀, cenv₀, hlk₀, hb₀, hagbody⟩ := hΔ (f, d) (lookupDelta_mem hld)
          cases hs with
          | @letVal _ _ _ _ _ vals stv he hlenv =>
              cases he with
              | @callOk _ _ _ _ _ argvals st1' decl cenv Vend st2' o' ha hlk harity hbody ho =>
                  rw [hlk₀] at hlk
                  injection hlk with hlk; injection hlk with hdecl hcenv
                  -- hdecl : ⟨d.ps,d.rs,body₀⟩ = decl, hcenv : cenv₀ = cenv (NOT subst yet)
                  set S : FScope D := hoist D ([Stmt.letDecl d.rs none]
                    ++ (d.ps.zip as).reverse.map (fun pa => Stmt.letDecl [pa.1] (some pa.2))
                    ++ [Stmt.block d.ss]
                    ++ (xs.zip d.rs).map (fun xr => Stmt.assign [xr.1] (Expr.var xr.2)))
                    with hS
                  have hSnil : S = [] := hS.trans (inlineStmts_hoist_nil d xs as)
                  set funsT : FunEnv D := S :: funs₂ with hfunsT
                  have hRb : CyFunsRel (calls := calls) (creates := creates)
                      (S :: funs₁) funsT :=
                    .cons (cyScopeRel_refl _ _) hR
                  -- recurse on the RAW hbody (in decl/cenv terms) BEFORE subst
                  obtain ⟨res₂, hstepb, htr⟩ := carry_body_fwd hbody
                    (A := d.ps.zip argvals ++ bindZeros D d.rs) (W := ([] : VEnv D))
                    (bound := d.ps ++ d.rs)
                    (S :: funs₁) funsT (bindZeros D xs ++ V) (by rw [← hdecl]; simp)
                    (by
                      rw [← hdecl]
                      rcases hb₀ with rfl | rfl
                      · exact Or.inl hsc
                      · exact Or.inr ⟨d.ss, rfl, hsc⟩)
                    (fun x hx => by
                      rw [calleeFrame_keys (by have := args_length ha; omega)]; exact hx)
                    (by
                      rw [← hdecl, ← hcenv, hSnil]
                      refine FunsAgree.cons_nil_right ?_
                      intro g hg
                      have hgd : g ∈ stmtsCallNames d.ss := by
                        rcases hb₀ with rfl | rfl
                        · simpa [carryCallNames, stmtCallNames] using hg
                        · simpa [carryCallNames, stmtCallNames, stmtsCallNames_append_leave]
                            using hg
                      exact (hagbody g hgd).symm) hRb
                  subst hdecl hcenv
                  have htbody_raw : Step D funsT
                      (d.ps.zip argvals ++ bindZeros D d.rs ++ (bindZeros D xs ++ V)) st1'
                      (.stmt (.block body₀)) (.sres (Vend ++ (bindZeros D xs ++ V)) st2' o') := by
                    rcases ho with rfl | rfl
                    · obtain ⟨A'', hVe, hres₂, _⟩ := TResL.norm_inv htr
                      have hae : A'' = Vend := by simpa using hVe.symm
                      rw [hae] at hres₂; rw [hres₂] at hstepb; exact hstepb
                    · obtain ⟨A'', hVe, hres₂⟩ := TResL.leave_inv htr
                      have hae : A'' = Vend := by simpa using hVe.symm
                      rw [hae] at hres₂; rw [hres₂] at hstepb; exact hstepb
                  have htbody := carry_body_normalize_ok hb₀ hsc
                    (fun x hx => by
                      rw [List.map_append, calleeFrame_keys (by have := args_length ha; omega)]
                      exact List.mem_append.mpr (Or.inl hx))
                    htbody_raw ho
                  have hcore := inlineCore_carry_fwd_normal (funs₂ := funs₂) hnd hlen_as hnc hsh
                    hxout hlen_xs (Z := bindZeros D xs) ha htbody
                    (fun y hy => by rw [bindZeros_keys]; exact hxlet rfl y hy)
                  have hsm : VEnv.setMany (bindZeros D xs ++ V) xs (d.rs.map
                      (fun r => (VEnv.get Vend r).getD (evmWithExternal calls creates).zero)) =
                      xs.zip (d.rs.map (fun r => (VEnv.get Vend r).getD
                        (evmWithExternal calls creates).zero)) ++ V :=
                    VEnv.setMany_bindZeros hxnd (by simp only [List.length_map]; omega) V
                  rw [hsm] at hcore
                  obtain ⟨res₃, hs₂, hres₃⟩ := cy_fwd hrest hR hΔ hrestrel
                  cases hres₃ with
                  | refl => exact ⟨_, Step.seqCons Step.letZero (Step.seqCons hcore hs₂), .refl _⟩
                  | haltIns Zp => exact ⟨_, Step.seqCons Step.letZero
                      (Step.seqCons hcore hs₂), .haltIns _ _ _⟩
      | @siteAssign _ f d xs as _ rest' hld hnd hsc hok hrestrel => sorry
      | @siteExpr _ f d as _ rest' hld hnd hsc hok hrestrel => sorry
  | @Step.seqStop _ _ _ V st s rest V1 st1 o hs hne =>
      intro funs₂ Δ pc' hR hΔ hrel
      cases hrel with
      | consSS hsrel hrestrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_fwd hs hR hΔ hsrel
          rw [show res₁ = _ from heq₁] at hs₁
          exact ⟨_, Step.seqStop hs₁ hne, .refl _⟩
      | @siteLet _ f d xs as _ rest' hld hnd hsc hok hrestrel => sorry
      | @siteAssign _ f d xs as _ rest' hld hnd hsc hok hrestrel => sorry
      | @siteExpr _ f d as _ rest' hld hnd hsc hok hrestrel => sorry
  | .loopDone hc hcz =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | loopL hpost hbody =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_fwd hc hR hΔ CyRel.expr
          rw [show res₁ = _ from heq₁] at hs₁
          exact ⟨_, Step.loopDone hs₁ hcz, rfl⟩
  | .loopCondHalt hc =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | loopL hpost hbody =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_fwd hc hR hΔ CyRel.expr
          rw [show res₁ = _ from heq₁] at hs₁
          exact ⟨_, Step.loopCondHalt hs₁, rfl⟩
  | .loopStep hc hcv hbody hob hpost hnext =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | @loopL _ _ _ post' _ body' hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_fwd hc hR hΔ CyRel.expr
          rw [show res₁ = _ from heq₁] at hs₁
          obtain ⟨res₂, hs₂, heq₂⟩ := cy_fwd hbody hR hΔ (CyRel.blockS hbodyrel)
          rw [show res₂ = _ from heq₂] at hs₂
          obtain ⟨res₃, hs₃, heq₃⟩ := cy_fwd hpost hR hΔ (CyRel.blockS hpostrel)
          rw [show res₃ = _ from heq₃] at hs₃
          obtain ⟨res₄, hs₄, heq₄⟩ := cy_fwd hnext hR hΔ (CyRel.loopL hpostrel hbodyrel)
          rw [show res₄ = _ from heq₄] at hs₄
          exact ⟨_, Step.loopStep hs₁ hcv hs₂ hob hs₃ hs₄, rfl⟩
  | .loopPostHalt hc hcv hbody hob hpost =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | loopL hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_fwd hc hR hΔ CyRel.expr
          rw [show res₁ = _ from heq₁] at hs₁
          obtain ⟨res₂, hs₂, heq₂⟩ := cy_fwd hbody hR hΔ (CyRel.blockS hbodyrel)
          rw [show res₂ = _ from heq₂] at hs₂
          obtain ⟨res₃, hs₃, heq₃⟩ := cy_fwd hpost hR hΔ (CyRel.blockS hpostrel)
          rw [show res₃ = _ from heq₃] at hs₃
          exact ⟨_, Step.loopPostHalt hs₁ hcv hs₂ hob hs₃, rfl⟩
  | .loopBreak hc hcv hbody =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | loopL hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_fwd hc hR hΔ CyRel.expr
          rw [show res₁ = _ from heq₁] at hs₁
          obtain ⟨res₂, hs₂, heq₂⟩ := cy_fwd hbody hR hΔ (CyRel.blockS hbodyrel)
          rw [show res₂ = _ from heq₂] at hs₂
          exact ⟨_, Step.loopBreak hs₁ hcv hs₂, rfl⟩
  | .loopLeave hc hcv hbody =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | loopL hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_fwd hc hR hΔ CyRel.expr
          rw [show res₁ = _ from heq₁] at hs₁
          obtain ⟨res₂, hs₂, heq₂⟩ := cy_fwd hbody hR hΔ (CyRel.blockS hbodyrel)
          rw [show res₂ = _ from heq₂] at hs₂
          exact ⟨_, Step.loopLeave hs₁ hcv hs₂, rfl⟩
  | .loopBodyHalt hc hcv hbody =>
      intro funs₂ Δ pc' hR hΔ hrel; cases hrel with
      | loopL hpostrel hbodyrel =>
          obtain ⟨res₁, hs₁, heq₁⟩ := cy_fwd hc hR hΔ CyRel.expr
          rw [show res₁ = _ from heq₁] at hs₁
          obtain ⟨res₂, hs₂, heq₂⟩ := cy_fwd hbody hR hΔ (CyRel.blockS hbodyrel)
          rw [show res₂ = _ from heq₂] at hs₂
          exact ⟨_, Step.loopBodyHalt hs₁ hcv hs₂, rfl⟩
  termination_by structural h

/-- Callee-body transfer with call simulation. -/
theorem carry_body_fwd {cenv : FunEnv D} {V₁ : VEnv D} {st : EvmState}
    {code : Code Op} {res₁ : Res D} (h : Step D cenv V₁ st code res₁) :
    ∀ {A W : VEnv D} {bound : List Ident} (funs₁ funs₂ : FunEnv D) (W' : VEnv D),
      V₁ = A ++ W → carryBodyCode bound code →
      (∀ x ∈ bound, x ∈ A.map Prod.fst) →
      FunsAgree (calls := calls) (creates := creates) cenv funs₁ (carryCallNames code) →
      CyFunsRel (calls := calls) (creates := creates) funs₁ funs₂ →
      ∃ res₂, Step D funs₂ (A ++ W') st code res₂ ∧
        TResL (calls := calls) (creates := creates) W W'
          (carryPostBound bound code) res₁ res₂ := by
  match h with
  | .lit =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      exact ⟨_, Step.lit, .eres _⟩
  | @Step.var _ _ _ _ _ x v hv =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      subst hV
      have hx : x ∈ bound := by
        have h2 : carryExpr bound (.var x) = true := hsc
        have := List.all_eq_true.mp h2 x (by simp [exprVars])
        simpa using this
      have hxA : x ∈ A.map Prod.fst := hb x hx
      have hgv : VEnv.get A x = some v := by
        rw [← VEnv.get_append_mem hxA W]; exact hv
      refine ⟨_, Step.var ?_, .eres _⟩
      rw [VEnv.get_append_mem hxA W']; exact hgv
  | @Step.builtinOk _ _ _ _ _ op args argvals st1 rets st2 ha hbi =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      have hargs : carryArgs bound args = true := carryExpr_builtin_args hsc
      obtain ⟨res₂, hstep, htr⟩ := carry_body_fwd ha funs₁ funs₂ W' hV
        (by simpa [carryBodyCode, carryCode] using hargs) hb
        (by simpa [carryCallNames, exprCallNames] using hag) hR
      subst hV
      cases htr with
      | eres => exact ⟨_, Step.builtinOk hstep hbi, .eres _⟩
  | @Step.builtinHalt _ _ _ _ _ op args argvals st1 st2 ha hbi =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      have hargs : carryArgs bound args = true := carryExpr_builtin_args hsc
      obtain ⟨res₂, hstep, htr⟩ := carry_body_fwd ha funs₁ funs₂ W' hV
        (by simpa [carryBodyCode, carryCode] using hargs) hb
        (by simpa [carryCallNames, exprCallNames] using hag) hR
      subst hV
      cases htr with
      | eres => exact ⟨_, Step.builtinHalt hstep hbi, .eres _⟩
  | @Step.builtinArgsHalt _ _ _ _ _ op args st1 ha =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      have hargs : carryArgs bound args = true := carryExpr_builtin_args hsc
      obtain ⟨res₂, hstep, htr⟩ := carry_body_fwd ha funs₁ funs₂ W' hV
        (by simpa [carryBodyCode, carryCode] using hargs) hb
        (by simpa [carryCallNames, exprCallNames] using hag) hR
      subst hV
      cases htr with
      | eres => exact ⟨_, Step.builtinArgsHalt hstep, .eres _⟩
  | @Step.callOk _ _ _ _ _ fn args argvals st1 decl cenv_c Vend st2 o ha hlk harity hbody ho =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      have hargs : carryArgs bound args = true := carryExpr_call_args hsc
      obtain ⟨res₂, hstep, htr⟩ := carry_body_fwd ha funs₁ funs₂ W' hV
        (by simpa [carryBodyCode, carryCode] using hargs) hb
        (by refine hag.mono ?_; intro y hy;
            show y ∈ carryCallNames (Code.expr (.call fn args));
            simp only [carryCallNames, exprCallNames];
            exact List.mem_cons_of_mem fn (by simpa [carryCallNames] using hy)) hR
      subst hV
      cases htr with
      | eres =>
          have hagfn : lookupFun cenv fn = lookupFun funs₁ fn :=
            hag fn (by simp [carryCallNames, exprCallNames])
          rw [hagfn] at hlk
          obtain ⟨decl₂, cenv₂, hlk₂, hdecl, hcenvR⟩ := lookupFun_cyFunsRel hR hlk
          obtain ⟨hps, hrs, Δf, hΔf, hbrel⟩ := hdecl
          obtain ⟨resb, hsb, heqb⟩ := cy_fwd hbody hcenvR hΔf (CyRel.blockS hbrel)
          rw [show resb = _ from heqb] at hsb
          have hsb' : Step D cenv₂ (decl₂.params.zip argvals ++ bindZeros D decl₂.rets)
              st1 (.stmt (.block decl₂.body)) (.sres Vend st2 o) := by
            rw [← hps, ← hrs]; exact hsb
          have harity' : argvals.length = decl₂.params.length := by rw [← hps]; exact harity
          refine ⟨_, Step.callOk hstep hlk₂ harity' hsb' ho, ?_⟩
          rw [← hrs]; exact .eres _
  | @Step.callHalt _ _ _ _ _ fn args argvals st1 decl cenv_c Vend st2 ha hlk harity hbody =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      have hargs : carryArgs bound args = true := carryExpr_call_args hsc
      obtain ⟨res₂, hstep, htr⟩ := carry_body_fwd ha funs₁ funs₂ W' hV
        (by simpa [carryBodyCode, carryCode] using hargs) hb
        (by refine hag.mono ?_; intro y hy;
            show y ∈ carryCallNames (Code.expr (.call fn args));
            simp only [carryCallNames, exprCallNames];
            exact List.mem_cons_of_mem fn (by simpa [carryCallNames] using hy)) hR
      subst hV
      cases htr with
      | eres =>
          have hagfn : lookupFun cenv fn = lookupFun funs₁ fn :=
            hag fn (by simp [carryCallNames, exprCallNames])
          rw [hagfn] at hlk
          obtain ⟨decl₂, cenv₂, hlk₂, hdecl, hcenvR⟩ := lookupFun_cyFunsRel hR hlk
          obtain ⟨hps, hrs, Δf, hΔf, hbrel⟩ := hdecl
          obtain ⟨resb, hsb, heqb⟩ := cy_fwd hbody hcenvR hΔf (CyRel.blockS hbrel)
          rw [show resb = _ from heqb] at hsb
          have hsb' : Step D cenv₂ (decl₂.params.zip argvals ++ bindZeros D decl₂.rets)
              st1 (.stmt (.block decl₂.body)) (.sres Vend st2 .halt) := by
            rw [← hps, ← hrs]; exact hsb
          have harity' : argvals.length = decl₂.params.length := by rw [← hps]; exact harity
          exact ⟨_, Step.callHalt hstep hlk₂ harity' hsb', .eres _⟩
  | @Step.callArgsHalt _ _ _ _ _ fn args st1 ha =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      have hargs : carryArgs bound args = true := carryExpr_call_args hsc
      obtain ⟨res₂, hstep, htr⟩ := carry_body_fwd ha funs₁ funs₂ W' hV
        (by simpa [carryBodyCode, carryCode] using hargs) hb
        (by refine hag.mono ?_; intro y hy;
            show y ∈ carryCallNames (Code.expr (.call fn args));
            simp only [carryCallNames, exprCallNames];
            exact List.mem_cons_of_mem fn (by simpa [carryCallNames] using hy)) hR
      subst hV
      cases htr with
      | eres => exact ⟨_, Step.callArgsHalt hstep, .eres _⟩
  | .argsNil =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      exact ⟨_, Step.argsNil, .eres _⟩
  | @Step.argsCons _ _ _ _ _ e rest restvals st1 v st2 hrest he =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      have hsc2 : (carryExpr bound e && carryArgs bound rest) = true := hsc
      rw [Bool.and_eq_true] at hsc2
      have hagE : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (exprCallNames e) :=
        hag.mono (fun y hy => by
          show y ∈ argsCallNames (e :: rest); exact List.mem_append.mpr (Or.inl hy))
      have hagR : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (argsCallNames rest) :=
        hag.mono (fun y hy => by
          show y ∈ argsCallNames (e :: rest); exact List.mem_append.mpr (Or.inr hy))
      obtain ⟨res₂, hstep₁, htr₁⟩ := carry_body_fwd hrest funs₁ funs₂ W' hV
        (by simpa [carryBodyCode, carryCode] using hsc2.2) hb
        (by simpa [carryCallNames] using hagR) hR
      obtain ⟨res₃, hstep₂, htr₂⟩ := carry_body_fwd he funs₁ funs₂ W' hV
        (by simpa [carryBodyCode, carryCode] using hsc2.1) hb
        (by simpa [carryCallNames] using hagE) hR
      cases htr₁ with
      | eres => cases htr₂ with
        | eres => exact ⟨_, Step.argsCons hstep₁ hstep₂, .eres _⟩
  | @Step.argsRestHalt _ _ _ _ _ e rest st1 hrest =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      have hsc2 : (carryExpr bound e && carryArgs bound rest) = true := hsc
      rw [Bool.and_eq_true] at hsc2
      have hagR : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (argsCallNames rest) :=
        hag.mono (fun y hy => by
          show y ∈ argsCallNames (e :: rest); exact List.mem_append.mpr (Or.inr hy))
      obtain ⟨res₂, hstep₁, htr₁⟩ := carry_body_fwd hrest funs₁ funs₂ W' hV
        (by simpa [carryBodyCode, carryCode] using hsc2.2) hb
        (by simpa [carryCallNames] using hagR) hR
      cases htr₁ with
      | eres => exact ⟨_, Step.argsRestHalt hstep₁, .eres _⟩
  | @Step.argsHeadHalt _ _ _ _ _ e rest restvals st1 st2 hrest he =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      have hsc2 : (carryExpr bound e && carryArgs bound rest) = true := hsc
      rw [Bool.and_eq_true] at hsc2
      have hagE : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (exprCallNames e) :=
        hag.mono (fun y hy => by
          show y ∈ argsCallNames (e :: rest); exact List.mem_append.mpr (Or.inl hy))
      have hagR : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (argsCallNames rest) :=
        hag.mono (fun y hy => by
          show y ∈ argsCallNames (e :: rest); exact List.mem_append.mpr (Or.inr hy))
      obtain ⟨res₂, hstep₁, htr₁⟩ := carry_body_fwd hrest funs₁ funs₂ W' hV
        (by simpa [carryBodyCode, carryCode] using hsc2.2) hb
        (by simpa [carryCallNames] using hagR) hR
      obtain ⟨res₃, hstep₂, htr₂⟩ := carry_body_fwd he funs₁ funs₂ W' hV
        (by simpa [carryBodyCode, carryCode] using hsc2.1) hb
        (by simpa [carryCallNames] using hagE) hR
      cases htr₁ with
      | eres => cases htr₂ with
        | eres => exact ⟨_, Step.argsHeadHalt hstep₁ hstep₂, .eres _⟩
  | .funDef =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode, carryStmt])
  | @Step.block _ _ _ _ _ body Vb stb o hbody =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      have hstmts : carryLeaveStmts bound body := hsc
      have hpost : carryPostBound bound (Code.stmt (.block body)) = bound :=
        carryPostBound_block bound body
      have hhoist : hoist D body = [] := carryLeaveStmts_hoist_nil hstmts
      have hagb : FunsAgree (calls := calls) (creates := creates)
          (hoist D body :: cenv) (hoist D body :: funs₁) (carryCallNames (.stmts body)) := by
        rw [hhoist]
        exact FunsAgree.cons_nil (by simpa [carryCallNames, stmtCallNames] using hag)
      have hRb : CyFunsRel (calls := calls) (creates := creates)
          (hoist D body :: funs₁) (hoist D body :: funs₂) := by
        rw [hhoist]; exact CyFunsRel.cons_nil hR
      obtain ⟨res₂, hstep, htr⟩ :=
        carry_body_fwd hbody (hoist D body :: funs₁) (hoist D body :: funs₂) W' hV
          hstmts hb hagb hRb
      have hlenV : V₁.length ≤ Vb.length := venvLen_mono hbody rfl
      have hkeysV := venvKeys_suffix hbody rfl
      subst hV
      cases htr with
      | @norm A' st' hk =>
          have hlen : A.length ≤ A'.length := by
            rw [List.length_append, List.length_append] at hlenV; omega
          refine ⟨_, Step.block hstep, ?_⟩
          rw [hpost, restore_append hlen, restore_append hlen]
          exact .norm (fun x hx => by
            rw [restore_keys (keys_suffix_cancel hkeysV) hlen]; exact hb x hx)
      | @halt A' st' =>
          have hlen : A.length ≤ A'.length := by
            rw [List.length_append, List.length_append] at hlenV; omega
          refine ⟨_, Step.block hstep, ?_⟩
          rw [restore_append hlen, restore_append hlen]; exact .halt
      | @«leave» A' st' =>
          have hlen : A.length ≤ A'.length := by
            rw [List.length_append, List.length_append] at hlenV; omega
          refine ⟨_, Step.block hstep, ?_⟩
          rw [restore_append hlen, restore_append hlen]; exact TResL.leave
  | @Step.letZero _ _ _ _ _ vars =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      subst hV
      refine ⟨_, Step.letZero, ?_⟩
      rw [show bindZeros D vars ++ (A ++ W) = (bindZeros D vars ++ A) ++ W from
            (List.append_assoc _ _ _).symm,
          show bindZeros D vars ++ (A ++ W') = (bindZeros D vars ++ A) ++ W' from
            (List.append_assoc _ _ _).symm]
      refine .norm (fun x hx => ?_)
      have hpost : carryPostBound bound (Code.stmt (.letDecl vars none)) = vars ++ bound := by
        simp [carryPostBound, carryStmt]
      rw [hpost] at hx
      rw [List.map_append, bindZeros_keys]
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append.mpr (Or.inl hx)
      · exact List.mem_append.mpr (Or.inr (hb x hx))
  | @Step.letVal _ _ _ _ _ vars e vals st1 he hlen =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      have hse : carryExpr bound e = true := by
        have h2 : (carryStmt bound (.letDecl vars (some e))).isSome = true := hsc
        by_cases hc : carryExpr bound e = true
        · exact hc
        · simp [carryStmt, hc] at h2
      obtain ⟨res₂, hstep, htr⟩ := carry_body_fwd he funs₁ funs₂ W' hV
        (by simpa [carryBodyCode, carryCode] using hse) hb
        (by simpa [carryCallNames, stmtCallNames] using hag) hR
      subst hV
      cases htr with
      | eres =>
          refine ⟨_, Step.letVal hstep hlen, ?_⟩
          rw [show vars.zip vals ++ (A ++ W) = (vars.zip vals ++ A) ++ W from
                (List.append_assoc _ _ _).symm,
              show vars.zip vals ++ (A ++ W') = (vars.zip vals ++ A) ++ W' from
                (List.append_assoc _ _ _).symm]
          refine .norm (fun x hx => ?_)
          have hpost : carryPostBound bound (Code.stmt (.letDecl vars (some e))) =
              vars ++ bound := by simp [carryPostBound, carryStmt, hse]
          rw [hpost] at hx
          rw [List.map_append, List.map_fst_zip (by omega)]
          rcases List.mem_append.mp hx with hx | hx
          · exact List.mem_append.mpr (Or.inl hx)
          · exact List.mem_append.mpr (Or.inr (hb x hx))
  | @Step.letHalt _ _ _ _ _ vars e st1 he =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      have hse : carryExpr bound e = true := by
        have h2 : (carryStmt bound (.letDecl vars (some e))).isSome = true := hsc
        by_cases hc : carryExpr bound e = true
        · exact hc
        · simp [carryStmt, hc] at h2
      obtain ⟨res₂, hstep, htr⟩ := carry_body_fwd he funs₁ funs₂ W' hV
        (by simpa [carryBodyCode, carryCode] using hse) hb
        (by simpa [carryCallNames, stmtCallNames] using hag) hR
      subst hV
      cases htr with
      | eres => exact ⟨_, Step.letHalt hstep, .halt⟩
  | @Step.assignVal _ _ _ _ _ vars e vals st1 he hlen =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      have hsc' : vars.all bound.contains = true ∧ carryExpr bound e = true := by
        have h2 : (carryStmt bound (.assign vars e)).isSome = true := hsc
        by_cases hc : (vars.all bound.contains && carryExpr bound e) = true
        · rw [Bool.and_eq_true] at hc; exact hc
        · simp [carryStmt, hc] at h2
      have hvars : ∀ x ∈ vars, x ∈ A.map Prod.fst := fun x hx =>
        hb x (all_contains_subset hsc'.1 x hx)
      obtain ⟨res₂, hstep, htr⟩ := carry_body_fwd he funs₁ funs₂ W' hV
        (by simpa [carryBodyCode, carryCode] using hsc'.2) hb
        (by simpa [carryCallNames, stmtCallNames] using hag) hR
      subst hV
      cases htr with
      | eres =>
          refine ⟨_, Step.assignVal hstep hlen, ?_⟩
          rw [VEnv.setMany_append_mem hvars, VEnv.setMany_append_mem hvars]
          refine .norm (fun x hx => ?_)
          have hpost : carryPostBound bound (Code.stmt (.assign vars e)) = bound := by
            simp [carryPostBound, carryStmt, hsc'.1, hsc'.2]
          rw [hpost] at hx
          rw [VEnv.setMany_keys («D» := D)]
          exact hb x hx
  | @Step.assignHalt _ _ _ _ _ vars e st1 he =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      have hse : carryExpr bound e = true := by
        have h2 : (carryStmt bound (.assign vars e)).isSome = true := hsc
        by_cases hc : (vars.all bound.contains && carryExpr bound e) = true
        · rw [Bool.and_eq_true] at hc; exact hc.2
        · simp [carryStmt, hc] at h2
      obtain ⟨res₂, hstep, htr⟩ := carry_body_fwd he funs₁ funs₂ W' hV
        (by simpa [carryBodyCode, carryCode] using hse) hb
        (by simpa [carryCallNames, stmtCallNames] using hag) hR
      subst hV
      cases htr with
      | eres => exact ⟨_, Step.assignHalt hstep, .halt⟩
  | @Step.exprStmt _ _ _ _ _ e st1 he =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      have hse : carryExpr bound e = true := by
        have h2 : (carryStmt bound (.exprStmt e)).isSome = true := hsc
        by_cases hc : carryExpr bound e = true
        · exact hc
        · simp [carryStmt, hc] at h2
      obtain ⟨res₂, hstep, htr⟩ := carry_body_fwd he funs₁ funs₂ W' hV
        (by simpa [carryBodyCode, carryCode] using hse) hb
        (by simpa [carryCallNames, stmtCallNames] using hag) hR
      subst hV
      cases htr with
      | eres =>
          refine ⟨_, Step.exprStmt hstep, ?_⟩
          refine .norm (fun x hx => ?_)
          have hpost : carryPostBound bound (Code.stmt (.exprStmt e)) = bound := by
            simp [carryPostBound, carryStmt, hse]
          rw [hpost] at hx
          exact hb x hx
  | @Step.exprStmtHalt _ _ _ _ _ e st1 he =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      have hse : carryExpr bound e = true := by
        have h2 : (carryStmt bound (.exprStmt e)).isSome = true := hsc
        by_cases hc : carryExpr bound e = true
        · exact hc
        · simp [carryStmt, hc] at h2
      obtain ⟨res₂, hstep, htr⟩ := carry_body_fwd he funs₁ funs₂ W' hV
        (by simpa [carryBodyCode, carryCode] using hse) hb
        (by simpa [carryCallNames, stmtCallNames] using hag) hR
      subst hV
      cases htr with
      | eres => exact ⟨_, Step.exprStmtHalt hstep, .halt⟩
  | @Step.ifTrue _ _ _ _ _ c body cv st1 V' st2 o hc hcv hbody =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      have hsc' : carryExpr bound c = true ∧ carryStmts bound body = true := by
        have h2 : (carryStmt bound (.cond c body)).isSome = true := hsc
        by_cases hcnd : (carryExpr bound c && carryStmts bound body) = true
        · rw [Bool.and_eq_true] at hcnd; exact hcnd
        · simp [carryStmt, hcnd] at h2
      have hagc : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (exprCallNames c) :=
        hag.mono (fun y hy => by
          show y ∈ stmtCallNames (.cond c body); exact List.mem_append.mpr (Or.inl hy))
      have hagb : FunsAgree (calls := calls) (creates := creates) cenv funs₁
          (carryCallNames (.stmt (.block body))) :=
        hag.mono (fun y hy => by
          show y ∈ stmtCallNames (.cond c body)
          exact List.mem_append.mpr (Or.inr (by simpa [carryCallNames, stmtCallNames] using hy)))
      obtain ⟨res₂, hstepc, htrc⟩ := carry_body_fwd hc funs₁ funs₂ W' hV
        (by simpa [carryBodyCode, carryCode] using hsc'.1) hb hagc hR
      have hscb : carryBodyCode bound (Code.stmt (.block body)) := Or.inl hsc'.2
      obtain ⟨res₃, hstepb, htrb⟩ := carry_body_fwd hbody funs₁ funs₂ W' hV hscb hb hagb hR
      subst hV
      cases htrc with
      | eres =>
          have hpostb : carryPostBound bound (Code.stmt (.block body)) = bound :=
            carryPostBound_block bound body
          have hpost : carryPostBound bound (Code.stmt (.cond c body)) = bound := by
            simp [carryPostBound, carryStmt, hsc'.1, hsc'.2]
          rw [hpostb] at htrb
          rw [hpost]
          cases htrb with
          | norm hk => exact ⟨_, Step.ifTrue hstepc hcv hstepb, .norm hk⟩
          | halt => exact ⟨_, Step.ifTrue hstepc hcv hstepb, .halt⟩
          | «leave» => exact ⟨_, Step.ifTrue hstepc hcv hstepb, TResL.leave⟩
  | @Step.ifFalse _ _ _ _ _ c body cv st1 hc hcv =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      have hsc' : carryExpr bound c = true := by
        have h2 : (carryStmt bound (.cond c body)).isSome = true := hsc
        by_cases hcnd : (carryExpr bound c && carryStmts bound body) = true
        · rw [Bool.and_eq_true] at hcnd; exact hcnd.1
        · simp [carryStmt, hcnd] at h2
      have hagc : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (exprCallNames c) :=
        hag.mono (fun y hy => by
          show y ∈ stmtCallNames (.cond c body); exact List.mem_append.mpr (Or.inl hy))
      obtain ⟨res₂, hstepc, htrc⟩ := carry_body_fwd hc funs₁ funs₂ W' hV
        (by simpa [carryBodyCode, carryCode] using hsc') hb hagc hR
      subst hV
      cases htrc with
      | eres =>
          refine ⟨_, Step.ifFalse hstepc hcv, .norm (fun x hx => ?_)⟩
          exact hb x (by
            have : carryPostBound bound (Code.stmt (.cond c body)) = bound := by
              simp only [carryPostBound, carryStmt]; split <;> rfl
            rwa [this] at hx)
  | @Step.ifHalt _ _ _ _ _ c body st1 hc =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      have hsc' : carryExpr bound c = true := by
        have h2 : (carryStmt bound (.cond c body)).isSome = true := hsc
        by_cases hcnd : (carryExpr bound c && carryStmts bound body) = true
        · rw [Bool.and_eq_true] at hcnd; exact hcnd.1
        · simp [carryStmt, hcnd] at h2
      have hagc : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (exprCallNames c) :=
        hag.mono (fun y hy => by
          show y ∈ stmtCallNames (.cond c body); exact List.mem_append.mpr (Or.inl hy))
      obtain ⟨res₂, hstepc, htrc⟩ := carry_body_fwd hc funs₁ funs₂ W' hV
        (by simpa [carryBodyCode, carryCode] using hsc') hb hagc hR
      subst hV
      cases htrc with
      | eres => exact ⟨_, Step.ifHalt hstepc, .halt⟩
  | @Step.switchExec _ _ _ _ _ c cases' dflt cv st1 V' st2 o hc hsel =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      have hsc' : carryExpr bound c = true ∧ carryCases bound cases' = true ∧
          carryDflt bound dflt = true := by
        have h2 : (carryStmt bound (.switch c cases' dflt)).isSome = true := hsc
        by_cases hcnd : (carryExpr bound c && carryCases bound cases' &&
            carryDflt bound dflt) = true
        · rw [Bool.and_eq_true, Bool.and_eq_true] at hcnd; exact ⟨hcnd.1.1, hcnd.1.2, hcnd.2⟩
        · simp [carryStmt, hcnd] at h2
      have hagc : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (exprCallNames c) :=
        hag.mono (fun y hy => by
          show y ∈ stmtCallNames (.switch c cases' dflt)
          exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hy))))
      have hagsel : FunsAgree (calls := calls) (creates := creates) cenv funs₁
          (carryCallNames (.stmt (.block (selectSwitch D cv cases' dflt)))) := by
        refine hag.mono (fun y hy => ?_)
        show y ∈ stmtCallNames (.switch c cases' dflt)
        have hsub := selectSwitch_callNames_sub (calls := calls) (creates := creates)
          (cv := cv) (cases := cases') (dflt := dflt) y
          (by simpa [carryCallNames, stmtCallNames] using hy)
        rcases List.mem_append.mp hsub with hh | hh
        · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hh)))
        · exact List.mem_append.mpr (Or.inr hh)
      obtain ⟨res₂, hstepc, htrc⟩ := carry_body_fwd hc funs₁ funs₂ W' hV
        (by simpa [carryBodyCode, carryCode] using hsc'.1) hb hagc hR
      have hsels : carryStmts bound (selectSwitch D cv cases' dflt) = true :=
        carry_selectSwitch hsc'.2.1 hsc'.2.2
      have hscb : carryBodyCode bound (Code.stmt (.block (selectSwitch D cv cases' dflt))) :=
        Or.inl hsels
      obtain ⟨res₃, hstepb, htrb⟩ := carry_body_fwd hsel funs₁ funs₂ W' hV hscb hb hagsel hR
      subst hV
      cases htrc with
      | eres =>
          have hpostb : carryPostBound bound
              (Code.stmt (.block (selectSwitch D cv cases' dflt))) = bound :=
            carryPostBound_block bound _
          have hpost : carryPostBound bound (Code.stmt (.switch c cases' dflt)) = bound := by
            simp [carryPostBound, carryStmt, hsc'.1, hsc'.2.1, hsc'.2.2]
          rw [hpostb] at htrb
          rw [hpost]
          cases htrb with
          | norm hk => exact ⟨_, Step.switchExec hstepc hstepb, .norm hk⟩
          | halt => exact ⟨_, Step.switchExec hstepc hstepb, .halt⟩
          | «leave» => exact ⟨_, Step.switchExec hstepc hstepb, TResL.leave⟩
  | @Step.switchHalt _ _ _ _ _ c cases' dflt st1 hc =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      have hsc' : carryExpr bound c = true := by
        have h2 : (carryStmt bound (.switch c cases' dflt)).isSome = true := hsc
        by_cases hcnd : (carryExpr bound c && carryCases bound cases' &&
            carryDflt bound dflt) = true
        · rw [Bool.and_eq_true, Bool.and_eq_true] at hcnd; exact hcnd.1.1
        · simp [carryStmt, hcnd] at h2
      have hagc : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (exprCallNames c) :=
        hag.mono (fun y hy => by
          show y ∈ stmtCallNames (.switch c cases' dflt)
          exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hy))))
      obtain ⟨res₂, hstepc, htrc⟩ := carry_body_fwd hc funs₁ funs₂ W' hV
        (by simpa [carryBodyCode, carryCode] using hsc') hb hagc hR
      subst hV
      cases htrc with
      | eres => exact ⟨_, Step.switchHalt hstepc, .halt⟩
  | @Step.forLoop _ _ _ _ _ init c post body Vinit stinit Vend stend o hinit hloop =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode, carryStmt])
  | @Step.forInitHalt _ _ _ _ _ init c post body Vinit stinit hinit =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode, carryStmt])
  | .«break» =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode, carryStmt])
  | .«continue» =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode, carryStmt])
  | .«leave» =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode, carryStmt])
  | .seqNil =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      subst hV
      exact ⟨_, Step.seqNil, .norm (fun x hx => by simp [carryPostBound] at hx)⟩
  | @Step.seqCons _ _ _ _ _ s rest V1 st1 V2 st2 o hs hrest =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      have hlv : carryLeaveStmts bound (s :: rest) := hsc
      rcases carryLeaveStmts_cons_inv hlv with ⟨bound₁, hstmt, hrest'⟩ | ⟨rfl, rfl⟩
      · have hags : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (stmtCallNames s) :=
          hag.mono (fun y hy => by
            show y ∈ stmtsCallNames (s :: rest); exact List.mem_append.mpr (Or.inl hy))
        have hagr : FunsAgree (calls := calls) (creates := creates) cenv funs₁
            (stmtsCallNames rest) :=
          hag.mono (fun y hy => by
            show y ∈ stmtsCallNames (s :: rest); exact List.mem_append.mpr (Or.inr hy))
        obtain ⟨res₂, hstep₁, htr₁⟩ := carry_body_fwd hs funs₁ funs₂ W' hV
          (carryBodyCode_of_stmt hstmt) hb
          (by simpa [carryCallNames] using hags) hR
        have hpost₁ : carryPostBound bound (Code.stmt s) = bound₁ := by
          simp [carryPostBound, hstmt]
        rw [hpost₁] at htr₁
        obtain ⟨A₁, hV1, hres₂, hk⟩ := TResL.norm_inv htr₁
        obtain ⟨res₃, hstep₂, htr₂⟩ := carry_body_fwd hrest funs₁ funs₂ W' hV1
          hrest' hk (by simpa [carryCallNames] using hagr) hR
        subst hres₂
        cases htr₂ with
        | norm hk₂ => exact ⟨_, Step.seqCons hstep₁ hstep₂, .norm hk₂⟩
        | halt => exact ⟨_, Step.seqCons hstep₁ hstep₂, .halt⟩
        | «leave» => exact ⟨_, Step.seqCons hstep₁ hstep₂, TResL.leave⟩
      · cases hs
  | @Step.seqStop _ _ _ _ _ s rest V1 st1 o hs hne =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      have hlv : carryLeaveStmts bound (s :: rest) := hsc
      rcases carryLeaveStmts_cons_inv hlv with ⟨bound₁, hstmt, hrest'⟩ | ⟨rfl, rfl⟩
      · have hags : FunsAgree (calls := calls) (creates := creates) cenv funs₁ (stmtCallNames s) :=
          hag.mono (fun y hy => by
            show y ∈ stmtsCallNames (s :: rest); exact List.mem_append.mpr (Or.inl hy))
        obtain ⟨res₂, hstep₁, htr₁⟩ := carry_body_fwd hs funs₁ funs₂ W' hV
          (carryBodyCode_of_stmt hstmt) hb
          (by simpa [carryCallNames] using hags) hR
        cases htr₁ with
        | norm hk => exact absurd rfl hne
        | halt => exact ⟨_, Step.seqStop hstep₁ (by simp), .halt⟩
        | «leave» => exact ⟨_, Step.seqStop hstep₁ (by simp), TResL.leave⟩
      · cases hs with
        | «leave» => subst hV; exact ⟨_, Step.seqStop Step.leave (by simp), TResL.leave⟩
  | .loopDone hc hcz =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode])
  | .loopCondHalt hc =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode])
  | .loopStep hc hcv hbody hob hpost hnext =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode])
  | .loopPostHalt hc hcv hbody hob hpost =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode])
  | .loopBreak hc hcv hbody =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode])
  | .loopLeave hc hcv hbody =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode])
  | .loopBodyHalt hc hcv hbody =>
      intro A W bound funs₁ funs₂ W' hV hsc hb hag hR
      exact absurd hsc (by simp [carryBodyCode, carryCode])
  termination_by structural h

end

end YulEvmCompiler.Optimizer
