import YulEvmCompiler.Optimizer.Implementation.Normalization.DisambiguateRen
/-!
# Semantic soundness of name disambiguation — the backward simulation

The mirror of `sim_fwd`: a *target* `Step` (on the disambiguated program) pulls
back to a source `Step` whose renamed result is the target's. Same relation,
same environment configs (stated on source objects), same transport equalities
used in the reverse direction — no inverse renaming is needed.
-/

namespace YulEvmCompiler.Optimizer.Normalize

open YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

set_option maxHeartbeats 1600000 in
theorem sim_bwd {funs₂ : FunEnv D} {V₂ mst code₂ res₂} (h : Step D funs₂ V₂ mst code₂ res₂) :
    ∀ {lo hi : Nat} {σ φ σ' φ' funs₁ V₁ code₁}, V₂ = renVEnv σ V₁ →
      RenCfg σ V₁ lo → RenFCfg φ funs₁ lo → RenFunsRelF φ funs₁ funs₂ →
      WScopedCode (V₁.map Prod.fst) code₁ → FScopedCode (funNamesOf funs₁) code₁ →
      NScopedCode (V₁.map Prod.fst) (funNamesOf funs₁) code₁ →
      AlphaCode lo hi σ φ σ' φ' code₁ code₂ →
      ∃ res₁, Step D funs₁ V₁ mst code₁ res₁ ∧ res₂ = renRes σ' res₁ ∧ ResOK σ' hi res₁ := by
  induction h with
  | @lit funs V st l =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | expr hae => cases hae with | lit =>
          exact ⟨_, Step.lit, rfl, trivial⟩
  | @var funs V st y v hv =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | expr hae => cases hae with | var hx =>
          refine ⟨_, Step.var ?_, rfl, trivial⟩
          rw [renVEnv_get σ V₁ _ (hcfg.no_merge hx)] at hv
          exact hv
  | @builtinOk funs V st op args argvals st1 rets st2 ha hb iha =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | expr hae => cases hae with | builtin ha2 =>
          obtain ⟨r₁, hstep₁, hreq, -⟩ := iha hV hcfg hφ hfuns (by trivial) (by trivial) (by exact hns)
            (.args (lo := lo) (hi := hi) ha2)
          have hr := renRes_eres_inv hreq
          subst hr
          exact ⟨_, Step.builtinOk hstep₁ hb, rfl, trivial⟩
  | @builtinHalt funs V st op args argvals st1 st2 ha hb iha =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | expr hae => cases hae with | builtin ha2 =>
          obtain ⟨r₁, hstep₁, hreq, -⟩ := iha hV hcfg hφ hfuns (by trivial) (by trivial) (by exact hns)
            (.args (lo := lo) (hi := hi) ha2)
          have hr := renRes_eres_inv hreq
          subst hr
          exact ⟨_, Step.builtinHalt hstep₁ hb, rfl, trivial⟩
  | @builtinArgsHalt funs V st op args st1 ha iha =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | expr hae => cases hae with | builtin ha2 =>
          obtain ⟨r₁, hstep₁, hreq, -⟩ := iha hV hcfg hφ hfuns (by trivial) (by trivial) (by exact hns)
            (.args (lo := lo) (hi := hi) ha2)
          have hr := renRes_eres_inv hreq
          subst hr
          exact ⟨_, Step.builtinArgsHalt hstep₁, rfl, trivial⟩
  | @callArgsHalt funs V st fn₂ args st1 ha iha =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | expr hae => cases hae with | call hfn ha2 =>
          obtain ⟨r₁, hstep₁, hreq, -⟩ := iha hV hcfg hφ hfuns (by trivial) (by trivial)
            (by exact hns.2) (.args (lo := lo) (hi := hi) ha2)
          have hr := renRes_eres_inv hreq
          subst hr
          exact ⟨_, Step.callArgsHalt hstep₁, rfl, trivial⟩
  | @argsNil funs V st =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | args hae => cases hae with | nil =>
          exact ⟨_, Step.argsNil, rfl, trivial⟩
  | @argsCons funs V st e rest restvals st1 v st2 hrest he ihrest ihe =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | args hae => cases hae with | cons he2 hr2 =>
          obtain ⟨r₁, hstep_r, hreq_r, -⟩ := ihrest hV hcfg hφ hfuns (by trivial) (by trivial)
            (by exact hns.2) (.args (lo := lo) (hi := hi) hr2)
          have hr := renRes_eres_inv hreq_r
          subst hr
          obtain ⟨r₂, hstep_e, hreq_e, -⟩ := ihe hV hcfg hφ hfuns (by trivial) (by trivial)
            (by exact hns.1) (.expr (lo := lo) (hi := hi) he2)
          have hr := renRes_eres_inv hreq_e
          subst hr
          exact ⟨_, Step.argsCons hstep_r hstep_e, rfl, trivial⟩
  | @argsRestHalt funs V st e rest st1 hrest ihrest =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | args hae => cases hae with | cons he2 hr2 =>
          obtain ⟨r₁, hstep_r, hreq_r, -⟩ := ihrest hV hcfg hφ hfuns (by trivial) (by trivial)
            (by exact hns.2) (.args (lo := lo) (hi := hi) hr2)
          have hr := renRes_eres_inv hreq_r
          subst hr
          exact ⟨_, Step.argsRestHalt hstep_r, rfl, trivial⟩
  | @argsHeadHalt funs V st e rest restvals st1 st2 hrest he ihrest ihe =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | args hae => cases hae with | cons he2 hr2 =>
          obtain ⟨r₁, hstep_r, hreq_r, -⟩ := ihrest hV hcfg hφ hfuns (by trivial) (by trivial)
            (by exact hns.2) (.args (lo := lo) (hi := hi) hr2)
          have hr := renRes_eres_inv hreq_r
          subst hr
          obtain ⟨r₂, hstep_e, hreq_e, -⟩ := ihe hV hcfg hφ hfuns (by trivial) (by trivial)
            (by exact hns.1) (.expr (lo := lo) (hi := hi) he2)
          have hr := renRes_eres_inv hreq_e
          subst hr
          exact ⟨_, Step.argsHeadHalt hstep_r hstep_e, rfl, trivial⟩
  | @funDef funs V st n₂ ps₂ rs₂ b₂ =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | stmt hs => cases hs with | funD _ _ _ _ hrn hbe =>
          exact ⟨_, Step.funDef, rfl,
            hcfg.mono (Nat.le_trans hrn.2.2 (alphaBlockExt_le hbe))⟩
  | @«break» funs V st =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | stmt hs => cases hs with | breakD hle =>
          exact ⟨_, Step.break, rfl, trivial⟩
  | @«continue» funs V st =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | stmt hs => cases hs with | contD hle =>
          exact ⟨_, Step.continue, rfl, trivial⟩
  | @leave funs V st =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | stmt hs => cases hs with | leaveD hle =>
          exact ⟨_, Step.leave, rfl, trivial⟩
  | @seqNil funs V st =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | stmts hss => cases hss with | nil hle =>
          exact ⟨_, Step.seqNil, rfl, hcfg.mono hle⟩
  | @exprStmt funs V st e st1 he ihe =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | stmt hs => cases hs with | exprD hle he2 =>
          obtain ⟨r₁, hstep_e, hreq, -⟩ := ihe rfl hcfg hφ hfuns (by trivial) (by trivial) (by exact hns)
            (.expr (lo := lo) (hi := hi) he2)
          have hr := renRes_eres_inv hreq
          subst hr
          exact ⟨_, Step.exprStmt hstep_e, rfl, hcfg.mono hle⟩
  | @exprStmtHalt funs V st e st1 he ihe =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | stmt hs => cases hs with | exprD _ he2 =>
          obtain ⟨r₁, hstep_e, hreq, -⟩ := ihe rfl hcfg hφ hfuns (by trivial) (by trivial) (by exact hns)
            (.expr (lo := lo) (hi := hi) he2)
          have hr := renRes_eres_inv hreq
          subst hr
          exact ⟨_, Step.exprStmtHalt hstep_e, rfl, trivial⟩
  | @assignVal funs V st vars₂ e₂ vals st1 he hlen ihe =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | stmt hs => cases hs with | @assignD _ _ _ _ vars _ _ hle hvars he2 =>
          obtain ⟨r₁, hstep_e, hreq, -⟩ := ihe rfl hcfg hφ hfuns (by trivial) (by trivial)
            (by exact hns.2) (.expr (lo := lo) (hi := hi) he2)
          have hr := renRes_eres_inv hreq
          subst hr
          have hnm : ∀ x ∈ vars, ∀ k ∈ V₁.map Prod.fst, σ k = σ x → k = x := by
            intro x hx k hk hkeq
            obtain ⟨p, hp, hpk⟩ := List.mem_map.mp hk
            subst hpk
            exact hcfg.no_merge (hvars x hx) p hp hkeq
          refine ⟨_, Step.assignVal hstep_e (by rw [List.length_map] at hlen; exact hlen),
            ?_, (RenCfg.setMany hcfg vars vals).mono hle⟩
          show _ = Res.sres (renVEnv σ (VEnv.setMany V₁ vars vals)) st1 .normal
          rw [← renVEnv_setMany_dom σ vars vals V₁ hnm]
  | @assignHalt funs V st vars₂ e₂ st1 he ihe =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | stmt hs => cases hs with | assignD _ hvars he2 =>
          obtain ⟨r₁, hstep_e, hreq, -⟩ := ihe rfl hcfg hφ hfuns (by trivial) (by trivial)
            (by exact hns.2) (.expr (lo := lo) (hi := hi) he2)
          have hr := renRes_eres_inv hreq
          subst hr
          exact ⟨_, Step.assignHalt hstep_e, rfl, trivial⟩
  | @ifHalt funs V st c₂ body₂ st1 hc ihc =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | stmt hs => cases hs with | condD hc2 hb2 =>
          obtain ⟨r₁, hstep_c, hreq, -⟩ := ihc rfl hcfg hφ hfuns (by trivial) (by trivial)
            (by exact hns.1) (.expr (lo := lo) (hi := hi) hc2)
          have hr := renRes_eres_inv hreq
          subst hr
          exact ⟨_, Step.ifHalt hstep_c, rfl, trivial⟩
  | @switchHalt funs V st c₂ cs₂ dflt₂ st1 hc ihc =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | stmt hs => cases hs with | switchD hc2 hcs2 hd2 =>
          obtain ⟨r₁, hstep_c, hreq, -⟩ := ihc rfl hcfg hφ hfuns (by trivial) (by trivial)
            (by exact hns.1) (.expr (lo := lo) (hi := hi) hc2)
          have hr := renRes_eres_inv hreq
          subst hr
          exact ⟨_, Step.switchHalt hstep_c, rfl, trivial⟩
  | @loopCondHalt funs V st c₂ post₂ body₂ st1 hc ihc =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | loop hc2 hb2 hp2 =>
          obtain ⟨r₁, hstep_c, hreq, -⟩ := ihc rfl hcfg hφ hfuns (by trivial) (by trivial)
            (by exact hns.1) (.expr (lo := lo) (hi := hi) hc2)
          have hr := renRes_eres_inv hreq
          subst hr
          exact ⟨_, Step.loopCondHalt hstep_c, rfl, trivial⟩
  | @loopDone funs V st c₂ post₂ body₂ cv st1 hc hz ihc =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | loop hc2 hb2 hp2 =>
          obtain ⟨r₁, hstep_c, hreq, -⟩ := ihc rfl hcfg hφ hfuns (by trivial) (by trivial)
            (by exact hns.1) (.expr (lo := lo) (hi := hi) hc2)
          have hr := renRes_eres_inv hreq
          subst hr
          exact ⟨_, Step.loopDone hstep_c hz, rfl,
            hcfg.mono (Nat.le_trans (alphaBlockExt_le hb2) (alphaBlockExt_le hp2))⟩
  | @ifFalse funs V st c₂ body₂ cv st1 hc hz ihc =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | stmt hs => cases hs with | condD hc2 hb2 =>
          obtain ⟨r₁, hstep_c, hreq, -⟩ := ihc rfl hcfg hφ hfuns (by trivial) (by trivial)
            (by exact hns.1) (.expr (lo := lo) (hi := hi) hc2)
          have hr := renRes_eres_inv hreq
          subst hr
          exact ⟨_, Step.ifFalse hstep_c hz, rfl, hcfg.mono (alphaBlockExt_le hb2)⟩
  | @letZero funs V st vars₂ =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | stmt hs => cases hs with
        | @letD _ _ _ _ vars _ eo _ hvnd hlen hvNF hrn ho => cases ho with | none =>
            have hsc' : ∀ x ∈ vars, x ∉ V₁.map Prod.fst := hsc
            have hW : (bindZeros D vars ++ V₁).map Prod.fst = vars ++ V₁.map Prod.fst := by
              simp [bindZeros, List.map_append, List.map_map, Function.comp_def]
            have hagree : renVEnv (updRen σ (vars.zip vars₂)) V₁ = renVEnv σ V₁ :=
              renVEnv_congr (fun p hp => updRen_of_not_mem
                (fun q hq hqp => hsc' p.1 (hqp ▸ (List.of_mem_zip hq).1) (List.mem_map_of_mem hp)))
            refine ⟨_, Step.letZero, ?_, RenCfg.extend hcfg hvnd hlen hvNF hrn hsc' hW⟩
            show _ = Res.sres (renVEnv (updRen σ (vars.zip vars₂)) (bindZeros D vars ++ V₁)) st .normal
            rw [renVEnv_append, renVEnv_bindZeros, map_updRen_zip hvnd hlen, hagree]
  | @letVal funs V st vars₂ e₂ vals st1 hval hlen0 ihe =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | stmt hs => cases hs with
        | @letD _ _ _ _ vars _ eo _ hvnd hlen hvNF hrn ho => cases ho with | @some e₁ _ he' =>
            obtain ⟨r₁, hstep_e, hreq, -⟩ := ihe rfl hcfg hφ hfuns (by trivial) (by trivial) (by exact hns)
              (.expr (lo := lo) (hi := hi) he')
            have hr := renRes_eres_inv hreq
            subst hr
            have hsc' : ∀ x ∈ vars, x ∉ V₁.map Prod.fst := hsc
            have hW : (vars.zip vals ++ V₁).map Prod.fst = vars ++ V₁.map Prod.fst := by
              rw [List.map_append, List.map_fst_zip
                (Nat.le_of_eq (hlen0.trans hlen.symm).symm)]
            have hagree : renVEnv (updRen σ (vars.zip vars₂)) V₁ = renVEnv σ V₁ :=
              renVEnv_congr (fun p hp => updRen_of_not_mem
                (fun q hq hqp => hsc' p.1 (hqp ▸ (List.of_mem_zip hq).1) (List.mem_map_of_mem hp)))
            refine ⟨_, Step.letVal hstep_e (hlen0.trans hlen.symm), ?_,
              RenCfg.extend hcfg hvnd hlen hvNF hrn hsc' hW⟩
            show _ = Res.sres (renVEnv (updRen σ (vars.zip vars₂)) (vars.zip vals ++ V₁)) st1 .normal
            rw [renVEnv_append, hagree, renVEnv_zip, map_updRen_zip hvnd hlen]
  | @letHalt funs V st vars₂ e₂ st1 hval ihe =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | stmt hs => cases hs with
        | @letD _ _ _ _ vars _ eo _ hvnd hlen hvNF hrn ho => cases ho with | @some e₁ _ he' =>
            obtain ⟨r₁, hstep_e, hreq, -⟩ := ihe rfl hcfg hφ hfuns (by trivial) (by trivial) (by exact hns)
              (.expr (lo := lo) (hi := hi) he')
            have hr := renRes_eres_inv hreq
            subst hr
            have hsc' : ∀ x ∈ vars, x ∉ V₁.map Prod.fst := hsc
            have hagree : renVEnv (updRen σ (vars.zip vars₂)) V₁ = renVEnv σ V₁ :=
              renVEnv_congr (fun p hp => updRen_of_not_mem
                (fun q hq hqp => hsc' p.1 (hqp ▸ (List.of_mem_zip hq).1) (List.mem_map_of_mem hp)))
            refine ⟨_, Step.letHalt hstep_e, ?_, trivial⟩
            show _ = Res.sres (renVEnv (updRen σ (vars.zip vars₂)) V₁) st1 .halt
            rw [hagree]
  | @seqCons funs V st s₂ rest₂ V1₂ st1 V2₂ st2 o hs₂ hrest₂ ihs ihrest =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | stmts hss => cases hss with
        | @cons _ _ _ _ _ s₁ _ rest₁ _ σmid φmid _ _ hs1 hrest1 =>
          obtain ⟨hsc_s, hsc_r⟩ := (hsc : WScopedStmt (V₁.map Prod.fst) s₁ ∧
            WScopedStmts (declVars s₁ ++ V₁.map Prod.fst) rest₁)
          obtain ⟨hfsc_s, hfsc_r⟩ := (hfsc : FScopedStmt _ s₁ ∧ FScopedStmts _ rest₁)
          obtain ⟨hns_s, hns_r⟩ := (hns : NormalForm.ScopedStmt _ _ s₁ ∧
            NormalForm.ScopedStmts (V₁.map Prod.fst ++ NormalForm.declTopVars s₁) _ rest₁)
          obtain ⟨r₁, hstep_s, hreq_s, hcfg1⟩ := ihs rfl hcfg hφ hfuns (by exact hsc_s) (by exact hfsc_s) (by exact hns_s)
            (.stmt hs1)
          obtain ⟨V1₁, hr₁eq, hV1⟩ := renRes_sres_inv hreq_s
          subst hr₁eq
          have hpe := hs1.phi_eq; subst hpe
          have hk : V1₁.map Prod.fst = declVars s₁ ++ V₁.map Prod.fst := venvKeys_stmt hstep_s
          obtain ⟨r₂, hstep_r, hreq_r, hcfgr⟩ := ihrest hV1 hcfg1
            (hφ.mono (alphaStmt1_le hs1)) hfuns
            (by show WScopedStmts (V1₁.map Prod.fst) rest₁; rw [hk]; exact hsc_r)
            (by exact hfsc_r)
            (by
              show NormalForm.ScopedStmts (V1₁.map Prod.fst) _ rest₁
              rw [hk]
              refine scopedStmts_mono (fun x hx => ?_) (fun x hx => hx) hns_r
              rw [declVars_eq_declTopVars]
              rcases List.mem_append.mp hx with h2 | h2
              · exact List.mem_append.mpr (Or.inr h2)
              · exact List.mem_append.mpr (Or.inl h2))
            (.stmts hrest1)
          obtain ⟨V2₁, hr₂eq, hV2⟩ := renRes_sres_inv hreq_r
          subst hr₂eq
          refine ⟨_, Step.seqCons hstep_s hstep_r, ?_, hcfgr⟩
          show _ = Res.sres (renVEnv σ' V2₁) st2 o
          rw [← hV2]
  | @seqStop funs V st s₂ rest₂ V1₂ st1 o hs₂ hne ihs =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | stmts hss => cases hss with
        | @cons _ _ _ _ _ s₁ _ rest₁ _ σmid φmid _ _ hs1 hrest1 =>
          obtain ⟨hsc_s, hsc_r⟩ := (hsc : WScopedStmt (V₁.map Prod.fst) s₁ ∧
            WScopedStmts (declVars s₁ ++ V₁.map Prod.fst) rest₁)
          obtain ⟨hfsc_s, hfsc_r⟩ := (hfsc : FScopedStmt _ s₁ ∧ FScopedStmts _ rest₁)
          obtain ⟨hns_s, hns_r⟩ := (hns : NormalForm.ScopedStmt _ _ s₁ ∧
            NormalForm.ScopedStmts (V₁.map Prod.fst ++ NormalForm.declTopVars s₁) _ rest₁)
          obtain ⟨r₁, hstep_s, hreq_s, -⟩ := ihs rfl hcfg hφ hfuns (by exact hsc_s) (by exact hfsc_s) (by exact hns_s)
            (.stmt hs1)
          obtain ⟨V1₁, hr₁eq, hV1⟩ := renRes_sres_inv hreq_s
          subst hr₁eq
          have hpe := hs1.phi_eq; subst hpe
          have hk1 : V1₁.map Prod.fst = V₁.map Prod.fst :=
            venvKeys_stmt_abnormal hstep_s hne
          have hagree : renVEnv σ' V1₁ = renVEnv σmid V1₁ := by
            refine renVEnv_congr (fun p hp => ?_)
            have hpk : p.1 ∈ V₁.map Prod.fst := by
              rw [← hk1]; exact List.mem_map_of_mem hp
            exact alphaSeq_agrees hrest1 p.1
              (wscoped_declVars_disjoint hsc_r p.1 (List.mem_append.mpr (Or.inr hpk)))
          refine ⟨_, Step.seqStop hstep_s hne, ?_, ?_⟩
          · show _ = Res.sres (renVEnv σ' V1₁) st1 o
            rw [hagree, ← hV1]
          · cases o with
            | normal => exact absurd rfl hne
            | «break» => trivial
            | «continue» => trivial
            | leave => trivial
            | halt => trivial
  | @block funs V st body₂ Vb₂ stb o hb ihb =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | stmt hs =>
      have hle : lo ≤ hi := alphaStmt1_le hs
      cases hs with | @blockD _ _ _ _ body₁ _ σend φend hbe =>
      cases hbe with | @mk _ m _ _ _ _ _ _ _ hnd hlen hNF hrn hseq =>
      have hws_body : WScopedStmts (V₁.map Prod.fst) body₁ := hsc
      obtain ⟨hdisj, hfs2⟩ := (hfsc : (∀ fn ∈ funNames body₁, fn ∉ funNamesOf funs₁) ∧
        FScopedStmts (funNames body₁ ++ funNamesOf funs₁) body₁)
      have hns_body : NormalForm.ScopedStmts (V₁.map Prod.fst)
          (funNamesOf funs₁ ++ NormalForm.funDefNames body₁) body₁ := hns
      have hkeys' : funNamesOf (hoist D body₁ :: funs₁)
          = funNames body₁ ++ funNamesOf funs₁ := by
        rw [funNamesOf_cons, hoist_keys]
      have hagOld : ∀ fn ∈ funNamesOf funs₁,
          updRen φ ((funNames body₁).zip (funNames body₂)) fn = φ fn :=
        fun fn hfn => updRen_of_not_mem
          (fun p hp hpfn => hdisj p.1 (List.of_mem_zip hp).1 (hpfn ▸ hfn))
      have hns_body' : NormalForm.ScopedStmts (V₁.map Prod.fst)
          (funNames body₁ ++ funNamesOf funs₁) body₁ := by
        refine scopedStmts_mono (fun x hx => hx) (fun x hx => ?_) hns_body
        rw [funNames_eq_funDefNames]
        rcases List.mem_append.mp hx with h2 | h2
        · exact List.mem_append.mpr (Or.inr h2)
        · exact List.mem_append.mpr (Or.inl h2)
      have hφ' : RenFCfg (updRen φ ((funNames body₁).zip (funNames body₂)))
          (hoist D body₁ :: funs₁) m :=
        RenFCfg.extend hφ hnd hlen hNF hrn hdisj (hoist_keys body₁)
      have hfuns' : RenFunsRelF (updRen φ ((funNames body₁).zip (funNames body₂)))
          (hoist D body₁ :: funs₁) (hoist D body₂ :: funs) := by
        refine RenFunsRelF.cons ?_ (hfuns.congr_phi hagOld)
        rw [hkeys']
        refine hoist_renScopeRel hseq (Nat.le_refl m) ?_ hws_body hfs2 hns_body'
        intro a ha
        have ha' : a ∈ funNamesOf (hoist D body₁ :: funs₁) := by rw [hkeys']; exact ha
        exact ⟨hφ'.2.2.1 a ha', hφ'.2.2.2 a ha'⟩
      obtain ⟨r₁, hstep_b, hreq_b, -⟩ := ihb rfl (hcfg.mono hrn.2.2) hφ' hfuns'
        (by exact hws_body)
        (by
          show FScopedStmts (funNamesOf (hoist D body₁ :: funs₁)) body₁
          rw [hkeys']
          exact hfs2)
        (by
          show NormalForm.ScopedStmts (V₁.map Prod.fst)
            (funNamesOf (hoist D body₁ :: funs₁)) body₁
          rw [hkeys']
          exact hns_body')
        (.stmts hseq)
      obtain ⟨Vb₁, hr₁eq, hVb⟩ := renRes_sres_inv hreq_b
      subst hr₁eq
      have hrk : (restore V₁ Vb₁).map Prod.fst = V₁.map Prod.fst :=
        restore_keys (venvKeys_suffix hstep_b rfl) (venvLen_mono hstep_b rfl)
      have hres : restore (renVEnv σ V₁) (renVEnv σend Vb₁)
          = renVEnv σ (restore V₁ Vb₁) := by
        have h1 : restore (renVEnv σ V₁) (renVEnv σend Vb₁)
            = renVEnv σend (restore V₁ Vb₁) := by
          rw [renVEnv_restore]
          simp only [restore, renVEnv_length]
        rw [h1]
        refine renVEnv_congr (fun p hp => ?_)
        have hpk : p.1 ∈ V₁.map Prod.fst := by
          rw [← hrk]; exact List.mem_map_of_mem hp
        exact alphaSeq_agrees hseq p.1 (wscoped_declVars_disjoint hws_body p.1 hpk)
      refine ⟨_, Step.block hstep_b, ?_, ?_⟩
      · show _ = Res.sres (renVEnv σ (restore V₁ Vb₁)) stb o
        rw [hVb, hres]
      · cases o with
        | normal => exact (RenCfg.of_keys hrk hcfg).mono hle
        | «break» => trivial
        | «continue» => trivial
        | leave => trivial
        | halt => trivial
  | @ifTrue funs V st c₂ body₂ cv st1 V'₂ st2 o hc hnz hbody ihc ihbody =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | stmt hs =>
      cases hs with | condD hc2 hb2 =>
      obtain ⟨hnsc, hnsb⟩ := (hns : NormalForm.ScopedExpr _ _ _ ∧
        NormalForm.ScopedStmts _ (_ ++ NormalForm.funDefNames _) _)
      obtain ⟨rc, hstep_c, hreq_c, -⟩ := ihc rfl hcfg hφ hfuns (by trivial) (by trivial) (by exact hnsc)
        (.expr (lo := lo) (hi := hi) hc2)
      have hr := renRes_eres_inv hreq_c
      subst hr
      obtain ⟨rb, hstep_b, hreq_b, hresb⟩ := ihbody rfl hcfg hφ hfuns
        (by exact hsc) (by exact hfsc) (by exact hnsb)
        (.stmt (.blockD hb2))
      obtain ⟨V'₁, hr₁eq, hV'⟩ := renRes_sres_inv hreq_b
      subst hr₁eq
      refine ⟨_, Step.ifTrue hstep_c hnz hstep_b, ?_, hresb⟩
      show _ = Res.sres (renVEnv σ V'₁) st2 o
      rw [← hV']
  | @switchExec funs V st c₂ cases₂ dflt₂ cv st1 V'₂ st2 o hc hbody ihc ihbody =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | stmt hs =>
      cases hs with | switchD hc2 hcs2 hd2 =>
      obtain ⟨hnsc, hnscs, hnsd⟩ := (hns : NormalForm.ScopedExpr _ _ _ ∧
        NormalForm.ScopedCases _ _ _ ∧ NormalForm.ScopedDflt _ _ _)
      obtain ⟨hwscs, hwsd⟩ := (hsc : WScopedCases (V₁.map Prod.fst) _ ∧
        WScopedDflt (V₁.map Prod.fst) _)
      obtain ⟨hfscs, hfsd⟩ := (hfsc : FScopedCases (funNamesOf funs₁) _ ∧
        FScopedDflt (funNamesOf funs₁) _)
      obtain ⟨rc, hstep_c, hreq_c, -⟩ := ihc rfl hcfg hφ hfuns (by trivial) (by trivial) (by exact hnsc)
        (.expr (lo := lo) (hi := hi) hc2)
      have hr := renRes_eres_inv hreq_c
      subst hr
      obtain ⟨lo', hi', σb, φb, hlo', hhi', hsel⟩ := selectSwitch_alpha (cv := cv) hcs2 hd2
      obtain ⟨rb, hstep_b, hreq_b, hresb⟩ := ihbody rfl (hcfg.mono hlo') (hφ.mono hlo')
        hfuns (by exact selectSwitch_wscoped hwscs hwsd)
        (by exact selectSwitch_fscoped hfscs hfsd)
        (by exact selectSwitch_nscoped hnscs hnsd) (.stmt (.blockD hsel))
      obtain ⟨V'₁, hr₁eq, hV'⟩ := renRes_sres_inv hreq_b
      subst hr₁eq
      refine ⟨_, Step.switchExec hstep_c hstep_b, ?_, ?_⟩
      · show _ = Res.sres (renVEnv σ V'₁) st2 o
        rw [← hV']
      · cases o with
        | normal => exact (hresb : RenCfg σ V'₁ hi').mono hhi'
        | «break» => trivial
        | «continue» => trivial
        | leave => trivial
        | halt => trivial
  | @loopStep funs V st c₂ post₂ body₂ cv st1 Vb₂ stb ob Vp₂ stp Vend₂ stend o hc hnz hbody hob hpost hloop ihc ihbody ihpost ihloop =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | loop hc2 hb2 hp2 =>
      obtain ⟨hnsc, hnsp, hnsb⟩ := (hns : NormalForm.ScopedExpr _ _ _ ∧
        NormalForm.ScopedStmts _ (_ ++ NormalForm.funDefNames _) _ ∧
        NormalForm.ScopedStmts _ (_ ++ NormalForm.funDefNames _) _)
      obtain ⟨hscb, hscp⟩ := (hsc : WScopedStmts (V₁.map Prod.fst) _ ∧
        WScopedStmts (V₁.map Prod.fst) _)
      obtain ⟨hfscb, hfscp⟩ := (hfsc : _ ∧ _)
      obtain ⟨rc, hstep_c, hreq_c, -⟩ := ihc rfl hcfg hφ hfuns (by trivial) (by trivial) (by exact hnsc)
        (.expr (lo := lo) (hi := hi) hc2)
      have hr := renRes_eres_inv hreq_c
      subst hr
      obtain ⟨rb, hstep_b, hreq_b, -⟩ := ihbody rfl hcfg hφ hfuns (by exact hscb)
        (by exact hfscb) (by exact hnsb)
        (.stmt (.blockD hb2))
      obtain ⟨Vb₁, hrbeq, hVb⟩ := renRes_sres_inv hreq_b
      subst hrbeq
      have hkb : Vb₁.map Prod.fst = V₁.map Prod.fst := block_keys hstep_b
      have hleb := alphaBlockExt_le hb2
      obtain ⟨rp, hstep_p, hreq_p, -⟩ := ihpost hVb ((RenCfg.of_keys hkb hcfg).mono hleb)
        (hφ.mono hleb) hfuns (by rw [hkb]; exact hscp) (by exact hfscp)
        (by rw [hkb]; exact hnsp)
        (.stmt (.blockD hp2))
      obtain ⟨Vp₁, hrpeq, hVp⟩ := renRes_sres_inv hreq_p
      subst hrpeq
      have hkp : Vp₁.map Prod.fst = V₁.map Prod.fst := (block_keys hstep_p).trans hkb
      obtain ⟨re, hstep_l, hreq_l, hres⟩ := ihloop hVp (RenCfg.of_keys hkp hcfg) hφ hfuns
        (by rw [hkp]; exact ⟨hscb, hscp⟩) (by exact ⟨hfscb, hfscp⟩)
        (by rw [hkp]; exact ⟨hnsc, hnsp, hnsb⟩)
        (.loop hc2 hb2 hp2)
      obtain ⟨Vend₁, hreeq, hVend⟩ := renRes_sres_inv hreq_l
      subst hreeq
      refine ⟨_, Step.loopStep hstep_c hnz hstep_b hob hstep_p hstep_l, ?_, hres⟩
      show _ = Res.sres (renVEnv σ Vend₁) stend o
      rw [← hVend]
  | @loopPostHalt funs V st c₂ post₂ body₂ cv st1 Vb₂ stb ob Vp₂ stp hc hnz hbody hob hpost ihc ihbody ihpost =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | loop hc2 hb2 hp2 =>
      obtain ⟨hnsc, hnsp, hnsb⟩ := (hns : NormalForm.ScopedExpr _ _ _ ∧
        NormalForm.ScopedStmts _ (_ ++ NormalForm.funDefNames _) _ ∧
        NormalForm.ScopedStmts _ (_ ++ NormalForm.funDefNames _) _)
      obtain ⟨hscb, hscp⟩ := (hsc : WScopedStmts (V₁.map Prod.fst) _ ∧
        WScopedStmts (V₁.map Prod.fst) _)
      obtain ⟨hfscb, hfscp⟩ := (hfsc : _ ∧ _)
      obtain ⟨rc, hstep_c, hreq_c, -⟩ := ihc rfl hcfg hφ hfuns (by trivial) (by trivial) (by exact hnsc)
        (.expr (lo := lo) (hi := hi) hc2)
      have hr := renRes_eres_inv hreq_c
      subst hr
      obtain ⟨rb, hstep_b, hreq_b, -⟩ := ihbody rfl hcfg hφ hfuns (by exact hscb)
        (by exact hfscb) (by exact hnsb)
        (.stmt (.blockD hb2))
      obtain ⟨Vb₁, hrbeq, hVb⟩ := renRes_sres_inv hreq_b
      subst hrbeq
      have hkb : Vb₁.map Prod.fst = V₁.map Prod.fst := block_keys hstep_b
      have hleb := alphaBlockExt_le hb2
      obtain ⟨rp, hstep_p, hreq_p, -⟩ := ihpost hVb ((RenCfg.of_keys hkb hcfg).mono hleb)
        (hφ.mono hleb) hfuns (by rw [hkb]; exact hscp) (by exact hfscp)
        (by rw [hkb]; exact hnsp)
        (.stmt (.blockD hp2))
      obtain ⟨Vp₁, hrpeq, hVp⟩ := renRes_sres_inv hreq_p
      subst hrpeq
      refine ⟨_, Step.loopPostHalt hstep_c hnz hstep_b hob hstep_p, ?_, trivial⟩
      show _ = Res.sres (renVEnv σ Vp₁) stp .halt
      rw [← hVp]
  | @loopBreak funs V st c₂ post₂ body₂ cv st1 Vb₂ stb hc hnz hbody ihc ihbody =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | loop hc2 hb2 hp2 =>
      obtain ⟨hnsc, hnsp, hnsb⟩ := (hns : NormalForm.ScopedExpr _ _ _ ∧
        NormalForm.ScopedStmts _ (_ ++ NormalForm.funDefNames _) _ ∧
        NormalForm.ScopedStmts _ (_ ++ NormalForm.funDefNames _) _)
      obtain ⟨hscb, hscp⟩ := (hsc : WScopedStmts (V₁.map Prod.fst) _ ∧
        WScopedStmts (V₁.map Prod.fst) _)
      obtain ⟨hfscb, hfscp⟩ := (hfsc : _ ∧ _)
      obtain ⟨rc, hstep_c, hreq_c, -⟩ := ihc rfl hcfg hφ hfuns (by trivial) (by trivial) (by exact hnsc)
        (.expr (lo := lo) (hi := hi) hc2)
      have hr := renRes_eres_inv hreq_c
      subst hr
      obtain ⟨rb, hstep_b, hreq_b, -⟩ := ihbody rfl hcfg hφ hfuns (by exact hscb)
        (by exact hfscb) (by exact hnsb)
        (.stmt (.blockD hb2))
      obtain ⟨Vb₁, hrbeq, hVb⟩ := renRes_sres_inv hreq_b
      subst hrbeq
      refine ⟨_, Step.loopBreak hstep_c hnz hstep_b, ?_, ?_⟩
      · show _ = Res.sres (renVEnv σ Vb₁) stb .normal
        rw [← hVb]
      · exact (RenCfg.of_keys (block_keys hstep_b) hcfg).mono
          (Nat.le_trans (alphaBlockExt_le hb2) (alphaBlockExt_le hp2))
  | @loopLeave funs V st c₂ post₂ body₂ cv st1 Vb₂ stb hc hnz hbody ihc ihbody =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | loop hc2 hb2 hp2 =>
      obtain ⟨hnsc, hnsp, hnsb⟩ := (hns : NormalForm.ScopedExpr _ _ _ ∧
        NormalForm.ScopedStmts _ (_ ++ NormalForm.funDefNames _) _ ∧
        NormalForm.ScopedStmts _ (_ ++ NormalForm.funDefNames _) _)
      obtain ⟨hscb, hscp⟩ := (hsc : WScopedStmts (V₁.map Prod.fst) _ ∧
        WScopedStmts (V₁.map Prod.fst) _)
      obtain ⟨hfscb, hfscp⟩ := (hfsc : _ ∧ _)
      obtain ⟨rc, hstep_c, hreq_c, -⟩ := ihc rfl hcfg hφ hfuns (by trivial) (by trivial) (by exact hnsc)
        (.expr (lo := lo) (hi := hi) hc2)
      have hr := renRes_eres_inv hreq_c
      subst hr
      obtain ⟨rb, hstep_b, hreq_b, -⟩ := ihbody rfl hcfg hφ hfuns (by exact hscb)
        (by exact hfscb) (by exact hnsb)
        (.stmt (.blockD hb2))
      obtain ⟨Vb₁, hrbeq, hVb⟩ := renRes_sres_inv hreq_b
      subst hrbeq
      refine ⟨_, Step.loopLeave hstep_c hnz hstep_b, ?_, trivial⟩
      show _ = Res.sres (renVEnv σ Vb₁) stb .leave
      rw [← hVb]
  | @loopBodyHalt funs V st c₂ post₂ body₂ cv st1 Vb₂ stb hc hnz hbody ihc ihbody =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | loop hc2 hb2 hp2 =>
      obtain ⟨hnsc, hnsp, hnsb⟩ := (hns : NormalForm.ScopedExpr _ _ _ ∧
        NormalForm.ScopedStmts _ (_ ++ NormalForm.funDefNames _) _ ∧
        NormalForm.ScopedStmts _ (_ ++ NormalForm.funDefNames _) _)
      obtain ⟨hscb, hscp⟩ := (hsc : WScopedStmts (V₁.map Prod.fst) _ ∧
        WScopedStmts (V₁.map Prod.fst) _)
      obtain ⟨hfscb, hfscp⟩ := (hfsc : _ ∧ _)
      obtain ⟨rc, hstep_c, hreq_c, -⟩ := ihc rfl hcfg hφ hfuns (by trivial) (by trivial) (by exact hnsc)
        (.expr (lo := lo) (hi := hi) hc2)
      have hr := renRes_eres_inv hreq_c
      subst hr
      obtain ⟨rb, hstep_b, hreq_b, -⟩ := ihbody rfl hcfg hφ hfuns (by exact hscb)
        (by exact hfscb) (by exact hnsb)
        (.stmt (.blockD hb2))
      obtain ⟨Vb₁, hrbeq, hVb⟩ := renRes_sres_inv hreq_b
      subst hrbeq
      refine ⟨_, Step.loopBodyHalt hstep_c hnz hstep_b, ?_, trivial⟩
      show _ = Res.sres (renVEnv σ Vb₁) stb .halt
      rw [← hVb]
  | @forLoop funs V st init₂ c₂ post₂ body₂ Vinit₂ stinit Vend₂ stend o hinit hloop ihinit ihloop =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | stmt hs =>
      have hle : lo ≤ hi := alphaStmt1_le hs
      cases hs with
      | @forD _ m₁ m₂ _ _ _ init₁ _ c₁ _ post₁ _ body₁ _ σi φi _ _ _ _ hInit hc2 hb2 hp2 =>
      have hphiI := hInit.phi_out
      cases hInit with | @mk _ mI _ _ _ _ _ _ _ hndI hlenI hNFI hrnI hseqI =>
      obtain ⟨hscI, hscB, hscP⟩ := (hsc : WScopedStmts (V₁.map Prod.fst) init₁ ∧
        WScopedStmts (declVarsSeq init₁ ++ V₁.map Prod.fst) body₁ ∧
        WScopedStmts (declVarsSeq init₁ ++ V₁.map Prod.fst) post₁)
      obtain ⟨hdisjI, hfsI, hfsB, hfsP⟩ := (hfsc :
        (∀ fn ∈ funNames init₁, fn ∉ funNamesOf funs₁) ∧
        FScopedStmts (funNames init₁ ++ funNamesOf funs₁) init₁ ∧
        ((∀ fn ∈ funNames body₁, fn ∉ funNames init₁ ++ funNamesOf funs₁) ∧
          FScopedStmts (funNames body₁ ++ funNames init₁ ++ funNamesOf funs₁) body₁) ∧
        ((∀ fn ∈ funNames post₁, fn ∉ funNames init₁ ++ funNamesOf funs₁) ∧
          FScopedStmts (funNames post₁ ++ funNames init₁ ++ funNamesOf funs₁) post₁))
      obtain ⟨hnsI, hnsC, hnsP, hnsB⟩ := (hns :
        NormalForm.ScopedStmts (V₁.map Prod.fst)
          (funNamesOf funs₁ ++ NormalForm.funDefNames init₁) init₁ ∧
        NormalForm.ScopedExpr (V₁.map Prod.fst ++ NormalForm.declTopVarsL init₁)
          (funNamesOf funs₁ ++ NormalForm.funDefNames init₁) c₁ ∧
        NormalForm.ScopedStmts (V₁.map Prod.fst ++ NormalForm.declTopVarsL init₁)
          ((funNamesOf funs₁ ++ NormalForm.funDefNames init₁) ++
            NormalForm.funDefNames post₁) post₁ ∧
        NormalForm.ScopedStmts (V₁.map Prod.fst ++ NormalForm.declTopVarsL init₁)
          ((funNamesOf funs₁ ++ NormalForm.funDefNames init₁) ++
            NormalForm.funDefNames body₁) body₁)
      have hkeys' : funNamesOf (hoist D init₁ :: funs₁)
          = funNames init₁ ++ funNamesOf funs₁ := by
        rw [funNamesOf_cons, hoist_keys]
      have hagOld : ∀ fn ∈ funNamesOf funs₁,
          updRen φ ((funNames init₁).zip (funNames init₂)) fn = φ fn :=
        fun fn hfn => updRen_of_not_mem
          (fun p hp hpfn => hdisjI p.1 (List.of_mem_zip hp).1 (hpfn ▸ hfn))
      have hnsI' : NormalForm.ScopedStmts (V₁.map Prod.fst)
          (funNames init₁ ++ funNamesOf funs₁) init₁ := by
        refine scopedStmts_mono (fun x hx => hx) (fun x hx => ?_) hnsI
        rw [funNames_eq_funDefNames]
        rcases List.mem_append.mp hx with h2 | h2
        · exact List.mem_append.mpr (Or.inr h2)
        · exact List.mem_append.mpr (Or.inl h2)
      have hφI : RenFCfg (updRen φ ((funNames init₁).zip (funNames init₂)))
          (hoist D init₁ :: funs₁) mI :=
        RenFCfg.extend hφ hndI hlenI hNFI hrnI hdisjI (hoist_keys init₁)
      have hfunsI : RenFunsRelF (updRen φ ((funNames init₁).zip (funNames init₂)))
          (hoist D init₁ :: funs₁) (hoist D init₂ :: funs) := by
        refine RenFunsRelF.cons ?_ (hfuns.congr_phi hagOld)
        rw [hkeys']
        refine hoist_renScopeRel hseqI (Nat.le_refl mI) ?_ hscI hfsI hnsI'
        intro a ha
        have ha' : a ∈ funNamesOf (hoist D init₁ :: funs₁) := by rw [hkeys']; exact ha
        exact ⟨hφI.2.2.1 a ha', hφI.2.2.2 a ha'⟩
      obtain ⟨ri, hstep_init, hreq_i, hcfgInit⟩ := ihinit rfl (hcfg.mono hrnI.2.2) hφI
        hfunsI (by exact hscI)
        (by
          show FScopedStmts (funNamesOf (hoist D init₁ :: funs₁)) init₁
          rw [hkeys']
          exact hfsI)
        (by
          show NormalForm.ScopedStmts (V₁.map Prod.fst)
            (funNamesOf (hoist D init₁ :: funs₁)) init₁
          rw [hkeys']
          exact hnsI')
        (.stmts hseqI)
      obtain ⟨Vinit₁, hrieq, hVinit⟩ := renRes_sres_inv hreq_i
      subst hrieq
      have hVinitKeys := venvKeys_stmts hstep_init
      have hdomI : ∀ x ∈ Vinit₁.map Prod.fst, x ∈ declVarsSeq init₁ ++ V₁.map Prod.fst := by
        intro x hx
        rcases (hVinitKeys x).mp hx with h2 | h2
        · exact List.mem_append.mpr (Or.inl h2)
        · exact List.mem_append.mpr (Or.inr h2)
      have hdomI' : ∀ x ∈ V₁.map Prod.fst ++ NormalForm.declTopVarsL init₁,
          x ∈ Vinit₁.map Prod.fst := by
        intro x hx
        refine (hVinitKeys x).mpr ?_
        rw [(declVarsSeq_eq_declTopVarsL init₁).symm] at hx
        rcases List.mem_append.mp hx with h2 | h2
        · exact Or.inr h2
        · exact Or.inl h2
      have hfnI' : ∀ x ∈ funNamesOf funs₁ ++ NormalForm.funDefNames init₁,
          x ∈ funNamesOf (hoist D init₁ :: funs₁) := by
        intro x hx
        rw [hkeys', ← funNames_eq_funDefNames] at *
        rcases List.mem_append.mp hx with h2 | h2
        · exact List.mem_append.mpr (Or.inr h2)
        · exact List.mem_append.mpr (Or.inl h2)
      have hmIle : mI ≤ m₁ := alphaSeqExt_le hseqI
      have hphiEq : φi = updRen φ ((funNames init₁).zip (funNames init₂)) := hphiI
      obtain ⟨re, hstep_loop, hreq_l, hres⟩ := ihloop hVinit hcfgInit
        (by rw [hphiEq]; exact hφI.mono hmIle)
        (by rw [hphiEq]; exact hfunsI)
        (by exact ⟨wscopedStmts_anti hdomI hscB, wscopedStmts_anti hdomI hscP⟩)
        (by
          show ((∀ fn ∈ funNames body₁, fn ∉ funNamesOf (hoist D init₁ :: funs₁)) ∧
              FScopedStmts (funNames body₁ ++ funNamesOf (hoist D init₁ :: funs₁)) body₁) ∧
            ((∀ fn ∈ funNames post₁, fn ∉ funNamesOf (hoist D init₁ :: funs₁)) ∧
              FScopedStmts (funNames post₁ ++ funNamesOf (hoist D init₁ :: funs₁)) post₁)
          rw [hkeys']
          exact ⟨⟨hfsB.1, by rw [← List.append_assoc]; exact hfsB.2⟩,
            ⟨hfsP.1, by rw [← List.append_assoc]; exact hfsP.2⟩⟩)
        (by exact ⟨scopedExpr_mono hdomI' hfnI' hnsC,
          scopedStmts_mono hdomI' (mem_append_mono hfnI' (fun x hx => hx)) hnsP,
          scopedStmts_mono hdomI' (mem_append_mono hfnI' (fun x hx => hx)) hnsB⟩)
        (.loop hc2 hb2 hp2)
      obtain ⟨Vend₁, hreeq, hVend⟩ := renRes_sres_inv hreq_l
      subst hreeq
      have hrk : (restore V₁ Vend₁).map Prod.fst = V₁.map Prod.fst :=
        restore_keys ((venvKeys_suffix hstep_init rfl).trans (venvKeys_suffix hstep_loop rfl))
          (Nat.le_trans (venvLen_mono hstep_init rfl) (venvLen_mono hstep_loop rfl))
      have hres_env : restore (renVEnv σ V₁) (renVEnv σi Vend₁)
          = renVEnv σ (restore V₁ Vend₁) := by
        have h1 : restore (renVEnv σ V₁) (renVEnv σi Vend₁)
            = renVEnv σi (restore V₁ Vend₁) := by
          rw [renVEnv_restore]
          simp only [restore, renVEnv_length]
        rw [h1]
        refine renVEnv_congr (fun p hp => ?_)
        have hpk : p.1 ∈ V₁.map Prod.fst := by
          rw [← hrk]; exact List.mem_map_of_mem hp
        exact alphaSeq_agrees hseqI p.1 (wscoped_declVars_disjoint hscI p.1 hpk)
      refine ⟨_, Step.forLoop hstep_init hstep_loop, ?_, ?_⟩
      · show _ = Res.sres (renVEnv σ (restore V₁ Vend₁)) stend o
        rw [hVend, hres_env]
      · cases o with
        | normal => exact (RenCfg.of_keys hrk hcfg).mono hle
        | «break» => trivial
        | «continue» => trivial
        | leave => trivial
        | halt => trivial
  | @forInitHalt funs V st init₂ c₂ post₂ body₂ Vinit₂ stinit hinit ihinit =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | stmt hs =>
      cases hs with
      | @forD _ m₁ m₂ _ _ _ init₁ _ c₁ _ post₁ _ body₁ _ σi φi _ _ _ _ hInit hc2 hb2 hp2 =>
      cases hInit with | @mk _ mI _ _ _ _ _ _ _ hndI hlenI hNFI hrnI hseqI =>
      obtain ⟨hscI, hscB, hscP⟩ := (hsc : WScopedStmts (V₁.map Prod.fst) init₁ ∧
        WScopedStmts (declVarsSeq init₁ ++ V₁.map Prod.fst) body₁ ∧
        WScopedStmts (declVarsSeq init₁ ++ V₁.map Prod.fst) post₁)
      obtain ⟨hdisjI, hfsI, hfsB, hfsP⟩ := (hfsc :
        (∀ fn ∈ funNames init₁, fn ∉ funNamesOf funs₁) ∧
        FScopedStmts (funNames init₁ ++ funNamesOf funs₁) init₁ ∧ (_ ∧ _) ∧ (_ ∧ _))
      obtain ⟨hnsI, hnsC, hnsP, hnsB⟩ := (hns :
        NormalForm.ScopedStmts (V₁.map Prod.fst)
          (funNamesOf funs₁ ++ NormalForm.funDefNames init₁) init₁ ∧ _ ∧ _ ∧ _)
      have hkeys' : funNamesOf (hoist D init₁ :: funs₁)
          = funNames init₁ ++ funNamesOf funs₁ := by
        rw [funNamesOf_cons, hoist_keys]
      have hagOld : ∀ fn ∈ funNamesOf funs₁,
          updRen φ ((funNames init₁).zip (funNames init₂)) fn = φ fn :=
        fun fn hfn => updRen_of_not_mem
          (fun p hp hpfn => hdisjI p.1 (List.of_mem_zip hp).1 (hpfn ▸ hfn))
      have hnsI' : NormalForm.ScopedStmts (V₁.map Prod.fst)
          (funNames init₁ ++ funNamesOf funs₁) init₁ := by
        refine scopedStmts_mono (fun x hx => hx) (fun x hx => ?_) hnsI
        rw [funNames_eq_funDefNames]
        rcases List.mem_append.mp hx with h2 | h2
        · exact List.mem_append.mpr (Or.inr h2)
        · exact List.mem_append.mpr (Or.inl h2)
      have hφI : RenFCfg (updRen φ ((funNames init₁).zip (funNames init₂)))
          (hoist D init₁ :: funs₁) mI :=
        RenFCfg.extend hφ hndI hlenI hNFI hrnI hdisjI (hoist_keys init₁)
      have hfunsI : RenFunsRelF (updRen φ ((funNames init₁).zip (funNames init₂)))
          (hoist D init₁ :: funs₁) (hoist D init₂ :: funs) := by
        refine RenFunsRelF.cons ?_ (hfuns.congr_phi hagOld)
        rw [hkeys']
        refine hoist_renScopeRel hseqI (Nat.le_refl mI) ?_ hscI hfsI hnsI'
        intro a ha
        have ha' : a ∈ funNamesOf (hoist D init₁ :: funs₁) := by rw [hkeys']; exact ha
        exact ⟨hφI.2.2.1 a ha', hφI.2.2.2 a ha'⟩
      obtain ⟨ri, hstep_init, hreq_i, -⟩ := ihinit rfl (hcfg.mono hrnI.2.2) hφI hfunsI (by exact hscI)
        (by
          show FScopedStmts (funNamesOf (hoist D init₁ :: funs₁)) init₁
          rw [hkeys']
          exact hfsI)
        (by
          show NormalForm.ScopedStmts (V₁.map Prod.fst)
            (funNamesOf (hoist D init₁ :: funs₁)) init₁
          rw [hkeys']
          exact hnsI')
        (.stmts hseqI)
      obtain ⟨Vinit₁, hrieq, hVinit⟩ := renRes_sres_inv hreq_i
      subst hrieq
      have hrk : (restore V₁ Vinit₁).map Prod.fst = V₁.map Prod.fst :=
        restore_keys (venvKeys_suffix hstep_init rfl) (venvLen_mono hstep_init rfl)
      have hres_env : restore (renVEnv σ V₁) (renVEnv σi Vinit₁)
          = renVEnv σ (restore V₁ Vinit₁) := by
        have h1 : restore (renVEnv σ V₁) (renVEnv σi Vinit₁)
            = renVEnv σi (restore V₁ Vinit₁) := by
          rw [renVEnv_restore]
          simp only [restore, renVEnv_length]
        rw [h1]
        refine renVEnv_congr (fun p hp => ?_)
        have hpk : p.1 ∈ V₁.map Prod.fst := by
          rw [← hrk]; exact List.mem_map_of_mem hp
        exact alphaSeq_agrees hseqI p.1 (wscoped_declVars_disjoint hscI p.1 hpk)
      refine ⟨_, Step.forInitHalt hstep_init, ?_, trivial⟩
      show _ = Res.sres (renVEnv σ (restore V₁ Vinit₁)) stinit .halt
      rw [hVinit, hres_env]
  | @callOk funs V st fn₂ args₂ argvals st1 decl₂ cenv₂ Vend₂ st2 o hargs hlook hlen hbody ho ihargs ihbody =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | expr hae =>
      cases hae with | @call fn _ args₁ hfn ha2 =>
      obtain ⟨ra, hstep_a, hreq_a, -⟩ := ihargs rfl hcfg hφ hfuns (by trivial) (by trivial)
        (by exact hns.2) (.args (lo := lo) (hi := hi) ha2)
      have hr := renRes_eres_inv hreq_a
      subst hr
      have hnm : ∀ s ∈ funs₁, ∀ p ∈ s, φ p.1 = φ fn → p.1 = fn :=
        fun s hs => hφ.no_merge_scope hfn hs
      obtain ⟨decl, cenv, hlook₁, hFD, hRc⟩ := lookupFun_renFunsRelF_rev hfuns hnm hlook
      obtain ⟨hsub, hfnmem⟩ := lookupFun_scopes_sub hlook₁
      obtain ⟨loF, hiF, σc, σc', φc', hps, hrs, hcfgF, hφd, hnsF, hwsF, hfsF, hbeF⟩ := hFD
      have hsubn : ∀ a ∈ funNamesOf cenv, a ∈ funNamesOf funs₁ := by
        intro a ha
        obtain ⟨s, hs, ha2'⟩ := List.mem_flatMap.mp ha
        exact List.mem_flatMap.mpr ⟨s, hsub s hs, ha2'⟩
      have hagF : ∀ a ∈ funNamesOf cenv,
          (fun z => if z ∈ funNamesOf cenv then φ z else z) a = φ a :=
        fun a ha => if_pos ha
      have hφF : RenFCfg (fun z => if z ∈ funNamesOf cenv then φ z else z) cenv loF := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro a ha b hb hab
          simp only [if_pos ha, if_pos hb] at hab
          exact hφ.1 a (hsubn a ha) b (hsubn b hb) hab
        · intro z hz
          exact if_neg hz
        · intro a ha
          exact (hφd a ha).1.imp (fun k hk => ⟨hk.1, by simp only [if_pos ha]; exact hk.2⟩)
        · intro a ha
          exact (hφd a ha).2
      have hbeF' := alphaBlockExt_congr_phi hbeF hnsF hagF
      have hRc' := hRc.congr_phi hagF
      have hbz : (bindZeros D (decl.params ++ decl.rets)).map Prod.fst
          = decl.params ++ decl.rets := by
        simp [bindZeros, List.map_map, Function.comp_def]
      have hlen₁ : argvals.length = decl.params.length := by
        rw [hps, List.length_map] at hlen
        exact hlen
      have hkeys₁ : ((decl.params.zip argvals) ++ bindZeros D decl.rets).map Prod.fst
          = decl.params ++ decl.rets := by
        rw [List.map_append, List.map_fst_zip (Nat.le_of_eq hlen₁.symm)]
        congr 1
        simp [bindZeros, List.map_map, Function.comp_def]
      have hcfg₁ : RenCfg σc ((decl.params.zip argvals) ++ bindZeros D decl.rets) loF :=
        RenCfg.of_keys (by rw [hkeys₁, hbz]) hcfgF
      have heq₁ : renVEnv σc ((decl.params.zip argvals) ++ bindZeros D decl.rets)
          = (decl₂.params.zip argvals) ++ bindZeros D decl₂.rets := by
        rw [renVEnv_append, renVEnv_zip, renVEnv_bindZeros, hps, hrs]
      obtain ⟨rb, hstep_b, hreq_b, -⟩ := ihbody heq₁.symm hcfg₁ hφF hRc'
        (by
          show WScopedStmts (((decl.params.zip argvals) ++
            bindZeros D decl.rets).map Prod.fst) decl.body
          rw [hkeys₁]
          exact hwsF)
        (by exact hfsF)
        (by
          show NormalForm.ScopedStmts (((decl.params.zip argvals) ++
              bindZeros D decl.rets).map Prod.fst)
            (funNamesOf cenv ++ NormalForm.funDefNames decl.body) decl.body
          rw [hkeys₁]
          exact hnsF)
        (.stmt (.blockD hbeF'))
      obtain ⟨Vend₁, hrbeq, hVend⟩ := renRes_sres_inv hreq_b
      subst hrbeq
      have hVendKeys : Vend₁.map Prod.fst
          = ((decl.params.zip argvals) ++ bindZeros D decl.rets).map Prod.fst :=
        block_keys hstep_b
      have hcfgVend : RenCfg σc Vend₁ loF := RenCfg.of_keys hVendKeys hcfg₁
      have hvals : decl₂.rets.map (fun r => (VEnv.get (renVEnv σc Vend₁) r).getD D.zero)
          = decl.rets.map (fun r => (VEnv.get Vend₁ r).getD D.zero) := by
        rw [hrs, List.map_map]
        refine List.map_congr_left (fun r hr => ?_)
        show (VEnv.get (renVEnv σc Vend₁) (σc r)).getD D.zero = _
        have hrNF : NotFresh r := by
          refine hcfgF.keys_notFresh r ?_
          rw [hbz]
          exact List.mem_append.mpr (Or.inr hr)
        rw [renVEnv_get σc Vend₁ r (hcfgVend.no_merge hrNF)]
      refine ⟨_, Step.callOk hstep_a hlook₁ hlen₁ hstep_b ho, ?_, trivial⟩
      show Res.eres (.vals (decl₂.rets.map fun r => (VEnv.get Vend₂ r).getD D.zero) st2)
        = Res.eres (.vals (decl.rets.map fun r => (VEnv.get Vend₁ r).getD D.zero) st2)
      rw [hVend, hvals]
  | @callHalt funs V st fn₂ args₂ argvals st1 decl₂ cenv₂ Vend₂ st2 hargs hlook hlen hbody ihargs ihbody =>
      intro lo hi σ φ σ' φ' funs₁ V₁ code₁ hV hcfg hφ hfuns hsc hfsc hns hcode
      subst hV
      cases hcode with | expr hae =>
      cases hae with | @call fn _ args₁ hfn ha2 =>
      obtain ⟨ra, hstep_a, hreq_a, -⟩ := ihargs rfl hcfg hφ hfuns (by trivial) (by trivial)
        (by exact hns.2) (.args (lo := lo) (hi := hi) ha2)
      have hr := renRes_eres_inv hreq_a
      subst hr
      have hnm : ∀ s ∈ funs₁, ∀ p ∈ s, φ p.1 = φ fn → p.1 = fn :=
        fun s hs => hφ.no_merge_scope hfn hs
      obtain ⟨decl, cenv, hlook₁, hFD, hRc⟩ := lookupFun_renFunsRelF_rev hfuns hnm hlook
      obtain ⟨hsub, hfnmem⟩ := lookupFun_scopes_sub hlook₁
      obtain ⟨loF, hiF, σc, σc', φc', hps, hrs, hcfgF, hφd, hnsF, hwsF, hfsF, hbeF⟩ := hFD
      have hsubn : ∀ a ∈ funNamesOf cenv, a ∈ funNamesOf funs₁ := by
        intro a ha
        obtain ⟨s, hs, ha2'⟩ := List.mem_flatMap.mp ha
        exact List.mem_flatMap.mpr ⟨s, hsub s hs, ha2'⟩
      have hagF : ∀ a ∈ funNamesOf cenv,
          (fun z => if z ∈ funNamesOf cenv then φ z else z) a = φ a :=
        fun a ha => if_pos ha
      have hφF : RenFCfg (fun z => if z ∈ funNamesOf cenv then φ z else z) cenv loF := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro a ha b hb hab
          simp only [if_pos ha, if_pos hb] at hab
          exact hφ.1 a (hsubn a ha) b (hsubn b hb) hab
        · intro z hz
          exact if_neg hz
        · intro a ha
          exact (hφd a ha).1.imp (fun k hk => ⟨hk.1, by simp only [if_pos ha]; exact hk.2⟩)
        · intro a ha
          exact (hφd a ha).2
      have hbeF' := alphaBlockExt_congr_phi hbeF hnsF hagF
      have hRc' := hRc.congr_phi hagF
      have hbz : (bindZeros D (decl.params ++ decl.rets)).map Prod.fst
          = decl.params ++ decl.rets := by
        simp [bindZeros, List.map_map, Function.comp_def]
      have hlen₁ : argvals.length = decl.params.length := by
        rw [hps, List.length_map] at hlen
        exact hlen
      have hkeys₁ : ((decl.params.zip argvals) ++ bindZeros D decl.rets).map Prod.fst
          = decl.params ++ decl.rets := by
        rw [List.map_append, List.map_fst_zip (Nat.le_of_eq hlen₁.symm)]
        congr 1
        simp [bindZeros, List.map_map, Function.comp_def]
      have hcfg₁ : RenCfg σc ((decl.params.zip argvals) ++ bindZeros D decl.rets) loF :=
        RenCfg.of_keys (by rw [hkeys₁, hbz]) hcfgF
      have heq₁ : renVEnv σc ((decl.params.zip argvals) ++ bindZeros D decl.rets)
          = (decl₂.params.zip argvals) ++ bindZeros D decl₂.rets := by
        rw [renVEnv_append, renVEnv_zip, renVEnv_bindZeros, hps, hrs]
      obtain ⟨rb, hstep_b, hreq_b, -⟩ := ihbody heq₁.symm hcfg₁ hφF hRc'
        (by
          show WScopedStmts (((decl.params.zip argvals) ++
            bindZeros D decl.rets).map Prod.fst) decl.body
          rw [hkeys₁]
          exact hwsF)
        (by exact hfsF)
        (by
          show NormalForm.ScopedStmts (((decl.params.zip argvals) ++
              bindZeros D decl.rets).map Prod.fst)
            (funNamesOf cenv ++ NormalForm.funDefNames decl.body) decl.body
          rw [hkeys₁]
          exact hnsF)
        (.stmt (.blockD hbeF'))
      obtain ⟨Vend₁, hrbeq, hVend⟩ := renRes_sres_inv hreq_b
      subst hrbeq
      exact ⟨_, Step.callHalt hstep_a hlook₁ hlen₁ hstep_b, rfl, trivial⟩

end YulEvmCompiler.Optimizer.Normalize
