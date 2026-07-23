import YulEvmCompiler.Optimizer.Implementation.Normalization.DisambiguateRen
/-!
# Semantic soundness of name disambiguation — the forward simulation

Goal: `RunEquivBlock D b (disambiguate b)` for well-formed `b` (the `GlobalPass`
obligation — whole-program equivalence from the empty environment).
Disambiguation renames only *declared* (bound) names; from the empty top-level
environment every in-scope variable is a program variable, so the target
environment is the whole-environment renaming `renVEnv σ V₁` and the target
function environment is `RenFunsRel`-related.

This file holds the forward direction: a source `Step` yields a target `Step`
with `renRes`-renamed result. The relation and environment-transport foundations
live in `DisambiguateAlpha` (syntax) and `DisambiguateRen` (environments); the
backward direction and the `Run`-level assembly build on top.
-/

namespace YulEvmCompiler.Optimizer.Normalize

open YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

theorem sim_fwd {funs₁ : FunEnv D} {V₁ mst code₁ res₁} (h : Step D funs₁ V₁ mst code₁ res₁) :
    ∀ {lo hi : Nat} {σ φ σ' φ' funs₂ code₂}, RenCfg σ V₁ lo → RenFCfg φ funs₁ lo →
      RenFunsRelF φ funs₁ funs₂ → WScopedCode (V₁.map Prod.fst) code₁ →
      FScopedCode (funNamesOf funs₁) code₁ →
      NScopedCode (V₁.map Prod.fst) (funNamesOf funs₁) code₁ →
      AlphaCode lo hi σ φ σ' φ' code₁ code₂ →
      Step D funs₂ (renVEnv σ V₁) mst code₂ (renRes σ' res₁) ∧ ResOK σ' hi res₁ := by
  induction h with
  | @lit funs V st l =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | expr hae => cases hae; exact ⟨Step.lit, trivial⟩
  | @var funs V st x v hv =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | expr hae => cases hae with | var hx =>
          exact ⟨Step.var (by rw [renVEnv_get σ V x (hcfg.no_merge hx)]; exact hv), trivial⟩
  | @builtinOk funs V st op args argvals st1 rets st2 ha hb iha =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | expr hae => cases hae with | builtin ha2 =>
          exact ⟨Step.builtinOk (iha hcfg hφ hfuns trivial trivial hns (.args (lo := lo) (hi := hi) ha2)).1 hb, trivial⟩
  | @builtinHalt funs V st op args argvals st1 st2 ha hb iha =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | expr hae => cases hae with | builtin ha2 =>
          exact ⟨Step.builtinHalt (iha hcfg hφ hfuns trivial trivial hns (.args (lo := lo) (hi := hi) ha2)).1 hb, trivial⟩
  | @builtinArgsHalt funs V st op args st1 ha iha =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | expr hae => cases hae with | builtin ha2 =>
          exact ⟨Step.builtinArgsHalt (iha hcfg hφ hfuns trivial trivial hns (.args (lo := lo) (hi := hi) ha2)).1, trivial⟩
  | @callArgsHalt funs V st fn args st1 ha iha =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | expr hae => cases hae with | call hfn ha2 =>
          exact ⟨Step.callArgsHalt (iha hcfg hφ hfuns trivial trivial
            (hns : _ ∧ _).2 (.args (lo := lo) (hi := hi) ha2)).1, trivial⟩
  | @argsNil funs V st =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | args hae => cases hae; exact ⟨Step.argsNil, trivial⟩
  | @argsCons funs V st e rest restvals st1 v st2 hrest he ihrest ihe =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | args hae => cases hae with | cons he2 hr2 =>
          exact ⟨Step.argsCons (ihrest hcfg hφ hfuns trivial trivial
              (hns : _ ∧ _).2 (.args (lo := lo) (hi := hi) hr2)).1
            (ihe hcfg hφ hfuns trivial trivial
              (hns : _ ∧ _).1 (.expr (lo := lo) (hi := hi) he2)).1, trivial⟩
  | @argsRestHalt funs V st e rest st1 hrest ihrest =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | args hae => cases hae with | cons he2 hr2 =>
          exact ⟨Step.argsRestHalt (ihrest hcfg hφ hfuns trivial trivial
            (hns : _ ∧ _).2 (.args (lo := lo) (hi := hi) hr2)).1, trivial⟩
  | @argsHeadHalt funs V st e rest restvals st1 st2 hrest he ihrest ihe =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | args hae => cases hae with | cons he2 hr2 =>
          exact ⟨Step.argsHeadHalt (ihrest hcfg hφ hfuns trivial trivial
              (hns : _ ∧ _).2 (.args (lo := lo) (hi := hi) hr2)).1
            (ihe hcfg hφ hfuns trivial trivial
              (hns : _ ∧ _).1 (.expr (lo := lo) (hi := hi) he2)).1, trivial⟩
  | @funDef funs V st n ps rs b =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | stmt hs => cases hs with | funD _ _ _ _ hrn hbe =>
          exact ⟨Step.funDef, hcfg.mono (Nat.le_trans hrn.2.2 (alphaBlockExt_le hbe))⟩
  | @«break» funs V st =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | stmt hs => cases hs with | breakD => exact ⟨Step.break, trivial⟩
  | @«continue» funs V st =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | stmt hs => cases hs with | contD => exact ⟨Step.continue, trivial⟩
  | @leave funs V st =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | stmt hs => cases hs with | leaveD => exact ⟨Step.leave, trivial⟩
  | @seqNil funs V st =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | stmts hs => cases hs with | nil hle =>
          exact ⟨Step.seqNil, hcfg.mono hle⟩
  | @exprStmt funs V st e st1 he ihe =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | stmt hs => cases hs with | exprD hle he2 =>
          exact ⟨Step.exprStmt (ihe hcfg hφ hfuns trivial trivial hns (.expr (lo := lo) (hi := hi) he2)).1, hcfg.mono hle⟩
  | @exprStmtHalt funs V st e st1 he ihe =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | stmt hs => cases hs with | exprD _ he2 =>
          exact ⟨Step.exprStmtHalt (ihe hcfg hφ hfuns trivial trivial hns (.expr (lo := lo) (hi := hi) he2)).1, trivial⟩
  | @assignVal funs V st vars e vals st1 he hlen ihe =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | stmt hs => cases hs with | assignD hle hvars he2 =>
          have hnm : ∀ x ∈ vars, ∀ k ∈ V.map Prod.fst, σ k = σ x → k = x := by
            intro x hx k hk hkeq
            obtain ⟨p, hp, hpk⟩ := List.mem_map.mp hk
            subst hpk
            exact hcfg.no_merge (hvars x hx) p hp hkeq
          refine ⟨?_, (RenCfg.setMany hcfg vars vals).mono hle⟩
          simp only [renRes]
          rw [← renVEnv_setMany_dom σ vars vals V hnm]
          exact Step.assignVal (ihe hcfg hφ hfuns trivial trivial
              (hns : _ ∧ _).2 (.expr (lo := lo) (hi := hi) he2)).1
            (by rw [List.length_map]; exact hlen)
  | @assignHalt funs V st vars e st1 he ihe =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | stmt hs => cases hs with | assignD _ hvars he2 =>
          exact ⟨Step.assignHalt (ihe hcfg hφ hfuns trivial trivial
            (hns : _ ∧ _).2 (.expr (lo := lo) (hi := hi) he2)).1, trivial⟩
  | @ifHalt funs V st c body st1 hc ihc =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | stmt hs => cases hs with | condD hc2 hb2 =>
          exact ⟨Step.ifHalt (ihc hcfg hφ hfuns trivial trivial
            (hns : _ ∧ _).1 (.expr (lo := lo) (hi := hi) hc2)).1, trivial⟩
  | @switchHalt funs V st c cs dflt st1 hc ihc =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | stmt hs => cases hs with | switchD hc2 hcs2 hd2 =>
          exact ⟨Step.switchHalt (ihc hcfg hφ hfuns trivial trivial
            (hns : _ ∧ _ ∧ _).1 (.expr (lo := lo) (hi := hi) hc2)).1, trivial⟩
  | @loopCondHalt funs V st c post body st1 hc ihc =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | loop hc2 hb2 hp2 =>
          exact ⟨Step.loopCondHalt (ihc hcfg hφ hfuns trivial trivial
            (hns : _ ∧ _ ∧ _).1 (.expr (lo := lo) (hi := hi) hc2)).1, trivial⟩
  | @loopDone funs V st c post body cv st1 hc hz ihc =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | loop hc2 hb2 hp2 =>
          exact ⟨Step.loopDone (ihc hcfg hφ hfuns trivial trivial
              (hns : _ ∧ _ ∧ _).1 (.expr (lo := lo) (hi := hi) hc2)).1 hz,
            hcfg.mono (Nat.le_trans (alphaBlockExt_le hb2) (alphaBlockExt_le hp2))⟩
  | @ifFalse funs V st c body cv st1 hc hz ihc =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | stmt hs => cases hs with | condD hc2 hb2 =>
          exact ⟨Step.ifFalse (ihc hcfg hφ hfuns trivial trivial
              (hns : _ ∧ _).1 (.expr (lo := lo) (hi := hi) hc2)).1 hz,
            hcfg.mono (alphaBlockExt_le hb2)⟩
  | @letZero funs V st vars =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | stmt hs => cases hs with
        | @letD _ _ _ _ _ vars' _ _ hvnd hlen hvNF hrn ho => cases ho with | none =>
            have hsc' : ∀ x ∈ vars, x ∉ V.map Prod.fst := hsc
            have hW : (bindZeros D vars ++ V).map Prod.fst = vars ++ V.map Prod.fst := by
              simp [bindZeros, List.map_append, List.map_map, Function.comp_def]
            have hagree : renVEnv (updRen σ (vars.zip vars')) V = renVEnv σ V :=
              renVEnv_congr (fun p hp => updRen_of_not_mem
                (fun q hq hqp => hsc' p.1 (hqp ▸ (List.of_mem_zip hq).1) (List.mem_map_of_mem hp)))
            refine ⟨?_, RenCfg.extend hcfg hvnd hlen hvNF hrn hsc' hW⟩
            simp only [renRes, renVEnv_append, renVEnv_bindZeros, map_updRen_zip hvnd hlen, hagree]
            exact Step.letZero
  | @letVal funs V st vars e vals st1 hval hlen0 ihe =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | stmt hs => cases hs with
        | @letD _ _ _ _ _ vars' _ _ hvnd hlen hvNF hrn ho => cases ho with | some he' =>
            have hsc' : ∀ x ∈ vars, x ∉ V.map Prod.fst := hsc
            have hW : (vars.zip vals ++ V).map Prod.fst = vars ++ V.map Prod.fst := by
              rw [List.map_append, List.map_fst_zip (Nat.le_of_eq hlen0.symm)]
            have hagree : renVEnv (updRen σ (vars.zip vars')) V = renVEnv σ V :=
              renVEnv_congr (fun p hp => updRen_of_not_mem
                (fun q hq hqp => hsc' p.1 (hqp ▸ (List.of_mem_zip hq).1) (List.mem_map_of_mem hp)))
            refine ⟨?_, RenCfg.extend hcfg hvnd hlen hvNF hrn hsc' hW⟩
            simp only [renRes, renVEnv_append, hagree, renVEnv_zip, map_updRen_zip hvnd hlen]
            exact Step.letVal (ihe hcfg hφ hfuns trivial trivial hns (.expr (lo := lo) (hi := hi) he')).1 (hlen0.trans hlen)
  | @letHalt funs V st vars e st1 hval ihe =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | stmt hs => cases hs with
        | @letD _ _ _ _ _ vars' _ _ hvnd hlen hvNF hrn ho => cases ho with | some he' =>
            have hsc' : ∀ x ∈ vars, x ∉ V.map Prod.fst := hsc
            have hagree : renVEnv (updRen σ (vars.zip vars')) V = renVEnv σ V :=
              renVEnv_congr (fun p hp => updRen_of_not_mem
                (fun q hq hqp => hsc' p.1 (hqp ▸ (List.of_mem_zip hq).1) (List.mem_map_of_mem hp)))
            refine ⟨?_, trivial⟩
            simp only [renRes, hagree]
            exact Step.letHalt (ihe hcfg hφ hfuns trivial trivial hns (.expr (lo := lo) (hi := hi) he')).1
  | @seqCons funs V st s rest V1 st1 V2 st2 o hs hrest ihs ihrest =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | stmts hss => cases hss with | cons hs1 hrest1 =>
          simp only [WScopedCode, WScopedStmts] at hsc
          simp only [FScopedCode, FScopedStmts] at hfsc
          obtain ⟨hsc_s, hsc_r⟩ := hsc
          obtain ⟨hfsc_s, hfsc_r⟩ := hfsc
          obtain ⟨hns_s, hns_r⟩ := (hns : NormalForm.ScopedStmt _ _ s ∧
            NormalForm.ScopedStmts (V.map Prod.fst ++ NormalForm.declTopVars s) _ rest)
          obtain ⟨hstep_s, hcfg1⟩ := ihs hcfg hφ hfuns hsc_s hfsc_s hns_s (.stmt hs1)
          have hpe := hs1.phi_eq; subst hpe
          have hk : V1.map Prod.fst = declVars s ++ V.map Prod.fst := venvKeys_stmt hs
          obtain ⟨hstep_r, hcfgr⟩ := ihrest hcfg1 (hφ.mono (alphaStmt1_le hs1)) hfuns
            (by show WScopedStmts (V1.map Prod.fst) rest; rw [hk]; exact hsc_r) hfsc_r
            (by
              show NormalForm.ScopedStmts (V1.map Prod.fst) _ rest
              rw [hk]
              refine scopedStmts_mono (fun x hx => ?_) (fun x hx => hx) hns_r
              rw [declVars_eq_declTopVars]
              rcases List.mem_append.mp hx with h | h
              · exact List.mem_append.mpr (Or.inr h)
              · exact List.mem_append.mpr (Or.inl h))
            (.stmts hrest1)
          exact ⟨Step.seqCons hstep_s hstep_r, hcfgr⟩
  | _ => intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode; sorry

end YulEvmCompiler.Optimizer.Normalize
