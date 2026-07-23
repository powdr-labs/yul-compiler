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
  | @block funs V st body Vb stb o hb ihb =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | stmt hs =>
      have hle : lo ≤ hi := alphaStmt1_le hs
      cases hs with | @blockD _ _ _ _ _ body₂ σend φend hbe =>
      cases hbe with | @mk _ m _ _ _ _ _ _ _ hnd hlen hNF hrn hseq =>
      have hws_body : WScopedStmts (V.map Prod.fst) body := hsc
      obtain ⟨hdisj, hfs2⟩ := (hfsc : (∀ fn ∈ funNames body, fn ∉ funNamesOf funs) ∧
        FScopedStmts (funNames body ++ funNamesOf funs) body)
      have hns_body : NormalForm.ScopedStmts (V.map Prod.fst)
          (funNamesOf funs ++ NormalForm.funDefNames body) body := hns
      have hkeys' : funNamesOf (hoist D body :: funs)
          = funNames body ++ funNamesOf funs := by
        rw [funNamesOf_cons, hoist_keys]
      have hagOld : ∀ fn ∈ funNamesOf funs,
          updRen φ ((funNames body).zip (funNames body₂)) fn = φ fn :=
        fun fn hfn => updRen_of_not_mem
          (fun p hp hpfn => hdisj p.1 (List.of_mem_zip hp).1 (hpfn ▸ hfn))
      have hns_body' : NormalForm.ScopedStmts (V.map Prod.fst)
          (funNames body ++ funNamesOf funs) body := by
        refine scopedStmts_mono (fun x hx => hx) (fun x hx => ?_) hns_body
        rw [funNames_eq_funDefNames]
        rcases List.mem_append.mp hx with h | h
        · exact List.mem_append.mpr (Or.inr h)
        · exact List.mem_append.mpr (Or.inl h)
      have hφ' : RenFCfg (updRen φ ((funNames body).zip (funNames body₂)))
          (hoist D body :: funs) m :=
        RenFCfg.extend hφ hnd hlen hNF hrn hdisj (hoist_keys body)
      have hfuns' : RenFunsRelF (updRen φ ((funNames body).zip (funNames body₂)))
          (hoist D body :: funs) (hoist D body₂ :: funs₂) := by
        refine RenFunsRelF.cons ?_ (hfuns.congr_phi hagOld)
        rw [hkeys']
        refine hoist_renScopeRel hseq (Nat.le_refl m) ?_ hws_body hfs2 hns_body'
        intro a ha
        have ha' : a ∈ funNamesOf (hoist D body :: funs) := by rw [hkeys']; exact ha
        exact ⟨hφ'.2.2.1 a ha', hφ'.2.2.2 a ha'⟩
      obtain ⟨hstep_b, hcfgb⟩ := ihb (hcfg.mono hrn.2.2) hφ' hfuns' hws_body
        (by
          show FScopedStmts (funNamesOf (hoist D body :: funs)) body
          rw [hkeys']
          exact hfs2)
        (by
          show NormalForm.ScopedStmts (V.map Prod.fst)
            (funNamesOf (hoist D body :: funs)) body
          rw [hkeys']
          exact hns_body')
        (.stmts hseq)
      have hrk : (restore V Vb).map Prod.fst = V.map Prod.fst :=
        restore_keys (venvKeys_suffix hb rfl) (venvLen_mono hb rfl)
      have hres : restore (renVEnv σ V) (renVEnv σend Vb) = renVEnv σ (restore V Vb) := by
        have h1 : restore (renVEnv σ V) (renVEnv σend Vb)
            = renVEnv σend (restore V Vb) := by
          rw [renVEnv_restore]
          simp only [restore, renVEnv_length]
        rw [h1]
        refine renVEnv_congr (fun p hp => ?_)
        have hpk : p.1 ∈ V.map Prod.fst := by
          rw [← hrk]; exact List.mem_map_of_mem hp
        exact alphaSeq_agrees hseq p.1 (wscoped_declVars_disjoint hws_body p.1 hpk)
      refine ⟨?_, ?_⟩
      · show Step D funs₂ (renVEnv σ V) st (.stmt (.block body₂))
          (.sres (renVEnv σ (restore V Vb)) stb o)
        rw [← hres]
        exact Step.block hstep_b
      · cases o with
        | normal => exact (RenCfg.of_keys hrk hcfg).mono hle
        | «break» => trivial
        | «continue» => trivial
        | leave => trivial
        | halt => trivial
  | @ifTrue funs V st c body cv st1 V' st2 o hc hnz hbody ihc ihbody =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | stmt hs =>
      cases hs with | condD hc2 hb2 =>
      obtain ⟨hnsc, hnsb⟩ := (hns : NormalForm.ScopedExpr _ _ c ∧
        NormalForm.ScopedStmts _ (_ ++ NormalForm.funDefNames body) body)
      obtain ⟨hstep_b, hresb⟩ := ihbody hcfg hφ hfuns
        (hsc : WScopedStmts (V.map Prod.fst) body)
        (hfsc : (∀ fn ∈ funNames body, fn ∉ funNamesOf funs) ∧
          FScopedStmts (funNames body ++ funNamesOf funs) body)
        (hnsb : NormalForm.ScopedStmt _ _ (.block body))
        (.stmt (.blockD hb2))
      exact ⟨Step.ifTrue (ihc hcfg hφ hfuns trivial trivial hnsc
        (.expr (lo := lo) (hi := hi) hc2)).1 hnz hstep_b, hresb⟩
  | @switchExec funs V st c cases dflt cv st1 V' st2 o hc hbody ihc ihbody =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | stmt hs =>
      cases hs with | @switchD _ m _ _ _ _ c₂ _ cases₂ _ dflt₂ hc2 hcs2 hd2 =>
      obtain ⟨hnsc, hnscs, hnsd⟩ := (hns : NormalForm.ScopedExpr _ _ c ∧
        NormalForm.ScopedCases _ _ cases ∧ NormalForm.ScopedDflt _ _ dflt)
      obtain ⟨hwscs, hwsd⟩ := (hsc : WScopedCases (V.map Prod.fst) cases ∧
        WScopedDflt (V.map Prod.fst) dflt)
      obtain ⟨hfscs, hfsd⟩ := (hfsc : FScopedCases (funNamesOf funs) cases ∧
        FScopedDflt (funNamesOf funs) dflt)
      obtain ⟨lo', hi', σb, φb, hlo', hhi', hsel⟩ := selectSwitch_alpha (cv := cv) hcs2 hd2
      obtain ⟨hstep_b, hresb⟩ := ihbody (hcfg.mono hlo') (hφ.mono hlo') hfuns
        (selectSwitch_wscoped hwscs hwsd)
        (selectSwitch_fscoped hfscs hfsd)
        (selectSwitch_nscoped hnscs hnsd)
        (.stmt (.blockD hsel))
      refine ⟨Step.switchExec (ihc hcfg hφ hfuns trivial trivial hnsc
        (.expr (lo := lo) (hi := hi) hc2)).1 hstep_b, ?_⟩
      cases o with
      | normal => exact (hresb : RenCfg σ V' hi').mono hhi'
      | «break» => trivial
      | «continue» => trivial
      | leave => trivial
      | halt => trivial
  | @loopStep funs V st c post body cv st1 Vb stb ob Vp stp Vend stend o hc hnz hbody hob hpost hloop ihc ihbody ihpost ihloop =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | loop hc2 hb2 hp2 =>
      obtain ⟨hnsc, hnsp, hnsb⟩ := (hns : NormalForm.ScopedExpr _ _ c ∧
        NormalForm.ScopedStmts _ (_ ++ NormalForm.funDefNames post) post ∧
        NormalForm.ScopedStmts _ (_ ++ NormalForm.funDefNames body) body)
      obtain ⟨hscb, hscp⟩ := (hsc : WScopedStmts (V.map Prod.fst) body ∧
        WScopedStmts (V.map Prod.fst) post)
      obtain ⟨hfscb, hfscp⟩ := (hfsc :
        ((∀ fn ∈ funNames body, fn ∉ funNamesOf funs) ∧
          FScopedStmts (funNames body ++ funNamesOf funs) body) ∧
        ((∀ fn ∈ funNames post, fn ∉ funNamesOf funs) ∧
          FScopedStmts (funNames post ++ funNamesOf funs) post))
      have hkb : Vb.map Prod.fst = V.map Prod.fst := block_keys hbody
      have hkp : Vp.map Prod.fst = V.map Prod.fst := (block_keys hpost).trans hkb
      have hleb := alphaBlockExt_le hb2
      obtain ⟨hstep_body, _⟩ := ihbody hcfg hφ hfuns hscb hfscb hnsb (.stmt (.blockD hb2))
      obtain ⟨hstep_post, _⟩ := ihpost ((RenCfg.of_keys hkb hcfg).mono hleb) (hφ.mono hleb)
        hfuns (by rw [hkb]; exact hscp) hfscp (by rw [hkb]; exact hnsp)
        (.stmt (.blockD hp2))
      obtain ⟨hstep_loop, hres⟩ := ihloop (RenCfg.of_keys hkp hcfg) hφ hfuns
        (by rw [hkp]; exact ⟨hscb, hscp⟩) ⟨hfscb, hfscp⟩
        (by rw [hkp]; exact ⟨hnsc, hnsp, hnsb⟩)
        (.loop hc2 hb2 hp2)
      exact ⟨Step.loopStep (ihc hcfg hφ hfuns trivial trivial hnsc
        (.expr (lo := lo) (hi := hi) hc2)).1 hnz hstep_body hob hstep_post hstep_loop, hres⟩
  | @loopPostHalt funs V st c post body cv st1 Vb stb ob Vp stp hc hnz hbody hob hpost ihc ihbody ihpost =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | loop hc2 hb2 hp2 =>
      obtain ⟨hnsc, hnsp, hnsb⟩ := (hns : NormalForm.ScopedExpr _ _ c ∧
        NormalForm.ScopedStmts _ (_ ++ NormalForm.funDefNames post) post ∧
        NormalForm.ScopedStmts _ (_ ++ NormalForm.funDefNames body) body)
      obtain ⟨hscb, hscp⟩ := (hsc : WScopedStmts (V.map Prod.fst) body ∧
        WScopedStmts (V.map Prod.fst) post)
      obtain ⟨hfscb, hfscp⟩ := (hfsc : _ ∧ _)
      have hkb : Vb.map Prod.fst = V.map Prod.fst := block_keys hbody
      have hleb : lo ≤ _ := alphaBlockExt_le hb2
      obtain ⟨hstep_body, _⟩ := ihbody hcfg hφ hfuns hscb hfscb hnsb (.stmt (.blockD hb2))
      obtain ⟨hstep_post, _⟩ := ihpost ((RenCfg.of_keys hkb hcfg).mono hleb) (hφ.mono hleb)
        hfuns (by rw [hkb]; exact hscp) hfscp (by rw [hkb]; exact hnsp)
        (.stmt (.blockD hp2))
      exact ⟨Step.loopPostHalt (ihc hcfg hφ hfuns trivial trivial hnsc
        (.expr (lo := lo) (hi := hi) hc2)).1 hnz hstep_body hob hstep_post, trivial⟩
  | @loopBreak funs V st c post body cv st1 Vb stb hc hnz hbody ihc ihbody =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | loop hc2 hb2 hp2 =>
      obtain ⟨hnsc, hnsp, hnsb⟩ := (hns : NormalForm.ScopedExpr _ _ c ∧
        NormalForm.ScopedStmts _ (_ ++ NormalForm.funDefNames post) post ∧
        NormalForm.ScopedStmts _ (_ ++ NormalForm.funDefNames body) body)
      obtain ⟨hscb, hscp⟩ := (hsc : WScopedStmts (V.map Prod.fst) body ∧
        WScopedStmts (V.map Prod.fst) post)
      obtain ⟨hfscb, hfscp⟩ := (hfsc : _ ∧ _)
      obtain ⟨hstep_body, _⟩ := ihbody hcfg hφ hfuns hscb hfscb hnsb (.stmt (.blockD hb2))
      refine ⟨Step.loopBreak (ihc hcfg hφ hfuns trivial trivial hnsc
        (.expr (lo := lo) (hi := hi) hc2)).1 hnz hstep_body, ?_⟩
      exact (RenCfg.of_keys (block_keys hbody) hcfg).mono
        (Nat.le_trans (alphaBlockExt_le hb2) (alphaBlockExt_le hp2))
  | @loopLeave funs V st c post body cv st1 Vb stb hc hnz hbody ihc ihbody =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | loop hc2 hb2 hp2 =>
      obtain ⟨hnsc, hnsp, hnsb⟩ := (hns : NormalForm.ScopedExpr _ _ c ∧
        NormalForm.ScopedStmts _ (_ ++ NormalForm.funDefNames post) post ∧
        NormalForm.ScopedStmts _ (_ ++ NormalForm.funDefNames body) body)
      obtain ⟨hscb, hscp⟩ := (hsc : WScopedStmts (V.map Prod.fst) body ∧
        WScopedStmts (V.map Prod.fst) post)
      obtain ⟨hfscb, hfscp⟩ := (hfsc : _ ∧ _)
      obtain ⟨hstep_body, _⟩ := ihbody hcfg hφ hfuns hscb hfscb hnsb (.stmt (.blockD hb2))
      exact ⟨Step.loopLeave (ihc hcfg hφ hfuns trivial trivial hnsc
        (.expr (lo := lo) (hi := hi) hc2)).1 hnz hstep_body, trivial⟩
  | @loopBodyHalt funs V st c post body cv st1 Vb stb hc hnz hbody ihc ihbody =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | loop hc2 hb2 hp2 =>
      obtain ⟨hnsc, hnsp, hnsb⟩ := (hns : NormalForm.ScopedExpr _ _ c ∧
        NormalForm.ScopedStmts _ (_ ++ NormalForm.funDefNames post) post ∧
        NormalForm.ScopedStmts _ (_ ++ NormalForm.funDefNames body) body)
      obtain ⟨hscb, hscp⟩ := (hsc : WScopedStmts (V.map Prod.fst) body ∧
        WScopedStmts (V.map Prod.fst) post)
      obtain ⟨hfscb, hfscp⟩ := (hfsc : _ ∧ _)
      obtain ⟨hstep_body, _⟩ := ihbody hcfg hφ hfuns hscb hfscb hnsb (.stmt (.blockD hb2))
      exact ⟨Step.loopBodyHalt (ihc hcfg hφ hfuns trivial trivial hnsc
        (.expr (lo := lo) (hi := hi) hc2)).1 hnz hstep_body, trivial⟩
  | @seqStop funs V st s rest V1 st1 o hs hne ihs =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | stmts hss =>
      cases hss with | @cons _ m _ _ _ _ s₂ _ rest₂ σmid _ _ _ hs1 hrest1 =>
      obtain ⟨hsc_s, hsc_r⟩ := (hsc : WScopedStmt (V.map Prod.fst) s ∧
        WScopedStmts (declVars s ++ V.map Prod.fst) rest)
      obtain ⟨hfsc_s, hfsc_r⟩ := (hfsc : FScopedStmt _ s ∧ FScopedStmts _ rest)
      obtain ⟨hns_s, hns_r⟩ := (hns : NormalForm.ScopedStmt _ _ s ∧
        NormalForm.ScopedStmts (V.map Prod.fst ++ NormalForm.declTopVars s) _ rest)
      obtain ⟨hstep_s, _⟩ := ihs hcfg hφ hfuns hsc_s hfsc_s hns_s (.stmt hs1)
      have hpe := hs1.phi_eq; subst hpe
      have hk1 : V1.map Prod.fst = V.map Prod.fst := venvKeys_stmt_abnormal hs hne
      have hagree : renVEnv σ' V1 = renVEnv σmid V1 := by
        refine renVEnv_congr (fun p hp => ?_)
        have hpk : p.1 ∈ V.map Prod.fst := by
          rw [← hk1]; exact List.mem_map_of_mem hp
        exact alphaSeq_agrees hrest1 p.1
          (wscoped_declVars_disjoint hsc_r p.1
            (List.mem_append.mpr (Or.inr hpk)))
      refine ⟨?_, ?_⟩
      · show Step D funs₂ (renVEnv σ V) st (.stmts (s₂ :: rest₂))
          (.sres (renVEnv σ' V1) st1 o)
        rw [hagree]
        exact Step.seqStop hstep_s hne
      · cases o with
        | normal => exact absurd rfl hne
        | «break» => trivial
        | «continue» => trivial
        | leave => trivial
        | halt => trivial
  | @forLoop funs V st init c post body Vinit stinit Vend stend o hinit hloop ihinit ihloop =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | stmt hs =>
      have hle : lo ≤ hi := alphaStmt1_le hs
      cases hs with
      | @forD _ m₁ m₂ _ _ _ _ init₂ _ c₂ _ post₂ _ body₂ σi φi _ _ _ _ hInit hc2 hb2 hp2 =>
      have hphiI := hInit.phi_out
      cases hInit with | @mk _ mI _ _ _ _ _ _ _ hndI hlenI hNFI hrnI hseqI =>
      obtain ⟨hscI, hscB, hscP⟩ := (hsc : WScopedStmts (V.map Prod.fst) init ∧
        WScopedStmts (declVarsSeq init ++ V.map Prod.fst) body ∧
        WScopedStmts (declVarsSeq init ++ V.map Prod.fst) post)
      obtain ⟨hdisjI, hfsI, hfsB, hfsP⟩ := (hfsc :
        (∀ fn ∈ funNames init, fn ∉ funNamesOf funs) ∧
        FScopedStmts (funNames init ++ funNamesOf funs) init ∧
        ((∀ fn ∈ funNames body, fn ∉ funNames init ++ funNamesOf funs) ∧
          FScopedStmts (funNames body ++ funNames init ++ funNamesOf funs) body) ∧
        ((∀ fn ∈ funNames post, fn ∉ funNames init ++ funNamesOf funs) ∧
          FScopedStmts (funNames post ++ funNames init ++ funNamesOf funs) post))
      obtain ⟨hnsI, hnsC, hnsP, hnsB⟩ := (hns :
        NormalForm.ScopedStmts (V.map Prod.fst)
          (funNamesOf funs ++ NormalForm.funDefNames init) init ∧
        NormalForm.ScopedExpr (V.map Prod.fst ++ NormalForm.declTopVarsL init)
          (funNamesOf funs ++ NormalForm.funDefNames init) c ∧
        NormalForm.ScopedStmts (V.map Prod.fst ++ NormalForm.declTopVarsL init)
          ((funNamesOf funs ++ NormalForm.funDefNames init) ++
            NormalForm.funDefNames post) post ∧
        NormalForm.ScopedStmts (V.map Prod.fst ++ NormalForm.declTopVarsL init)
          ((funNamesOf funs ++ NormalForm.funDefNames init) ++
            NormalForm.funDefNames body) body)
      have hkeys' : funNamesOf (hoist D init :: funs)
          = funNames init ++ funNamesOf funs := by
        rw [funNamesOf_cons, hoist_keys]
      have hagOld : ∀ fn ∈ funNamesOf funs,
          updRen φ ((funNames init).zip (funNames init₂)) fn = φ fn :=
        fun fn hfn => updRen_of_not_mem
          (fun p hp hpfn => hdisjI p.1 (List.of_mem_zip hp).1 (hpfn ▸ hfn))
      have hnsI' : NormalForm.ScopedStmts (V.map Prod.fst)
          (funNames init ++ funNamesOf funs) init := by
        refine scopedStmts_mono (fun x hx => hx) (fun x hx => ?_) hnsI
        rw [funNames_eq_funDefNames]
        rcases List.mem_append.mp hx with h | h
        · exact List.mem_append.mpr (Or.inr h)
        · exact List.mem_append.mpr (Or.inl h)
      have hφI : RenFCfg (updRen φ ((funNames init).zip (funNames init₂)))
          (hoist D init :: funs) mI :=
        RenFCfg.extend hφ hndI hlenI hNFI hrnI hdisjI (hoist_keys init)
      have hfunsI : RenFunsRelF (updRen φ ((funNames init).zip (funNames init₂)))
          (hoist D init :: funs) (hoist D init₂ :: funs₂) := by
        refine RenFunsRelF.cons ?_ (hfuns.congr_phi hagOld)
        rw [hkeys']
        refine hoist_renScopeRel hseqI (Nat.le_refl mI) ?_ hscI hfsI hnsI'
        intro a ha
        have ha' : a ∈ funNamesOf (hoist D init :: funs) := by rw [hkeys']; exact ha
        exact ⟨hφI.2.2.1 a ha', hφI.2.2.2 a ha'⟩
      obtain ⟨hstep_init, hcfgInit⟩ := ihinit (hcfg.mono hrnI.2.2) hφI hfunsI hscI
        (by
          show FScopedStmts (funNamesOf (hoist D init :: funs)) init
          rw [hkeys']
          exact hfsI)
        (by
          show NormalForm.ScopedStmts (V.map Prod.fst)
            (funNamesOf (hoist D init :: funs)) init
          rw [hkeys']
          exact hnsI')
        (.stmts hseqI)
      -- the loop configuration, at φi = the prescan-extended φ
      have hVinitKeys := venvKeys_stmts hinit
      have hdomI : ∀ x ∈ Vinit.map Prod.fst, x ∈ declVarsSeq init ++ V.map Prod.fst := by
        intro x hx
        rcases (hVinitKeys x).mp hx with h | h
        · exact List.mem_append.mpr (Or.inl h)
        · exact List.mem_append.mpr (Or.inr h)
      have hdomI' : ∀ x ∈ V.map Prod.fst ++ NormalForm.declTopVarsL init,
          x ∈ Vinit.map Prod.fst := by
        intro x hx
        refine (hVinitKeys x).mpr ?_
        rw [(declVarsSeq_eq_declTopVarsL init).symm] at hx
        rcases List.mem_append.mp hx with h | h
        · exact Or.inr h
        · exact Or.inl h
      have hfnI' : ∀ x ∈ funNamesOf funs ++ NormalForm.funDefNames init,
          x ∈ funNamesOf (hoist D init :: funs) := by
        intro x hx
        rw [hkeys', ← funNames_eq_funDefNames] at *
        rcases List.mem_append.mp hx with h | h
        · exact List.mem_append.mpr (Or.inr h)
        · exact List.mem_append.mpr (Or.inl h)
      have hmIle : mI ≤ m₁ := alphaSeqExt_le hseqI
      have hphiEq : φi = updRen φ ((funNames init).zip (funNames init₂)) := hphiI
      obtain ⟨hstep_loop, hres⟩ := ihloop hcfgInit
        (by rw [hphiEq]; exact hφI.mono hmIle)
        (by rw [hphiEq]; exact hfunsI)
        (⟨wscopedStmts_anti hdomI hscB, wscopedStmts_anti hdomI hscP⟩)
        (by
          show ((∀ fn ∈ funNames body, fn ∉ funNamesOf (hoist D init :: funs)) ∧
              FScopedStmts (funNames body ++ funNamesOf (hoist D init :: funs)) body) ∧
            ((∀ fn ∈ funNames post, fn ∉ funNamesOf (hoist D init :: funs)) ∧
              FScopedStmts (funNames post ++ funNamesOf (hoist D init :: funs)) post)
          rw [hkeys']
          exact ⟨⟨hfsB.1, by rw [← List.append_assoc]; exact hfsB.2⟩,
            ⟨hfsP.1, by rw [← List.append_assoc]; exact hfsP.2⟩⟩)
        (⟨scopedExpr_mono hdomI' hfnI' hnsC,
          scopedStmts_mono hdomI' (mem_append_mono hfnI' (fun x hx => hx)) hnsP,
          scopedStmts_mono hdomI' (mem_append_mono hfnI' (fun x hx => hx)) hnsB⟩)
        (.loop hc2 hb2 hp2)
      have hrk : (restore V Vend).map Prod.fst = V.map Prod.fst :=
        restore_keys ((venvKeys_suffix hinit rfl).trans (venvKeys_suffix hloop rfl))
          (Nat.le_trans (venvLen_mono hinit rfl) (venvLen_mono hloop rfl))
      have hres_env : restore (renVEnv σ V) (renVEnv σi Vend) = renVEnv σ (restore V Vend) := by
        have h1 : restore (renVEnv σ V) (renVEnv σi Vend)
            = renVEnv σi (restore V Vend) := by
          rw [renVEnv_restore]
          simp only [restore, renVEnv_length]
        rw [h1]
        refine renVEnv_congr (fun p hp => ?_)
        have hpk : p.1 ∈ V.map Prod.fst := by
          rw [← hrk]; exact List.mem_map_of_mem hp
        exact alphaSeq_agrees hseqI p.1 (wscoped_declVars_disjoint hscI p.1 hpk)
      refine ⟨?_, ?_⟩
      · show Step D funs₂ (renVEnv σ V) st (.stmt (.forLoop init₂ c₂ post₂ body₂))
          (.sres (renVEnv σ (restore V Vend)) stend o)
        rw [← hres_env]
        exact Step.forLoop hstep_init hstep_loop
      · cases o with
        | normal => exact (RenCfg.of_keys hrk hcfg).mono hle
        | «break» => trivial
        | «continue» => trivial
        | leave => trivial
        | halt => trivial
  | @forInitHalt funs V st init c post body Vinit stinit hinit ihinit =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | stmt hs =>
      cases hs with
      | @forD _ m₁ m₂ _ _ _ _ init₂ _ c₂ _ post₂ _ body₂ σi φi _ _ _ _ hInit hc2 hb2 hp2 =>
      cases hInit with | @mk _ mI _ _ _ _ _ _ _ hndI hlenI hNFI hrnI hseqI =>
      obtain ⟨hscI, hscB, hscP⟩ := (hsc : WScopedStmts (V.map Prod.fst) init ∧
        WScopedStmts (declVarsSeq init ++ V.map Prod.fst) body ∧
        WScopedStmts (declVarsSeq init ++ V.map Prod.fst) post)
      obtain ⟨hdisjI, hfsI, hfsB, hfsP⟩ := (hfsc :
        (∀ fn ∈ funNames init, fn ∉ funNamesOf funs) ∧
        FScopedStmts (funNames init ++ funNamesOf funs) init ∧ (_ ∧ _) ∧ (_ ∧ _))
      obtain ⟨hnsI, hnsC, hnsP, hnsB⟩ := (hns :
        NormalForm.ScopedStmts (V.map Prod.fst)
          (funNamesOf funs ++ NormalForm.funDefNames init) init ∧ _ ∧ _ ∧ _)
      have hkeys' : funNamesOf (hoist D init :: funs)
          = funNames init ++ funNamesOf funs := by
        rw [funNamesOf_cons, hoist_keys]
      have hagOld : ∀ fn ∈ funNamesOf funs,
          updRen φ ((funNames init).zip (funNames init₂)) fn = φ fn :=
        fun fn hfn => updRen_of_not_mem
          (fun p hp hpfn => hdisjI p.1 (List.of_mem_zip hp).1 (hpfn ▸ hfn))
      have hnsI' : NormalForm.ScopedStmts (V.map Prod.fst)
          (funNames init ++ funNamesOf funs) init := by
        refine scopedStmts_mono (fun x hx => hx) (fun x hx => ?_) hnsI
        rw [funNames_eq_funDefNames]
        rcases List.mem_append.mp hx with h | h
        · exact List.mem_append.mpr (Or.inr h)
        · exact List.mem_append.mpr (Or.inl h)
      have hφI : RenFCfg (updRen φ ((funNames init).zip (funNames init₂)))
          (hoist D init :: funs) mI :=
        RenFCfg.extend hφ hndI hlenI hNFI hrnI hdisjI (hoist_keys init)
      have hfunsI : RenFunsRelF (updRen φ ((funNames init).zip (funNames init₂)))
          (hoist D init :: funs) (hoist D init₂ :: funs₂) := by
        refine RenFunsRelF.cons ?_ (hfuns.congr_phi hagOld)
        rw [hkeys']
        refine hoist_renScopeRel hseqI (Nat.le_refl mI) ?_ hscI hfsI hnsI'
        intro a ha
        have ha' : a ∈ funNamesOf (hoist D init :: funs) := by rw [hkeys']; exact ha
        exact ⟨hφI.2.2.1 a ha', hφI.2.2.2 a ha'⟩
      obtain ⟨hstep_init, _⟩ := ihinit (hcfg.mono hrnI.2.2) hφI hfunsI hscI
        (by
          show FScopedStmts (funNamesOf (hoist D init :: funs)) init
          rw [hkeys']
          exact hfsI)
        (by
          show NormalForm.ScopedStmts (V.map Prod.fst)
            (funNamesOf (hoist D init :: funs)) init
          rw [hkeys']
          exact hnsI')
        (.stmts hseqI)
      have hrk : (restore V Vinit).map Prod.fst = V.map Prod.fst :=
        restore_keys (venvKeys_suffix hinit rfl) (venvLen_mono hinit rfl)
      have hres_env : restore (renVEnv σ V) (renVEnv σi Vinit)
          = renVEnv σ (restore V Vinit) := by
        have h1 : restore (renVEnv σ V) (renVEnv σi Vinit)
            = renVEnv σi (restore V Vinit) := by
          rw [renVEnv_restore]
          simp only [restore, renVEnv_length]
        rw [h1]
        refine renVEnv_congr (fun p hp => ?_)
        have hpk : p.1 ∈ V.map Prod.fst := by
          rw [← hrk]; exact List.mem_map_of_mem hp
        exact alphaSeq_agrees hseqI p.1 (wscoped_declVars_disjoint hscI p.1 hpk)
      refine ⟨?_, trivial⟩
      show Step D funs₂ (renVEnv σ V) st (.stmt (.forLoop init₂ c₂ post₂ body₂))
        (.sres (renVEnv σ (restore V Vinit)) stinit .halt)
      rw [← hres_env]
      exact Step.forInitHalt hstep_init
  | @callOk funs V st fn args argvals st1 decl cenv Vend st2 o hargs hlook hlen hbody ho ihargs ihbody =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | expr hae =>
      cases hae with | call hfn ha2 =>
      obtain ⟨hsub, hfnmem⟩ := lookupFun_scopes_sub hlook
      have hnm : ∀ s ∈ funs, ∀ p ∈ s, φ p.1 = φ fn → p.1 = fn :=
        fun s hs => hφ.no_merge_scope hfn hs
      obtain ⟨decl₂, cenv₂, hlook₂, hFD, hRc⟩ := lookupFun_renFunsRelF hfuns hnm hlook
      obtain ⟨loF, hiF, σc, σc', φc', hps, hrs, hcfgF, hφd, hnsF, hwsF, hfsF, hbeF⟩ := hFD
      have hsubn : ∀ a ∈ funNamesOf cenv, a ∈ funNamesOf funs := by
        intro a ha
        obtain ⟨s, hs, ha2⟩ := List.mem_flatMap.mp ha
        exact List.mem_flatMap.mpr ⟨s, hsub s hs, ha2⟩
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
      have hkeys₁ : ((decl.params.zip argvals) ++ bindZeros D decl.rets).map Prod.fst
          = decl.params ++ decl.rets := by
        rw [List.map_append, List.map_fst_zip (Nat.le_of_eq hlen.symm)]
        congr 1
        simp [bindZeros, List.map_map, Function.comp_def]
      have hcfg₁ : RenCfg σc ((decl.params.zip argvals) ++ bindZeros D decl.rets) loF :=
        RenCfg.of_keys (by rw [hkeys₁, hbz]) hcfgF
      obtain ⟨hstep_body, _⟩ := ihbody hcfg₁ hφF hRc'
        (by
          show WScopedStmts (((decl.params.zip argvals) ++
            bindZeros D decl.rets).map Prod.fst) decl.body
          rw [hkeys₁]
          exact hwsF)
        hfsF
        (by
          show NormalForm.ScopedStmts (((decl.params.zip argvals) ++
              bindZeros D decl.rets).map Prod.fst)
            (funNamesOf cenv ++ NormalForm.funDefNames decl.body) decl.body
          rw [hkeys₁]
          exact hnsF)
        (.stmt (.blockD hbeF'))
      have heq₁ : renVEnv σc ((decl.params.zip argvals) ++ bindZeros D decl.rets)
          = (decl₂.params.zip argvals) ++ bindZeros D decl₂.rets := by
        rw [renVEnv_append, renVEnv_zip, renVEnv_bindZeros, hps, hrs]
      rw [heq₁] at hstep_body
      have hVendKeys : Vend.map Prod.fst
          = ((decl.params.zip argvals) ++ bindZeros D decl.rets).map Prod.fst :=
        block_keys hbody
      have hcfgVend : RenCfg σc Vend loF := RenCfg.of_keys hVendKeys hcfg₁
      have hvals : decl₂.rets.map (fun r => (VEnv.get (renVEnv σc Vend) r).getD D.zero)
          = decl.rets.map (fun r => (VEnv.get Vend r).getD D.zero) := by
        rw [hrs, List.map_map]
        refine List.map_congr_left (fun r hr => ?_)
        show (VEnv.get (renVEnv σc Vend) (σc r)).getD D.zero = _
        have hrNF : NotFresh r := by
          refine hcfgF.keys_notFresh r ?_
          rw [hbz]
          exact List.mem_append.mpr (Or.inr hr)
        rw [renVEnv_get σc Vend r (hcfgVend.no_merge hrNF)]
      have hstep := Step.callOk
        (ihargs hcfg hφ hfuns trivial trivial (hns : _ ∧ _).2
          (.args (lo := lo) (hi := hi) ha2)).1
        hlook₂ (by rw [hps, List.length_map]; exact hlen) hstep_body ho
      rw [hvals] at hstep
      exact ⟨hstep, trivial⟩
  | @callHalt funs V st fn args argvals st1 decl cenv Vend st2 hargs hlook hlen hbody ihargs ihbody =>
      intro lo hi σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hsc hfsc hns hcode
      cases hcode with | expr hae =>
      cases hae with | call hfn ha2 =>
      obtain ⟨hsub, hfnmem⟩ := lookupFun_scopes_sub hlook
      have hnm : ∀ s ∈ funs, ∀ p ∈ s, φ p.1 = φ fn → p.1 = fn :=
        fun s hs => hφ.no_merge_scope hfn hs
      obtain ⟨decl₂, cenv₂, hlook₂, hFD, hRc⟩ := lookupFun_renFunsRelF hfuns hnm hlook
      obtain ⟨loF, hiF, σc, σc', φc', hps, hrs, hcfgF, hφd, hnsF, hwsF, hfsF, hbeF⟩ := hFD
      have hsubn : ∀ a ∈ funNamesOf cenv, a ∈ funNamesOf funs := by
        intro a ha
        obtain ⟨s, hs, ha2⟩ := List.mem_flatMap.mp ha
        exact List.mem_flatMap.mpr ⟨s, hsub s hs, ha2⟩
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
      have hkeys₁ : ((decl.params.zip argvals) ++ bindZeros D decl.rets).map Prod.fst
          = decl.params ++ decl.rets := by
        rw [List.map_append, List.map_fst_zip (Nat.le_of_eq hlen.symm)]
        congr 1
        simp [bindZeros, List.map_map, Function.comp_def]
      have hcfg₁ : RenCfg σc ((decl.params.zip argvals) ++ bindZeros D decl.rets) loF :=
        RenCfg.of_keys (by rw [hkeys₁, hbz]) hcfgF
      obtain ⟨hstep_body, _⟩ := ihbody hcfg₁ hφF hRc'
        (by
          show WScopedStmts (((decl.params.zip argvals) ++
            bindZeros D decl.rets).map Prod.fst) decl.body
          rw [hkeys₁]
          exact hwsF)
        hfsF
        (by
          show NormalForm.ScopedStmts (((decl.params.zip argvals) ++
              bindZeros D decl.rets).map Prod.fst)
            (funNamesOf cenv ++ NormalForm.funDefNames decl.body) decl.body
          rw [hkeys₁]
          exact hnsF)
        (.stmt (.blockD hbeF'))
      have heq₁ : renVEnv σc ((decl.params.zip argvals) ++ bindZeros D decl.rets)
          = (decl₂.params.zip argvals) ++ bindZeros D decl₂.rets := by
        rw [renVEnv_append, renVEnv_zip, renVEnv_bindZeros, hps, hrs]
      rw [heq₁] at hstep_body
      exact ⟨Step.callHalt
        (ihargs hcfg hφ hfuns trivial trivial (hns : _ ∧ _).2
          (.args (lo := lo) (hi := hi) ha2)).1
        hlook₂ (by rw [hps, List.length_map]; exact hlen) hstep_body, trivial⟩

end YulEvmCompiler.Optimizer.Normalize
