import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.CondSim
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.OfYulSound.BlockSim

The sequencing and `for`-wrapper statement cases of `sim`.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics (Ident Literal Expr Stmt VEnv Outcome)
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal evmWithExternal)

section Semantics
variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates YulSemantics.EVM.ExternalGas.any

set_option maxHeartbeats 1000000 in
/-- **A `for` whose initializer completes.**  The initializer scope is
allocated and run, and the static loop layout is entered from its end. -/
theorem sim_forLoop {P : Prog} {f : Func} {funs : YulSemantics.FunEnv yulD}
    {V Vinit Vend : VEnv yulD} {st stinit stend : EvmState} {c : Expr Op}
    {init post body : List (Stmt Op)} {o : Outcome}
    {doneFuncs : Array (Option Func)}
    {hfuncs : FuncTableComplete P doneFuncs}
    (hinit : YulSemantics.Step yulD (YulSemantics.hoist yulD init :: funs) V st
      (.stmts init) (.sres Vinit stinit .normal))
    (hloop : YulSemantics.Step yulD (YulSemantics.hoist yulD init :: funs)
      Vinit stinit (.loop c post body) (.sres Vend stend o))
    (ihi : Motive (model := model) P f
      (YulSemantics.hoist yulD init :: funs) V st doneFuncs hfuncs
      (.stmts init) (.sres Vinit stinit .normal))
    (ihl : Motive (model := model) P f
      (YulSemantics.hoist yulD init :: funs) Vinit stinit doneFuncs hfuncs
      (.loop c post body) (.sres Vend stend o)) :
    Motive (model := model) P f funs V st doneFuncs hfuncs
      (.stmt (.forLoop init c post body))
      (.sres (YulSemantics.restore V Vend) stend o) := by
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq hctx hfr hvalid hp
      hcompl hcp hfin done owned hdone hbound hown htr
    obtain ⟨scope, sA, sI, rinit, ha, hi, htail⟩ := trStmt_forLoop_inv htr
    have hfnA : sA.fn = s₀.fn := (allocScope_funcsOnly ha).1
    have hvalidA : CurValid sA := by rw [CurValid, hfnA]; exact hvalid
    have hfrA : RegsFresh R sA.fn := by simpa only [hfnA] using hfr
    have hpA : ProtectedAt joins sA.fn := by simpa only [hfnA] using hp
    have gAI := trStmts_grows (scope :: fenv) env lctx rets false init
      sA rinit sI hi
    have hvalidI : CurValid sI :=
      (trStmts_cur (scope :: fenv) env lctx rets false init
        sA rinit sI hvalidA hi).1
    have hpI : ProtectedAt joins sI.fn := ProtectedAt.forward hpA gAI
    have hboundI : ∀ i : FuncId, i ∈ owned → i < sI.funcs.size := by
      intro i him
      exact Nat.lt_of_lt_of_le (hbound i him)
        (Nat.le_trans (allocScope_funcsOnly ha).2 gAI.funcsSize)
    cases rinit with
    | none =>
        obtain ⟨hrenv, hs₁⟩ := htail
        subst renv
        subst s₁
        obtain ⟨hfe', hbound', hslots, hnd, -⟩ :=
          allocScope_motive_inputs hfuncs hfe hdone hbound hown ha hi
        have hout := ihi (scope :: fenv) env R lctx rets sA sI none joins
          hfe' henv huniq hctx hfrA hvalidA hpA hcompl hcp hfin
          done owned hdone hbound' hslots hnd hown hi
        obtain ⟨env', R', hbad, -⟩ := hout
        cases hbad
    | some envI =>
        obtain ⟨envX, ⟨layout⟩, hrenv⟩ := htail
        have hcomplI : Completes f sI.fn joins :=
          layout.sgrows.completes_of hcompl
        have hcpI : CurPlaced f sI.fn :=
          curPlaced_back (renv := some envX)
            (Or.inr (layout.curMoved hvalidI)) hpI.away hcompl
            (fun hbad => nomatch hbad) hcp
        have hownI : FOwned owned sI done :=
          FOwned.back_fprefix layout.fprefix hboundI hown
        obtain ⟨hfe', hbound', hslots, hnd, -⟩ :=
          allocScope_motive_inputs hfuncs hfe hdone hbound hownI ha hi
        have hinitOut := ihi (scope :: fenv) env R lctx rets
          sA sI (some envI) joins hfe' henv huniq hctx hfrA hvalidA hpA
          hcomplI hcpI (fun hbad => nomatch hbad)
          done owned hdone hbound' hslots hnd hownI hi
        have hinner : SOut (model := model) P f lctx rets sA s₁ R
            (some envX) Vend st stend o := by
          apply SOut.seq gAI.nextVal hinitOut
          intro RI hleI hfrI henvI huniqI
          obtain ⟨RH, hbelowH, hfrH, henvH, hcleanH, hrebH, hsimH⟩ :=
            layout.enter henvI huniqI hfrI hvalidI hpI hcompl
          have hctxI : CtxVars lctx rets envI := by
            obtain ⟨W, hnamesI, -⟩ := (mod_sim hinit).1
            refine hctx.mono (fun x hx => ?_)
            rw [henv.names] at hx
            rw [henvI.names, hnamesI]
            exact List.mem_append_right W hx
          have hctxLoop : CtxVars none rets envI := by
            constructor
            · intro lc hnone
              cases hnone
            · exact hctxI.2
          have hloopOut := ihl (scope :: fenv) envI rets sI s₁
            (some envX) joins layout hfe' huniqI hctxLoop hvalidI hpI hcompl hcp
            (fun hbad => nomatch hbad) done owned hdone hboundI hown
            RH henvH hfrH hcleanH hrebH
          have hbase : sI.fn.nextVal ≤ layout.sA.fn.nextVal := by
            rw [(M.edgeArgs_inv layout.h1).2]
          exact LHOut.prefix hbase hbelowH hfrI hsimH hloopOut
        have hnsEnd : NoShadow (model := model) V Vend := by
          obtain ⟨W, hnamesInit, hdisj⟩ :=
            (ns_sim hinit (scope :: fenv) env lctx rets sA sI (some envI)
              henv.names hi).1
          apply noShadow_of_NSOut
          exact ⟨W, (loop_names hloop).trans hnamesInit, hdisj⟩
        subst renv
        rcases loop_outcome_ssa hloop with rfl | rfl | rfl
        · obtain ⟨envEnd, REnd, henvEnd, hleEnd, hbelowEnd, hfrEnd,
            henvOK, huniqEnd, hsimEnd⟩ := hinner
          obtain rfl : envX = envEnd := Option.some.inj henvEnd
          refine ⟨(envX.drop (envX.length - env.length)), REnd, rfl,
            hleEnd, ?_, hfrEnd, henvOK.restore henv.length,
            huniqEnd.drop _, ?_⟩
          · simpa only [hfnA] using hbelowEnd
          · simpa only [hfnA] using hsimEnd
        · change ExecFrom (model := model) P f s₀.fn R st (.halt stend)
          change ExecFrom (model := model) P f sA.fn R st (.halt stend) at hinner
          rwa [hfnA] at hinner
        · obtain ⟨rs, vals, hrs, hvals, hex⟩ := hinner
          refine ⟨rs, vals, hrs, ?_, ?_⟩
          · exact List.Forall₂.imp_mem hvals (fun x hx v hv => by
              rw [get_restore_of_noShadow hnsEnd]
              · exact hv
              · rw [← henv.names]
                exact hctx.2 rs hrs x hx)
          · simpa only [hfnA] using hex

set_option maxHeartbeats 1000000 in
/-- **A statement sequence that continues.**  The head statement falls
through, handing its residual environment and register file to the tail. -/
theorem sim_seqCons {P : Prog} {f : Func} {funs : YulSemantics.FunEnv yulD}
    {V V1 V2 : VEnv yulD} {st st1 st2 : EvmState} {s : Stmt Op}
    {rest : List (Stmt Op)} {o : Outcome} {doneFuncs : Array (Option Func)}
    {hfuncs : FuncTableComplete P doneFuncs}
    (h1 : YulSemantics.Step yulD funs V st (.stmt s) (.sres V1 st1 .normal))
    (ih1 : Motive (model := model) P f funs V st doneFuncs hfuncs
      (.stmt s) (.sres V1 st1 .normal))
    (ih2 : Motive (model := model) P f funs V1 st1 doneFuncs hfuncs
      (.stmts rest) (.sres V2 st2 o)) :
    Motive (model := model) P f funs V st doneFuncs hfuncs
      (.stmts (s :: rest)) (.sres V2 st2 o) := by
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq hctx hfr hvalid
      hp hcompl hcp hfin done owned hdone hbound hslots hnd hown htr
    cases s with
    | funDef n ps rs body =>
      cases h1
      rw [trStmts] at htr
      obtain ⟨fid, sA, ha, htr⟩ := M.bind_inv htr
      obtain ⟨g, sB, hb, htr⟩ := M.bind_inv htr
      obtain ⟨u, sC, hc, htail⟩ := M.bind_inv htr
      obtain ⟨hget, hsA⟩ := M.liftO_inv ha
      subst sA
      simp only [stmtFuncIds, hget, Option.toList_some,
        List.singleton_append] at hbound hslots hnd
      have hpFunc := trFunc_prefix fenv ps rs body hb
      have hfid0 : s₀.funcs[fid]? = some none := hslots fid (by simp)
      have hfidB : sB.funcs[fid]? = some none := by
        rw [hpFunc fid (lt_size_of_getElem? hfid0)]
        exact hfid0
      obtain ⟨hfidLt, hsC⟩ := M.fillFunc_inv hc
      have hndTail : (stmtFuncIds fenv rest ++ owned).Nodup :=
        (List.nodup_cons.mp hnd).2
      have hfidNot : fid ∉ stmtFuncIds fenv rest ++ owned :=
        (List.nodup_cons.mp hnd).1
      have hslotsTail : ∀ i : FuncId, i ∈ stmtFuncIds fenv rest →
          sC.funcs[i]? = some none := by
        intro i hi
        have hi0 := hslots i (by simp [hi])
        have hiB : sB.funcs[i]? = some none := by
          rw [hpFunc i (lt_size_of_getElem? hi0)]
          exact hi0
        have hine : i ≠ fid := by
          intro he
          subst i
          exact hfidNot (List.mem_append_left _ hi)
        rw [hsC, Array.getElem?_set (h := hfidLt), if_neg (Ne.symm hine)]
        exact hiB
      have hboundTail : ∀ i : FuncId,
          i ∈ stmtFuncIds fenv rest ++ owned → i < sC.funcs.size := by
        intro i hi
        have hi0 := hbound i (by simp [hi])
        rw [hsC]
        simpa using Nat.lt_of_lt_of_le hi0 (hpFunc.size (Nat.le_refl _))
      have hfnB : sB.fn = s₀.fn := (trFunc_grows fenv ps rs body s₀ g sB hb).1
      have hfnC : sC.fn = sB.fn := by rw [(M.fillFunc_inv hc).choose_spec]
      have hfn : sC.fn = s₀.fn := hfnC.trans hfnB
      have hvalidC : CurValid sC := by rw [CurValid, hfn]; exact hvalid
      have hpC : ProtectedAt joins sC.fn := by simpa only [hfn] using hp
      simpa only [SOut, hfn] using
        (ih2 fenv env R lctx rets sC s₁ renv joins hfe henv
          huniq hctx (by simpa only [hfn] using hfr) hvalidC
          hpC hcompl hcp hfin done owned hdone hboundTail hslotsTail
          hndTail hown htail)
    | block body | letDecl vars val | assign vars e | cond e body
    | forLoop init e post body | «break» | «continue» | leave
    | switch e cases dflt | exprStmt e =>
      simp only [stmtFuncIds] at hbound hslots hnd
      obtain ⟨renvA, sA, hhead, htail⟩ := trStmts_false_cons_inv
        (by intros; simp) htr
      have hvalidA : CurValid sA := (trStmt_cur hvalid hhead).1
      have hgHead : SGrows s₀ sA :=
        trStmt_grows fenv env lctx rets _ s₀ renvA sA hhead
      have hpA : ProtectedAt joins sA.fn := ProtectedAt.forward hp hgHead
      have hpHead := trStmt_fprefix fenv env lctx rets _ s₀.funcs.size
        s₀ renvA sA (Nat.le_refl _) hhead
      have hboundA : ∀ i : FuncId,
          i ∈ stmtFuncIds fenv rest ++ owned → i < sA.funcs.size := by
        intro i hi
        exact Nat.lt_of_lt_of_le (hbound i hi) (hpHead.size (Nat.le_refl _))
      have hslotsA : ∀ i : FuncId, i ∈ stmtFuncIds fenv rest →
          sA.funcs[i]? = some none := by
        intro i hi
        rw [hpHead i (hbound i (List.mem_append_left _ hi))]
        exact hslots i hi
      cases renvA with
      | none =>
        obtain ⟨hrenv, hfn⟩ := trStmts_true_fn fenv env lctx rets rest sA s₁ renv htail
        have hcomplA : Completes f sA.fn joins := by simpa only [hfn] using hcompl
        have hcpA : CurPlaced f sA.fn := by simpa only [hfn] using hcp
        have hfinA : CurFinal f sA.fn := by
          simpa only [hfn] using hfin hrenv
        have hownA := trStmts_owned_back fenv lctx rets rest env true
          sA s₁ done renv owned hboundA hslotsA hnd hown htail
        obtain ⟨envA, R₁, hbad, -⟩ :=
          ih1 fenv env R lctx rets s₀ sA none joins hfe henv huniq hctx hfr
            hvalid hp hcomplA hcpA
            (fun _ => hfinA) done (stmtFuncIds fenv rest ++ owned) hdone
            hbound hownA hhead
        exact absurd hbad (by simp)
      | some envA =>
        have hgTail : SGrows sA s₁ :=
          trStmts_grows fenv envA lctx rets false rest sA renv s₁ htail
        have hcomplA : Completes f sA.fn joins := SGrowsAt.completes_of hgTail hcompl
        have hcpA : CurPlaced f sA.fn :=
          trStmts_curPlaced_back hvalidA hpA hcompl hcp hfin htail
        have hownA := trStmts_owned_back fenv lctx rets rest envA false
          sA s₁ done renv owned hboundA hslotsA hnd hown htail
        refine SOut.seq hgHead.nextVal
          (ih1 fenv env R lctx rets s₀ sA (some envA) joins hfe henv huniq hctx
            hfr hvalid hp hcomplA hcpA
            (by simp) done (stmtFuncIds fenv rest ++ owned) hdone hbound
            hownA hhead) ?_
        intro R₁ hle hfrA henvA huniqA
        exact ih2 fenv envA R₁ lctx rets sA s₁ renv joins hfe henvA huniqA
          (hctx.step_normal henv henvA h1) hfrA
          hvalidA hpA hcompl hcp hfin done owned hdone hboundA hslotsA hnd
          hown htail
end Semantics
end YulEvmCompiler.SsaCfg
