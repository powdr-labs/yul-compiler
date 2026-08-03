import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.LoopSim
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.OfYulSound.LoopStepSim

The iteration cases of the `for` loop.

`sim_loopStepShared` carries everything the two body-completes-normally loop
clauses have in common — the condition edge, the body fragment, the post
block entry — up to the point where the source derivation of the post
fragment is consumed; `sim_loopStep` and `sim_loopPostHalt` supply the two
continuations.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics (Ident Literal Expr Stmt VEnv Outcome)
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal evmWithExternal)

section Semantics
variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates

set_option maxHeartbeats 1000000 in
/-- The shared run of a loop iteration whose body completes: evaluate the
condition, take the true edge into the body block, run the body, and arrive at
the post block with a register file that rebinds the loop's modified set.
`hcont` receives that post-block situation and finishes the clause — either
by recursing on the next iteration (`sim_loopStep`) or by propagating the halt
the post fragment raises (`sim_loopPostHalt`). -/
theorem sim_loopStepShared {P : Prog} {f : Func}
    {funs : YulSemantics.FunEnv yulD} {V Vb : VEnv yulD}
    {st st1 stb : EvmState} {c : Expr Op} {post body : List (Stmt Op)}
    {cv : U256} {ob : Outcome} {doneFuncs : Array (Option Func)}
    {hfuncs : FuncTableComplete P doneFuncs} {Q : Prop}
    {fenv : FMap} {env : VMap} {rets : Option (List Ident)}
    {s₀ s₁ : BState} {renv : Option VMap} {joins : List BlockId}
    {xvals hParams exitParams postParams hX : List ValId}
    {sA sB sC sD sE sF sG sH sI sJ sK sL sM sN sO : BState}
    {hId exitId postId bodyId : BlockId} {cvId : ValId}
    {bodyEnv : Option VMap} {done : BState} {owned : List FuncId} {R : Regs}
    (h1 : edgeArgs env (modifiedX env [post, body]) s₀ = some (xvals, sA))
    (h2 : (modifiedX env [post, body]).mapM (fun _ => freshVal) sA =
      some (hParams, sB))
    (h3 : newBlock hParams sB = some (hId, sC))
    (h4 : (modifiedX env [post, body]).mapM (fun _ => freshVal) sC =
      some (exitParams, sD))
    (h5 : newBlock exitParams sD = some (exitId, sE))
    (h6 : (modifiedX env [post, body]).mapM (fun _ => freshVal) sE =
      some (postParams, sF))
    (h7 : newBlock postParams sF = some (postId, sG))
    (h8 : sealCur (.jump ⟨hId, xvals⟩) sG = some ((), sH))
    (h9 : moveTo hId sH = some ((), sI))
    (h10 : trExpr fenv
      (env.setMany (modifiedX env [post, body]) hParams) c sI = some (cvId, sJ))
    (h11 : newBlock [] sJ = some (bodyId, sK))
    (h12 : edgeArgs (env.setMany (modifiedX env [post, body]) hParams)
      (modifiedX env [post, body]) sK = some (hX, sL))
    (h13 : sealCur (.branch cvId ⟨bodyId, []⟩ ⟨exitId, hX⟩) sL = some ((), sM))
    (h14 : moveTo bodyId sM = some ((), sN))
    (h15 : trScope fenv
      (env.setMany (modifiedX env [post, body]) hParams)
      (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body sN =
      some (bodyEnv, sO))
    (htr : (do
      if let some envB := bodyEnv then
        let xvB ← edgeArgs envB (modifiedX env [post, body])
        sealCur (.jump ⟨postId, xvB⟩)
      moveTo postId
      let envP := env.setMany (modifiedX env [post, body]) postParams
      let renvP ← trScope fenv envP none rets post
      if let some envP' := renvP then
        let xvP ← edgeArgs envP' (modifiedX env [post, body])
        sealCur (.jump ⟨hId, xvP⟩)
      moveTo exitId
      pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sO =
      some (renv, s₁))
    (hfe : FEnvOK (model := model) P funs fenv)
    (huniq : env.Unique)
    (hctx : CtxVars none rets env)
    (hp : ProtectedAt joins s₀.fn)
    (hcompl : Completes f s₁.fn joins)
    (hdone : done.funcs = doneFuncs)
    (hbound : ∀ i : FuncId, i ∈ owned → i < s₀.funcs.size)
    (hown : FOwned owned s₁ done)
    (henv : EnvOK (model := model)
      (env.setMany (modifiedX env [post, body]) hParams) V R)
    (hfr : RegsFresh R sI.fn)
    (hclean : HeaderClean sA.fn.nextVal hParams R)
    (hpTail : FPrefix sO.funcs.size sO s₁)
    (ihc : Motive (model := model) P f funs V st doneFuncs hfuncs
      (.expr c) (.eres (.vals [cv] st1)))
    (hbodyStep : YulSemantics.Step yulD funs V st1 (.stmt (.block body))
      (.sres Vb stb ob))
    (ihb : Motive (model := model) P f funs V st1 doneFuncs hfuncs
      (.stmt (.block body)) (.sres Vb stb ob))
    (hnz : cv ≠ YulSemantics.Dialect.zero yulD)
    (hob : ob = .normal ∨ ob = .«continue»)
    (hpostCont : ∀ (sPost sPostOut : BState) (postEnv : Option VMap) (RP : Regs),
      Regs.Le R RP → RegsFresh RP sPost.fn →
      EnvOK (model := model)
        (env.setMany (modifiedX env [post, body]) postParams) Vb RP →
      SimS (model := model) P f sI.fn R st sPost.fn RP stb →
      CurValid sPost → ProtectedAt (exitId :: joins) sPost.fn →
      ProtectedAt (exitId :: joins) sPostOut.fn →
      Completes f sPostOut.fn (exitId :: joins) → CurPlaced f sPostOut.fn →
      (postEnv = none → CurFinal f sPostOut.fn) →
      (∀ i : FuncId, i ∈ owned → i < sPost.funcs.size) →
      FOwned owned sPostOut done →
      trStmt fenv (env.setMany (modifiedX env [post, body]) postParams)
        none rets (.block post) sPost = some (postEnv, sPostOut) →
      (do
        if let some envP := postEnv then
          let xvP ← edgeArgs envP (modifiedX env [post, body])
          sealCur (.jump ⟨hId, xvP⟩)
        moveTo exitId
        pure (some (env.setMany (modifiedX env [post, body]) exitParams)))
          sPostOut = some (renv, s₁) →
      Q) :
    Q := by
    have G := loopGrowth h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    obtain ⟨g0A, gAB, gCD, gEF, a0A, a0B, a0C, a0D, a0E, a0F, a0G, a0H,
      hheadBase, a0I, aAI, gIJ, aJK, gKL, aJL, aJM, hbodyBase, aJN,
      eF, eG, eH, eI, eJ, eK, eL, eM, eN⟩ := id G
    obtain ⟨hcN, -, -, -, -⟩ := loopTail_exit h15 htr hcompl
    obtain ⟨hcJ, hcI, hcurI, hcurI0, hheadExit, hexitPost, hpI0, hpI, hvalidI,
      hvalidJ, csJL, hcurM, hbodyNe, hpM, hfinM, hbranchL, hbranchJ, hcpJ,
      hcpI⟩ := loopHeader G h3 h5 h7 h8 h9 h11 ⟨_, _, h12⟩ h13 h14 hp hcN
    obtain ⟨hlenH, hrangeH, hsB⟩ := M.mapM_freshVal_length h2
    have hndH : hParams.Nodup := by
      rw [hrangeH]
      exact M.nodup_range' _ _
    obtain ⟨RA, hleA, hbelowA, hfrA, hcv, hsimC⟩ := ihc.1 fenv
      (env.setMany (modifiedX env [post, body]) hParams) R sI sJ cvId cv
      (exitId :: postId :: joins) hfe henv hfr hpI hcJ hcpJ rfl h10
    have hnz' : cv ≠ 0 := by simpa only [yulD_zero] using hnz
    have aKN : SGrowsAt 0 sK sN :=
      ((SGrowsAt.of_grows gKL).trans (SGrowsAt.of_sealCur h13)).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h14)
    obtain ⟨bb, hbb, hbp⟩ := aKN.params bodyId ⟨[], [], .ret []⟩
      (newBlock_target_get h11)
    have hcurN : sN.fn.curId = bodyId := by
      rw [M.moveTo_apply] at h14
      exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h14).2).symm
    have hcurN0 : sN.fn.cur = [] := by
      rw [M.moveTo_apply] at h14
      simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h14).2
    have hsimB := simS_branchTrue_body (model := model) (P := P) (f := f)
      (st := st1) hcN hbranchJ hcv hnz' hbb hbp hcurN hcurN0
    have hvalidN : CurValid sN := by
      apply CurValid.of_moveTo _ h14
      exact Nat.lt_of_lt_of_le (newBlock_target_lt h11)
        ((SGrowsAt.of_grows (N := 0) gKL).trans
          (SGrowsAt.of_sealCur h13)).size
    have aIJ : SGrows sI sJ := SGrowsAt.of_grows gIJ
    have gIN : SGrows sI sN :=
      SGrowsAt.trans aIJ (aJN.mono aIJ.size)
    have hpN : ProtectedAt (exitId :: postId :: joins) sN.fn :=
      ProtectedAt.forward hpI gIN
    have gbody : SGrows sN sO := trScope_grows fenv
      (env.setMany (modifiedX env [post, body]) hParams)
      (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
      sN bodyEnv sO h15
    have hpO : ProtectedAt (exitId :: postId :: joins) sO.fn :=
      ProtectedAt.forward hpN gbody
    have htrB : trStmt fenv
        (env.setMany (modifiedX env [post, body]) hParams)
        (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets
        (.block body) sN = some (bodyEnv, sO) := by
      rw [trStmt]
      exact h15
    have hvalidO : CurValid sO := (trStmt_cur hvalidN htrB).1
    have tailBody :
        Completes f sO.fn (exitId :: postId :: joins) ∧
        CurPlaced f sO.fn ∧
        (bodyEnv = none → CurFinal f sO.fn) := by
      cases bodyEnv with
      | none =>
        change (do
          moveTo postId
          let envP := env.setMany (modifiedX env [post, body]) postParams
          let renvP ← trScope fenv envP none rets post
          if let some envP' := renvP then
            let xvP ← edgeArgs envP' (modifiedX env [post, body])
            sealCur (.jump ⟨hId, xvP⟩)
          moveTo exitId
          pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sO =
            some (renv, s₁) at htr
        obtain ⟨uP, sP, h16, htr⟩ := M.bind_inv htr
        obtain ⟨postEnv, sQ, h17, htr⟩ := M.bind_inv htr
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sP postEnv sQ h17
        have hcP : Completes f sP.fn (exitId :: postId :: joins) := by
          cases postEnv with
          | none =>
            change (do
              moveTo exitId
              pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sQ =
                some (renv, s₁) at htr
            obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
            obtain ⟨-, hs₁⟩ := M.pure_inv htr
            subst s₁
            have hcQ : Completes f sQ.fn (exitId :: postId :: joins) :=
              Completes.of_moveTo_protected (by simp) h18
                ((hcompl.protect postId).protect exitId)
            exact SGrowsAt.completes_of gp hcQ
          | some envP =>
            obtain ⟨xvP, sR, h18, htr⟩ := M.bind_inv htr
            obtain ⟨uS, sS, h19, htr⟩ := M.bind_inv htr
            obtain ⟨uT, sT, h20, htr⟩ := M.bind_inv htr
            obtain ⟨-, hs₁⟩ := M.pure_inv htr
            subst s₁
            have hcS : Completes f sS.fn (exitId :: postId :: joins) :=
              Completes.of_moveTo_protected (by simp) h20
                ((hcompl.protect postId).protect exitId)
            have gQS : SGrows sQ sS :=
              (SGrowsAt.of_grows (Grows.of_liftO h18)).trans
                (SGrowsAt.of_sealCur h19)
            exact SGrowsAt.completes_of gp
              (SGrowsAt.completes_of gQS hcS)
        have hpostNe : sO.fn.curId ≠ postId := fun he =>
          hpO.away (by simp [he])
        have hcurO0 := trScope_none_cur_nil fenv
          (env.setMany (modifiedX env [post, body]) hParams)
          (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
          sN sO h15
        have hcomplO := Completes.of_moveTo_protected (by simp) h16 hcP
        have hfinO := curFinal_of_move_grows h16 hpostNe hpO.away
          (SGrows.rfl' sP) hcP
        exact ⟨hcomplO,
          CurPlaced.of_moveTo_empty hvalidO hcurO0 hpostNe h16 hpO.away hcP,
          fun _ => hfinO⟩
      | some envB =>
        obtain ⟨xvB, sP, h16, htr⟩ := M.bind_inv htr
        obtain ⟨uQ, sQ, h17, htr⟩ := M.bind_inv htr
        obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
        obtain ⟨postEnv, sS, h19, htr⟩ := M.bind_inv htr
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sR postEnv sS h19
        have hcR : Completes f sR.fn (exitId :: postId :: joins) := by
          cases postEnv with
          | none =>
            change (do
              moveTo exitId
              pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sS =
                some (renv, s₁) at htr
            obtain ⟨uT, sT, h20, htr⟩ := M.bind_inv htr
            obtain ⟨-, hs₁⟩ := M.pure_inv htr
            subst s₁
            have hcS : Completes f sS.fn (exitId :: postId :: joins) :=
              Completes.of_moveTo_protected (by simp) h20
                ((hcompl.protect postId).protect exitId)
            exact SGrowsAt.completes_of gp hcS
          | some envP =>
            obtain ⟨xvP, sT, h20, htr⟩ := M.bind_inv htr
            obtain ⟨uU, sU, h21, htr⟩ := M.bind_inv htr
            obtain ⟨uW, sW, h22, htr⟩ := M.bind_inv htr
            obtain ⟨-, hs₁⟩ := M.pure_inv htr
            subst s₁
            have hcU : Completes f sU.fn (exitId :: postId :: joins) :=
              Completes.of_moveTo_protected (by simp) h22
                ((hcompl.protect postId).protect exitId)
            have gSU : SGrows sS sU :=
              (SGrowsAt.of_grows (Grows.of_liftO h20)).trans
                (SGrowsAt.of_sealCur h21)
            exact SGrowsAt.completes_of gp
              (SGrowsAt.completes_of gSU hcU)
        have hcQ : Completes f sQ.fn (exitId :: postId :: joins) :=
          Completes.of_moveTo_protected (by simp) h18 hcR
        have gOQ : SGrows sO sQ :=
          (SGrowsAt.of_grows (Grows.of_liftO h16)).trans
            (SGrowsAt.of_sealCur h17)
        have hpostNe : sQ.fn.curId ≠ postId := by
          have hpQ := ProtectedAt.forward hpO gOQ
          exact fun he => hpQ.away (by simp [he])
        have hfinQ := curFinal_of_move_grows h18 hpostNe
          (ProtectedAt.forward hpO gOQ).away (SGrows.rfl' sR) hcR
        have hsealP : CurOK f sP.fn ⟨[], .jump ⟨postId, xvB⟩⟩ :=
          curOK_of_sealCur hfinQ h17
        have hsP : sP = sO := (M.edgeArgs_inv h16).2
        subst sP
        exact ⟨SGrowsAt.completes_of gOQ hcQ, ⟨_, hsealP⟩,
          fun hbad => nomatch hbad⟩
    have hfrN : RegsFresh RA sN.fn := hfrA.mono aJN.nextVal
    have hboundN : ∀ i : FuncId, i ∈ owned → i < sN.funcs.size := by
      intro i hi
      exact Nat.lt_of_lt_of_le (hbound i hi)
        (Nat.le_trans a0I.funcsSize
          (Nat.le_trans (SGrows.of_grows gIJ).funcsSize aJN.funcsSize))
    have hboundO : ∀ i : FuncId, i ∈ owned → i < sO.funcs.size := by
      intro i hi
      exact Nat.lt_of_lt_of_le (hboundN i hi) gbody.funcsSize
    have hownO : FOwned owned sO done :=
      FOwned.back_fprefix hpTail hboundO hown
    have hbodySim := ihb fenv
      (env.setMany (modifiedX env [post, body]) hParams) RA
      (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets
      sN sO bodyEnv (exitId :: postId :: joins) hfe
      (henv.mono hleA) (huniq.setMany _ _)
      (hctx.loopBody exitId postId [post, body] hParams) hfrN hvalidN hpN
      tailBody.1 tailBody.2.1 tailBody.2.2 done owned hdone hboundN hownO htrB
    have hpre := hsimC.trans hsimB
    have gGNall : SGrowsAt 0 sG sN :=
      (((((SGrowsAt.of_sealCur (N := 0) h8).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)).trans
        (SGrowsAt.of_grows gIJ)).trans (aJL.mono (Nat.zero_le _))).trans
        (SGrowsAt.of_sealCur h13)).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h14)
    have finish : ∀ {sPost sPostOut : BState} {postEnv : Option VMap}
        {RB : Regs} {vals : List U256},
        SGrowsAt 0 sO sPost → sPost.fn.curId = postId → sPost.fn.cur = [] →
        CurValid sPost →
        trScope fenv (env.setMany (modifiedX env [post, body]) postParams)
            none rets post sPost = some (postEnv, sPostOut) →
        (do
          if let some envP := postEnv then
            let xvP ← edgeArgs envP (modifiedX env [post, body])
            sealCur (.jump ⟨hId, xvP⟩)
          moveTo exitId
          pure (some (env.setMany (modifiedX env [post, body]) exitParams)))
            sPostOut = some (renv, s₁) →
        Regs.Le RA RB → Regs.BelowEq sN.fn.nextVal RA RB →
        RegsFresh RB sO.fn →
        List.Forall₂ (fun x v => YulSemantics.VEnv.get Vb x = some v)
          (modifiedX env [post, body]) vals →
        (∀ res, JumpTo (model := model) P f postId vals RB stb res →
          ExecFrom (model := model) P f sI.fn R st res) →
        Q := by
      intro sPost sPostOut postEnv RB vals gOP hcurPost hcurPost0 hvalidPost
        htrPost htailPost hleB hbelowB hfrB hvals hcont
      have gpost : SGrows sPost sPostOut := trScope_grows fenv
        (env.setMany (modifiedX env [post, body]) postParams) none rets post
        sPost postEnv sPostOut htrPost
      have hpostBase : s₀.fn.blocks.size ≤ postId := by
        rw [SGrowsAt.newBlock_id h7]
        exact a0F.size
      have hpPost : ProtectedAt (exitId :: joins) sPost.fn := by
        refine ⟨?_, ?_⟩
        · intro i hi
          apply Nat.lt_of_lt_of_le (hpO.below i ?_) gOP.size
          simp only [List.mem_cons] at hi ⊢
          rcases hi with rfl | hi
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hi)
        · rw [hcurPost]
          simp only [List.mem_cons, not_or]
          exact ⟨Nat.ne_of_gt hexitPost, fun hmem =>
            Nat.not_lt_of_ge hpostBase (hp.below postId hmem)⟩
      have hpPostOut : ProtectedAt (exitId :: joins) sPostOut.fn :=
        ProtectedAt.forward hpPost gpost
      have htrPostStmt : trStmt fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets
          (.block post) sPost = some (postEnv, sPostOut) := by
        rw [trStmt]
        exact htrPost
      have hvalidPostOut : CurValid sPostOut :=
        (trStmt_cur hvalidPost htrPostStmt).1
      obtain ⟨hcomplPostOut, hcpPostOut, hfinPostOut⟩ :=
        loopPost_back hvalidPostOut hpPostOut htrPost htailPost hcompl
      have hcomplPost : Completes f sPost.fn (exitId :: joins) :=
        SGrowsAt.completes_of gpost hcomplPostOut
      obtain ⟨hlenP, hrangeP, hsF⟩ := M.mapM_freshVal_length h6
      have hndP : postParams.Nodup := by
        rw [hrangeP]
        exact M.nodup_range' _ _
      have fI : SGrowsAt 0 sF sI :=
        ((SGrowsAt.of_newBlock (N := 0) h7).trans
          (SGrowsAt.of_sealCur h8)).trans
          (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)
      have fN : SGrowsAt 0 sF sN := fI.trans
        (((SGrowsAt.of_grows (N := 0) gIJ).trans
          (aJL.mono (Nat.zero_le _))).trans
          (SGrowsAt.of_sealCur h13) |>.trans
            (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h14))
      have hparamsLtN : ∀ i ∈ postParams, i < sN.fn.nextVal := by
        intro i hi
        rw [hrangeP] at hi
        exact Nat.lt_of_lt_of_le
          (by simpa [hsF] using (M.mem_range'_bounds hi).2) fN.nextVal
      have hparamsLtO : ∀ i ∈ postParams, i < sO.fn.nextVal := by
        intro i hi
        exact Nat.lt_of_lt_of_le (hparamsLtN i hi) gbody.nextVal
      have hnoneP : ∀ i ∈ postParams, RB i = none := by
        intro i hi
        rw [hbelowB i (hparamsLtN i hi)]
        have hiRange := hi
        rw [hrangeP] at hiRange
        have hiLtI : i < sI.fn.nextVal := Nat.lt_of_lt_of_le
          (by simpa [hsF] using (M.mem_range'_bounds hiRange).2) fI.nextVal
        rw [hbelowA i hiLtI]
        apply hclean i
        · exact Nat.le_trans
            (((SGrowsAt.of_grows (N := 0) gAB).trans
              (SGrowsAt.of_newBlock h3)).trans (SGrowsAt.of_grows gCD) |>.trans
              (SGrowsAt.of_newBlock h5)).nextVal
            (M.mem_range'_bounds hiRange).1
        · intro hiH
          rw [hrangeH] at hiH
          have hu := (M.mem_range'_bounds hiH).2
          have hl := (M.mem_range'_bounds hiRange).1
          have hnextCB : sC.fn.nextVal = sB.fn.nextVal := by
            rw [M.newBlock_apply] at h3
            exact (congrArg (fun z => z.fn.nextVal)
              (M.some_pair_inj h3).2).symm
          have hendH : sA.fn.nextVal + (modifiedX env [post, body]).length =
              sC.fn.nextVal := by rw [hnextCB, hsB]
          have huC : i < sC.fn.nextVal := by rwa [hendH] at hu
          have hCE : sC.fn.nextVal ≤ sE.fn.nextVal :=
            (SGrowsAt.of_grows (N := 0) gCD).trans
              (SGrowsAt.of_newBlock h5) |>.nextVal
          exact Nat.not_lt_of_ge (Nat.le_trans hCE hl) huC
      have hbaseP : ∀ i ∈ postParams, sA.fn.nextVal ≤ i := by
        intro i hi
        rw [hrangeP] at hi
        exact Nat.le_trans
          (((SGrowsAt.of_grows (N := 0) gAB).trans
            (SGrowsAt.of_newBlock h3)).trans (SGrowsAt.of_grows gCD) |>.trans
            (SGrowsAt.of_newBlock h5)).nextVal
          (M.mem_range'_bounds hi).1
      have gGPost : SGrowsAt 0 sG sPost :=
        (gGNall.trans (gbody.mono (Nat.zero_le _))).trans gOP
      obtain ⟨pb, hpb, hpp⟩ := gGPost.params postId
        ⟨postParams, [], .ret []⟩ (newBlock_target_get h7)
      have hnextOP : sO.fn.nextVal ≤ sPost.fn.nextVal := gOP.nextVal
      have hVbody : YulSemantics.VEnv.setMany V
          (modifiedX env [post, body]) vals = Vb := by
        have hnames : VEnv.names Vb = VEnv.names V := by
          have hm := (mod_sim hbodyStep).1
          simpa [declsOfStmt] using hm
        have hmod : ModOut [] (modStmts [] body) V Vb := by
          have hm := (mod_sim hbodyStep).2 [] (localsOK_nil V)
          simpa [modStmt] using hm
        exact setMany_eq_of_modOut (xs := modifiedX env [post, body]) henv
          (huniq.setMany _ _) hnames hmod hvals
          (fun x hx => by
            rw [VMap.names_setMany]
            exact modifiedX_mem_names hx)
          (fun x hx hm => mem_modifiedX (by
            rw [VMap.names_setMany] at hx
            exact hx) (by
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
            exact List.mem_append_right _ hm))
      have hleBody : Regs.Le R RB := hleA.trans hleB
      have hbelowBody : Regs.BelowEq sA.fn.nextVal R RB :=
        (hbelowA.mono aAI.nextVal).trans
          (hbelowB.mono (Nat.le_trans aAI.nextVal
            (Nat.le_trans (SGrowsAt.of_grows (N := 0) gIJ).nextVal
              aJN.nextVal)))
      obtain ⟨RP, hleP, hbelowP, hfrP, henvP, hsimP⟩ :=
        sim_loopPostEntry (model := model) (P := P) (f := f) (sBody := sO)
          (base := sA.fn.nextVal) henv hVbody hleBody hbelowBody hndP hnoneP
          hbaseP hparamsLtO hfrB hnextOP hcomplPost hpb hpp hcurPost
          hcurPost0 (by rw [hlenP]; exact hvals.length_eq) hcont
      rw [VMap.setMany_overwrite env (modifiedX_nodup huniq _)
        hlenH.symm hlenP.symm] at henvP
      have hboundPost : ∀ i : FuncId, i ∈ owned → i < sPost.funcs.size := by
        intro i hi
        exact Nat.lt_of_lt_of_le (hbound i hi)
          (Nat.le_trans a0G.funcsSize gGPost.funcsSize)
      have hboundPostOut : ∀ i : FuncId,
          i ∈ owned → i < sPostOut.funcs.size := by
        intro i hi
        exact Nat.lt_of_lt_of_le (hboundPost i hi) gpost.funcsSize
      have hownPostOut : FOwned owned sPostOut done :=
        FOwned.back_fprefix (loopPostTail_fprefix htailPost)
          hboundPostOut hown
      exact hpostCont sPost sPostOut postEnv RP hleP hfrP henvP hsimP
        hvalidPost hpPost hpPostOut hcomplPostOut hcpPostOut hfinPostOut
        hboundPost hownPostOut htrPostStmt htailPost
    rcases hob with rfl | rfl
    · obtain ⟨envB, RB, hbodyEnv, hleB, hbelowB, hfrB, henvB, _huniqB,
          hsimBody⟩ := hbodySim
      obtain rfl : bodyEnv = some envB := hbodyEnv
      obtain ⟨xvB, sP, h16, htr⟩ := M.bind_inv htr
      obtain ⟨uQ, sQ, h17, htr⟩ := M.bind_inv htr
      obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
      obtain ⟨postEnv, sS, h19, htailPost⟩ := M.bind_inv htr
      obtain ⟨rfl, vals, hgetB, hvals⟩ := edgeArgs_ok henvB h16
      have gOQ : SGrows sP sQ :=
        (SGrowsAt.of_grows (Grows.of_liftO h16)).trans
          (SGrowsAt.of_sealCur h17)
      have hpQ := ProtectedAt.forward hpO gOQ
      have gp := trScope_grows fenv
        (env.setMany (modifiedX env [post, body]) postParams) none rets post
        sR postEnv sS h19
      have gQR : SGrowsAt 0 sQ sR :=
        SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h18
      have hvalidR : CurValid sR := CurValid.of_moveTo
        (Nat.lt_of_lt_of_le (newBlock_target_lt h7)
          ((gGNall.trans (gbody.mono (Nat.zero_le _))).trans
            (gOQ.mono (Nat.zero_le _))).size)
        h18
      have hpostBase : s₀.fn.blocks.size ≤ postId := by
        rw [SGrowsAt.newBlock_id h7]
        exact a0F.size
      have hpRPost : ProtectedAt (exitId :: joins) sR.fn := by
        refine ⟨?_, ?_⟩
        · intro i hi
          have hi' : i ∈ exitId :: postId :: joins := by
            simp only [List.mem_cons] at hi ⊢
            rcases hi with rfl | hi
            · exact Or.inl rfl
            · exact Or.inr (Or.inr hi)
          exact Nat.lt_of_lt_of_le (hpQ.below i hi') gQR.size
        · have hcurR : sR.fn.curId = postId := by
            rw [M.moveTo_apply] at h18
            exact (congrArg (fun z => z.fn.curId)
              (M.some_pair_inj h18).2).symm
          rw [hcurR]
          simp only [List.mem_cons, not_or]
          exact ⟨Nat.ne_of_gt hexitPost, fun hmem =>
            Nat.not_lt_of_ge hpostBase (hp.below postId hmem)⟩
      have hvalidS : CurValid sS :=
        (trStmt_cur hvalidR (by rw [trStmt]; exact h19)).1
      have hpS : ProtectedAt (exitId :: joins) sS.fn :=
        ProtectedAt.forward hpRPost gp
      have hback := loopPost_back hvalidS hpS h19 htailPost hcompl
      have hcR := (SGrowsAt.completes_of gp hback.1).protect postId
      have hpQ' : ProtectedAt (postId :: exitId :: joins) sQ.fn := by
        refine ⟨?_, ?_⟩
        · intro i hi
          apply hpQ.below i
          simp only [List.mem_cons] at hi ⊢
          rcases hi with rfl | rfl | hi
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hi)
        · intro hi
          apply hpQ.away
          simp only [List.mem_cons] at hi ⊢
          rcases hi with h | h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
      have hfinQ := curFinal_of_move_grows h18
        (fun he => hpQ'.away (by simp [he])) hpQ'.away
        (SGrows.rfl' sR) hcR
      have hcurJump : CurOK f sP.fn ⟨[], .jump ⟨postId, xvB⟩⟩ :=
        curOK_of_sealCur hfinQ h17
      have hcont : ∀ res, JumpTo (model := model) P f postId vals RB stb res →
          ExecFrom (model := model) P f sI.fn R st res := by
        intro res hj
        exact hpre res (hsimBody res (execFrom_jump hcurJump hgetB hj))
      exact finish
        (((SGrowsAt.of_grows (N := 0) (Grows.of_liftO h16)).trans
          (SGrowsAt.of_sealCur h17)).trans
          (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h18))
        (by rw [M.moveTo_apply] at h18
            exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h18).2).symm)
        (by rw [M.moveTo_apply] at h18
            simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h18).2)
        (CurValid.of_moveTo
          (Nat.lt_of_lt_of_le (newBlock_target_lt h7)
            ((gGNall.trans (gbody.mono (Nat.zero_le _))).trans
              (gOQ.mono (Nat.zero_le _))).size)
          h18)
        h19 htailPost hleB hbelowB hfrB hvals hcont
    · obtain ⟨lc, RB, vals, hlc, hleB, hbelowB, hfrB, hvals, hcontB⟩ :=
        hbodySim
      have hlc' : lc = ⟨exitId, postId, modifiedX env [post, body]⟩ :=
        Option.some.inj hlc.symm
      subst lc
      cases bodyEnv with
      | none =>
        change (do
          moveTo postId
          let envP := env.setMany (modifiedX env [post, body]) postParams
          let renvP ← trScope fenv envP none rets post
          if let some envP' := renvP then
            let xvP ← edgeArgs envP' (modifiedX env [post, body])
            sealCur (.jump ⟨hId, xvP⟩)
          moveTo exitId
          pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sO =
            some (renv, s₁) at htr
        obtain ⟨uP, sP, h16, htr⟩ := M.bind_inv htr
        obtain ⟨postEnv, sQ, h17, htailPost⟩ := M.bind_inv htr
        have hcont : ∀ res,
            JumpTo (model := model) P f postId vals RB stb res →
            ExecFrom (model := model) P f sI.fn R st res :=
          fun res hj => hpre res (hcontB res hj)
        exact finish (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h16)
          (by rw [M.moveTo_apply] at h16
              exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h16).2).symm)
          (by rw [M.moveTo_apply] at h16
              simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h16).2)
          (CurValid.of_moveTo
            (Nat.lt_of_lt_of_le (newBlock_target_lt h7)
              (gGNall.trans (gbody.mono (Nat.zero_le _))).size) h16)
          h17 htailPost hleB hbelowB hfrB hvals hcont
      | some envB =>
        obtain ⟨xvB, sP, h16, htr⟩ := M.bind_inv htr
        obtain ⟨uQ, sQ, h17, htr⟩ := M.bind_inv htr
        obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
        obtain ⟨postEnv, sS, h19, htailPost⟩ := M.bind_inv htr
        have gOQ : SGrows sO sQ :=
          (SGrowsAt.of_grows (Grows.of_liftO h16)).trans
            (SGrowsAt.of_sealCur h17)
        have hcont : ∀ res,
            JumpTo (model := model) P f postId vals RB stb res →
            ExecFrom (model := model) P f sI.fn R st res :=
          fun res hj => hpre res (hcontB res hj)
        exact finish
          ((gOQ.mono (Nat.zero_le _)).trans
            (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h18))
          (by rw [M.moveTo_apply] at h18
              exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h18).2).symm)
          (by rw [M.moveTo_apply] at h18
              simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h18).2)
          (CurValid.of_moveTo
            (Nat.lt_of_lt_of_le (newBlock_target_lt h7)
              ((gGNall.trans (gbody.mono (Nat.zero_le _))).trans
                (gOQ.mono (Nat.zero_le _))).size)
            h18)
          h19 htailPost hleB hbelowB hfrB hvals hcont


set_option maxHeartbeats 1000000 in
/-- **The loop iteration case.**  The body completes, the post fragment
completes, and the back edge re-enters the header with the rebound modified
set — so the remaining iterations are exactly the recursive `LOut`. -/
theorem sim_loopStep {P : Prog} {f : Func} {funs : YulSemantics.FunEnv yulD}
    {V Vb Vp Vend : VEnv yulD} {st st1 stb stp stend : EvmState}
    {c : Expr Op} {post body : List (Stmt Op)} {cv : U256} {ob o : Outcome}
    {doneFuncs : Array (Option Func)} {hfuncs : FuncTableComplete P doneFuncs}
    (ihc : Motive (model := model) P f funs V st doneFuncs hfuncs
      (.expr c) (.eres (.vals [cv] st1)))
    (hnz : cv ≠ YulSemantics.Dialect.zero yulD)
    (hbodyStep : YulSemantics.Step yulD funs V st1 (.stmt (.block body))
      (.sres Vb stb ob))
    (hob : ob = .normal ∨ ob = .«continue»)
    (hpost : YulSemantics.Step yulD funs Vb stb (.stmt (.block post))
      (.sres Vp stp .normal))
    (ihb : Motive (model := model) P f funs V st1 doneFuncs hfuncs
      (.stmt (.block body)) (.sres Vb stb ob))
    (ihpost : Motive (model := model) P f funs Vb stb doneFuncs hfuncs
      (.stmt (.block post)) (.sres Vp stp .normal))
    (ihloop : Motive (model := model) P f funs Vp stp doneFuncs hfuncs
      (.loop c post body) (.sres Vend stend o)) :
    LOut (model := model) P f funs V st c post body Vend stend o
      doneFuncs := by
    intro fenv env rets s₀ s₁ renv joins layout hfe huniq hctx hvalid hp
      hcompl hcp _hfin done owned hdone hbound hown R henv hfr hclean hreb
    have hpTail := layout.tail_fprefix
    rcases layout with
      ⟨xvals, sA, h1, hParams, sB, h2, hId, sC, h3,
       exitParams, sD, h4, exitId, sE, h5, postParams, sF, h6,
       postId, sG, h7, sH, h8, sI, h9, cvId, sJ, h10,
       bodyId, sK, h11, hX, sL, h12, sM, h13, sN, h14,
       bodyEnv, sO, h15, htr⟩
    simp only [] at henv hfr hclean hreb ⊢
    have G := loopGrowth h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    obtain ⟨g0A, gAB, gCD, gEF, a0A, a0B, a0C, a0D, a0E, a0F, a0G, a0H,
      hheadBase, a0I, aAI, gIJ, aJK, gKL, aJL, aJM, hbodyBase, aJN,
      eF, eG, eH, eI, eJ, eK, eL, eM, eN⟩ := id G
    obtain ⟨hcN, -, -, -, -⟩ := loopTail_exit h15 htr hcompl
    obtain ⟨hcJ, hcI, hcurI, hcurI0, hheadExit, hexitPost, hpI0, hpI, hvalidI,
      hvalidJ, csJL, hcurM, hbodyNe, hpM, hfinM, hbranchL, hbranchJ, hcpJ,
      hcpI⟩ := loopHeader G h3 h5 h7 h8 h9 h11 ⟨_, _, h12⟩ h13 h14 hp hcN
    obtain ⟨hlenH, hrangeH, hsB⟩ := M.mapM_freshVal_length h2
    have hndH : hParams.Nodup := by
      rw [hrangeH]
      exact M.nodup_range' _ _
    refine sim_loopStepShared h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
      h15 htr hfe huniq hctx hp hcompl hdone hbound hown henv hfr hclean
      hpTail ihc hbodyStep ihb hnz hob ?_
    intro sPost sPostOut postEnv RP hleP hfrP henvP hsimP hvalidPost hpPost
      hpPostOut hcomplPostOut hcpPostOut hfinPostOut hboundPost hownPostOut
      htrPostStmt htailPost
    obtain ⟨envP, RPost, hpostEnv, hlePost, hbelowPost, hfrPost,
        henvPost, huniqPost, hsimPost⟩ := ihpost fenv
      (env.setMany (modifiedX env [post, body]) postParams) RP none rets
      sPost sPostOut postEnv (exitId :: joins) hfe henvP
      (huniq.setMany _ _) (hctx.setMany _ _) hfrP hvalidPost hpPost
      hcomplPostOut hcpPostOut
      hfinPostOut done owned hdone hboundPost hownPostOut htrPostStmt
    obtain rfl : postEnv = some envP := hpostEnv
    change (do
      let xvP ← edgeArgs envP (modifiedX env [post, body])
      sealCur (.jump ⟨hId, xvP⟩)
      moveTo exitId
      pure (some (env.setMany (modifiedX env [post, body]) exitParams)))
        sPostOut = some (renv, s₁) at htailPost
    obtain ⟨xvNext, sEdge, hargsNext, htailPost⟩ := M.bind_inv htailPost
    obtain ⟨uSeal, sSealed, hsealNext, htailPost⟩ := M.bind_inv htailPost
    obtain ⟨uExit, sExit, hmoveExit, htailPost⟩ := M.bind_inv htailPost
    obtain ⟨hrenv, hs₁⟩ := M.pure_inv htailPost
    subst s₁
    obtain ⟨rfl, valsNext, hgetNext, hvalsNext⟩ :=
      edgeArgs_ok henvPost hargsNext
    have hnamesBody : VEnv.names Vb = VEnv.names V := by
      have hm := (mod_sim hbodyStep).1
      simpa [declsOfStmt] using hm
    have hnamesPost : VEnv.names Vp = VEnv.names Vb := by
      have hm := (mod_sim hpost).1
      simpa [declsOfStmt] using hm
    have hnamesNext : VEnv.names Vp = VEnv.names V :=
      hnamesPost.trans hnamesBody
    have hmodBody : ModOut [] (modStmts [] body) V Vb := by
      have hm := (mod_sim hbodyStep).2 [] (localsOK_nil V)
      simpa [modStmt] using hm
    have hmodPost : ModOut [] (modStmts [] post) Vb Vp := by
      have hm := (mod_sim hpost).2 [] (localsOK_nil Vb)
      simpa [modStmt] using hm
    have hmodNext : ModOut []
        (modStmts [] body ++ modStmts [] post) V Vp :=
      ModOut.trans hmodBody hmodPost (fun _ hn => by
        rw [← VEnv.length_names, hnamesBody, VEnv.length_names]
        exact hn)
    have hVnext : YulSemantics.VEnv.setMany V
        (modifiedX env [post, body]) valsNext = Vp :=
      setMany_eq_of_modOut (xs := modifiedX env [post, body]) henv
        (huniq.setMany _ _) hnamesNext hmodNext hvalsNext
        (fun x hx => by
          rw [VMap.names_setMany]
          exact modifiedX_mem_names hx)
        (fun x hx hm => mem_modifiedX (by
          rw [VMap.names_setMany] at hx
          exact hx) (by
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
          rcases List.mem_append.mp hm with hb | hp'
          · exact List.mem_append_right _ hb
          · exact List.mem_append_left _ hp'))
    let RNext := R.setMany hParams valsNext
    have hlenNext : hParams.length = valsNext.length :=
      hlenH.trans hvalsNext.length_eq
    have henvNext : EnvOK (model := model)
        (env.setMany (modifiedX env [post, body]) hParams) Vp RNext := by
      exact hreb valsNext Vp hvalsNext.length_eq hVnext
    have bI : SGrowsAt 0 sB sI :=
      ((((((SGrowsAt.of_newBlock (N := 0) h3).trans
        (SGrowsAt.of_grows gCD)).trans (SGrowsAt.of_newBlock h5)).trans
        (SGrowsAt.of_grows gEF)).trans (SGrowsAt.of_newBlock h7)).trans
        (SGrowsAt.of_sealCur h8)).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)
    have hendI : sA.fn.nextVal + (modifiedX env [post, body]).length ≤
        sI.fn.nextVal := by
      have hn := bI.nextVal
      rw [hsB] at hn
      exact hn
    have hfrNext : RegsFresh RNext sI.fn := by
      intro i hi
      dsimp [RNext]
      rw [Regs.setMany_other]
      · exact hfr i hi
      · intro him
        rw [hrangeH] at him
        exact absurd (Nat.lt_of_lt_of_le (M.mem_range'_bounds him).2 hendI)
          (Nat.not_lt_of_ge hi)
    have hcleanNext : HeaderClean sA.fn.nextVal hParams RNext := by
      intro i hi hnot
      dsimp [RNext]
      rw [Regs.setMany_other hnot]
      exact hclean i hi hnot
    have hrebNext : HeaderRebind (model := model)
        (env.setMany (modifiedX env [post, body]) hParams)
        (modifiedX env [post, body]) hParams Vp RNext := by
      intro vals' W hlen' hset'
      dsimp [RNext]
      rw [Regs.setMany_overwrite R hndH hlenNext (hlenH.trans hlen')]
      apply hreb vals' W hlen'
      rw [← hset', ← hVnext,
        VEnv.setMany_overwrite V (modifiedX_nodup huniq _)
          hvalsNext.length_eq hlen']
    let layout' : LoopLayout fenv env rets c post body s₀ sExit renv :=
      ⟨xvals, sA, h1, hParams, sB, h2, hId, sC, h3,
       exitParams, sD, h4, exitId, sE, h5, postParams, sF, h6,
       postId, sG, h7, sH, h8, sI, h9, cvId, sJ, h10,
       bodyId, sK, h11, hX, sL, h12, sM, h13, sN, h14,
       bodyEnv, sO, h15, htr⟩
    have hrec := ihloop fenv env rets s₀ sExit renv joins layout'
      hfe huniq hctx hvalid hp hcompl hcp _hfin done owned hdone hbound hown
      RNext henvNext hfrNext hcleanNext hrebNext
    have cI : SGrowsAt 0 sC sI :=
      (((((SGrowsAt.of_grows (N := 0) gCD).trans
        (SGrowsAt.of_newBlock h5)).trans (SGrowsAt.of_grows gEF)).trans
        (SGrowsAt.of_newBlock h7)).trans (SGrowsAt.of_sealCur h8)).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)
    obtain ⟨hbH, hhbH, hhpH⟩ := cI.params hId
      ⟨hParams, [], .ret []⟩ (newBlock_target_get h3)
    have hleToPost : Regs.Le R RPost := hleP.trans hlePost
    have hleBack : Regs.Le RNext (RPost.setMany hParams valsNext) := by
      exact Regs.Le.setManyBoth hleToPost
    have hlenBack : hbH.params.length = valsNext.length := by
      rw [hhpH]
      exact hlenNext
    have gPostSeal : SGrows sEdge sSealed :=
      (SGrowsAt.of_grows (Grows.of_liftO hargsNext)).trans
        (SGrowsAt.of_sealCur hsealNext)
    have hpSealed : ProtectedAt (exitId :: joins) sSealed.fn :=
      ProtectedAt.forward hpPostOut gPostSeal
    have hcExit : Completes f sExit.fn (exitId :: joins) := by
      exact hcompl.protect exitId
    have hcSealed : Completes f sSealed.fn (exitId :: joins) :=
      Completes.of_moveTo_protected (by simp) hmoveExit hcExit
    have hneExit : sSealed.fn.curId ≠ exitId := fun he =>
      hpSealed.away (by simp [he])
    have hfinSealed : CurFinal f sSealed.fn :=
      curFinal_of_move_grows hmoveExit hneExit hpSealed.away
        (SGrows.rfl' sExit) hcExit
    have hcurBack : CurOK f sEdge.fn
        ⟨[], .jump ⟨hId, xvNext⟩⟩ :=
      curOK_of_sealCur hfinSealed hsealNext
    have hbridge : ∀ res,
        ExecFrom (model := model) P f sI.fn RNext stp res →
        ExecFrom (model := model) P f sI.fn R st res := by
      intro res hex
      have hjump : JumpTo (model := model) P f hId valsNext RPost stp res :=
        jumpTo_of_completes hcI hhbH hcurI hcurI0 hlenBack (by
          simpa only [hhpH] using hex.mono hleBack)
      exact hsimP res (hsimPost res
        (execFrom_jump hcurBack hgetNext hjump))
    have hbaseH : ∀ i ∈ hParams, sA.fn.nextVal ≤ i := by
      intro i hi
      rw [hrangeH] at hi
      exact (M.mem_range'_bounds hi).1
    have hbelowNext : Regs.BelowEq sA.fn.nextVal R RNext :=
      Regs.BelowEq.setMany hbaseH
    cases o with
    | normal =>
      obtain ⟨envEnd, REnd, hrenvEnd, hbelowEnd, hfrEnd, henvEnd,
        huniqEnd, hsimEnd⟩ := hrec
      exact ⟨envEnd, REnd, hrenvEnd, hbelowNext.trans hbelowEnd,
        hfrEnd, henvEnd, huniqEnd, fun res hex => hbridge res (hsimEnd res hex)⟩
    | halt => exact hbridge (.halt stend) hrec
    | leave =>
      obtain ⟨rs, retVals, hrets, hretVals, hex⟩ := hrec
      exact ⟨rs, retVals, hrets, hretVals, hbridge (.ret retVals stend) hex⟩
    | «break» => exact hrec.elim
    | «continue» => exact hrec.elim

set_option maxHeartbeats 1000000 in
/-- **The halting-post case.**  The body completes and the post fragment
halts, so the loop halts where post did: the post block's simulation carries
the halt back to the loop entry. -/
theorem sim_loopPostHalt {P : Prog} {f : Func}
    {funs : YulSemantics.FunEnv yulD} {V Vb Vp : VEnv yulD}
    {st st1 stb stp : EvmState} {c : Expr Op} {post body : List (Stmt Op)}
    {cv : U256} {ob : Outcome}
    {doneFuncs : Array (Option Func)} {hfuncs : FuncTableComplete P doneFuncs}
    (ihc : Motive (model := model) P f funs V st doneFuncs hfuncs
      (.expr c) (.eres (.vals [cv] st1)))
    (hnz : cv ≠ YulSemantics.Dialect.zero yulD)
    (hbodyStep : YulSemantics.Step yulD funs V st1 (.stmt (.block body))
      (.sres Vb stb ob))
    (hob : ob = .normal ∨ ob = .«continue»)
    (ihb : Motive (model := model) P f funs V st1 doneFuncs hfuncs
      (.stmt (.block body)) (.sres Vb stb ob))
    (ihpost : Motive (model := model) P f funs Vb stb doneFuncs hfuncs
      (.stmt (.block post)) (.sres Vp stp .halt)) :
    LOut (model := model) P f funs V st c post body Vp stp .halt
      doneFuncs := by
    intro fenv env rets s₀ s₁ renv joins layout hfe huniq hctx hvalid hp
      hcompl hcp _hfin done owned hdone hbound hown R henv hfr hclean hreb
    have hpTail := layout.tail_fprefix
    rcases layout with
      ⟨xvals, sA, h1, hParams, sB, h2, hId, sC, h3,
       exitParams, sD, h4, exitId, sE, h5, postParams, sF, h6,
       postId, sG, h7, sH, h8, sI, h9, cvId, sJ, h10,
       bodyId, sK, h11, hX, sL, h12, sM, h13, sN, h14,
       bodyEnv, sO, h15, htr⟩
    simp only [] at henv hfr hclean hreb ⊢
    have G := loopGrowth h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    obtain ⟨g0A, gAB, gCD, gEF, a0A, a0B, a0C, a0D, a0E, a0F, a0G, a0H,
      hheadBase, a0I, aAI, gIJ, aJK, gKL, aJL, aJM, hbodyBase, aJN,
      eF, eG, eH, eI, eJ, eK, eL, eM, eN⟩ := id G
    obtain ⟨hcN, -, -, -, -⟩ := loopTail_exit h15 htr hcompl
    obtain ⟨hcJ, hcI, hcurI, hcurI0, hheadExit, hexitPost, hpI0, hpI, hvalidI,
      hvalidJ, csJL, hcurM, hbodyNe, hpM, hfinM, hbranchL, hbranchJ, hcpJ,
      hcpI⟩ := loopHeader G h3 h5 h7 h8 h9 h11 ⟨_, _, h12⟩ h13 h14 hp hcN
    obtain ⟨hlenH, hrangeH, hsB⟩ := M.mapM_freshVal_length h2
    have hndH : hParams.Nodup := by
      rw [hrangeH]
      exact M.nodup_range' _ _
    refine sim_loopStepShared h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
      h15 htr hfe huniq hctx hp hcompl hdone hbound hown henv hfr hclean
      hpTail ihc hbodyStep ihb hnz hob ?_
    intro sPost sPostOut postEnv RP _hleP hfrP henvP hsimP hvalidPost hpPost
      _hpPostOut hcomplPostOut hcpPostOut hfinPostOut hboundPost hownPostOut
      htrPostStmt _htailPost
    have hpostHalt := ihpost fenv
      (env.setMany (modifiedX env [post, body]) postParams) RP none rets
      sPost sPostOut postEnv (exitId :: joins) hfe henvP
      (huniq.setMany _ _) (hctx.setMany _ _) hfrP hvalidPost hpPost
      hcomplPostOut hcpPostOut
      hfinPostOut done owned hdone hboundPost hownPostOut htrPostStmt
    exact hsimP (.halt stp) hpostHalt
end Semantics
end YulEvmCompiler.SsaCfg
