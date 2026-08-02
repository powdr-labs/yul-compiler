import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.Loop
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.OfYulSound.LoopSim

The loop reconstruction.

`sim_loopBodyNonNormal` — the body-exits-abnormally case of the `for` loop —
together with the post-block entry step and the backward frame lemma the main
induction consumes.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics (Ident Literal Expr Stmt VEnv Outcome)
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal evmWithExternal)

section Semantics
variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates

set_option maxHeartbeats 1000000 in
/-- The shared nonzero-condition/body prefix for loop outcomes which bypass
post and the back edge. A body `break` uses the same prefix, then consumes its
edge at the protected exit block and becomes a normal loop result. -/
theorem sim_loopBodyNonNormal {P : Prog} {f : Func}
    {funs : YulSemantics.FunEnv yulD} {V Vb : VEnv yulD}
    {st st1 stb : EvmState} {c : Expr Op} {post body : List (Stmt Op)}
    {cv : U256} {o : Outcome} {doneFuncs : Array (Option Func)}
    (hfuncs : FuncTableComplete P doneFuncs)
    (ihc : Motive (model := model) P f funs V st doneFuncs hfuncs
      (.expr c) (.eres (.vals [cv] st1)))
    (hb : YulSemantics.Step yulD funs V st1 (.stmt (.block body))
      (.sres Vb stb o))
    (ihb : Motive (model := model) P f funs V st1 doneFuncs hfuncs
      (.stmt (.block body)) (.sres Vb stb o))
    (hnz : cv ≠ YulSemantics.Dialect.zero yulD)
    (ho : o = .halt ∨ o = .leave ∨ o = .break) :
    LOut (model := model) P f funs V st c post body Vb stb
      (if o = .break then .normal else o) doneFuncs := by
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
    have g0A : Grows s₀ sA := Grows.of_liftO h1
    have gAB : Grows sA sB := Grows.of_mapM_freshVal h2
    have gCD : Grows sC sD := Grows.of_mapM_freshVal h4
    have gEF : Grows sE sF := Grows.of_mapM_freshVal h6
    have a0A : SGrowsAt s₀.fn.blocks.size s₀ sA := SGrowsAt.of_grows g0A
    have a0B := a0A.trans (SGrowsAt.of_grows gAB)
    have a0C := a0B.trans (SGrowsAt.of_newBlock h3)
    have a0D := a0C.trans (SGrowsAt.of_grows gCD)
    have a0E := a0D.trans (SGrowsAt.of_newBlock h5)
    have a0F := a0E.trans (SGrowsAt.of_grows gEF)
    have a0G := a0F.trans (SGrowsAt.of_newBlock h7)
    have a0H := a0G.trans (SGrowsAt.of_sealCur h8)
    have hheadBase : s₀.fn.blocks.size ≤ hId := by
      rw [SGrowsAt.newBlock_id h3]
      exact a0B.size
    have a0I := a0H.trans (SGrowsAt.of_moveTo (Or.inl hheadBase) h9)
    have aAI : SGrowsAt 0 sA sI :=
      (((((((SGrowsAt.of_grows (N := 0) gAB).trans
        (SGrowsAt.of_newBlock h3)).trans (SGrowsAt.of_grows gCD)).trans
        (SGrowsAt.of_newBlock h5)).trans (SGrowsAt.of_grows gEF)).trans
        (SGrowsAt.of_newBlock h7)).trans (SGrowsAt.of_sealCur h8)).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)
    have gIJ : Grows sI sJ := trExpr_grows c fenv
      (env.setMany (modifiedX env [post, body]) hParams) sI sJ cvId h10
    have aJK : SGrowsAt sJ.fn.blocks.size sJ sK := SGrowsAt.of_newBlock h11
    have gKL : Grows sK sL := Grows.of_liftO h12
    have aJL := aJK.trans (SGrowsAt.of_grows gKL)
    have aJM := aJL.trans (SGrowsAt.of_sealCur h13)
    have hbodyBase : sJ.fn.blocks.size ≤ bodyId := by
      rw [SGrowsAt.newBlock_id h11]
    have aJN := aJM.trans (SGrowsAt.of_moveTo (Or.inl hbodyBase) h14)
    have eF : SGrowsAt 0 sE sF := SGrowsAt.of_grows gEF
    have eG := eF.trans (SGrowsAt.of_newBlock h7)
    have eH := eG.trans (SGrowsAt.of_sealCur h8)
    have eI := eH.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)
    have eJ := eI.trans (SGrowsAt.of_grows gIJ)
    have eK := eJ.trans (SGrowsAt.of_newBlock h11)
    have eL := eK.trans (SGrowsAt.of_grows gKL)
    have eM := eL.trans (SGrowsAt.of_sealCur h13)
    have eN := eM.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h14)
    have hcN : Completes f sN.fn (exitId :: postId :: joins) := by
      have gb := trScope_grows fenv
        (env.setMany (modifiedX env [post, body]) hParams)
        (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
        sN bodyEnv sO h15
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
          have hcP := SGrowsAt.completes_of gp hcQ
          have hcO := Completes.of_moveTo_protected (by simp) h16 hcP
          exact SGrowsAt.completes_of gb hcO
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
          have hcQ := SGrowsAt.completes_of gQS hcS
          have hcP := SGrowsAt.completes_of gp hcQ
          have hcO := Completes.of_moveTo_protected (by simp) h16 hcP
          exact SGrowsAt.completes_of gb hcO
      | some envB =>
        obtain ⟨xvB, sP, h16, htr⟩ := M.bind_inv htr
        obtain ⟨uQ, sQ, h17, htr⟩ := M.bind_inv htr
        obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
        obtain ⟨postEnv, sS, h19, htr⟩ := M.bind_inv htr
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sR postEnv sS h19
        have gOQ : SGrows sO sQ :=
          (SGrowsAt.of_grows (Grows.of_liftO h16)).trans
            (SGrowsAt.of_sealCur h17)
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
          have hcR := SGrowsAt.completes_of gp hcS
          have hcQ := Completes.of_moveTo_protected (by simp) h18 hcR
          have hcO := SGrowsAt.completes_of gOQ hcQ
          exact SGrowsAt.completes_of gb hcO
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
          have hcS := SGrowsAt.completes_of gSU hcU
          have hcR := SGrowsAt.completes_of gp hcS
          have hcQ := Completes.of_moveTo_protected (by simp) h18 hcR
          have hcO := SGrowsAt.completes_of gOQ hcQ
          exact SGrowsAt.completes_of gb hcO
    have hcJ : Completes f sJ.fn (exitId :: postId :: joins) :=
      SGrowsAt.completes_of aJN hcN
    have hcI : Completes f sI.fn (exitId :: postId :: joins) :=
      SGrowsAt.completes_of (SGrowsAt.of_grows gIJ) hcJ
    have hcurI : sI.fn.curId = hId := by
      rw [M.moveTo_apply] at h9
      exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h9).2).symm
    have hcurI0 : sI.fn.cur = [] := by
      rw [M.moveTo_apply] at h9
      simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h9).2
    have hheadExit : hId < exitId := by
      rw [SGrowsAt.newBlock_id h5]
      exact Nat.lt_of_lt_of_le (newBlock_target_lt h3)
        (SGrowsAt.of_grows (N := 0) gCD).size
    have hexitPost : exitId < postId := by
      rw [SGrowsAt.newBlock_id h7]
      exact Nat.lt_of_lt_of_le (newBlock_target_lt h5)
        (SGrowsAt.of_grows (N := 0) gEF).size
    have hpI0 : ProtectedAt joins sI.fn := ProtectedAt.forward hp a0I
    have hpI : ProtectedAt (exitId :: postId :: joins) sI.fn := by
      refine ⟨?_, ?_⟩
      · intro i hi
        simp only [List.mem_cons] at hi
        rcases hi with rfl | rfl | hi
        · exact Nat.lt_of_lt_of_le (newBlock_target_lt h5) eI.size
        · exact Nat.lt_of_lt_of_le (newBlock_target_lt h7)
            ((SGrowsAt.of_sealCur (N := 0) h8).trans
              (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h9)).size
        · exact hpI0.below i hi
      · simp only [List.mem_cons, not_or]
        exact ⟨by rw [hcurI]; exact Nat.ne_of_lt hheadExit,
          by rw [hcurI]; exact Nat.ne_of_lt (Nat.lt_trans hheadExit hexitPost),
          hpI0.away⟩
    have hvalidI : CurValid sI := by
      apply CurValid.of_moveTo _ h9
      exact Nat.lt_of_lt_of_le (newBlock_target_lt h3)
        (((((SGrowsAt.of_grows (N := 0) gCD).trans
          (SGrowsAt.of_newBlock h5)).trans
          (SGrowsAt.of_grows gEF)).trans
          (SGrowsAt.of_newBlock h7)).trans
          (SGrowsAt.of_sealCur h8)).size
    have hvalidJ : CurValid sJ := hvalidI.of_grows gIJ
    have csJL : CurSame sJ sL :=
      (CurSame.of_newBlock h11).trans (CurSame.of_grows gKL)
    have hcurM : sM.fn.curId = sJ.fn.curId := by
      rw [(sealCur_cur h13).choose_spec.1, csJL.1]
    have hbodyNe : sM.fn.curId ≠ bodyId := by
      rw [hcurM, SGrowsAt.newBlock_id h11]
      exact Nat.ne_of_lt hvalidJ
    have hpM : ProtectedAt (exitId :: postId :: joins) sM.fn := by
      have hgIM : SGrowsAt sI.fn.blocks.size sI sM :=
        ((SGrowsAt.of_grows (N := sI.fn.blocks.size) gIJ).trans
          (aJL.mono
            (SGrowsAt.of_grows (N := sI.fn.blocks.size) gIJ).size)).trans
          (SGrowsAt.of_sealCur h13)
      exact ProtectedAt.forward hpI hgIM
    have hfinM : CurFinal f sM.fn :=
      curFinal_of_move_grows h14 hbodyNe hpM.away (SGrows.rfl' sN) hcN
    have hbranchL : CurOK f sL.fn
        ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨exitId, hX⟩⟩ :=
      curOK_of_sealCur hfinM h13
    have hbranchJ : CurOK f sJ.fn
        ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨exitId, hX⟩⟩ :=
      CurOK.back_of_cur_eq csJL.1 (by
        have hnew : sK.fn.cur = sJ.fn.cur := by
          rw [M.newBlock_apply] at h11
          simpa using (congrArg (fun z => z.fn.cur) (M.some_pair_inj h11).2).symm
        have hedge : sL = sK := (M.edgeArgs_inv h12).2
        rw [hedge, hnew]) hbranchL
    have hcpJ : CurPlaced f sJ.fn := ⟨_, hbranchJ⟩
    have hcpI : CurPlaced f sI.fn := curPlaced_back_grows gIJ hcpJ
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
    rcases ho with rfl | rfl | rfl
    · rw [if_neg (by decide)]
      exact hpre (.halt stb) hbodySim
    · rw [if_neg (by decide)]
      obtain ⟨rs, vals, hrs, hvals, hex⟩ := hbodySim
      exact ⟨rs, vals, hrs, hvals, hpre (.ret vals stb) hex⟩
    · rw [if_pos rfl]
      obtain ⟨lc, RB, vals, hlc, hleB, hbelowB, hfrB, hvals, hcont⟩ :=
        hbodySim
      have hlc' : lc = ⟨exitId, postId, modifiedX env [post, body]⟩ :=
        Option.some.inj hlc.symm
      subst lc
      have tailData :
          SGrowsAt 0 sE s₁ ∧ sO.fn.nextVal ≤ s₁.fn.nextVal
            ∧ s₁.fn.curId = exitId ∧ s₁.fn.cur = []
            ∧ renv = some
              (env.setMany (modifiedX env [post, body]) exitParams) := by
        have gb := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) hParams)
          (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
          sN bodyEnv sO h15
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
          cases postEnv with
          | none =>
            change (do
              moveTo exitId
              pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sQ =
                some (renv, s₁) at htr
            obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
            obtain ⟨hrenv, hs₁⟩ := M.pure_inv htr
            subst s₁
            have go1 := (SGrowsAt.of_moveTo (N := 0)
              (Or.inl (Nat.zero_le _)) h16).trans (gp.mono (Nat.zero_le _))
            have go := go1.trans (SGrowsAt.of_moveTo
              (Or.inl (Nat.zero_le _)) h18)
            exact ⟨eN.trans ((gb.mono (Nat.zero_le _)).trans go), go.nextVal,
              by rw [M.moveTo_apply] at h18
                 exact (congrArg (fun z => z.fn.curId)
                   (M.some_pair_inj h18).2).symm,
              by rw [M.moveTo_apply] at h18
                 simpa using congrArg (fun z => z.fn.cur)
                   (M.some_pair_inj h18).2,
              hrenv⟩
          | some envP =>
            obtain ⟨xvP, sR, h18, htr⟩ := M.bind_inv htr
            obtain ⟨uS, sS, h19, htr⟩ := M.bind_inv htr
            obtain ⟨uT, sT, h20, htr⟩ := M.bind_inv htr
            obtain ⟨hrenv, hs₁⟩ := M.pure_inv htr
            subst s₁
            have gQS : SGrows sQ sS :=
              (SGrowsAt.of_grows (Grows.of_liftO h18)).trans
                (SGrowsAt.of_sealCur h19)
            have go1 := (SGrowsAt.of_moveTo (N := 0)
              (Or.inl (Nat.zero_le _)) h16).trans (gp.mono (Nat.zero_le _))
            have go2 := go1.trans (gQS.mono (Nat.zero_le _))
            have go := go2.trans (SGrowsAt.of_moveTo
              (Or.inl (Nat.zero_le _)) h20)
            exact ⟨eN.trans ((gb.mono (Nat.zero_le _)).trans go), go.nextVal,
              by rw [M.moveTo_apply] at h20
                 exact (congrArg (fun z => z.fn.curId)
                   (M.some_pair_inj h20).2).symm,
              by rw [M.moveTo_apply] at h20
                 simpa using congrArg (fun z => z.fn.cur)
                   (M.some_pair_inj h20).2,
              hrenv⟩
        | some envB =>
          obtain ⟨xvB, sP, h16, htr⟩ := M.bind_inv htr
          obtain ⟨uQ, sQ, h17, htr⟩ := M.bind_inv htr
          obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
          obtain ⟨postEnv, sS, h19, htr⟩ := M.bind_inv htr
          have gOQ : SGrows sO sQ :=
            (SGrowsAt.of_grows (Grows.of_liftO h16)).trans
              (SGrowsAt.of_sealCur h17)
          have gp := trScope_grows fenv
            (env.setMany (modifiedX env [post, body]) postParams) none rets post
            sR postEnv sS h19
          cases postEnv with
          | none =>
            change (do
              moveTo exitId
              pure (some (env.setMany (modifiedX env [post, body]) exitParams))) sS =
                some (renv, s₁) at htr
            obtain ⟨uT, sT, h20, htr⟩ := M.bind_inv htr
            obtain ⟨hrenv, hs₁⟩ := M.pure_inv htr
            subst s₁
            have go1 := (gOQ.mono (Nat.zero_le _)).trans
              (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h18)
            have go2 := go1.trans (gp.mono (Nat.zero_le _))
            have go := go2.trans (SGrowsAt.of_moveTo
              (Or.inl (Nat.zero_le _)) h20)
            exact ⟨eN.trans ((gb.mono (Nat.zero_le _)).trans go), go.nextVal,
              by rw [M.moveTo_apply] at h20
                 exact (congrArg (fun z => z.fn.curId)
                   (M.some_pair_inj h20).2).symm,
              by rw [M.moveTo_apply] at h20
                 simpa using congrArg (fun z => z.fn.cur)
                   (M.some_pair_inj h20).2,
              hrenv⟩
          | some envP =>
            obtain ⟨xvP, sT, h20, htr⟩ := M.bind_inv htr
            obtain ⟨uU, sU, h21, htr⟩ := M.bind_inv htr
            obtain ⟨uW, sW, h22, htr⟩ := M.bind_inv htr
            obtain ⟨hrenv, hs₁⟩ := M.pure_inv htr
            subst s₁
            have gSU : SGrows sS sU :=
              (SGrowsAt.of_grows (Grows.of_liftO h20)).trans
                (SGrowsAt.of_sealCur h21)
            have go1 := (gOQ.mono (Nat.zero_le _)).trans
              (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h18)
            have go2 := go1.trans (gp.mono (Nat.zero_le _))
            have go3 := go2.trans (gSU.mono (Nat.zero_le _))
            have go := go3.trans (SGrowsAt.of_moveTo
              (Or.inl (Nat.zero_le _)) h22)
            exact ⟨eN.trans ((gb.mono (Nat.zero_le _)).trans go), go.nextVal,
              by rw [M.moveTo_apply] at h22
                 exact (congrArg (fun z => z.fn.curId)
                   (M.some_pair_inj h22).2).symm,
              by rw [M.moveTo_apply] at h22
                 simpa using congrArg (fun z => z.fn.cur)
                   (M.some_pair_inj h22).2,
              hrenv⟩
      obtain ⟨ge, hnextO1, hcurExit, hcurExit0, hrenv⟩ := tailData
      obtain ⟨hlenE, hrangeE, hsD⟩ := M.mapM_freshVal_length h4
      have hndE : exitParams.Nodup := by
        rw [hrangeE]
        exact M.nodup_range' _ _
      have dI : SGrowsAt 0 sD sI :=
        (((((SGrowsAt.of_newBlock (N := 0) h5).trans
          (SGrowsAt.of_grows gEF)).trans (SGrowsAt.of_newBlock h7)).trans
          (SGrowsAt.of_sealCur h8)).trans
          (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9))
      have dN : SGrowsAt 0 sD sN := dI.trans
        (((SGrowsAt.of_grows (N := 0) gIJ).trans (aJL.mono (Nat.zero_le _))).trans
          (SGrowsAt.of_sealCur h13) |>.trans
            (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h14))
      have hparamsLtN : ∀ i ∈ exitParams, i < sN.fn.nextVal := by
        intro i hi
        rw [hrangeE] at hi
        exact Nat.lt_of_lt_of_le (by simpa [hsD] using (M.mem_range'_bounds hi).2)
          dN.nextVal
      have hnoneE : ∀ i ∈ exitParams, RB i = none := by
        intro i hi
        rw [hbelowB i (hparamsLtN i hi)]
        have hiRange := hi
        rw [hrangeE] at hiRange
        have hiLtI : i < sI.fn.nextVal := Nat.lt_of_lt_of_le
          (by simpa [hsD] using (M.mem_range'_bounds hiRange).2) dI.nextVal
        rw [hbelowA i hiLtI]
        apply hclean i
        · exact Nat.le_trans
            ((SGrowsAt.of_grows (N := 0) gAB).trans
              (SGrowsAt.of_newBlock h3)).nextVal
            (M.mem_range'_bounds hiRange).1
        · intro hiH
          rw [hrangeH] at hiH
          have hu := (M.mem_range'_bounds hiH).2
          have hl := (M.mem_range'_bounds hiRange).1
          have hnextCB : sC.fn.nextVal = sB.fn.nextVal := by
            rw [M.newBlock_apply] at h3
            exact (congrArg (fun z => z.fn.nextVal)
              (M.some_pair_inj h3).2).symm
          have hend : sA.fn.nextVal + (modifiedX env [post, body]).length =
              sC.fn.nextVal := by rw [hnextCB, hsB]
          have hu' : i < sC.fn.nextVal := by rwa [hend] at hu
          exact Nat.not_lt_of_ge hl hu'
      let RE := RB.setMany exitParams vals
      have hleE : Regs.Le RB RE := Regs.Le.setMany hndE hnoneE
      have hbelowE : Regs.BelowEq sA.fn.nextVal RB RE := by
        apply Regs.BelowEq.setMany
        intro i hi
        rw [hrangeE] at hi
        exact Nat.le_trans
          ((SGrowsAt.of_grows (N := 0) gAB).trans
            (SGrowsAt.of_newBlock h3)).nextVal
          (M.mem_range'_bounds hi).1
      have hfrE : RegsFresh RE s₁.fn := by
        intro i hi
        dsimp [RE]
        rw [Regs.setMany_other]
        · exact hfrB i (Nat.le_trans hnextO1 hi)
        · intro him
          exact absurd (hparamsLtN i him)
            (Nat.not_lt_of_ge (Nat.le_trans
              ((trScope_grows fenv
                (env.setMany (modifiedX env [post, body]) hParams)
                (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
                sN bodyEnv sO h15).nextVal) (Nat.le_trans hnextO1 hi)))
      obtain ⟨eb, heb, hep⟩ := ge.params exitId ⟨exitParams, [], .ret []⟩
        (newBlock_target_get h5)
      have hlenEB : eb.params.length = vals.length := by
        rw [hep, hlenE]
        exact hvals.length_eq
      have hsimExit : SimS (model := model) P f sI.fn R st s₁.fn RE stb := by
        intro res hex
        apply hpre res
        apply hcont res
        apply jumpTo_of_completes hcompl heb
          hcurExit hcurExit0 hlenEB
        simpa only [RE, hep] using hex
      have hnames : VEnv.names Vb = VEnv.names V := by
        have hm := (mod_sim hb).1
        simpa [declsOfStmt] using hm
      have hmod : ModOut [] (modStmts [] body) V Vb := by
        have hm := (mod_sim hb).2 [] (localsOK_nil V)
        simpa [modStmt] using hm
      have hVexit : YulSemantics.VEnv.setMany V
          (modifiedX env [post, body]) vals = Vb :=
        setMany_eq_of_modOut (xs := modifiedX env [post, body]) henv
          (huniq.setMany _ _) hnames hmod hvals
          (fun x hx => by
            rw [VMap.names_setMany]
            exact modifiedX_mem_names hx)
          (fun x hx hm => mem_modifiedX (by
            rw [VMap.names_setMany] at hx
            exact hx) (by
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
            exact List.mem_append_right _ hm))
      have hpgetE : RE.getMany exitParams = some vals :=
        Regs.getMany_setMany_self hndE (by rw [hlenE]; exact hvals.length_eq)
      have henvE : EnvOK (model := model)
          (env.setMany (modifiedX env [post, body]) exitParams) Vb RE := by
        have he : EnvOK (model := model)
            ((env.setMany (modifiedX env [post, body]) hParams).setMany
              (modifiedX env [post, body]) exitParams)
            (YulSemantics.VEnv.setMany V (modifiedX env [post, body]) vals) RE :=
          EnvOK.setMany
            (henv.mono (hleA.trans (hleB.trans hleE)))
            (Regs.getMany_eq_some_iff.mp hpgetE)
        rw [VMap.setMany_overwrite env (modifiedX_nodup huniq _)
          hlenH.symm hlenE.symm] at he
        rwa [hVexit] at he
      have hbelowFinal : Regs.BelowEq sA.fn.nextVal R RE :=
        (hbelowA.mono aAI.nextVal).trans
          ((hbelowB.mono (Nat.le_trans aAI.nextVal
            (Nat.le_trans (SGrowsAt.of_grows (N := 0) gIJ).nextVal
              aJN.nextVal))).trans hbelowE)
      exact ⟨env.setMany (modifiedX env [post, body]) exitParams, RE, hrenv,
        hbelowFinal,
        hfrE, henvE, huniq.setMany _ _, hsimExit⟩

/-- Bind the values carried by a body fall-through/`continue` edge to the
reserved post block's parameters.  This is the common post-entry boundary of
`loopStep` and `loopPostHalt`: it extends the register file at the fresh post
parameters, reconstructs the fixed post environment, and turns the body's
edge continuation into a straight-line simulation ending at the post block. -/
theorem sim_loopPostEntry {P : Prog} {f : Func} {X : List Ident}
    {V Vb : VEnv yulD} {env : VMap} {R₀ RB : Regs}
    {st stb : EvmState} {fn₀ : FnState} {sBody sPost : BState}
    {postId : BlockId} {postParams : List ValId} {vals : List U256}
    {pb : Block} {joins : List BlockId} {base : Nat}
    (henv : EnvOK (model := model) env V R₀)
    (hV : YulSemantics.VEnv.setMany V X vals = Vb)
    (hle : Regs.Le R₀ RB) (hbelow : Regs.BelowEq base R₀ RB)
    (hnd : postParams.Nodup) (hnone : ∀ i ∈ postParams, RB i = none)
    (hbase : ∀ i ∈ postParams, base ≤ i)
    (hparamsLt : ∀ i ∈ postParams, i < sBody.fn.nextVal)
    (hfr : RegsFresh RB sBody.fn)
    (hnext : sBody.fn.nextVal ≤ sPost.fn.nextVal)
    (hcompl : Completes f sPost.fn joins)
    (hpb : sPost.fn.blocks[postId]? = some pb)
    (hpp : pb.params = postParams)
    (hcur : sPost.fn.curId = postId) (hcur0 : sPost.fn.cur = [])
    (hlen : postParams.length = vals.length)
    (hcont : ∀ res, JumpTo (model := model) P f postId vals RB stb res →
      ExecFrom (model := model) P f fn₀ R₀ st res) :
    ∃ RP : Regs, Regs.Le R₀ RP ∧ Regs.BelowEq base R₀ RP
      ∧ RegsFresh RP sPost.fn
      ∧ EnvOK (model := model) (env.setMany X postParams) Vb RP
      ∧ SimS (model := model) P f fn₀ R₀ st sPost.fn RP stb := by
  let RP := RB.setMany postParams vals
  have hleP : Regs.Le RB RP := Regs.Le.setMany hnd hnone
  have hbelowP : Regs.BelowEq base RB RP :=
    Regs.BelowEq.setMany hbase
  have hfrP : RegsFresh RP sPost.fn := by
    intro i hi
    dsimp [RP]
    rw [Regs.setMany_other]
    · exact hfr i (Nat.le_trans hnext hi)
    · intro him
      exact absurd (hparamsLt i him)
        (Nat.not_lt_of_ge (Nat.le_trans hnext hi))
  have hpget : RP.getMany postParams = some vals :=
    Regs.getMany_setMany_self hnd hlen
  have henvP : EnvOK (model := model) (env.setMany X postParams) Vb RP := by
    have he : EnvOK (model := model) (env.setMany X postParams)
        (YulSemantics.VEnv.setMany V X vals) RP :=
      EnvOK.setMany (henv.mono (hle.trans hleP))
        (Regs.getMany_eq_some_iff.mp hpget)
    rwa [hV] at he
  have hsimP : SimS (model := model) P f fn₀ R₀ st sPost.fn RP stb := by
    intro res hex
    apply hcont res
    apply jumpTo_of_completes hcompl hpb hcur hcur0
    · rw [hpp]
      exact hlen
    · simpa only [RP, hpp] using hex
  exact ⟨RP, hle.trans hleP, hbelow.trans hbelowP, hfrP, henvP, hsimP⟩

omit model in
/-- Backward reconstruction at the output of the loop post fragment.  The
overall loop builder always leaves the post block by moving to the protected
exit block.  If the post diverts, that move directly makes its sealed current
block final; if it falls through, the generated back edge seals it first. -/
theorem loopPost_back {f : Func} {fenv : FMap} {env : VMap}
    {rets : Option (List Ident)} {post : List (Stmt Op)} {X : List Ident}
    {hId exitId : BlockId} {sP sQ s₁ : BState}
    {postEnv : Option VMap} {renv : Option VMap} {outEnv : VMap}
    {joins : List BlockId}
    (hvalidQ : CurValid sQ)
    (hpQ : ProtectedAt (exitId :: joins) sQ.fn)
    (hpost : trScope fenv env none rets post sP = some (postEnv, sQ))
    (htail : (do
      if let some envP := postEnv then
        let xvP ← edgeArgs envP X
        sealCur (.jump ⟨hId, xvP⟩)
      moveTo exitId
      pure (some outEnv)) sQ = some (renv, s₁))
    (hcompl : Completes f s₁.fn joins) :
    Completes f sQ.fn (exitId :: joins) ∧
      CurPlaced f sQ.fn ∧ (postEnv = none → CurFinal f sQ.fn) := by
  cases postEnv with
  | none =>
    change (do
      moveTo exitId
      pure (some outEnv)) sQ = some (renv, s₁) at htail
    obtain ⟨uR, sR, hmove, htail⟩ := M.bind_inv htail
    obtain ⟨-, hs₁⟩ := M.pure_inv htail
    subst s₁
    have hcR : Completes f sR.fn (exitId :: joins) := hcompl.protect exitId
    have hcQ : Completes f sQ.fn (exitId :: joins) :=
      Completes.of_moveTo_protected (by simp) hmove hcR
    have hne : sQ.fn.curId ≠ exitId := fun he => hpQ.away (by simp [he])
    have hcur0 : sQ.fn.cur = [] :=
      trScope_none_cur_nil fenv env none rets post sP sQ hpost
    have hfin : CurFinal f sQ.fn :=
      curFinal_of_move_grows hmove hne hpQ.away (SGrows.rfl' sR) hcR
    exact ⟨hcQ,
      CurPlaced.of_moveTo_empty hvalidQ hcur0 hne hmove hpQ.away hcR,
      fun _ => hfin⟩
  | some envP =>
    obtain ⟨xvP, sR, hargs, htail⟩ := M.bind_inv htail
    obtain ⟨uS, sS, hseal, htail⟩ := M.bind_inv htail
    obtain ⟨uT, sT, hmove, htail⟩ := M.bind_inv htail
    obtain ⟨-, hs₁⟩ := M.pure_inv htail
    subst s₁
    have gQS : SGrows sQ sS :=
      (SGrowsAt.of_grows (Grows.of_liftO hargs)).trans
        (SGrowsAt.of_sealCur hseal)
    have hpS : ProtectedAt (exitId :: joins) sS.fn :=
      ProtectedAt.forward hpQ gQS
    have hcT : Completes f sT.fn (exitId :: joins) := hcompl.protect exitId
    have hcS : Completes f sS.fn (exitId :: joins) :=
      Completes.of_moveTo_protected (by simp) hmove hcT
    have hne : sS.fn.curId ≠ exitId := fun he => hpS.away (by simp [he])
    have hfinS : CurFinal f sS.fn :=
      curFinal_of_move_grows hmove hne hpS.away (SGrows.rfl' sT) hcT
    have hplacedR : CurPlaced f sR.fn :=
      ⟨_, curOK_of_sealCur hfinS hseal⟩
    have hsR : sR = sQ := (M.edgeArgs_inv hargs).2
    subst sR
    exact ⟨SGrowsAt.completes_of gQS hcS, hplacedR, fun h => nomatch h⟩

end Semantics
end YulEvmCompiler.SsaCfg
