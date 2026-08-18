import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.CallSim
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.OfYulSound.CondSim

The conditional and switch-halt statement cases of `sim`.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics (Ident Literal Expr Stmt VEnv Outcome)
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal evmWithExternal)

section Semantics
variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates YulSemantics.EVM.ExternalGas.any


/-- The static growth chain of the one generated conditional layout: what the
condition, the branch and the body-block move guarantee between the statement
entry `s₀` and the body fragment `sG`/`sH`.  Shared by the three `cond`
clauses of `sim`. -/
structure IfGrowth (s₀ sA sB sC sD sE sF sG sH : BState)
    (bodyId joinId : BlockId) : Prop where
  /-- Evaluating the condition only grows the state. -/
  g0A : Grows s₀ sA
  /-- The condition ends in a valid current block. -/
  hvalidA : CurValid sA
  /-- The join edge arguments only grow the state. -/
  gAB : Grows sA sB
  /-- Reserving the join parameters only grows the state. -/
  gCD : Grows sC sD
  /-- Growth from the condition past the join edge arguments. -/
  aAB : SGrowsAt sA.fn.blocks.size sA sB
  /-- Growth from the condition past the body block. -/
  aAC : SGrowsAt sA.fn.blocks.size sA sC
  /-- Growth from the condition past the join parameters. -/
  aAD : SGrowsAt sA.fn.blocks.size sA sD
  /-- Growth from the condition past the join block. -/
  aAE : SGrowsAt sA.fn.blocks.size sA sE
  /-- Growth from the condition past the branch. -/
  aAF : SGrowsAt sA.fn.blocks.size sA sF
  /-- Growth from the condition to the body block. -/
  aAG : SGrowsAt sA.fn.blocks.size sA sG
  /-- The body block is reserved at or after the condition. -/
  hbodyBase : sA.fn.blocks.size ≤ bodyId
  /-- So is the join block. -/
  hjoinBase : sA.fn.blocks.size ≤ joinId
  /-- Laying out the two blocks does not move the current block. -/
  csAE : CurSame sA sE
  /-- The branch is sealed away from the body block. -/
  hbodyNe : sE.fn.curId ≠ bodyId
  /-- The two reserved blocks are distinct. -/
  hjoinBody : joinId ≠ bodyId
  /-- The body block is a valid current block. -/
  hvalidG : CurValid sG
  /-- The body fragment only grows the state. -/
  gbody : SGrows sG sH

omit model in
/-- Read the conditional growth chain off the builder steps. -/
theorem ifGrowth {fenv : FMap} {env : VMap} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {c : Expr Op} {body : List (Stmt Op)}
    {s₀ sA sB sC sD sE sF sG sH : BState} {cvId : ValId}
    {xvals joinParams : List ValId} {bodyId joinId : BlockId}
    {bodyEnv : Option VMap}
    (hvalid : CurValid s₀)
    (h1 : trExpr fenv env c s₀ = some (cvId, sA))
    (h2 : edgeArgs env (modifiedX env [body]) sA = some (xvals, sB))
    (h3 : newBlock [] sB = some (bodyId, sC))
    (h4 : (modifiedX env [body]).mapM (fun _ => freshVal) sC =
      some (joinParams, sD))
    (h5 : newBlock joinParams sD = some (joinId, sE))
    (h6 : sealCur (.branch cvId ⟨bodyId, []⟩ ⟨joinId, xvals⟩) sE =
      some ((), sF))
    (h7 : moveTo bodyId sF = some ((), sG))
    (h8 : trScope fenv env lctx rets body sG = some (bodyEnv, sH)) :
    IfGrowth s₀ sA sB sC sD sE sF sG sH bodyId joinId := by
  have g0A : Grows s₀ sA := trExpr_grows c fenv env s₀ sA cvId h1
  have hvalidA : CurValid sA := hvalid.of_grows g0A
  have gAB : Grows sA sB := Grows.of_liftO h2
  have gCD : Grows sC sD := Grows.of_mapM_freshVal h4
  have aAB : SGrowsAt sA.fn.blocks.size sA sB := SGrowsAt.of_grows gAB
  have aAC := SGrowsAt.trans aAB
    (SGrowsAt.of_newBlock (N := sA.fn.blocks.size) h3)
  have aAD := SGrowsAt.trans aAC
    (SGrowsAt.of_grows (N := sA.fn.blocks.size) gCD)
  have aAE := SGrowsAt.trans aAD
    (SGrowsAt.of_newBlock (N := sA.fn.blocks.size) h5)
  have aAF := SGrowsAt.trans aAE
    (SGrowsAt.of_sealCur (N := sA.fn.blocks.size) h6)
  have hbodyBase : sA.fn.blocks.size ≤ bodyId := by
    rw [SGrowsAt.newBlock_id h3]
    exact aAB.size
  have hjoinBase : sA.fn.blocks.size ≤ joinId := by
    rw [SGrowsAt.newBlock_id h5]
    exact aAD.size
  have aAG := SGrowsAt.trans aAF
    (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hbodyBase) h7)
  have csAE : CurSame sA sE :=
    (((CurSame.of_grows gAB).trans (CurSame.of_newBlock h3)).trans
      (CurSame.of_grows gCD)).trans (CurSame.of_newBlock h5)
  have hbodyNe : sE.fn.curId ≠ bodyId := by
    rw [csAE.1, SGrowsAt.newBlock_id h3]
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hvalidA aAB.size)
  have hjoinBody : joinId ≠ bodyId := by
    rw [SGrowsAt.newBlock_id h5]
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (newBlock_target_lt h3)
      (SGrowsAt.of_grows (N := sC.fn.blocks.size) gCD).size)
  have hvalidG : CurValid sG := by
    apply CurValid.of_moveTo _ h7
    exact Nat.lt_of_lt_of_le (newBlock_target_lt h3)
      (((SGrowsAt.of_grows (N := sC.fn.blocks.size) gCD).trans
        (SGrowsAt.of_newBlock h5)).trans (SGrowsAt.of_sealCur h6)).size
  have gbody : SGrows sG sH :=
    trScope_grows fenv env lctx rets body sG bodyEnv sH h8
  exact ⟨g0A, hvalidA, gAB, gCD, aAB, aAC, aAD, aAE, aAF, aAG,
    hbodyBase, hjoinBase, csAE, hbodyNe, hjoinBody, hvalidG, gbody⟩

set_option maxHeartbeats 1000000 in
/-- **A conditional whose test is nonzero.**  The branch takes the body edge;
the body's outcome is the statement's outcome. -/
theorem sim_ifTrue {P : Prog} {f : Func} {funs : YulSemantics.FunEnv yulD}
    {V V' : VEnv yulD} {st st1 st2 : EvmState} {c : Expr Op}
    {body : List (Stmt Op)} {cv : U256} {o : Outcome}
    {doneFuncs : Array (Option Func)}
    {hfuncs : FuncTableComplete P doneFuncs}
    (hnz : cv ≠ YulSemantics.Dialect.zero yulD)
    (hbody : YulSemantics.Step yulD funs V st1 (.stmt (.block body))
      (.sres V' st2 o))
    (ihc : Motive (model := model) P f funs V st doneFuncs hfuncs
      (.expr c) (.eres (.vals [cv] st1)))
    (ihb : Motive (model := model) P f funs V st1 doneFuncs hfuncs
      (.stmt (.block body)) (.sres V' st2 o)) :
    Motive (model := model) P f funs V st doneFuncs hfuncs
      (.stmt (.cond c body)) (.sres V' st2 o) := by
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq hctx hfr hvalid
      hp hcompl hcp _ done owned hdone hbound hown htr
    rw [trStmt] at htr
    obtain ⟨cvId, sA, h1, htr⟩ := M.bind_inv htr
    obtain ⟨xvals, sB, h2, htr⟩ := M.bind_inv htr
    obtain ⟨bodyId, sC, h3, htr⟩ := M.bind_inv htr
    obtain ⟨joinParams, sD, h4, htr⟩ := M.bind_inv htr
    obtain ⟨joinId, sE, h5, htr⟩ := M.bind_inv htr
    obtain ⟨uF, sF, h6, htr⟩ := M.bind_inv htr
    obtain ⟨uG, sG, h7, htr⟩ := M.bind_inv htr
    obtain ⟨bodyEnv, sH, h8, htr⟩ := M.bind_inv htr
    obtain ⟨g0A, hvalidA, gAB, gCD, aAB, aAC, aAD, aAE, aAF, aAG,
      hbodyBase, hjoinBase, csAE, hbodyNe, hjoinBody, hvalidG, gbody⟩ :=
      ifGrowth hvalid h1 h2 h3 h4 h5 h6 h7 h8
    have hpA : ProtectedAt joins sA.fn :=
      ProtectedAt.forward hp (SGrows.of_grows g0A)
    have hpG0 : ProtectedAt joins sG.fn :=
      ProtectedAt.forward hpA aAG
    have hpG : ProtectedAt (joinId :: joins) sG.fn := by
      refine ⟨?_, ?_⟩
      · intro i hi
        simp only [List.mem_cons] at hi
        rcases hi with rfl | hi
        · exact Nat.lt_of_lt_of_le (newBlock_target_lt h5)
            ((SGrowsAt.of_sealCur (N := 0) h6).trans
              (SGrowsAt.of_moveTo (N := 0)
                (Or.inl (Nat.zero_le _)) h7)).size
        · exact hpG0.below i hi
      · simp only [List.mem_cons, not_or]
        exact ⟨by
          rw [M.moveTo_apply] at h7
          have hc := congrArg (fun z => z.fn.curId) (M.some_pair_inj h7).2
          simpa only using hc ▸ hjoinBody.symm, hpG0.away⟩
    have hpH : ProtectedAt (joinId :: joins) sH.fn :=
      ProtectedAt.forward hpG gbody
    cases bodyEnv with
    | none =>
      obtain ⟨ub, sb, hb, hc'⟩ := M.bind_inv htr
      obtain ⟨hrenv, hs₁⟩ := M.pure_inv hc'
      subst sb
      have htail : SGrowsAt sA.fn.blocks.size sH s₁ :=
        SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hjoinBase) hb
      have hcomplH : Completes f sH.fn (joinId :: joins) :=
        Completes.of_moveTo_protected (by simp) hb (hcompl.protect joinId)
      have hcurH0 : sH.fn.cur = [] :=
        trScope_none_cur_nil fenv env lctx rets body sG sH h8
      have h8' : trStmt fenv env lctx rets (.block body) sG = some (none, sH) := by
        rw [trStmt]
        exact h8
      have hvalidH : CurValid sH :=
        (trStmt_cur hvalidG h8').1
      have hHjoin : sH.fn.curId ≠ joinId := fun he =>
        hpH.away (by simp [he])
      have hfinH : CurFinal f sH.fn :=
        curFinal_of_move_grows hb hHjoin hpH.away (SGrows.rfl' s₁)
          (hcompl.protect joinId)
      have hcpH : CurPlaced f sH.fn :=
        CurPlaced.of_moveTo_empty hvalidH hcurH0 hHjoin hb hpH.away
          (hcompl.protect joinId)
      have gCH : SGrowsAt 0 sC sH :=
        (((((SGrowsAt.of_grows gCD).trans (SGrowsAt.of_newBlock h5)).trans
          (SGrowsAt.of_sealCur h6)).trans
            (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h7)).trans
              (gbody.mono (Nat.zero_le _)))
      obtain ⟨bb, hbb, hbp⟩ := gCH.params bodyId ⟨[], [], .ret []⟩
        (newBlock_target_get h3)
      have hcurFE : sF.fn.curId = sE.fn.curId := (sealCur_cur h6).choose_spec.1
      have hfinalF : CurFinal f sF.fn :=
        curFinal_of_move_sgrowsAt (by rw [hcurFE, csAE.1]; exact hvalidA)
          h7 (by rw [hcurFE]; exact hbodyNe)
          (by rw [hcurFE, csAE.1]; exact hpA.away)
          (SGrowsAt.trans (gbody.mono aAG.size)
            htail) hcompl
      have hbranchE : CurOK f sE.fn
          ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨joinId, xvals⟩⟩ :=
        curOK_of_sealCur hfinalF h6
      have hcurAE : sE.fn.cur = sA.fn.cur := by
        have hBA : sB = sA := (M.edgeArgs_inv h2).2
        have hCB : sC.fn.cur = sB.fn.cur := by
          rw [M.newBlock_apply] at h3
          simpa using (congrArg (fun z => z.fn.cur) (M.some_pair_inj h3).2).symm
        have hDC : sD.fn.cur = sC.fn.cur := by
          obtain ⟨-, -, hsD⟩ := M.mapM_freshVal_length h4
          rw [hsD]
        have hED : sE.fn.cur = sD.fn.cur := by
          rw [M.newBlock_apply] at h5
          simpa using (congrArg (fun z => z.fn.cur) (M.some_pair_inj h5).2).symm
        rw [hED, hDC, hCB, hBA]
      have hbranch : CurOK f sA.fn
          ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨joinId, xvals⟩⟩ :=
        CurOK.back_of_cur_eq csAE.1 hcurAE hbranchE
      have hcpA : CurPlaced f sA.fn := ⟨_, hbranch⟩
      have hcomplA : Completes f sA.fn joins := SGrowsAt.completes_of
        (SGrowsAt.trans aAG (SGrowsAt.trans
          (gbody.mono aAG.size)
          htail)) hcompl
      obtain ⟨RA, hleA, hbelowA, hfrA, hcv, hsimC⟩ :=
        ihc.1 fenv env R s₀ sA cvId cv joins hfe henv hfr hp hcomplA hcpA rfl h1
      have hfrG : RegsFresh RA sG.fn := hfrA.mono aAG.nextVal
      have hnz' : cv ≠ 0 := by simpa only [yulD_zero] using hnz
      have hcurG : sG.fn.curId = bodyId := by
        rw [M.moveTo_apply] at h7
        exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h7).2).symm
      have hcurG0 : sG.fn.cur = [] := by
        rw [M.moveTo_apply] at h7
        simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h7).2
      have hsimB := simS_branchTrue_body (model := model) (P := P) (f := f)
        (st := st1)
        hcomplH hbranch hcv hnz' hbb hbp hcurG hcurG0
      have hboundG : ∀ i : FuncId, i ∈ owned → i < sG.funcs.size := by
        intro i hi
        exact Nat.lt_of_lt_of_le (hbound i hi)
          (Nat.le_trans (SGrows.of_grows g0A).funcsSize aAG.funcsSize)
      have hboundH : ∀ i : FuncId, i ∈ owned → i < sH.funcs.size := by
        intro i hi
        exact Nat.lt_of_lt_of_le (hboundG i hi) gbody.funcsSize
      have hownH : FOwned owned sH done :=
        FOwned.back_fprefix (FPrefix.of_moveTo hb) hboundH hown
      have hbodySim := ihb fenv env RA lctx rets sG sH none (joinId :: joins)
        hfe (henv.mono hleA) huniq hctx hfrG hvalidG hpG hcomplH hcpH
        (fun _ => hfinH) done owned hdone hboundG hownH h8'
      have hpre := hsimC.trans hsimB
      have hnext : sH.fn.nextVal ≤ s₁.fn.nextVal := by
        rw [M.moveTo_apply] at hb
        rw [(congrArg (fun z => z.fn.nextVal) (M.some_pair_inj hb).2).symm]
      cases o with
      | normal =>
        obtain ⟨env', R', hbad, -⟩ := hbodySim
        exact absurd hbad (by simp)
      | halt =>
        exact SOut.prefix hleA hbelowA
          (Nat.le_trans g0A.nextVal aAG.nextVal) hpre
          (SOut.of_nonNormal (by simp) hnext hbodySim)
      | «break» =>
        exact SOut.prefix hleA hbelowA
          (Nat.le_trans g0A.nextVal aAG.nextVal) hpre
          (SOut.of_nonNormal (by simp) hnext hbodySim)
      | «continue» =>
        exact SOut.prefix hleA hbelowA
          (Nat.le_trans g0A.nextVal aAG.nextVal) hpre
          (SOut.of_nonNormal (by simp) hnext hbodySim)
      | leave =>
        exact SOut.prefix hleA hbelowA
          (Nat.le_trans g0A.nextVal aAG.nextVal) hpre
          (SOut.of_nonNormal (by simp) hnext hbodySim)
    | some envB =>
      obtain ⟨xvB, sI, h9, htr⟩ := M.bind_inv htr
      obtain ⟨uJ, sJ, h10, htr⟩ := M.bind_inv htr
      obtain ⟨uK, sK, h11, htr⟩ := M.bind_inv htr
      obtain ⟨hrenv, hs₁⟩ := M.pure_inv htr
      subst sK
      have gHI : Grows sH sI := Grows.of_liftO h9
      have aHJ : SGrowsAt sA.fn.blocks.size sH sJ :=
        SGrowsAt.trans (SGrowsAt.of_grows gHI)
          (SGrowsAt.of_sealCur (N := sA.fn.blocks.size) h10)
      have aHJlocal : SGrows sH sJ :=
        SGrowsAt.trans (SGrowsAt.of_grows gHI) (SGrowsAt.of_sealCur h10)
      have htail : SGrowsAt sA.fn.blocks.size sH s₁ :=
        SGrowsAt.trans aHJ
          (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hjoinBase) h11)
      have hcomplJ : Completes f sJ.fn (joinId :: joins) :=
        Completes.of_moveTo_protected (by simp) h11 (hcompl.protect joinId)
      have hcomplH : Completes f sH.fn (joinId :: joins) :=
        SGrowsAt.completes_of aHJlocal hcomplJ
      have h8' : trStmt fenv env lctx rets (.block body) sG = some (some envB, sH) := by
        rw [trStmt]
        exact h8
      have hvalidH : CurValid sH := (trStmt_cur hvalidG h8').1
      have hjoinH : sH.fn.curId ≠ joinId := fun he => hpH.away (by simp [he])
      have hcurIH : sI.fn.curId = sH.fn.curId := gHI.curId.symm
      have hjoinI : sI.fn.curId ≠ joinId := by simpa only [hcurIH] using hjoinH
      have hcurJI : sJ.fn.curId = sI.fn.curId := (sealCur_cur h10).choose_spec.1
      have hjoinJ : sJ.fn.curId ≠ joinId := by simpa only [hcurJI] using hjoinI
      have hpJ : ProtectedAt (joinId :: joins) sJ.fn :=
        ProtectedAt.forward hpH aHJlocal
      have hfinJ : CurFinal f sJ.fn :=
        curFinal_of_move_grows h11 hjoinJ hpJ.away (SGrows.rfl' s₁)
          (hcompl.protect joinId)
      have hsealI : CurOK f sI.fn ⟨[], .jump ⟨joinId, xvB⟩⟩ :=
        curOK_of_sealCur hfinJ h10
      have hcurHI : sI.fn.cur = sH.fn.cur := by
        obtain ⟨Δ, he⟩ := gHI.cur
        have hEq : sI = sH := (M.edgeArgs_inv h9).2
        simp only [hEq]
      have hsealH : CurOK f sH.fn ⟨[], .jump ⟨joinId, xvB⟩⟩ :=
        CurOK.back_of_cur_eq gHI.curId.symm hcurHI hsealI
      have hcpH : CurPlaced f sH.fn := ⟨_, hsealH⟩
      have hcurAE : sE.fn.cur = sA.fn.cur := by
        have hBA : sB = sA := (M.edgeArgs_inv h2).2
        have hCB : sC.fn.cur = sB.fn.cur := by
          rw [M.newBlock_apply] at h3
          simpa using (congrArg (fun z => z.fn.cur) (M.some_pair_inj h3).2).symm
        have hDC : sD.fn.cur = sC.fn.cur := by
          obtain ⟨-, -, hsD⟩ := M.mapM_freshVal_length h4
          rw [hsD]
        have hED : sE.fn.cur = sD.fn.cur := by
          rw [M.newBlock_apply] at h5
          simpa using (congrArg (fun z => z.fn.cur) (M.some_pair_inj h5).2).symm
        rw [hED, hDC, hCB, hBA]
      have hbranchE : CurOK f sE.fn
          ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨joinId, xvals⟩⟩ := by
        have hcurFE : sF.fn.curId = sE.fn.curId := (sealCur_cur h6).choose_spec.1
        have hfinalF : CurFinal f sF.fn :=
          curFinal_of_move_sgrowsAt (by rw [hcurFE, csAE.1]; exact hvalidA)
            h7 (by rw [hcurFE]; exact hbodyNe)
            (by rw [hcurFE, csAE.1]; exact hpA.away)
            (SGrowsAt.trans (gbody.mono aAG.size) htail) hcompl
        exact curOK_of_sealCur hfinalF h6
      have hbranch : CurOK f sA.fn
          ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨joinId, xvals⟩⟩ :=
        CurOK.back_of_cur_eq csAE.1 hcurAE hbranchE
      have gCH : SGrowsAt 0 sC sH :=
        (((((SGrowsAt.of_grows gCD).trans (SGrowsAt.of_newBlock h5)).trans
          (SGrowsAt.of_sealCur h6)).trans
            (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h7)).trans
              (gbody.mono (Nat.zero_le _)))
      obtain ⟨bb, hbb, hbp⟩ := gCH.params bodyId ⟨[], [], .ret []⟩
        (newBlock_target_get h3)
      have hcomplA : Completes f sA.fn joins := SGrowsAt.completes_of
        (SGrowsAt.trans aAG (SGrowsAt.trans
          (gbody.mono aAG.size) htail)) hcompl
      have hcpA : CurPlaced f sA.fn := ⟨_, hbranch⟩
      obtain ⟨RA, hleA, hbelowA, hfrA, hcv, hsimC⟩ :=
        ihc.1 fenv env R s₀ sA cvId cv joins hfe henv hfr hp hcomplA hcpA rfl h1
      have hfrG : RegsFresh RA sG.fn := hfrA.mono aAG.nextVal
      have hnz' : cv ≠ 0 := by simpa only [yulD_zero] using hnz
      have hcurG : sG.fn.curId = bodyId := by
        rw [M.moveTo_apply] at h7
        exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h7).2).symm
      have hcurG0 : sG.fn.cur = [] := by
        rw [M.moveTo_apply] at h7
        simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h7).2
      have hsimB := simS_branchTrue_body (model := model) (P := P) (f := f)
        (st := st1) hcomplH hbranch hcv hnz' hbb hbp hcurG hcurG0
      have hboundG : ∀ i : FuncId, i ∈ owned → i < sG.funcs.size := by
        intro i hi
        exact Nat.lt_of_lt_of_le (hbound i hi)
          (Nat.le_trans (SGrows.of_grows g0A).funcsSize aAG.funcsSize)
      have hboundH : ∀ i : FuncId, i ∈ owned → i < sH.funcs.size := by
        intro i hi
        exact Nat.lt_of_lt_of_le (hboundG i hi) gbody.funcsSize
      have hownH : FOwned owned sH done := FOwned.back_fprefix
        (((FPrefix.of_edgeArgs h9).trans (FPrefix.of_sealCur h10)).trans
          (FPrefix.of_moveTo h11)) hboundH hown
      have hbodySim := ihb fenv env RA lctx rets sG sH (some envB)
        (joinId :: joins) hfe (henv.mono hleA) huniq hctx hfrG hvalidG hpG
        hcomplH hcpH (by simp) done owned hdone hboundG hownH h8'
      have hpre := hsimC.trans hsimB
      cases o with
      | halt =>
        exact SOut.prefix hleA hbelowA
          (Nat.le_trans g0A.nextVal aAG.nextVal) hpre
          (SOut.of_nonNormal (by simp) htail.nextVal hbodySim)
      | «break» =>
        exact SOut.prefix hleA hbelowA
          (Nat.le_trans g0A.nextVal aAG.nextVal) hpre
          (SOut.of_nonNormal (by simp) htail.nextVal hbodySim)
      | «continue» =>
        exact SOut.prefix hleA hbelowA
          (Nat.le_trans g0A.nextVal aAG.nextVal) hpre
          (SOut.of_nonNormal (by simp) htail.nextVal hbodySim)
      | leave =>
        exact SOut.prefix hleA hbelowA
          (Nat.le_trans g0A.nextVal aAG.nextVal) hpre
          (SOut.of_nonNormal (by simp) htail.nextVal hbodySim)
      | normal =>
        obtain ⟨envB', RB, henvB', hleB, hbelowB, hfrB, henvB, huniqB,
          hsimBody⟩ := hbodySim
        obtain rfl : envB' = envB := (Option.some.inj henvB').symm
        obtain ⟨rfl, vals, hxget, hxvals⟩ := edgeArgs_ok henvB h9
        obtain ⟨hparamLen, hparamRange, hsD⟩ := M.mapM_freshVal_length h4
        have hnd : joinParams.Nodup := by
          rw [hparamRange]
          exact M.nodup_range' _ _
        have hfrC : RegsFresh RA sC.fn := hfrA.mono aAC.nextVal
        have aDG : SGrowsAt 0 sD sG :=
          (SGrowsAt.of_newBlock (N := 0) h5).trans
            ((SGrowsAt.of_sealCur (N := 0) h6).trans
              (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h7))
        have hparamsLt : ∀ i ∈ joinParams, i < sG.fn.nextVal := by
          intro i hi
          rw [hparamRange] at hi
          have hi' := (M.mem_range'_bounds hi).2
          have hiD : i < sD.fn.nextVal := by rw [hsD]; exact hi'
          exact Nat.lt_of_lt_of_le hiD aDG.nextVal
        have hnone : ∀ i ∈ joinParams, RB i = none := by
          intro i hi
          rw [hbelowB i (hparamsLt i hi)]
          exact hfrC i (by
            rw [hparamRange] at hi
            exact (M.mem_range'_bounds hi).1)
        have hleJ : Regs.Le RB (RB.setMany joinParams vals) :=
          Regs.Le.setMany hnd hnone
        have hbelowJ : Regs.BelowEq s₀.fn.nextVal RB
            (RB.setMany joinParams vals) := by
          apply Regs.BelowEq.setMany
          intro i hi
          rw [hparamRange] at hi
          exact Nat.le_trans g0A.nextVal
            (Nat.le_trans aAC.nextVal (M.mem_range'_bounds hi).1)
        have hfrJ : RegsFresh (RB.setMany joinParams vals) s₁.fn := by
          intro i hi
          rw [Regs.setMany_other]
          · exact hfrB i (Nat.le_trans htail.nextVal hi)
          · intro himem
            exact absurd (hparamsLt i himem)
              (Nat.not_lt_of_ge
                (Nat.le_trans (Nat.le_trans gbody.nextVal htail.nextVal) hi))
        have hnew := newBlock_target_get h5
        have hE1 : SGrowsAt sA.fn.blocks.size sE s₁ :=
          SGrowsAt.trans (SGrowsAt.of_sealCur (N := sA.fn.blocks.size) h6)
            (SGrowsAt.trans
              (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hbodyBase) h7)
              (SGrowsAt.trans (gbody.mono aAG.size) htail))
        obtain ⟨jb, hjb, hjp⟩ := hE1.params joinId
          ⟨joinParams, [], .ret []⟩ hnew
        have hcur : s₁.fn.curId = joinId := by
          rw [M.moveTo_apply] at h11
          exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h11).2).symm
        have hcur0 : s₁.fn.cur = [] := by
          rw [M.moveTo_apply] at h11
          simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h11).2
        have hjbLen : jb.params.length = vals.length := by
          rw [hjp, hparamLen]
          exact hxvals.length_eq
        have hsimJ : SimS (model := model) P f sI.fn RB st2 s₁.fn
            (RB.setMany joinParams vals) st2 := by
          have hs := simS_jump_join (model := model) (P := P) (f := f)
            (st := st2) hcompl hsealH hjb hcur hcur0 hxget hjbLen
          simpa only [hjp] using hs
        have hnames : VEnv.names V' = VEnv.names V := by
          have hm := (mod_sim hbody).1
          simpa [declsOfStmt] using hm
        have hmod : ModOut [] (modStmts [] body) V V' := by
          have hm := (mod_sim hbody).2 [] (localsOK_nil V)
          simpa [modStmt] using hm
        have hVjoin : YulSemantics.VEnv.setMany V
            (modifiedX env [body]) vals = V' :=
          setMany_eq_of_modOut henv huniq hnames hmod hxvals
            (fun x hx => modifiedX_mem_names hx)
            (fun x hx hm => mem_modifiedX hx (by simpa using hm))
        have hpget : (RB.setMany joinParams vals).getMany joinParams = some vals :=
          Regs.getMany_setMany_self hnd (by rw [hparamLen]; exact hxvals.length_eq)
        have henvJ : EnvOK (model := model)
            (env.setMany (modifiedX env [body]) joinParams) V'
            (RB.setMany joinParams vals) := by
          have he : EnvOK (model := model)
              (env.setMany (modifiedX env [body]) joinParams)
              (YulSemantics.VEnv.setMany V (modifiedX env [body]) vals)
              (RB.setMany joinParams vals) :=
            EnvOK.setMany (henv.mono (hleA.trans (hleB.trans hleJ)))
              (Regs.getMany_eq_some_iff.mp hpget)
          rwa [hVjoin] at he
        exact ⟨env.setMany (modifiedX env [body]) joinParams,
          RB.setMany joinParams vals, hrenv, hleA.trans (hleB.trans hleJ),
          (hbelowA.trans
            (hbelowB.mono (Nat.le_trans g0A.nextVal aAG.nextVal))).trans hbelowJ,
          hfrJ, henvJ, huniq.setMany _ _,
          hpre.trans (hsimBody.trans hsimJ)⟩

set_option maxHeartbeats 1000000 in
/-- **A conditional whose test is zero.**  The branch takes the join edge and
the body block is never entered. -/
theorem sim_ifFalse {P : Prog} {f : Func} {funs : YulSemantics.FunEnv yulD}
    {V : VEnv yulD} {st st1 : EvmState} {c : Expr Op}
    {body : List (Stmt Op)} {cv : U256} {doneFuncs : Array (Option Func)}
    {hfuncs : FuncTableComplete P doneFuncs}
    (hz : cv = YulSemantics.Dialect.zero yulD)
    (ihc : Motive (model := model) P f funs V st doneFuncs hfuncs
      (.expr c) (.eres (.vals [cv] st1))) :
    Motive (model := model) P f funs V st doneFuncs hfuncs
      (.stmt (.cond c body)) (.sres V st1 .normal) := by
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq hctx hfr hvalid
      hp hcompl hcp _ _done _owned _hdone _hbound _hown htr
    rw [trStmt] at htr
    obtain ⟨cvId, sA, h1, htr⟩ := M.bind_inv htr
    obtain ⟨xvals, sB, h2, htr⟩ := M.bind_inv htr
    obtain ⟨bodyId, sC, h3, htr⟩ := M.bind_inv htr
    obtain ⟨joinParams, sD, h4, htr⟩ := M.bind_inv htr
    obtain ⟨joinId, sE, h5, htr⟩ := M.bind_inv htr
    obtain ⟨uF, sF, h6, htr⟩ := M.bind_inv htr
    obtain ⟨uG, sG, h7, htr⟩ := M.bind_inv htr
    obtain ⟨bodyEnv, sH, h8, htr⟩ := M.bind_inv htr
    obtain ⟨g0A, hvalidA, gAB, gCD, aAB, aAC, aAD, aAE, aAF, aAG,
      hbodyBase, hjoinBase, csAE, hbodyNe, hjoinBody, hvalidG, gbody⟩ :=
      ifGrowth hvalid h1 h2 h3 h4 h5 h6 h7 h8
    have tailData : SGrowsAt sA.fn.blocks.size sG s₁
        ∧ s₁.fn.curId = joinId ∧ s₁.fn.cur = []
        ∧ renv = some (env.setMany (modifiedX env [body]) joinParams) := by
      cases bodyEnv with
      | none =>
        obtain ⟨ub, sb, hb, hc'⟩ := M.bind_inv htr
        obtain ⟨hrenv, hs₁⟩ := M.pure_inv hc'
        subst hs₁
        refine ⟨SGrowsAt.trans (gbody.mono
          (Nat.le_trans aAE.size
            ((SGrowsAt.of_sealCur (N := sA.fn.blocks.size) h6).trans
              (SGrowsAt.of_moveTo (N := sA.fn.blocks.size)
                (Or.inl hbodyBase) h7)).size))
            (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hjoinBase) hb),
          ?_, ?_, hrenv⟩
        · rw [M.moveTo_apply] at hb
          exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj hb).2).symm
        · rw [M.moveTo_apply] at hb
          simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj hb).2
      | some env' =>
        obtain ⟨xv, sa, ha, htr⟩ := M.bind_inv htr
        obtain ⟨ub, sb, hb, htr⟩ := M.bind_inv htr
        obtain ⟨uc, sc, hc', hd⟩ := M.bind_inv htr
        obtain ⟨hrenv, hs₁⟩ := M.pure_inv hd
        subst hs₁
        have abase : sA.fn.blocks.size ≤ sG.fn.blocks.size := by
          exact (SGrowsAt.trans aAE
            (SGrowsAt.trans (SGrowsAt.of_sealCur (N := sA.fn.blocks.size) h6)
              (SGrowsAt.of_moveTo (N := sA.fn.blocks.size)
                (Or.inl hbodyBase) h7))).size
        refine ⟨SGrowsAt.trans
          (SGrowsAt.trans
            (SGrowsAt.trans (gbody.mono abase)
              (SGrowsAt.of_edgeArgs (N := sA.fn.blocks.size) ha))
            (SGrowsAt.of_sealCur (N := sA.fn.blocks.size) hb))
          (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hjoinBase) hc'),
          ?_, ?_, hrenv⟩
        · rw [M.moveTo_apply] at hc'
          exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj hc').2).symm
        · rw [M.moveTo_apply] at hc'
          simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj hc').2
    obtain ⟨gsuffix, hcur, hcur0, hrenv⟩ := tailData
    have hcurFE : sF.fn.curId = sE.fn.curId := (sealCur_cur h6).choose_spec.1
    have hfinalF : CurFinal f sF.fn :=
      curFinal_of_move_sgrowsAt (by rw [hcurFE, csAE.1]; exact hvalidA)
        h7 (by rw [hcurFE]; exact hbodyNe)
        (by rw [hcurFE, csAE.1]
            exact (ProtectedAt.forward hp (SGrows.of_grows g0A)).away)
        gsuffix hcompl
    have hbranchE : CurOK f sE.fn
        ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨joinId, xvals⟩⟩ :=
      curOK_of_sealCur hfinalF h6
    have hcurIdAE : sE.fn.curId = sA.fn.curId := csAE.1
    have hcurAE : sE.fn.cur = sA.fn.cur := by
      have hBA : sB = sA := (M.edgeArgs_inv h2).2
      have hCB : sC.fn.cur = sB.fn.cur := by
        rw [M.newBlock_apply] at h3
        simpa using (congrArg (fun z => z.fn.cur) (M.some_pair_inj h3).2).symm
      have hDC : sD.fn.cur = sC.fn.cur := by
        obtain ⟨-, -, hsD⟩ := M.mapM_freshVal_length h4
        rw [hsD]
      have hED : sE.fn.cur = sD.fn.cur := by
        rw [M.newBlock_apply] at h5
        simpa using (congrArg (fun z => z.fn.cur) (M.some_pair_inj h5).2).symm
      rw [hED, hDC, hCB, hBA]
    have hbranch : CurOK f sA.fn
        ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨joinId, xvals⟩⟩ :=
      CurOK.back_of_cur_eq hcurIdAE hcurAE hbranchE
    obtain ⟨RA, hleA, hbelowA, hfrA, hcv, hsimC⟩ :=
      ihc.1 fenv env R s₀ sA cvId cv joins hfe henv hfr hp
        (SGrowsAt.completes_of
          (SGrowsAt.trans aAE
            (SGrowsAt.trans (SGrowsAt.of_sealCur (N := sA.fn.blocks.size) h6)
              (SGrowsAt.trans
                (SGrowsAt.of_moveTo (N := sA.fn.blocks.size)
                  (Or.inl hbodyBase) h7) gsuffix))) hcompl)
        (csAE.placed_back ⟨_, hbranchE⟩) rfl h1
    obtain ⟨hsB, vals, hxget, hxvals⟩ := edgeArgs_ok (henv.mono hleA) h2
    have hparams := M.mapM_freshVal_length h4
    obtain ⟨hparamLen, hparamRange, hsD⟩ := hparams
    have hnd : joinParams.Nodup := by rw [hparamRange]; exact M.nodup_range' _ _
    have hfrC : RegsFresh RA sC.fn := hfrA.mono aAC.nextVal
    have hnone : ∀ i ∈ joinParams, RA i = none := by
      intro i hi
      rw [hparamRange] at hi
      exact hfrC i (M.mem_range'_bounds hi).1
    have hleJ : Regs.Le RA (RA.setMany joinParams vals) :=
      Regs.Le.setMany hnd hnone
    have hbelowJ : Regs.BelowEq sA.fn.nextVal RA
        (RA.setMany joinParams vals) := by
      apply Regs.BelowEq.setMany
      intro i hi
      rw [hparamRange] at hi
      exact Nat.le_trans aAC.nextVal (M.mem_range'_bounds hi).1
    have hD1 : SGrowsAt sA.fn.blocks.size sD s₁ :=
      SGrowsAt.trans (SGrowsAt.of_newBlock (N := sA.fn.blocks.size) h5)
        (SGrowsAt.trans (SGrowsAt.of_sealCur (N := sA.fn.blocks.size) h6)
          (SGrowsAt.trans
            (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hbodyBase) h7)
            gsuffix))
    have hnext : sC.fn.nextVal + (modifiedX env [body]).length ≤ s₁.fn.nextVal := by
      simpa [hsD] using hD1.nextVal
    have hfrJ : RegsFresh (RA.setMany joinParams vals) s₁.fn := by
      rw [hparamRange]
      exact hfrC.setMany hnext
    have hnew := newBlock_target_get h5
    have hE1 : SGrowsAt sA.fn.blocks.size sE s₁ :=
      SGrowsAt.trans (SGrowsAt.of_sealCur (N := sA.fn.blocks.size) h6)
        (SGrowsAt.trans
          (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hbodyBase) h7)
          gsuffix)
    obtain ⟨jb, hjb, hjp⟩ := hE1.params joinId
      ⟨joinParams, [], .ret []⟩ hnew
    have hvalsLen : (modifiedX env [body]).length = vals.length := hxvals.length_eq
    have hjbLen : jb.params.length = vals.length := by
      rw [hjp, hparamLen, hvalsLen]
    have hzero : RA cvId = some 0 := by
      rw [hz] at hcv
      simpa only [yulD_zero] using hcv
    have hsimJ : SimS (model := model) P f sA.fn RA st1 s₁.fn
        (RA.setMany joinParams vals) st1 := by
      have hs := simS_branchFalse_join (model := model) (P := P) (f := f)
        (st := st1) hcompl hbranch hzero hjb hcur hcur0 hxget hjbLen
      simpa only [hjp] using hs
    have henvJ : EnvOK (model := model)
        (env.setMany (modifiedX env [body]) joinParams) V
        (RA.setMany joinParams vals) := by
      have hpget : (RA.setMany joinParams vals).getMany joinParams = some vals :=
        Regs.getMany_setMany_self hnd (by rw [hparamLen]; exact hvalsLen)
      have he : EnvOK (model := model)
          (env.setMany (modifiedX env [body]) joinParams)
          (YulSemantics.VEnv.setMany V (modifiedX env [body]) vals)
          (RA.setMany joinParams vals) :=
        EnvOK.setMany (henv.mono (hleA.trans hleJ))
          (Regs.getMany_eq_some_iff.mp hpget)
      rw [VEnv.setMany_self hxvals] at he
      exact he
    exact ⟨env.setMany (modifiedX env [body]) joinParams,
      RA.setMany joinParams vals, hrenv, hleA.trans hleJ,
      hbelowA.trans (hbelowJ.mono g0A.nextVal), hfrJ, henvJ,
      huniq.setMany _ _, hsimC.trans hsimJ⟩

set_option maxHeartbeats 400000 in
/-- **A conditional whose test halts.**  Neither edge is taken. -/
theorem sim_ifHalt {P : Prog} {f : Func} {funs : YulSemantics.FunEnv yulD}
    {V : VEnv yulD} {st st1 : EvmState} {c : Expr Op}
    {body : List (Stmt Op)} {doneFuncs : Array (Option Func)}
    {hfuncs : FuncTableComplete P doneFuncs}
    (ihc : Motive (model := model) P f funs V st doneFuncs hfuncs
      (.expr c) (.eres (.halt st1))) :
    Motive (model := model) P f funs V st doneFuncs hfuncs
      (.stmt (.cond c body)) (.sres V st1 .halt) := by
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv _huniq hctx hfr
      hvalid hp hcompl hcp _ _done _owned _hdone _hbound _hown htr
    rw [trStmt] at htr
    obtain ⟨cv, sA, h1, htr⟩ := M.bind_inv htr
    obtain ⟨xvals, sB, h2, htr⟩ := M.bind_inv htr
    obtain ⟨bodyId, sC, h3, htr⟩ := M.bind_inv htr
    obtain ⟨joinParams, sD, h4, htr⟩ := M.bind_inv htr
    obtain ⟨joinId, sE, h5, htr⟩ := M.bind_inv htr
    obtain ⟨uF, sF, h6, htr⟩ := M.bind_inv htr
    obtain ⟨uG, sG, h7, htr⟩ := M.bind_inv htr
    obtain ⟨bodyEnv, sH, h8, htr⟩ := M.bind_inv htr
    obtain ⟨g0A, hvalidA, gAB, gCD, aAB, aAC, aAD, aAE, aAF, aAG,
      hbodyBase, hjoinBase, csAE, hbodyNe, hjoinBody, hvalidG, gbody⟩ :=
      ifGrowth hvalid h1 h2 h3 h4 h5 h6 h7 h8
    have gsuffix : SGrowsAt sA.fn.blocks.size sG s₁ := by
      cases bodyEnv with
      | none =>
        obtain ⟨ub, sb, hb, hc'⟩ := M.bind_inv htr
        obtain ⟨rfl, rfl⟩ := M.pure_inv hc'
        exact SGrowsAt.trans (gbody.mono aAG.size)
          (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hjoinBase) hb)
      | some env' =>
        obtain ⟨xv, sa, ha, htr⟩ := M.bind_inv htr
        obtain ⟨ub, sb, hb, htr⟩ := M.bind_inv htr
        obtain ⟨uc, sc, hc', hd⟩ := M.bind_inv htr
        obtain ⟨rfl, rfl⟩ := M.pure_inv hd
        exact SGrowsAt.trans (SGrowsAt.trans
          (SGrowsAt.trans (gbody.mono aAG.size)
            (SGrowsAt.of_edgeArgs (N := sA.fn.blocks.size) ha))
          (SGrowsAt.of_sealCur (N := sA.fn.blocks.size) hb))
            (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hjoinBase) hc')
    have hcurFE : sF.fn.curId = sE.fn.curId := (sealCur_cur h6).choose_spec.1
    have hfinalF : CurFinal f sF.fn :=
      curFinal_of_move_sgrowsAt (by rw [hcurFE, csAE.1]; exact hvalidA)
        h7 (by rw [hcurFE]; exact hbodyNe)
        (by rw [hcurFE, csAE.1]
            exact (ProtectedAt.forward hp (SGrows.of_grows g0A)).away)
        gsuffix hcompl
    have hcpE : CurPlaced f sE.fn :=
      ⟨⟨[], .branch cv ⟨bodyId, []⟩ ⟨joinId, xvals⟩⟩,
        curOK_of_sealCur hfinalF h6⟩
    have hcpA : CurPlaced f sA.fn := csAE.placed_back hcpE
    have hcomplA : Completes f sA.fn joins := SGrowsAt.completes_of
      (SGrowsAt.trans aAE
        (SGrowsAt.trans (SGrowsAt.of_sealCur (N := sA.fn.blocks.size) h6)
          (SGrowsAt.trans
            (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hbodyBase) h7)
            gsuffix))) hcompl
    exact SOut.ofExprHalt
      (ihc.1 fenv env R s₀ sA cv joins hfe henv hfr hp hcomplA hcpA h1)
  -- The dispatch chain is `trCases_sim`; `sim_switchExec` glues it to the
  -- scrutinee's `EOut` and to the reserved-join reconstruction.

set_option maxHeartbeats 400000 in
/-- **A switch whose scrutinee halts.**  The dispatch chain is never
entered. -/
theorem sim_switchHalt {P : Prog} {f : Func} {funs : YulSemantics.FunEnv yulD}
    {V : VEnv yulD} {st st1 : EvmState} {c : Expr Op}
    {cases : List (Literal × List (Stmt Op))}
    {dflt : Option (List (Stmt Op))} {doneFuncs : Array (Option Func)}
    {hfuncs : FuncTableComplete P doneFuncs}
    (ihc : Motive (model := model) P f funs V st doneFuncs hfuncs
      (.expr c) (.eres (.halt st1))) :
    Motive (model := model) P f funs V st doneFuncs hfuncs
      (.stmt (.switch c cases dflt)) (.sres V st1 .halt) := by
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv _huniq hctx hfr
      hvalid hp hcompl _hcp _ _done _owned _hdone _hbound _hown htr
    let X := modifiedX env (cases.map Prod.snd ++ dflt.toList)
    unfold trStmt at htr
    obtain ⟨sv, sA, h1, htr⟩ := M.bind_inv htr
    obtain ⟨joinParams, sB, h2, htr⟩ := M.bind_inv htr
    obtain ⟨joinId, sC, h3, htr⟩ := M.bind_inv htr
    obtain ⟨uD, sD, h4, htr⟩ := M.bind_inv htr
    obtain ⟨uE, sE, h5, h6⟩ := M.bind_inv htr
    obtain ⟨-, hs₁⟩ := M.pure_inv h6
    have hXE := congrArg (modifiedX env) (switchBodies_eq cases dflt)
    have h2X : X.mapM (fun _ => freshVal) sA = some (joinParams, sB) := by
      exact Eq.mp (congrArg
        (fun X' => X'.mapM (fun _ => freshVal) sA = some (joinParams, sB)) hXE) h2
    have h4X : trCases fenv env lctx rets sv X joinId cases dflt sC =
        some (uD, sD) := by
      exact Eq.mp (congrArg (fun X' =>
        trCases fenv env lctx rets sv X' joinId cases dflt sC = some (uD, sD)) hXE) h4
    have hcomplE : Completes f sE.fn joins := by simpa only [hs₁] using hcompl
    have g0A : Grows s₀ sA := trExpr_grows c fenv env s₀ sA sv h1
    have hvalidA : CurValid sA := hvalid.of_grows g0A
    have aAB : SGrowsAt sA.fn.blocks.size sA sB :=
      SGrowsAt.of_grows (Grows.of_mapM_freshVal h2X)
    have aAC := aAB.trans (SGrowsAt.of_newBlock h3)
    have csAC := (CurSame.of_grows (Grows.of_mapM_freshVal h2X)).trans
      (CurSame.of_newBlock h3)
    have hvalidC : CurValid sC := CurValid.of_same_sgrows hvalidA aAC csAC.1
    obtain ⟨hvalidD, hkCD⟩ := trCases_cur_closed fenv env lctx rets sv
      X joinId cases dflt sC sD uD hvalidC h4X
    have gCD := trCases_grows fenv env lctx rets sv X joinId cases dflt
      sv X joinId sC uD sD h4X
    have hjoinLt : joinId < sC.fn.blocks.size := newBlock_target_lt h3
    have hcurLtJoin : sC.fn.curId < joinId := by
      rw [csAC.1, SGrowsAt.newBlock_id h3]
      exact Nat.lt_of_lt_of_le hvalidA aAB.size
    have hjoinNeC : sC.fn.curId ≠ joinId := Nat.ne_of_lt hcurLtJoin
    have hjoinNeD : sD.fn.curId ≠ joinId := by
      intro heq
      rcases gCD.curId with heqC | hge
      · exact hjoinNeC (heqC ▸ heq)
      · exact Nat.not_lt_of_ge (heq ▸ hge) hjoinLt
    have hpA : ProtectedAt joins sA.fn :=
      ProtectedAt.forward hp (SGrows.of_grows g0A)
    have hpC : ProtectedAt joins sC.fn := ProtectedAt.forward hpA aAC
    have hpD : ProtectedAt joins sD.fn := ProtectedAt.forward hpC gCD
    have hcomplD : Completes f sD.fn (joinId :: joins) :=
      Completes.of_moveTo_protected (by simp) h5 (hcomplE.protect joinId)
    have hprotD : sD.fn.curId ∉ joinId :: joins := by
      simp only [List.mem_cons]
      exact fun h => h.elim hjoinNeD hpD.away
    have hcurD : sD.fn.cur = [] := trCases_cur_nil fenv env lctx rets sv
      X joinId cases dflt sC sD uD h4X
    have hcpD : CurPlaced f sD.fn := CurPlaced.of_moveTo_empty hvalidD hcurD
      hjoinNeD h5 hprotD (hcomplE.protect joinId)
    have hfinD : CurFinal f sD.fn := curFinal_of_move_grows h5 hjoinNeD
      hpD.away (SGrows.rfl' sE) hcomplE
    have hprotC : sC.fn.curId ∉ joinId :: joins := by
      simp only [List.mem_cons]
      exact fun h => h.elim hjoinNeC hpC.away
    have hcpC : CurPlaced f sC.fn :=
      curPlaced_back (renv := none) hkCD hprotC hcomplD (fun _ => hfinD) hcpD
    have hcpB : CurPlaced f sB.fn :=
      (CurSame.of_newBlock h3).placed_back hcpC
    have hcpA : CurPlaced f sA.fn :=
      curPlaced_back_grows (Grows.of_mapM_freshVal h2X) hcpB
    have hjoinBase : sA.fn.blocks.size ≤ joinId := by
      rw [SGrowsAt.newBlock_id h3]
      exact aAB.size
    have htail : SGrowsAt sA.fn.blocks.size sA sE :=
      aAC.trans ((gCD.mono aAC.size).trans
        (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hjoinBase) h5))
    have hcomplA : Completes f sA.fn joins := htail.completes_of hcomplE
    exact SOut.ofExprHalt
      (ihc.1 fenv env R s₀ sA sv joins hfe henv hfr hp hcomplA hcpA h1)
end Semantics
end YulEvmCompiler.SsaCfg
