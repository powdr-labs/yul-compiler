import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.Loop
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.OfYulSound.LoopSim

The loop reconstruction.

The blocks every loop-iteration clause shares (`LoopGrowth`/`loopGrowth`,
`loopTail_exit`, `LoopHeader`/`loopHeader`), the post-block entry step and the
backward frame lemma, and the three clauses that never reach the back edge:
`sim_loopBodyNonNormal` (the body exits abnormally), `sim_loopDone` (the
condition is zero) and `sim_loopCondHalt` (the condition halts).
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics (Ident Literal Expr Stmt VEnv Outcome)
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal evmWithExternal)

section Semantics
variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates

/-! ### The shared blocks of the loop family

Every loop-iteration clause — `sim_loopBodyNonNormal` here, and `loopDone`,
`loopCondHalt`, `loopStep`, `loopPostHalt` in the main induction — opens on
the same three blocks:

* `loopGrowth`, the static growth chain of the single generated layout;
* `loopTail_exit`, which reads the loop tail backwards from the finished
  function to the body block;
* `loopHeader`, the header-edge facts the condition IH is applied against.

They are bundled as records so that a clause picks the fields it needs with a
projection instead of restating a fifty-line prologue. -/

/-- The static growth chain of the one generated loop layout: what every
builder step between the loop entry `s₀` and the body block `sN` guarantees
about block ids, value ids and the function table. -/
structure LoopGrowth (s₀ sA sB sC sD sE sF sG sH sI sJ sK sL sM sN : BState)
    (hId bodyId : BlockId) : Prop where
  /-- The entry edge arguments only grow the state. -/
  g0A : Grows s₀ sA
  /-- Reserving the header parameters only grows the state. -/
  gAB : Grows sA sB
  /-- Reserving the exit parameters only grows the state. -/
  gCD : Grows sC sD
  /-- Reserving the post parameters only grows the state. -/
  gEF : Grows sE sF
  /-- Growth from loop entry to the entry edge. -/
  a0A : SGrowsAt s₀.fn.blocks.size s₀ sA
  /-- Growth from loop entry past the header parameters. -/
  a0B : SGrowsAt s₀.fn.blocks.size s₀ sB
  /-- Growth from loop entry past the header block. -/
  a0C : SGrowsAt s₀.fn.blocks.size s₀ sC
  /-- Growth from loop entry past the exit parameters. -/
  a0D : SGrowsAt s₀.fn.blocks.size s₀ sD
  /-- Growth from loop entry past the exit block. -/
  a0E : SGrowsAt s₀.fn.blocks.size s₀ sE
  /-- Growth from loop entry past the post parameters. -/
  a0F : SGrowsAt s₀.fn.blocks.size s₀ sF
  /-- Growth from loop entry past the post block. -/
  a0G : SGrowsAt s₀.fn.blocks.size s₀ sG
  /-- Growth from loop entry past the entry jump. -/
  a0H : SGrowsAt s₀.fn.blocks.size s₀ sH
  /-- The header block is reserved at or after loop entry. -/
  hheadBase : s₀.fn.blocks.size ≤ hId
  /-- Growth from loop entry to the header block. -/
  a0I : SGrowsAt s₀.fn.blocks.size s₀ sI
  /-- Growth from the entry edge to the header block. -/
  aAI : SGrowsAt 0 sA sI
  /-- Evaluating the condition only grows the state. -/
  gIJ : Grows sI sJ
  /-- Growth from the condition past the body block. -/
  aJK : SGrowsAt sJ.fn.blocks.size sJ sK
  /-- The back-edge arguments only grow the state. -/
  gKL : Grows sK sL
  /-- Growth from the condition past the header edge arguments. -/
  aJL : SGrowsAt sJ.fn.blocks.size sJ sL
  /-- Growth from the condition past the header branch. -/
  aJM : SGrowsAt sJ.fn.blocks.size sJ sM
  /-- The body block is reserved at or after the condition. -/
  hbodyBase : sJ.fn.blocks.size ≤ bodyId
  /-- Growth from the condition to the body block. -/
  aJN : SGrowsAt sJ.fn.blocks.size sJ sN
  /-- Growth from the exit block past the post parameters. -/
  eF : SGrowsAt 0 sE sF
  /-- Growth from the exit block past the post block. -/
  eG : SGrowsAt 0 sE sG
  /-- Growth from the exit block past the entry jump. -/
  eH : SGrowsAt 0 sE sH
  /-- Growth from the exit block to the header block. -/
  eI : SGrowsAt 0 sE sI
  /-- Growth from the exit block past the condition. -/
  eJ : SGrowsAt 0 sE sJ
  /-- Growth from the exit block past the body block. -/
  eK : SGrowsAt 0 sE sK
  /-- Growth from the exit block past the header edge arguments. -/
  eL : SGrowsAt 0 sE sL
  /-- Growth from the exit block past the header branch. -/
  eM : SGrowsAt 0 sE sM
  /-- Growth from the exit block to the body block. -/
  eN : SGrowsAt 0 sE sN

omit model in
/-- Read the growth chain off the builder steps of the loop layout. -/
theorem loopGrowth {fenv : FMap} {env : VMap} {c : Expr Op}
    {post body : List (Stmt Op)}
    {s₀ sA sB sC sD sE sF sG sH sI sJ sK sL sM sN : BState}
    {xvals hParams exitParams postParams hX : List ValId}
    {hId exitId postId bodyId : BlockId} {cvId : ValId}
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
    (h14 : moveTo bodyId sM = some ((), sN)) :
    LoopGrowth s₀ sA sB sC sD sE sF sG sH sI sJ sK sL sM sN hId bodyId := by
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
  exact ⟨g0A, gAB, gCD, gEF, a0A, a0B, a0C, a0D, a0E, a0F, a0G, a0H,
    hheadBase, a0I, aAI, gIJ, aJK, gKL, aJL, aJM, hbodyBase, aJN,
    eF, eG, eH, eI, eJ, eK, eL, eM, eN⟩

omit model in
/-- Read the loop tail backwards.  Whatever the body and the post fragment
divert or fall through, the generated tail ends by moving to the protected
exit block, so the finished function completes the body block, the exit block
is current and empty at the end, and the loop's residual environment is the
exit rebinding. -/
theorem loopTail_exit {f : Func} {fenv : FMap} {env : VMap}
    {rets : Option (List Ident)} {post body : List (Stmt Op)}
    {hId exitId postId : BlockId}
    {hParams exitParams postParams : List ValId}
    {sN sO s₁ : BState} {bodyEnv renv : Option VMap} {joins : List BlockId}
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
    (hcompl : Completes f s₁.fn joins) :
    Completes f sN.fn (exitId :: postId :: joins) ∧ SGrowsAt 0 sN s₁
      ∧ s₁.fn.curId = exitId ∧ s₁.fn.cur = []
      ∧ renv = some (env.setMany (modifiedX env [post, body]) exitParams) := by
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
      have hcQ : Completes f sQ.fn (exitId :: postId :: joins) :=
        Completes.of_moveTo_protected (by simp) h18
          ((hcompl.protect postId).protect exitId)
      have hcP := SGrowsAt.completes_of gp hcQ
      have hcO := Completes.of_moveTo_protected (by simp) h16 hcP
      have gn0 := gb.mono (Nat.zero_le _)
      have gn1 := gn0.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h16)
      have gn2 := gn1.trans (gp.mono (Nat.zero_le _))
      have gn := gn2.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h18)
      refine ⟨SGrowsAt.completes_of gb hcO, gn, ?_, ?_, hrenv⟩
      · rw [M.moveTo_apply] at h18
        exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h18).2).symm
      · rw [M.moveTo_apply] at h18
        simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h18).2
    | some envP =>
      obtain ⟨xvP, sR, h18, htr⟩ := M.bind_inv htr
      obtain ⟨uS, sS, h19, htr⟩ := M.bind_inv htr
      obtain ⟨uT, sT, h20, htr⟩ := M.bind_inv htr
      obtain ⟨hrenv, hs₁⟩ := M.pure_inv htr
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
      have gn0 := gb.mono (Nat.zero_le _)
      have gn1 := gn0.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h16)
      have gn2 := gn1.trans (gp.mono (Nat.zero_le _))
      have gn3 := gn2.trans (gQS.mono (Nat.zero_le _))
      have gn := gn3.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h20)
      refine ⟨SGrowsAt.completes_of gb hcO, gn, ?_, ?_, hrenv⟩
      · rw [M.moveTo_apply] at h20
        exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h20).2).symm
      · rw [M.moveTo_apply] at h20
        simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h20).2
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
      obtain ⟨hrenv, hs₁⟩ := M.pure_inv htr
      subst s₁
      have hcS : Completes f sS.fn (exitId :: postId :: joins) :=
        Completes.of_moveTo_protected (by simp) h20
          ((hcompl.protect postId).protect exitId)
      have hcR := SGrowsAt.completes_of gp hcS
      have hcQ := Completes.of_moveTo_protected (by simp) h18 hcR
      have hcO := SGrowsAt.completes_of gOQ hcQ
      have gn0 := gb.mono (Nat.zero_le _)
      have gn1 := gn0.trans (gOQ.mono (Nat.zero_le _))
      have gn2 := gn1.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h18)
      have gn3 := gn2.trans (gp.mono (Nat.zero_le _))
      have gn := gn3.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h20)
      refine ⟨SGrowsAt.completes_of gb hcO, gn, ?_, ?_, hrenv⟩
      · rw [M.moveTo_apply] at h20
        exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h20).2).symm
      · rw [M.moveTo_apply] at h20
        simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h20).2
    | some envP =>
      obtain ⟨xvP, sT, h20, htr⟩ := M.bind_inv htr
      obtain ⟨uU, sU, h21, htr⟩ := M.bind_inv htr
      obtain ⟨uW, sW, h22, htr⟩ := M.bind_inv htr
      obtain ⟨hrenv, hs₁⟩ := M.pure_inv htr
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
      have gn0 := gb.mono (Nat.zero_le _)
      have gn1 := gn0.trans (gOQ.mono (Nat.zero_le _))
      have gn2 := gn1.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h18)
      have gn3 := gn2.trans (gp.mono (Nat.zero_le _))
      have gn4 := gn3.trans (gSU.mono (Nat.zero_le _))
      have gn := gn4.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h22)
      refine ⟨SGrowsAt.completes_of gb hcO, gn, ?_, ?_, hrenv⟩
      · rw [M.moveTo_apply] at h22
        exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h22).2).symm
      · rw [M.moveTo_apply] at h22
        simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h22).2

/-- The header-edge facts of the generated loop layout: the condition is
evaluated in a protected, placed, valid header block, and the branch it feeds
is the one the finished function carries. -/
structure LoopHeader (f : Func) (joins : List BlockId)
    (hId exitId postId bodyId : BlockId) (cvId : ValId) (hX : List ValId)
    (sI sJ sL sM : BState) : Prop where
  /-- The finished function completes the condition state. -/
  hcJ : Completes f sJ.fn (exitId :: postId :: joins)
  /-- The finished function completes the header block. -/
  hcI : Completes f sI.fn (exitId :: postId :: joins)
  /-- The header block is current at the condition. -/
  hcurI : sI.fn.curId = hId
  /-- Nothing has been emitted into the header block yet. -/
  hcurI0 : sI.fn.cur = []
  /-- The exit block is reserved after the header block. -/
  hheadExit : hId < exitId
  /-- The post block is reserved after the exit block. -/
  hexitPost : exitId < postId
  /-- The ambient joins are protected at the header block. -/
  hpI0 : ProtectedAt joins sI.fn
  /-- The loop's own exit and post blocks are protected too. -/
  hpI : ProtectedAt (exitId :: postId :: joins) sI.fn
  /-- The header block is a valid current block. -/
  hvalidI : CurValid sI
  /-- So is the block the condition ends in. -/
  hvalidJ : CurValid sJ
  /-- The header edge arguments do not move the current block. -/
  csJL : CurSame sJ sL
  /-- Nor does sealing the header branch. -/
  hcurM : sM.fn.curId = sJ.fn.curId
  /-- The header branch is sealed away from the body block. -/
  hbodyNe : sM.fn.curId ≠ bodyId
  /-- The exit and post blocks are still protected at the header branch. -/
  hpM : ProtectedAt (exitId :: postId :: joins) sM.fn
  /-- The block holding the header branch is final. -/
  hfinM : CurFinal f sM.fn
  /-- The header branch as the builder sealed it. -/
  hbranchL : CurOK f sL.fn ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨exitId, hX⟩⟩
  /-- The same branch read back at the end of the condition. -/
  hbranchJ : CurOK f sJ.fn ⟨[], .branch cvId ⟨bodyId, []⟩ ⟨exitId, hX⟩⟩
  /-- Hence the condition ends in a placed block. -/
  hcpJ : CurPlaced f sJ.fn
  /-- And so does the header block. -/
  hcpI : CurPlaced f sI.fn

omit model in
/-- Assemble the header-edge facts from the layout steps, the ambient
protection at loop entry, and the completion of the body block. -/
theorem loopHeader {f : Func} {hParams exitParams postParams hX : List ValId}
    {xvals : List ValId} {joins : List BlockId}
    {s₀ sA sB sC sD sE sF sG sH sI sJ sK sL sM sN : BState}
    {hId exitId postId bodyId : BlockId} {cvId : ValId}
    (G : LoopGrowth s₀ sA sB sC sD sE sF sG sH sI sJ sK sL sM sN hId bodyId)
    (h3 : newBlock hParams sB = some (hId, sC))
    (h5 : newBlock exitParams sD = some (exitId, sE))
    (h7 : newBlock postParams sF = some (postId, sG))
    (h8 : sealCur (.jump ⟨hId, xvals⟩) sG = some ((), sH))
    (h9 : moveTo hId sH = some ((), sI))
    (h11 : newBlock [] sJ = some (bodyId, sK))
    (h12 : ∃ envH X, edgeArgs envH X sK = some (hX, sL))
    (h13 : sealCur (.branch cvId ⟨bodyId, []⟩ ⟨exitId, hX⟩) sL = some ((), sM))
    (h14 : moveTo bodyId sM = some ((), sN))
    (hp : ProtectedAt joins s₀.fn)
    (hcN : Completes f sN.fn (exitId :: postId :: joins)) :
    LoopHeader f joins hId exitId postId bodyId cvId hX sI sJ sL sM := by
  have hcJ : Completes f sJ.fn (exitId :: postId :: joins) :=
    SGrowsAt.completes_of G.aJN hcN
  have hcI : Completes f sI.fn (exitId :: postId :: joins) :=
    SGrowsAt.completes_of (SGrowsAt.of_grows G.gIJ) hcJ
  have hcurI : sI.fn.curId = hId := by
    rw [M.moveTo_apply] at h9
    exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h9).2).symm
  have hcurI0 : sI.fn.cur = [] := by
    rw [M.moveTo_apply] at h9
    simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h9).2
  have hheadExit : hId < exitId := by
    rw [SGrowsAt.newBlock_id h5]
    exact Nat.lt_of_lt_of_le (newBlock_target_lt h3)
      (SGrowsAt.of_grows (N := 0) G.gCD).size
  have hexitPost : exitId < postId := by
    rw [SGrowsAt.newBlock_id h7]
    exact Nat.lt_of_lt_of_le (newBlock_target_lt h5)
      (SGrowsAt.of_grows (N := 0) G.gEF).size
  have hpI0 : ProtectedAt joins sI.fn := ProtectedAt.forward hp G.a0I
  have hpI : ProtectedAt (exitId :: postId :: joins) sI.fn := by
    refine ⟨?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with rfl | rfl | hi
      · exact Nat.lt_of_lt_of_le (newBlock_target_lt h5) G.eI.size
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
      (((((SGrowsAt.of_grows (N := 0) G.gCD).trans
        (SGrowsAt.of_newBlock h5)).trans
        (SGrowsAt.of_grows G.gEF)).trans
        (SGrowsAt.of_newBlock h7)).trans
        (SGrowsAt.of_sealCur h8)).size
  have hvalidJ : CurValid sJ := hvalidI.of_grows G.gIJ
  have csJL : CurSame sJ sL :=
    (CurSame.of_newBlock h11).trans (CurSame.of_grows G.gKL)
  have hcurM : sM.fn.curId = sJ.fn.curId := by
    rw [(sealCur_cur h13).choose_spec.1, csJL.1]
  have hbodyNe : sM.fn.curId ≠ bodyId := by
    rw [hcurM, SGrowsAt.newBlock_id h11]
    exact Nat.ne_of_lt hvalidJ
  have hpM : ProtectedAt (exitId :: postId :: joins) sM.fn := by
    have hgIM : SGrowsAt sI.fn.blocks.size sI sM :=
      ((SGrowsAt.of_grows (N := sI.fn.blocks.size) G.gIJ).trans
        (G.aJL.mono
          (SGrowsAt.of_grows (N := sI.fn.blocks.size) G.gIJ).size)).trans
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
      obtain ⟨envH, X, h12⟩ := h12
      have hedge : sL = sK := (M.edgeArgs_inv h12).2
      rw [hedge, hnew]) hbranchL
  have hcpJ : CurPlaced f sJ.fn := ⟨_, hbranchJ⟩
  have hcpI : CurPlaced f sI.fn := curPlaced_back_grows G.gIJ hcpJ
  exact ⟨hcJ, hcI, hcurI, hcurI0, hheadExit, hexitPost, hpI0, hpI, hvalidI,
    hvalidJ, csJL, hcurM, hbodyNe, hpM, hfinM, hbranchL, hbranchJ, hcpJ, hcpI⟩

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

set_option maxHeartbeats 1000000 in
/-- **The loop-exits case.**  The condition is zero, so the header branch
takes the exit edge and the loop's residual environment is the exit
rebinding. -/
theorem sim_loopDone {P : Prog} {f : Func} {funs : YulSemantics.FunEnv yulD}
    {V : VEnv yulD} {st st1 : EvmState} {c : Expr Op}
    {post body : List (Stmt Op)} {cv : U256}
    {doneFuncs : Array (Option Func)}
    {hfuncs : FuncTableComplete P doneFuncs}
    (hz : cv = YulSemantics.Dialect.zero yulD)
    (ihc : Motive (model := model) P f funs V st doneFuncs hfuncs
      (.expr c) (.eres (.vals [cv] st1))) :
    LOut (model := model) P f funs V st c post body V st1 .normal
      doneFuncs := by
    intro fenv env rets s₀ s₁ renv joins layout hfe huniq hctx hvalid hp
      hcompl hcp _hfin done owned hdone hbound hown R henv hfr hclean hreb
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
    obtain ⟨hcN, gn, hcurExit, hcurExit0, hrenv⟩ :=
      loopTail_exit h15 htr hcompl
    have ge : SGrowsAt 0 sE s₁ := eN.trans gn
    have hnextJ1 : sJ.fn.nextVal ≤ s₁.fn.nextVal :=
      Nat.le_trans aJN.nextVal gn.nextVal
    obtain ⟨hcJ, hcI, hcurI, hcurI0, hheadExit, hexitPost, hpI0, hpI, hvalidI,
      hvalidJ, csJL, hcurM, hbodyNe, hpM, hfinM, hbranchL, hbranchJ, hcpJ,
      hcpI⟩ := loopHeader G h3 h5 h7 h8 h9 h11 ⟨_, _, h12⟩ h13 h14 hp hcN
    obtain ⟨hlenH, hrangeH, hsB⟩ := M.mapM_freshVal_length h2
    have hndH : hParams.Nodup := by
      rw [hrangeH]
      exact M.nodup_range' _ _
    obtain ⟨RA, hleA, hbelowA, hfrA, hcv, hsimC⟩ :=
      ihc.1 fenv (env.setMany (modifiedX env [post, body]) hParams) R
        sI sJ cvId cv (exitId :: postId :: joins) hfe henv hfr hpI
        hcJ hcpJ rfl h10
    obtain ⟨rfl, valsE, hXget, hXvals⟩ :=
      edgeArgs_ok (henv.mono hleA) h12
    obtain ⟨hlenE, hrangeE, hsD⟩ := M.mapM_freshVal_length h4
    have hndE : exitParams.Nodup := by
      rw [hrangeE]
      exact M.nodup_range' _ _
    have hnextCB : sC.fn.nextVal = sB.fn.nextVal := by
      rw [M.newBlock_apply] at h3
      exact (congrArg (fun z => z.fn.nextVal) (M.some_pair_inj h3).2).symm
    have dI : SGrowsAt 0 sD sI :=
      (((((SGrowsAt.of_newBlock (N := 0) h5).trans
        (SGrowsAt.of_grows gEF)).trans (SGrowsAt.of_newBlock h7)).trans
        (SGrowsAt.of_sealCur h8)).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9))
    have hnoneE : ∀ i ∈ exitParams, RA i = none := by
      intro i hi
      have hiRange := hi
      rw [hrangeE] at hiRange
      have hiLtI : i < sI.fn.nextVal :=
        Nat.lt_of_lt_of_le (M.mem_range'_bounds hiRange).2 (by
          simpa [hsD] using dI.nextVal)
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
        have hend : sA.fn.nextVal + (modifiedX env [post, body]).length =
            sC.fn.nextVal := by rw [hnextCB, hsB]
        have hu' : i < sC.fn.nextVal := by rwa [hend] at hu
        exact Nat.not_lt_of_ge hl hu'
    let RE := RA.setMany exitParams valsE
    have hleE : Regs.Le RA RE := Regs.Le.setMany hndE hnoneE
    have hbelowE : Regs.BelowEq sA.fn.nextVal RA RE := by
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
      · exact hfrA i (Nat.le_trans hnextJ1 hi)
      · intro him
        rw [hrangeE] at him
        have hltD := (M.mem_range'_bounds him).2
        have hD1 : sD.fn.nextVal ≤ s₁.fn.nextVal := by
          exact Nat.le_trans
            (SGrowsAt.of_newBlock (N := 0) h5).nextVal ge.nextVal
        have hltD' : i < sD.fn.nextVal := by simpa [hsD] using hltD
        exact Nat.not_lt_of_ge (Nat.le_trans hD1 hi) hltD'
    obtain ⟨eb, heb, hep⟩ := ge.params exitId ⟨exitParams, [], .ret []⟩
      (newBlock_target_get h5)
    have hlenEB : eb.params.length = valsE.length := by
      rw [hep, hlenE]
      exact hXvals.length_eq
    have hzero : RA cvId = some 0 := by
      rw [hz] at hcv
      simpa only [yulD_zero] using hcv
    have hsimE : SimS (model := model) P f sJ.fn RA st1 s₁.fn RE st1 := by
      have hs := simS_branchFalse_join (model := model) (P := P) (f := f)
        (st := st1) hcompl hbranchJ hzero heb hcurExit hcurExit0 hXget hlenEB
      simpa only [hep] using hs
    have hpgetE : RE.getMany exitParams = some valsE :=
      Regs.getMany_setMany_self hndE (by rw [hlenE]; exact hXvals.length_eq)
    have henvE : EnvOK (model := model)
        (env.setMany (modifiedX env [post, body]) exitParams) V RE := by
      have he : EnvOK (model := model)
          ((env.setMany (modifiedX env [post, body]) hParams).setMany
            (modifiedX env [post, body]) exitParams)
          (YulSemantics.VEnv.setMany V (modifiedX env [post, body]) valsE) RE :=
        EnvOK.setMany (xs := modifiedX env [post, body])
          (henv.mono (hleA.trans hleE))
          (Regs.getMany_eq_some_iff.mp hpgetE)
      rw [VMap.setMany_overwrite env (modifiedX_nodup huniq _)
        hlenH.symm hlenE.symm] at he
      rw [VEnv.setMany_self hXvals] at he
      exact he
    exact ⟨env.setMany (modifiedX env [post, body]) exitParams, RE, hrenv,
      (hbelowA.mono aAI.nextVal).trans hbelowE, hfrE,
      henvE, huniq.setMany _ _, hsimC.trans hsimE⟩

set_option maxHeartbeats 1000000 in
/-- **The condition-halts case.**  The loop halts inside the header block. -/
theorem sim_loopCondHalt {P : Prog} {f : Func}
    {funs : YulSemantics.FunEnv yulD} {V : VEnv yulD} {st st1 : EvmState}
    {c : Expr Op} {post body : List (Stmt Op)}
    {doneFuncs : Array (Option Func)}
    {hfuncs : FuncTableComplete P doneFuncs}
    (ihc : Motive (model := model) P f funs V st doneFuncs hfuncs
      (.expr c) (.eres (.halt st1))) :
    LOut (model := model) P f funs V st c post body V st1 .halt
      doneFuncs := by
    intro fenv env rets s₀ s₁ renv joins layout hfe huniq hctx hvalid hp
      hcompl hcp _hfin done owned hdone hbound hown R henv hfr hclean hreb
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
    have hhalt := ihc.1 fenv
      (env.setMany (modifiedX env [post, body]) hParams) R sI sJ cvId
      (exitId :: postId :: joins) hfe henv hfr hpI hcJ hcpJ h10
    exact hhalt
end Semantics
end YulEvmCompiler.SsaCfg
