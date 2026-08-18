import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.NoShadow
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.OfYulSound.Loop

Loop layout, and the simulation motive.

`LoopLayout` and its frame lemmas, the loop-header entry step
(`LoopLayout.enter`), the loop outcome shapes (`LHOut`, `loop_outcome_ssa`),
and finally `LOut` and `Motive` — the statement-class simulation motive the
main induction is stated against.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics (Ident Literal Expr Stmt VEnv Outcome)
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal evmWithExternal)

section Semantics
variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates

/-- The statement-expression entry point needs its own expression induction
clause: unlike `trExpr`, it deliberately emits no destination for zero-result
builtins and calls. -/
def EStmtOut (P : Prog) (f : Func) (funs : YulSemantics.FunEnv yulD)
    (V : VEnv yulD) (yst : EvmState) (e : Expr Op)
    (V' : VEnv yulD) (yst' : EvmState) (o : Outcome) : Prop :=
  ∀ (fenv : FMap) (env : VMap) (R : Regs) (lctx : Option LoopCtx)
      (rets : Option (List Ident)) (s₀ s₁ : BState) (renv : Option VMap)
      (joins : List BlockId),
    FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
    env.Unique → RegsFresh R s₀.fn → CurValid s₀ →
    ProtectedAt joins s₀.fn → Completes f s₁.fn joins → CurPlaced f s₁.fn →
    (renv = none → CurFinal f s₁.fn) →
    trStmt fenv env lctx rets (.exprStmt e) s₀ = some (renv, s₁) →
    SOut (model := model) P f lctx rets s₀ s₁ R renv V' yst yst' o

/-- A named decomposition of the one statically generated loop.  The source
loop induction revisits `sI`, but never translates another copy of the loop;
keeping the complete layout in one witness lets its IH reuse precisely these
header/body/post/exit blocks. -/
structure LoopLayout (fenv : FMap) (env : VMap) (rets : Option (List Ident))
    (c : Expr Op) (post body : List (Stmt Op)) (s₀ s₁ : BState)
    (renv : Option VMap) where
  xvals : List ValId
  sA : BState
  h1 : edgeArgs env (modifiedX env [post, body]) s₀ = some (xvals, sA)
  hParams : List ValId
  sB : BState
  h2 : (modifiedX env [post, body]).mapM (fun _ => freshVal) sA =
    some (hParams, sB)
  hId : BlockId
  sC : BState
  h3 : newBlock hParams sB = some (hId, sC)
  exitParams : List ValId
  sD : BState
  h4 : (modifiedX env [post, body]).mapM (fun _ => freshVal) sC =
    some (exitParams, sD)
  exitId : BlockId
  sE : BState
  h5 : newBlock exitParams sD = some (exitId, sE)
  postParams : List ValId
  sF : BState
  h6 : (modifiedX env [post, body]).mapM (fun _ => freshVal) sE =
    some (postParams, sF)
  postId : BlockId
  sG : BState
  h7 : newBlock postParams sF = some (postId, sG)
  sH : BState
  h8 : sealCur (.jump ⟨hId, xvals⟩) sG = some ((), sH)
  sI : BState
  h9 : moveTo hId sH = some ((), sI)
  cvId : ValId
  sJ : BState
  h10 : trExpr fenv
      (env.setMany (modifiedX env [post, body]) hParams) c sI =
    some (cvId, sJ)
  bodyId : BlockId
  sK : BState
  h11 : newBlock [] sJ = some (bodyId, sK)
  hX : List ValId
  sL : BState
  h12 : edgeArgs (env.setMany (modifiedX env [post, body]) hParams)
      (modifiedX env [post, body]) sK = some (hX, sL)
  sM : BState
  h13 : sealCur (.branch cvId ⟨bodyId, []⟩ ⟨exitId, hX⟩) sL =
    some ((), sM)
  sN : BState
  h14 : moveTo bodyId sM = some ((), sN)
  bodyEnv : Option VMap
  sO : BState
  h15 : trScope fenv
      (env.setMany (modifiedX env [post, body]) hParams)
      (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body sN =
    some (bodyEnv, sO)
  tail : (do
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
    some (renv, s₁)

omit model in
/-- Replace only the final scope-dropping `pure` in the loop tail.  The four
body/post result shapes have identical builder effects before that `pure`. -/
theorem loopTail_drop_inv {fenv : FMap} {env envI : VMap}
    {rets : Option (List Ident)} {post body : List (Stmt Op)}
    {hId exitId postId : BlockId} {exitParams postParams : List ValId}
    {bodyEnv : Option VMap} {sO s₁ : BState} {renv : Option VMap}
    (h : (do
      if let some envB := bodyEnv then
        let xvB ← edgeArgs envB (modifiedX envI [post, body])
        sealCur (.jump ⟨postId, xvB⟩)
      moveTo postId
      let envP := envI.setMany (modifiedX envI [post, body]) postParams
      let renvP ← trScope fenv envP none rets post
      if let some envP' := renvP then
        let xvP ← edgeArgs envP' (modifiedX envI [post, body])
        sealCur (.jump ⟨hId, xvP⟩)
      moveTo exitId
      let envX := envI.setMany (modifiedX envI [post, body]) exitParams
      pure (some (envX.drop (envX.length - env.length)))) sO =
        some (renv, s₁)) :
    (do
      if let some envB := bodyEnv then
        let xvB ← edgeArgs envB (modifiedX envI [post, body])
        sealCur (.jump ⟨postId, xvB⟩)
      moveTo postId
      let envP := envI.setMany (modifiedX envI [post, body]) postParams
      let renvP ← trScope fenv envP none rets post
      if let some envP' := renvP then
        let xvP ← edgeArgs envP' (modifiedX envI [post, body])
        sealCur (.jump ⟨hId, xvP⟩)
      moveTo exitId
      pure (some (envI.setMany (modifiedX envI [post, body]) exitParams))) sO =
        some (some (envI.setMany (modifiedX envI [post, body]) exitParams), s₁) ∧
      renv = some ((envI.setMany (modifiedX envI [post, body]) exitParams).drop
        ((envI.setMany (modifiedX envI [post, body]) exitParams).length - env.length)) := by
  cases bodyEnv with
  | none =>
      obtain ⟨uP, sP, h16, h⟩ := M.bind_inv h
      obtain ⟨-, hsP⟩ := M.pure_inv h16
      subst sP
      obtain ⟨uQ, sQ, h17, h⟩ := M.bind_inv h
      obtain ⟨postEnv, sR, h18, h⟩ := M.bind_inv h
      cases postEnv with
      | none =>
          obtain ⟨uS, sS, h19, h⟩ := M.bind_inv h
          obtain ⟨-, hsS⟩ := M.pure_inv h19
          subst sS
          obtain ⟨uT, sT, h20, h⟩ := M.bind_inv h
          obtain ⟨hrenv, hs₁⟩ := M.pure_inv h
          subst s₁
          constructor
          · simp only [bind, StateT.bind, Option.bind, pure, StateT.pure,
              h17, h18, h20]
          · exact hrenv
      | some envP =>
          obtain ⟨xvP, sS, h19, h⟩ := M.bind_inv h
          obtain ⟨uT, sT, h20, h⟩ := M.bind_inv h
          obtain ⟨uU, sU, h21, h⟩ := M.bind_inv h
          obtain ⟨hrenv, hs₁⟩ := M.pure_inv h
          subst s₁
          constructor
          · simp only [bind, StateT.bind, Option.bind, pure, StateT.pure,
              h17, h18, h19, h20, h21]
          · exact hrenv
  | some envB =>
      obtain ⟨xvB, sP, h16, h⟩ := M.bind_inv h
      obtain ⟨uQ, sQ, h17, h⟩ := M.bind_inv h
      obtain ⟨uR, sR, h18, h⟩ := M.bind_inv h
      obtain ⟨postEnv, sS, h19, h⟩ := M.bind_inv h
      cases postEnv with
      | none =>
          obtain ⟨uT, sT, h20, h⟩ := M.bind_inv h
          obtain ⟨-, hsT⟩ := M.pure_inv h20
          subst sT
          obtain ⟨uU, sU, h21, h⟩ := M.bind_inv h
          obtain ⟨hrenv, hs₁⟩ := M.pure_inv h
          subst s₁
          constructor
          · simp only [bind, StateT.bind, Option.bind, pure, StateT.pure,
              h16, h17, h18, h19, h21]
          · exact hrenv
      | some envP =>
          obtain ⟨xvP, sT, h20, h⟩ := M.bind_inv h
          obtain ⟨uU, sU, h21, h⟩ := M.bind_inv h
          obtain ⟨uW, sW, h22, h⟩ := M.bind_inv h
          obtain ⟨hrenv, hs₁⟩ := M.pure_inv h
          subst s₁
          constructor
          · simp only [bind, StateT.bind, Option.bind, pure, StateT.pure,
              h16, h17, h18, h19, h20, h21, h22]
          · exact hrenv

omit model in
/-- Invert the `forLoop` wrapper into its initializer and the inner static loop
layout.  The layout ends before the wrapper drops initializer declarations. -/
theorem trStmt_forLoop_inv {fenv : FMap} {env : VMap}
    {lctx : Option LoopCtx} {rets : Option (List Ident)}
    {init post body : List (Stmt Op)} {c : Expr Op}
    {s₀ s₁ : BState} {renv : Option VMap}
    (h : trStmt fenv env lctx rets (.forLoop init c post body) s₀ =
      some (renv, s₁)) :
    ∃ (scope : List (Ident × FuncId)) (sA sI : BState)
        (rinit : Option VMap),
      allocScope init s₀ = some (scope, sA) ∧
      trStmts (scope :: fenv) env lctx rets false init sA = some (rinit, sI) ∧
      match rinit with
      | none => renv = none ∧ s₁ = sI
      | some envI => ∃ envX,
          Nonempty (LoopLayout (scope :: fenv) envI rets c post body
            sI s₁ (some envX)) ∧
          renv = some (envX.drop (envX.length - env.length)) := by
  unfold trStmt at h
  obtain ⟨scope, sA, ha, h⟩ := M.bind_inv h
  obtain ⟨rinit, sI, hi, h⟩ := M.bind_inv h
  refine ⟨scope, sA, sI, rinit, ha, hi, ?_⟩
  cases rinit with
  | none => exact M.pure_inv h
  | some envI =>
      obtain ⟨xvals, sB, h1, h⟩ := M.bind_inv h
      obtain ⟨hParams, sC, h2, h⟩ := M.bind_inv h
      obtain ⟨hId, sD, h3, h⟩ := M.bind_inv h
      obtain ⟨exitParams, sE, h4, h⟩ := M.bind_inv h
      obtain ⟨exitId, sF, h5, h⟩ := M.bind_inv h
      obtain ⟨postParams, sG, h6, h⟩ := M.bind_inv h
      obtain ⟨postId, sH, h7, h⟩ := M.bind_inv h
      obtain ⟨uI, sI', h8, h⟩ := M.bind_inv h
      obtain ⟨uJ, sJ, h9, h⟩ := M.bind_inv h
      obtain ⟨cvId, sK, h10, h⟩ := M.bind_inv h
      obtain ⟨bodyId, sL, h11, h⟩ := M.bind_inv h
      obtain ⟨hX, sM, h12, h⟩ := M.bind_inv h
      obtain ⟨uN, sN, h13, h⟩ := M.bind_inv h
      obtain ⟨uO, sO, h14, h⟩ := M.bind_inv h
      obtain ⟨bodyEnv, sP, h15, htail⟩ := M.bind_inv h
      obtain ⟨htail', hrenv⟩ := loopTail_drop_inv htail
      let envX := envI.setMany (modifiedX envI [post, body]) exitParams
      exact ⟨envX, ⟨⟨xvals, sB, h1, hParams, sC, h2, hId, sD, h3,
        exitParams, sE, h4, exitId, sF, h5, postParams, sG, h6,
        postId, sH, h7, sI', h8, sJ, h9, cvId, sK, h10,
        bodyId, sL, h11, hX, sM, h12, sN, h13, sO, h14,
        bodyEnv, sP, h15, htail'⟩⟩, hrenv⟩

omit model in
/-- The code after the body of a fixed loop layout is closed with respect to
the function table present at body exit. -/
theorem LoopLayout.tail_fprefix {fenv : FMap} {env : VMap}
    {rets : Option (List Ident)} {c : Expr Op} {post body : List (Stmt Op)}
    {s₀ s₁ : BState} {renv : Option VMap}
    (layout : LoopLayout fenv env rets c post body s₀ s₁ renv) :
    FPrefix layout.sO.funcs.size layout.sO s₁ := by
  rcases layout with
    ⟨xvals, sA, h1, hParams, sB, h2, hId, sC, h3,
     exitParams, sD, h4, exitId, sE, h5, postParams, sF, h6,
     postId, sG, h7, sH, h8, sI, h9, cvId, sJ, h10,
     bodyId, sK, h11, hX, sL, h12, sM, h13, sN, h14,
     bodyEnv, sO, h15, htail⟩
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
          some (renv, s₁) at htail
      obtain ⟨uP, sP, h16, htail⟩ := M.bind_inv htail
      obtain ⟨postEnv, sQ, h17, htail⟩ := M.bind_inv htail
      have pOP : FPrefix sO.funcs.size sO sP := FPrefix.of_moveTo h16
      have pOQ : FPrefix sO.funcs.size sO sQ := pOP.trans
        (trScope_fprefix fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sO.funcs.size sP postEnv sQ (pOP.size (Nat.le_refl _)) h17)
      cases postEnv with
      | none =>
          obtain ⟨uR, sR, h18, htail⟩ := M.bind_inv htail
          obtain ⟨-, rfl⟩ := M.pure_inv h18
          obtain ⟨uT, sT, h19, htail⟩ := M.bind_inv htail
          obtain ⟨-, rfl⟩ := M.pure_inv h19
          obtain ⟨-, rfl⟩ := M.pure_inv htail
          exact pOQ
      | some envP =>
          obtain ⟨xvP, sR, h18, htail⟩ := M.bind_inv htail
          obtain ⟨uS, sS, h19, htail⟩ := M.bind_inv htail
          obtain ⟨uT, sT, h20, htail⟩ := M.bind_inv htail
          obtain ⟨-, rfl⟩ := M.pure_inv htail
          exact ((pOQ.trans (FPrefix.of_edgeArgs h18)).trans
            (FPrefix.of_sealCur h19)).trans (FPrefix.of_moveTo h20)
  | some envB =>
      obtain ⟨xvB, sP, h16, htail⟩ := M.bind_inv htail
      obtain ⟨uQ, sQ, h17, htail⟩ := M.bind_inv htail
      obtain ⟨uR, sR, h18, htail⟩ := M.bind_inv htail
      obtain ⟨postEnv, sS, h19, htail⟩ := M.bind_inv htail
      have pOR : FPrefix sO.funcs.size sO sR :=
        (((FPrefix.of_edgeArgs h16).trans (FPrefix.of_sealCur h17)).trans
          (FPrefix.of_moveTo h18))
      have pOS : FPrefix sO.funcs.size sO sS := pOR.trans
        (trScope_fprefix fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sO.funcs.size sR postEnv sS (pOR.size (Nat.le_refl _)) h19)
      cases postEnv with
      | none =>
          obtain ⟨uT, sT, h20, htail⟩ := M.bind_inv htail
          obtain ⟨-, rfl⟩ := M.pure_inv h20
          obtain ⟨uU, sU, h21, htail⟩ := M.bind_inv htail
          obtain ⟨-, rfl⟩ := M.pure_inv h21
          obtain ⟨-, rfl⟩ := M.pure_inv htail
          exact pOS
      | some envP =>
          obtain ⟨xvP, sT, h20, htail⟩ := M.bind_inv htail
          obtain ⟨uU, sU, h21, htail⟩ := M.bind_inv htail
          obtain ⟨uW, sW, h22, htail⟩ := M.bind_inv htail
          obtain ⟨-, rfl⟩ := M.pure_inv htail
          exact ((pOS.trans (FPrefix.of_edgeArgs h20)).trans
            (FPrefix.of_sealCur h21)).trans (FPrefix.of_moveTo h22)

omit model in
/-- A complete loop layout preserves every function-table slot that existed at
its preheader. -/
theorem LoopLayout.fprefix {fenv : FMap} {env : VMap}
    {rets : Option (List Ident)} {c : Expr Op} {post body : List (Stmt Op)}
    {s₀ s₁ : BState} {renv : Option VMap}
    (layout : LoopLayout fenv env rets c post body s₀ s₁ renv) :
    FPrefix s₀.funcs.size s₀ s₁ := by
  have ptail := layout.tail_fprefix
  rcases layout with
    ⟨xvals, sA, h1, hParams, sB, h2, hId, sC, h3,
     exitParams, sD, h4, exitId, sE, h5, postParams, sF, h6,
     postId, sG, h7, sH, h8, sI, h9, cvId, sJ, h10,
     bodyId, sK, h11, hX, sL, h12, sM, h13, sN, h14,
     bodyEnv, sO, h15, htail⟩
  have p0A : FPrefix s₀.funcs.size s₀ sA := FPrefix.of_edgeArgs h1
  have p0B := p0A.trans (FPrefix.of_grows (Grows.of_mapM_freshVal h2))
  have p0C := p0B.trans (FPrefix.of_newBlock h3)
  have p0D := p0C.trans (FPrefix.of_grows (Grows.of_mapM_freshVal h4))
  have p0E := p0D.trans (FPrefix.of_newBlock h5)
  have p0F := p0E.trans (FPrefix.of_grows (Grows.of_mapM_freshVal h6))
  have p0G := p0F.trans (FPrefix.of_newBlock h7)
  have p0H := p0G.trans (FPrefix.of_sealCur h8)
  have p0I := p0H.trans (FPrefix.of_moveTo h9)
  have p0J := p0I.trans
    (FPrefix.of_grows (trExpr_grows c fenv
      (env.setMany (modifiedX env [post, body]) hParams) sI sJ cvId h10))
  have p0K := p0J.trans (FPrefix.of_newBlock h11)
  have p0L := p0K.trans (FPrefix.of_edgeArgs h12)
  have p0M := p0L.trans (FPrefix.of_sealCur h13)
  have p0N := p0M.trans (FPrefix.of_moveTo h14)
  have p0O := p0N.trans
    (trScope_fprefix fenv
      (env.setMany (modifiedX env [post, body]) hParams)
      (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
      s₀.funcs.size sN bodyEnv sO (p0N.size (Nat.le_refl _)) h15)
  exact p0O.trans (ptail.mono (p0O.size (Nat.le_refl _)))

omit model in
/-- Everything after entering the loop header grows above the loop's entry
block watermark.  This is the framing fact needed to recover placement of the
initializer's open continuation from the completed loop layout. -/
theorem LoopLayout.header_tail_sgrows {fenv : FMap} {env : VMap}
    {rets : Option (List Ident)} {c : Expr Op} {post body : List (Stmt Op)}
    {s₀ s₁ : BState} {renv : Option VMap}
    (layout : LoopLayout fenv env rets c post body s₀ s₁ renv) :
    SGrowsAt s₀.fn.blocks.size layout.sI s₁ := by
  rcases layout with
    ⟨xvals, sA, h1, hParams, sB, h2, hId, sC, h3,
     exitParams, sD, h4, exitId, sE, h5, postParams, sF, h6,
     postId, sG, h7, sH, h8, sI, h9, cvId, sJ, h10,
     bodyId, sK, h11, hX, sL, h12, sM, h13, sN, h14,
     bodyEnv, sO, h15, htail⟩
  have g0A : Grows s₀ sA := Grows.of_liftO h1
  have a0B : SGrowsAt s₀.fn.blocks.size s₀ sB :=
    (SGrowsAt.of_grows g0A).trans
      (SGrowsAt.of_grows (Grows.of_mapM_freshVal h2))
  have a0C := a0B.trans (SGrowsAt.of_newBlock h3)
  have a0D := a0C.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h4))
  have a0E := a0D.trans (SGrowsAt.of_newBlock h5)
  have a0F := a0E.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h6))
  have a0G := a0F.trans (SGrowsAt.of_newBlock h7)
  have a0H := a0G.trans (SGrowsAt.of_sealCur h8)
  have hheader : s₀.fn.blocks.size ≤ hId := by
    rw [SGrowsAt.newBlock_id h3]
    exact a0B.size
  have a0I := a0H.trans (SGrowsAt.of_moveTo (Or.inl hheader) h9)
  have aIJ : SGrowsAt s₀.fn.blocks.size sI sJ :=
    SGrowsAt.of_grows (trExpr_grows c fenv
      (env.setMany (modifiedX env [post, body]) hParams) sI sJ cvId h10)
  have aIK := aIJ.trans (SGrowsAt.of_newBlock h11)
  have aIL := aIK.trans (SGrowsAt.of_edgeArgs h12)
  have aIM := aIL.trans (SGrowsAt.of_sealCur h13)
  have hbody : s₀.fn.blocks.size ≤ bodyId := by
    rw [SGrowsAt.newBlock_id h11]
    exact Nat.le_trans a0I.size aIJ.size
  have aIN := aIM.trans (SGrowsAt.of_moveTo (Or.inl hbody) h14)
  have gbody := trScope_grows fenv
    (env.setMany (modifiedX env [post, body]) hParams)
    (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
    sN bodyEnv sO h15
  have aIO := aIN.trans (gbody.mono (Nat.le_trans a0I.size aIN.size))
  have hpost : s₀.fn.blocks.size ≤ postId := by
    rw [SGrowsAt.newBlock_id h7]
    exact a0F.size
  have hexit : s₀.fn.blocks.size ≤ exitId := by
    rw [SGrowsAt.newBlock_id h5]
    exact a0D.size
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
          some (renv, s₁) at htail
      obtain ⟨uP, sP, h16, htail⟩ := M.bind_inv htail
      obtain ⟨postEnv, sQ, h17, htail⟩ := M.bind_inv htail
      have aIP := aIO.trans (SGrowsAt.of_moveTo (Or.inl hpost) h16)
      have gp := trScope_grows fenv
        (env.setMany (modifiedX env [post, body]) postParams) none rets post
        sP postEnv sQ h17
      have aIQ := aIP.trans (gp.mono (Nat.le_trans a0I.size aIP.size))
      cases postEnv with
      | none =>
          obtain ⟨uR, sR, h18, htail⟩ := M.bind_inv htail
          obtain ⟨uT, sT, h19, htail⟩ := M.bind_inv htail
          exact ((aIQ.trans (SGrowsAt.of_pure h18)).trans
            (SGrowsAt.of_moveTo (Or.inl hexit) h19)).trans
              (SGrowsAt.of_pure htail)
      | some envP =>
          obtain ⟨xvP, sR, h18, htail⟩ := M.bind_inv htail
          obtain ⟨uS, sS, h19, htail⟩ := M.bind_inv htail
          obtain ⟨uT, sT, h20, htail⟩ := M.bind_inv htail
          obtain ⟨-, rfl⟩ := M.pure_inv htail
          exact (((aIQ.trans (SGrowsAt.of_edgeArgs h18)).trans
            (SGrowsAt.of_sealCur h19)).trans
              (SGrowsAt.of_moveTo (Or.inl hexit) h20))
  | some envB =>
      obtain ⟨xvB, sP, h16, htail⟩ := M.bind_inv htail
      obtain ⟨uQ, sQ, h17, htail⟩ := M.bind_inv htail
      obtain ⟨uR, sR, h18, htail⟩ := M.bind_inv htail
      obtain ⟨postEnv, sS, h19, htail⟩ := M.bind_inv htail
      have aIR := (((aIO.trans (SGrowsAt.of_edgeArgs h16)).trans
        (SGrowsAt.of_sealCur h17)).trans
          (SGrowsAt.of_moveTo (Or.inl hpost) h18))
      have gp := trScope_grows fenv
        (env.setMany (modifiedX env [post, body]) postParams) none rets post
        sR postEnv sS h19
      have aIS := aIR.trans (gp.mono (Nat.le_trans a0I.size aIR.size))
      cases postEnv with
      | none =>
          obtain ⟨uT, sT, h20, htail⟩ := M.bind_inv htail
          obtain ⟨uU, sU, h21, htail⟩ := M.bind_inv htail
          exact ((aIS.trans (SGrowsAt.of_pure h20)).trans
            (SGrowsAt.of_moveTo (Or.inl hexit) h21)).trans
              (SGrowsAt.of_pure htail)
      | some envP =>
          obtain ⟨xvP, sT, h20, htail⟩ := M.bind_inv htail
          obtain ⟨uU, sU, h21, htail⟩ := M.bind_inv htail
          obtain ⟨uW, sW, h22, htail⟩ := M.bind_inv htail
          obtain ⟨-, rfl⟩ := M.pure_inv htail
          exact (((aIS.trans (SGrowsAt.of_edgeArgs h20)).trans
            (SGrowsAt.of_sealCur h21)).trans
              (SGrowsAt.of_moveTo (Or.inl hexit) h22))

omit model in
/-- A complete loop layout grows above its preheader's block watermark. -/
theorem LoopLayout.sgrows {fenv : FMap} {env : VMap}
    {rets : Option (List Ident)} {c : Expr Op} {post body : List (Stmt Op)}
    {s₀ s₁ : BState} {renv : Option VMap}
    (layout : LoopLayout fenv env rets c post body s₀ s₁ renv) :
    SGrowsAt s₀.fn.blocks.size s₀ s₁ := by
  have htail := layout.header_tail_sgrows
  rcases layout with
    ⟨xvals, sA, h1, hParams, sB, h2, hId, sC, h3,
     exitParams, sD, h4, exitId, sE, h5, postParams, sF, h6,
     postId, sG, h7, sH, h8, sI, h9, cvId, sJ, h10,
     bodyId, sK, h11, hX, sL, h12, sM, h13, sN, h14,
     bodyEnv, sO, h15, htr⟩
  have a0A : SGrowsAt s₀.fn.blocks.size s₀ sA :=
    SGrowsAt.of_grows (Grows.of_liftO h1)
  have a0B := a0A.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h2))
  have a0C := a0B.trans (SGrowsAt.of_newBlock h3)
  have a0D := a0C.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h4))
  have a0E := a0D.trans (SGrowsAt.of_newBlock h5)
  have a0F := a0E.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h6))
  have a0G := a0F.trans (SGrowsAt.of_newBlock h7)
  have a0H := a0G.trans (SGrowsAt.of_sealCur h8)
  have hheader : s₀.fn.blocks.size ≤ hId := by
    rw [SGrowsAt.newBlock_id h3]
    exact a0B.size
  exact (a0H.trans (SGrowsAt.of_moveTo (Or.inl hheader) h9)).trans htail

omit model in
/-- The preheader in a successful loop layout is sealed and left for the fresh
header, and later construction cannot return to it. -/
theorem LoopLayout.curMoved {fenv : FMap} {env : VMap}
    {rets : Option (List Ident)} {c : Expr Op} {post body : List (Stmt Op)}
    {s₀ s₁ : BState} {renv : Option VMap}
    (layout : LoopLayout fenv env rets c post body s₀ s₁ renv)
    (hvalid : CurValid s₀) : CurMoved s₀ s₁ := by
  have htail := layout.header_tail_sgrows
  rcases layout with
    ⟨xvals, sA, h1, hParams, sB, h2, hId, sC, h3,
     exitParams, sD, h4, exitId, sE, h5, postParams, sF, h6,
     postId, sG, h7, sH, h8, sI, h9, cvId, sJ, h10,
     bodyId, sK, h11, hX, sL, h12, sM, h13, sN, h14,
     bodyEnv, sO, h15, htr⟩
  have cs0G : CurSame s₀ sG :=
    ((((((CurSame.of_grows (Grows.of_liftO h1)).trans
      (CurSame.of_grows (Grows.of_mapM_freshVal h2))).trans
      (CurSame.of_newBlock h3)).trans
      (CurSame.of_grows (Grows.of_mapM_freshVal h4))).trans
      (CurSame.of_newBlock h5)).trans
      (CurSame.of_grows (Grows.of_mapM_freshVal h6))).trans
      (CurSame.of_newBlock h7)
  have hne : sG.fn.curId ≠ hId := by
    rw [cs0G.1, SGrowsAt.newBlock_id h3]
    have a0B : SGrowsAt s₀.fn.blocks.size s₀ sB :=
      (SGrowsAt.of_grows (N := s₀.fn.blocks.size) (Grows.of_liftO h1)).trans
        (SGrowsAt.of_grows (Grows.of_mapM_freshVal h2))
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hvalid a0B.size)
  have hmGI : CurMoved sG sI := curMoved_of_seal_move hne h8 h9
  have hm0I : CurMoved s₀ sI := cs0G.transMoved hmGI
  have a0B : SGrows s₀ sB :=
    (SGrowsAt.of_grows (N := s₀.fn.blocks.size) (Grows.of_liftO h1)).trans
      (SGrowsAt.of_grows (Grows.of_mapM_freshVal h2))
  have a0C := a0B.trans (SGrowsAt.of_newBlock h3)
  have a0D := a0C.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h4))
  have a0E := a0D.trans (SGrowsAt.of_newBlock h5)
  have a0F := a0E.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h6))
  have a0G := a0F.trans (SGrowsAt.of_newBlock h7)
  have a0H := a0G.trans (SGrowsAt.of_sealCur h8)
  have hheader : s₀.fn.blocks.size ≤ hId := by
    rw [SGrowsAt.newBlock_id h3]
    exact a0B.size
  have g0I : SGrows s₀ sI :=
    SGrowsAt.trans a0H
      (SGrowsAt.of_moveTo (N := s₀.fn.blocks.size) (Or.inl hheader) h9)
  exact hm0I.forward hvalid g0I htail

omit model in
theorem loopPostTail_fprefix {envP : Option VMap} {X : List Ident}
    {hId exitId : BlockId} {s s' : BState} {out renv : Option VMap}
    (h : (do
      if let some envP' := envP then
        let xvP ← edgeArgs envP' X
        sealCur (.jump ⟨hId, xvP⟩)
      moveTo exitId
      pure out) s = some (renv, s')) :
    FPrefix s.funcs.size s s' := by
  cases envP with
  | none =>
      obtain ⟨u, s1, h1, h2⟩ := M.bind_inv h
      obtain ⟨-, rfl⟩ := M.pure_inv h1
      obtain ⟨u', s2, h2, h3⟩ := M.bind_inv h2
      obtain ⟨-, rfl⟩ := M.pure_inv h3
      exact FPrefix.of_moveTo h2
  | some envP' =>
      obtain ⟨xv, s1, h1, h⟩ := M.bind_inv h
      obtain ⟨u, s2, h2, h⟩ := M.bind_inv h
      obtain ⟨u', s3, h3, h4⟩ := M.bind_inv h
      obtain ⟨-, rfl⟩ := M.pure_inv h4
      exact ((FPrefix.of_edgeArgs h1).trans (FPrefix.of_sealCur h2)).trans
        (FPrefix.of_moveTo h3)

/-- Loop simulation beginning at the already-bound header parameters.  The
`base` watermark precedes all three reserved parameter vectors, so a normal
result may bind post/exit parameters while still preserving the caller's
register file below `base`. -/
def LHOut (P : Prog) (f : Func) (rets : Option (List Ident)) (base : Nat)
    (sH s₁ : BState) (RH : Regs) (renv : Option VMap)
    (V' : VEnv yulD) (yst yst' : EvmState) (o : Outcome) : Prop :=
  match o with
  | .normal => ∃ (env' : VMap) (R₁ : Regs),
      renv = some env' ∧ Regs.BelowEq base RH R₁
        ∧ RegsFresh R₁ s₁.fn ∧ EnvOK (model := model) env' V' R₁
        ∧ env'.Unique
        ∧ SimS (model := model) P f sH.fn RH yst s₁.fn R₁ yst'
  | .halt => ExecFrom (model := model) P f sH.fn RH yst (.halt yst')
  | .leave => ∃ (rs : List Ident) (vals : List U256),
      rets = some rs
        ∧ YulSemantics.Forall₂ (fun x v => YulSemantics.VEnv.get V' x = some v) rs vals
        ∧ ExecFrom (model := model) P f sH.fn RH yst (.ret vals yst')
  | .break | .continue => False

/-- Prepend the preheader-to-header simulation to a loop result. -/
theorem LHOut.prefix {P : Prog} {f : Func} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {base : Nat} {s₀ sH s₁ : BState}
    {R₀ RH : Regs} {renv : Option VMap} {V' : VEnv yulD}
    {yst ystH yst' : EvmState} {o : Outcome}
    (hbase : s₀.fn.nextVal ≤ base)
    (hbelow : Regs.BelowEq s₀.fn.nextVal R₀ RH)
    (hfresh : RegsFresh R₀ s₀.fn)
    (hsim : SimS (model := model) P f s₀.fn R₀ yst sH.fn RH ystH)
    (h : LHOut (model := model) P f rets base sH s₁ RH renv
      V' ystH yst' o) :
    SOut (model := model) P f lctx rets s₀ s₁ R₀ renv
      V' yst yst' o := by
  cases o with
  | normal =>
      obtain ⟨env', R₁, hrenv, hbelow₁, hfr, henv, huniq, hsim₁⟩ := h
      have hbelowEnd := hbelow.trans (hbelow₁.mono hbase)
      have hleEnd : Regs.Le R₀ R₁ := by
        intro i v hi
        by_cases hilow : i < s₀.fn.nextVal
        · rw [hbelowEnd i hilow]
          exact hi
        · exact absurd hi (by rw [hfresh i (Nat.le_of_not_gt hilow)]; simp)
      exact ⟨env', R₁, hrenv, hleEnd, hbelowEnd,
        hfr, henv, huniq, hsim.trans hsim₁⟩
  | halt => exact hsim _ h
  | leave =>
      obtain ⟨rs, vals, hrets, hvals, hex⟩ := h
      exact ⟨rs, vals, hrets, hvals, hsim _ hex⟩
  | «break» => exact h.elim
  | «continue» => exact h.elim

/-- A source loop iteration cannot expose `break` or `continue`: both are
consumed by the loop rules themselves. -/
theorem loop_outcome_ssa {funs : YulSemantics.FunEnv yulD} {V : VEnv yulD}
    {yst : EvmState} {c : Expr Op} {post body : List (Stmt Op)}
    {V' : VEnv yulD} {yst' : EvmState} {o : Outcome}
    (h : YulSemantics.Step yulD funs V yst (.loop c post body)
      (.sres V' yst' o)) :
    o = .normal ∨ o = .halt ∨ o = .leave := by
  generalize hc : (YulSemantics.Code.loop c post body
    : YulSemantics.Code Op) = code at h
  generalize hr : (YulSemantics.Res.sres V' yst' o
    : YulSemantics.Res yulD) = res at h
  induction h generalizing V' yst' o <;> try cases hc
  case loopDone =>
    cases hr
    exact .inl rfl
  case loopCondHalt =>
    cases hr
    exact .inr (.inl rfl)
  case loopStep ihc ihbody ihpost ihrest =>
    exact ihrest rfl hr
  case loopPostHalt =>
    cases hr
    exact .inr (.inl rfl)
  case loopBreak =>
    cases hr
    exact .inl rfl
  case loopLeave =>
    cases hr
    exact .inr (.inr rfl)
  case loopBodyHalt =>
    cases hr
    exact .inr (.inl rfl)

/-- At a loop header, only its parameter vector may be bound among ids
reserved since the preheader watermark.  A back edge obtains such a file by
starting from the preheader file and rebinding exactly `hParams`; the live file
may contain more iteration temporaries and is reached later with `Exec.mono`. -/
def HeaderClean (base : Nat) (hParams : List ValId) (R : Regs) : Prop :=
  ∀ i, base ≤ i → i ∉ hParams → R i = none

/-- Rebinding the header parameter vector updates exactly the source variables
represented by the header map.  This packages the no-alias placement fact the
static layout establishes for its fresh parameter ids. -/
def HeaderRebind (envH : VMap) (X : List Ident) (hParams : List ValId)
    (V : VEnv yulD) (R : Regs) : Prop :=
  ∀ (vals : List U256) (W : VEnv yulD),
    X.length = vals.length →
    YulSemantics.VEnv.setMany V X vals = W →
    EnvOK (model := model) envH W (R.setMany hParams vals)

set_option maxHeartbeats 1000000 in
/-- Execute the loop preheader edge and bind the first header parameter
vector, establishing the iteration invariant expected by `LOut`. -/
theorem LoopLayout.enter {P : Prog} {f : Func} {fenv : FMap} {env : VMap}
    {rets : Option (List Ident)} {c : Expr Op} {post body : List (Stmt Op)}
    {s₀ s₁ : BState} {renv : Option VMap} {joins : List BlockId}
    {V : VEnv yulD} {R : Regs} {yst : EvmState}
    (layout : LoopLayout fenv env rets c post body s₀ s₁ renv)
    (henv : EnvOK (model := model) env V R) (_huniq : env.Unique)
    (hfr : RegsFresh R s₀.fn) (hvalid : CurValid s₀)
    (hp : ProtectedAt joins s₀.fn) (hcompl : Completes f s₁.fn joins) :
    ∃ RH : Regs,
      Regs.BelowEq s₀.fn.nextVal R RH ∧
      RegsFresh RH layout.sI.fn ∧
      EnvOK (model := model)
        (env.setMany (modifiedX env [post, body]) layout.hParams) V RH ∧
      HeaderClean layout.sA.fn.nextVal layout.hParams RH ∧
      HeaderRebind (model := model)
        (env.setMany (modifiedX env [post, body]) layout.hParams)
        (modifiedX env [post, body]) layout.hParams V RH ∧
      SimS (model := model) P f s₀.fn R yst layout.sI.fn RH yst := by
  have htail := layout.header_tail_sgrows
  rcases layout with
    ⟨xvals, sA, h1, hParams, sB, h2, hId, sC, h3,
     exitParams, sD, h4, exitId, sE, h5, postParams, sF, h6,
     postId, sG, h7, sH, h8, sI, h9, cvId, sJ, h10,
     bodyId, sK, h11, hX, sL, h12, sM, h13, sN, h14,
     bodyEnv, sO, h15, htr⟩
  simp only [] at htail ⊢
  obtain ⟨hsA, vals, hget, hvals⟩ := edgeArgs_ok henv h1
  subst sA
  obtain ⟨hlenH, hrangeH, hsB⟩ := M.mapM_freshVal_length h2
  have hndH : hParams.Nodup := by rw [hrangeH]; exact M.nodup_range' _ _
  have hnoneH : ∀ i ∈ hParams, R i = none := by
    intro i hi
    exact hfr i (by rw [hrangeH] at hi; exact (M.mem_range'_bounds hi).1)
  let RH := R.setMany hParams vals
  have hleH : Regs.Le R RH := Regs.Le.setMany hndH hnoneH
  have hbelowH : Regs.BelowEq s₀.fn.nextVal R RH := by
    exact Regs.BelowEq.setMany (fun i hi => by
      rw [hrangeH] at hi
      exact (M.mem_range'_bounds hi).1)
  have hgetH : RH.getMany hParams = some vals :=
    Regs.getMany_setMany_self hndH (hlenH.trans hvals.length_eq)
  have henvH : EnvOK (model := model)
      (env.setMany (modifiedX env [post, body]) hParams) V RH := by
    have he := EnvOK.setMany (xs := modifiedX env [post, body])
      (henv.mono hleH)
      (Regs.getMany_eq_some_iff.mp hgetH)
    rw [VEnv.setMany_self hvals] at he
    exact he
  have hcleanH : HeaderClean s₀.fn.nextVal hParams RH := by
    intro i hi hnot
    dsimp [RH]
    rw [Regs.setMany_other hnot]
    exact hfr i hi
  have hrebH : HeaderRebind (model := model)
      (env.setMany (modifiedX env [post, body]) hParams)
      (modifiedX env [post, body]) hParams V RH := by
    intro vals' W hlen' hset'
    have hle' : Regs.Le R (R.setMany hParams vals') :=
      Regs.Le.setMany hndH hnoneH
    have hget' : (R.setMany hParams vals').getMany hParams = some vals' :=
      Regs.getMany_setMany_self hndH (hlenH.trans hlen')
    have he := EnvOK.setMany (xs := modifiedX env [post, body])
      (henv.mono hle')
      (Regs.getMany_eq_some_iff.mp hget')
    dsimp [RH]
    rw [Regs.setMany_overwrite R hndH
      (hlenH.trans hvals.length_eq) (hlenH.trans hlen')]
    rwa [hset'] at he
  have g0B : SGrowsAt s₀.fn.blocks.size s₀ sB :=
    (SGrowsAt.of_grows (Grows.of_liftO h1)).trans
      (SGrowsAt.of_grows (Grows.of_mapM_freshVal h2))
  have g0C := g0B.trans (SGrowsAt.of_newBlock h3)
  have g0D := g0C.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h4))
  have g0E := g0D.trans (SGrowsAt.of_newBlock h5)
  have g0F := g0E.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h6))
  have g0G := g0F.trans (SGrowsAt.of_newBlock h7)
  have g0H := g0G.trans (SGrowsAt.of_sealCur h8)
  have hheader : s₀.fn.blocks.size ≤ hId := by
    rw [SGrowsAt.newBlock_id h3]
    exact g0B.size
  have g0I := g0H.trans (SGrowsAt.of_moveTo (Or.inl hheader) h9)
  have gBI : SGrowsAt 0 sB sI :=
    ((((((SGrowsAt.of_newBlock (N := 0) h3).trans
      (SGrowsAt.of_grows (Grows.of_mapM_freshVal h4))).trans
      (SGrowsAt.of_newBlock h5)).trans
      (SGrowsAt.of_grows (Grows.of_mapM_freshVal h6))).trans
      (SGrowsAt.of_newBlock h7)).trans
      (SGrowsAt.of_sealCur h8)).trans
      (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)
  have hendH : s₀.fn.nextVal + (modifiedX env [post, body]).length ≤
      sI.fn.nextVal := by
    simpa only [hsB] using gBI.nextVal
  have hfrH : RegsFresh RH sI.fn := by
    dsimp [RH]
    rw [hrangeH]
    exact hfr.setMany hendH
  have cs0G : CurSame s₀ sG :=
    ((((((CurSame.of_grows (Grows.of_liftO h1)).trans
      (CurSame.of_grows (Grows.of_mapM_freshVal h2))).trans
      (CurSame.of_newBlock h3)).trans
      (CurSame.of_grows (Grows.of_mapM_freshVal h4))).trans
      (CurSame.of_newBlock h5)).trans
      (CurSame.of_grows (Grows.of_mapM_freshVal h6))).trans
      (CurSame.of_newBlock h7)
  have hne : sG.fn.curId ≠ hId := by
    rw [cs0G.1, SGrowsAt.newBlock_id h3]
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hvalid g0B.size)
  have hpH : ProtectedAt joins sH.fn := ProtectedAt.forward hp g0H
  have hfinalH : CurFinal f sH.fn :=
    curFinal_of_move_sgrowsAt
      (by rw [(sealCur_cur h8).choose_spec.1, cs0G.1]; exact hvalid) h9
      (by simpa only [(sealCur_cur h8).choose_spec.1] using hne)
      hpH.away htail hcompl
  have hsealG : CurOK f sG.fn ⟨[], .jump ⟨hId, xvals⟩⟩ :=
    curOK_of_sealCur hfinalH h8
  have hcur0G : sG.fn.cur = s₀.fn.cur := by
    have hcurAB : sB.fn.cur = s₀.fn.cur := by rw [hsB]
    have hcurBC : sC.fn.cur = sB.fn.cur := by
      have hh := h3
      rw [M.newBlock_apply] at hh
      exact (congrArg (fun z => z.fn.cur) (M.some_pair_inj hh).2).symm
    have hcurCD : sD.fn.cur = sC.fn.cur := by
      obtain ⟨-, -, hsD⟩ := M.mapM_freshVal_length h4
      rw [hsD]
    have hcurDE : sE.fn.cur = sD.fn.cur := by
      have hh := h5
      rw [M.newBlock_apply] at hh
      exact (congrArg (fun z => z.fn.cur) (M.some_pair_inj hh).2).symm
    have hcurEF : sF.fn.cur = sE.fn.cur := by
      obtain ⟨-, -, hsF⟩ := M.mapM_freshVal_length h6
      rw [hsF]
    have hcurFG : sG.fn.cur = sF.fn.cur := by
      have hh := h7
      rw [M.newBlock_apply] at hh
      exact (congrArg (fun z => z.fn.cur) (M.some_pair_inj hh).2).symm
    exact hcurFG.trans (hcurEF.trans (hcurDE.trans
      (hcurCD.trans (hcurBC.trans hcurAB))))
  have hseal0 : CurOK f s₀.fn ⟨[], .jump ⟨hId, xvals⟩⟩ :=
    CurOK.back_of_cur_eq cs0G.1 hcur0G hsealG
  have cI : SGrowsAt 0 sC sI :=
    (((((SGrowsAt.of_grows (N := 0) (Grows.of_mapM_freshVal h4)).trans
      (SGrowsAt.of_newBlock h5)).trans
      (SGrowsAt.of_grows (Grows.of_mapM_freshVal h6))).trans
      (SGrowsAt.of_newBlock h7)).trans
      (SGrowsAt.of_sealCur h8)).trans
      (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h9)
  obtain ⟨hbI, hhbI, hbpI⟩ := cI.params hId
    ⟨hParams, [], .ret []⟩ (newBlock_target_get h3)
  obtain ⟨hbEnd, hhbEnd, hbpEnd⟩ :=
    htail.params hId hbI hhbI
  have hcurI : sI.fn.curId = hId := by
    rw [M.moveTo_apply] at h9
    exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h9).2).symm
  have hcurI0 : sI.fn.cur = [] := by
    rw [M.moveTo_apply] at h9
    simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h9).2
  have hlenEnd : hbEnd.params.length = vals.length := by
    rw [hbpEnd, hbpI]
    exact hlenH.trans hvals.length_eq
  have hsimH : SimS (model := model) P f s₀.fn R yst sI.fn RH yst := by
    intro res hex
    exact execFrom_jump hseal0 hget
      (jumpTo_of_completes hcompl hhbEnd hcurI hcurI0 hlenEnd (by
        simpa only [RH, hbpEnd, hbpI] using hex))
  exact ⟨RH, hbelowH, hfrH, henvH, hcleanH, hrebH, hsimH⟩

/-- The genuine loop-iteration induction clause is parametric in the register
file at the shared header.  This is the crucial difference from `SOut`: the
static `LoopLayout` is fixed, while a recursive source iteration may rebind the
header parameters to different values. -/
def LOut (P : Prog) (f : Func) (funs : YulSemantics.FunEnv yulD)
    (V : VEnv yulD) (yst : EvmState) (c : Expr Op)
    (post body : List (Stmt Op)) (V' : VEnv yulD) (yst' : EvmState)
    (o : Outcome) (doneFuncs : Array (Option Func)) : Prop :=
  ∀ (fenv : FMap) (env : VMap) (rets : Option (List Ident))
      (s₀ s₁ : BState) (renv : Option VMap) (joins : List BlockId)
      (layout : LoopLayout fenv env rets c post body s₀ s₁ renv),
    FEnvOK (model := model) P funs fenv → env.Unique →
    CtxVars none rets env → CurValid s₀ →
    ProtectedAt joins s₀.fn → Completes f s₁.fn joins → CurPlaced f s₁.fn →
    (renv = none → CurFinal f s₁.fn) →
    ∀ (done : BState) (owned : List FuncId),
      done.funcs = doneFuncs →
      (∀ i : FuncId, i ∈ owned → i < s₀.funcs.size) →
      FOwned owned s₁ done →
    ∀ (RH : Regs),
      EnvOK (model := model)
          (env.setMany (modifiedX env [post, body]) layout.hParams) V RH →
      RegsFresh RH layout.sI.fn →
      HeaderClean layout.sA.fn.nextVal layout.hParams RH →
      HeaderRebind (model := model)
        (env.setMany (modifiedX env [post, body]) layout.hParams)
        (modifiedX env [post, body]) layout.hParams V RH →
      LHOut (model := model) P f rets layout.sA.fn.nextVal layout.sI s₁ RH
        renv V' yst yst' o

/-- **The induction motive** for the construction simulation: what a source
derivation of each syntactic class means on the SSA side, against *any*
construction run that accepts the same syntax. The SSA analogue of
`SimAsm.Motive`.

Shape notes:

* the expression class carries three clauses, for the construction's three
  expression entry points — `trExpr` (one value, `EOut`), `trExprN` (the
  `let`/`assign` right-hand side, `EOutL`), and the zero-destination
  `exprStmt` path (`EStmtOut`);
* statement clauses additionally require `VMap.Unique` at entry and return it
  in normal `SOut`; declaration gates establish it and `seqCons` threads it;
* the placement hypotheses are `Completes f s₁.fn` (the finished function
  completes the state the fragment ends in — travels inwards by
  `SGrowsAt.completes_of`) and, **only when the fragment diverts**,
  `CurFinal f s₁.fn`. The conditioning on `renv = none` matters: a fragment that
  falls through leaves its current block *unsealed*, so `CurFinal` is false
  there — and unnecessary, since only a diverting statement needs its own
  sealed block to be final.
* `doneFuncs` and its `FuncTableComplete` witness are fixed across the whole
  source induction.  Intermediate scopes may still contain pending `none`
  slots; once an `allocScope`/`trFunc` inversion shows that a filled slot
  survives into `doneFuncs`, `FuncTableComplete.get` places it in `P.funcs`.

The `.loop` clause is deliberately `True` for now: the loop-iteration class
needs the header/exit/post choreography, which is the round that attacks the
`for` family. Every other clause is final. -/
def Motive (P : Prog) (f : Func) (funs : YulSemantics.FunEnv yulD)
    (V : VEnv yulD) (yst : EvmState)
    (doneFuncs : Array (Option Func))
    (_hfuncs : FuncTableComplete P doneFuncs) :
    YulSemantics.Code Op → YulSemantics.Res yulD → Prop
  | .expr e, .eres (.vals vs yst') =>
      (∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState) (i : ValId)
          (v : U256) (joins : List BlockId),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        RegsFresh R s₀.fn → ProtectedAt joins s₀.fn →
        Completes f s₁.fn joins → CurPlaced f s₁.fn → vs = [v] →
        trExpr fenv env e s₀ = some (i, s₁) →
        EOut (model := model) P f s₀ s₁ R i v yst yst')
      ∧ (∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState) (n : Nat)
          (ids : List ValId) (joins : List BlockId),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        RegsFresh R s₀.fn → ProtectedAt joins s₀.fn →
        Completes f s₁.fn joins → CurPlaced f s₁.fn →
        vs.length = n →
        trExprN fenv env n e s₀ = some (ids, s₁) →
        EOutL (model := model) P f s₀ s₁ R ids vs yst yst')
      ∧ (vs = [] → EStmtOut (model := model) P f funs V yst e V yst' .normal)
  | .expr e, .eres (.halt yst') =>
      (∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState) (i : ValId)
          (joins : List BlockId),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        RegsFresh R s₀.fn → ProtectedAt joins s₀.fn →
        Completes f s₁.fn joins → CurPlaced f s₁.fn →
        trExpr fenv env e s₀ = some (i, s₁) →
        EOutHalt (model := model) P f s₀ R yst yst')
      ∧ (∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState) (n : Nat)
          (ids : List ValId) (joins : List BlockId),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        RegsFresh R s₀.fn → ProtectedAt joins s₀.fn →
        Completes f s₁.fn joins → CurPlaced f s₁.fn →
        trExprN fenv env n e s₀ = some (ids, s₁) →
        EOutHalt (model := model) P f s₀ R yst yst')
      ∧ EStmtOut (model := model) P f funs V yst e V yst' .halt
  | .args es, .eres (.vals vs yst') =>
      ∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState)
        (ids : List ValId) (joins : List BlockId),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        RegsFresh R s₀.fn → ProtectedAt joins s₀.fn →
        Completes f s₁.fn joins → CurPlaced f s₁.fn →
        trArgs fenv env es s₀ = some (ids, s₁) →
        EOutL (model := model) P f s₀ s₁ R ids vs yst yst'
  | .args es, .eres (.halt yst') =>
      ∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState)
        (ids : List ValId) (joins : List BlockId),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        RegsFresh R s₀.fn → ProtectedAt joins s₀.fn →
        Completes f s₁.fn joins → CurPlaced f s₁.fn →
        trArgs fenv env es s₀ = some (ids, s₁) →
        EOutHalt (model := model) P f s₀ R yst yst'
  | .stmt st, .sres V' yst' o =>
      ∀ (fenv : FMap) (env : VMap) (R : Regs) (lctx : Option LoopCtx)
        (rets : Option (List Ident)) (s₀ s₁ : BState) (renv : Option VMap)
        (joins : List BlockId),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        env.Unique → CtxVars lctx rets env →
        RegsFresh R s₀.fn → CurValid s₀ →
        ProtectedAt joins s₀.fn → Completes f s₁.fn joins → CurPlaced f s₁.fn →
        (renv = none → CurFinal f s₁.fn) →
        ∀ (done : BState) (owned : List FuncId),
        done.funcs = doneFuncs →
        (∀ i : FuncId, i ∈ owned → i < s₀.funcs.size) →
        FOwned owned s₁ done →
        trStmt fenv env lctx rets st s₀ = some (renv, s₁) →
        SOut (model := model) P f lctx rets s₀ s₁ R renv V' yst yst' o
  | .stmts ss, .sres V' yst' o =>
      ∀ (fenv : FMap) (env : VMap) (R : Regs) (lctx : Option LoopCtx)
        (rets : Option (List Ident)) (s₀ s₁ : BState) (renv : Option VMap)
        (joins : List BlockId),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        env.Unique → CtxVars lctx rets env →
        RegsFresh R s₀.fn → CurValid s₀ →
        ProtectedAt joins s₀.fn → Completes f s₁.fn joins → CurPlaced f s₁.fn →
        (renv = none → CurFinal f s₁.fn) →
        ∀ (done : BState) (owned : List FuncId),
        done.funcs = doneFuncs →
        (∀ i : FuncId, i ∈ stmtFuncIds fenv ss ++ owned →
          i < s₀.funcs.size) →
        (∀ i : FuncId, i ∈ stmtFuncIds fenv ss →
          s₀.funcs[i]? = some none) →
        (stmtFuncIds fenv ss ++ owned).Nodup →
        FOwned owned s₁ done →
        trStmts fenv env lctx rets false ss s₀ = some (renv, s₁) →
        SOut (model := model) P f lctx rets s₀ s₁ R renv V' yst yst' o
  | .loop c post body, .sres V' yst' o =>
      LOut (model := model) P f funs V yst c post body V' yst' o doneFuncs
  | _, _ => True

end Semantics
end YulEvmCompiler.SsaCfg
