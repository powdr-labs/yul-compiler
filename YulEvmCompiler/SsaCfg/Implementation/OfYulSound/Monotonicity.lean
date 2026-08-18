import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.Frames
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.OfYulSound.Monotonicity

The statement-class monotonicity and function-table frame inductions.

The two big mutual inductions over the translation functions
(`trStmt_grows`/`trScope_grows`/`trStmts_grows`/`trCases_grows`/`trFunc_grows`
and `trFrames_fprefix`), plus the corollaries that specialise them to a single
statement class and the `trStmts_*` ownership/survival facts they yield.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics (Ident Literal Expr Stmt VEnv Outcome)
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal evmWithExternal)

section Semantics

variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates YulSemantics.EVM.ExternalGas.any

/-! ### The statement-class monotonicity induction

One `trStmt.induct` over the construction's five mutually recursive functions.
Every case is a chain of the `SGrowsAt` primitive lemmas above, at the fixed
base `N = ` the case's incoming block count; sub-fragments are weakened to that
base with `SGrowsAt.mono`. -/

/-- Motive for `trFunc`: the per-function state is saved and restored, so only
the function table moves. -/
def FuncGrows (fenv : FMap) (ps rs : List Ident) (body : List (Stmt Op)) : Prop :=
  ∀ (s : BState) (g : Func) (s' : BState),
    trFunc fenv ps rs body s = some (g, s') → s'.fn = s.fn ∧ FGrows s s'

/-- Motive for `trScope`. -/
def ScopeGrows (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (body : List (Stmt Op)) : Prop :=
  ∀ (s : BState) (r : Option VMap) (s' : BState),
    trScope fenv env lctx rets body s = some (r, s') → SGrows s s'

/-- Motive for `trStmts`. -/
def StmtsGrows (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (d : Bool) (ss : List (Stmt Op)) : Prop :=
  ∀ (s : BState) (r : Option VMap) (s' : BState),
    trStmts fenv env lctx rets d ss s = some (r, s') → SGrows s s'

/-- Motive for `trStmt`. -/
def StmtGrows (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (st : Stmt Op) : Prop :=
  ∀ (s : BState) (r : Option VMap) (s' : BState),
    trStmt fenv env lctx rets st s = some (r, s') → SGrows s s'

/-- Motive for `trCases`. -/
def CasesGrows (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (_sv : ValId) (_X : List Ident)
    (_joinId : BlockId) (cases : List (Literal × List (Stmt Op)))
    (dflt : Option (List (Stmt Op))) : Prop :=
  ∀ (sv : ValId) (X : List Ident) (joinId : BlockId) (s : BState) (u : Unit)
    (s' : BState),
    trCases fenv env lctx rets sv X joinId cases dflt s = some (u, s') →
      SGrows s s'

omit model in
/-- **Statement translation only allocates and seals what it reserved.**

One `trFunc.mutual_induct` over the construction's five mutually recursive
functions, proving the five `*Grows` motives simultaneously.  The five
per-function `.induct` principles the `mutual` block generates share a single
hypothesis list, and `mutual_induct` discharges that same list once for the
whole conjunction, so the 29-case script below is written -- and elaborated --
only once.  `trFunc_grows`/`trScope_grows`/`trStmts_grows`/`trStmt_grows`/
`trCases_grows` are its projections. -/
theorem trAll_grows :
    (∀ (fenv : FMap) (ps rs : List Ident) (body : List (Stmt Op)),
        FuncGrows fenv ps rs body) ∧
    (∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
      (rets : Option (List Ident)) (body : List (Stmt Op)),
        ScopeGrows fenv env lctx rets body) ∧
    (∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
      (rets : Option (List Ident)) (d : Bool) (ss : List (Stmt Op)),
        StmtsGrows fenv env lctx rets d ss) ∧
    (∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
      (rets : Option (List Ident)) (st : Stmt Op),
        StmtGrows fenv env lctx rets st) ∧
    (∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
      (rets : Option (List Ident)) (sv : ValId) (X : List Ident)
      (joinId : BlockId) (cases : List (Literal × List (Stmt Op)))
      (dflt : Option (List (Stmt Op))),
        CasesGrows fenv env lctx rets sv X joinId cases dflt) := by
  refine trFunc.mutual_induct FuncGrows ScopeGrows StmtsGrows StmtGrows CasesGrows
    ?trFunc ?trScope ?stmtsNil ?stmtsFunDef ?stmtsSkip ?stmtsCons
    ?block ?funDef ?letNoneBad ?letNone ?letSomeBad ?letSome ?assignBad ?assign
    ?cond ?switch ?forLoop ?exprBuiltin ?exprCall ?exprBad
    ?breakNone ?breakSome ?contNone ?contSome ?leaveNone ?leaveSome
    ?casesNilNone ?casesNilSome ?casesCons
  case trFunc =>
    intro fenv ps rs body ih s g s' h
    unfold trFunc at h
    obtain ⟨saved, s1, h1, h⟩ := M.bind_inv h
    have hsv : saved = s.fn := by
      rw [M.getFn_apply] at h1; exact (M.some_pair_inj h1).1.symm
    obtain ⟨u2, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨entry, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨pids, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨rids, s6, h6, h⟩ := M.bind_inv h
    have f1 : FGrows s s2 :=
      FGrows.trans (FGrows.of_getFn h1) (FGrows.of_setFn h2)
    have f2 : FGrows s s4 :=
      FGrows.trans f1 (FGrows.trans (FGrows.of_newBlock h3) (FGrows.of_moveTo h4))
    have f3 : FGrows s s6 :=
      FGrows.trans f2 (FGrows.trans
        (FGrows.of_grows (Grows.of_mapM_freshVal h5))
        (FGrows.of_grows (Grows.of_mapM_constZero h6)))
    -- the closing `getFn; setFn saved; pure` restores the caller's `fn`
    have hfin : ∀ (sk : BState), FGrows s sk →
        (getFn >>= fun done => setFn saved >>= fun _ =>
          (pure { params := pids, nrets := rs.length, entry := entry,
                  blocks := done.blocks } : M Func)) sk = some (g, s') →
        s'.fn = s.fn ∧ FGrows s s' := by
      intro sk hk hh
      obtain ⟨done, sa, ha, hh⟩ := M.bind_inv hh
      rw [M.getFn_apply] at ha
      obtain ⟨-, hd2⟩ := M.some_pair_inj ha
      obtain ⟨ub, sb, hb2, hc2⟩ := M.bind_inv hh
      rw [M.setFn_apply] at hb2
      obtain ⟨-, hb3⟩ := M.some_pair_inj hb2
      obtain ⟨-, hc3⟩ := M.pure_inv hc2
      refine ⟨?_, ?_⟩
      · rw [hc3, ← hb3, hsv]
      · rw [FGrows, hc3, ← hb3]
        exact hd2 ▸ hk
    by_cases hg : (!decide (ps ++ rs).Nodup) = true
    · rw [if_pos hg] at h
      obtain ⟨u7, s7, h7, -⟩ := M.bind_inv h
      exact absurd h7 (by simp [reject])
    · rw [if_neg hg] at h
      obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
      obtain ⟨renv, s8, h8, h⟩ := M.bind_inv h
      have f4 : FGrows s s8 :=
        FGrows.trans f3 (FGrows.trans (FGrows.of_pure h7)
          ((ih pids rids s7 renv s8 h8).funcsSize))
      cases renv with
      | none =>
        obtain ⟨ua, sa, ha, hh⟩ := M.bind_inv h
        exact hfin sa (FGrows.trans f4 (FGrows.of_pure ha)) hh
      | some envEnd =>
        obtain ⟨vals, sa, ha, hh⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb2, hh⟩ := M.bind_inv hh
        exact hfin sb (FGrows.trans f4 (FGrows.trans (FGrows.of_liftO ha)
          (FGrows.of_sealCur hb2))) hh
  case trScope =>
    intro fenv env lctx rets body ih s r s' h
    rw [trScope] at h
    obtain ⟨scope, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨renv, s₂, h2, h3⟩ := M.bind_inv h
    have g1 : SGrows s s₁ := allocScope_sgrows h1
    have g2 : SGrows s₁ s₂ := ih scope s₁ renv s₂ h2
    refine (g1.trans g2).trans ?_
    cases renv with
    | none => exact SGrowsAt.of_pure h3
    | some e => exact SGrowsAt.of_pure h3
    
  case stmtsNil =>
    intro fenv env lctx rets d s r s' h
    rw [trStmts] at h
    exact SGrowsAt.of_pure h
  case stmtsFunDef =>
    intro fenv env lctx rets d n ps rs fbody rest ihf ihr s r s' h
    rw [trStmts] at h
    obtain ⟨fid, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨g, s₂, h2, h⟩ := M.bind_inv h
    obtain ⟨u, s₃, h3, h4⟩ := M.bind_inv h
    obtain ⟨hfn, hfg⟩ := ihf s₁ g s₂ h2
    exact (((SGrows.trans (SGrowsAt.of_liftO h1)
      (SGrowsAt.of_funcsOnly hfn hfg)).trans
        (SGrowsAt.of_fillFunc h3)).trans (ihr s₃ r s' h4))
  case stmtsSkip =>
    intro fenv env lctx rets st rest hnf ih s r s' h
    rw [trStmts] at h
    · split at h
      · exact ih s r s' h
      · rename_i hc; exact absurd rfl hc
    · exact hnf
  case stmtsCons =>
    intro fenv env lctx rets d st rest hnf hd ih4 ih3n ih3t s r s' h
    rw [trStmts] at h
    · rw [if_neg hd] at h
      obtain ⟨renv, s₁, h1, h2⟩ := M.bind_inv h
      have g1 : SGrows s s₁ := ih4 s renv s₁ h1
      cases renv with
      | some env' => exact SGrows.trans g1 (ih3n env' s₁ r s' h2)
      | none => exact SGrows.trans g1 (ih3t s₁ r s' h2)
    · exact hnf
  case block =>
    intro fenv env lctx rets body ih s r s' h
    rw [trStmt] at h
    exact ih s r s' h
  case funDef =>
    intro fenv env lctx rets name ps rs body s r s' h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case letNoneBad =>
    intro fenv env lctx rets vars hgate s r s' h
    rw [trStmt] at h
    rw [if_pos hgate] at h
    obtain ⟨u, s₁, h1, -⟩ := M.bind_inv h
    exact absurd h1 (by simp [reject])
  case letNone =>
    intro fenv env lctx rets vars hgate s r s' h
    rw [trStmt] at h
    rw [if_neg hgate] at h
    obtain ⟨u, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_pure h1)
      (SGrows.trans (SGrows.of_grows (Grows.of_mapM_constZero h2))
        (SGrowsAt.of_pure h3))
  case letSomeBad =>
    intro fenv env lctx rets vars e hgate s r s' h
    rw [trStmt] at h
    rw [if_pos hgate] at h
    obtain ⟨u, s₁, h1, -⟩ := M.bind_inv h
    exact absurd h1 (by simp [reject])
  case letSome =>
    intro fenv env lctx rets vars e hgate s r s' h
    rw [trStmt] at h
    rw [if_neg hgate] at h
    obtain ⟨u, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_pure h1)
      (SGrows.trans (SGrows.of_grows (trExprN_grows h2)) (SGrowsAt.of_pure h3))
  case assignBad =>
    intro fenv env lctx rets vars e hgate s r s' h
    rw [trStmt] at h
    rw [if_pos hgate] at h
    obtain ⟨u, s₁, h1, -⟩ := M.bind_inv h
    exact absurd h1 (by simp [reject])
  case assign =>
    intro fenv env lctx rets vars e hgate s r s' h
    rw [trStmt] at h
    rw [if_neg hgate] at h
    obtain ⟨u, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_pure h1)
      (SGrows.trans (SGrows.of_grows (trExprN_grows h2)) (SGrowsAt.of_pure h3))
  case cond =>
    intro fenv env lctx rets c body ih s r s' h
    rw [trStmt] at h
    obtain ⟨cv, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨xvals, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨bodyId, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨joinParams, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨joinId, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨u6, s6, h6, h⟩ := M.bind_inv h
    obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
    obtain ⟨renv, s8, h8, h⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 :=
      SGrowsAt.of_grows (trExpr_grows c fenv env s s1 cv h1)
    have a2 := a1.trans (SGrowsAt.of_edgeArgs h2)
    have a3 := a2.trans (SGrowsAt.of_newBlock h3)
    have a4 := a3.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h4))
    have a5 := a4.trans (SGrowsAt.of_newBlock h5)
    have a6 := a5.trans (SGrowsAt.of_sealCur h6)
    have hbody : s.fn.blocks.size ≤ bodyId := by
      rw [SGrowsAt.newBlock_id h3]; exact a2.size
    have hjoin : s.fn.blocks.size ≤ joinId := by
      rw [SGrowsAt.newBlock_id h5]; exact a4.size
    have a7 := a6.trans (SGrowsAt.of_moveTo (Or.inl hbody) h7)
    have a8 := a7.trans ((ih s7 renv s8 h8).mono a7.size)
    refine a8.trans ?_
    cases renv with
    | none =>
      obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, hc2⟩ := M.bind_inv h
      exact (SGrowsAt.of_pure ha).trans
        ((SGrowsAt.of_moveTo (Or.inl hjoin) hb2).trans (SGrowsAt.of_pure hc2))
    | some env' =>
      obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
      obtain ⟨uc, sc, hc2, hd2⟩ := M.bind_inv h
      exact (SGrowsAt.of_edgeArgs ha).trans
        ((SGrowsAt.of_sealCur hb2).trans
          ((SGrowsAt.of_moveTo (Or.inl hjoin) hc2).trans (SGrowsAt.of_pure hd2)))
  case switch =>
    intro fenv env lctx rets c cases dflt ih s r s' h
    unfold trStmt at h
    obtain ⟨sv, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨joinParams, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨joinId, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨u5, s5, h5, h6⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 :=
      SGrowsAt.of_grows (trExpr_grows c fenv env s s1 sv h1)
    have a2 := a1.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h2))
    have a3 := a2.trans (SGrowsAt.of_newBlock h3)
    have hjoin : s.fn.blocks.size ≤ joinId := by
      rw [SGrowsAt.newBlock_id h3]; exact a2.size
    have a4 := a3.trans ((ih 0 0 _ _ _ s3 u4 s4 h4).mono a3.size)
    exact (a4.trans (SGrowsAt.of_moveTo (Or.inl hjoin) h5)).trans
      (SGrowsAt.of_pure h6)
  case forLoop =>
    intro fenv env lctx rets init c post body ihInit ihBody ihPost s r s' h
    unfold trStmt at h
    obtain ⟨scope, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨rinit, s2, h2, h⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 := allocScope_sgrows h1
    have a2 := a1.trans ((ihInit scope s1 rinit s2 h2).mono a1.size)
    cases rinit with
    | none => exact a2.trans (SGrowsAt.of_pure h)
    | some envI =>
      obtain ⟨xvals, s3, h3, h⟩ := M.bind_inv h
      obtain ⟨hParams, s4, h4, h⟩ := M.bind_inv h
      obtain ⟨hId, s5, h5, h⟩ := M.bind_inv h
      obtain ⟨exitParams, s6, h6, h⟩ := M.bind_inv h
      obtain ⟨exitId, s7, h7, h⟩ := M.bind_inv h
      obtain ⟨postParams, s8, h8, h⟩ := M.bind_inv h
      obtain ⟨postId, s9, h9, h⟩ := M.bind_inv h
      obtain ⟨u10, s10, h10, h⟩ := M.bind_inv h
      obtain ⟨u11, s11, h11, h⟩ := M.bind_inv h
      obtain ⟨cv, s12, h12, h⟩ := M.bind_inv h
      obtain ⟨bodyId, s13, h13, h⟩ := M.bind_inv h
      obtain ⟨hX, s14, h14, h⟩ := M.bind_inv h
      obtain ⟨u15, s15, h15, h⟩ := M.bind_inv h
      obtain ⟨u16, s16, h16, h⟩ := M.bind_inv h
      obtain ⟨renvB, s17, h17, h⟩ := M.bind_inv h
      have a3 := a2.trans (SGrowsAt.of_edgeArgs h3)
      have a4 := a3.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h4))
      have a5 := a4.trans (SGrowsAt.of_newBlock h5)
      have a6 := a5.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h6))
      have a7 := a6.trans (SGrowsAt.of_newBlock h7)
      have a8 := a7.trans (SGrowsAt.of_grows (Grows.of_mapM_freshVal h8))
      have a9 := a8.trans (SGrowsAt.of_newBlock h9)
      have a10 := a9.trans (SGrowsAt.of_sealCur h10)
      have hhdr : s.fn.blocks.size ≤ hId := by
        rw [SGrowsAt.newBlock_id h5]; exact a4.size
      have hexit : s.fn.blocks.size ≤ exitId := by
        rw [SGrowsAt.newBlock_id h7]; exact a6.size
      have hpost : s.fn.blocks.size ≤ postId := by
        rw [SGrowsAt.newBlock_id h9]; exact a8.size
      have a11 := a10.trans (SGrowsAt.of_moveTo (Or.inl hhdr) h11)
      have a12 := a11.trans (SGrowsAt.of_grows
        (trExpr_grows c (scope :: fenv) _ s11 s12 cv h12))
      have a13 := a12.trans (SGrowsAt.of_newBlock h13)
      have a14 := a13.trans (SGrowsAt.of_edgeArgs h14)
      have a15 := a14.trans (SGrowsAt.of_sealCur h15)
      have hbody : s.fn.blocks.size ≤ bodyId := by
        rw [SGrowsAt.newBlock_id h13]; exact a12.size
      have a16 := a15.trans (SGrowsAt.of_moveTo (Or.inl hbody) h16)
      have a17 := a16.trans
        ((ihBody scope envI hParams exitId postId s16 renvB s17 h17).mono a16.size)
      -- the `post` scope and the loop exit, under both `if let` branches
      cases renvB with
      | none =>
        obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
        obtain ⟨renvP, sc, hc2, h⟩ := M.bind_inv h
        have b1 := a17.trans (SGrowsAt.of_pure ha)
        have b2 := b1.trans (SGrowsAt.of_moveTo (Or.inl hpost) hb2)
        have b3 := b2.trans
          ((ihPost scope envI postParams sb renvP sc hc2).mono b2.size)
        cases renvP with
        | none =>
          obtain ⟨ud, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, hf⟩ := M.bind_inv h
          exact ((b3.trans (SGrowsAt.of_pure hd)).trans
            (SGrowsAt.of_moveTo (Or.inl hexit) he)).trans (SGrowsAt.of_pure hf)
        | some envP' =>
          obtain ⟨xvP, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, h⟩ := M.bind_inv h
          obtain ⟨uf, sf, hf, hg2⟩ := M.bind_inv h
          exact (((b3.trans (SGrowsAt.of_edgeArgs hd)).trans
            (SGrowsAt.of_sealCur he)).trans
              (SGrowsAt.of_moveTo (Or.inl hexit) hf)).trans (SGrowsAt.of_pure hg2)
      | some envB =>
        obtain ⟨xvB, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ua', sa', ha', h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
        obtain ⟨renvP, sc, hc2, h⟩ := M.bind_inv h
        have b0 := a17.trans (SGrowsAt.of_edgeArgs ha)
        have b1 := b0.trans (SGrowsAt.of_sealCur ha')
        have b2 := b1.trans (SGrowsAt.of_moveTo (Or.inl hpost) hb2)
        have b3 := b2.trans
          ((ihPost scope envI postParams sb renvP sc hc2).mono b2.size)
        cases renvP with
        | none =>
          obtain ⟨ud, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, hf⟩ := M.bind_inv h
          exact ((b3.trans (SGrowsAt.of_pure hd)).trans
            (SGrowsAt.of_moveTo (Or.inl hexit) he)).trans (SGrowsAt.of_pure hf)
        | some envP' =>
          obtain ⟨xvP, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, h⟩ := M.bind_inv h
          obtain ⟨uf, sf, hf, hg2⟩ := M.bind_inv h
          exact (((b3.trans (SGrowsAt.of_edgeArgs hd)).trans
            (SGrowsAt.of_sealCur he)).trans
              (SGrowsAt.of_moveTo (Or.inl hexit) hf)).trans (SGrowsAt.of_pure hg2)
  case exprBuiltin =>
    intro fenv env lctx rets op args s r s' h
    rw [trStmt] at h
    obtain ⟨as, s₁, h1, h⟩ := M.bind_inv h
    refine SGrows.trans (SGrows.of_grows (trArgs_grows args fenv env s s₁ as h1)) ?_
    by_cases hop : isHaltingOp op = true
    · rw [if_pos hop] at h
      obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
      exact SGrows.trans (SGrowsAt.of_sealCur h2) (SGrowsAt.of_pure h3)
    · rw [if_neg hop] at h
      obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
      exact SGrows.trans (SGrows.of_grows (Grows.of_emit h2)) (SGrowsAt.of_pure h3)
  case exprCall =>
    intro fenv env lctx rets fn args s r s' h
    rw [trStmt] at h
    obtain ⟨as, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨fid, s₂, h2, h⟩ := M.bind_inv h
    obtain ⟨u, s₃, h3, h4⟩ := M.bind_inv h
    exact SGrows.trans (SGrows.of_grows (trArgs_grows args fenv env s s₁ as h1))
      (SGrows.trans (SGrowsAt.of_liftO h2)
        (SGrows.trans (SGrows.of_grows (Grows.of_emit h3)) (SGrowsAt.of_pure h4)))
  case exprBad =>
    intro fenv env lctx rets e hnb hnc s r s' h
    rw [trStmt] at h
    · exact absurd h (by simp [reject])
    · exact hnb
    · exact hnc
  case breakNone =>
    intro fenv env rets s r s' h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case breakSome =>
    intro fenv env rets l s r s' h
    rw [trStmt] at h
    obtain ⟨vals, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_edgeArgs h1)
      (SGrows.trans (SGrowsAt.of_sealCur h2) (SGrowsAt.of_pure h3))
  case contNone =>
    intro fenv env rets s r s' h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case contSome =>
    intro fenv env rets l s r s' h
    rw [trStmt] at h
    obtain ⟨vals, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_edgeArgs h1)
      (SGrows.trans (SGrowsAt.of_sealCur h2) (SGrowsAt.of_pure h3))
  case leaveNone =>
    intro fenv env lctx s r s' h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case leaveSome =>
    intro fenv env lctx rs s r s' h
    rw [trStmt] at h
    obtain ⟨vals, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_edgeArgs h1)
      (SGrows.trans (SGrowsAt.of_sealCur h2) (SGrowsAt.of_pure h3))
  case casesNilNone =>
    intro fenv env lctx rets _sv _X _joinId sv X joinId s u s' h
    rw [trCases] at h
    obtain ⟨xvals, s₁, h1, h2⟩ := M.bind_inv h
    exact SGrows.trans (SGrowsAt.of_edgeArgs h1) (SGrowsAt.of_sealCur h2)
  case casesNilSome =>
    intro fenv env lctx rets _sv _X _joinId dbody ih sv X joinId s u s' h
    rw [trCases] at h
    obtain ⟨renv, s₁, h1, h2⟩ := M.bind_inv h
    refine SGrows.trans (ih s renv s₁ h1) ?_
    cases renv with
    | none => exact SGrowsAt.of_pure h2
    | some env' =>
      obtain ⟨xv, s₂, h3, h4⟩ := M.bind_inv h2
      exact SGrows.trans (SGrowsAt.of_edgeArgs h3) (SGrowsAt.of_sealCur h4)
  case casesCons =>
    intro fenv env lctx rets _sv _X _joinId lit cbody restCases dflt ihc ihr
      sv X joinId s u s' h
    rw [trCases] at h
    obtain ⟨t, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨u2, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨e, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨caseId, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨nextId, s6, h6, h⟩ := M.bind_inv h
    obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
    obtain ⟨u8, s8, h8, h⟩ := M.bind_inv h
    obtain ⟨renv, s9, h9, h⟩ := M.bind_inv h
    have a1 : SGrowsAt s.fn.blocks.size s s1 :=
      SGrowsAt.of_grows (Grows.of_freshVal h1)
    have a2 := a1.trans (SGrowsAt.of_grows (Grows.of_emit h2))
    have a3 := a2.trans (SGrowsAt.of_grows (Grows.of_freshVal h3))
    have a4 := a3.trans (SGrowsAt.of_grows (Grows.of_emit h4))
    have a5 := a4.trans (SGrowsAt.of_newBlock h5)
    have a6 := a5.trans (SGrowsAt.of_newBlock h6)
    have a7 := a6.trans (SGrowsAt.of_sealCur h7)
    have hcase : s.fn.blocks.size ≤ caseId := by
      rw [SGrowsAt.newBlock_id h5]; exact a4.size
    have hnext : s.fn.blocks.size ≤ nextId := by
      rw [SGrowsAt.newBlock_id h6]; exact a5.size
    have a8 := a7.trans (SGrowsAt.of_moveTo (Or.inl hcase) h8)
    have a9 := a8.trans ((ihc s8 renv s9 h9).mono a8.size)
    refine a9.trans ?_
    cases renv with
    | none =>
      obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, hc2⟩ := M.bind_inv h
      refine (SGrowsAt.of_pure ha).trans
        ((SGrowsAt.of_moveTo (Or.inl hnext) hb2).trans ?_)
      exact ((ihr sv X joinId sb u s' hc2).mono
        (Nat.le_trans (Nat.le_trans a9.size (SGrowsAt.of_pure (N := 0) ha).size)
          (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) hb2).size))
    | some env' =>
      obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
      obtain ⟨uc, sc, hc2, hd2⟩ := M.bind_inv h
      refine (SGrowsAt.of_edgeArgs ha).trans
        ((SGrowsAt.of_sealCur hb2).trans
          ((SGrowsAt.of_moveTo (Or.inl hnext) hc2).trans ?_))
      exact ((ihr sv X joinId sc u s' hd2).mono
        (Nat.le_trans (Nat.le_trans (Nat.le_trans a9.size
          (SGrowsAt.of_edgeArgs (N := 0) ha).size)
            (SGrowsAt.of_sealCur (N := 0) hb2).size)
          (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) hc2).size))

/-! ### The five statement-class projections

Each is the corresponding conjunct of `trAll_grows`; the statements are the
ones the rest of the development consumes. -/

omit model in
/-- Function translation leaves the caller's function table in place and only
grows the reserved slots. -/
theorem trFunc_grows : ∀ (fenv : FMap) (ps rs : List Ident) (body : List (Stmt Op)),
    FuncGrows fenv ps rs body :=
  trAll_grows.1

omit model in
/-- Scope translation only allocates and seals what it reserved. -/
theorem trScope_grows : ∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (body : List (Stmt Op)),
    ScopeGrows fenv env lctx rets body :=
  trAll_grows.2.1

omit model in
/-- Statement-list translation only allocates and seals what it reserved. -/
theorem trStmts_grows : ∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (d : Bool) (ss : List (Stmt Op)),
    StmtsGrows fenv env lctx rets d ss :=
  trAll_grows.2.2.1

omit model in
/-- Statement translation only allocates and seals what it reserved. -/
theorem trStmt_grows : ∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (st : Stmt Op), StmtGrows fenv env lctx rets st :=
  trAll_grows.2.2.2.1

omit model in
/-- Switch-case translation only allocates and seals what it reserved. -/
theorem trCases_grows : ∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (sv : ValId) (X : List Ident) (joinId : BlockId)
    (cs : List (Literal × List (Stmt Op))) (df : Option (List (Stmt Op))),
    CasesGrows fenv env lctx rets sv X joinId cs df :=
  trAll_grows.2.2.2.2

/-! ### Mutual function-table frame induction -/

def FuncFrame (fenv : FMap) (ps rs : List Ident)
    (body : List (Stmt Op)) : Prop :=
  ∀ (N : Nat) (s : BState) (g : Func) (s' : BState),
    N ≤ s.funcs.size → trFunc fenv ps rs body s = some (g, s') →
      FPrefix N s s'

def ScopeFrame (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (body : List (Stmt Op)) : Prop :=
  ∀ (N : Nat) (s : BState) (r : Option VMap) (s' : BState),
    N ≤ s.funcs.size → trScope fenv env lctx rets body s = some (r, s') →
      FPrefix N s s'

def StmtsFrame (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (d : Bool) (ss : List (Stmt Op)) : Prop :=
  ∀ (N : Nat) (s : BState) (r : Option VMap) (s' : BState),
    N ≤ s.funcs.size → FillAbove N fenv ss →
    trStmts fenv env lctx rets d ss s = some (r, s') → FPrefix N s s'

def StmtFrame (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (st : Stmt Op) : Prop :=
  ∀ (N : Nat) (s : BState) (r : Option VMap) (s' : BState),
    N ≤ s.funcs.size → trStmt fenv env lctx rets st s = some (r, s') →
      FPrefix N s s'

def CasesFrame (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (_sv : ValId) (_X : List Ident)
    (_joinId : BlockId) (cases : List (Literal × List (Stmt Op)))
    (dflt : Option (List (Stmt Op))) : Prop :=
  ∀ (sv : ValId) (X : List Ident) (joinId : BlockId) (N : Nat)
    (s : BState) (u : Unit) (s' : BState),
    N ≤ s.funcs.size →
    trCases fenv env lctx rets sv X joinId cases dflt s = some (u, s') →
      FPrefix N s s'

omit model in
theorem FillAbove.mono {N N' : Nat} (hNN' : N ≤ N')
    {fenv : FMap} {ss : List (Stmt Op)} (h : FillAbove N' fenv ss) :
    FillAbove N fenv ss := by
  intro n ps rs body hm fid hget
  exact Nat.le_trans hNN' (h n ps rs body hm fid hget)

omit model in
theorem FillAbove.tail {N : Nat} {fenv : FMap} {st : Stmt Op}
    {rest : List (Stmt Op)} (h : FillAbove N fenv (st :: rest)) :
    FillAbove N fenv rest := by
  intro n ps rs body hm
  exact h n ps rs body (by simp [hm])

omit model in
/-- **Mutual function-table frame theorem.** Every translation preserves the
prefix below its entry allocation watermark.  The statement-list member has
the one necessary side condition: the slots it is entitled to fill lie at or
above that watermark.  `trScope` establishes the condition from its own
`allocScope`, so the four public translation members are unconditional. -/
theorem trFrames_fprefix :
    (∀ (fenv : FMap) (ps rs : List Ident)
      (body : List (Stmt Op)), FuncFrame fenv ps rs body) ∧
    (∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
      (rets : Option (List Ident)) (body : List (Stmt Op)),
        ScopeFrame fenv env lctx rets body) ∧
    (∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
      (rets : Option (List Ident)) (d : Bool) (ss : List (Stmt Op)),
        StmtsFrame fenv env lctx rets d ss) ∧
    (∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
      (rets : Option (List Ident)) (st : Stmt Op),
        StmtFrame fenv env lctx rets st) ∧
    (∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
      (rets : Option (List Ident)) (sv : ValId) (X : List Ident)
      (joinId : BlockId) (cases : List (Literal × List (Stmt Op)))
      (dflt : Option (List (Stmt Op))),
        CasesFrame fenv env lctx rets sv X joinId cases dflt) := by
  refine trFunc.mutual_induct FuncFrame ScopeFrame StmtsFrame StmtFrame CasesFrame
    ?trFunc ?trScope ?stmtsNil ?stmtsFunDef ?stmtsSkip ?stmtsCons
    ?block ?funDef ?letNoneBad ?letNone ?letSomeBad ?letSome ?assignBad ?assign
    ?cond ?switch ?forLoop ?exprBuiltin ?exprCall ?exprBad
    ?breakNone ?breakSome ?contNone ?contSome ?leaveNone ?leaveSome
    ?casesNilNone ?casesNilSome ?casesCons
  case trFunc =>
    intro fenv ps rs body ih N s g s' hN h
    unfold trFunc at h
    obtain ⟨saved, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨u2, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨entry, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨pids, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨rids, s6, h6, h⟩ := M.bind_inv h
    have p6 : FPrefix N s s6 :=
      (((((FPrefix.of_getFn h1).trans (FPrefix.of_setFn h2)).trans
        (FPrefix.of_newBlock h3)).trans (FPrefix.of_moveTo h4)).trans
        (FPrefix.of_grows (Grows.of_mapM_freshVal h5))).trans
        (FPrefix.of_grows (Grows.of_mapM_constZero h6))
    by_cases hg : (!decide (ps ++ rs).Nodup) = true
    · rw [if_pos hg] at h
      obtain ⟨u7, s7, h7, -⟩ := M.bind_inv h
      exact absurd h7 (by simp [reject])
    · rw [if_neg hg] at h
      obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
      obtain ⟨renv, s8, h8, h⟩ := M.bind_inv h
      have p7 := p6.trans (FPrefix.of_pure h7)
      have p8 : FPrefix N s s8 := p7.trans
        (ih pids rids N s7 renv s8 (p7.size hN) h8)
      have finish : ∀ (sk : BState), FPrefix N s sk →
          (getFn >>= fun done => setFn saved >>= fun _ =>
          (pure { params := pids, nrets := rs.length, entry := entry,
                  blocks := done.blocks } : M Func)) sk = some (g, s') →
          FPrefix N s s' := by
        intro sk pk hk
        obtain ⟨done, sa, ha, hk⟩ := M.bind_inv hk
        obtain ⟨ub, sb, hb, hc⟩ := M.bind_inv hk
        exact ((pk.trans (FPrefix.of_getFn ha)).trans
          (FPrefix.of_setFn hb)).trans (FPrefix.of_pure hc)
      cases renv with
      | none =>
          obtain ⟨ua, sa, ha, hh⟩ := M.bind_inv h
          exact finish sa (p8.trans (FPrefix.of_pure ha)) hh
      | some envEnd =>
          obtain ⟨vals, sa, ha, h⟩ := M.bind_inv h
          obtain ⟨ub, sb, hb, hh⟩ := M.bind_inv h
          exact finish sb ((p8.trans (FPrefix.of_liftO ha)).trans
            (FPrefix.of_sealCur hb)) hh
  case trScope =>
    intro fenv env lctx rets body ih N s r s' hN h
    rw [trScope] at h
    obtain ⟨scope, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨renv, s2, h2, h3⟩ := M.bind_inv h
    have pa : FPrefix N s s1 := (allocScope_fprefix h1).mono hN
    have habove : FillAbove N (scope :: fenv) body :=
      (allocScope_fillAbove h1 fenv).mono hN
    have pb := ih scope N s1 renv s2 (pa.size hN) habove h2
    cases renv <;> exact (pa.trans pb).trans (FPrefix.of_pure h3)
  case stmtsNil =>
    intro fenv env lctx rets d N s r s' hN ha h
    rw [trStmts] at h
    exact FPrefix.of_pure h
  case stmtsFunDef =>
    intro fenv env lctx rets d n ps rs body rest ihf ihr N s r s' hN ha h
    rw [trStmts] at h
    obtain ⟨fid, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨g, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨u, s3, h3, h4⟩ := M.bind_inv h
    have hfid : N ≤ fid := ha n ps rs body (by simp) fid
      (M.liftO_inv h1).1
    have p1 : FPrefix N s s1 := FPrefix.of_liftO h1
    have p2 := ihf N s1 g s2 (p1.size hN) h2
    have p3 := FPrefix.of_fillFunc hfid h3
    have p03 := (p1.trans p2).trans p3
    exact p03.trans (ihr N s3 r s' (p03.size hN) ha.tail h4)
  case stmtsSkip =>
    intro fenv env lctx rets st rest hnf ih N s r s' hN ha h
    rw [trStmts] at h
    · split at h
      · exact ih N s r s' hN ha.tail h
      · rename_i hc; exact absurd rfl hc
    · exact hnf
  case stmtsCons =>
    intro fenv env lctx rets d st rest hnf hd ihs ihN ihT N s r s' hN ha h
    rw [trStmts] at h
    · rw [if_neg hd] at h
      obtain ⟨renv, s1, h1, h2⟩ := M.bind_inv h
      have p1 := ihs N s renv s1 hN h1
      have hN1 := Nat.le_trans hN
        (trStmt_grows fenv env lctx rets st s renv s1 h1).funcsSize
      cases renv with
      | some env' => exact p1.trans (ihN env' N s1 r s' hN1 ha.tail h2)
      | none => exact p1.trans (ihT N s1 r s' hN1 ha.tail h2)
    · exact hnf
  case block =>
    intro fenv env lctx rets body ih N s r s' hN h
    rw [trStmt] at h
    exact ih N s r s' hN h
  case funDef =>
    intro fenv env lctx rets n ps rs body N s r s' hN h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case letNoneBad =>
    intro fenv env lctx rets vars hg N s r s' hN h
    rw [trStmt, if_pos hg] at h
    obtain ⟨u, t, hb, -⟩ := M.bind_inv h
    exact absurd hb (by simp [reject])
  case letNone =>
    intro fenv env lctx rets vars hg N s r s' hN h
    rw [trStmt, if_neg hg] at h
    obtain ⟨u, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s2, h2, h3⟩ := M.bind_inv h
    exact ((FPrefix.of_pure h1).trans
      (FPrefix.of_grows (Grows.of_mapM_constZero h2))).trans
      (FPrefix.of_pure h3)
  case letSomeBad =>
    intro fenv env lctx rets vars e hg N s r s' hN h
    rw [trStmt, if_pos hg] at h
    obtain ⟨u, t, hb, -⟩ := M.bind_inv h
    exact absurd hb (by simp [reject])
  case letSome =>
    intro fenv env lctx rets vars e hg N s r s' hN h
    rw [trStmt, if_neg hg] at h
    obtain ⟨u, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s2, h2, h3⟩ := M.bind_inv h
    exact ((FPrefix.of_pure h1).trans
      (FPrefix.of_grows (trExprN_grows h2))).trans (FPrefix.of_pure h3)
  case assignBad =>
    intro fenv env lctx rets vars e hg N s r s' hN h
    rw [trStmt, if_pos hg] at h
    obtain ⟨u, t, hb, -⟩ := M.bind_inv h
    exact absurd hb (by simp [reject])
  case assign =>
    intro fenv env lctx rets vars e hg N s r s' hN h
    rw [trStmt, if_neg hg] at h
    obtain ⟨u, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨ids, s2, h2, h3⟩ := M.bind_inv h
    exact ((FPrefix.of_pure h1).trans
      (FPrefix.of_grows (trExprN_grows h2))).trans (FPrefix.of_pure h3)
  case cond =>
    intro fenv env lctx rets c body ih N s r s' hN h
    rw [trStmt] at h
    obtain ⟨cv, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨xv, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨bodyId, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨jps, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨joinId, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨u6, s6, h6, h⟩ := M.bind_inv h
    obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
    obtain ⟨renv, s8, h8, h⟩ := M.bind_inv h
    have p7 : FPrefix N s s7 :=
      ((((((FPrefix.of_grows (trExpr_grows c fenv env s s1 cv h1)).trans
        (FPrefix.of_edgeArgs h2)).trans (FPrefix.of_newBlock h3)).trans
        (FPrefix.of_grows (Grows.of_mapM_freshVal h4))).trans
        (FPrefix.of_newBlock h5)).trans (FPrefix.of_sealCur h6)).trans
        (FPrefix.of_moveTo h7)
    have p8 : FPrefix N s s8 := p7.trans
      (ih N s7 renv s8 (p7.size hN) h8)
    cases renv with
    | none =>
        obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb, hc⟩ := M.bind_inv h
        exact ((p8.trans (FPrefix.of_pure ha)).trans
          (FPrefix.of_moveTo hb)).trans (FPrefix.of_pure hc)
    | some env' =>
        obtain ⟨xa, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb, h⟩ := M.bind_inv h
        obtain ⟨uc, sc, hc, hd⟩ := M.bind_inv h
        exact (((p8.trans (FPrefix.of_edgeArgs ha)).trans
          (FPrefix.of_sealCur hb)).trans (FPrefix.of_moveTo hc)).trans
          (FPrefix.of_pure hd)
  case switch =>
    intro fenv env lctx rets c cases dflt ih N s r s' hN h
    unfold trStmt at h
    obtain ⟨sv, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨jps, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨jid, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨u5, s5, h5, h6⟩ := M.bind_inv h
    have p3 : FPrefix N s s3 := ((FPrefix.of_grows
      (trExpr_grows c fenv env s s1 sv h1)).trans
      (FPrefix.of_grows (Grows.of_mapM_freshVal h2))).trans
      (FPrefix.of_newBlock h3)
    exact ((p3.trans
      (ih sv jid sv _ jid N s3 u4 s4 (p3.size hN) h4)).trans
      (FPrefix.of_moveTo h5)).trans (FPrefix.of_pure h6)
  case forLoop =>
    intro fenv env lctx rets init c post body ihI ihB ihP N s r s' hN h
    unfold trStmt at h
    obtain ⟨scope, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨rinit, s2, h2, h⟩ := M.bind_inv h
    have p1 : FPrefix N s s1 := (allocScope_fprefix h1).mono hN
    have habove : FillAbove N (scope :: fenv) init :=
      (allocScope_fillAbove h1 fenv).mono hN
    have p2 := ihI scope N s1 rinit s2 (p1.size hN) habove h2
    have pinit := p1.trans p2
    cases rinit with
    | none => exact pinit.trans (FPrefix.of_pure h)
    | some envI =>
      obtain ⟨xv, s3, h3, h⟩ := M.bind_inv h
      obtain ⟨hps, s4, h4, h⟩ := M.bind_inv h
      obtain ⟨hid, s5, h5, h⟩ := M.bind_inv h
      obtain ⟨eps, s6, h6, h⟩ := M.bind_inv h
      obtain ⟨eid, s7, h7, h⟩ := M.bind_inv h
      obtain ⟨pps, s8, h8, h⟩ := M.bind_inv h
      obtain ⟨pid, s9, h9, h⟩ := M.bind_inv h
      obtain ⟨u10, s10, h10, h⟩ := M.bind_inv h
      obtain ⟨u11, s11, h11, h⟩ := M.bind_inv h
      obtain ⟨cv, s12, h12, h⟩ := M.bind_inv h
      obtain ⟨bid, s13, h13, h⟩ := M.bind_inv h
      obtain ⟨hx, s14, h14, h⟩ := M.bind_inv h
      obtain ⟨u15, s15, h15, h⟩ := M.bind_inv h
      obtain ⟨u16, s16, h16, h⟩ := M.bind_inv h
      obtain ⟨rb, s17, h17, h⟩ := M.bind_inv h
      have p3 := pinit.trans (FPrefix.of_edgeArgs h3)
      have p4 := p3.trans (FPrefix.of_grows (Grows.of_mapM_freshVal h4))
      have p5 := p4.trans (FPrefix.of_newBlock h5)
      have p6 := p5.trans (FPrefix.of_grows (Grows.of_mapM_freshVal h6))
      have p7 := p6.trans (FPrefix.of_newBlock h7)
      have p8 := p7.trans (FPrefix.of_grows (Grows.of_mapM_freshVal h8))
      have p9 := p8.trans (FPrefix.of_newBlock h9)
      have p10 := p9.trans (FPrefix.of_sealCur h10)
      have p11 := p10.trans (FPrefix.of_moveTo h11)
      have p12 := p11.trans (FPrefix.of_grows
        (trExpr_grows c (scope :: fenv) _ s11 s12 cv h12))
      have p13 := p12.trans (FPrefix.of_newBlock h13)
      have p14 := p13.trans (FPrefix.of_edgeArgs h14)
      have p15 := p14.trans (FPrefix.of_sealCur h15)
      have p16 := p15.trans (FPrefix.of_moveTo h16)
      have p17 : FPrefix N s s17 := p16.trans
        (ihB scope envI hps eid pid N s16 rb s17 (p16.size hN) h17)
      cases rb with
      | none =>
        obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb, h⟩ := M.bind_inv h
        obtain ⟨rp, sc, hc, h⟩ := M.bind_inv h
        have pp := (p17.trans (FPrefix.of_pure ha)).trans
          (FPrefix.of_moveTo hb)
        have pc := pp.trans
          (ihP scope envI pps N sb rp sc (pp.size hN) hc)
        cases rp with
        | none =>
          obtain ⟨ud, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, hf⟩ := M.bind_inv h
          exact ((pc.trans (FPrefix.of_pure hd)).trans
            (FPrefix.of_moveTo he)).trans (FPrefix.of_pure hf)
        | some ep =>
          obtain ⟨xd, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, h⟩ := M.bind_inv h
          obtain ⟨uf, sf, hf, h⟩ := M.bind_inv h
          exact (((pc.trans (FPrefix.of_edgeArgs hd)).trans
            (FPrefix.of_sealCur he)).trans (FPrefix.of_moveTo hf)).trans
            (FPrefix.of_pure h)
      | some eb =>
        obtain ⟨xa, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb, h⟩ := M.bind_inv h
        obtain ⟨uc, sc, hc, h⟩ := M.bind_inv h
        obtain ⟨rp, sd, hd, h⟩ := M.bind_inv h
        have pp := ((p17.trans (FPrefix.of_edgeArgs ha)).trans
          (FPrefix.of_sealCur hb)).trans (FPrefix.of_moveTo hc)
        have pd := pp.trans
          (ihP scope envI pps N sc rp sd (pp.size hN) hd)
        cases rp with
        | none =>
          obtain ⟨ue, se, he, h⟩ := M.bind_inv h
          obtain ⟨uf, sf, hf, hg⟩ := M.bind_inv h
          exact ((pd.trans (FPrefix.of_pure he)).trans
            (FPrefix.of_moveTo hf)).trans (FPrefix.of_pure hg)
        | some ep =>
          obtain ⟨xe, se, he, h⟩ := M.bind_inv h
          obtain ⟨uf, sf, hf, h⟩ := M.bind_inv h
          obtain ⟨ug, sg, hg, h⟩ := M.bind_inv h
          exact (((pd.trans (FPrefix.of_edgeArgs he)).trans
            (FPrefix.of_sealCur hf)).trans (FPrefix.of_moveTo hg)).trans
            (FPrefix.of_pure h)
  case exprBuiltin =>
    intro fenv env lctx rets op args N s r s' hN h
    rw [trStmt] at h
    obtain ⟨as, s1, h1, h⟩ := M.bind_inv h
    have p1 : FPrefix N s s1 :=
      FPrefix.of_grows (trArgs_grows args fenv env s s1 as h1)
    by_cases hop : isHaltingOp op = true
    · rw [if_pos hop] at h
      obtain ⟨u, s2, h2, h3⟩ := M.bind_inv h
      exact (p1.trans (FPrefix.of_sealCur h2)).trans (FPrefix.of_pure h3)
    · rw [if_neg hop] at h
      obtain ⟨u, s2, h2, h3⟩ := M.bind_inv h
      exact (p1.trans (FPrefix.of_grows (Grows.of_emit h2))).trans
        (FPrefix.of_pure h3)
  case exprCall =>
    intro fenv env lctx rets fn args N s r s' hN h
    rw [trStmt] at h
    obtain ⟨as, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨fid, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨u, s3, h3, h4⟩ := M.bind_inv h
    exact ((FPrefix.of_grows (trArgs_grows args fenv env s s1 as h1)).trans
      (FPrefix.of_liftO h2)).trans
      ((FPrefix.of_grows (Grows.of_emit h3)).trans (FPrefix.of_pure h4))
  case exprBad =>
    intro fenv env lctx rets e hnb hnc N s r s' hN h
    rw [trStmt] at h
    · exact absurd h (by simp [reject])
    · exact hnb
    · exact hnc
  case breakNone =>
    intro fenv env rets N s r s' hN h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case breakSome =>
    intro fenv env rets l N s r s' hN h
    rw [trStmt] at h
    obtain ⟨vals, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s2, h2, h3⟩ := M.bind_inv h
    exact ((FPrefix.of_edgeArgs h1).trans (FPrefix.of_sealCur h2)).trans
      (FPrefix.of_pure h3)
  case contNone =>
    intro fenv env rets N s r s' hN h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case contSome =>
    intro fenv env rets l N s r s' hN h
    rw [trStmt] at h
    obtain ⟨vals, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s2, h2, h3⟩ := M.bind_inv h
    exact ((FPrefix.of_edgeArgs h1).trans (FPrefix.of_sealCur h2)).trans
      (FPrefix.of_pure h3)
  case leaveNone =>
    intro fenv env lctx N s r s' hN h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case leaveSome =>
    intro fenv env lctx rs N s r s' hN h
    rw [trStmt] at h
    obtain ⟨vals, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s2, h2, h3⟩ := M.bind_inv h
    exact ((FPrefix.of_edgeArgs h1).trans (FPrefix.of_sealCur h2)).trans
      (FPrefix.of_pure h3)
  case casesNilNone =>
    intro fenv env lctx rets _sv _X _jid sv X jid N s u s' hN h
    rw [trCases] at h
    obtain ⟨xv, s1, h1, h2⟩ := M.bind_inv h
    exact (FPrefix.of_edgeArgs h1).trans (FPrefix.of_sealCur h2)
  case casesNilSome =>
    intro fenv env lctx rets _sv _X _jid body ih sv X jid N s u s' hN h
    rw [trCases] at h
    obtain ⟨renv, s1, h1, h2⟩ := M.bind_inv h
    have p1 := ih N s renv s1 hN h1
    cases renv with
    | none => exact p1.trans (FPrefix.of_pure h2)
    | some env' =>
      obtain ⟨xv, s2, h3, h4⟩ := M.bind_inv h2
      exact (p1.trans (FPrefix.of_edgeArgs h3)).trans
        (FPrefix.of_sealCur h4)
  case casesCons =>
    intro fenv env lctx rets _sv _X _jid lit body rest dflt ihB ihR
      sv X jid N s u s' hN h
    rw [trCases] at h
    obtain ⟨t, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨u2, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨e, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨cid, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨nid, s6, h6, h⟩ := M.bind_inv h
    obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
    obtain ⟨u8, s8, h8, h⟩ := M.bind_inv h
    obtain ⟨renv, s9, h9, h⟩ := M.bind_inv h
    have p8 : FPrefix N s s8 :=
      (((((((FPrefix.of_grows (Grows.of_freshVal h1)).trans
        (FPrefix.of_grows (Grows.of_emit h2))).trans
        (FPrefix.of_grows (Grows.of_freshVal h3))).trans
        (FPrefix.of_grows (Grows.of_emit h4))).trans
        (FPrefix.of_newBlock h5)).trans (FPrefix.of_newBlock h6)).trans
        (FPrefix.of_sealCur h7)).trans (FPrefix.of_moveTo h8)
    have p9 : FPrefix N s s9 := p8.trans
      (ihB N s8 renv s9 (p8.size hN) h9)
    cases renv with
    | none =>
      obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb, hc⟩ := M.bind_inv h
      have pp := (p9.trans (FPrefix.of_pure ha)).trans
        (FPrefix.of_moveTo hb)
      exact pp.trans (ihR sv X jid N sb u s' (pp.size hN) hc)
    | some env' =>
      obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb, h⟩ := M.bind_inv h
      obtain ⟨uc, sc, hc, hd⟩ := M.bind_inv h
      have pp := ((p9.trans (FPrefix.of_edgeArgs ha)).trans
        (FPrefix.of_sealCur hb)).trans (FPrefix.of_moveTo hc)
      exact pp.trans (ihR sv X jid N sc u s' (pp.size hN) hd)

omit model in
theorem trFunc_fprefix : ∀ (fenv : FMap) (ps rs : List Ident)
    (body : List (Stmt Op)), FuncFrame fenv ps rs body :=
  trFrames_fprefix.1

omit model in
theorem trScope_fprefix : ∀ (fenv : FMap) (env : VMap)
    (lctx : Option LoopCtx) (rets : Option (List Ident))
    (body : List (Stmt Op)), ScopeFrame fenv env lctx rets body :=
  trFrames_fprefix.2.1

omit model in
theorem trStmt_fprefix : ∀ (fenv : FMap) (env : VMap)
    (lctx : Option LoopCtx) (rets : Option (List Ident)) (st : Stmt Op),
    StmtFrame fenv env lctx rets st :=
  trFrames_fprefix.2.2.2.1

omit model in
theorem trCases_fprefix : ∀ (fenv : FMap) (env : VMap)
    (lctx : Option LoopCtx) (rets : Option (List Ident)) (sv : ValId)
    (X : List Ident) (joinId : BlockId)
    (cases : List (Literal × List (Stmt Op)))
    (dflt : Option (List (Stmt Op))),
    CasesFrame fenv env lctx rets sv X joinId cases dflt :=
  trFrames_fprefix.2.2.2.2

omit model in
/-- Natural-watermark specialization used by callers protecting all slots
that existed before a nested closed translation. -/
theorem trFunc_prefix (fenv : FMap) (ps rs : List Ident)
    (body : List (Stmt Op)) {s s' : BState} {g : Func}
    (h : trFunc fenv ps rs body s = some (g, s')) :
    FPrefix s.funcs.size s s' :=
  trFunc_fprefix fenv ps rs body s.funcs.size s g s' (Nat.le_refl _) h

/-- The ordered function-slot budget consumed by a statement walk.  Function
definitions are the only statements which consume a reservation; all other
statements are closed translations and therefore preserve the caller's
budget.  Successful `trStmts` runs ensure every `filterMap` entry is present. -/
def stmtFuncIds (fenv : FMap) : List (Stmt Op) → List FuncId
  | [] => []
  | .funDef n _ _ _ :: rest => (fenv.get n).toList ++ stmtFuncIds fenv rest
  | _ :: rest => stmtFuncIds fenv rest

omit model in
/-- Pull a completed output ownership budget backward through a statement
walk.  The input additionally owns exactly the slots selected by its direct
`funDef`s.  `hslots` is supplied by the enclosing `allocScope`; its `Nodup`
clause rules out duplicate selection, which is precisely what permits each
`fillFunc` to consume one distinct reservation.

This is the input/output ownership transition used by the simulation motive.
Nested statements and functions frame every input slot by `FPrefix`; the sole
consuming step is discharged by `FOwned.back_fillFunc`. -/
theorem trStmts_owned_back (fenv : FMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) :
    ∀ (ss : List (Stmt Op)) (env : VMap) (d : Bool)
      (s s' done : BState) (r : Option VMap) (owned : List FuncId),
      (∀ i : FuncId, i ∈ stmtFuncIds fenv ss ++ owned → i < s.funcs.size) →
      (∀ i : FuncId, i ∈ stmtFuncIds fenv ss →
        s.funcs[i]? = some none) →
      (stmtFuncIds fenv ss ++ owned).Nodup →
      FOwned owned s' done →
      trStmts fenv env lctx rets d ss s = some (r, s') →
      FOwned (stmtFuncIds fenv ss ++ owned) s done := by
  intro ss
  induction ss with
  | nil =>
      intro env d s s' done r owned _ _ _ ho htr
      rw [trStmts] at htr
      obtain ⟨-, rfl⟩ := M.pure_inv htr
      simpa [stmtFuncIds] using ho
  | cons st rest ih =>
      intro env d s s' done r owned hbound hslots hnd ho htr
      let st0 := st
      cases st with
      | funDef n ps rs body =>
          rw [trStmts] at htr
          obtain ⟨fid, s1, hget, htr⟩ := M.bind_inv htr
          obtain ⟨g, s2, hfunc, htr⟩ := M.bind_inv htr
          obtain ⟨u, s3, hfill, htail⟩ := M.bind_inv htr
          obtain ⟨hfid, hs1⟩ := M.liftO_inv hget
          subst s1
          simp only [stmtFuncIds, hfid, Option.toList_some,
            List.singleton_append] at hbound hslots hnd ⊢
          have hfid0 : s.funcs[fid]? = some none :=
            hslots fid (by simp)
          have hp := trFunc_prefix fenv ps rs body hfunc
          have hfid2 : s2.funcs[fid]? = some none := by
            rw [hp fid (lt_size_of_getElem? hfid0)]
            exact hfid0
          have hndTail : (stmtFuncIds fenv rest ++ owned).Nodup :=
            (List.nodup_cons.mp hnd).2
          have hfidNot : fid ∉ stmtFuncIds fenv rest ++ owned :=
            (List.nodup_cons.mp hnd).1
          have hs3 := (M.fillFunc_inv hfill).choose_spec
          have hboundTail : ∀ i : FuncId,
              i ∈ stmtFuncIds fenv rest ++ owned → i < s3.funcs.size := by
            intro i hi
            have hi0 := hbound i (by simp [hi])
            have hsize : s.funcs.size ≤ s2.funcs.size :=
              (trFunc_fprefix fenv ps rs body s.funcs.size s g s2
                (Nat.le_refl _) hfunc).size (Nat.le_refl _)
            rw [hs3]
            simpa using Nat.lt_of_lt_of_le hi0 hsize
          have hslotsTail : ∀ i : FuncId, i ∈ stmtFuncIds fenv rest →
              s3.funcs[i]? = some none := by
            intro i hi
            have hiAll : i ∈ stmtFuncIds fenv rest ++ owned :=
              List.mem_append_left _ hi
            have hi0 : s.funcs[i]? = some none :=
              hslots i (by simp [hi])
            have hi2 : s2.funcs[i]? = some none := by
              rw [hp i (lt_size_of_getElem? hi0)]
              exact hi0
            have hine : i ≠ fid := by
              intro heq
              subst i
              exact hfidNot hiAll
            rw [hs3, Array.getElem?_set, if_neg (Ne.symm hine)]
            exact hi2
          have ho3 := ih env d s3 s' done r owned hboundTail hslotsTail
            hndTail ho htail
          have ho2 : FOwned (fid :: (stmtFuncIds fenv rest ++ owned)) s2 done :=
            FOwned.back_fillFunc hfid2 hfill ho3
          have hbound2 : ∀ i : FuncId,
              i ∈ fid :: (stmtFuncIds fenv rest ++ owned) →
                i < s.funcs.size := by
            intro i hi
            exact hbound i (by simpa using hi)
          exact FOwned.back_fprefix hp hbound2 ho2
      | block body | letDecl vars val | assign vars e | cond e body
      | forLoop init e post body | «break» | «continue» | leave
      | switch e cases dflt | exprStmt e =>
          simp only [stmtFuncIds] at hbound hslots hnd ⊢
          have runTail (env' : VMap) (d' : Bool) (s1 : BState)
              (hhead : trStmt fenv env lctx rets st0 s = some (some env', s1) ∨
                trStmt fenv env lctx rets st0 s = some (none, s1))
              (htail : trStmts fenv env' lctx rets d' rest s1 = some (r, s')) :
              FOwned (stmtFuncIds fenv rest ++ owned) s done := by
            have htrHead : ∃ ro, trStmt fenv env lctx rets st0 s = some (ro, s1) :=
              hhead.elim (fun h => ⟨some env', h⟩) (fun h => ⟨none, h⟩)
            obtain ⟨ro, hro⟩ := htrHead
            have hp := trStmt_fprefix fenv env lctx rets st0 s.funcs.size
              s ro s1 (Nat.le_refl _) hro
            have hbound1 : ∀ i : FuncId,
                i ∈ stmtFuncIds fenv rest ++ owned → i < s1.funcs.size := by
              intro i hi
              exact hp.size (Nat.le_refl _) |>
                Nat.lt_of_lt_of_le (hbound i hi)
            have hslots1 : ∀ i : FuncId, i ∈ stmtFuncIds fenv rest →
                s1.funcs[i]? = some none := by
              intro i hi
              rw [hp i (hbound i (List.mem_append_left _ hi))]
              exact hslots i hi
            have ho1 := ih env' d' s1 s' done r owned hbound1 hslots1
              hnd ho htail
            exact FOwned.back_fprefix hp hbound ho1
          rw [trStmts] at htr
          · split at htr
            · exact ih env true s s' done r owned hbound hslots hnd ho htr
            · obtain ⟨renv, s1, hhead, htail⟩ := M.bind_inv htr
              cases renv with
              | none =>
                  exact runTail env true s1 (Or.inr hhead) htail
              | some env' =>
                  exact runTail env' false s1 (Or.inl hhead) htail
          · intro n ps rs fbody heq
            cases heq

omit model in
/-- A pending function slot which no declaration in a statement suffix selects
survives that suffix.  Nested scopes and nested function translations frame
the whole table present at their entry; the only operation which can touch the
protected slot is therefore the direct `fillFunc` at a `funDef` head. -/
theorem trStmts_pending_survives (fenv : FMap) (env : VMap)
    (lctx : Option LoopCtx) (rets : Option (List Ident)) (d : Bool) :
    ∀ (ss : List (Stmt Op)) (s s' : BState) (r : Option VMap) (i : FuncId),
      s.funcs[i]? = some none →
      (∀ (n : Ident) (ps rs : List Ident) (body : List (Stmt Op)),
        Stmt.funDef n ps rs body ∈ ss → fenv.get n ≠ some i) →
      trStmts fenv env lctx rets d ss s = some (r, s') →
      s'.funcs[i]? = some none := by
  intro ss
  induction ss generalizing env d with
  | nil =>
      intro s s' r i hi _ h
      rw [trStmts] at h
      obtain ⟨-, rfl⟩ := M.pure_inv h
      exact hi
  | cons st rest ih =>
      intro s s' r i hi hskip h
      cases st with
      | funDef n ps rs body =>
          rw [trStmts] at h
          obtain ⟨fid, s1, h1, h⟩ := M.bind_inv h
          obtain ⟨g, s2, h2, h⟩ := M.bind_inv h
          obtain ⟨u, s3, h3, h4⟩ := M.bind_inv h
          obtain ⟨hget, hs1⟩ := M.liftO_inv h1
          subst s1
          have hlt : i < s.funcs.size := lt_size_of_getElem? hi
          have hi2 : s2.funcs[i]? = some none := by
            rw [trFunc_prefix fenv ps rs body h2 i hlt]
            exact hi
          have hne : i ≠ fid := by
            intro heq
            subst fid
            exact hskip n ps rs body (by simp) hget
          obtain ⟨hfid, hs3⟩ := M.fillFunc_inv h3
          have hi3 : s3.funcs[i]? = some none := by
            rw [hs3]
            rw [Array.getElem?_set (h := hfid), if_neg (Ne.symm hne)]
            exact hi2
          have hskipRest : ∀ (n' : Ident) (ps' rs' : List Ident)
              (body' : List (Stmt Op)),
              Stmt.funDef n' ps' rs' body' ∈ rest →
                fenv.get n' ≠ some i := by
            intro n' ps' rs' body' hm
            exact hskip n' ps' rs' body' (List.mem_cons_of_mem _ hm)
          exact ih env d s3 s' r i hi3 hskipRest h4
      | block body | letDecl vars val | assign vars e | cond e body
      | forLoop init e post body | «break» | «continue» | leave
      | switch e cases dflt | exprStmt e =>
          have hskipRest : ∀ (n : Ident) (ps rs : List Ident)
              (body : List (Stmt Op)),
              Stmt.funDef n ps rs body ∈ rest → fenv.get n ≠ some i := by
            intro n ps rs body hm
            exact hskip n ps rs body (List.mem_cons_of_mem _ hm)
          rw [trStmts] at h
          · split at h
            · exact ih env true s s' r i hi hskipRest h
            · obtain ⟨renv, s1, h1, h2⟩ := M.bind_inv h
              have hlt : i < s.funcs.size := lt_size_of_getElem? hi
              have hi1 : s1.funcs[i]? = some none := by
                have hp := trStmt_fprefix fenv env lctx rets _ s.funcs.size
                  s renv s1 (Nat.le_refl _) h1
                rw [hp i hlt]
                exact hi
              cases renv with
              | none => exact ih env true s1 s' r i hi1 hskipRest h2
              | some env' => exact ih env' false s1 s' r i hi1 hskipRest h2
          · intro n ps rs fbody heq
            cases heq

omit model in
/-- Once control has diverted, `trStmts` only fills hoisted function slots;
the caller's per-function construction state is restored exactly. -/
theorem trStmts_true_fn (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) : ∀ (ss : List (Stmt Op)) (s s' : BState)
      (r : Option VMap),
      trStmts fenv env lctx rets true ss s = some (r, s') →
        r = none ∧ s'.fn = s.fn := by
  intro ss
  induction ss with
  | nil =>
    intro s s' r h
    rw [trStmts] at h
    obtain ⟨rfl, rfl⟩ := M.pure_inv h
    exact ⟨rfl, rfl⟩
  | cons st rest ih =>
    cases st with
    | funDef n ps rs body =>
      intro s s' r h
      rw [trStmts] at h
      obtain ⟨fid, s₁, h1, h⟩ := M.bind_inv h
      obtain ⟨g, s₂, h2, h⟩ := M.bind_inv h
      obtain ⟨u, s₃, h3, h4⟩ := M.bind_inv h
      have hfn₁ : s₁.fn = s.fn := congrArg BState.fn (M.liftO_inv h1).2
      have hfn₂ : s₂.fn = s₁.fn := (trFunc_grows fenv ps rs body s₁ g s₂ h2).1
      obtain ⟨hlt, rfl⟩ := M.fillFunc_inv h3
      obtain ⟨hr, hfn₃⟩ := ih _ s' r h4
      exact ⟨hr, hfn₃.trans (hfn₂.trans hfn₁)⟩
    | block body | letDecl vars val | assign vars e | cond c body
    | forLoop init c post body | «break» | «continue» | leave
    | switch c cases dflt | exprStmt e =>
      intro s s' r h
      exact ih s s' r (by simpa [trStmts] using h)

omit model in
/-- Invert the live, non-function head of a statement list. -/
theorem trStmts_false_cons_inv {fenv : FMap} {env : VMap}
    {lctx : Option LoopCtx} {rets : Option (List Ident)} {st : Stmt Op}
    {rest : List (Stmt Op)} {s₀ s₁ : BState} {renv : Option VMap}
    (hnf : ∀ n ps rs body, st ≠ .funDef n ps rs body)
    (h : trStmts fenv env lctx rets false (st :: rest) s₀ = some (renv, s₁)) :
    ∃ (renvA : Option VMap) (sA : BState),
      trStmt fenv env lctx rets st s₀ = some (renvA, sA) ∧
      (match renvA with
        | some env' => trStmts fenv env' lctx rets false rest sA
        | none => trStmts fenv env lctx rets true rest sA) = some (renv, s₁) := by
  rw [trStmts] at h
  · obtain ⟨renvA, sA, h1, h2⟩ := M.bind_inv h
    refine ⟨renvA, sA, h1, ?_⟩
    cases renvA <;> exact h2
  · exact fun n ps rs body => hnf n ps rs body

/-- **`edgeArgs` carries the right values.** The ids an edge passes read back,
through `EnvOK`, as exactly the values the source environment records for those
names. This is the fact behind every join edge and every non-local exit
(`break`/`continue`/`leave`): the values the target block's parameters receive
agree with the source configuration at the jump. -/
theorem edgeArgs_ok {env : VMap} {V : VEnv yulD} {R : Regs} {xs : List Ident}
    {ids : List ValId} {s s' : BState}
    (henv : EnvOK (model := model) env V R)
    (h : edgeArgs env xs s = some (ids, s')) :
    s' = s ∧ ∃ vals, R.getMany ids = some vals
      ∧ YulSemantics.Forall₂ (fun x v => YulSemantics.VEnv.get V x = some v) xs vals := by
  obtain ⟨hm, rfl⟩ := M.edgeArgs_inv h
  exact ⟨rfl, EnvOK.edge_vals henv (YulSemantics.Forall₂.mapM_eq_some_iff.mp hm)⟩

end Semantics
end YulEvmCompiler.SsaCfg
