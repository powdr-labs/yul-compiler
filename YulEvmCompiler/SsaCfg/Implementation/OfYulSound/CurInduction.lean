import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.CurBlock
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.OfYulSound.CurInduction

The current-block induction, and the straight-line statement leaves.

`trStmts_cur` and its siblings — the induction that says what the mutual
translation does to the current block — followed by the leaves for the
statement forms that emit straight-line code (`sim_letDecl_*`, `sim_assign`,
`sim_exprStmt_*`).
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics (Ident Literal Expr Stmt VEnv Outcome)
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal evmWithExternal)

section Semantics
variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates model.gas

omit model in
/-- A successful translation preserves current-id validity and records whether
its incoming block stayed open or was sealed.  `trFunc` is irrelevant to the
caller-current invariant because it restores the saved `FnState`; its motive is
therefore `True`, while the other four mutually recursive functions carry the
result-sensitive relation. -/
theorem trStmts_cur : ∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (d : Bool) (ss : List (Stmt Op)),
    StmtsCur fenv env lctx rets d ss := by
  refine trStmts.induct (fun _ _ _ _ => True) ScopeCur StmtsCur StmtCur CasesCur
    ?trFunc ?trScope ?stmtsNil ?stmtsFunDef ?stmtsSkip ?stmtsCons
    ?block ?funDef ?letNoneBad ?letNone ?letSomeBad ?letSome ?assignBad ?assign
    ?cond ?switch ?forLoop ?exprBuiltin ?exprCall ?exprBad
    ?breakNone ?breakSome ?contNone ?contSome ?leaveNone ?leaveSome
    ?casesNilNone ?casesNilSome ?casesCons
  case trFunc =>
    intro fenv ps rs body ih
    trivial
  case trScope =>
    intro fenv env lctx rets body ih s r s' hv h
    rw [trScope] at h
    obtain ⟨scope, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨renv, s₂, h2, h3⟩ := M.bind_inv h
    obtain ⟨hfn1, -⟩ := allocScope_funcsOnly h1
    have hv1 : CurValid s₁ := by rw [CurValid, hfn1]; exact hv
    obtain ⟨hv2, hk2⟩ := ih scope s₁ renv s₂ hv1 h2
    have hg2 := trStmts_grows (scope :: fenv) env lctx rets false body
      s₁ renv s₂ h2
    cases renv with
    | none =>
      obtain ⟨rfl, rfl⟩ := M.pure_inv h3
      refine ⟨hv2, ?_⟩
      exact CurOpen.transClosed hv (allocScope_sgrows h1)
        hg2 (Or.inl (CurSame.of_fnEq hfn1)) hk2
    | some env' =>
      obtain ⟨rfl, rfl⟩ := M.pure_inv h3
      refine ⟨hv2, ?_⟩
      exact CurOpen.trans hv (allocScope_sgrows h1)
        hg2 (Or.inl (CurSame.of_fnEq hfn1)) hk2
  case stmtsNil =>
    intro fenv env lctx rets d
    cases d <;> simp only [StmtsCur, Bool.false_eq_true, ↓reduceIte]
    intro s r s' hv h
    rw [trStmts] at h
    obtain ⟨rfl, rfl⟩ := M.pure_inv h
    exact ⟨hv, Or.inl (CurSame.rfl' _)⟩
  case stmtsFunDef =>
    intro fenv env lctx rets d n ps rs fbody rest ihf ihr
    cases d with
    | true => simp [StmtsCur]
    | false =>
      simp only [StmtsCur, Bool.false_eq_true, ↓reduceIte]
      intro s r s' hv h
      rw [trStmts] at h
      obtain ⟨fid, s₁, h1, h⟩ := M.bind_inv h
      obtain ⟨g, s₂, h2, h⟩ := M.bind_inv h
      obtain ⟨u, s₃, h3, h4⟩ := M.bind_inv h
      have hfn1 : s₁.fn = s.fn := congrArg BState.fn (M.liftO_inv h1).2
      have hfn2 : s₂.fn = s₁.fn := (trFunc_grows fenv ps rs fbody s₁ g s₂ h2).1
      have hfn3 : s₃.fn = s₂.fn := by rw [(M.fillFunc_inv h3).choose_spec]
      have hfn : s₃.fn = s.fn := hfn3.trans (hfn2.trans hfn1)
      have hv3 : CurValid s₃ := by rw [CurValid, hfn]; exact hv
      obtain ⟨hv', hk⟩ := ihr s₃ r s' hv3 h4
      have hgpre : SGrows s s₃ := ((SGrows.trans (SGrowsAt.of_liftO h1)
        (SGrowsAt.of_funcsOnly hfn2
          (trFunc_grows fenv ps rs fbody s₁ g s₂ h2).2)).trans
            (SGrowsAt.of_fillFunc h3))
      have hs : CurOpen s s₃ := Or.inl (CurSame.of_fnEq hfn)
      have hgtail := trStmts_grows fenv env lctx rets false rest s₃ r s' h4
      refine ⟨hv', ?_⟩
      cases r with
      | none => exact CurOpen.transClosed hv hgpre hgtail hs hk
      | some e => exact CurOpen.trans hv hgpre hgtail hs hk
  case stmtsSkip =>
    intro fenv env lctx rets st rest hnf ih
    simp [StmtsCur]
  case stmtsCons =>
    intro fenv env lctx rets d st rest hnf hd ih4 ih3n ih3t
    have hd0 : d = false := Bool.eq_false_of_not_eq_true hd
    subst d
    simp only [StmtsCur, Bool.false_eq_true, ↓reduceIte]
    intro s r s' hv h
    rw [trStmts] at h
    · rw [if_neg hd] at h
      obtain ⟨renv, s₁, h1, h2⟩ := M.bind_inv h
      obtain ⟨hv1, hk1⟩ := ih4 s renv s₁ hv h1
      have hg1 := trStmt_grows fenv env lctx rets st s renv s₁ h1
      cases renv with
      | some env' =>
        obtain ⟨hv2, hk2⟩ := ih3n env' s₁ r s' hv1 h2
        have hg2 := trStmts_grows fenv env' lctx rets false rest s₁ r s' h2
        refine ⟨hv2, ?_⟩
        cases r with
        | none => exact CurOpen.transClosed hv hg1 hg2 hk1 hk2
        | some e => exact CurOpen.trans hv hg1 hg2 hk1 hk2
      | none =>
        obtain ⟨hr, hfn⟩ := trStmts_true_fn fenv env lctx rets rest s₁ s' r h2
        subst r
        have hs : CurSame s₁ s' := CurSame.of_fnEq hfn
        have hg2 := trStmts_grows fenv env lctx rets true rest s₁ none s' h2
        exact ⟨by rw [CurValid, hfn]; exact hv1,
          CurClosed.transSame hv hg1 hg2 hk1 hs⟩
    · exact hnf
  case block =>
    intro fenv env lctx rets body ih s r s' hv h
    rw [trStmt] at h
    exact ih s r s' hv h
  case funDef =>
    intro fenv env lctx rets name ps rs body s r s' hv h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case letNoneBad =>
    intro fenv env lctx rets vars hgate s r s' hv h
    rw [trStmt, if_pos hgate] at h
    obtain ⟨u, s₁, h1, -⟩ := M.bind_inv h
    exact absurd h1 (by simp [reject])
  case letNone =>
    intro fenv env lctx rets vars hgate s r s' hv h
    rw [trStmt, if_neg hgate] at h
    obtain ⟨ids, s₁, h1, h2⟩ := M.bind_inv h
    obtain ⟨rfl, rfl⟩ := M.pure_inv h2
    have hg := Grows.of_mapM_constZero h1
    exact ⟨hv.of_grows hg, Or.inl (CurSame.of_grows hg)⟩
  case letSomeBad =>
    intro fenv env lctx rets vars e hgate s r s' hv h
    rw [trStmt, if_pos hgate] at h
    obtain ⟨u, s₁, h1, -⟩ := M.bind_inv h
    exact absurd h1 (by simp [reject])
  case letSome =>
    intro fenv env lctx rets vars e hgate s r s' hv h
    rw [trStmt, if_neg hgate] at h
    obtain ⟨ids, s₁, h1, h2⟩ := M.bind_inv h
    obtain ⟨rfl, rfl⟩ := M.pure_inv h2
    have hg := trExprN_grows h1
    exact ⟨hv.of_grows hg, Or.inl (CurSame.of_grows hg)⟩
  case assignBad =>
    intro fenv env lctx rets vars e hgate s r s' hv h
    rw [trStmt, if_pos hgate] at h
    obtain ⟨u, s₁, h1, -⟩ := M.bind_inv h
    exact absurd h1 (by simp [reject])
  case assign =>
    intro fenv env lctx rets vars e hgate s r s' hv h
    rw [trStmt, if_neg hgate] at h
    obtain ⟨ids, s₁, h1, h2⟩ := M.bind_inv h
    obtain ⟨rfl, rfl⟩ := M.pure_inv h2
    have hg := trExprN_grows h1
    exact ⟨hv.of_grows hg, Or.inl (CurSame.of_grows hg)⟩
  case cond =>
    intro fenv env lctx rets c body ih s r s' hv h
    rw [trStmt] at h
    obtain ⟨cv, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨xvals, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨bodyId, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨joinParams, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨joinId, s5, h5, h⟩ := M.bind_inv h
    obtain ⟨u6, s6, h6, h⟩ := M.bind_inv h
    obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
    obtain ⟨renv, s8, h8, h⟩ := M.bind_inv h
    have g1 := trExpr_grows c fenv env s s1 cv h1
    have g2 := Grows.of_liftO h2
    have g4 := Grows.of_mapM_freshVal h4
    have cs5 := ((((CurSame.of_grows g1).trans (CurSame.of_grows g2)).trans
      (CurSame.of_newBlock h3)).trans (CurSame.of_grows g4)).trans
        (CurSame.of_newBlock h5)
    have a1 : SGrowsAt s.fn.blocks.size s s1 := SGrowsAt.of_grows g1
    have a2 := a1.trans (SGrowsAt.of_edgeArgs h2)
    have a3 := a2.trans (SGrowsAt.of_newBlock h3)
    have a4 := a3.trans (SGrowsAt.of_grows g4)
    have a5 := a4.trans (SGrowsAt.of_newBlock h5)
    have a6 := a5.trans (SGrowsAt.of_sealCur h6)
    have hbodyNe : s5.fn.curId ≠ bodyId := by
      rw [cs5.1, SGrowsAt.newBlock_id h3]
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hv a2.size)
    have hm57 := curMoved_of_seal_move hbodyNe h6 h7
    have hm : CurMoved s s7 := cs5.transMoved hm57
    have hbodyBase : s.fn.blocks.size ≤ bodyId := by
      rw [SGrowsAt.newBlock_id h3]
      exact a2.size
    have a7 := a6.trans (SGrowsAt.of_moveTo (Or.inl hbodyBase) h7)
    have hbodyLt : bodyId < s6.fn.blocks.size :=
      Nat.lt_of_lt_of_le (newBlock_target_lt h3)
        (((SGrowsAt.of_grows (N := 0) g4).trans
          (SGrowsAt.of_newBlock h5)).trans (SGrowsAt.of_sealCur h6)).size
    have hv7 := CurValid.of_moveTo hbodyLt h7
    obtain ⟨hv8, hk8⟩ := ih s7 renv s8 hv7 h8
    have gbody := trScope_grows fenv env lctx rets body s7 renv s8 h8
    have hjoinBase : s.fn.blocks.size ≤ joinId := by
      rw [SGrowsAt.newBlock_id h5]
      exact a4.size
    cases renv with
    | none =>
      obtain ⟨ua, sa, ha, hc2⟩ := M.bind_inv h
      obtain ⟨rfl, rfl⟩ := M.pure_inv hc2
      have g5a : SGrowsAt 0 s5 s8 := ((SGrowsAt.of_sealCur h6).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h7)).trans
          (gbody.mono (Nat.zero_le _))
      have hjoinLt : joinId < s8.fn.blocks.size :=
        Nat.lt_of_lt_of_le (newBlock_target_lt h5) g5a.size
      have hv' := CurValid.of_moveTo hjoinLt ha
      have gb : SGrowsAt s.fn.blocks.size s7 s' :=
        (gbody.mono a7.size).trans (SGrowsAt.of_moveTo (Or.inl hjoinBase) ha)
      exact ⟨hv', Or.inr (hm.forward hv a7 gb)⟩
    | some env' =>
      obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
      obtain ⟨uc, sc, hc2, hd2⟩ := M.bind_inv h
      obtain ⟨rfl, rfl⟩ := M.pure_inv hd2
      have g5sb : SGrowsAt 0 s5 sb := (((SGrowsAt.of_sealCur h6).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h7)).trans
          (gbody.mono (Nat.zero_le _))).trans
            ((SGrowsAt.of_edgeArgs ha).trans (SGrowsAt.of_sealCur hb2))
      have hjoinLt : joinId < sb.fn.blocks.size :=
        Nat.lt_of_lt_of_le (newBlock_target_lt h5) g5sb.size
      have hv' := CurValid.of_moveTo hjoinLt hc2
      have gb : SGrowsAt s.fn.blocks.size s7 s' :=
        (((gbody.mono a7.size).trans (SGrowsAt.of_edgeArgs ha)).trans
          (SGrowsAt.of_sealCur hb2)).trans
            (SGrowsAt.of_moveTo (Or.inl hjoinBase) hc2)
      exact ⟨hv', Or.inr (hm.forward hv a7 gb)⟩
  case switch =>
    intro fenv env lctx rets c cases dflt ih s r s' hv h
    unfold trStmt at h
    obtain ⟨sv, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨joinParams, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨joinId, s3, h3, h⟩ := M.bind_inv h
    obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
    obtain ⟨u5, s5, h5, h6⟩ := M.bind_inv h
    have g1 := trExpr_grows c fenv env s s1 sv h1
    have g2 := Grows.of_mapM_freshVal h2
    have cs3 := ((CurSame.of_grows g1).trans (CurSame.of_grows g2)).trans
      (CurSame.of_newBlock h3)
    have a1 : SGrowsAt s.fn.blocks.size s s1 := SGrowsAt.of_grows g1
    have a2 := a1.trans (SGrowsAt.of_grows g2)
    have a3 := a2.trans (SGrowsAt.of_newBlock h3)
    have hv3 := CurValid.of_same_sgrows hv a3 cs3.1
    have hh : CurValid s4 ∧ CurClosed s3 s4 := by
      apply ih 0 0
      · exact hv3
      · exact h4
    obtain ⟨hv4, hk4⟩ := hh
    have gcases : SGrows s3 s4 := by
      apply trCases_grows fenv env lctx rets 0 [] 0 cases dflt
      exact h4
    have hjoinBase : s.fn.blocks.size ≤ joinId := by
      rw [SGrowsAt.newBlock_id h3]
      exact a2.size
    have g3s4 : SGrowsAt 0 s3 s4 := gcases.mono (Nat.zero_le _)
    have hjoinLt : joinId < s4.fn.blocks.size :=
      Nat.lt_of_lt_of_le (newBlock_target_lt h3) g3s4.size
    have hv5 := CurValid.of_moveTo hjoinLt h5
    rcases hk4 with hm | hs
    · have hm0 : CurMoved s s4 := cs3.transMoved hm
      have a4 := a3.trans (gcases.mono a3.size)
      have hout : CurOpen s s5 := Or.inr (hm0.forward hv a4
        (SGrowsAt.of_moveTo (Or.inl hjoinBase) h5))
      obtain ⟨rfl, rfl⟩ := M.pure_inv h6
      exact ⟨hv5, hout⟩
    · have hm35 : CurMoved s3 s5 := by
        rcases hs with ⟨hc, b, hb, Δ, hi⟩
        rw [M.moveTo_apply] at h5
        obtain ⟨rfl, rfl⟩ := M.some_pair_inj h5
        have hne : s3.fn.curId ≠ joinId := by
          rw [cs3.1, SGrowsAt.newBlock_id h3]
          exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hv a2.size)
        exact ⟨hne, b, by simpa only [hc] using hb, Δ, hi⟩
      have hout : CurOpen s s5 := Or.inr (cs3.transMoved hm35)
      obtain ⟨rfl, rfl⟩ := M.pure_inv h6
      exact ⟨hv5, hout⟩
  case forLoop =>
    intro fenv env lctx rets init c post body ihInit ihBody ihPost s r s' hv h
    unfold trStmt at h
    obtain ⟨scope, s1, h1, h⟩ := M.bind_inv h
    obtain ⟨rinit, s2, h2, h⟩ := M.bind_inv h
    obtain ⟨hfn1, -⟩ := allocScope_funcsOnly h1
    have hv1 : CurValid s1 := by rw [CurValid, hfn1]; exact hv
    obtain ⟨hv2, hk2⟩ := ihInit scope s1 rinit s2 hv1 h2
    have a1 : SGrows s s1 := allocScope_sgrows h1
    have gi := trStmts_grows (scope :: fenv) env lctx rets false init
      s1 rinit s2 h2
    have a2 := a1.trans gi
    cases rinit with
    | none =>
      obtain ⟨rfl, rfl⟩ := M.pure_inv h
      exact ⟨hv2, CurOpen.transClosed hv a1 gi
        (Or.inl (CurSame.of_fnEq hfn1)) hk2⟩
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
      have hopen2 : CurOpen s s2 := CurOpen.trans hv a1 gi
        (Or.inl (CurSame.of_fnEq hfn1)) hk2
      have g3 := Grows.of_liftO h3
      have g4 := Grows.of_mapM_freshVal h4
      have g6 := Grows.of_mapM_freshVal h6
      have g8 := Grows.of_mapM_freshVal h8
      have cs9 := ((((((CurSame.of_grows g3).trans (CurSame.of_grows g4)).trans
        (CurSame.of_newBlock h5)).trans (CurSame.of_grows g6)).trans
          (CurSame.of_newBlock h7)).trans (CurSame.of_grows g8)).trans
            (CurSame.of_newBlock h9)
      have b3 : SGrowsAt s2.fn.blocks.size s2 s3 := SGrowsAt.of_grows g3
      have b4 := b3.trans (SGrowsAt.of_grows g4)
      have b5 := b4.trans (SGrowsAt.of_newBlock h5)
      have b6 := b5.trans (SGrowsAt.of_grows g6)
      have b7 := b6.trans (SGrowsAt.of_newBlock h7)
      have b8 := b7.trans (SGrowsAt.of_grows g8)
      have b9 := b8.trans (SGrowsAt.of_newBlock h9)
      have b10 := b9.trans (SGrowsAt.of_sealCur h10)
      have hheadNe : s9.fn.curId ≠ hId := by
        rw [cs9.1, SGrowsAt.newBlock_id h5]
        exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hv2 b4.size)
      have hm911 := curMoved_of_seal_move hheadNe h10 h11
      have hm2 : CurMoved s2 s11 := cs9.transMoved hm911
      have hhead2 : s2.fn.blocks.size ≤ hId := by
        rw [SGrowsAt.newBlock_id h5]
        exact b4.size
      have b11 := b10.trans (SGrowsAt.of_moveTo (Or.inl hhead2) h11)
      have hm : CurMoved s s11 := hopen2.transMoved hv a2 b11 hm2
      have a11 := a2.trans b11
      have hheadLt : hId < s10.fn.blocks.size :=
        Nat.lt_of_lt_of_le (newBlock_target_lt h5)
          (((((SGrowsAt.of_grows (N := 0) g6).trans
            (SGrowsAt.of_newBlock h7)).trans (SGrowsAt.of_grows g8)).trans
              (SGrowsAt.of_newBlock h9)).trans (SGrowsAt.of_sealCur h10)).size
      have hv11 := CurValid.of_moveTo hheadLt h11
      have gc := trExpr_grows c (scope :: fenv) _ s11 s12 cv h12
      have hv12 := hv11.of_grows gc
      have hv13 := CurValid.of_same_sgrows hv12
        (SGrowsAt.of_newBlock (N := s12.fn.blocks.size) h13)
        (CurSame.of_newBlock h13).1
      have hv14 := hv13.of_grows (Grows.of_liftO h14)
      have hs15 := curSealed_of_sealCur h15
      have hv15 := CurValid.of_same_sgrows hv14
        (SGrowsAt.of_sealCur (N := s14.fn.blocks.size) h15) hs15.1
      have hbodyLt : bodyId < s15.fn.blocks.size :=
        Nat.lt_of_lt_of_le (newBlock_target_lt h13)
          ((SGrowsAt.of_edgeArgs (N := 0) h14).trans
            (SGrowsAt.of_sealCur h15)).size
      have hv16 := CurValid.of_moveTo hbodyLt h16
      obtain ⟨hv17, hk17⟩ := ihBody scope envI hParams exitId postId
        s16 renvB s17 hv16 h17
      have gBody := trScope_grows (scope :: fenv) _ (some ⟨exitId, postId, _⟩)
        rets body s16 renvB s17 h17
      have hbodyBase : s.fn.blocks.size ≤ bodyId := by
        rw [SGrowsAt.newBlock_id h13]
        exact (a11.trans (SGrowsAt.of_grows gc)).size
      have q16 : SGrowsAt s.fn.blocks.size s11 s16 := ((((
        SGrowsAt.of_grows gc).trans (SGrowsAt.of_newBlock h13)).trans
          (SGrowsAt.of_edgeArgs h14)).trans (SGrowsAt.of_sealCur h15)).trans
            (SGrowsAt.of_moveTo (Or.inl hbodyBase) h16)
      have a16 : SGrowsAt s.fn.blocks.size s s16 := SGrowsAt.trans a11 q16
      have g7s11 : SGrowsAt 0 s7 s11 := ((SGrowsAt.of_grows g8).trans
        (SGrowsAt.of_newBlock h9)).trans ((SGrowsAt.of_sealCur h10).trans
          (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h11))
      have g11s16z : SGrowsAt 0 s11 s16 := ((((SGrowsAt.of_grows gc).trans
        (SGrowsAt.of_newBlock h13)).trans (SGrowsAt.of_edgeArgs h14)).trans
          (SGrowsAt.of_sealCur h15)).trans
            (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h16)
      have hpostBase : s.fn.blocks.size ≤ postId := by
        rw [SGrowsAt.newBlock_id h9]
        exact (a2.trans b8).size
      have hexitBase : s.fn.blocks.size ≤ exitId := by
        rw [SGrowsAt.newBlock_id h7]
        exact (a2.trans b6).size
      cases renvB with
      | none =>
        obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨renvP, sc, hc2, h⟩ := M.bind_inv h
        have g9s11 : SGrowsAt 0 s9 s11 := (SGrowsAt.of_sealCur h10).trans
          (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h11)
        have g9s17 : SGrowsAt 0 s9 s17 := (g9s11.trans g11s16z).trans
          (gBody.mono (Nat.zero_le _))
        have hpostLt : postId < s17.fn.blocks.size :=
          Nat.lt_of_lt_of_le (newBlock_target_lt h9) g9s17.size
        have hvb := CurValid.of_moveTo hpostLt ha
        obtain ⟨hvc, hkc⟩ := ihPost scope envI postParams sa renvP sc hvb hc2
        have gPost := trScope_grows (scope :: fenv) _ none rets post
          sa renvP sc hc2
        have qBody : SGrowsAt s.fn.blocks.size s16 s17 :=
          gBody.mono a16.size
        have qPostIn : SGrowsAt s.fn.blocks.size s11 sa :=
          (q16.trans qBody).trans (SGrowsAt.of_moveTo (Or.inl hpostBase) ha)
        cases renvP with
        | none =>
          obtain ⟨ue, se, he, hf⟩ := M.bind_inv h
          obtain ⟨rfl, rfl⟩ := M.pure_inv hf
          have g7sc : SGrowsAt 0 s7 sc := (g7s11.trans g11s16z).trans
            (((gBody.mono (Nat.zero_le _)).trans
              (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) ha)).trans
                (gPost.mono (Nat.zero_le _)))
          have hexitLt : exitId < sc.fn.blocks.size :=
            Nat.lt_of_lt_of_le (newBlock_target_lt h7) g7sc.size
          have hv' := CurValid.of_moveTo hexitLt he
          have qFinal := (qPostIn.trans (gPost.mono
            (Nat.le_trans a11.size qPostIn.size))).trans
            (SGrowsAt.of_moveTo (Or.inl hexitBase) he)
          exact ⟨hv', Or.inr (hm.forward hv a11 qFinal)⟩
        | some envP' =>
          obtain ⟨xvP, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, h⟩ := M.bind_inv h
          obtain ⟨uf, sf, hf, hg2⟩ := M.bind_inv h
          obtain ⟨rfl, rfl⟩ := M.pure_inv hg2
          have g16se : SGrowsAt 0 s16 se := ((((gBody.mono (Nat.zero_le _)).trans
            (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) ha)).trans
              (gPost.mono (Nat.zero_le _))).trans
                (SGrowsAt.of_edgeArgs hd)).trans (SGrowsAt.of_sealCur he)
          have g7se : SGrowsAt 0 s7 se := (g7s11.trans g11s16z).trans g16se
          have hexitLt : exitId < se.fn.blocks.size :=
            Nat.lt_of_lt_of_le (newBlock_target_lt h7) g7se.size
          have hv' := CurValid.of_moveTo hexitLt hf
          have qFinal := (((qPostIn.trans (gPost.mono
            (Nat.le_trans a11.size qPostIn.size))).trans
              (SGrowsAt.of_edgeArgs hd)).trans (SGrowsAt.of_sealCur he)).trans
                (SGrowsAt.of_moveTo (Or.inl hexitBase) hf)
          exact ⟨hv', Or.inr (hm.forward hv a11 qFinal)⟩
      | some envB =>
        obtain ⟨xvB, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ua', sa', ha', h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
        obtain ⟨renvP, sc, hc2, h⟩ := M.bind_inv h
        have g9s11 : SGrowsAt 0 s9 s11 := (SGrowsAt.of_sealCur h10).trans
          (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h11)
        have gBodyClosed0 : SGrowsAt 0 s16 sa' :=
          ((gBody.mono (Nat.zero_le _)).trans (SGrowsAt.of_edgeArgs ha)).trans
            (SGrowsAt.of_sealCur ha')
        have g9sa' : SGrowsAt 0 s9 sa' := (g9s11.trans g11s16z).trans
          gBodyClosed0
        have hpostLt : postId < sa'.fn.blocks.size :=
          Nat.lt_of_lt_of_le (newBlock_target_lt h9) g9sa'.size
        have hvb := CurValid.of_moveTo hpostLt hb2
        obtain ⟨hvc, hkc⟩ := ihPost scope envI postParams sb renvP sc hvb hc2
        have gPost := trScope_grows (scope :: fenv) _ none rets post
          sb renvP sc hc2
        have qBody : SGrowsAt s.fn.blocks.size s16 s17 :=
          gBody.mono a16.size
        have qPostIn : SGrowsAt s.fn.blocks.size s11 sb := ((((q16.trans qBody).trans
          (SGrowsAt.of_edgeArgs ha)).trans (SGrowsAt.of_sealCur ha')).trans
            (SGrowsAt.of_moveTo (Or.inl hpostBase) hb2))
        cases renvP with
        | none =>
          obtain ⟨ue, se, he, hf⟩ := M.bind_inv h
          obtain ⟨rfl, rfl⟩ := M.pure_inv hf
          have g7sc : SGrowsAt 0 s7 sc := (g7s11.trans g11s16z).trans
            ((gBodyClosed0.trans
              (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) hb2)).trans
                (gPost.mono (Nat.zero_le _)))
          have hexitLt : exitId < sc.fn.blocks.size :=
            Nat.lt_of_lt_of_le (newBlock_target_lt h7) g7sc.size
          have hv' := CurValid.of_moveTo hexitLt he
          have qFinal := (qPostIn.trans (gPost.mono
            (Nat.le_trans a11.size qPostIn.size))).trans
            (SGrowsAt.of_moveTo (Or.inl hexitBase) he)
          exact ⟨hv', Or.inr (hm.forward hv a11 qFinal)⟩
        | some envP' =>
          obtain ⟨xvP, sd, hd, h⟩ := M.bind_inv h
          obtain ⟨ue, se, he, h⟩ := M.bind_inv h
          obtain ⟨uf, sf, hf, hg2⟩ := M.bind_inv h
          obtain ⟨rfl, rfl⟩ := M.pure_inv hg2
          have g16se : SGrowsAt 0 s16 se := (((gBodyClosed0.trans
            (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) hb2)).trans
              (gPost.mono (Nat.zero_le _))).trans
                (SGrowsAt.of_edgeArgs hd)).trans (SGrowsAt.of_sealCur he)
          have g7se : SGrowsAt 0 s7 se := (g7s11.trans g11s16z).trans g16se
          have hexitLt : exitId < se.fn.blocks.size :=
            Nat.lt_of_lt_of_le (newBlock_target_lt h7) g7se.size
          have hv' := CurValid.of_moveTo hexitLt hf
          have qFinal := (((qPostIn.trans (gPost.mono
            (Nat.le_trans a11.size qPostIn.size))).trans
              (SGrowsAt.of_edgeArgs hd)).trans (SGrowsAt.of_sealCur he)).trans
                (SGrowsAt.of_moveTo (Or.inl hexitBase) hf)
          exact ⟨hv', Or.inr (hm.forward hv a11 qFinal)⟩
  case exprBuiltin =>
    intro fenv env lctx rets op args s r s' hv h
    rw [trStmt] at h
    obtain ⟨as, s₁, h1, h⟩ := M.bind_inv h
    have hg1 := trArgs_grows args fenv env s s₁ as h1
    by_cases hop : isHaltingOp op = true
    · rw [if_pos hop] at h
      obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
      obtain ⟨rfl, rfl⟩ := M.pure_inv h3
      have hseal := curSealed_of_sealCur h2
      refine ⟨CurValid.of_same_sgrows (hv.of_grows hg1)
        (SGrowsAt.of_sealCur (N := s₁.fn.blocks.size) h2) hseal.1, Or.inr ?_⟩
      rcases hseal with ⟨hc, b, hb, Δ, hi⟩
      rcases CurSame.of_grows hg1 with ⟨hc1, ⟨Δ1, hi1⟩, -⟩
      refine ⟨hc.trans hc1, b, by simpa only [hc1] using hb,
        Δ1.reverse ++ Δ, ?_⟩
      rw [hi, hi1]
      simp
    · rw [if_neg hop] at h
      obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
      obtain ⟨rfl, rfl⟩ := M.pure_inv h3
      have hg := hg1.trans (Grows.of_emit h2)
      exact ⟨hv.of_grows hg, Or.inl (CurSame.of_grows hg)⟩
  case exprCall =>
    intro fenv env lctx rets fn args s r s' hv h
    rw [trStmt] at h
    obtain ⟨as, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨fid, s₂, h2, h⟩ := M.bind_inv h
    obtain ⟨u, s₃, h3, h4⟩ := M.bind_inv h
    obtain ⟨rfl, rfl⟩ := M.pure_inv h4
    have hg := (trArgs_grows args fenv env s s₁ as h1).trans
      ((Grows.of_liftO h2).trans (Grows.of_emit h3))
    exact ⟨hv.of_grows hg, Or.inl (CurSame.of_grows hg)⟩
  case exprBad =>
    intro fenv env lctx rets e hnb hnc s r s' hv h
    rw [trStmt] at h
    · exact absurd h (by simp [reject])
    · exact hnb
    · exact hnc
  case breakNone =>
    intro fenv env rets s r s' hv h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case breakSome =>
    intro fenv env rets l s r s' hv h
    rw [trStmt] at h
    obtain ⟨vals, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    obtain ⟨rfl, rfl⟩ := M.pure_inv h3
    have hg1 := Grows.of_liftO h1
    have hs := curSealed_of_sealCur h2
    refine ⟨CurValid.of_same_sgrows (hv.of_grows hg1)
      (SGrowsAt.of_sealCur (N := s₁.fn.blocks.size) h2) hs.1, Or.inr ?_⟩
    rcases hs with ⟨hc, b, hb, Δ, hi⟩
    rcases CurSame.of_grows hg1 with ⟨hc1, ⟨Δ1, hi1⟩, -⟩
    refine ⟨hc.trans hc1, b, by simpa only [hc1] using hb,
      Δ1.reverse ++ Δ, ?_⟩
    rw [hi, hi1]
    simp
  case contNone =>
    intro fenv env rets s r s' hv h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case contSome =>
    intro fenv env rets l s r s' hv h
    rw [trStmt] at h
    obtain ⟨vals, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    obtain ⟨rfl, rfl⟩ := M.pure_inv h3
    have hg1 := Grows.of_liftO h1
    have hs := curSealed_of_sealCur h2
    refine ⟨CurValid.of_same_sgrows (hv.of_grows hg1)
      (SGrowsAt.of_sealCur (N := s₁.fn.blocks.size) h2) hs.1, Or.inr ?_⟩
    rcases hs with ⟨hc, b, hb, Δ, hi⟩
    rcases CurSame.of_grows hg1 with ⟨hc1, ⟨Δ1, hi1⟩, -⟩
    refine ⟨hc.trans hc1, b, by simpa only [hc1] using hb,
      Δ1.reverse ++ Δ, ?_⟩
    rw [hi, hi1]
    simp
  case leaveNone =>
    intro fenv env lctx s r s' hv h
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  case leaveSome =>
    intro fenv env lctx rs s r s' hv h
    rw [trStmt] at h
    obtain ⟨vals, s₁, h1, h⟩ := M.bind_inv h
    obtain ⟨u, s₂, h2, h3⟩ := M.bind_inv h
    obtain ⟨rfl, rfl⟩ := M.pure_inv h3
    have hg1 := Grows.of_liftO h1
    have hs := curSealed_of_sealCur h2
    refine ⟨CurValid.of_same_sgrows (hv.of_grows hg1)
      (SGrowsAt.of_sealCur (N := s₁.fn.blocks.size) h2) hs.1, Or.inr ?_⟩
    rcases hs with ⟨hc, b, hb, Δ, hi⟩
    rcases CurSame.of_grows hg1 with ⟨hc1, ⟨Δ1, hi1⟩, -⟩
    refine ⟨hc.trans hc1, b, by simpa only [hc1] using hb,
      Δ1.reverse ++ Δ, ?_⟩
    rw [hi, hi1]
    simp
  case casesNilNone =>
    intro fenv env lctx rets _sv _X _joinId sv X joinId s u s' hv h
    rw [trCases] at h
    obtain ⟨xvals, s₁, h1, h2⟩ := M.bind_inv h
    have hg1 := Grows.of_liftO h1
    have hs := curSealed_of_sealCur h2
    refine ⟨CurValid.of_same_sgrows (hv.of_grows hg1)
      (SGrowsAt.of_sealCur (N := s₁.fn.blocks.size) h2) hs.1, Or.inr ?_⟩
    rcases hs with ⟨hc, b, hb, Δ, hi⟩
    rcases CurSame.of_grows hg1 with ⟨hc1, ⟨Δ1, hi1⟩, -⟩
    refine ⟨hc.trans hc1, b, by simpa only [hc1] using hb,
      Δ1.reverse ++ Δ, ?_⟩
    rw [hi, hi1]
    simp
  case casesNilSome =>
    intro fenv env lctx rets _sv _X _joinId dbody ih sv X joinId s u s' hv h
    rw [trCases] at h
    obtain ⟨renv, s₁, h1, h2⟩ := M.bind_inv h
    obtain ⟨hv1, hk1⟩ := ih s renv s₁ hv h1
    have hg1 := trScope_grows fenv env lctx rets dbody s renv s₁ h1
    cases renv with
    | none =>
      obtain ⟨rfl, rfl⟩ := M.pure_inv h2
      exact ⟨hv1, hk1⟩
    | some env' =>
      obtain ⟨xv, s₂, h3, h4⟩ := M.bind_inv h2
      have hgE := Grows.of_liftO h3
      have hs := curSealed_of_sealCur h4
      have hv2 := hv1.of_grows hgE
      have hv' := CurValid.of_same_sgrows hv2
        (SGrowsAt.of_sealCur (N := s₂.fn.blocks.size) h4) hs.1
      have hclosed : CurClosed s₁ s' := by
        refine Or.inr ?_
        rcases hs with ⟨hc, b, hb, Δ, hi⟩
        rcases CurSame.of_grows hgE with ⟨hc1, ⟨Δ1, hi1⟩, -⟩
        refine ⟨hc.trans hc1, b, by simpa only [hc1] using hb,
          Δ1.reverse ++ Δ, ?_⟩
        rw [hi, hi1]
        simp
      exact ⟨hv', CurOpen.transClosed hv hg1
        (SGrows.trans (SGrows.of_grows hgE) (SGrowsAt.of_sealCur h4))
        hk1 hclosed⟩
  case casesCons =>
    intro fenv env lctx rets _sv _X _joinId lit cbody restCases dflt ihc ihr
      sv X joinId s u s' hv h
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
    have g1 := Grows.of_freshVal h1
    have g2 := Grows.of_emit h2
    have g3 := Grows.of_freshVal h3
    have g4 := Grows.of_emit h4
    have cs4 := (((CurSame.of_grows g1).trans (CurSame.of_grows g2)).trans
      (CurSame.of_grows g3)).trans (CurSame.of_grows g4)
    have cs5 := cs4.trans (CurSame.of_newBlock h5)
    have cs6 := cs5.trans (CurSame.of_newBlock h6)
    have a1 : SGrowsAt s.fn.blocks.size s s1 := SGrowsAt.of_grows g1
    have a2 := a1.trans (SGrowsAt.of_grows g2)
    have a3 := a2.trans (SGrowsAt.of_grows g3)
    have a4 := a3.trans (SGrowsAt.of_grows g4)
    have a5 := a4.trans (SGrowsAt.of_newBlock h5)
    have a6 := a5.trans (SGrowsAt.of_newBlock h6)
    have a7 := a6.trans (SGrowsAt.of_sealCur h7)
    have hcaseNe : s6.fn.curId ≠ caseId := by
      have hid := SGrowsAt.newBlock_id h5
      rw [cs6.1, hid]
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hv a4.size)
    have hm68 : CurMoved s6 s8 := curMoved_of_seal_move hcaseNe h7 h8
    have hm : CurMoved s s8 := cs6.transMoved hm68
    have a8 := a7.trans (SGrowsAt.of_moveTo
      (Or.inl (by rw [SGrowsAt.newBlock_id h5]; exact a4.size)) h8)
    have hcaseLt : caseId < s7.fn.blocks.size := by
      exact Nat.lt_of_lt_of_le (newBlock_target_lt h5)
        ((SGrowsAt.of_newBlock (N := 0) h6).trans
          (SGrowsAt.of_sealCur h7)).size
    have hv8 : CurValid s8 := CurValid.of_moveTo hcaseLt h8
    obtain ⟨hv9, hk9⟩ := ihc s8 renv s9 hv8 h9
    have gbody := trScope_grows fenv env lctx rets cbody s8 renv s9 h9
    cases renv with
    | none =>
      obtain ⟨ua, sa, ha, hc2⟩ := M.bind_inv h
      have g6a : SGrowsAt 0 s6 s9 := ((SGrowsAt.of_sealCur h7).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h8)).trans
          (gbody.mono (Nat.zero_le _))
      have hnextLt : nextId < s9.fn.blocks.size :=
        Nat.lt_of_lt_of_le (newBlock_target_lt h6) g6a.size
      have hvb : CurValid sa := CurValid.of_moveTo hnextLt ha
      obtain ⟨hv', hkrest⟩ := ihr sv X joinId sa u s' hvb hc2
      have hnextBase : s.fn.blocks.size ≤ nextId := by
        rw [SGrowsAt.newBlock_id h6]
        exact a5.size
      have gb : SGrowsAt s.fn.blocks.size s8 sa :=
        (gbody.mono a8.size).trans
          (SGrowsAt.of_moveTo (Or.inl hnextBase) ha)
      have gr := trCases_grows fenv env lctx rets sv X joinId restCases dflt
        sv X joinId sa u s' hc2
      exact ⟨hv', Or.inl (hm.forward hv a8
        (gb.trans (gr.mono (Nat.le_trans a8.size gb.size))))⟩
    | some env' =>
      obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
      obtain ⟨uc, sc, hc2, hd2⟩ := M.bind_inv h
      have g6sb : SGrowsAt 0 s6 sb := (((SGrowsAt.of_sealCur h7).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h8)).trans
          (gbody.mono (Nat.zero_le _))).trans
            ((SGrowsAt.of_edgeArgs ha).trans (SGrowsAt.of_sealCur hb2))
      have hnextLt : nextId < sb.fn.blocks.size :=
        Nat.lt_of_lt_of_le (newBlock_target_lt h6) g6sb.size
      have hvc : CurValid sc := CurValid.of_moveTo hnextLt hc2
      obtain ⟨hv', hkrest⟩ := ihr sv X joinId sc u s' hvc hd2
      have hnextBase : s.fn.blocks.size ≤ nextId := by
        rw [SGrowsAt.newBlock_id h6]
        exact a5.size
      have gb : SGrowsAt s.fn.blocks.size s8 sc :=
        (((gbody.mono a8.size).trans (SGrowsAt.of_edgeArgs ha)).trans
          (SGrowsAt.of_sealCur hb2)).trans
            (SGrowsAt.of_moveTo (Or.inl hnextBase) hc2)
      have gr := trCases_grows fenv env lctx rets sv X joinId restCases dflt
        sv X joinId sc u s' hd2
      exact ⟨hv', Or.inl (hm.forward hv a8
        (gb.trans (gr.mono (Nat.le_trans a8.size gb.size))))⟩

omit model in
/-- A diverting scope has no pending instructions in its current block.

This is deliberately separate from `CurResult`: the latter records how the
*incoming* block is preserved, whereas this fact is about the output selected
by a later structured-control `moveTo`. -/
theorem trScope_none_cur_nil : ∀ (fenv : FMap) (env : VMap)
    (lctx : Option LoopCtx) (rets : Option (List Ident))
    (body : List (Stmt Op)) (s s' : BState),
    trScope fenv env lctx rets body s = some (none, s') → s'.fn.cur = [] := by
  let ScopeNil := fun (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (body : List (Stmt Op)) =>
      ∀ (s s' : BState),
        trScope fenv env lctx rets body s = some (none, s') → s'.fn.cur = []
  let StmtsNil := fun (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (d : Bool) (ss : List (Stmt Op)) =>
      if d then True else ∀ (s s' : BState),
        trStmts fenv env lctx rets d ss s = some (none, s') → s'.fn.cur = []
  let StmtNil := fun (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (st : Stmt Op) =>
      ∀ (s s' : BState),
        trStmt fenv env lctx rets st s = some (none, s') → s'.fn.cur = []
  have hall : ∀ (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
      (rets : Option (List Ident)) (d : Bool) (body : List (Stmt Op)),
      StmtsNil fenv env lctx rets d body := by
    refine trStmts.induct (fun _ _ _ _ => True) ScopeNil StmtsNil StmtNil
      (fun _ _ _ _ _ _ _ _ _ => True)
      ?trFunc ?trScope ?stmtsNil ?stmtsFunDef ?stmtsSkip ?stmtsCons
      ?block ?funDef ?letNoneBad ?letNone ?letSomeBad ?letSome ?assignBad ?assign
      ?cond ?switch ?forLoop ?exprBuiltin ?exprCall ?exprBad
      ?breakNone ?breakSome ?contNone ?contSome ?leaveNone ?leaveSome
      ?casesNilNone ?casesNilSome ?casesCons
    case trFunc => intros; trivial
    case trScope =>
      intro fenv env lctx rets body ih s s' h
      rw [trScope] at h
      obtain ⟨scope, s1, h1, h⟩ := M.bind_inv h
      obtain ⟨renv, s2, h2, h3⟩ := M.bind_inv h
      cases renv with
      | none =>
        obtain ⟨-, hs⟩ := M.pure_inv h3
        rw [hs]
        exact ih scope s1 s2 h2
      | some env' => exact absurd h3 (by simp)
    case stmtsNil =>
      intro fenv env lctx rets d
      cases d <;> simp only [StmtsNil, Bool.false_eq_true, ↓reduceIte]
      intro s s' h
      rw [trStmts] at h
      exact absurd h (by simp)
    case stmtsFunDef =>
      intro fenv env lctx rets d n ps rs fbody rest ihf ihr
      cases d with
      | true => simp [StmtsNil]
      | false =>
        simp only [StmtsNil, Bool.false_eq_true, ↓reduceIte]
        intro s s' h
        rw [trStmts] at h
        obtain ⟨fid, s1, h1, h⟩ := M.bind_inv h
        obtain ⟨g, s2, h2, h⟩ := M.bind_inv h
        obtain ⟨u, s3, h3, h4⟩ := M.bind_inv h
        exact ihr s3 s' h4
    case stmtsSkip => intros; simp [StmtsNil]
    case stmtsCons =>
      intro fenv env lctx rets d st rest hnf hd ihs ihr0 ihr1
      have hd0 : d = false := Bool.eq_false_of_not_eq_true hd
      subst d
      simp only [StmtsNil, Bool.false_eq_true, ↓reduceIte]
      intro s s' h
      rw [trStmts] at h
      · rw [if_neg hd] at h
        obtain ⟨renv, s1, h1, h2⟩ := M.bind_inv h
        cases renv with
        | some env' => exact ihr0 env' s1 s' h2
        | none =>
          obtain ⟨-, hfn⟩ := trStmts_true_fn fenv env lctx rets rest
            s1 s' none h2
          rw [hfn]
          exact ihs s s1 h1
      · exact hnf
    case block =>
      intro fenv env lctx rets body ih s s' h
      rw [trStmt] at h
      exact ih s s' h
    case funDef =>
      intro fenv env lctx rets name ps rs body s s' h
      rw [trStmt] at h
      exact absurd h (by simp [reject])
    case letNoneBad =>
      intro fenv env lctx rets vars hgate s s' h
      rw [trStmt, if_pos hgate] at h
      obtain ⟨u, s1, h1, -⟩ := M.bind_inv h
      exact absurd h1 (by simp [reject])
    case letNone =>
      intro fenv env lctx rets vars hgate s s' h
      rw [trStmt, if_neg hgate] at h
      obtain ⟨ids, s1, h1, h2⟩ := M.bind_inv h
      exact absurd h2 (by simp)
    case letSomeBad =>
      intro fenv env lctx rets vars e hgate s s' h
      rw [trStmt, if_pos hgate] at h
      obtain ⟨u, s1, h1, -⟩ := M.bind_inv h
      exact absurd h1 (by simp [reject])
    case letSome =>
      intro fenv env lctx rets vars e hgate s s' h
      rw [trStmt, if_neg hgate] at h
      obtain ⟨ids, s1, h1, h2⟩ := M.bind_inv h
      exact absurd h2 (by simp)
    case assignBad =>
      intro fenv env lctx rets vars e hgate s s' h
      rw [trStmt, if_pos hgate] at h
      obtain ⟨u, s1, h1, -⟩ := M.bind_inv h
      exact absurd h1 (by simp [reject])
    case assign =>
      intro fenv env lctx rets vars e hgate s s' h
      rw [trStmt, if_neg hgate] at h
      obtain ⟨ids, s1, h1, h2⟩ := M.bind_inv h
      exact absurd h2 (by simp)
    case cond =>
      intro fenv env lctx rets c body ih s s' h
      rw [trStmt] at h
      obtain ⟨cv, s1, h1, h⟩ := M.bind_inv h
      obtain ⟨xvals, s2, h2, h⟩ := M.bind_inv h
      obtain ⟨bodyId, s3, h3, h⟩ := M.bind_inv h
      obtain ⟨joinParams, s4, h4, h⟩ := M.bind_inv h
      obtain ⟨joinId, s5, h5, h⟩ := M.bind_inv h
      obtain ⟨u6, s6, h6, h⟩ := M.bind_inv h
      obtain ⟨u7, s7, h7, h⟩ := M.bind_inv h
      obtain ⟨renv, s8, h8, h⟩ := M.bind_inv h
      cases renv with
      | none =>
        obtain ⟨u9, s9, h9, h10⟩ := M.bind_inv h
        exact absurd h10 (by simp)
      | some env' =>
        obtain ⟨xv, s9, h9, h⟩ := M.bind_inv h
        obtain ⟨u10, s10, h10, h⟩ := M.bind_inv h
        obtain ⟨u11, s11, h11, h12⟩ := M.bind_inv h
        exact absurd h12 (by simp)
    case switch =>
      intro fenv env lctx rets c cases dflt ih s s' h
      unfold trStmt at h
      obtain ⟨sv, s1, h1, h⟩ := M.bind_inv h
      obtain ⟨joinParams, s2, h2, h⟩ := M.bind_inv h
      obtain ⟨joinId, s3, h3, h⟩ := M.bind_inv h
      obtain ⟨u4, s4, h4, h⟩ := M.bind_inv h
      obtain ⟨u5, s5, h5, h6⟩ := M.bind_inv h
      exact absurd h6 (by simp)
    case forLoop =>
      intro fenv env lctx rets init c post body ihInit ihBody ihPost s s' h
      unfold trStmt at h
      obtain ⟨scope, s1, h1, h⟩ := M.bind_inv h
      obtain ⟨rinit, s2, h2, h⟩ := M.bind_inv h
      cases rinit with
      | none =>
        obtain ⟨-, hs⟩ := M.pure_inv h
        rw [hs]
        exact ihInit scope s1 s2 h2
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
        cases renvB with
        | none =>
          obtain ⟨u18, s18, h18, h⟩ := M.bind_inv h
          obtain ⟨renvP, s20, h20, h⟩ := M.bind_inv h
          cases renvP with
          | none =>
            obtain ⟨u21, s21, h21, h22⟩ := M.bind_inv h
            exact absurd h22 (by simp)
          | some envP =>
            obtain ⟨xvP, s21, h21, h⟩ := M.bind_inv h
            obtain ⟨u22, s22, h22, h⟩ := M.bind_inv h
            obtain ⟨u23, s23, h23, h⟩ := M.bind_inv h
            exact absurd h (by simp)
        | some envB =>
          obtain ⟨xvB, s18, h18, h⟩ := M.bind_inv h
          obtain ⟨u19, s19, h19, h⟩ := M.bind_inv h
          obtain ⟨u20, s20, h20, h⟩ := M.bind_inv h
          obtain ⟨renvP, s21, h21, h⟩ := M.bind_inv h
          cases renvP with
          | none =>
            obtain ⟨u22, s22, h22, h23⟩ := M.bind_inv h
            exact absurd h23 (by simp)
          | some envP =>
            obtain ⟨xvP, s22, h22, h⟩ := M.bind_inv h
            obtain ⟨u23, s23, h23, h⟩ := M.bind_inv h
            obtain ⟨u24, s24, h24, h25⟩ := M.bind_inv h
            exact absurd h25 (by simp)
    case exprBuiltin =>
      intro fenv env lctx rets op args s s' h
      rw [trStmt] at h
      obtain ⟨as, s1, h1, h⟩ := M.bind_inv h
      by_cases hop : isHaltingOp op = true
      · rw [if_pos hop] at h
        obtain ⟨u, s2, h2, h3⟩ := M.bind_inv h
        obtain ⟨-, rfl⟩ := M.pure_inv h3
        exact (sealCur_cur h2).choose_spec.2.1
      · rw [if_neg hop] at h
        obtain ⟨u, s2, h2, h3⟩ := M.bind_inv h
        exact absurd h3 (by simp)
    case exprCall =>
      intro fenv env lctx rets fn args s s' h
      rw [trStmt] at h
      obtain ⟨as, s1, h1, h⟩ := M.bind_inv h
      obtain ⟨fid, s2, h2, h⟩ := M.bind_inv h
      obtain ⟨u, s3, h3, h4⟩ := M.bind_inv h
      exact absurd h4 (by simp)
    case exprBad =>
      intro fenv env lctx rets e hnb hnc s s' h
      rw [trStmt] at h
      · exact absurd h (by simp [reject])
      · exact hnb
      · exact hnc
    case breakNone =>
      intro fenv env rets s s' h
      rw [trStmt] at h
      exact absurd h (by simp [reject])
    case breakSome =>
      intro fenv env rets l s s' h
      rw [trStmt] at h
      obtain ⟨vals, s1, h1, h⟩ := M.bind_inv h
      obtain ⟨u, s2, h2, h3⟩ := M.bind_inv h
      obtain ⟨-, rfl⟩ := M.pure_inv h3
      exact (sealCur_cur h2).choose_spec.2.1
    case contNone =>
      intro fenv env rets s s' h
      rw [trStmt] at h
      exact absurd h (by simp [reject])
    case contSome =>
      intro fenv env rets l s s' h
      rw [trStmt] at h
      obtain ⟨vals, s1, h1, h⟩ := M.bind_inv h
      obtain ⟨u, s2, h2, h3⟩ := M.bind_inv h
      obtain ⟨-, rfl⟩ := M.pure_inv h3
      exact (sealCur_cur h2).choose_spec.2.1
    case leaveNone =>
      intro fenv env lctx s s' h
      rw [trStmt] at h
      exact absurd h (by simp [reject])
    case leaveSome =>
      intro fenv env lctx rs s s' h
      rw [trStmt] at h
      obtain ⟨vals, s1, h1, h⟩ := M.bind_inv h
      obtain ⟨u, s2, h2, h3⟩ := M.bind_inv h
      obtain ⟨-, rfl⟩ := M.pure_inv h3
      exact (sealCur_cur h2).choose_spec.2.1
    case casesNilNone => intros; trivial
    case casesNilSome => intros; trivial
    case casesCons => intros; trivial
  intro fenv env lctx rets body s s' h
  rw [trScope] at h
  obtain ⟨scope, s1, h1, h⟩ := M.bind_inv h
  obtain ⟨renv, s2, h2, h3⟩ := M.bind_inv h
  cases renv with
  | none =>
    obtain ⟨-, hs⟩ := M.pure_inv h3
    rw [hs]
    exact hall (scope :: fenv) env lctx rets false body s1 s2 h2
  | some env' => exact absurd h3 (by simp)

omit model in
/-- Every completed switch dispatch chain ends in a sealed block. -/
theorem trCases_cur_nil (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (sv : ValId) (X : List Ident)
    (joinId : BlockId) (cs : List (Literal × List (Stmt Op)))
    (df : Option (List (Stmt Op))) (s s' : BState) (u : Unit)
    (h : trCases fenv env lctx rets sv X joinId cs df s = some (u, s')) :
    s'.fn.cur = [] := by
  induction cs generalizing s with
  | nil =>
    cases df with
    | none =>
      rw [trCases] at h
      obtain ⟨xv, sA, h1, h2⟩ := M.bind_inv h
      exact (sealCur_cur h2).choose_spec.2.1
    | some body =>
      rw [trCases] at h
      obtain ⟨renv, sA, h1, h2⟩ := M.bind_inv h
      cases renv with
      | none =>
        obtain ⟨-, rfl⟩ := M.pure_inv h2
        exact trScope_none_cur_nil fenv env lctx rets body s s' h1
      | some env' =>
        obtain ⟨xv, sB, h3, h4⟩ := M.bind_inv h2
        exact (sealCur_cur h4).choose_spec.2.1
  | cons p rest ih =>
    obtain ⟨lit, body⟩ := p
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
    cases renv with
    | none =>
      obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
      exact ih sa h
    | some env' =>
      obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb, h⟩ := M.bind_inv h
      obtain ⟨uc, sc, hc, hd⟩ := M.bind_inv h
      exact ih sc hd

omit model in
/-- Statement-current validity as a corollary of the list invariant, using a
singleton list.  Function definitions are handled by `trStmts` itself and are
rejected by `trStmt`. -/
theorem trStmt_cur {fenv : FMap} {env : VMap} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {st : Stmt Op} {s s' : BState}
    {renv : Option VMap} (hv : CurValid s)
    (h : trStmt fenv env lctx rets st s = some (renv, s')) :
    CurValid s' ∧ CurResult renv s s' := by
  cases st with
  | funDef n ps rs body =>
    rw [trStmt] at h
    exact absurd h (by simp [reject])
  | block body =>
    apply trStmts_cur fenv env lctx rets false [.block body] s renv s' hv
    rw [trStmts] <;> try { intros; contradiction }
    simp only [Bool.false_eq_true, if_false]
    rw [M.bind_eq, h]; cases renv <;> simp [trStmts]
  | letDecl vars val =>
    apply trStmts_cur fenv env lctx rets false [.letDecl vars val] s renv s' hv
    rw [trStmts] <;> try { intros; contradiction }
    simp only [Bool.false_eq_true, if_false]
    rw [M.bind_eq, h]; cases renv <;> simp [trStmts]
  | assign vars e =>
    apply trStmts_cur fenv env lctx rets false [.assign vars e] s renv s' hv
    rw [trStmts] <;> try { intros; contradiction }
    simp only [Bool.false_eq_true, if_false]
    rw [M.bind_eq, h]; cases renv <;> simp [trStmts]
  | cond e body =>
    apply trStmts_cur fenv env lctx rets false [.cond e body] s renv s' hv
    rw [trStmts] <;> try { intros; contradiction }
    simp only [Bool.false_eq_true, if_false]
    rw [M.bind_eq, h]; cases renv <;> simp [trStmts]
  | switch e cases dflt =>
    apply trStmts_cur fenv env lctx rets false [.switch e cases dflt] s renv s' hv
    rw [trStmts] <;> try { intros; contradiction }
    simp only [Bool.false_eq_true, if_false]
    rw [M.bind_eq, h]; cases renv <;> simp [trStmts]
  | forLoop init e post body =>
    apply trStmts_cur fenv env lctx rets false [.forLoop init e post body] s renv s' hv
    rw [trStmts] <;> try { intros; contradiction }
    simp only [Bool.false_eq_true, if_false]
    rw [M.bind_eq, h]; cases renv <;> simp [trStmts]
  | exprStmt e =>
    apply trStmts_cur fenv env lctx rets false [.exprStmt e] s renv s' hv
    rw [trStmts] <;> try { intros; contradiction }
    simp only [Bool.false_eq_true, if_false]
    rw [M.bind_eq, h]; cases renv <;> simp [trStmts]
  | «break» =>
    apply trStmts_cur fenv env lctx rets false [.break] s renv s' hv
    rw [trStmts] <;> try { intros; contradiction }
    simp only [Bool.false_eq_true, if_false]
    rw [M.bind_eq, h]; cases renv <;> simp [trStmts]
  | «continue» =>
    apply trStmts_cur fenv env lctx rets false [.continue] s renv s' hv
    rw [trStmts] <;> try { intros; contradiction }
    simp only [Bool.false_eq_true, if_false]
    rw [M.bind_eq, h]; cases renv <;> simp [trStmts]
  | leave =>
    apply trStmts_cur fenv env lctx rets false [.leave] s renv s' hv
    rw [trStmts] <;> try { intros; contradiction }
    simp only [Bool.false_eq_true, if_false]
    rw [M.bind_eq, h]
    cases renv <;> simp [trStmts]

omit model in
/-- Switch dispatch always seals the block in which it starts.  This is the
standalone `trCases` specialization of the mutual current-shape invariant. -/
theorem trCases_cur_closed (fenv : FMap) (env : VMap)
    (lctx : Option LoopCtx) (rets : Option (List Ident)) (sv : ValId)
    (X : List Ident) (joinId : BlockId)
    (cs : List (Literal × List (Stmt Op)))
    (df : Option (List (Stmt Op))) (s s' : BState) (u : Unit)
    (hv : CurValid s)
    (h : trCases fenv env lctx rets sv X joinId cs df s = some (u, s')) :
    CurValid s' ∧ CurClosed s s' := by
  induction cs generalizing s with
  | nil =>
    cases df with
    | none =>
      rw [trCases] at h
      obtain ⟨xvals, s₁, h1, h2⟩ := M.bind_inv h
      have hg1 := Grows.of_liftO h1
      have hs := curSealed_of_sealCur h2
      refine ⟨CurValid.of_same_sgrows (hv.of_grows hg1)
        (SGrowsAt.of_sealCur (N := s₁.fn.blocks.size) h2) hs.1, Or.inr ?_⟩
      rcases hs with ⟨hc, b, hb, Δ, hi⟩
      rcases CurSame.of_grows hg1 with ⟨hc1, ⟨Δ1, hi1⟩, -⟩
      refine ⟨hc.trans hc1, b, by simpa only [hc1] using hb,
        Δ1.reverse ++ Δ, ?_⟩
      rw [hi, hi1]
      simp
    | some dbody =>
      rw [trCases] at h
      obtain ⟨renv, s₁, h1, h2⟩ := M.bind_inv h
      have h1' : trStmt fenv env lctx rets (.block dbody) s = some (renv, s₁) := by
        rw [trStmt]
        exact h1
      obtain ⟨hv1, hk1⟩ := trStmt_cur hv h1'
      have hg1 := trScope_grows fenv env lctx rets dbody s renv s₁ h1
      cases renv with
      | none =>
        obtain ⟨rfl, rfl⟩ := M.pure_inv h2
        exact ⟨hv1, hk1⟩
      | some env' =>
        obtain ⟨xv, s₂, h3, h4⟩ := M.bind_inv h2
        have hgE := Grows.of_liftO h3
        have hs := curSealed_of_sealCur h4
        have hv2 := hv1.of_grows hgE
        have hv' := CurValid.of_same_sgrows hv2
          (SGrowsAt.of_sealCur (N := s₂.fn.blocks.size) h4) hs.1
        have hclosed : CurClosed s₁ s' := by
          refine Or.inr ?_
          rcases hs with ⟨hc, b, hb, Δ, hi⟩
          rcases CurSame.of_grows hgE with ⟨hc1, ⟨Δ1, hi1⟩, -⟩
          refine ⟨hc.trans hc1, b, by simpa only [hc1] using hb,
            Δ1.reverse ++ Δ, ?_⟩
          rw [hi, hi1]
          simp
        exact ⟨hv', CurOpen.transClosed hv hg1
          (SGrows.trans (SGrows.of_grows hgE) (SGrowsAt.of_sealCur h4))
          hk1 hclosed⟩
  | cons p rest ih =>
    obtain ⟨lit, cbody⟩ := p
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
    have g1 := Grows.of_freshVal h1
    have g2 := Grows.of_emit h2
    have g3 := Grows.of_freshVal h3
    have g4 := Grows.of_emit h4
    have cs4 := (((CurSame.of_grows g1).trans (CurSame.of_grows g2)).trans
      (CurSame.of_grows g3)).trans (CurSame.of_grows g4)
    have cs5 := cs4.trans (CurSame.of_newBlock h5)
    have cs6 := cs5.trans (CurSame.of_newBlock h6)
    have a1 : SGrowsAt s.fn.blocks.size s s1 := SGrowsAt.of_grows g1
    have a2 := a1.trans (SGrowsAt.of_grows g2)
    have a3 := a2.trans (SGrowsAt.of_grows g3)
    have a4 := a3.trans (SGrowsAt.of_grows g4)
    have a5 := a4.trans (SGrowsAt.of_newBlock h5)
    have a6 := a5.trans (SGrowsAt.of_newBlock h6)
    have a7 := a6.trans (SGrowsAt.of_sealCur h7)
    have hcaseNe : s6.fn.curId ≠ caseId := by
      rw [cs6.1, SGrowsAt.newBlock_id h5]
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hv a4.size)
    have hm68 : CurMoved s6 s8 := curMoved_of_seal_move hcaseNe h7 h8
    have hm : CurMoved s s8 := cs6.transMoved hm68
    have a8 := a7.trans (SGrowsAt.of_moveTo
      (Or.inl (by rw [SGrowsAt.newBlock_id h5]; exact a4.size)) h8)
    have hcaseLt : caseId < s7.fn.blocks.size :=
      Nat.lt_of_lt_of_le (newBlock_target_lt h5)
        ((SGrowsAt.of_newBlock (N := 0) h6).trans
          (SGrowsAt.of_sealCur h7)).size
    have hv8 : CurValid s8 := CurValid.of_moveTo hcaseLt h8
    have gbody := trScope_grows fenv env lctx rets cbody s8 renv s9 h9
    cases renv with
    | none =>
      obtain ⟨ua, sa, ha, hc2⟩ := M.bind_inv h
      have g6a : SGrowsAt 0 s6 s9 := ((SGrowsAt.of_sealCur h7).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h8)).trans
          (gbody.mono (Nat.zero_le _))
      have hnextLt : nextId < s9.fn.blocks.size :=
        Nat.lt_of_lt_of_le (newBlock_target_lt h6) g6a.size
      have hvb : CurValid sa := CurValid.of_moveTo hnextLt ha
      obtain ⟨hv', -⟩ := ih sa hvb hc2
      have hnextBase : s.fn.blocks.size ≤ nextId := by
        rw [SGrowsAt.newBlock_id h6]
        exact a5.size
      have gb : SGrowsAt s.fn.blocks.size s8 sa :=
        (gbody.mono a8.size).trans
          (SGrowsAt.of_moveTo (Or.inl hnextBase) ha)
      have gr := trCases_grows fenv env lctx rets sv X joinId rest df
        sv X joinId sa u s' hc2
      exact ⟨hv', Or.inl (hm.forward hv a8
        (gb.trans (gr.mono (Nat.le_trans a8.size gb.size))))⟩
    | some env' =>
      obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
      obtain ⟨ub, sb, hb2, h⟩ := M.bind_inv h
      obtain ⟨uc, sc, hc2, hd2⟩ := M.bind_inv h
      have g6sb : SGrowsAt 0 s6 sb := (((SGrowsAt.of_sealCur h7).trans
        (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h8)).trans
          (gbody.mono (Nat.zero_le _))).trans
            ((SGrowsAt.of_edgeArgs ha).trans (SGrowsAt.of_sealCur hb2))
      have hnextLt : nextId < sb.fn.blocks.size :=
        Nat.lt_of_lt_of_le (newBlock_target_lt h6) g6sb.size
      have hvc : CurValid sc := CurValid.of_moveTo hnextLt hc2
      obtain ⟨hv', -⟩ := ih sc hvc hd2
      have hnextBase : s.fn.blocks.size ≤ nextId := by
        rw [SGrowsAt.newBlock_id h6]
        exact a5.size
      have gb : SGrowsAt s.fn.blocks.size s8 sc :=
        (((gbody.mono a8.size).trans (SGrowsAt.of_edgeArgs ha)).trans
          (SGrowsAt.of_sealCur hb2)).trans
            (SGrowsAt.of_moveTo (Or.inl hnextBase) hc2)
      have gr := trCases_grows fenv env lctx rets sv X joinId rest df
        sv X joinId sc u s' hd2
      exact ⟨hv', Or.inl (hm.forward hv a8
        (gb.trans (gr.mono (Nat.le_trans a8.size gb.size))))⟩

omit model in
/-- A non-dependent spelling of the optional default-body list.  Rewriting to
`Option.toList` avoids dependent `match` terms acquiring local proof arguments
when a switch equation is inverted. -/
theorem switchBodies_eq (cases : List (Literal × List (Stmt Op)))
    (dflt : Option (List (Stmt Op))) :
    cases.map Prod.snd ++ (match dflt with | some b => [b] | none => []) =
      cases.map Prod.snd ++ dflt.toList := by
  cases dflt <;> rfl

omit model in
/-- `CurPlaced` travels backwards along an expression-level step. -/
theorem curPlaced_back_grows {f : Func} {sA sB : BState} (hg : Grows sA sB)
    (h : CurPlaced f sB.fn) : CurPlaced f sA.fn := by
  obtain ⟨Δ, hΔ⟩ := hg.cur
  exact h.ofPrefix hg.curId.symm Δ hΔ

omit model in
/-- Backward placement across a statement-list construction.  The `CurFinal`
premise is used precisely when the list diverts after sealing (and therefore
clearing) the same current block; in the fall-through case `curPlaced_back`
and the list's growth witness suffice. -/
theorem trStmts_curPlaced_back {f : Func} {fenv : FMap} {env : VMap}
    {lctx : Option LoopCtx} {rets : Option (List Ident)} {d : Bool}
    {ss : List (Stmt Op)} {s₀ s₁ : BState} {renv : Option VMap}
    {joins : List BlockId} (hvalid : CurValid s₀)
    (hprot : ProtectedAt joins s₀.fn)
    (hcompl : Completes f s₁.fn joins) (hcp : CurPlaced f s₁.fn)
    (hfin : renv = none → CurFinal f s₁.fn)
    (htr : trStmts fenv env lctx rets d ss s₀ = some (renv, s₁)) :
    CurPlaced f s₀.fn := by
  cases d with
  | false =>
    obtain ⟨-, hk⟩ := trStmts_cur fenv env lctx rets false ss s₀ renv s₁
      hvalid htr
    exact curPlaced_back hk hprot.away hcompl hfin hcp
  | true =>
    obtain ⟨hrenv, hfn⟩ := trStmts_true_fn fenv env lctx rets ss
      s₀ s₁ renv htr
    have : renv = none := hrenv
    subst renv
    simpa only [hfn] using hcp

/-- An expression whose evaluation halts: the fragment the construction laid
down reaches that halt from the fragment's entry configuration. -/
def EOutHalt (P : Prog) (f : Func) (s₀ : BState) (R₀ : Regs)
    (yst yst' : EvmState) : Prop :=
  ExecFrom (model := model) P f s₀.fn R₀ yst (.halt yst')

/-- **Every "the right-hand side halted" statement rule at once.** `letHalt`,
`assignHalt`, `exprStmtHalt`, `ifHalt` and `switchHalt` all leave the
environment untouched and report `.halt`; on the SSA side the halt happens
inside the expression's own fragment, which is a prefix of the statement's, so
the statement's `SOut` *is* the expression's. -/
theorem SOut.ofExprHalt {P : Prog} {f : Func} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {s₀ s₁ : BState} {R : Regs}
    {renv : Option VMap} {V : VEnv yulD} {yst yst' : EvmState}
    (h : EOutHalt (model := model) P f s₀ R yst yst') :
    SOut (model := model) P f lctx rets s₀ s₁ R renv V yst yst' .halt := h

omit model in
/-- `trExprN` on a right-hand side that is *not* a user call is `trExpr` plus a
singleton: the arity gate forces `n = 1`. -/
theorem trExprN_nonCall_inv {fenv : FMap} {env : VMap} {n : Nat} {e : Expr Op}
    {s₀ s₁ : BState} {ids : List ValId}
    (hne : ∀ (fn : Ident) (args : List (Expr Op)), e ≠ .call fn args)
    (h : trExprN fenv env n e s₀ = some (ids, s₁)) :
    n = 1 ∧ ∃ i : ValId, ids = [i] ∧ trExpr fenv env e s₀ = some (i, s₁) := by
  cases e with
  | call fn args => exact absurd rfl (hne fn args)
  | lit l =>
    rw [trExprN] at h
    · obtain ⟨hn, h⟩ := M.ite_reject_inv' h
      obtain ⟨i, sX, h1, h2⟩ := M.bind_inv h
      obtain ⟨hids, hsX⟩ := M.pure_inv h2
      exact ⟨hn, i, hids, by rw [← hsX] at h1; exact h1⟩
    · intro fn' args' hc; exact absurd hc (hne fn' args')
  | var x =>
    rw [trExprN] at h
    · obtain ⟨hn, h⟩ := M.ite_reject_inv' h
      obtain ⟨i, sX, h1, h2⟩ := M.bind_inv h
      obtain ⟨hids, hsX⟩ := M.pure_inv h2
      exact ⟨hn, i, hids, by rw [← hsX] at h1; exact h1⟩
    · intro fn' args' hc; exact absurd hc (hne fn' args')
  | builtin op args =>
    rw [trExprN] at h
    · obtain ⟨hn, h⟩ := M.ite_reject_inv' h
      obtain ⟨i, sX, h1, h2⟩ := M.bind_inv h
      obtain ⟨hids, hsX⟩ := M.pure_inv h2
      exact ⟨hn, i, hids, by rw [← hsX] at h1; exact h1⟩
    · intro fn' args' hc; exact absurd hc (hne fn' args')

/-- A one-value expression result read as a one-element argument list. -/
theorem EOut.toEOutL {P : Prog} {f : Func} {s₀ s₁ : BState} {R : Regs}
    {i : ValId} {v : U256} {yst yst' : EvmState}
    (h : EOut (model := model) P f s₀ s₁ R i v yst yst') :
    EOutL (model := model) P f s₀ s₁ R [i] [v] yst yst' := by
  obtain ⟨R₁, hle, hbelow, hfr, hi, hsim⟩ := h
  exact ⟨R₁, hle, hbelow, hfr, by rw [Regs.getMany_cons, hi]; simp, hsim⟩

/-- **`letDecl vars (some e)`** — the right-hand side's ids become the new
bindings; `EnvOK.zip` pairs them with the source values. -/
theorem sim_letDecl_some {P : Prog} {f : Func} {fenv : FMap} {env : VMap}
    {R : Regs} {V : VEnv yulD} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {vars : List Ident} {e : Expr Op}
    {s₀ s₁ sA : BState} {renv : Option VMap} {ids : List ValId}
    {vals : List U256} {yst yst1 : EvmState}
    (henv : EnvOK (model := model) env V R)
    (huniq : env.Unique)
    (hvals : vals.length = vars.length)
    (htrN : trExprN fenv env vars.length e s₀ = some (ids, sA))
    (hE : EOutL (model := model) P f s₀ sA R ids vals yst yst1)
    (htr : trStmt fenv env lctx rets (.letDecl vars (some e)) s₀
        = some (renv, s₁)) :
    SOut (model := model) P f lctx rets s₀ s₁ R renv
      (vars.zip vals ++ V) yst yst1 .normal := by
  rw [trStmt] at htr
  by_cases hgate : (vars.any env.mem || !decide vars.Nodup) = true
  · rw [if_pos hgate] at htr
    obtain ⟨u, sX, h1, -⟩ := M.bind_inv htr
    exact absurd h1 (by simp [reject])
  rw [if_neg hgate] at htr
  obtain ⟨ids', sA', h2, h3⟩ := M.bind_inv htr
  obtain ⟨rfl, rfl⟩ : ids' = ids ∧ sA' = sA := by
    have he := h2.symm.trans htrN
    exact ⟨(M.some_pair_inj he).1, (M.some_pair_inj he).2⟩
  obtain ⟨hrenv, hs₁⟩ := M.pure_inv h3
  subst hs₁
  obtain ⟨R₁, hle, hbelow, hfr, hget, hsim⟩ := hE
  refine ⟨vars.zip ids' ++ env, R₁, hrenv, hle, hbelow, hfr, ?_, ?_, hsim⟩
  · refine EnvOK.append (EnvOK.zip (Regs.getMany_eq_some_iff.mp hget) ?_)
      (henv.mono hle)
    rw [Regs.getMany_length hget]
    exact hvals.symm
  · have ha : vars.any env.mem = false := by
      cases he : vars.any env.mem with
      | false => rfl
      | true => exact False.elim (hgate (by simp [he]))
    have hnd : vars.Nodup := by
      by_contra hn
      exact hgate (by simp [hn])
    refine huniq.zip_append hnd ?_ ?_
    · intro x hx
      exact Bool.eq_false_of_not_eq_true (List.any_eq_false.mp ha x hx)
    · exact ((Regs.getMany_length hget).trans hvals).symm

/-- **`assign vars e`** — the right-hand side's ids replace the bindings in
place; `EnvOK.setMany` tracks `VEnv.setMany`. -/
theorem sim_assign {P : Prog} {f : Func} {fenv : FMap} {env : VMap}
    {R : Regs} {V : VEnv yulD} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {vars : List Ident} {e : Expr Op}
    {s₀ s₁ sA : BState} {renv : Option VMap} {ids : List ValId}
    {vals : List U256} {yst yst1 : EvmState}
    (henv : EnvOK (model := model) env V R)
    (huniq : env.Unique)
    (htrN : trExprN fenv env vars.length e s₀ = some (ids, sA))
    (hE : EOutL (model := model) P f s₀ sA R ids vals yst yst1)
    (htr : trStmt fenv env lctx rets (.assign vars e) s₀ = some (renv, s₁)) :
    SOut (model := model) P f lctx rets s₀ s₁ R renv
      (YulSemantics.VEnv.setMany V vars vals) yst yst1 .normal := by
  rw [trStmt] at htr
  by_cases hgate : (!vars.all env.mem) = true
  · rw [if_pos hgate] at htr
    obtain ⟨u, sX, h1, -⟩ := M.bind_inv htr
    exact absurd h1 (by simp [reject])
  rw [if_neg hgate] at htr
  obtain ⟨ids', sA', h2, h3⟩ := M.bind_inv htr
  obtain ⟨rfl, rfl⟩ : ids' = ids ∧ sA' = sA := by
    have he := h2.symm.trans htrN
    exact ⟨(M.some_pair_inj he).1, (M.some_pair_inj he).2⟩
  obtain ⟨hrenv, hs₁⟩ := M.pure_inv h3
  subst hs₁
  obtain ⟨R₁, hle, hbelow, hfr, hget, hsim⟩ := hE
  exact ⟨env.setMany vars ids', R₁, hrenv, hle, hbelow, hfr,
    EnvOK.setMany (henv.mono hle) (Regs.getMany_eq_some_iff.mp hget),
    huniq.setMany _ _, hsim⟩

/-- **`exprStmt` of an always-halting built-in** — the construction seals the
block with `Term.halt`, and `isHaltingOp_halts` says the source really does
halt there, so no execution is lost. -/
theorem sim_exprStmt_halt {P : Prog} {f : Func} {fenv : FMap} {env : VMap}
    {R : Regs} {V : VEnv yulD} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {op : Op} {args : List (Expr Op)}
    {s₀ s₁ sA : BState} {renv : Option VMap} {ids : List ValId}
    {argvals : List U256} {yst yst1 yst' : EvmState}
    (hop : isHaltingOp op = true)
    (hfin : CurFinal f s₁.fn)
    (htrA : trArgs fenv env args s₀ = some (ids, sA))
    (hA : EOutL (model := model) P f s₀ sA R ids argvals yst yst1)
    (hb : builtinWithExternal model.calls model.creates model.gas op argvals yst1 (.halt yst'))
    (htr : trStmt fenv env lctx rets (.exprStmt (.builtin op args)) s₀
        = some (renv, s₁)) :
    SOut (model := model) P f lctx rets s₀ s₁ R renv V yst yst' .halt := by
  rw [trStmt] at htr
  obtain ⟨ids', sA', h1, htr⟩ := M.bind_inv htr
  obtain ⟨rfl, rfl⟩ : ids' = ids ∧ sA' = sA := by
    have he := h1.symm.trans htrA
    exact ⟨(M.some_pair_inj he).1, (M.some_pair_inj he).2⟩
  rw [if_pos hop] at htr
  obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
  obtain ⟨-, hs₁⟩ := M.pure_inv h3
  rw [hs₁] at hfin
  obtain ⟨R₁, -, -, -, hget, hsim⟩ := hA
  exact hsim (.halt yst')
    (execFrom_halt (curOK_of_sealCur hfin h2) hget hb)

/-- **`exprStmt` of a value-less built-in** — one `op` instruction with no
destinations; the source rule forces the built-in to return no values. -/
theorem sim_exprStmt_op {P : Prog} {f : Func} {fenv : FMap} {env : VMap}
    {R : Regs} {V : VEnv yulD} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {op : Op} {args : List (Expr Op)}
    {s₀ s₁ sA : BState} {renv : Option VMap} {ids : List ValId}
    {argvals : List U256} {yst yst1 yst' : EvmState}
    (hop : ¬ isHaltingOp op = true)
    (henv : EnvOK (model := model) env V R)
    (huniq : env.Unique)
    (htrA : trArgs fenv env args s₀ = some (ids, sA))
    (hA : EOutL (model := model) P f s₀ sA R ids argvals yst yst1)
    (hb : builtinWithExternal model.calls model.creates model.gas op argvals yst1
      (.ok [] yst'))
    (htr : trStmt fenv env lctx rets (.exprStmt (.builtin op args)) s₀
        = some (renv, s₁)) :
    SOut (model := model) P f lctx rets s₀ s₁ R renv V yst yst' .normal := by
  rw [trStmt] at htr
  obtain ⟨ids', sA', h1, htr⟩ := M.bind_inv htr
  obtain ⟨rfl, rfl⟩ : ids' = ids ∧ sA' = sA := by
    have he := h1.symm.trans htrA
    exact ⟨(M.some_pair_inj he).1, (M.some_pair_inj he).2⟩
  rw [if_neg hop] at htr
  obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
  rw [M.emit_apply] at h2
  obtain ⟨-, hsB⟩ := M.some_pair_inj h2
  obtain ⟨hrenv, hs₁⟩ := M.pure_inv h3
  obtain ⟨R₁, hle, hbelow, hfr, hget, hsim⟩ := hA
  subst hsB
  subst hs₁
  refine ⟨env, R₁, hrenv, hle, hbelow, hfr, henv.mono hle, huniq, ?_⟩
  refine hsim.trans ?_
  simpa using simS_op (model := model) (P := P) (f := f) (ds := ([] : List ValId))
    (fn := sA'.fn)
    (fn' := { sA'.fn with cur := Instr.op [] op ids' :: sA'.fn.cur })
    hget hb rfl rfl rfl

/-- **`letDecl vars none`** — the construction emits one zero `const` per
declared name and prepends them to its `VMap`; the source rule prepends
`bindZeros`. -/
theorem sim_letDecl_none {P : Prog} {f : Func} {fenv : FMap} {env : VMap}
    {R : Regs} {V : VEnv yulD} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {vars : List Ident} {s₀ s₁ : BState}
    {renv : Option VMap} {yst : EvmState}
    (hfresh : RegsFresh R s₀.fn) (henv : EnvOK (model := model) env V R)
    (huniq : env.Unique)
    (htr : trStmt fenv env lctx rets (.letDecl vars none) s₀ = some (renv, s₁)) :
    SOut (model := model) P f lctx rets s₀ s₁ R renv
      (YulSemantics.bindZeros yulD vars ++ V) yst yst .normal := by
  rw [trStmt] at htr
  by_cases hgate : (vars.any env.mem || !decide vars.Nodup) = true
  · rw [if_pos hgate] at htr
    obtain ⟨u, sA, h1, -⟩ := M.bind_inv htr
    exact absurd h1 (by simp [reject])
  rw [if_neg hgate] at htr
  obtain ⟨ids, sB, h2, h3⟩ := M.bind_inv htr
  rw [mapM_constZero_spec] at h2
  obtain ⟨hids, hsB⟩ := M.some_pair_inj h2
  subst hids
  subst hsB
  obtain ⟨hrenv, hs₁⟩ := M.pure_inv h3
  subst hs₁
  have hnd : (List.range' s₀.fn.nextVal vars.length).Nodup := M.nodup_range' _ _
  have hlen : (List.range' s₀.fn.nextVal vars.length).length = vars.length := by simp
  have hnone : ∀ i ∈ List.range' s₀.fn.nextVal vars.length, R i = none :=
    fun i hi => hfresh i (M.mem_range'_bounds hi).1
  have hle := Regs.Le.setMany (vs := List.replicate
      (List.range' s₀.fn.nextVal vars.length).length (0 : U256)) hnd hnone
  refine ⟨vars.zip (List.range' s₀.fn.nextVal vars.length) ++ env,
    R.setMany (List.range' s₀.fn.nextVal vars.length)
      (List.replicate (List.range' s₀.fn.nextVal vars.length).length 0),
    hrenv, hle, ?_, ?_, ?_, ?_, ?_⟩
  · exact Regs.BelowEq.setMany fun i hi => (M.mem_range'_bounds hi).1
  · rw [hlen]
    exact hfresh.setMany (Nat.le_refl _)
  · exact EnvOK.append (EnvOK.zip_bindZeros hlen.symm
      (fun i hi => Regs.setMany_replicate_mem hnd i hi)) (henv.mono hle)
  · have ha : vars.any env.mem = false := by
      cases he : vars.any env.mem with
      | false => rfl
      | true => exact False.elim (hgate (by simp [he]))
    have hvnd : vars.Nodup := by
      by_contra hn
      exact hgate (by simp [hn])
    exact huniq.zip_append hvnd
      (fun x hx => Bool.eq_false_of_not_eq_true (List.any_eq_false.mp ha x hx)) hlen.symm
  · exact simS_consts _ R s₀.fn _ rfl rfl

end Semantics
end YulEvmCompiler.SsaCfg
