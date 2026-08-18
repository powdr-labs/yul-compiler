import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.LoopSim
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.OfYulSound.Switch

The switch reconstruction.

`CasesOut`, the dispatch-chain step lemmas, the `trCases_sim` induction over
the case list, and `sim_switchExec`, which assembles them into the single
`switch` step the main induction uses.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics (Ident Literal Expr Stmt VEnv Outcome)
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal evmWithExternal)

section Semantics
variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates YulSemantics.EVM.ExternalGas.any

/-! ### The switch dispatch chain

`trCases` lays down one `const; eq; branch` test per case, each guarding a
block that runs the case body and jumps to the reserved join.  `CasesOut`
is what a whole chain achieves against a source derivation of the *selected*
block, and `trCases_sim` is the induction over the case list that establishes
it. -/

/-- What the switch dispatch chain achieves, by source outcome. -/
def CasesOut (P : Prog) (f : Func) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (X : List Ident) (joinId : BlockId)
    (s₀ s₁ : BState) (R₀ : Regs) (V' : VEnv yulD) (yst yst' : EvmState)
    (o : Outcome) : Prop :=
  match o with
  | .normal => ∃ (R₁ : Regs) (vals : List U256),
      Regs.Le R₀ R₁ ∧ Regs.BelowEq s₀.fn.nextVal R₀ R₁ ∧ RegsFresh R₁ s₁.fn
        ∧ YulSemantics.Forall₂ (fun x v => YulSemantics.VEnv.get V' x = some v) X vals
        ∧ ∀ res, JumpTo (model := model) P f joinId vals R₁ yst' res
            → ExecFrom (model := model) P f s₀.fn R₀ yst res
  | o => SOut (model := model) P f lctx rets s₀ s₁ R₀ none V' yst yst' o

theorem CasesOut.prefix {P : Prog} {f : Func} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {X : List Ident} {joinId : BlockId}
    {s₀ sA s₁ : BState} {R₀ RA : Regs} {V' : VEnv yulD}
    {yst ystA yst' : EvmState} {o : Outcome}
    (hle : Regs.Le R₀ RA)
    (hbelow : Regs.BelowEq s₀.fn.nextVal R₀ RA)
    (hgrow : s₀.fn.nextVal ≤ sA.fn.nextVal)
    (hsim : SimS (model := model) P f s₀.fn R₀ yst sA.fn RA ystA)
    (h : CasesOut (model := model) P f lctx rets X joinId sA s₁ RA V' ystA yst' o) :
    CasesOut (model := model) P f lctx rets X joinId s₀ s₁ R₀ V' yst yst' o := by
  cases o with
  | normal =>
    obtain ⟨R₁, vals, hle1, hbelow1, hfr, hvals, hcont⟩ := h
    exact ⟨R₁, vals, hle.trans hle1, hbelow.trans (hbelow1.mono hgrow), hfr, hvals,
      fun res hj => hsim res (hcont res hj)⟩
  | halt =>
    have h' : SOut (model := model) P f lctx rets sA s₁ RA none V' ystA yst' .halt := h
    show SOut (model := model) P f lctx rets s₀ s₁ R₀ none V' yst yst' .halt
    exact SOut.prefix hle hbelow hgrow hsim h'
  | «break» =>
    have h' : SOut (model := model) P f lctx rets sA s₁ RA none V' ystA yst' .break := h
    show SOut (model := model) P f lctx rets s₀ s₁ R₀ none V' yst yst' .break
    exact SOut.prefix hle hbelow hgrow hsim h'
  | «continue» =>
    have h' : SOut (model := model) P f lctx rets sA s₁ RA none V' ystA yst' .continue := h
    show SOut (model := model) P f lctx rets s₀ s₁ R₀ none V' yst yst' .continue
    exact SOut.prefix hle hbelow hgrow hsim h'
  | leave =>
    have h' : SOut (model := model) P f lctx rets sA s₁ RA none V' ystA yst' .leave := h
    show SOut (model := model) P f lctx rets s₀ s₁ R₀ none V' yst yst' .leave
    exact SOut.prefix hle hbelow hgrow hsim h'

omit model in
/-- A sealed, in-bounds current block that the finished function keeps is
placed. -/
theorem curPlaced_of_curFinal {f : Func} {fn : FnState}
    (hv : fn.curId < fn.blocks.size) (hcur : fn.cur = [])
    (hfin : CurFinal f fn) : CurPlaced f fn := by
  refine ⟨⟨(fn.blocks[fn.curId]).instrs, (fn.blocks[fn.curId]).term⟩,
    fn.blocks[fn.curId], hfin _ (Array.getElem?_eq_getElem hv), ?_, rfl⟩
  rw [hcur]
  simp

theorem CasesOut.ofNonNormal {P : Prog} {f : Func} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {X : List Ident} {joinId : BlockId}
    {s₀ sA s₁ : BState} {R : Regs} {renv : Option VMap} {V' : VEnv yulD}
    {yst yst' : EvmState} {o : Outcome}
    (ho : o ≠ .normal) (hgrow : sA.fn.nextVal ≤ s₁.fn.nextVal)
    (h : SOut (model := model) P f lctx rets s₀ sA R renv V' yst yst' o) :
    CasesOut (model := model) P f lctx rets X joinId s₀ s₁ R V' yst yst' o := by
  cases o with
  | normal => exact absurd rfl ho
  | halt =>
    show SOut (model := model) P f lctx rets s₀ s₁ R none V' yst yst' .halt
    exact SOut.of_nonNormal (by simp) hgrow h
  | «break» =>
    show SOut (model := model) P f lctx rets s₀ s₁ R none V' yst yst' .break
    exact SOut.of_nonNormal (by simp) hgrow h
  | «continue» =>
    show SOut (model := model) P f lctx rets s₀ s₁ R none V' yst yst' .continue
    exact SOut.of_nonNormal (by simp) hgrow h
  | leave =>
    show SOut (model := model) P f lctx rets s₀ s₁ R none V' yst yst' .leave
    exact SOut.of_nonNormal (by simp) hgrow h

omit model in
theorem newBlock_fn {ps : List ValId} {s s' : BState} {bid : BlockId}
    (h : newBlock ps s = some (bid, s')) :
    bid = s.fn.blocks.size ∧ s'.fn.nextVal = s.fn.nextVal ∧ s'.fn.cur = s.fn.cur
      ∧ s'.fn.curId = s.fn.curId := by
  rw [M.newBlock_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact ⟨rfl, rfl, rfl, rfl⟩

omit model in
theorem moveTo_fn {bid : BlockId} {s s' : BState} {u : Unit}
    (h : moveTo bid s = some (u, s')) :
    s'.fn.nextVal = s.fn.nextVal ∧ s'.fn.cur = [] ∧ s'.fn.curId = bid
      ∧ s'.fn.blocks = s.fn.blocks := by
  rw [M.moveTo_apply] at h
  obtain ⟨-, rfl⟩ := M.some_pair_inj h
  exact ⟨rfl, rfl, rfl, rfl⟩

omit model in
theorem freshVal_fn {s s' : BState} {v : ValId} (h : freshVal s = some (v, s')) :
    v = s.fn.nextVal ∧ s'.fn.nextVal = s.fn.nextVal + 1 ∧ s'.fn.cur = s.fn.cur
      ∧ s'.fn.curId = s.fn.curId ∧ s'.fn.blocks = s.fn.blocks := by
  rw [M.freshVal_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

omit model in
theorem emit_fn {i : Instr} {s s' : BState} {u : Unit} (h : emit i s = some (u, s')) :
    s'.fn.nextVal = s.fn.nextVal ∧ s'.fn.cur = i :: s.fn.cur
      ∧ s'.fn.curId = s.fn.curId ∧ s'.fn.blocks = s.fn.blocks := by
  rw [M.emit_apply] at h
  obtain ⟨-, rfl⟩ := M.some_pair_inj h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- One `case` test of the switch dispatch chain: materialise the literal,
compare it with the scrutinee, and land on the `eq` result register. -/
theorem trCases_test_step {P : Prog} {f : Func} {R : Regs} {st : EvmState}
    {sv t e : ValId} {cv w : U256} {s₀ s1 s2 s3 s4 : BState} {u2 u4 : Unit}
    (hfr : RegsFresh R s₀.fn) (hsv : R sv = some cv)
    (h1 : freshVal s₀ = some (t, s1))
    (h2 : emit (Instr.const t w) s1 = some (u2, s2))
    (h3 : freshVal s2 = some (e, s3))
    (h4 : emit (Instr.op [e] .eq [sv, t]) s3 = some (u4, s4)) :
    ∃ R' : Regs, Regs.Le R R' ∧ Regs.BelowEq s₀.fn.nextVal R R'
      ∧ RegsFresh R' s4.fn
      ∧ R' e = some (YulSemantics.EVM.b2w (decide (cv = w)))
      ∧ SimS (model := model) P f s₀.fn R st s4.fn R' st := by
  obtain ⟨htv, hnv1, hcur1, hid1, hbl1⟩ := freshVal_fn h1
  obtain ⟨hnv2, hcur2, hid2, hbl2⟩ := emit_fn h2
  obtain ⟨hev, hnv3, hcur3, hid3, hbl3⟩ := freshVal_fn h3
  obtain ⟨hnv4, hcur4, hid4, hbl4⟩ := emit_fn h4
  subst htv
  -- the literal register
  have hfr1 : RegsFresh (R.set s₀.fn.nextVal w) s2.fn := by
    refine hfr.set w ?_
    rw [hnv2, hnv1]
  have hle1 : Regs.Le R (R.set s₀.fn.nextVal w) :=
    Regs.Le.set _ hfr.unbound
  have hbelow1 : Regs.BelowEq s₀.fn.nextVal R (R.set s₀.fn.nextVal w) :=
    Regs.BelowEq.set _ (Nat.le_refl _)
  have hstep1 : SimS (model := model) P f s₀.fn R st s2.fn
      (R.set s₀.fn.nextVal w) st :=
    simS_const (hid2.trans hid1) (by rw [hcur2, hcur1])
  -- the comparison register
  subst hev
  have hfr2 : RegsFresh ((R.set s₀.fn.nextVal w).set s2.fn.nextVal
      (YulSemantics.EVM.b2w (decide (cv = w)))) s4.fn := by
    refine hfr1.set _ ?_
    rw [hnv4, hnv3]
  have hle2 : Regs.Le (R.set s₀.fn.nextVal w)
      ((R.set s₀.fn.nextVal w).set s2.fn.nextVal
        (YulSemantics.EVM.b2w (decide (cv = w)))) :=
    Regs.Le.set _ hfr1.unbound
  have hbelow2 : Regs.BelowEq s₀.fn.nextVal (R.set s₀.fn.nextVal w)
      ((R.set s₀.fn.nextVal w).set s2.fn.nextVal
        (YulSemantics.EVM.b2w (decide (cv = w)))) := by
    refine Regs.BelowEq.set _ ?_
    rw [hnv2, hnv1]
    omega
  have hargs : (R.set s₀.fn.nextVal w).getMany [sv, s₀.fn.nextVal]
      = some [cv, w] := by
    rw [Regs.getMany_cons, Regs.getMany_cons]
    have hsv' : (R.set s₀.fn.nextVal w) sv = some cv := hle1 sv cv hsv
    rw [hsv', Regs.set_same]
    rfl
  have hstep2 : SimS (model := model) P f s2.fn (R.set s₀.fn.nextVal w) st s4.fn
      ((R.set s₀.fn.nextVal w).setMany [s2.fn.nextVal]
        [YulSemantics.EVM.b2w (decide (cv = w))]) st :=
    simS_op hargs (builtin_eq cv w st) rfl (hid4.trans hid3) (by rw [hcur4, hcur3])
  have hsm : (R.set s₀.fn.nextVal w).setMany [s2.fn.nextVal]
      [YulSemantics.EVM.b2w (decide (cv = w))]
      = (R.set s₀.fn.nextVal w).set s2.fn.nextVal
        (YulSemantics.EVM.b2w (decide (cv = w))) := rfl
  rw [hsm] at hstep2
  exact ⟨_, hle1.trans hle2, hbelow1.trans hbelow2, hfr2, Regs.set_same ..,
    hstep1.trans hstep2⟩

theorem trCases_sim {P : Prog} {f : Func} {funs : YulSemantics.FunEnv yulD}
    {V V' : VEnv yulD} {st1 st2 : EvmState} {cv : U256} {o : Outcome}
    {doneFuncs : Array (Option Func)} {hfuncs : FuncTableComplete P doneFuncs}
    {dflt : Option (List (Stmt Op))} :
    ∀ (cases : List (Literal × List (Stmt Op)))
      (fenv : FMap) (env : VMap) (R : Regs) (lctx : Option LoopCtx)
      (rets : Option (List Ident)) (sv : ValId) (X : List Ident)
      (joinId : BlockId) (s₀ s₁ : BState) (u : Unit) (joins : List BlockId),
      Motive (model := model) P f funs V st1 doneFuncs hfuncs
        (.stmt (.block (YulSemantics.selectSwitch yulD cv cases dflt)))
        (.sres V' st2 o) →
      FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
      env.Unique → CtxVars lctx rets env →
      RegsFresh R s₀.fn → CurValid s₀ → R sv = some cv →
      joinId ∈ joins → ProtectedAt joins s₀.fn →
      Completes f s₁.fn joins → CurFinal f s₁.fn →
      ∀ (done : BState) (owned : List FuncId),
      done.funcs = doneFuncs →
      (∀ i : FuncId, i ∈ owned → i < s₀.funcs.size) →
      FOwned owned s₁ done →
      trCases fenv env lctx rets sv X joinId cases dflt s₀ = some (u, s₁) →
      CasesOut (model := model) P f lctx rets X joinId s₀ s₁ R V' st1 st2 o := by
  intro cases
  induction cases with
  | nil =>
    intro fenv env R lctx rets sv X joinId s₀ s₁ u joins ihs hfe henv huniq hctx
      hfr hvalid _hsv _hjmem hp hcompl hfin done owned hdone hbound hown h
    cases dflt with
    | none =>
      rw [trCases] at h
      obtain ⟨xvals, sA, h1, h2⟩ := M.bind_inv h
      obtain rfl : s₀ = sA := ((M.edgeArgs_inv h1).2).symm
      have aA1 : SGrowsAt s₀.fn.blocks.size s₀ s₁ := SGrowsAt.of_sealCur h2
      have hcompl0 : Completes f s₀.fn joins := SGrowsAt.completes_of aA1 hcompl
      have hseal : CurOK f s₀.fn ⟨[], .jump ⟨joinId, xvals⟩⟩ :=
        curOK_of_sealCur hfin h2
      have hsel0 : YulSemantics.selectSwitch yulD cv
          ([] : List (Literal × List (Stmt Op))) none = [] := rfl
      rw [hsel0] at ihs
      have htrs : trStmt fenv env lctx rets (.block ([] : List (Stmt Op))) s₀
          = some (some env, s₀) := by
        rw [trStmt, trScope]
        simp [allocScope, trStmts]
      have hout := ihs fenv env R lctx rets s₀ s₀ (some env) joins hfe henv huniq
        hctx hfr hvalid hp hcompl0 ⟨_, hseal⟩ (by simp) done owned hdone hbound
        (FOwned.back_fprefix (FPrefix.of_sealCur h2) hbound hown) htrs
      cases o with
      | normal =>
        obtain ⟨env2, R₁, henv2, hle, hbelow, hfr1, henvOK, _huniq2, hsim⟩ := hout
        obtain rfl : env2 = env := (Option.some.inj henv2).symm
        obtain ⟨-, vals, hget, hvals⟩ := edgeArgs_ok henvOK h1
        exact ⟨R₁, vals, hle, hbelow, hfr1.mono aA1.nextVal, hvals,
          fun res hj => hsim res (execFrom_jump hseal hget hj)⟩
      | halt => exact CasesOut.ofNonNormal (by simp) aA1.nextVal hout
      | «break» => exact CasesOut.ofNonNormal (by simp) aA1.nextVal hout
      | «continue» => exact CasesOut.ofNonNormal (by simp) aA1.nextVal hout
      | leave => exact CasesOut.ofNonNormal (by simp) aA1.nextVal hout
    | some dbody =>
      rw [trCases] at h
      obtain ⟨renv, sA, h1, h2⟩ := M.bind_inv h
      have hsel0 : YulSemantics.selectSwitch yulD cv
          ([] : List (Literal × List (Stmt Op))) (some dbody) = dbody := rfl
      rw [hsel0] at ihs
      have h1' : trStmt fenv env lctx rets (.block dbody) s₀ = some (renv, sA) := by
        rw [trStmt]; exact h1
      have hvalidA : CurValid sA := (trStmt_cur hvalid h1').1
      cases renv with
      | none =>
        obtain ⟨-, rfl⟩ := M.pure_inv h2
        have hcurA : s₁.fn.cur = [] :=
          trScope_none_cur_nil fenv env lctx rets dbody s₀ s₁ h1
        have hcpA : CurPlaced f s₁.fn := curPlaced_of_curFinal hvalidA hcurA hfin
        have hout := ihs fenv env R lctx rets s₀ s₁ none joins hfe henv huniq
          hctx hfr hvalid hp hcompl hcpA (fun _ => hfin) done owned hdone hbound hown h1'
        cases o with
        | normal =>
          obtain ⟨env2, R₁, hbad, -⟩ := hout
          exact absurd hbad (by simp)
        | halt => exact CasesOut.ofNonNormal (by simp) (Nat.le_refl _) hout
        | «break» => exact CasesOut.ofNonNormal (by simp) (Nat.le_refl _) hout
        | «continue» => exact CasesOut.ofNonNormal (by simp) (Nat.le_refl _) hout
        | leave => exact CasesOut.ofNonNormal (by simp) (Nat.le_refl _) hout
      | some env' =>
        obtain ⟨xv, sB, h3, h4⟩ := M.bind_inv h2
        obtain rfl : sA = sB := ((M.edgeArgs_inv h3).2).symm
        have aA1 : SGrowsAt sA.fn.blocks.size sA s₁ := SGrowsAt.of_sealCur h4
        have hcomplA : Completes f sA.fn joins := SGrowsAt.completes_of aA1 hcompl
        have hsealA : CurOK f sA.fn ⟨[], .jump ⟨joinId, xv⟩⟩ :=
          curOK_of_sealCur hfin h4
        have hout := ihs fenv env R lctx rets s₀ sA (some env') joins hfe henv
          huniq hctx hfr hvalid hp hcomplA ⟨_, hsealA⟩ (by simp) done owned hdone
          hbound (FOwned.back_fprefix (FPrefix.of_sealCur h4)
            (fun i hi => Nat.lt_of_lt_of_le (hbound i hi)
              (trScope_grows fenv env lctx rets dbody s₀ (some env') sA h1).funcsSize)
            hown) h1'
        cases o with
        | normal =>
          obtain ⟨env2, R₁, henv2, hle, hbelow, hfr1, henvOK, _huniq2, hsim⟩ := hout
          obtain rfl : env2 = env' := (Option.some.inj henv2).symm
          obtain ⟨-, vals, hget, hvals⟩ := edgeArgs_ok henvOK h3
          exact ⟨R₁, vals, hle, hbelow, hfr1.mono aA1.nextVal, hvals,
            fun res hj => hsim res (execFrom_jump hsealA hget hj)⟩
        | halt => exact CasesOut.ofNonNormal (by simp) aA1.nextVal hout
        | «break» => exact CasesOut.ofNonNormal (by simp) aA1.nextVal hout
        | «continue» => exact CasesOut.ofNonNormal (by simp) aA1.nextVal hout
        | leave => exact CasesOut.ofNonNormal (by simp) aA1.nextVal hout
  | cons pcase rest ih =>
    obtain ⟨lit, cbody⟩ := pcase
    intro fenv env R lctx rets sv X joinId s₀ s₁ u joins ihs hfe henv huniq
      hctx hfr hvalid hsv hjmem hp hcompl hfin done owned hdone hbound hown h
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
    -- the dispatch test
    obtain ⟨R4, hle4, hbelow4, hfr4, hE4, hsim4⟩ :=
      trCases_test_step (P := P) (f := f) (st := st1) hfr hsv h1 h2 h3 h4
    -- builder bookkeeping for the two reserved blocks
    obtain ⟨-, -, -, -, hbl1⟩ := freshVal_fn h1
    obtain ⟨-, -, -, hbl2⟩ := emit_fn h2
    obtain ⟨-, -, -, -, hbl3⟩ := freshVal_fn h3
    obtain ⟨-, -, -, hbl4⟩ := emit_fn h4
    obtain ⟨hcase5, -, hcur5, hid5⟩ := newBlock_fn h5
    obtain ⟨hnext6, -, hcur6, hid6⟩ := newBlock_fn h6
    obtain ⟨-, hcur8, hid8, -⟩ := moveTo_fn h8
    have hbl04 : s4.fn.blocks = s₀.fn.blocks := by rw [hbl4, hbl3, hbl2, hbl1]
    have hid04 : s4.fn.curId = s₀.fn.curId := by
      obtain ⟨-, -, -, hi1, -⟩ := freshVal_fn h1
      obtain ⟨-, -, hi2, -⟩ := emit_fn h2
      obtain ⟨-, -, -, hi3, -⟩ := freshVal_fn h3
      obtain ⟨-, -, hi4, -⟩ := emit_fn h4
      rw [hi4, hi3, hi2, hi1]
    have hsz5 : s5.fn.blocks.size = s4.fn.blocks.size + 1 := newBlock_size h5
    have hsz6 : s6.fn.blocks.size = s5.fn.blocks.size + 1 := newBlock_size h6
    have hcaseEq : caseId = s₀.fn.blocks.size := by rw [hcase5, hbl04]
    have hnextEq : nextId = s₀.fn.blocks.size + 1 := by rw [hnext6, hsz5, hbl04]
    have hsz60 : s6.fn.blocks.size = s₀.fn.blocks.size + 2 := by
      rw [hsz6, hsz5, hbl04]
    have hnextLt6 : nextId < s6.fn.blocks.size := by
      rw [hnextEq, hsz60]; exact Nat.lt_succ_self _
    have hcaseLt6 : caseId < s6.fn.blocks.size := by
      rw [hcaseEq, hsz60]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)
    have hcaseNeNext : caseId ≠ nextId := by
      rw [hcaseEq, hnextEq]; exact Nat.ne_of_lt (Nat.lt_succ_self _)
    have a04 : SGrowsAt s₀.fn.blocks.size s₀ s4 :=
      (((SGrowsAt.of_grows (Grows.of_freshVal h1)).trans
        (SGrowsAt.of_grows (Grows.of_emit h2))).trans
        (SGrowsAt.of_grows (Grows.of_freshVal h3))).trans
        (SGrowsAt.of_grows (Grows.of_emit h4))
    have a06 : SGrowsAt s₀.fn.blocks.size s₀ s6 :=
      (a04.trans (SGrowsAt.of_newBlock h5)).trans (SGrowsAt.of_newBlock h6)
    have a08 : SGrowsAt s₀.fn.blocks.size s₀ s8 :=
      (a06.trans (SGrowsAt.of_sealCur h7)).trans
        (SGrowsAt.of_moveTo (N := s₀.fn.blocks.size)
          (Or.inl (Nat.le_of_eq hcaseEq.symm)) h8)
    have hsz68 : s6.fn.blocks.size ≤ s8.fn.blocks.size :=
      ((SGrowsAt.of_sealCur (N := 0) h7).trans
        (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h8)).size
    have hnextLt8 : nextId < s8.fn.blocks.size := Nat.lt_of_lt_of_le hnextLt6 hsz68
    have hcaseLt8 : caseId < s8.fn.blocks.size := Nat.lt_of_lt_of_le hcaseLt6 hsz68
    have hcurId6 : s6.fn.curId = s₀.fn.curId := by rw [hid6, hid5, hid04]
    have hcurId7 : s7.fn.curId = s6.fn.curId := (sealCur_cur h7).choose_spec.1
    have hnextNotIn : nextId ∉ joins := by
      intro hi
      exact Nat.lt_irrefl _ (Nat.lt_of_succ_lt (hnextEq ▸ hp.below nextId hi))
    have hcaseNotIn : caseId ∉ joins := by
      intro hi
      exact Nat.lt_irrefl _ (hcaseEq ▸ hp.below caseId hi)
    have hne7case : s7.fn.curId ≠ caseId := by
      rw [hcurId7, hcurId6, hcaseEq]
      exact Nat.ne_of_lt hvalid
    have hprot7 : s7.fn.curId ∉ joins := by rw [hcurId7, hcurId6]; exact hp.away
    have hold7 : s7.fn.curId < nextId := by
      rw [hcurId7, hcurId6, hnextEq]
      exact Nat.lt_succ_of_lt hvalid
    have hsim46 : SimS (model := model) P f s4.fn R4 st1 s6.fn R4 st1 :=
      simS_id (by rw [hid6, hid5]) (by rw [hcur6, hcur5])
    have gbody : SGrows s8 s9 :=
      trScope_grows fenv env lctx rets cbody s8 renv s9 h9
    have hbound9 : ∀ i : FuncId, i ∈ owned → i < s9.funcs.size := by
      intro i hi
      exact Nat.lt_of_lt_of_le (hbound i hi)
        (Nat.le_trans a08.funcsSize gbody.funcsSize)
    have hnextLe8 : nextId ≤ s8.fn.blocks.size := Nat.le_of_lt hnextLt8
    have hcur9 : s9.fn.curId = caseId ∨ s8.fn.blocks.size ≤ s9.fn.curId := by
      rcases gbody.curId with hq | hq
      · exact Or.inl (by rw [hq, hid8])
      · exact Or.inr hq
    have hne9next : s9.fn.curId ≠ nextId := by
      rcases hcur9 with hq | hq
      · rw [hq]; exact hcaseNeNext
      · exact (Nat.ne_of_lt (Nat.lt_of_lt_of_le hnextLt8 hq)).symm
    have hprot9 : s9.fn.curId ∉ joins := by
      intro hi
      have hlt := hp.below _ hi
      rcases hcur9 with hq | hq
      · exact Nat.lt_irrefl _ (hcaseEq ▸ hq ▸ hlt)
      · exact Nat.lt_irrefl _
          (Nat.lt_of_lt_of_le hlt (Nat.le_trans a08.size hq))
    have h9' : trStmt fenv env lctx rets (.block cbody) s8 = some (renv, s9) := by
      rw [trStmt]; exact h9
    have hvalid8 : CurValid s8 := by
      show s8.fn.curId < s8.fn.blocks.size
      rw [hid8]; exact hcaseLt8
    have hvalid9 : CurValid s9 := (trStmt_cur hvalid8 h9').1
    have hfr8 : RegsFresh R4 s8.fn := hfr4.mono
      (((SGrowsAt.of_newBlock (N := 0) h5).trans
        ((SGrowsAt.of_newBlock (N := 0) h6).trans
          ((SGrowsAt.of_sealCur (N := 0) h7).trans
            (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h8)))).nextVal)
    have hp8 : ProtectedAt (nextId :: joins) s8.fn := by
      refine ⟨?_, ?_⟩
      · intro i hi
        simp only [List.mem_cons] at hi
        rcases hi with rfl | hi
        · exact hnextLt8
        · exact Nat.lt_of_lt_of_le (hp.below i hi) a08.size
      · rw [hid8]
        simp only [List.mem_cons, not_or]
        exact ⟨hcaseNeNext, hcaseNotIn⟩
    have hnv08 : s₀.fn.nextVal ≤ s8.fn.nextVal := a08.nextVal
    by_cases hmatch : cv = YulSemantics.EVM.litValue lit
    · -- the scrutinee selects this case: enter `caseId`
      have hsel0 : YulSemantics.selectSwitch yulD cv ((lit, cbody) :: rest) dflt
          = cbody := by
        simp [YulSemantics.selectSwitch, hmatch]
      rw [hsel0] at ihs
      have hE1 : R4 e = some 1 := by
        rw [hE4]; simp [YulSemantics.EVM.b2w, hmatch]
      have a59 : SGrowsAt 0 s5 s9 :=
        ((SGrowsAt.of_newBlock (N := 0) h6).trans
          ((SGrowsAt.of_sealCur (N := 0) h7).trans
            (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h8))).trans
          (gbody.mono (Nat.zero_le _))
      obtain ⟨bb, hbb, hbp⟩ := a59.params caseId ⟨[], [], .ret []⟩
        (newBlock_target_get h5)
      cases renv with
      | none =>
        obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb, hc⟩ := M.bind_inv h
        have gT1 : SGrows sb s₁ :=
          trCases_grows fenv env lctx rets sv X joinId rest dflt sv X joinId sb u
            s₁ hc
        have aP : SGrowsAt nextId s8 sa :=
          (gbody.mono hnextLe8).trans (SGrowsAt.of_pure ha)
        have aPT : SGrowsAt nextId sa sb :=
          SGrowsAt.of_moveTo (Or.inl (Nat.le_refl _)) hb
        have hnextLtT : nextId < sb.fn.blocks.size :=
          Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hnextLt8 aP.size) aPT.size
        have a81 : SGrowsAt nextId s8 s₁ :=
          (aP.trans aPT).trans (gT1.mono (Nat.le_of_lt hnextLtT))
        have hfin7 : CurFinal f s7.fn :=
          curFinal_of_move_sgrowsAt hold7 h8 hne7case hprot7 a81 hcompl
        have hbranch : CurOK f s6.fn
            ⟨[], .branch e ⟨caseId, []⟩ ⟨nextId, []⟩⟩ :=
          curOK_of_sealCur hfin7 h7
        have hcomplb : Completes f sb.fn joins := SGrowsAt.completes_of gT1 hcompl
        have hcompla : Completes f sa.fn (nextId :: joins) :=
          Completes.of_moveTo_protected (by simp) hb (hcomplb.protect nextId)
        have hcompl9 : Completes f s9.fn (nextId :: joins) :=
          SGrowsAt.completes_of (SGrowsAt.of_pure ha) hcompla
        have hcura : sa.fn.curId = s9.fn.curId := by
          obtain ⟨-, rfl⟩ := M.pure_inv ha; rfl
        have hfina : CurFinal f sa.fn :=
          curFinal_of_move_grows hb (by rw [hcura]; exact hne9next)
            (by rw [hcura]; exact hprot9) gT1 hcompl
        have hfin9 : CurFinal f s9.fn := by
          obtain ⟨-, hq⟩ := M.pure_inv ha; rw [← hq]; exact hfina
        have hcur9nil : s9.fn.cur = [] :=
          trScope_none_cur_nil fenv env lctx rets cbody s8 s9 h9
        have hcp9 : CurPlaced f s9.fn :=
          curPlaced_of_curFinal hvalid9 hcur9nil hfin9
        have hsimTrue : SimS (model := model) P f s6.fn R4 st1 s8.fn R4 st1 :=
          simS_branchTrue_body hcompl9 hbranch hE1 (by decide) hbb hbp hid8 hcur8
        have hsimPre : SimS (model := model) P f s₀.fn R st1 s8.fn R4 st1 :=
          hsim4.trans (hsim46.trans hsimTrue)
        have p9a : FPrefix s9.funcs.size s9 sa := FPrefix.of_pure ha
        have p9b : FPrefix s9.funcs.size sa sb := FPrefix.of_moveTo hb
        have p9rest : FPrefix s9.funcs.size sb s₁ :=
          trCases_fprefix fenv env lctx rets sv X joinId rest dflt
            sv X joinId s9.funcs.size sb u s₁
              ((p9a.trans p9b).size (Nat.le_refl _)) hc
        have hown9 : FOwned owned s9 done :=
          FOwned.back_fprefix ((p9a.trans p9b).trans p9rest) hbound9 hown
        have hout := ihs fenv env R4 lctx rets s8 s9 none (nextId :: joins) hfe
          (henv.mono hle4) huniq hctx hfr8 hvalid8 hp8 hcompl9 hcp9
          (fun _ => hfin9)
          done owned hdone
          (fun i hi => Nat.lt_of_lt_of_le (hbound i hi) a08.funcsSize)
          hown9 h9'
        have a91 : SGrowsAt 0 s9 s₁ :=
          ((SGrowsAt.of_pure (N := 0) ha).trans
            (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) hb)).trans
            (gT1.mono (Nat.zero_le _))
        cases o with
        | normal =>
          obtain ⟨env2, R2, hbad, -⟩ := hout
          exact absurd hbad (by simp)
        | halt =>
          exact CasesOut.ofNonNormal (by simp) a91.nextVal
            (SOut.prefix hle4 hbelow4 hnv08 hsimPre hout)
        | «break» =>
          exact CasesOut.ofNonNormal (by simp) a91.nextVal
            (SOut.prefix hle4 hbelow4 hnv08 hsimPre hout)
        | «continue» =>
          exact CasesOut.ofNonNormal (by simp) a91.nextVal
            (SOut.prefix hle4 hbelow4 hnv08 hsimPre hout)
        | leave =>
          exact CasesOut.ofNonNormal (by simp) a91.nextVal
            (SOut.prefix hle4 hbelow4 hnv08 hsimPre hout)
      | some envB =>
        obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb, h⟩ := M.bind_inv h
        obtain ⟨uc, sc, hc, hd⟩ := M.bind_inv h
        obtain rfl : s9 = sa := ((M.edgeArgs_inv ha).2).symm
        have gT1 : SGrows sc s₁ :=
          trCases_grows fenv env lctx rets sv X joinId rest dflt sv X joinId sc u
            s₁ hd
        have aP : SGrowsAt nextId s8 sb :=
          (gbody.mono hnextLe8).trans (SGrowsAt.of_sealCur hb)
        have aPT : SGrowsAt nextId sb sc :=
          SGrowsAt.of_moveTo (Or.inl (Nat.le_refl _)) hc
        have hnextLtT : nextId < sc.fn.blocks.size :=
          Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hnextLt8 aP.size) aPT.size
        have a81 : SGrowsAt nextId s8 s₁ :=
          (aP.trans aPT).trans (gT1.mono (Nat.le_of_lt hnextLtT))
        have hfin7 : CurFinal f s7.fn :=
          curFinal_of_move_sgrowsAt hold7 h8 hne7case hprot7 a81 hcompl
        have hbranch : CurOK f s6.fn
            ⟨[], .branch e ⟨caseId, []⟩ ⟨nextId, []⟩⟩ :=
          curOK_of_sealCur hfin7 h7
        have hcomplc : Completes f sc.fn joins := SGrowsAt.completes_of gT1 hcompl
        have hcomplb : Completes f sb.fn (nextId :: joins) :=
          Completes.of_moveTo_protected (by simp) hc (hcomplc.protect nextId)
        have hcompl9 : Completes f s9.fn (nextId :: joins) :=
          SGrowsAt.completes_of (SGrowsAt.of_sealCur hb) hcomplb
        have hcurb : sb.fn.curId = s9.fn.curId := (sealCur_cur hb).choose_spec.1
        have hfinb : CurFinal f sb.fn :=
          curFinal_of_move_grows hc (by rw [hcurb]; exact hne9next)
            (by rw [hcurb]; exact hprot9) gT1 hcompl
        have hseal9 : CurOK f s9.fn ⟨[], .jump ⟨joinId, xv⟩⟩ :=
          curOK_of_sealCur hfinb hb
        have hsimTrue : SimS (model := model) P f s6.fn R4 st1 s8.fn R4 st1 :=
          simS_branchTrue_body hcompl9 hbranch hE1 (by decide) hbb hbp hid8 hcur8
        have hsimPre : SimS (model := model) P f s₀.fn R st1 s8.fn R4 st1 :=
          hsim4.trans (hsim46.trans hsimTrue)
        have p9a : FPrefix s9.funcs.size s9 s9 := FPrefix.of_edgeArgs ha
        have p9b : FPrefix s9.funcs.size s9 sb := FPrefix.of_sealCur hb
        have p9c : FPrefix s9.funcs.size sb sc := FPrefix.of_moveTo hc
        have p9rest : FPrefix s9.funcs.size sc s₁ :=
          trCases_fprefix fenv env lctx rets sv X joinId rest dflt
            sv X joinId s9.funcs.size sc u s₁
              (((p9a.trans p9b).trans p9c).size (Nat.le_refl _)) hd
        have hown9 : FOwned owned s9 done := FOwned.back_fprefix
          (((p9a.trans p9b).trans p9c).trans p9rest) hbound9 hown
        have hout := ihs fenv env R4 lctx rets s8 s9 (some envB) (nextId :: joins)
          hfe (henv.mono hle4) huniq hctx hfr8 hvalid8 hp8 hcompl9 ⟨_, hseal9⟩
          (by simp)
          done owned hdone
          (fun i hi => Nat.lt_of_lt_of_le (hbound i hi) a08.funcsSize)
          hown9 h9'
        have a91 : SGrowsAt 0 s9 s₁ :=
          ((SGrowsAt.of_sealCur (N := 0) hb).trans
            (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) hc)).trans
            (gT1.mono (Nat.zero_le _))
        cases o with
        | normal =>
          obtain ⟨envB', RB, henvB', hleB, hbelowB, hfrB, henvOK, -, hsimBody⟩ :=
            hout
          obtain rfl : envB' = envB := (Option.some.inj henvB').symm
          obtain ⟨-, vals, hget, hvals⟩ := edgeArgs_ok henvOK ha
          exact ⟨RB, vals, hle4.trans hleB,
            hbelow4.trans (hbelowB.mono hnv08), hfrB.mono a91.nextVal, hvals,
            fun res hj =>
              hsimPre res (hsimBody res (execFrom_jump hseal9 hget hj))⟩
        | halt =>
          exact CasesOut.ofNonNormal (by simp) a91.nextVal
            (SOut.prefix hle4 hbelow4 hnv08 hsimPre hout)
        | «break» =>
          exact CasesOut.ofNonNormal (by simp) a91.nextVal
            (SOut.prefix hle4 hbelow4 hnv08 hsimPre hout)
        | «continue» =>
          exact CasesOut.ofNonNormal (by simp) a91.nextVal
            (SOut.prefix hle4 hbelow4 hnv08 hsimPre hout)
        | leave =>
          exact CasesOut.ofNonNormal (by simp) a91.nextVal
            (SOut.prefix hle4 hbelow4 hnv08 hsimPre hout)
    · -- the scrutinee skips this case: fall through to `nextId`
      have hsel0 : YulSemantics.selectSwitch yulD cv ((lit, cbody) :: rest) dflt
          = YulSemantics.selectSwitch yulD cv rest dflt := by
        simp [YulSemantics.selectSwitch, hmatch]
      rw [hsel0] at ihs
      have hE0 : R4 e = some 0 := by
        rw [hE4]; simp [YulSemantics.EVM.b2w, hmatch]
      have hkey : ∀ (sP sT : BState) (u' : Unit),
          SGrowsAt nextId s8 sP → moveTo nextId sP = some (u', sT) →
          trCases fenv env lctx rets sv X joinId rest dflt sT = some (u, s₁) →
          CasesOut (model := model) P f lctx rets X joinId s₀ s₁ R V' st1 st2 o := by
        intro sP sT u' aP hmv hT
        obtain ⟨-, hcurT0, hcurT, -⟩ := moveTo_fn hmv
        have gT1 : SGrows sT s₁ :=
          trCases_grows fenv env lctx rets sv X joinId rest dflt sv X joinId sT u
            s₁ hT
        have aPT : SGrowsAt nextId sP sT :=
          SGrowsAt.of_moveTo (Or.inl (Nat.le_refl _)) hmv
        have a6T : SGrowsAt 0 s6 sT :=
          ((SGrowsAt.of_sealCur (N := 0) h7).trans
            (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h8)).trans
            ((aP.mono (Nat.zero_le _)).trans (aPT.mono (Nat.zero_le _)))
        have hnextLtT : nextId < sT.fn.blocks.size :=
          Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hnextLt8 aP.size) aPT.size
        have a81 : SGrowsAt nextId s8 s₁ :=
          (aP.trans aPT).trans (gT1.mono (Nat.le_of_lt hnextLtT))
        have hfin7 : CurFinal f s7.fn :=
          curFinal_of_move_sgrowsAt hold7 h8 hne7case hprot7 a81 hcompl
        have hbranch : CurOK f s6.fn
            ⟨[], .branch e ⟨caseId, []⟩ ⟨nextId, []⟩⟩ :=
          curOK_of_sealCur hfin7 h7
        have hcomplT : Completes f sT.fn joins := SGrowsAt.completes_of gT1 hcompl
        have hpT : ProtectedAt joins sT.fn := by
          refine ⟨fun i hi => ?_, ?_⟩
          · exact Nat.lt_of_lt_of_le (hp.below i hi)
              (Nat.le_trans a06.size a6T.size)
          · rw [hcurT]; exact hnextNotIn
        have hvalidT : CurValid sT := by
          show sT.fn.curId < sT.fn.blocks.size
          rw [hcurT]; exact hnextLtT
        have a4T : SGrowsAt 0 s4 sT :=
          ((SGrowsAt.of_newBlock (N := 0) h5).trans
            (SGrowsAt.of_newBlock (N := 0) h6)).trans a6T
        have hres := ih fenv env R4 lctx rets sv X joinId sT s₁ u joins ihs hfe
          (henv.mono hle4) huniq hctx (hfr4.mono a4T.nextVal) hvalidT
          (hle4 sv cv hsv)
          hjmem hpT hcompl hfin done owned hdone
          (fun i hi => Nat.lt_of_lt_of_le (hbound i hi)
            (Nat.le_trans a04.funcsSize a4T.funcsSize))
          hown hT
        obtain ⟨nb, hnb, hnbp⟩ := a6T.params nextId ⟨[], [], .ret []⟩
          (newBlock_target_get h6)
        have hsimBr : SimS (model := model) P f s6.fn R4 st1 sT.fn
            (R4.setMany nb.params []) st1 :=
          simS_branchFalse_join (vals := []) hcomplT hbranch hE0 hnb hcurT hcurT0
            (by simp) (by rw [hnbp]; simp)
        have hsm : R4.setMany nb.params [] = R4 := by rw [hnbp]; rfl
        rw [hsm] at hsimBr
        exact CasesOut.prefix hle4 hbelow4
          (Nat.le_trans a04.nextVal a4T.nextVal)
          (hsim4.trans (hsim46.trans hsimBr)) hres
      cases renv with
      | none =>
        obtain ⟨ua, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb, hc⟩ := M.bind_inv h
        exact hkey sa sb ub ((gbody.mono hnextLe8).trans (SGrowsAt.of_pure ha))
          hb hc
      | some envB =>
        obtain ⟨xv, sa, ha, h⟩ := M.bind_inv h
        obtain ⟨ub, sb, hb, h⟩ := M.bind_inv h
        obtain ⟨uc, sc, hc, hd⟩ := M.bind_inv h
        exact hkey sb sc uc
          (((gbody.mono hnextLe8).trans (SGrowsAt.of_edgeArgs ha)).trans
            (SGrowsAt.of_sealCur hb)) hc hd

omit model in
/-- The switch analysis scans every case body and the default. -/
theorem modCases_flatMap (cases : List (Literal × List (Stmt Op))) :
    (cases.map Prod.snd).flatMap (modStmts []) = modCases [] cases := by
  induction cases with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨l, b⟩ := p
    rw [List.map_cons, List.flatMap_cons, modCases, ih]

omit model in
theorem mem_switch_flatMap {cases : List (Literal × List (Stmt Op))}
    {dflt : Option (List (Stmt Op))} {x : Ident}
    (hx : x ∈ modStmt ([] : List Ident)
      (.switch (.lit (.number 0)) cases dflt)) :
    x ∈ (cases.map Prod.snd ++ dflt.toList).flatMap (modStmts []) := by
  rw [List.flatMap_append, modCases_flatMap]
  cases dflt with
  | none => simpa [modStmt] using hx
  | some b => simpa [modStmt] using hx

set_option maxHeartbeats 1000000 in
/-- **`switchExec`** — evaluate the scrutinee, run the dispatch chain, and
reconstruct the environment at the reserved join block. -/
theorem sim_switchExec {P : Prog} {f : Func} {funs : YulSemantics.FunEnv yulD}
    {V V' : VEnv yulD} {st st1 st2 : EvmState} {cv : U256} {o : Outcome}
    {c : Expr Op} {cases : List (Literal × List (Stmt Op))}
    {dflt : Option (List (Stmt Op))}
    {doneFuncs : Array (Option Func)} {hfuncs : FuncTableComplete P doneFuncs}
    (hsel : YulSemantics.Step yulD funs V st1
      (.stmt (.block (YulSemantics.selectSwitch yulD cv cases dflt)))
      (.sres V' st2 o))
    (ihc : Motive (model := model) P f funs V st doneFuncs hfuncs
      (.expr c) (.eres (.vals [cv] st1)))
    (ihs : Motive (model := model) P f funs V st1 doneFuncs hfuncs
      (.stmt (.block (YulSemantics.selectSwitch yulD cv cases dflt)))
      (.sres V' st2 o)) :
    Motive (model := model) P f funs V st doneFuncs hfuncs
      (.stmt (.switch c cases dflt)) (.sres V' st2 o) := by
  intro fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq hctx hfr hvalid hp
    hcompl _hcp _hfin done owned hdone hbound hown htr
  let X := modifiedX env (cases.map Prod.snd ++ dflt.toList)
  unfold trStmt at htr
  obtain ⟨sv, sA, h1, htr⟩ := M.bind_inv htr
  obtain ⟨joinParams, sB, h2, htr⟩ := M.bind_inv htr
  obtain ⟨joinId, sC, h3, htr⟩ := M.bind_inv htr
  obtain ⟨uD, sD, h4, htr⟩ := M.bind_inv htr
  obtain ⟨uE, sE, h5, h6⟩ := M.bind_inv htr
  obtain ⟨hrenv, rfl⟩ := M.pure_inv h6
  have hXE := congrArg (modifiedX env) (switchBodies_eq cases dflt)
  have h2X : X.mapM (fun _ => freshVal) sA = some (joinParams, sB) := by
    exact Eq.mp (congrArg
      (fun X' => X'.mapM (fun _ => freshVal) sA = some (joinParams, sB)) hXE) h2
  have h4X : trCases fenv env lctx rets sv X joinId cases dflt sC =
      some (uD, sD) := by
    exact Eq.mp (congrArg (fun X' =>
      trCases fenv env lctx rets sv X' joinId cases dflt sC = some (uD, sD)) hXE) h4
  have hrenvX : renv = some (env.setMany X joinParams) :=
    Eq.mp (congrArg (fun X' => renv = some (env.setMany X' joinParams)) hXE) hrenv
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
    Completes.of_moveTo_protected (by simp) h5 (hcompl.protect joinId)
  have hprotD : sD.fn.curId ∉ joinId :: joins := by
    simp only [List.mem_cons]
    exact fun hq => hq.elim hjoinNeD hpD.away
  have hcurD : sD.fn.cur = [] := trCases_cur_nil fenv env lctx rets sv
    X joinId cases dflt sC sD uD h4X
  have hcpD : CurPlaced f sD.fn := CurPlaced.of_moveTo_empty hvalidD hcurD
    hjoinNeD h5 hprotD (hcompl.protect joinId)
  have hfinD : CurFinal f sD.fn := curFinal_of_move_grows h5 hjoinNeD
    hpD.away (SGrows.rfl' s₁) hcompl
  have hprotC : sC.fn.curId ∉ joinId :: joins := by
    simp only [List.mem_cons]
    exact fun hq => hq.elim hjoinNeC hpC.away
  have hcpC : CurPlaced f sC.fn :=
    curPlaced_back (renv := none) hkCD hprotC hcomplD (fun _ => hfinD) hcpD
  have hcpB : CurPlaced f sB.fn :=
    (CurSame.of_newBlock h3).placed_back hcpC
  have hcpA : CurPlaced f sA.fn :=
    curPlaced_back_grows (Grows.of_mapM_freshVal h2X) hcpB
  have hjoinBase : sA.fn.blocks.size ≤ joinId := by
    rw [SGrowsAt.newBlock_id h3]
    exact aAB.size
  have htail : SGrowsAt sA.fn.blocks.size sA s₁ :=
    aAC.trans ((gCD.mono aAC.size).trans
      (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hjoinBase) h5))
  have hcomplA : Completes f sA.fn joins := htail.completes_of hcompl
  obtain ⟨RA, hleA, hbelowA, hfrA, hcv, hsimC⟩ :=
    ihc.1 fenv env R s₀ sA sv cv joins hfe henv hfr hp hcomplA hcpA rfl h1
  have hfrC : RegsFresh RA sC.fn := hfrA.mono aAC.nextVal
  have hpC' : ProtectedAt (joinId :: joins) sC.fn := by
    refine ⟨?_, hprotC⟩
    intro i hi
    simp only [List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact hjoinLt
    · exact hpC.below i hi
  have hboundD : ∀ i : FuncId, i ∈ owned → i < sD.funcs.size := by
    intro i hi
    exact Nat.lt_of_lt_of_le (hbound i hi)
      (((SGrows.of_grows g0A).trans aAC).trans gCD).funcsSize
  have hownD : FOwned owned sD done :=
    FOwned.back_fprefix (FPrefix.of_moveTo h5) hboundD hown
  have hcasesOut := trCases_sim (model := model) (P := P) (f := f) (funs := funs)
    (V := V) (st1 := st1) (st2 := st2) (cv := cv) (o := o) (V' := V')
    (doneFuncs := doneFuncs) (hfuncs := hfuncs) (dflt := dflt)
    cases fenv env RA lctx rets sv X joinId sC sD uD (joinId :: joins)
    ihs hfe (henv.mono hleA) huniq hctx hfrC hvalidC hcv (by simp) hpC' hcomplD
    hfinD
    done owned hdone
    (fun i hi => Nat.lt_of_lt_of_le (hbound i hi)
      ((SGrows.of_grows g0A).trans aAC).funcsSize)
    hownD h4X
  have hnv0C : s₀.fn.nextVal ≤ sC.fn.nextVal :=
    Nat.le_trans g0A.nextVal aAC.nextVal
  obtain ⟨hparamLen, hparamRange, hsB⟩ := M.mapM_freshVal_length h2X
  obtain ⟨-, -, hcurC, hidC⟩ := newBlock_fn h3
  have hsimAC : SimS (model := model) P f sA.fn RA st1 sC.fn RA st1 :=
    simS_id (by rw [hidC, hsB]) (by rw [hcurC, hsB])
  have hsimPre : SimS (model := model) P f s₀.fn R st sC.fn RA st1 :=
    hsimC.trans hsimAC
  have hnvD1 : sD.fn.nextVal ≤ s₁.fn.nextVal :=
    (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h5).nextVal
  cases o with
  | halt =>
    exact SOut.prefix hleA hbelowA hnv0C hsimPre
      (SOut.of_nonNormal (renv := none) (by simp) hnvD1 hcasesOut)
  | «break» =>
    exact SOut.prefix hleA hbelowA hnv0C hsimPre
      (SOut.of_nonNormal (renv := none) (by simp) hnvD1 hcasesOut)
  | «continue» =>
    exact SOut.prefix hleA hbelowA hnv0C hsimPre
      (SOut.of_nonNormal (renv := none) (by simp) hnvD1 hcasesOut)
  | leave =>
    exact SOut.prefix hleA hbelowA hnv0C hsimPre
      (SOut.of_nonNormal (renv := none) (by simp) hnvD1 hcasesOut)
  | normal =>
    obtain ⟨R₁, vals, hleB, hbelowB, hfrB, hvals, hcont⟩ := hcasesOut
    have hnd : joinParams.Nodup := by
      rw [hparamRange]; exact M.nodup_range' _ _
    have hparamsLt : ∀ i ∈ joinParams, i < sC.fn.nextVal := by
      intro i hi
      rw [hparamRange] at hi
      have hi' := (M.mem_range'_bounds hi).2
      have hiB : i < sB.fn.nextVal := by rw [hsB]; exact hi'
      exact Nat.lt_of_lt_of_le hiB (SGrowsAt.of_newBlock (N := 0) h3).nextVal
    have hparamsGe : ∀ i ∈ joinParams, sA.fn.nextVal ≤ i := by
      intro i hi
      rw [hparamRange] at hi
      exact (M.mem_range'_bounds hi).1
    have hnone : ∀ i ∈ joinParams, R₁ i = none := by
      intro i hi
      rw [hbelowB i (hparamsLt i hi)]
      exact hfrA i (hparamsGe i hi)
    have hleJ : Regs.Le R₁ (R₁.setMany joinParams vals) :=
      Regs.Le.setMany hnd hnone
    have hbelowJ : Regs.BelowEq s₀.fn.nextVal R₁ (R₁.setMany joinParams vals) := by
      apply Regs.BelowEq.setMany
      intro i hi
      exact Nat.le_trans g0A.nextVal (hparamsGe i hi)
    have hfrJ : RegsFresh (R₁.setMany joinParams vals) s₁.fn := by
      intro i hi
      rw [Regs.setMany_other]
      · exact hfrB i (Nat.le_trans
          (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h5).nextVal hi)
      · intro himem
        exact absurd (hparamsLt i himem)
          (Nat.not_lt_of_ge (Nat.le_trans
            (Nat.le_trans (gCD.mono (Nat.zero_le _)).nextVal
              (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h5).nextVal)
            hi))
    have aC1 : SGrowsAt 0 sC s₁ :=
      (gCD.mono (Nat.zero_le _)).trans
        (SGrowsAt.of_moveTo (N := 0) (Or.inl (Nat.zero_le _)) h5)
    obtain ⟨jb, hjb, hjp⟩ := aC1.params joinId ⟨joinParams, [], .ret []⟩
      (newBlock_target_get h3)
    obtain ⟨-, hcur0, hcur, -⟩ := moveTo_fn h5
    have hjbLen : jb.params.length = vals.length := by
      rw [hjp, hparamLen]
      exact hvals.length_eq
    have hsimJoin : SimS (model := model) P f sC.fn RA st1 s₁.fn
        (R₁.setMany joinParams vals) st2 := by
      have hs : SimS (model := model) P f sC.fn RA st1 s₁.fn
          (R₁.setMany jb.params vals) st2 := fun res hex =>
        hcont res (jumpTo_of_completes hcompl hjb hcur hcur0 hjbLen hex)
      simpa only [hjp] using hs
    have hnames : VEnv.names V' = VEnv.names V := by
      have hm := (mod_sim hsel).1
      simpa [declsOfStmt] using hm
    have hmod : ModOut []
        (modStmts [] (YulSemantics.selectSwitch yulD cv cases dflt)) V V' := by
      have hm := (mod_sim hsel).2 [] (localsOK_nil V)
      simpa [modStmt] using hm
    have hVjoin : YulSemantics.VEnv.setMany V X vals = V' :=
      setMany_eq_of_modOut henv huniq hnames hmod hvals
        (fun x hx => modifiedX_mem_names hx)
        (fun x hx hm => mem_modifiedX hx (mem_switch_flatMap
          (mem_modStmt_switch (cv := cv) hm)))
    have hpget : (R₁.setMany joinParams vals).getMany joinParams = some vals :=
      Regs.getMany_setMany_self hnd (by rw [hparamLen]; exact hvals.length_eq)
    have henvJ : EnvOK (model := model) (env.setMany X joinParams) V'
        (R₁.setMany joinParams vals) := by
      have he : EnvOK (model := model) (env.setMany X joinParams)
          (YulSemantics.VEnv.setMany V X vals) (R₁.setMany joinParams vals) :=
        EnvOK.setMany (henv.mono (hleA.trans (hleB.trans hleJ)))
          (Regs.getMany_eq_some_iff.mp hpget)
      rwa [hVjoin] at he
    exact ⟨env.setMany X joinParams, R₁.setMany joinParams vals, hrenvX,
      hleA.trans (hleB.trans hleJ),
      (hbelowA.trans (hbelowB.mono hnv0C)).trans hbelowJ,
      hfrJ, henvJ, huniq.setMany _ _,
      hsimPre.trans hsimJoin⟩

end Semantics
end YulEvmCompiler.SsaCfg
