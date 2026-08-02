import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.Switch
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.OfYulSound.Sim

The simulation theorem, and construction soundness.

`sim` — the one mutual induction over the statement classes that all the
preceding modules feed — plus `trScope_sim_of_fresh` and the top-level
`ofBlock_sound'`.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics (Ident Literal Expr Stmt VEnv Outcome)
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal evmWithExternal)

section Semantics
variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates

set_option maxHeartbeats 1000000 in
/-- **The construction simulation induction.** One `induction … with` over the
source `Step` derivation, with `Motive` above. The completed function table is
an induction-wide parameter, so every recursive IH uses the same final table
and completion proof. -/
theorem sim {P : Prog} {f : Func} {funs : YulSemantics.FunEnv yulD}
    {V : VEnv yulD} {yst : EvmState} {c : YulSemantics.Code Op}
    {res : YulSemantics.Res yulD} {doneFuncs : Array (Option Func)}
    (hfuncs : FuncTableComplete P doneFuncs)
    (h : YulSemantics.Step yulD funs V yst c res) :
    Motive (model := model) P f funs V yst doneFuncs hfuncs c res := by
  induction h generalizing f with
  | @lit funs V st l =>
    refine ⟨?_, ?_, ?_⟩
    · intro fenv env R s₀ s₁ i v _joins _ _ hfr _hp _ _ hvs htr
      obtain rfl : v = YulSemantics.EVM.litValue l := by simpa using hvs.symm
      exact sim_lit hfr htr
    · intro fenv env R s₀ s₁ n ids _joins _ _ hfr _hp _ _ _ htr
      obtain ⟨-, i, rfl, htrE⟩ := trExprN_nonCall_inv (by intro fn args; simp) htr
      exact (sim_lit hfr htrE).toEOutL
    · intro _ fenv env R lctx rets s₀ s₁ renv _joins _ _ _ _ _ _ _ _ _ htr
      rw [trStmt] at htr
      · exact absurd htr (by simp [reject])
      · intro op args h; cases h
      · intro fn args h; cases h
  | @var funs V st x v hget =>
    refine ⟨?_, ?_, ?_⟩
    · intro fenv env R s₀ s₁ i v' _joins _ henv hfr _hp _ _ hvs htr
      obtain rfl : v' = v := by simpa using hvs.symm
      exact sim_var hfr henv hget htr
    · intro fenv env R s₀ s₁ n ids _joins _ henv hfr _hp _ _ _ htr
      obtain ⟨-, i, rfl, htrE⟩ := trExprN_nonCall_inv (by intro fn args; simp) htr
      exact (sim_var hfr henv hget htrE).toEOutL
    · intro _ fenv env R lctx rets s₀ s₁ renv _joins _ _ _ _ _ _ _ _ _ htr
      rw [trStmt] at htr
      · exact absurd htr (by simp [reject])
      · intro op args h; cases h
      · intro fn args h; cases h
  | @builtinOk funs V st op args argvals st1 rets st2 hargs hb iha =>
    have key : ∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState)
        (i : ValId) (v : U256) (joins : List BlockId),
        FEnvOK (model := model) P funs fenv →
        EnvOK (model := model) env V R → RegsFresh R s₀.fn →
        ProtectedAt joins s₀.fn → Completes f s₁.fn joins →
        CurPlaced f s₁.fn → rets = [v] →
        trExpr fenv env (.builtin op args) s₀ = some (i, s₁) →
        EOut (model := model) P f s₀ s₁ R i v st st2 := by
      intro fenv env R s₀ s₁ i v joins hfe henv hfr hp hcompl hcp hvs htr
      rw [trExpr] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      obtain ⟨d, sB, h2, htr⟩ := M.bind_inv htr
      obtain ⟨u, sC, h3, h4⟩ := M.bind_inv htr
      obtain ⟨rfl, rfl⟩ := M.pure_inv h4
      rw [M.freshVal_apply] at h2
      obtain ⟨rfl, rfl⟩ := M.some_pair_inj h2
      rw [M.emit_apply] at h3
      obtain ⟨-, rfl⟩ := M.some_pair_inj h3
      obtain rfl : rets = [v] := hvs
      obtain ⟨R₁, hle, hbelow, hfr₁, hget, hsim⟩ :=
        iha fenv env R s₀ sA as joins hfe henv hfr hp
        (SGrowsAt.completes_of
          (SGrows.of_grows ((Grows.of_freshVal rfl).trans (Grows.of_emit rfl))) hcompl)
        (curPlaced_back_grows ((Grows.of_freshVal rfl).trans (Grows.of_emit rfl)) hcp) h1
      have g0A := trArgs_grows args fenv env s₀ sA as h1
      refine ⟨R₁.set sA.fn.nextVal v, hle.trans (Regs.Le.set _ hfr₁.unbound),
        hbelow.trans ((Regs.BelowEq.set _ (Nat.le_refl _)).mono g0A.nextVal),
        hfr₁.set _ (Nat.le_refl _), Regs.set_same .., hsim.trans ?_⟩
      exact simS_op (P := P) (f := f) (fn := sA.fn)
        (fn' := { { sA.fn with nextVal := sA.fn.nextVal + 1 } with
          cur := Instr.op [sA.fn.nextVal] op as :: sA.fn.cur }) hget hb rfl rfl rfl
    refine ⟨key, ?_, ?_⟩
    · intro fenv env R s₀ s₁ n ids joins hfe henv hfr hp hcompl hcp hlen htr
      obtain ⟨rfl, i, rfl, htrE⟩ := trExprN_nonCall_inv (by intro fn args'; simp) htr
      obtain ⟨v, rfl⟩ : ∃ v, rets = [v] := by
        cases rets with
        | nil => simp at hlen
        | cons v vs =>
          cases vs with
          | nil => exact ⟨v, rfl⟩
          | cons w ws => simp at hlen
      exact (key fenv env R s₀ s₁ i v joins hfe henv hfr hp hcompl hcp rfl htrE).toEOutL
    · intro hrets fenv env R lctx rs s₀ s₁ renv joins hfe henv huniq hfr _ hp hcompl hcp _ htr
      have htr0 := htr
      rw [trStmt] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      by_cases hop : isHaltingOp op = true
      · rw [if_pos hop] at htr
        obtain ⟨st', hbad⟩ := isHaltingOp_halts (model := model) hop hb
        rw [hrets] at hbad
        cases hbad
      · rw [if_neg hop] at htr
        obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
        obtain ⟨-, rfl⟩ := M.pure_inv h3
        have hg : Grows sA s₁ := Grows.of_emit h2
        exact sim_exprStmt_op hop henv huniq h1
          (iha fenv env R s₀ sA as joins hfe henv hfr hp
            (SGrowsAt.completes_of (SGrows.of_grows hg) hcompl)
            (curPlaced_back_grows hg hcp) h1)
          (hrets ▸ hb) htr0
  | @builtinHalt funs V st op args argvals st1 st2 hargs hb iha =>
    have key : ∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState)
        (i : ValId) (joins : List BlockId), FEnvOK (model := model) P funs fenv →
        EnvOK (model := model) env V R → RegsFresh R s₀.fn →
        ProtectedAt joins s₀.fn → Completes f s₁.fn joins → CurPlaced f s₁.fn →
        trExpr fenv env (.builtin op args) s₀ = some (i, s₁) →
        EOutHalt (model := model) P f s₀ R st st2 := by
      intro fenv env R s₀ s₁ i joins hfe henv hfr hp hcompl hcp htr
      rw [trExpr] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      obtain ⟨d, sB, h2, htr⟩ := M.bind_inv htr
      obtain ⟨u, sC, h3, h4⟩ := M.bind_inv htr
      obtain ⟨rfl, rfl⟩ := M.pure_inv h4
      rw [M.freshVal_apply] at h2
      obtain ⟨rfl, rfl⟩ := M.some_pair_inj h2
      rw [M.emit_apply] at h3
      obtain ⟨-, rfl⟩ := M.some_pair_inj h3
      have hg : Grows sA
          { sA with fn := { { sA.fn with nextVal := sA.fn.nextVal + 1 } with
            cur := Instr.op [sA.fn.nextVal] op as :: sA.fn.cur } } :=
        (Grows.of_freshVal rfl).trans (Grows.of_emit rfl)
      obtain ⟨R₁, -, -, -, hget, hsim⟩ :=
        iha fenv env R s₀ sA as joins hfe henv hfr hp
        (SGrowsAt.completes_of (SGrows.of_grows hg) hcompl)
        (curPlaced_back_grows hg hcp) h1
      obtain ⟨rest, hcur⟩ := hcp
      exact hsim (.halt st2) (execFrom_opHalt hcur hget hb)
    refine ⟨key, ?_, ?_⟩
    · intro fenv env R s₀ s₁ n ids joins hfe henv hfr hp hcompl hcp htr
      obtain ⟨-, i, -, htrE⟩ := trExprN_nonCall_inv (by intro fn args'; simp) htr
      exact key fenv env R s₀ s₁ i joins hfe henv hfr hp hcompl hcp htrE
    · intro fenv env R lctx rs s₀ s₁ renv joins hfe henv _huniq hfr _ hp hcompl hcp hfin htr
      have htr0 := htr
      rw [trStmt] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      by_cases hop : isHaltingOp op = true
      · rw [if_pos hop] at htr
        obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
        obtain ⟨hrenv, rfl⟩ := M.pure_inv h3
        have hfinal : CurFinal f s₁.fn := hfin hrenv
        have hcpA : CurPlaced f sA.fn :=
          ⟨⟨[], .halt op as⟩, curOK_of_sealCur hfinal h2⟩
        exact sim_exprStmt_halt hop hfinal h1
          (iha fenv env R s₀ sA as joins hfe henv hfr hp
            (SGrowsAt.completes_of (SGrowsAt.of_sealCur h2) hcompl) hcpA h1)
          hb htr0
      · rw [if_neg hop] at htr
        obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
        have hemit := h2
        rw [M.emit_apply] at h2
        obtain ⟨-, hsB⟩ := M.some_pair_inj h2
        subst hsB
        obtain ⟨hrenv, rfl⟩ := M.pure_inv h3
        subst renv
        have hg := Grows.of_emit hemit
        obtain ⟨R₁, -, -, -, hget, hsim⟩ :=
          iha fenv env R s₀ sA as joins hfe henv hfr hp
            (SGrowsAt.completes_of (SGrows.of_grows hg) hcompl)
            (curPlaced_back_grows hg hcp) h1
        obtain ⟨rest, hcur⟩ := hcp
        exact hsim (.halt st2) (execFrom_opHalt hcur hget hb)
  | @builtinArgsHalt funs V st op args st1 hargs iha =>
    have key : ∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState)
        (i : ValId) (joins : List BlockId), FEnvOK (model := model) P funs fenv →
        EnvOK (model := model) env V R → RegsFresh R s₀.fn →
        ProtectedAt joins s₀.fn → Completes f s₁.fn joins → CurPlaced f s₁.fn →
        trExpr fenv env (.builtin op args) s₀ = some (i, s₁) →
        EOutHalt (model := model) P f s₀ R st st1 := by
      intro fenv env R s₀ s₁ i joins hfe henv hfr hp hcompl hcp htr
      rw [trExpr] at htr
      obtain ⟨as, sA, h1, htr'⟩ := M.bind_inv htr
      obtain ⟨d, sB, h2, htr''⟩ := M.bind_inv htr'
      obtain ⟨u, sC, h3, h4⟩ := M.bind_inv htr''
      obtain ⟨-, rfl⟩ := M.pure_inv h4
      have hg1 : Grows sA s₁ := (Grows.of_freshVal h2).trans (Grows.of_emit h3)
      exact iha fenv env R s₀ sA as joins hfe henv hfr hp
        (SGrowsAt.completes_of (SGrows.of_grows hg1) hcompl)
        (curPlaced_back_grows hg1 hcp) h1
    refine ⟨key, ?_, ?_⟩
    · intro fenv env R s₀ s₁ n ids joins hfe henv hfr hp hcompl hcp htr
      obtain ⟨-, i, -, htrE⟩ := trExprN_nonCall_inv (by intro fn args'; simp) htr
      exact key fenv env R s₀ s₁ i joins hfe henv hfr hp hcompl hcp htrE
    · intro fenv env R lctx rs s₀ s₁ renv joins hfe henv _huniq hfr _ hp hcompl hcp hfin htr
      rw [trStmt] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      by_cases hop : isHaltingOp op = true
      · rw [if_pos hop] at htr
        obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
        obtain ⟨hrenv, rfl⟩ := M.pure_inv h3
        have hfinal : CurFinal f s₁.fn := hfin hrenv
        have hcpA : CurPlaced f sA.fn :=
          ⟨⟨[], .halt op as⟩, curOK_of_sealCur hfinal h2⟩
        exact SOut.ofExprHalt
          (iha fenv env R s₀ sA as joins hfe henv hfr hp
            (SGrowsAt.completes_of (SGrowsAt.of_sealCur h2) hcompl) hcpA h1)
      · rw [if_neg hop] at htr
        obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
        obtain ⟨-, rfl⟩ := M.pure_inv h3
        have hg : Grows sA s₁ := Grows.of_emit h2
        exact SOut.ofExprHalt
          (iha fenv env R s₀ sA as joins hfe henv hfr hp
            (SGrowsAt.completes_of (SGrows.of_grows hg) hcompl)
            (curPlaced_back_grows hg hcp) h1)
  -- **The callee-entry bridge.**  `FMap.get_ok hfe hlk` already hands over
  -- `fenv.get fn = some fid`, `FuncOK P fenv' decl fid` and
  -- `FEnvOK P cenv fenv'`, and `FuncOK` unfolds to
  -- `P.funcs[fid]? = some g`, `trFunc fenv' decl.params decl.rets decl.body sP
  --  = some (g, sQ)` and `FContents sQ ⟨_, P.funcs⟩`.  Inverting that `trFunc`
  -- gives the entry block (`newBlock []`/`moveTo`), the parameter ids
  -- `pids = g.params`, the zero-return `const` prologue (`simS_consts` executes
  -- it, `EnvOK.zip`/`EnvOK.zip_bindZeros` matches it against
  -- `decl.params.zip argvals ++ bindZeros decl.rets`), and the body run
  -- `trStmt fenv' env0 none (some decl.rets) (.block decl.body) sX
  --  = some (renvC, sY)`.  `simS_call`/`execFrom_callHalt` then splice the
  -- callee's `Exec` into the caller's `.call ds fid as`, and the `.leave`/
  -- fall-through return values come from `SOut`'s `leave` clause and from the
  -- `sealCur (.ret vals)` tail exactly as in `ofBlock_sound'`'s `main`.
  -- `FuncOK`'s pending-slot budget and `FuncTableComplete.get_rev` provide the
  -- `FOwned` witness needed by the recursive body simulation.  Splitting the
  -- final return seal reconstructs `Completes`, `CurPlaced`, and `CurFinal` for
  -- the callee in both fall-through and explicit-leave paths.
  | @callOk funs V st fn args argvals st1 decl cenv Vend st2 o
      hargs hlk harity hbody ho iha ihb =>
    have calleeExec : ∀ (fenv : FMap),
        FEnvOK (model := model) P funs fenv →
        ∃ (fid : FuncId) (g : Func) (eb : Block),
          FMap.get fenv fn = some fid ∧ P.funcs[fid]? = some g
          ∧ g.params.length = argvals.length
          ∧ g.blocks[g.entry]? = some eb
          ∧ Exec (model := model) P g (Regs.empty.setMany g.params argvals) st1
              ⟨eb.instrs, eb.term⟩
              (.ret (decl.rets.map fun r =>
                (YulSemantics.VEnv.get Vend r).getD (YulSemantics.Dialect.zero yulD)) st2) := by
      intro fenv hfe
      obtain ⟨fid, fenv', hfid, hok, hfe'⟩ := FMap.get_ok hfe hlk
      obtain ⟨g, sP, sQ, hg, htrF, hbudget, hcontents⟩ := hok
      unfold trFunc at htrF
      obtain ⟨saved, s1, h1, htrF⟩ := M.bind_inv htrF
      obtain ⟨u2, s2, h2, htrF⟩ := M.bind_inv htrF
      obtain ⟨entry, s3, h3, htrF⟩ := M.bind_inv htrF
      obtain ⟨u4, s4, h4, htrF⟩ := M.bind_inv htrF
      obtain ⟨pids, s5, h5, htrF⟩ := M.bind_inv htrF
      obtain ⟨rids, sX, h6, htrF⟩ := M.bind_inv htrF
      by_cases hgate : (!decide (decl.params ++ decl.rets).Nodup) = true
      · rw [if_pos hgate] at htrF
        obtain ⟨u7, s7, h7, -⟩ := M.bind_inv htrF
        exact absurd h7 (by simp [reject])
      rw [if_neg hgate] at htrF
      obtain ⟨u7, s7, h7, htrF⟩ := M.bind_inv htrF
      obtain ⟨renvC, sY, h8, htail⟩ := M.bind_inv htrF
      obtain ⟨hu7, hs7⟩ := M.pure_inv h7
      subst u7
      subst s7
      have htrBody : trStmt fenv'
          (decl.params.zip pids ++ decl.rets.zip rids) none (some decl.rets)
          (.block decl.body) sX = some (renvC, sY) := by
        rw [trStmt]
        exact h8
      have hvalid4 : CurValid s4 :=
        CurValid.of_moveTo (newBlock_target_lt h3) h4
      have hvalidX : CurValid sX :=
        CurValid.of_grows (CurValid.of_grows hvalid4 (Grows.of_mapM_freshVal h5))
          (Grows.of_mapM_constZero h6)
      have hcurX : sX.fn.curId = entry := by
        rw [M.moveTo_apply] at h4
        have hc4 := congrArg (fun z => z.fn.curId) (M.some_pair_inj h4).2
        exact (Grows.of_mapM_constZero h6).curId.symm.trans
          ((Grows.of_mapM_freshVal h5).curId.symm.trans hc4.symm)
      obtain ⟨hlenP, hrangeP, hs5⟩ := M.mapM_freshVal_length h5
      have hcur4 : s4.fn.cur = [] := by
        rw [M.moveTo_apply] at h4
        exact congrArg (fun z => z.fn.cur) (M.some_pair_inj h4).2 |>.symm
      have hcur5 : s5.fn.cur = [] := by rw [hs5]; exact hcur4
      have h6run := h6
      rw [mapM_constZero_spec] at h6
      obtain ⟨hrids, hsX⟩ := M.some_pair_inj h6
      have hlenR : rids.length = decl.rets.length := by rw [← hrids]; simp
      have hnext5 : s5.fn.nextVal = s4.fn.nextVal + decl.params.length := by
        rw [hs5]
      have hndP : pids.Nodup := by rw [hrangeP]; exact M.nodup_range' _ _
      have hndR : rids.Nodup := by rw [← hrids]; exact M.nodup_range' _ _
      let RP := Regs.empty.setMany pids argvals
      let RR := RP.setMany rids (List.replicate rids.length 0)
      have hpget : RP.getMany pids = some argvals :=
        Regs.getMany_setMany_self hndP (hlenP.trans harity.symm)
      have hnoneR : ∀ i ∈ rids, RP i = none := by
        intro i hi
        rw [← hrids] at hi
        dsimp [RP]
        rw [Regs.setMany_other]
        · rfl
        · intro hip
          rw [hrangeP] at hip
          obtain ⟨hipLo, hipHi⟩ := M.mem_range'_bounds hip
          obtain ⟨hiLo, -⟩ := M.mem_range'_bounds hi
          rw [hnext5] at hiLo
          omega
      have hleR : Regs.Le RP RR := Regs.Le.setMany hndR hnoneR
      have henv0 : EnvOK (model := model)
          (decl.params.zip pids ++ decl.rets.zip rids)
          (decl.params.zip argvals ++ YulSemantics.bindZeros yulD decl.rets) RR := by
        exact EnvOK.append
          (EnvOK.zip (Regs.getMany_eq_some_iff.mp
            (Regs.getMany_mono hleR hpget)) hlenP.symm)
          (EnvOK.zip_bindZeros hlenR.symm
            (fun i hi => Regs.setMany_replicate_mem hndR i hi))
      have huniq0 : VMap.Unique
          (decl.params.zip pids ++ decl.rets.zip rids) := by
        rw [VMap.Unique, List.map_append, List.map_fst_zip, List.map_fst_zip]
        · by_contra hn
          apply hgate
          simp [hn]
        · exact hlenR.symm.le
        · exact hlenP.symm.le
      have hctx0 : CtxVars none (some decl.rets)
          (decl.params.zip pids ++ decl.rets.zip rids) := by
        constructor
        · simp
        · intro rs hrs x hx
          obtain rfl := Option.some.inj hrs
          simp only [List.map_append, List.map_fst_zip hlenP.symm.le,
            List.map_fst_zip hlenR.symm.le, List.mem_append]
          exact Or.inr hx
      have hfrP : RegsFresh RP s5.fn := by
        intro i hi
        dsimp [RP]
        rw [Regs.setMany_other]
        · rfl
        · intro hip
          rw [hrangeP] at hip
          rw [hnext5] at hi
          exact Nat.not_lt_of_ge hi (M.mem_range'_bounds hip).2
      have hfrR : RegsFresh RR sX.fn := by
        dsimp [RR]
        rw [← hrids]
        apply hfrP.setMany
        rw [← hsX]
      have hsizePX : sP.funcs.size ≤ sX.funcs.size := by
        have fp5 := FGrows.trans (FGrows.of_getFn h1)
          (FGrows.trans (FGrows.of_setFn h2)
            (FGrows.trans (FGrows.of_newBlock h3)
              (FGrows.trans (FGrows.of_moveTo h4)
                (FGrows.of_grows (Grows.of_mapM_freshVal h5)))))
        exact FGrows.trans fp5
          (FGrows.of_grows (Grows.of_mapM_constZero h6run))
      let done : BState := { fn := {}, funcs := doneFuncs }
      have ownedY (hsq : sQ.funcs = sY.funcs) :
          ∃ owned : List FuncId,
            (∀ i : FuncId, i ∈ owned → i < sX.funcs.size)
            ∧ FOwned owned sY done := by
        let owned := (List.range sY.funcs.size).filter fun i =>
          match sY.funcs[i]? with | some none => true | _ => false
        have hpending : ∀ i : FuncId,
            i ∈ owned ↔ sY.funcs[i]? = some none := by
          intro i
          constructor
          · intro hi
            obtain ⟨-, hp⟩ := List.mem_filter.mp hi
            split at hp <;> simp_all
          · intro hi
            apply List.mem_filter.mpr
            refine ⟨List.mem_range.mpr (lt_size_of_getElem? hi), ?_⟩
            simp [hi]
        have hown : FOwned owned sY done := by
          refine ⟨List.Nodup.filter _ List.nodup_range, hpending, ?_⟩
          intro i g' hi
          change doneFuncs[i]? = some (some g')
          apply hfuncs.get_rev
          apply hcontents i g'
          rw [hsq]
          exact hi
        refine ⟨owned, ?_, hown⟩
        intro i hi
        exact Nat.lt_of_lt_of_le (hbudget i (by rw [hsq]; exact (hpending i).mp hi))
          hsizePX
      have retvals_eq : ∀ {rs : List Ident} {vals : List U256},
          List.Forall₂ (fun x v =>
            YulSemantics.VEnv.get Vend x = some v) rs vals →
          vals = rs.map (fun r => (YulSemantics.VEnv.get Vend r).getD
            (YulSemantics.Dialect.zero yulD)) := by
        intro rs vals hv
        induction hv with
        | nil => rfl
        | cons hh _ ih => simp only [List.map_cons, hh, Option.getD_some, ih]
      have hsimConst : SimS (model := model) P g s5.fn RP st1 sX.fn RR st1 := by
        dsimp [RR]
        apply simS_consts rids RP s5.fn sX.fn
        · exact (Grows.of_mapM_constZero h6run).curId.symm
        · rw [← hsX, hcur5, ← hrids]
      have entry_of {res : FRes}
          (hex : ExecFrom (model := model) P g s5.fn RP st1 res) :
          ∃ eb : Block, g.blocks[entry]? = some eb
            ∧ Exec (model := model) P g RP st1 ⟨eb.instrs, eb.term⟩ res := by
        obtain ⟨rest, hc, he⟩ := hex
        obtain ⟨eb, heb, hi, ht⟩ := hc
        have hentry5 : s5.fn.curId = entry := by
          rw [hs5]
          rw [M.moveTo_apply] at h4
          exact congrArg (fun z => z.fn.curId) (M.some_pair_inj h4).2 |>.symm
        rw [hentry5] at heb
        rw [hcur5] at hi
        have hi' : eb.instrs = rest.instrs := by simpa using hi
        refine ⟨eb, heb, ?_⟩
        simpa only [hi', ht] using he
      have hvalidY : CurValid sY := (trStmt_cur hvalidX htrBody).1
      have finish_inv : ∀ (sk : BState),
          ((do
            let doneFn ← getFn
            setFn saved
            (pure (⟨pids, decl.rets.length, entry, doneFn.blocks⟩ : Func) : M Func))
              sk = some (g, sQ)) →
          g.params = pids ∧ g.nrets = decl.rets.length ∧ g.entry = entry
            ∧ g.blocks = sk.fn.blocks ∧ sQ.funcs = sk.funcs := by
        intro sk hf
        obtain ⟨doneFn, sa, ha, hf⟩ := M.bind_inv hf
        rw [M.getFn_apply] at ha
        obtain ⟨rfl, rfl⟩ := M.some_pair_inj ha
        obtain ⟨ub, sb, hb, hc⟩ := M.bind_inv hf
        rw [M.setFn_apply] at hb
        obtain ⟨rfl, rfl⟩ := M.some_pair_inj hb
        obtain ⟨rfl, rfl⟩ := M.pure_inv hc
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      cases renvC with
      | none =>
        obtain ⟨ua, sa, ha, htail⟩ := M.bind_inv htail
        obtain ⟨hua, hsa⟩ := M.pure_inv ha
        subst ua
        subst sa
        obtain ⟨hgparams, hgnrets, hgentry, hgblocks, hsq⟩ := finish_inv sY htail
        have hcomplY : Completes g sY.fn :=
          ⟨fun _ _ _ _ hi => by rwa [hgblocks],
            fun _ b hb => ⟨b, by rwa [hgblocks], rfl⟩, by rw [hgblocks]⟩
        have hfinY : CurFinal g sY.fn :=
          fun _ hb => by rwa [hgblocks]
        have hcpY : CurPlaced g sY.fn :=
          curPlaced_of_curFinal hvalidY
            (trScope_none_cur_nil fenv'
              (decl.params.zip pids ++ decl.rets.zip rids) none
              (some decl.rets) decl.body sX sY h8) hfinY
        obtain ⟨owned, hboundY, hownY⟩ := ownedY hsq
        have hsout := ihb fenv'
          (decl.params.zip pids ++ decl.rets.zip rids) RR none
          (some decl.rets) sX sY none [] hfe' henv0 huniq0 hctx0 hfrR
          hvalidX (ProtectedAt.nil sX.fn) hcomplY hcpY (fun _ => hfinY)
          done owned rfl hboundY hownY htrBody
        rcases ho with ho | ho
        · subst o
          obtain ⟨envEnd, REnd, hbad, -⟩ := hsout
          exact absurd hbad (by simp)
        · subst o
          obtain ⟨rs, vals, hrs, hvals, hex⟩ := hsout
          obtain rfl : rs = decl.rets := Option.some.inj hrs.symm
          rw [retvals_eq hvals] at hex
          obtain ⟨eb, heb, he⟩ := entry_of (hsimConst _ hex)
          exact ⟨fid, g, eb, hfid, hg, by rw [hgparams]; omega,
            by rw [hgentry]; exact heb, by simpa [RP, hgparams] using he⟩
      | some envEnd =>
        obtain ⟨vals, sa, hedge, htail⟩ := M.bind_inv htail
        obtain ⟨hedgeMap, hsa⟩ := M.edgeArgs_inv hedge
        subst sa
        obtain ⟨ub, sb, hseal, htail⟩ := M.bind_inv htail
        obtain ⟨hgparams, hgnrets, hgentry, hgblocks, hsqb⟩ := finish_inv sb htail
        obtain ⟨b, hb, hblocks⟩ := M.sealCur_inv hseal
        have hsq : sQ.funcs = sY.funcs := by rw [hsqb, hblocks]
        have hcomplY : Completes g sY.fn := by
          refine ⟨fun i b' _ hne hi => ?_, fun i b' hi => ?_, ?_⟩
          · rw [hgblocks, hblocks, Array.set!_eq_setIfInBounds,
              Array.getElem?_setIfInBounds_ne (Ne.symm hne)]
            exact hi
          · by_cases hc : i = sY.fn.curId
            · subst i
              obtain rfl : b' = b := Option.some.inj (hi.symm.trans hb)
              refine ⟨⟨b'.params, sY.fn.cur.reverse, .ret vals⟩, ?_, rfl⟩
              rw [hgblocks, hblocks, Array.set!_eq_setIfInBounds,
                Array.getElem?_setIfInBounds_self_of_lt (lt_size_of_getElem? hb)]
            · refine ⟨b', ?_, rfl⟩
              rw [hgblocks, hblocks, Array.set!_eq_setIfInBounds,
                Array.getElem?_setIfInBounds_ne (Ne.intro fun hh => hc hh.symm)]
              exact hi
          · rw [hgblocks, hblocks]
            simp
        have hfinImp : some envEnd = none → CurFinal g sY.fn := by
          simp
        have hcpY : CurPlaced g sY.fn := by
          refine ⟨⟨[], .ret vals⟩, ⟨b.params, sY.fn.cur.reverse, .ret vals⟩, ?_, by simp, rfl⟩
          rw [hgblocks, hblocks, Array.set!_eq_setIfInBounds,
            Array.getElem?_setIfInBounds_self_of_lt (lt_size_of_getElem? hb)]
        obtain ⟨owned, hboundY, hownY⟩ := ownedY hsq
        have hsout := ihb fenv'
          (decl.params.zip pids ++ decl.rets.zip rids) RR none
          (some decl.rets) sX sY (some envEnd) [] hfe' henv0 huniq0 hctx0 hfrR
          hvalidX (ProtectedAt.nil sX.fn) hcomplY hcpY hfinImp
          done owned rfl hboundY hownY htrBody
        rcases ho with ho | ho
        · subst o
          obtain ⟨env', REnd, henvEq, -, -, -, henvEnd, -, hsimBody⟩ := hsout
          obtain rfl : env' = envEnd := (Option.some.inj henvEq).symm
          obtain ⟨_, rvals, hrget, hrvals⟩ := edgeArgs_ok henvEnd hedge
          have hrEq := retvals_eq hrvals
          rw [hrEq] at hrget
          have hcurRet : CurOK g sY.fn ⟨[], .ret vals⟩ := by
            refine ⟨⟨b.params, sY.fn.cur.reverse, .ret vals⟩, ?_, by simp, rfl⟩
            rw [hgblocks, hblocks, Array.set!_eq_setIfInBounds,
              Array.getElem?_setIfInBounds_self_of_lt (lt_size_of_getElem? hb)]
          have hex := (hsimConst.trans hsimBody) _ (execFrom_ret hcurRet hrget)
          obtain ⟨eb, heb, he⟩ := entry_of hex
          exact ⟨fid, g, eb, hfid, hg, by rw [hgparams]; omega,
            by rw [hgentry]; exact heb, by simpa [RP, hgparams] using he⟩
        · subst o
          obtain ⟨rs, rvals, hrs, hrvals, hex⟩ := hsout
          obtain rfl : rs = decl.rets := Option.some.inj hrs.symm
          rw [retvals_eq hrvals] at hex
          obtain ⟨eb, heb, he⟩ := entry_of (hsimConst _ hex)
          exact ⟨fid, g, eb, hfid, hg, by rw [hgparams]; omega,
            by rw [hgentry]; exact heb, by simpa [RP, hgparams] using he⟩
    have key : ∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState)
        (i : ValId) (v : U256) (joins : List BlockId),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        RegsFresh R s₀.fn → ProtectedAt joins s₀.fn →
        Completes f s₁.fn joins → CurPlaced f s₁.fn →
        decl.rets.map (fun r => (YulSemantics.VEnv.get Vend r).getD
          (YulSemantics.Dialect.zero yulD)) = [v] →
        trExpr fenv env (.call fn args) s₀ = some (i, s₁) →
        EOut (model := model) P f s₀ s₁ R i v st st2 := by
      intro fenv env R s₀ s₁ i v joins hfe henv hfr hp hcompl hcp hvals htr
      rw [trExpr] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      obtain ⟨fid, sB, h2, htr⟩ := M.bind_inv htr
      obtain ⟨d, sC, h3, htr⟩ := M.bind_inv htr
      obtain ⟨u, sD, h4, h5⟩ := M.bind_inv htr
      obtain ⟨hi, hsD⟩ := M.pure_inv h5
      subst i
      subst sD
      obtain ⟨hfid, hsB⟩ := M.liftO_inv h2
      subst sB
      have h3run := h3
      rw [M.freshVal_apply] at h3
      obtain ⟨hd, hsC⟩ := M.some_pair_inj h3
      subst d
      subst sC
      have h4run := h4
      rw [M.emit_apply] at h4
      obtain ⟨-, hs₁⟩ := M.some_pair_inj h4
      obtain ⟨fid', g, eb, hgetF, hg, hparams, heb, hcallee⟩ := calleeExec fenv hfe
      obtain rfl : fid' = fid := Option.some.inj (hgetF.symm.trans hfid)
      have hretLen : decl.rets.length = 1 := by
        simpa using congrArg List.length hvals
      have hgrow : Grows sA s₁ :=
        (Grows.of_freshVal h3run).trans (Grows.of_emit h4run)
      obtain ⟨RA, hleA, hbelowA, hfrA, hget, hsimA⟩ :=
        iha fenv env R s₀ sA as joins hfe henv hfr hp
          (SGrowsAt.completes_of (SGrows.of_grows hgrow) hcompl)
          (curPlaced_back_grows hgrow hcp) h1
      have hstep := simS_call (model := model) (P := P) (f := f)
        (fn := sA.fn) (fn' := s₁.fn) (R := RA) (ds := [sA.fn.nextVal])
        (as := as) (fid := fid') hg hget (by omega) heb hcallee
        (by simp [hretLen]) (by rw [← hs₁]) (by rw [← hs₁])
      refine ⟨RA.set sA.fn.nextVal v, hleA.trans (Regs.Le.set _ hfrA.unbound),
        hbelowA.trans ((Regs.BelowEq.set _ (Nat.le_refl _)).mono
          (trArgs_grows args fenv env s₀ sA as h1).nextVal),
        hfrA.set _ (by rw [← hs₁]), Regs.set_same .., ?_⟩
      simpa [Regs.setMany, hvals] using hsimA.trans hstep
    refine ⟨key, ?_, ?_⟩
    · intro fenv env R s₀ s₁ n ids joins hfe henv hfr hp hcompl hcp hlen htr
      rw [trExprN] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      obtain ⟨fid, sB, h2, htr⟩ := M.bind_inv htr
      obtain ⟨ds, sC, h3, htr⟩ := M.bind_inv htr
      obtain ⟨u, sD, h4, h5⟩ := M.bind_inv htr
      obtain ⟨hids, hsD⟩ := M.pure_inv h5
      subst sD
      obtain ⟨hfid, hsB⟩ := M.liftO_inv h2
      subst sB
      obtain ⟨hdsLen, hds, hsC⟩ := M.mapM_freshVal_length h3
      subst sC
      have h4run := h4
      rw [M.emit_apply] at h4
      obtain ⟨-, hs₁⟩ := M.some_pair_inj h4
      obtain ⟨fid', g, eb, hgetF, hg, hparams, heb, hcallee⟩ := calleeExec fenv hfe
      obtain rfl : fid' = fid := Option.some.inj (hgetF.symm.trans hfid)
      have hnd : ds.Nodup := by rw [hds]; exact M.nodup_range' _ _
      have hgrow : Grows sA s₁ :=
        (Grows.of_mapM_freshVal h3).trans (Grows.of_emit h4run)
      obtain ⟨RA, hleA, hbelowA, hfrA, hget, hsimA⟩ :=
        iha fenv env R s₀ sA as joins hfe henv hfr hp
          (SGrowsAt.completes_of (SGrows.of_grows hgrow) hcompl)
          (curPlaced_back_grows hgrow hcp) h1
      have hnoneA : ∀ d ∈ ds, RA d = none := by
        intro d hd
        rw [hds] at hd
        exact hfrA d (M.mem_range'_bounds hd).1
      have hleD : Regs.Le RA (RA.setMany ds
          (decl.rets.map fun r => (YulSemantics.VEnv.get Vend r).getD
            (YulSemantics.Dialect.zero yulD))) := Regs.Le.setMany hnd hnoneA
      have hfrD : RegsFresh (RA.setMany ds
          (decl.rets.map fun r => (YulSemantics.VEnv.get Vend r).getD
            (YulSemantics.Dialect.zero yulD))) s₁.fn := by
        rw [hds]
        apply hfrA.setMany
        rw [← hs₁]
      have hdsRetLen : ds.length = (decl.rets.map fun r =>
          (YulSemantics.VEnv.get Vend r).getD
            (YulSemantics.Dialect.zero yulD)).length := by
        calc
          ds.length = (List.range n).length := hdsLen
          _ = n := by simp
          _ = (decl.rets.map fun r =>
              (YulSemantics.VEnv.get Vend r).getD
                (YulSemantics.Dialect.zero yulD)).length := by simpa using hlen.symm
      have hbelowD : Regs.BelowEq sA.fn.nextVal RA
          (RA.setMany ds (decl.rets.map fun r =>
            (YulSemantics.VEnv.get Vend r).getD
              (YulSemantics.Dialect.zero yulD))) := by
        apply Regs.BelowEq.setMany
        intro d hd
        rw [hds] at hd
        exact (M.mem_range'_bounds hd).1
      have hstep := simS_call (model := model) (P := P) (f := f)
        (fn := sA.fn) (fn' := s₁.fn) (R := RA) (ds := ds)
        (as := as) (fid := fid') hg hget (by omega) heb hcallee
        hdsRetLen (by rw [← hs₁]) (by rw [← hs₁])
      refine ⟨_, hleA.trans hleD,
        hbelowA.trans (hbelowD.mono
          (trArgs_grows args fenv env s₀ sA as h1).nextVal),
        hfrD, ?_, hsimA.trans hstep⟩
      rw [hids]
      exact Regs.getMany_setMany_self hnd hdsRetLen
    · intro hvals fenv env R lctx rs s₀ s₁ renv joins hfe henv huniq hfr _ hp
        hcompl hcp _ htr
      rw [trStmt] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      obtain ⟨fid, sB, h2, htr⟩ := M.bind_inv htr
      obtain ⟨u, sC, h3, h4⟩ := M.bind_inv htr
      obtain ⟨hrenv, hsC⟩ := M.pure_inv h4
      subst renv
      subst sC
      obtain ⟨hfid, hsB⟩ := M.liftO_inv h2
      subst sB
      have h3run := h3
      rw [M.emit_apply] at h3
      obtain ⟨-, hs₁⟩ := M.some_pair_inj h3
      obtain ⟨fid', g, eb, hgetF, hg, hparams, heb, hcallee⟩ := calleeExec fenv hfe
      obtain rfl : fid' = fid := Option.some.inj (hgetF.symm.trans hfid)
      have hretLen : decl.rets.length = 0 := by
        simpa using congrArg List.length hvals
      have hgrow : Grows sA s₁ := Grows.of_emit h3run
      obtain ⟨RA, hleA, hbelowA, hfrA, hget, hsimA⟩ :=
        iha fenv env R s₀ sA as joins hfe henv hfr hp
          (SGrowsAt.completes_of (SGrows.of_grows hgrow) hcompl)
          (curPlaced_back_grows hgrow hcp) h1
      have hstep := simS_call (model := model) (P := P) (f := f)
        (fn := sA.fn) (fn' := s₁.fn) (R := RA) (ds := [])
        (as := as) (fid := fid') hg hget (by omega) heb hcallee
        (by simp [hretLen]) (by rw [← hs₁]) (by rw [← hs₁])
      have hfrEnd : RegsFresh RA s₁.fn := by
        rw [← hs₁]
        exact hfrA
      exact ⟨env, RA, rfl, hleA, hbelowA, hfrEnd, henv.mono hleA, huniq,
        by simpa using hsimA.trans hstep⟩
  | @callHalt funs V st fn args argvals st1 decl cenv Vend st2
      hargs hlk harity hbody iha ihb =>
    have calleeHalt : ∀ (fenv : FMap),
        FEnvOK (model := model) P funs fenv →
        ∃ (fid : FuncId) (g : Func) (eb : Block),
          FMap.get fenv fn = some fid ∧ P.funcs[fid]? = some g
          ∧ g.params.length = argvals.length
          ∧ g.blocks[g.entry]? = some eb
          ∧ Exec (model := model) P g (Regs.empty.setMany g.params argvals) st1
              ⟨eb.instrs, eb.term⟩ (.halt st2) := by
      intro fenv hfe
      obtain ⟨fid, fenv', hfid, hok, hfe'⟩ := FMap.get_ok hfe hlk
      obtain ⟨g, sP, sQ, hg, htrF, hbudget, hcontents⟩ := hok
      unfold trFunc at htrF
      obtain ⟨saved, s1, h1, htrF⟩ := M.bind_inv htrF
      obtain ⟨u2, s2, h2, htrF⟩ := M.bind_inv htrF
      obtain ⟨entry, s3, h3, htrF⟩ := M.bind_inv htrF
      obtain ⟨u4, s4, h4, htrF⟩ := M.bind_inv htrF
      obtain ⟨pids, s5, h5, htrF⟩ := M.bind_inv htrF
      obtain ⟨rids, sX, h6, htrF⟩ := M.bind_inv htrF
      by_cases hgate : (!decide (decl.params ++ decl.rets).Nodup) = true
      · rw [if_pos hgate] at htrF
        obtain ⟨u7, s7, h7, -⟩ := M.bind_inv htrF
        exact absurd h7 (by simp [reject])
      rw [if_neg hgate] at htrF
      obtain ⟨u7, s7, h7, htrF⟩ := M.bind_inv htrF
      obtain ⟨renvC, sY, h8, htail⟩ := M.bind_inv htrF
      obtain ⟨hu7, hs7⟩ := M.pure_inv h7
      subst u7
      subst s7
      have htrBody : trStmt fenv'
          (decl.params.zip pids ++ decl.rets.zip rids) none (some decl.rets)
          (.block decl.body) sX = some (renvC, sY) := by
        rw [trStmt]
        exact h8
      have hvalid4 : CurValid s4 := CurValid.of_moveTo (newBlock_target_lt h3) h4
      have hvalidX : CurValid sX :=
        CurValid.of_grows (CurValid.of_grows hvalid4 (Grows.of_mapM_freshVal h5))
          (Grows.of_mapM_constZero h6)
      obtain ⟨hlenP, hrangeP, hs5⟩ := M.mapM_freshVal_length h5
      have hcur4 : s4.fn.cur = [] := by
        rw [M.moveTo_apply] at h4
        exact congrArg (fun z => z.fn.cur) (M.some_pair_inj h4).2 |>.symm
      have hcur5 : s5.fn.cur = [] := by rw [hs5]; exact hcur4
      have h6run := h6
      rw [mapM_constZero_spec] at h6
      obtain ⟨hrids, hsX⟩ := M.some_pair_inj h6
      have hlenR : rids.length = decl.rets.length := by rw [← hrids]; simp
      have hnext5 : s5.fn.nextVal = s4.fn.nextVal + decl.params.length := by rw [hs5]
      have hndP : pids.Nodup := by rw [hrangeP]; exact M.nodup_range' _ _
      have hndR : rids.Nodup := by rw [← hrids]; exact M.nodup_range' _ _
      let RP := Regs.empty.setMany pids argvals
      let RR := RP.setMany rids (List.replicate rids.length 0)
      have hpget : RP.getMany pids = some argvals :=
        Regs.getMany_setMany_self hndP (hlenP.trans harity.symm)
      have hnoneR : ∀ i ∈ rids, RP i = none := by
        intro i hi
        rw [← hrids] at hi
        dsimp [RP]
        rw [Regs.setMany_other]
        · rfl
        · intro hip
          rw [hrangeP] at hip
          obtain ⟨-, hipHi⟩ := M.mem_range'_bounds hip
          obtain ⟨hiLo, -⟩ := M.mem_range'_bounds hi
          rw [hnext5] at hiLo
          omega
      have hleR : Regs.Le RP RR := Regs.Le.setMany hndR hnoneR
      have henv0 : EnvOK (model := model)
          (decl.params.zip pids ++ decl.rets.zip rids)
          (decl.params.zip argvals ++ YulSemantics.bindZeros yulD decl.rets) RR :=
        EnvOK.append
          (EnvOK.zip (Regs.getMany_eq_some_iff.mp (Regs.getMany_mono hleR hpget))
            hlenP.symm)
          (EnvOK.zip_bindZeros hlenR.symm
            (fun i hi => Regs.setMany_replicate_mem hndR i hi))
      have huniq0 : VMap.Unique
          (decl.params.zip pids ++ decl.rets.zip rids) := by
        rw [VMap.Unique, List.map_append, List.map_fst_zip, List.map_fst_zip]
        · by_contra hn
          apply hgate
          simp [hn]
        · exact hlenR.symm.le
        · exact hlenP.symm.le
      have hctx0 : CtxVars none (some decl.rets)
          (decl.params.zip pids ++ decl.rets.zip rids) := by
        constructor
        · simp
        · intro rs hrs x hx
          obtain rfl := Option.some.inj hrs
          simp only [List.map_append, List.map_fst_zip hlenP.symm.le,
            List.map_fst_zip hlenR.symm.le, List.mem_append]
          exact Or.inr hx
      have hfrP : RegsFresh RP s5.fn := by
        intro i hi
        dsimp [RP]
        rw [Regs.setMany_other]
        · rfl
        · intro hip
          rw [hrangeP] at hip
          rw [hnext5] at hi
          exact Nat.not_lt_of_ge hi (M.mem_range'_bounds hip).2
      have hfrR : RegsFresh RR sX.fn := by
        dsimp [RR]
        rw [← hrids]
        apply hfrP.setMany
        rw [← hsX]
      have hsizePX : sP.funcs.size ≤ sX.funcs.size := by
        have fp5 := FGrows.trans (FGrows.of_getFn h1)
          (FGrows.trans (FGrows.of_setFn h2)
            (FGrows.trans (FGrows.of_newBlock h3)
              (FGrows.trans (FGrows.of_moveTo h4)
                (FGrows.of_grows (Grows.of_mapM_freshVal h5)))))
        exact FGrows.trans fp5 (FGrows.of_grows (Grows.of_mapM_constZero h6run))
      let done : BState := { fn := {}, funcs := doneFuncs }
      have ownedY (hsq : sQ.funcs = sY.funcs) :
          ∃ owned : List FuncId,
            (∀ i : FuncId, i ∈ owned → i < sX.funcs.size) ∧ FOwned owned sY done := by
        let owned := (List.range sY.funcs.size).filter fun i =>
          match sY.funcs[i]? with | some none => true | _ => false
        have hpending : ∀ i : FuncId, i ∈ owned ↔ sY.funcs[i]? = some none := by
          intro i
          constructor
          · intro hi
            obtain ⟨-, hp⟩ := List.mem_filter.mp hi
            split at hp <;> simp_all
          · intro hi
            apply List.mem_filter.mpr
            refine ⟨List.mem_range.mpr (lt_size_of_getElem? hi), ?_⟩
            simp [hi]
        have hown : FOwned owned sY done := by
          refine ⟨List.Nodup.filter _ List.nodup_range, hpending, ?_⟩
          intro i g' hi
          change doneFuncs[i]? = some (some g')
          apply hfuncs.get_rev
          apply hcontents i g'
          rw [hsq]
          exact hi
        refine ⟨owned, ?_, hown⟩
        intro i hi
        exact Nat.lt_of_lt_of_le
          (hbudget i (by rw [hsq]; exact (hpending i).mp hi)) hsizePX
      have hsimConst : SimS (model := model) P g s5.fn RP st1 sX.fn RR st1 := by
        dsimp [RR]
        apply simS_consts rids RP s5.fn sX.fn
        · exact (Grows.of_mapM_constZero h6run).curId.symm
        · rw [← hsX, hcur5, ← hrids]
      have entry_of (hex : ExecFrom (model := model) P g s5.fn RP st1 (.halt st2)) :
          ∃ eb : Block, g.blocks[entry]? = some eb
            ∧ Exec (model := model) P g RP st1 ⟨eb.instrs, eb.term⟩ (.halt st2) := by
        obtain ⟨rest, hc, he⟩ := hex
        obtain ⟨eb, heb, hi, ht⟩ := hc
        have hentry5 : s5.fn.curId = entry := by
          rw [hs5]
          rw [M.moveTo_apply] at h4
          exact congrArg (fun z => z.fn.curId) (M.some_pair_inj h4).2 |>.symm
        rw [hentry5] at heb
        rw [hcur5] at hi
        have hi' : eb.instrs = rest.instrs := by simpa using hi
        exact ⟨eb, heb, by simpa only [hi', ht] using he⟩
      have hvalidY : CurValid sY := (trStmt_cur hvalidX htrBody).1
      have finish_inv : ∀ (sk : BState),
          ((do
            let doneFn ← getFn
            setFn saved
            (pure (⟨pids, decl.rets.length, entry, doneFn.blocks⟩ : Func) : M Func))
              sk = some (g, sQ)) →
          g.params = pids ∧ g.nrets = decl.rets.length ∧ g.entry = entry
            ∧ g.blocks = sk.fn.blocks ∧ sQ.funcs = sk.funcs := by
        intro sk hf
        obtain ⟨doneFn, sa, ha, hf⟩ := M.bind_inv hf
        rw [M.getFn_apply] at ha
        obtain ⟨rfl, rfl⟩ := M.some_pair_inj ha
        obtain ⟨ub, sb, hb, hc⟩ := M.bind_inv hf
        rw [M.setFn_apply] at hb
        obtain ⟨rfl, rfl⟩ := M.some_pair_inj hb
        obtain ⟨rfl, rfl⟩ := M.pure_inv hc
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      cases renvC with
      | none =>
        obtain ⟨ua, sa, ha, hfinish⟩ := M.bind_inv htail
        obtain ⟨hua, hsa⟩ := M.pure_inv ha
        subst ua
        subst sa
        obtain ⟨hgparams, hgnrets, hgentry, hgblocks, hsq⟩ := finish_inv sY hfinish
        have hcomplY : Completes g sY.fn :=
          ⟨fun _ _ _ _ hi => by rwa [hgblocks],
            fun _ b hb => ⟨b, by rwa [hgblocks], rfl⟩, by rw [hgblocks]⟩
        have hfinY : CurFinal g sY.fn := fun _ hb => by rwa [hgblocks]
        have hcpY : CurPlaced g sY.fn := curPlaced_of_curFinal hvalidY
          (trScope_none_cur_nil fenv'
            (decl.params.zip pids ++ decl.rets.zip rids) none (some decl.rets)
            decl.body sX sY h8) hfinY
        obtain ⟨owned, hboundY, hownY⟩ := ownedY hsq
        have hsout := ihb fenv' (decl.params.zip pids ++ decl.rets.zip rids) RR
          none (some decl.rets) sX sY none [] hfe' henv0 huniq0 hctx0 hfrR
          hvalidX (ProtectedAt.nil sX.fn) hcomplY hcpY (fun _ => hfinY)
          done owned rfl hboundY hownY htrBody
        obtain ⟨eb, heb, he⟩ := entry_of (hsimConst _ hsout)
        exact ⟨fid, g, eb, hfid, hg, by rw [hgparams]; omega,
          by rw [hgentry]; exact heb, by simpa [RP, hgparams] using he⟩
      | some envEnd =>
        obtain ⟨vals, sa, hedge, htail⟩ := M.bind_inv htail
        obtain ⟨-, hsa⟩ := M.edgeArgs_inv hedge
        subst sa
        obtain ⟨ub, sb, hseal, hfinish⟩ := M.bind_inv htail
        obtain ⟨hgparams, hgnrets, hgentry, hgblocks, hsqb⟩ := finish_inv sb hfinish
        obtain ⟨b, hb, hblocks⟩ := M.sealCur_inv hseal
        have hsq : sQ.funcs = sY.funcs := by rw [hsqb, hblocks]
        have hcomplY : Completes g sY.fn := by
          refine ⟨fun i b' _ hne hi => ?_, fun i b' hi => ?_, ?_⟩
          · rw [hgblocks, hblocks, Array.set!_eq_setIfInBounds,
              Array.getElem?_setIfInBounds_ne (Ne.symm hne)]
            exact hi
          · by_cases hc : i = sY.fn.curId
            · subst i
              obtain rfl : b' = b := Option.some.inj (hi.symm.trans hb)
              refine ⟨⟨b'.params, sY.fn.cur.reverse, .ret vals⟩, ?_, rfl⟩
              rw [hgblocks, hblocks, Array.set!_eq_setIfInBounds,
                Array.getElem?_setIfInBounds_self_of_lt (lt_size_of_getElem? hb)]
            · refine ⟨b', ?_, rfl⟩
              rw [hgblocks, hblocks, Array.set!_eq_setIfInBounds,
                Array.getElem?_setIfInBounds_ne (Ne.intro fun hh => hc hh.symm)]
              exact hi
          · rw [hgblocks, hblocks]
            simp
        have hcpY : CurPlaced g sY.fn := by
          refine ⟨⟨[], .ret vals⟩, ⟨b.params, sY.fn.cur.reverse, .ret vals⟩,
            ?_, by simp, rfl⟩
          rw [hgblocks, hblocks, Array.set!_eq_setIfInBounds,
            Array.getElem?_setIfInBounds_self_of_lt (lt_size_of_getElem? hb)]
        obtain ⟨owned, hboundY, hownY⟩ := ownedY hsq
        have hsout := ihb fenv' (decl.params.zip pids ++ decl.rets.zip rids) RR
          none (some decl.rets) sX sY (some envEnd) [] hfe' henv0 huniq0 hctx0
          hfrR hvalidX (ProtectedAt.nil sX.fn) hcomplY hcpY (by simp)
          done owned rfl hboundY hownY htrBody
        obtain ⟨eb, heb, he⟩ := entry_of (hsimConst _ hsout)
        exact ⟨fid, g, eb, hfid, hg, by rw [hgparams]; omega,
          by rw [hgentry]; exact heb, by simpa [RP, hgparams] using he⟩
    have haltAfterArgs : ∀ (fenv : FMap) (env : VMap) (R : Regs)
        (s₀ sA s₁ : BState) (as ds : List ValId) (fid : FuncId)
        (joins : List BlockId),
        FEnvOK (model := model) P funs fenv → EnvOK (model := model) env V R →
        RegsFresh R s₀.fn → ProtectedAt joins s₀.fn → Completes f s₁.fn joins →
        CurPlaced f s₁.fn → trArgs fenv env args s₀ = some (as, sA) →
        FMap.get fenv fn = some fid → Grows sA s₁ →
        s₁.fn.curId = sA.fn.curId → s₁.fn.cur = .call ds fid as :: sA.fn.cur →
        EOutHalt (model := model) P f s₀ R st st2 := by
      intro fenv env R s₀ sA s₁ as ds fid joins hfe henv hfr hp hcompl hcp
        htrArgs hfid hpost hcurId hcur
      obtain ⟨fid', g, eb, hgetF, hg, hparams, heb, hcallee⟩ := calleeHalt fenv hfe
      obtain rfl : fid' = fid := Option.some.inj (hgetF.symm.trans hfid)
      obtain ⟨RA, -, -, -, hget, hsimA⟩ :=
        iha fenv env R s₀ sA as joins hfe henv hfr hp
          (SGrowsAt.completes_of (SGrows.of_grows hpost) hcompl)
          (curPlaced_back_grows hpost hcp)
          htrArgs
      obtain ⟨rest, hcurOK⟩ := hcp
      have hcurCall : CurOK f { sA.fn with cur := .call ds fid' as :: sA.fn.cur } rest := by
        obtain ⟨b, hb, hi, ht⟩ := hcurOK
        refine ⟨b, by simpa only [hcurId] using hb, ?_, ht⟩
        simpa only [hcur] using hi
      exact hsimA _ (execFrom_callHalt hcurCall hg hget (by omega) heb hcallee)
    refine ⟨?_, ?_, ?_⟩
    · intro fenv env R s₀ s₁ i joins hfe henv hfr hp hcompl hcp htr
      rw [trExpr] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      obtain ⟨fid, sB, h2, htr⟩ := M.bind_inv htr
      obtain ⟨d, sC, h3, htr⟩ := M.bind_inv htr
      obtain ⟨u, sD, h4, h5⟩ := M.bind_inv htr
      obtain ⟨-, hsD⟩ := M.pure_inv h5
      subst sD
      obtain ⟨hfid, hsB⟩ := M.liftO_inv h2
      subst sB
      have hg := (Grows.of_freshVal h3).trans (Grows.of_emit h4)
      exact haltAfterArgs fenv env R s₀ sA s₁ as [d] fid joins hfe henv hfr hp
        hcompl hcp h1 hfid hg hg.curId.symm (by
          obtain ⟨Δ, hΔ⟩ := hg.cur
          rw [M.freshVal_apply] at h3
          obtain ⟨-, hsC⟩ := M.some_pair_inj h3
          rw [M.emit_apply] at h4
          obtain ⟨-, hs₁⟩ := M.some_pair_inj h4
          rw [← hs₁, ← hsC]
        )
    · intro fenv env R s₀ s₁ n ids joins hfe henv hfr hp hcompl hcp htr
      rw [trExprN] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      obtain ⟨fid, sB, h2, htr⟩ := M.bind_inv htr
      obtain ⟨ds, sC, h3, htr⟩ := M.bind_inv htr
      obtain ⟨u, sD, h4, h5⟩ := M.bind_inv htr
      obtain ⟨-, hsD⟩ := M.pure_inv h5
      subst sD
      obtain ⟨hfid, hsB⟩ := M.liftO_inv h2
      subst sB
      have hg := (Grows.of_mapM_freshVal h3).trans (Grows.of_emit h4)
      exact haltAfterArgs fenv env R s₀ sA s₁ as ds fid joins hfe henv hfr hp
        hcompl hcp h1 hfid hg hg.curId.symm (by
          obtain ⟨-, -, hsC⟩ := M.mapM_freshVal_length h3
          rw [M.emit_apply] at h4
          obtain ⟨-, hs₁⟩ := M.some_pair_inj h4
          rw [← hs₁, hsC]
        )
    · intro fenv env R lctx rs s₀ s₁ renv joins hfe henv _huniq hfr _ hp
        hcompl hcp _ htr
      rw [trStmt] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      obtain ⟨fid, sB, h2, htr⟩ := M.bind_inv htr
      obtain ⟨u, sC, h3, h4⟩ := M.bind_inv htr
      obtain ⟨-, hsC⟩ := M.pure_inv h4
      subst sC
      obtain ⟨hfid, hsB⟩ := M.liftO_inv h2
      subst sB
      have hg := Grows.of_emit h3
      exact SOut.ofExprHalt (haltAfterArgs fenv env R s₀ sA s₁ as [] fid joins
        hfe henv hfr hp hcompl hcp h1 hfid hg hg.curId.symm (by
          rw [M.emit_apply] at h3
          obtain ⟨-, hs₁⟩ := M.some_pair_inj h3
          rw [← hs₁]))
  | @callArgsHalt funs V st fn args st1 hargs iha =>
    have key : ∀ (fenv : FMap) (env : VMap) (R : Regs) (s₀ s₁ : BState)
        (i : ValId) (joins : List BlockId), FEnvOK (model := model) P funs fenv →
        EnvOK (model := model) env V R → RegsFresh R s₀.fn →
        ProtectedAt joins s₀.fn → Completes f s₁.fn joins → CurPlaced f s₁.fn →
        trExpr fenv env (.call fn args) s₀ = some (i, s₁) →
        EOutHalt (model := model) P f s₀ R st st1 := by
      intro fenv env R s₀ s₁ i joins hfe henv hfr hp hcompl hcp htr
      rw [trExpr] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      obtain ⟨fid, sB, h2, htr⟩ := M.bind_inv htr
      obtain ⟨d, sC, h3, htr⟩ := M.bind_inv htr
      obtain ⟨u, sD, h4, h5⟩ := M.bind_inv htr
      obtain ⟨-, rfl⟩ := M.pure_inv h5
      have hg : Grows sA s₁ := (Grows.of_liftO h2).trans
        ((Grows.of_freshVal h3).trans (Grows.of_emit h4))
      exact iha fenv env R s₀ sA as joins hfe henv hfr hp
        (SGrowsAt.completes_of (SGrows.of_grows hg) hcompl)
        (curPlaced_back_grows hg hcp) h1
    refine ⟨key, ?_, ?_⟩
    · intro fenv env R s₀ s₁ n ids joins hfe henv hfr hp hcompl hcp htr
      rw [trExprN] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      obtain ⟨fid, sB, h2, htr⟩ := M.bind_inv htr
      obtain ⟨ds, sC, h3, htr⟩ := M.bind_inv htr
      obtain ⟨u, sD, h4, h5⟩ := M.bind_inv htr
      obtain ⟨-, rfl⟩ := M.pure_inv h5
      have hg : Grows sA s₁ := (Grows.of_liftO h2).trans
        ((Grows.of_mapM_freshVal h3).trans (Grows.of_emit h4))
      exact iha fenv env R s₀ sA as joins hfe henv hfr hp
        (SGrowsAt.completes_of (SGrows.of_grows hg) hcompl)
        (curPlaced_back_grows hg hcp) h1
    · intro fenv env R lctx rs s₀ s₁ renv joins hfe henv _huniq hfr _ hp hcompl hcp _ htr
      rw [trStmt] at htr
      obtain ⟨as, sA, h1, htr⟩ := M.bind_inv htr
      obtain ⟨fid, sB, h2, htr⟩ := M.bind_inv htr
      obtain ⟨u, sC, h3, h4⟩ := M.bind_inv htr
      obtain ⟨-, rfl⟩ := M.pure_inv h4
      have hg : Grows sA s₁ := (Grows.of_liftO h2).trans (Grows.of_emit h3)
      exact SOut.ofExprHalt
        (iha fenv env R s₀ sA as joins hfe henv hfr hp
          (SGrowsAt.completes_of (SGrows.of_grows hg) hcompl)
          (curPlaced_back_grows hg hcp) h1)
  | @argsNil funs V st =>
    intro fenv env R s₀ s₁ ids _joins _ _ hfr _hp _ _ htr
    exact sim_args_nil hfr htr
  | @argsCons funs V st e rest restvals st1 v st2 hrest hhead ihr ihh =>
    intro fenv env R s₀ s₁ ids joins hfe henv hfr hp hcompl hcp htr
    rw [trArgs] at htr
    obtain ⟨restIds, sA, h1, htr'⟩ := M.bind_inv htr
    obtain ⟨i, s₁, h2, h3⟩ := M.bind_inv htr'
    obtain ⟨rfl, rfl⟩ := M.pure_inv h3
    have hgE : Grows sA s₁ := trExpr_grows e fenv env sA s₁ i h2
    have hcomplA : Completes f sA.fn joins :=
      SGrowsAt.completes_of (SGrows.of_grows hgE) hcompl
    have hcpA : CurPlaced f sA.fn := curPlaced_back_grows hgE hcp
    have hpA : ProtectedAt joins sA.fn :=
      ProtectedAt.forward hp (SGrows.of_grows
        (trArgs_grows rest fenv env s₀ sA restIds h1))
    refine sim_args_cons
      (ihr fenv env R s₀ sA restIds joins hfe henv hfr hp hcomplA hcpA h1)
      (trArgs_grows rest fenv env s₀ sA restIds h1).nextVal ?_
    intro R' hle hfrA
    exact (ihh.1 fenv env R' sA s₁ i v joins hfe (henv.mono hle) hfrA hpA
      hcompl hcp rfl h2)
  | @argsRestHalt funs V st e rest st1 hrest ihr =>
    intro fenv env R s₀ s₁ ids joins hfe henv hfr hp hcompl hcp htr
    rw [trArgs] at htr
    obtain ⟨restIds, sA, h1, htr'⟩ := M.bind_inv htr
    obtain ⟨i, s₁, h2, h3⟩ := M.bind_inv htr'
    obtain ⟨rfl, rfl⟩ := M.pure_inv h3
    have hgE : Grows sA s₁ := trExpr_grows e fenv env sA s₁ i h2
    exact ihr fenv env R s₀ sA restIds joins hfe henv hfr hp
      (SGrowsAt.completes_of (SGrows.of_grows hgE) hcompl)
      (curPlaced_back_grows hgE hcp) h1
  | @argsHeadHalt funs V st e rest restvals st1 st2 hrest hhead ihr ihh =>
    intro fenv env R s₀ s₁ ids joins hfe henv hfr hp hcompl hcp htr
    rw [trArgs] at htr
    obtain ⟨restIds, sA, h1, htr'⟩ := M.bind_inv htr
    obtain ⟨i, s₁, h2, h3⟩ := M.bind_inv htr'
    obtain ⟨rfl, rfl⟩ := M.pure_inv h3
    have hgE : Grows sA s₁ := trExpr_grows e fenv env sA s₁ i h2
    have hcomplA : Completes f sA.fn joins :=
      SGrowsAt.completes_of (SGrows.of_grows hgE) hcompl
    have hcpA : CurPlaced f sA.fn := curPlaced_back_grows hgE hcp
    have hpA : ProtectedAt joins sA.fn :=
      ProtectedAt.forward hp (SGrows.of_grows
        (trArgs_grows rest fenv env s₀ sA restIds h1))
    obtain ⟨R₁, hle, _hbelow, hfrA, hget, hsim⟩ :=
      ihr fenv env R s₀ sA restIds joins hfe henv hfr hp hcomplA hcpA h1
    exact hsim (.halt st2)
      (ihh.1 fenv env R₁ sA s₁ i joins hfe (henv.mono hle) hfrA hpA hcompl hcp h2)
  | @funDef funs V st n ps rs b =>
    intro fenv env R lctx rets s₀ s₁ renv _joins _ _ _ hctx _ _ _ _ _ _ _done
      _owned _hdone _hbound _hown htr
    rw [trStmt] at htr
    exact absurd htr (by simp [reject])
  -- **The scope case.**  `trScope` reserves the block's hoisted function slots
  -- (`allocScope`), translates the list against the extended `FMap`, and drops
  -- the scope's own `VMap` entries; the source rule hoists the same
  -- declarations and `restore`s.  `allocScope_motive_inputs` turns the
  -- reservation into the statement-list clause's four initializer premises
  -- (including `FEnvOK P (hoist yulD body :: funs) (scope :: fenv)`), `ns_sim`
  -- turns the construction's shadowing rejection into `NoShadow V Vb`, and
  -- `CtxVars` says the loop/return context is made of *outer* names — the two
  -- facts `SOut.scope` needs to carry a non-local exit's edge values out
  -- through the `restore`.
  | @block funs V yst body Vb stb o hb ihb =>
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq hctx hfr hvalid hp
      hcompl hcp hfin done owned hdone hbound hown htr
    rw [trStmt, trScope] at htr
    obtain ⟨scope, sA, ha, htr⟩ := M.bind_inv htr
    obtain ⟨renvI, sB, htrS, hend⟩ := M.bind_inv htr
    obtain ⟨hfnA, -⟩ := allocScope_funcsOnly ha
    -- the scope's own `VMap` drop, and the `renv` it produces
    have hkey : sB = s₁
        ∧ renv = renvI.map (fun e => e.drop (e.length - env.length)) := by
      cases renvI with
      | none =>
        obtain ⟨hr, hs⟩ := M.pure_inv hend
        exact ⟨hs.symm, by rw [hr]; rfl⟩
      | some e =>
        obtain ⟨hr, hs⟩ := M.pure_inv hend
        exact ⟨hs.symm, by rw [hr]; rfl⟩
    obtain ⟨rfl, hrenv⟩ := hkey
    -- the placement/freshness facts travel across `allocScope` unchanged
    have hfrA : RegsFresh R sA.fn := by rw [hfnA]; exact hfr
    have hvalidA : CurValid sA := by
      show sA.fn.curId < sA.fn.blocks.size
      rw [hfnA]; exact hvalid
    have hpA : ProtectedAt joins sA.fn := by rw [hfnA]; exact hp
    have hfinI : renvI = none → CurFinal f sB.fn := by
      intro hnone
      refine hfin ?_
      rw [hrenv, hnone]; rfl
    -- the hoisted scope, realized in the completed function table
    obtain ⟨hfe', hboundA, hslotsA, hndA, -⟩ :=
      allocScope_motive_inputs hfuncs hfe hdone hbound hown ha htrS
    have hout := ihb (scope :: fenv) env R lctx rets sA sB renvI joins hfe' henv
      huniq hctx hfrA hvalidA hpA hcompl hcp hfinI done owned hdone hboundA
      hslotsA hndA hown htrS
    -- the construction rejects shadowing, so scope exit is transparent
    have hns : NoShadow (model := model) V Vb :=
      noShadow_of_NSOut
        (ns_sim hb (scope :: fenv) env lctx rets sA sB renvI henv.names htrS).1
    have hvars : ∀ lc : LoopCtx, lctx = some lc →
        ∀ x ∈ lc.vars, x ∈ VEnv.names V := by
      intro lc hlc x hx
      rw [← henv.names]
      exact hctx.1 lc hlc x hx
    have hretsV : ∀ rs, rets = some rs → ∀ x ∈ rs, x ∈ VEnv.names V := by
      intro rs hrs x hx
      rw [← henv.names]
      exact hctx.2 rs hrs x hx
    have hscope := SOut.scope (P := P) (f := f) henv.length hns hvars hretsV hout
    rw [hrenv]
    simpa only [SOut, hfnA] using hscope
  | @letZero funs V st vars =>
    intro fenv env R lctx rets s₀ s₁ renv _joins _ henv huniq hctx hfr _ _hp _
      _ _ _done _owned _hdone _hbound _hown htr
    exact sim_letDecl_none hfr henv huniq htr
  | @letVal funs V st vars e vals st1 he hlen ihe =>
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq hctx hfr _ hp
      hcompl hcp _ _done _owned _hdone _hbound _hown htr
    have htr0 := htr
    rw [trStmt] at htr
    by_cases hgate : (vars.any env.mem || !decide vars.Nodup) = true
    · rw [if_pos hgate] at htr
      obtain ⟨u, sX, hx, -⟩ := M.bind_inv htr
      exact absurd hx (by simp [reject])
    rw [if_neg hgate] at htr
    obtain ⟨u, sX, hx, htr'⟩ := M.bind_inv htr
    obtain ⟨-, hsX⟩ := M.pure_inv hx
    rw [hsX] at htr'
    obtain ⟨ids, sA, h1, h2⟩ := M.bind_inv htr'
    obtain ⟨-, rfl⟩ := M.pure_inv h2
    exact sim_letDecl_some henv huniq hlen h1
      (ihe.2.1 fenv env R s₀ s₁ vars.length ids joins hfe henv hfr hp hcompl hcp hlen h1) htr0
  | @letHalt funs V st vars e st1 he ihe =>
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv _huniq hctx hfr _ hp
      hcompl hcp _ _done _owned _hdone _hbound _hown htr
    rw [trStmt] at htr
    by_cases hgate : (vars.any env.mem || !decide vars.Nodup) = true
    · rw [if_pos hgate] at htr
      obtain ⟨u, sX, hx, -⟩ := M.bind_inv htr
      exact absurd hx (by simp [reject])
    rw [if_neg hgate] at htr
    obtain ⟨u, sX, hx, htr'⟩ := M.bind_inv htr
    obtain ⟨-, hsX⟩ := M.pure_inv hx
    rw [hsX] at htr'
    obtain ⟨ids, sA, h1, h2⟩ := M.bind_inv htr'
    obtain ⟨-, rfl⟩ := M.pure_inv h2
    exact SOut.ofExprHalt
      (ihe.2.1 fenv env R s₀ s₁ vars.length ids joins hfe henv hfr hp hcompl hcp h1)
  | @assignVal funs V st vars e vals st1 he hlen ihe =>
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq hctx hfr _ hp
      hcompl hcp _ _done _owned _hdone _hbound _hown htr
    have htr0 := htr
    rw [trStmt] at htr
    by_cases hgate : (!vars.all env.mem) = true
    · rw [if_pos hgate] at htr
      obtain ⟨u, sX, hx, -⟩ := M.bind_inv htr
      exact absurd hx (by simp [reject])
    rw [if_neg hgate] at htr
    obtain ⟨u, sX, hx, htr'⟩ := M.bind_inv htr
    obtain ⟨-, hsX⟩ := M.pure_inv hx
    rw [hsX] at htr'
    obtain ⟨ids, sA, h1, h2⟩ := M.bind_inv htr'
    obtain ⟨-, rfl⟩ := M.pure_inv h2
    exact sim_assign henv huniq h1
      (ihe.2.1 fenv env R s₀ s₁ vars.length ids joins hfe henv hfr hp hcompl hcp hlen h1) htr0
  | @assignHalt funs V st vars e st1 he ihe =>
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv _huniq hctx hfr _ hp
      hcompl hcp _ _done _owned _hdone _hbound _hown htr
    rw [trStmt] at htr
    by_cases hgate : (!vars.all env.mem) = true
    · rw [if_pos hgate] at htr
      obtain ⟨u, sX, hx, -⟩ := M.bind_inv htr
      exact absurd hx (by simp [reject])
    rw [if_neg hgate] at htr
    obtain ⟨u, sX, hx, htr'⟩ := M.bind_inv htr
    obtain ⟨-, hsX⟩ := M.pure_inv hx
    rw [hsX] at htr'
    obtain ⟨ids, sA, h1, h2⟩ := M.bind_inv htr'
    obtain ⟨-, rfl⟩ := M.pure_inv h2
    exact SOut.ofExprHalt
      (ihe.2.1 fenv env R s₀ s₁ vars.length ids joins hfe henv hfr hp hcompl hcp h1)
  | exprStmt he ihe =>
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq hctx hfr hvalid
      hp hcompl hcp hfin _done _owned _hdone _hbound _hown htr
    exact ihe.2.2 rfl fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq
      hfr hvalid hp hcompl hcp hfin htr
  | exprStmtHalt he ihe =>
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq hctx hfr hvalid
      hp hcompl hcp hfin _done _owned _hdone _hbound _hown htr
    exact ihe.2.2 fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq
      hfr hvalid hp hcompl hcp hfin htr
  -- The selected-body path below now threads the reserved join through the
  -- protected `Completes` refinement, including the non-fresh move back to the
  -- join.  Its diverting (`bodyEnv = none`) half is fully discharged.  The
  -- fall-through half reaches the next independent invariant described at its
  -- remaining hole: preservation of pre-body unbound reserved parameter ids.
  | @ifTrue funs V st c body cv st1 V' st2 o hc hnz hbody ihc ihb =>
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
      obtain ⟨ua, sa, ha, htr⟩ := M.bind_inv htr
      obtain ⟨ub, sb, hb, hc'⟩ := M.bind_inv htr
      obtain ⟨-, hsa⟩ := M.pure_inv ha
      subst sa
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
  | @ifFalse funs V st c body cv st1 hc hz ihc =>
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
    have hbodyBase : sA.fn.blocks.size ≤ bodyId := by
      rw [SGrowsAt.newBlock_id h3]
      exact aAB.size
    have hjoinBase : sA.fn.blocks.size ≤ joinId := by
      rw [SGrowsAt.newBlock_id h5]
      exact aAD.size
    have csAE : CurSame sA sE :=
      (((CurSame.of_grows gAB).trans (CurSame.of_newBlock h3)).trans
        (CurSame.of_grows gCD)).trans (CurSame.of_newBlock h5)
    have hbodyNe : sE.fn.curId ≠ bodyId := by
      rw [csAE.1, SGrowsAt.newBlock_id h3]
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hvalidA aAB.size)
    have gbody : SGrows sG sH :=
      trScope_grows fenv env lctx rets body sG bodyEnv sH h8
    have tailData : SGrowsAt sA.fn.blocks.size sG s₁
        ∧ s₁.fn.curId = joinId ∧ s₁.fn.cur = []
        ∧ renv = some (env.setMany (modifiedX env [body]) joinParams) := by
      cases bodyEnv with
      | none =>
        obtain ⟨ua, sa, ha, htr⟩ := M.bind_inv htr
        obtain ⟨ub, sb, hb, hc'⟩ := M.bind_inv htr
        obtain ⟨-, hsa⟩ := M.pure_inv ha
        obtain ⟨hrenv, hs₁⟩ := M.pure_inv hc'
        subst hsa
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
  | @ifHalt funs V st c body st1 hc ihc =>
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
    have g0A : Grows s₀ sA := trExpr_grows c fenv env s₀ sA cv h1
    have hvalidA : CurValid sA := hvalid.of_grows g0A
    have gAB : Grows sA sB := Grows.of_liftO h2
    have gCD : Grows sC sD := Grows.of_mapM_freshVal h4
    have csAE : CurSame sA sE :=
      (((CurSame.of_grows gAB).trans (CurSame.of_newBlock h3)).trans
        (CurSame.of_grows gCD)).trans (CurSame.of_newBlock h5)
    have aAB : SGrowsAt sA.fn.blocks.size sA sB := SGrowsAt.of_grows gAB
    have aAC := SGrowsAt.trans aAB
      (SGrowsAt.of_newBlock (N := sA.fn.blocks.size) h3)
    have aAD := SGrowsAt.trans aAC (SGrowsAt.of_grows (N := sA.fn.blocks.size) gCD)
    have aAE := SGrowsAt.trans aAD
      (SGrowsAt.of_newBlock (N := sA.fn.blocks.size) h5)
    have aAF := SGrowsAt.trans aAE
      (SGrowsAt.of_sealCur (N := sA.fn.blocks.size) h6)
    have hbodyBase : sA.fn.blocks.size ≤ bodyId := by
      rw [SGrowsAt.newBlock_id h3]
      exact aAB.size
    have aAG := SGrowsAt.trans aAF
      (SGrowsAt.of_moveTo (N := sA.fn.blocks.size) (Or.inl hbodyBase) h7)
    have gbody : SGrows sG sH :=
      trScope_grows fenv env lctx rets body sG bodyEnv sH h8
    have hjoinBase : sA.fn.blocks.size ≤ joinId := by
      rw [SGrowsAt.newBlock_id h5]
      exact aAD.size
    have hbodyNe : sE.fn.curId ≠ bodyId := by
      rw [csAE.1, SGrowsAt.newBlock_id h3]
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hvalidA aAB.size)
    have gsuffix : SGrowsAt sA.fn.blocks.size sG s₁ := by
      cases bodyEnv with
      | none =>
        obtain ⟨ua, sa, ha, htr⟩ := M.bind_inv htr
        obtain ⟨ub, sb, hb, hc'⟩ := M.bind_inv htr
        obtain ⟨-, rfl⟩ := M.pure_inv ha
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
  | switchExec hc hsel ihc ihs => exact sim_switchExec hsel ihc ihs
  | @switchHalt funs V st c cases dflt st1 hc ihc =>
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
  | @forLoop funs V st init c post body Vinit stinit Vend stend o
      hinit hloop ihi ihl =>
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
          · exact Forall2.imp_mem hvals (fun x hx v hv => by
              rw [get_restore_of_noShadow hnsEnd]
              · exact hv
              · rw [← henv.names]
                exact hctx.2 rs hrs x hx)
          · simpa only [hfnA] using hex
  | @forInitHalt funs V st init c post body Vinit stinit hinit ihi =>
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
        change ExecFrom (model := model) P f s₀.fn R st (.halt stinit)
        change ExecFrom (model := model) P f sA.fn R st (.halt stinit) at hout
        rwa [hfnA] at hout
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
        have hout := ihi (scope :: fenv) env R lctx rets sA sI (some envI) joins
          hfe' henv huniq hctx hfrA hvalidA hpA hcomplI hcpI
          (fun hbad => nomatch hbad) done owned hdone hbound' hslots hnd hownI hi
        change ExecFrom (model := model) P f s₀.fn R st (.halt stinit)
        change ExecFrom (model := model) P f sA.fn R st (.halt stinit) at hout
        rwa [hfnA] at hout
  | @«break» funs V st =>
    intro fenv env R lctx rets s₀ s₁ renv _joins _ henv _huniq hctx hfr _ _hp
      _ _ hfin _done _owned _hdone _hbound _hown htr
    cases lctx with
    | none => rw [trStmt] at htr; exact absurd htr (by simp [reject])
    | some l =>
      have hnone : renv = none := by
        rw [trStmt] at htr
        obtain ⟨vals, sA, h1, htr⟩ := M.bind_inv htr
        obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
        exact (M.pure_inv h3).1
      exact sim_break henv
        (hfr.mono (trStmt_grows fenv env (some l) rets .break s₀ renv s₁ htr).nextVal)
        (hfin hnone) htr
  | @«continue» funs V st =>
    intro fenv env R lctx rets s₀ s₁ renv _joins _ henv _huniq hctx hfr _ _hp
      _ _ hfin _done _owned _hdone _hbound _hown htr
    cases lctx with
    | none => rw [trStmt] at htr; exact absurd htr (by simp [reject])
    | some l =>
      have hnone : renv = none := by
        rw [trStmt] at htr
        obtain ⟨vals, sA, h1, htr⟩ := M.bind_inv htr
        obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
        exact (M.pure_inv h3).1
      exact sim_continue henv
        (hfr.mono (trStmt_grows fenv env (some l) rets .continue s₀ renv s₁ htr).nextVal)
        (hfin hnone) htr
  | @leave funs V st =>
    intro fenv env R lctx rets s₀ s₁ renv _joins _ henv _huniq hctx hfr _ _hp
      _ _ hfin _done _owned _hdone _hbound _hown htr
    cases rets with
    | none => rw [trStmt] at htr; exact absurd htr (by simp [reject])
    | some rs =>
      have hnone : renv = none := by
        rw [trStmt] at htr
        obtain ⟨vals, sA, h1, htr⟩ := M.bind_inv htr
        obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
        exact (M.pure_inv h3).1
      exact sim_leave henv (hfin hnone) htr
  | @seqNil funs V st =>
    intro fenv env R lctx rets s₀ s₁ renv _joins _ henv huniq hctx hfr _ _hp _
      _ _ _done _owned _hdone _hbound _hslots _hnd _hown htr
    exact sim_seqNil henv huniq hfr htr
  | @seqCons funs V st s rest V1 st1 V2 st2 o h1 h2 ih1 ih2 =>
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
  | @seqStop funs V st s rest V1 st1 o h1 hne ih1 =>
    intro fenv env R lctx rets s₀ s₁ renv joins hfe henv huniq hctx hfr hvalid
      hp hcompl hcp hfin done owned hdone hbound hslots hnd hown htr
    cases s with
    | funDef n ps rs body =>
      cases h1
      exact absurd rfl hne
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
        have hfinA : CurFinal f sA.fn := by simpa only [hfn] using hfin hrenv
        have hownA := trStmts_owned_back fenv lctx rets rest env true
          sA s₁ done renv owned hboundA hslotsA hnd hown htail
        exact SOut.of_nonNormal hne (by rw [hfn])
          (ih1 fenv env R lctx rets s₀ sA none joins hfe henv huniq hctx hfr
            hvalid hp hcomplA hcpA
            (fun _ => hfinA) done (stmtFuncIds fenv rest ++ owned) hdone
            hbound hownA hhead)
      | some envA =>
        have hgTail : SGrows sA s₁ :=
          trStmts_grows fenv envA lctx rets false rest sA renv s₁ htail
        have hcomplA : Completes f sA.fn joins := SGrowsAt.completes_of hgTail hcompl
        have hcpA : CurPlaced f sA.fn :=
          trStmts_curPlaced_back hvalidA hpA hcompl hcp hfin htail
        have hownA := trStmts_owned_back fenv lctx rets rest envA false
          sA s₁ done renv owned hboundA hslotsA hnd hown htail
        exact SOut.of_nonNormal hne hgTail.nextVal
          (ih1 fenv env R lctx rets s₀ sA (some envA) joins hfe henv huniq hctx
            hfr hvalid hp hcomplA hcpA
            (by simp) done (stmtFuncIds fenv rest ++ owned) hdone hbound
            hownA hhead)
  | @loopDone funs V st c post body cv st1 hc hz ihc =>
    intro fenv env rets s₀ s₁ renv joins layout hfe huniq hctx hvalid hp
      hcompl hcp _hfin done owned hdone hbound hown R henv hfr hclean hreb
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
    have finish :
        Completes f sN.fn (exitId :: postId :: joins) →
        SGrowsAt 0 sE s₁ → sJ.fn.nextVal ≤ s₁.fn.nextVal →
        s₁.fn.curId = exitId → s₁.fn.cur = [] →
        renv = some (env.setMany (modifiedX env [post, body]) exitParams) →
        LHOut (model := model) P f rets sA.fn.nextVal sI s₁ R
          renv V st st1 .normal := by
      intro hcN ge hnextJ1 hcurExit hcurExit0 hrenv
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
      obtain ⟨uQ, sQ, h17, htr⟩ := M.bind_inv htr
      cases uQ with
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
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sP none sQ h17
        have hcP := SGrowsAt.completes_of gp hcQ
        have hcO := Completes.of_moveTo_protected (by simp) h16 hcP
        have gb := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) hParams)
          (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
          sN none sO h15
        have hcN := SGrowsAt.completes_of gb hcO
        have ge0 := eN.trans (gb.mono (Nat.zero_le _))
        have ge1 := ge0.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h16)
        have ge2 := ge1.trans (gp.mono (Nat.zero_le _))
        have ge := ge2.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h18)
        have gn0 := gb.mono (Nat.zero_le _)
        have gn1 := gn0.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h16)
        have gn2 := gn1.trans (gp.mono (Nat.zero_le _))
        have gn := gn2.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h18)
        exact finish hcN ge
          (Nat.le_trans aJN.nextVal gn.nextVal)
          (by rw [M.moveTo_apply] at h18
              exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h18).2).symm)
          (by rw [M.moveTo_apply] at h18
              simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h18).2)
          hrenv
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
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sP (some envP) sQ h17
        have hcP := SGrowsAt.completes_of gp hcQ
        have hcO := Completes.of_moveTo_protected (by simp) h16 hcP
        have gb := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) hParams)
          (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
          sN none sO h15
        have hcN := SGrowsAt.completes_of gb hcO
        have ge0 := eN.trans (gb.mono (Nat.zero_le _))
        have ge1 := ge0.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h16)
        have ge2 := ge1.trans (gp.mono (Nat.zero_le _))
        have ge3 := ge2.trans (gQS.mono (Nat.zero_le _))
        have ge := ge3.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h20)
        have gn0 := gb.mono (Nat.zero_le _)
        have gn1 := gn0.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h16)
        have gn2 := gn1.trans (gp.mono (Nat.zero_le _))
        have gn3 := gn2.trans (gQS.mono (Nat.zero_le _))
        have gn := gn3.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h20)
        exact finish hcN ge
          (Nat.le_trans aJN.nextVal gn.nextVal)
          (by rw [M.moveTo_apply] at h20
              exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h20).2).symm)
          (by rw [M.moveTo_apply] at h20
              simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h20).2)
          hrenv
    | some envB =>
      obtain ⟨xvB, sP, h16, htr⟩ := M.bind_inv htr
      obtain ⟨uQ, sQ, h17, htr⟩ := M.bind_inv htr
      obtain ⟨uR, sR, h18, htr⟩ := M.bind_inv htr
      obtain ⟨postEnv, sS, h19, htr⟩ := M.bind_inv htr
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
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sR none sS h19
        have hcR := SGrowsAt.completes_of gp hcS
        have hcQ := Completes.of_moveTo_protected (by simp) h18 hcR
        have gOQ : SGrows sO sQ :=
          (SGrowsAt.of_grows (Grows.of_liftO h16)).trans
            (SGrowsAt.of_sealCur h17)
        have hcO := SGrowsAt.completes_of gOQ hcQ
        have gb := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) hParams)
          (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
          sN (some envB) sO h15
        have hcN := SGrowsAt.completes_of gb hcO
        have ge0 := eN.trans (gb.mono (Nat.zero_le _))
        have ge1 := ge0.trans (gOQ.mono (Nat.zero_le _))
        have ge2 := ge1.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h18)
        have ge3 := ge2.trans (gp.mono (Nat.zero_le _))
        have ge := ge3.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h20)
        have gn0 := gb.mono (Nat.zero_le _)
        have gn1 := gn0.trans (gOQ.mono (Nat.zero_le _))
        have gn2 := gn1.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h18)
        have gn3 := gn2.trans (gp.mono (Nat.zero_le _))
        have gn := gn3.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h20)
        exact finish hcN ge
          (Nat.le_trans aJN.nextVal gn.nextVal)
          (by rw [M.moveTo_apply] at h20
              exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h20).2).symm)
          (by rw [M.moveTo_apply] at h20
              simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h20).2)
          hrenv
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
        have gp := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) postParams) none rets post
          sR (some envP) sS h19
        have hcR := SGrowsAt.completes_of gp hcS
        have hcQ := Completes.of_moveTo_protected (by simp) h18 hcR
        have gOQ : SGrows sO sQ :=
          (SGrowsAt.of_grows (Grows.of_liftO h16)).trans
            (SGrowsAt.of_sealCur h17)
        have hcO := SGrowsAt.completes_of gOQ hcQ
        have gb := trScope_grows fenv
          (env.setMany (modifiedX env [post, body]) hParams)
          (some ⟨exitId, postId, modifiedX env [post, body]⟩) rets body
          sN (some envB) sO h15
        have hcN := SGrowsAt.completes_of gb hcO
        have ge0 := eN.trans (gb.mono (Nat.zero_le _))
        have ge1 := ge0.trans (gOQ.mono (Nat.zero_le _))
        have ge2 := ge1.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h18)
        have ge3 := ge2.trans (gp.mono (Nat.zero_le _))
        have ge4 := ge3.trans (gSU.mono (Nat.zero_le _))
        have ge := ge4.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h22)
        have gn0 := gb.mono (Nat.zero_le _)
        have gn1 := gn0.trans (gOQ.mono (Nat.zero_le _))
        have gn2 := gn1.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h18)
        have gn3 := gn2.trans (gp.mono (Nat.zero_le _))
        have gn4 := gn3.trans (gSU.mono (Nat.zero_le _))
        have gn := gn4.trans (SGrowsAt.of_moveTo (Or.inl (Nat.zero_le _)) h22)
        exact finish hcN ge
          (Nat.le_trans aJN.nextVal gn.nextVal)
          (by rw [M.moveTo_apply] at h22
              exact (congrArg (fun z => z.fn.curId) (M.some_pair_inj h22).2).symm)
          (by rw [M.moveTo_apply] at h22
              simpa using congrArg (fun z => z.fn.cur) (M.some_pair_inj h22).2)
          hrenv
  | @loopCondHalt funs V st c post body st1 hc ihc =>
    intro fenv env rets s₀ s₁ renv joins layout hfe huniq hctx hvalid hp
      hcompl hcp _hfin done owned hdone hbound hown R henv hfr hclean hreb
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
    have hhalt := ihc.1 fenv
      (env.setMany (modifiedX env [post, body]) hParams) R sI sJ cvId
      (exitId :: postId :: joins) hfe henv hfr hpI hcJ hcpJ h10
    exact hhalt
  | @loopStep funs V st c post body cv st1 Vb stb ob Vp stp Vend stend o
      hc hnz hbodyStep hob hpost hloop ihc ihb ihpost ihloop =>
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
        LHOut (model := model) P f rets sA.fn.nextVal sI s₁ R
          renv Vend st stend o := by
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

  -- `sim_loopBodyNonNormal` also closes break: it consumes the body's
  -- `JumpTo exitId`, binds `exitParams`, and rebuilds `EnvOK` at the exit.
  | @loopPostHalt funs V st c post body cv st1 Vb stb ob Vp stp
      hc hnz hbodyStep hob hpost ihc ihb ihpost =>
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
        LHOut (model := model) P f rets sA.fn.nextVal sI s₁ R
          renv Vp st stp .halt := by
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
      have hpostHalt := ihpost fenv
        (env.setMany (modifiedX env [post, body]) postParams) RP none rets
        sPost sPostOut postEnv (exitId :: joins) hfe henvP
        (huniq.setMany _ _) (hctx.setMany _ _) hfrP hvalidPost hpPost
        hcomplPostOut hcpPostOut
        hfinPostOut done owned hdone hboundPost hownPostOut htrPostStmt
      exact hsimP (.halt stp) hpostHalt
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

  -- `sim_loopBodyNonNormal` also closes break: it consumes the body's
  -- `JumpTo exitId`, binds `exitParams`, and rebuilds `EnvOK` at the exit.
  | @loopBreak funs V st c post body cv st1 Vb stb _hc hnz hb ihc ihb =>
    change LOut (model := model) P f funs V st c post body Vb stb .normal doneFuncs
    simpa using sim_loopBodyNonNormal hfuncs ihc hb ihb hnz
      (Or.inr (Or.inr rfl))
  | @loopLeave funs V st c post body cv st1 Vb stb _hc hnz hb ihc ihb =>
    change LOut (model := model) P f funs V st c post body Vb stb .leave doneFuncs
    simpa using sim_loopBodyNonNormal hfuncs ihc hb ihb hnz
      (Or.inr (Or.inl rfl))
  | @loopBodyHalt funs V st c post body cv st1 Vb stb _hc hnz hb ihc ihb =>
    change LOut (model := model) P f funs V st c post body Vb stb .halt doneFuncs
    simpa using sim_loopBodyNonNormal hfuncs ihc hb ihb hnz (Or.inl rfl)

/-! `trScope_sim` (the scope wrapper WITHOUT register-freshness premises) was
deleted: the statement is false as written.  `SOut.normal` asserts
`∃ R₁, Regs.Le R R₁ ∧ RegsFresh R₁ s₁.fn`, yet nothing constrained `R`:
with `body := []`, empty environments, `s₀ = s₁ = initBState`, and
`R := fun _ => some 0`, every premise holds while the conclusion forces both
`R₁ = Regs.empty` and `R₁ 0 = some 0`.  `CurValid s₀`, `CurPlaced f s₁.fn`,
and `renv = none → CurFinal f s₁.fn` were likewise underivable.
`trScope_sim_of_fresh` below is that statement with exactly the four missing
premises added; `ofBlock_sound'` uses it, discharging all four at the
top-level instantiation (`R = Regs.empty`, `s₀ = initBState`). -/

/-- **The scope wrapper, with the premises `Motive` actually needs.**  The
conclusion of the deleted false wrapper above, plus the four facts it omitted.  Every
one of them holds at the top-level instantiation in `ofBlock_sound'`. -/
theorem trScope_sim_of_fresh {P : Prog} {f : Func}
    {funs : YulSemantics.FunEnv yulD} {fenv : FMap}
    {V V' : VEnv yulD} {env : VMap} {R : Regs}
    {lctx : Option LoopCtx} {rets : Option (List Ident)}
    {body : List (Stmt Op)} {s₀ s₁ : BState} {renv : Option VMap}
    {doneFuncs : Array (Option Func)}
    {yst yst' : EvmState} {o : Outcome}
    (hfuncs : FuncTableComplete P doneFuncs)
    (hfe : FEnvOK (model := model) P funs fenv)
    (henv : EnvOK (model := model) env V R)
    (huniq : env.Unique)
    (hctx : CtxVars lctx rets env)
    (hfr : RegsFresh R s₀.fn)
    (hvalid : CurValid s₀)
    (hcompl : Completes f s₁.fn)
    (hcp : CurPlaced f s₁.fn)
    (hfin : renv = none → CurFinal f s₁.fn)
    (hfuncsEq : s₁.funcs = doneFuncs)
    (htr : trScope fenv env lctx rets body s₀ = some (renv, s₁))
    (hstep : YulSemantics.ExecStmt yulD funs V yst (.block body) V' yst' o) :
    SOut (model := model) P f lctx rets s₀ s₁ R renv V' yst yst' o :=
  have hown : FOwned [] s₁ s₁ := by
    have ho := hfuncs.owned_nil
    rw [← hfuncsEq] at ho
    exact ⟨ho.nodup, ho.pending, ho.filled⟩
  sim (f := f) hfuncs hstep fenv env R lctx rets s₀ s₁ renv [] hfe henv huniq
    hctx hfr hvalid (ProtectedAt.nil s₀.fn) hcompl hcp hfin s₁ [] hfuncsEq
    (by simp) hown (by rw [trStmt]; exact htr)

/-! ## Construction soundness -/

/-- **Construction soundness.** If the construction accepts `prog` and the Yul
semantics runs it, the SSA program runs to the same final state and outcome.

The non-local top-level outcomes are impossible: with no loop context and no
enclosing function, `SOut`'s `break`/`continue`/`leave` cases demand
`none = some _`. -/
theorem ofBlock_sound' {prog : YulSemantics.Block Op} {P : Prog}
    {yst0 : EvmState} {V' : VEnv yulD} {yst' : EvmState} {o : Outcome}
    (hof : ofBlock prog = some P)
    (hrun : YulSemantics.Run yulD prog yst0 V' yst' o) :
    Run (model := model) P yst0 yst' o := by
  obtain ⟨_hwf, main, s, hbuild, hmapM, rfl⟩ := ofBlock_inv hof
  obtain ⟨renv, s₁, htr, hparams, hnrets, hentry, hfuncs, hblocks⟩ :=
    buildMain_inv hbuild
  -- the finished `main` completes the builder state the top-level scope left
  have hext : Completes P.main s₁.fn := by
    cases renv with
    | none =>
      exact ⟨fun i b _ _ hi => by rw [hblocks]; exact hi,
        fun i b hb => ⟨b, by rw [hblocks]; exact hb, rfl⟩,
        by rw [hblocks]⟩
    | some e =>
      obtain ⟨b, hb, hmb⟩ := hblocks
      refine ⟨fun i b' _ hne hi => ?_, fun i b' hb' => ?_, ?_⟩
      · rw [hmb, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_ne (Ne.symm hne)]
        exact hi
      · by_cases hc : i = s₁.fn.curId
        · subst hc
          obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
          refine ⟨⟨b'.params, s₁.fn.cur.reverse, .ret []⟩, ?_, rfl⟩
          rw [hmb, Array.set!_eq_setIfInBounds,
            Array.getElem?_setIfInBounds_self_of_lt (lt_size_of_getElem? hb)]
        · refine ⟨b', ?_, rfl⟩
          rw [hmb, Array.set!_eq_setIfInBounds,
            Array.getElem?_setIfInBounds_ne (Ne.intro fun hh => hc hh.symm)]
          exact hb'
      · rw [hmb]; simp
  -- the four placement/freshness facts `Motive` needs, at the top level
  have hvalid0 : CurValid initBState := by
    simp [CurValid, initBState]
  have htrStmt : trStmt [] [] none none (.block prog) initBState
      = some (renv, s₁) := by
    rw [trStmt]; exact htr
  have hvalid1 : CurValid s₁ := (trStmt_cur hvalid0 htrStmt).1
  have hfresh0 : RegsFresh (Regs.empty) initBState.fn := fun _ _ => rfl
  have hplace : CurPlaced P.main s₁.fn ∧ (renv = none → CurFinal P.main s₁.fn) := by
    cases renv with
    | none =>
      have hfin : CurFinal P.main s₁.fn := by
        intro b hb; rw [hblocks]; exact hb
      exact ⟨curPlaced_of_curFinal hvalid1
        (trScope_none_cur_nil [] [] none none prog initBState s₁ htr) hfin,
        fun _ => hfin⟩
    | some e =>
      obtain ⟨b, hb, hmb⟩ := hblocks
      refine ⟨⟨⟨[], .ret []⟩, ⟨b.params, s₁.fn.cur.reverse, .ret []⟩, ?_, by simp,
        rfl⟩, fun hq => absurd hq (by simp)⟩
      rw [hmb, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_self_of_lt (lt_size_of_getElem? hb)]
  -- the top-level source derivation is one `block` rule over `prog`
  rw [YulSemantics.Run] at hrun
  cases hrun with
  | @block _ _ _ _ Vb stb o hstmts =>
    have hmapM' : FuncTableComplete P s₁.funcs := by
      rw [← hfuncs]
      exact hmapM
    have hsim := trScope_sim_of_fresh (model := model) (P := P) (f := P.main)
      (funs := []) (fenv := []) (V := []) (env := []) (R := Regs.empty)
      (doneFuncs := s₁.funcs)
      hmapM' .nil EnvOK.nil VMap.unique_nil ⟨by simp, by simp⟩ hfresh0 hvalid0
      hext hplace.1
      hplace.2 rfl htr (.block hstmts)
    -- `initBState` is the entry block, empty and current
    have hentryCur : ∀ rest, CurOK P.main initBState.fn rest
        → ∃ eb, P.main.blocks[P.main.entry]? = some eb
            ∧ rest = ⟨eb.instrs, eb.term⟩ := by
      intro rest hc
      obtain ⟨b, hb, hi, ht⟩ := hc
      refine ⟨b, by rw [hentry]; exact hb, ?_⟩
      cases rest
      simp only [initBState] at hi
      simp_all
    cases o with
    | normal =>
      obtain ⟨env', R₁, hrenv, _hle, _hbelow, _hfr, _henv', _huniq, hsimS⟩ := hsim
      -- the fall-through seal put `ret []` on the block the scope ended in
      obtain ⟨b, hb, hmb⟩ : ∃ b, s₁.fn.blocks[s₁.fn.curId]? = some b
          ∧ P.main.blocks
              = s₁.fn.blocks.set! s₁.fn.curId ⟨b.params, s₁.fn.cur.reverse, .ret []⟩ := by
        rw [hrenv] at hblocks; exact hblocks
      have hcur : CurOK P.main s₁.fn ⟨[], .ret []⟩ := by
        refine ⟨⟨b.params, s₁.fn.cur.reverse, .ret []⟩, ?_, by simp, rfl⟩
        rw [hmb, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_self_of_lt
            (Array.getElem?_eq_some_iff.mp hb |>.1)]
      obtain ⟨rest, hc, hexec⟩ :=
        hsimS (.ret [] yst') (execFrom_ret hcur (by simp))
      obtain ⟨eb, heb, rfl⟩ := hentryCur rest hc
      exact .normal heb hexec
    | halt =>
      obtain ⟨rest, hc, hexec⟩ := hsim
      obtain ⟨eb, heb, rfl⟩ := hentryCur rest hc
      exact .halt heb hexec
    | «break» =>
      obtain ⟨lc, _, _, hlc, _⟩ := hsim
      exact absurd hlc (by simp)
    | «continue» =>
      obtain ⟨lc, _, _, hlc, _⟩ := hsim
      exact absurd hlc (by simp)
    | leave =>
      obtain ⟨rs, _, hrs, _⟩ := hsim
      exact absurd hrs (by simp)

end Semantics
end YulEvmCompiler.SsaCfg
