import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.Switch
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.OfYulSound.CallSim

The builtin and user-call expression cases of `sim`.

**The callee-entry bridge.**  `FMap.get_ok hfe hlk` already hands over
`fenv.get fn = some fid`, `FuncOK P fenv' decl fid` and `FEnvOK P cenv fenv'`,
and `FuncOK` unfolds to `P.funcs[fid]? = some g`,
`trFunc fenv' decl.params decl.rets decl.body sP = some (g, sQ)` and
`FContents sQ ⟨_, P.funcs⟩`.  Inverting that `trFunc` gives the entry block
(`newBlock []`/`moveTo`), the parameter ids `pids = g.params`, the zero-return
`const` prologue (`simS_consts` executes it, `EnvOK.zip`/`EnvOK.zip_bindZeros`
matches it against `decl.params.zip argvals ++ bindZeros decl.rets`), and the
body run `trStmt fenv' env0 none (some decl.rets) (.block decl.body) sX
= some (renvC, sY)`.  `simS_call`/`execFrom_callHalt` then splice the callee's
`Exec` into the caller's `.call ds fid as`, and the `.leave`/fall-through
return values come from `SOut`'s `leave` clause and from the
`sealCur (.ret vals)` tail exactly as in `ofBlock_sound'`'s `main`.  `FuncOK`'s
pending-slot budget and `FuncTableComplete.get_rev` provide the `FOwned`
witness needed by the recursive body simulation.  Splitting the final return
seal reconstructs `Completes`, `CurPlaced`, and `CurFinal` for the callee in
both fall-through and explicit-leave paths.  All of that is `sim_callEntry`,
which `sim_callOk` and `sim_callHalt` share.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics (Ident Literal Expr Stmt VEnv Outcome)
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal evmWithExternal)

section Semantics
variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates model.gas

/-- Read the return values a `leave`-free callee leaves in its environment
off the `VEnv` lookups the source derivation supplies. -/
theorem retvals_eq {Vend : VEnv yulD} {rs : List Ident} {vals : List U256}
    (hv : YulSemantics.Forall₂ (fun x v => YulSemantics.VEnv.get Vend x = some v)
      rs vals) :
    vals = rs.map (fun r => (YulSemantics.VEnv.get Vend r).getD
      (YulSemantics.Dialect.zero yulD)) := by
  induction hv with
  | nil => rfl
  | cons hh _ ih => simp only [List.map_cons, hh, Option.getD_some, ih]

set_option maxHeartbeats 1000000 in
/-- **The callee-entry bridge, shared by `sim_callOk` and `sim_callHalt`.**
`FMap.get_ok` hands over the callee's slot, `FuncOK` its `trFunc` run;
inverting that run gives the entry block, the parameter ids, the zero-return
`const` prologue and the body fragment.  The prologue is executed by
`simS_consts` and matched against `decl.params.zip argvals ++ bindZeros
decl.rets`, the pending-slot budget supplies the body's `FOwned` witness, and
`hres` turns the body's own `SOut` into the callee's `Exec` — the only part
that depends on how the callee left. -/
theorem sim_callEntry {P : Prog} {funs cenv : YulSemantics.FunEnv yulD}
    {fn : Ident} {argvals : List U256} {st1 st2 : EvmState}
    {decl : YulSemantics.FDecl yulD} {Vend : VEnv yulD} {o : Outcome}
    {res : FRes} {doneFuncs : Array (Option Func)}
    {hfuncs : FuncTableComplete P doneFuncs}
    (hlk : YulSemantics.lookupFun funs fn = some (decl, cenv))
    (harity : argvals.length = decl.params.length)
    (ihb : ∀ {g : Func}, Motive (model := model) P g cenv
      (decl.params.zip argvals ++ YulSemantics.bindZeros yulD decl.rets) st1
      doneFuncs hfuncs (.stmt (.block decl.body)) (.sres Vend st2 o))
    (hres : ∀ (g : Func) (RR : Regs) (sX sY : BState) (renvC : Option VMap),
      (∀ (envEnd : VMap), renvC = some envEnd →
        ∀ (REnd : Regs), EnvOK (model := model) envEnd Vend REnd →
        ExecFrom (model := model) P g sY.fn REnd st2
          (.ret (decl.rets.map fun r =>
            (YulSemantics.VEnv.get Vend r).getD
              (YulSemantics.Dialect.zero yulD)) st2)) →
      SOut (model := model) P g none (some decl.rets) sX sY RR renvC Vend st1
        st2 o →
      ExecFrom (model := model) P g sX.fn RR st1 res)
    (fenv : FMap) (hfe : FEnvOK (model := model) P funs fenv) :
    ∃ (fid : FuncId) (g : Func) (eb : Block),
      FMap.get fenv fn = some fid ∧ P.funcs[fid]? = some g
        ∧ g.params.length = argvals.length
        ∧ g.blocks[g.entry]? = some eb
        ∧ Exec (model := model) P g (Regs.empty.setMany g.params argvals) st1
            ⟨eb.instrs, eb.term⟩ res := by
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
    obtain ⟨renvC, sY, h8, htail⟩ := M.bind_inv htrF
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
      have hfall : ∀ (envEnd : VMap), (none : Option VMap) = some envEnd →
          ∀ (REnd : Regs), EnvOK (model := model) envEnd Vend REnd →
          ExecFrom (model := model) P g sY.fn REnd st2
            (.ret (decl.rets.map fun r =>
              (YulSemantics.VEnv.get Vend r).getD
                (YulSemantics.Dialect.zero yulD)) st2) := by
        intro _ heq
        exact absurd heq (by simp)
      obtain ⟨eb, heb, he⟩ :=
        entry_of (hsimConst _ (hres g RR sX sY _ hfall hsout))
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
      have hfall : ∀ (envEnd' : VMap), some envEnd = some envEnd' →
          ∀ (REnd : Regs), EnvOK (model := model) envEnd' Vend REnd →
          ExecFrom (model := model) P g sY.fn REnd st2
            (.ret (decl.rets.map fun r =>
              (YulSemantics.VEnv.get Vend r).getD
                (YulSemantics.Dialect.zero yulD)) st2) := by
        intro envEnd' heq REnd henvEnd
        obtain rfl : envEnd' = envEnd := (Option.some.inj heq).symm
        obtain ⟨_, rvals, hrget, hrvals⟩ := edgeArgs_ok henvEnd hedge
        rw [retvals_eq hrvals] at hrget
        have hcurRet : CurOK g sY.fn ⟨[], .ret vals⟩ := by
          refine ⟨⟨b.params, sY.fn.cur.reverse, .ret vals⟩, ?_, by simp, rfl⟩
          rw [hgblocks, hblocks, Array.set!_eq_setIfInBounds,
            Array.getElem?_setIfInBounds_self_of_lt (lt_size_of_getElem? hb)]
        exact execFrom_ret hcurRet hrget
      obtain ⟨eb, heb, he⟩ :=
        entry_of (hsimConst _ (hres g RR sX sY _ hfall hsout))
      exact ⟨fid, g, eb, hfid, hg, by rw [hgparams]; omega,
        by rw [hgentry]; exact heb, by simpa [RP, hgparams] using he⟩

set_option maxHeartbeats 400000 in
/-- **A builtin that returns.**  The arguments are evaluated left of the
builtin instruction, which the construction emits verbatim. -/
theorem sim_builtinOk {P : Prog} {f : Func} {funs : YulSemantics.FunEnv yulD}
    {V : VEnv yulD} {st st1 st2 : EvmState} {op : Op} {args : List (Expr Op)}
    {argvals rets : List U256} {doneFuncs : Array (Option Func)}
    {hfuncs : FuncTableComplete P doneFuncs}
    (hb : YulSemantics.Dialect.Builtin yulD op argvals st1 (.ok rets st2))
    (iha : Motive (model := model) P f funs V st doneFuncs hfuncs
      (.args args) (.eres (.vals argvals st1))) :
    Motive (model := model) P f funs V st doneFuncs hfuncs
      (.expr (.builtin op args)) (.eres (.vals rets st2)) := by
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

set_option maxHeartbeats 400000 in
/-- **A builtin that halts.**  Everything after the builtin instruction is
unreachable, so the fragment's own suffix never runs. -/
theorem sim_builtinHalt {P : Prog} {f : Func} {funs : YulSemantics.FunEnv yulD}
    {V : VEnv yulD} {st st1 st2 : EvmState} {op : Op} {args : List (Expr Op)}
    {argvals : List U256} {doneFuncs : Array (Option Func)}
    {hfuncs : FuncTableComplete P doneFuncs}
    (hb : YulSemantics.Dialect.Builtin yulD op argvals st1 (.halt st2))
    (iha : Motive (model := model) P f funs V st doneFuncs hfuncs
      (.args args) (.eres (.vals argvals st1))) :
    Motive (model := model) P f funs V st doneFuncs hfuncs
      (.expr (.builtin op args)) (.eres (.halt st2)) := by
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

set_option maxHeartbeats 1000000 in
/-- **A user call that returns.**  The callee is looked up in the completed
function table, its prologue binds the arguments and zeroes the returns, and
the callee body's own simulation supplies the `Exec` the `call` instruction
consumes. -/
theorem sim_callOk {P : Prog} {f : Func} {funs cenv : YulSemantics.FunEnv yulD}
    {V Vend : VEnv yulD} {st st1 st2 : EvmState} {fn : Ident}
    {args : List (Expr Op)} {argvals : List U256}
    {decl : YulSemantics.FDecl yulD} {o : Outcome}
    {doneFuncs : Array (Option Func)}
    {hfuncs : FuncTableComplete P doneFuncs}
    (hlk : YulSemantics.lookupFun funs fn = some (decl, cenv))
    (harity : argvals.length = decl.params.length)
    (ho : o = .normal ∨ o = .leave)
    (iha : Motive (model := model) P f funs V st doneFuncs hfuncs
      (.args args) (.eres (.vals argvals st1)))
    (ihb : ∀ {g : Func}, Motive (model := model) P g cenv
      (decl.params.zip argvals ++ YulSemantics.bindZeros yulD decl.rets) st1
      doneFuncs hfuncs (.stmt (.block decl.body)) (.sres Vend st2 o)) :
    Motive (model := model) P f funs V st doneFuncs hfuncs
      (.expr (.call fn args))
      (.eres (.vals (decl.rets.map fun r =>
        (YulSemantics.VEnv.get Vend r).getD
          (YulSemantics.Dialect.zero yulD)) st2)) := by
    have calleeExec : ∀ (fenv : FMap),
        FEnvOK (model := model) P funs fenv →
        ∃ (fid : FuncId) (g : Func) (eb : Block),
          FMap.get fenv fn = some fid ∧ P.funcs[fid]? = some g
          ∧ g.params.length = argvals.length
          ∧ g.blocks[g.entry]? = some eb
          ∧ Exec (model := model) P g (Regs.empty.setMany g.params argvals) st1
              ⟨eb.instrs, eb.term⟩
              (.ret (decl.rets.map fun r =>
                (YulSemantics.VEnv.get Vend r).getD
                  (YulSemantics.Dialect.zero yulD)) st2) :=
      sim_callEntry hlk harity ihb fun g RR sX sY renvC hfall hsout => by
        rcases ho with rfl | rfl
        · obtain ⟨envEnd, REnd, henvEq, -, -, -, henvEnd, -, hsimBody⟩ := hsout
          exact hsimBody _ (hfall envEnd henvEq REnd henvEnd)
        · obtain ⟨rs, vals, hrs, hvals, hex⟩ := hsout
          obtain rfl : rs = decl.rets := Option.some.inj hrs.symm
          rwa [retvals_eq hvals] at hex
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

set_option maxHeartbeats 1000000 in
/-- **A user call whose callee halts.**  Same callee entry as `sim_callOk`;
the callee's `Exec` ends in `.halt`, which the `call` instruction propagates
without binding any results. -/
theorem sim_callHalt {P : Prog} {f : Func}
    {funs cenv : YulSemantics.FunEnv yulD}
    {V Vend : VEnv yulD} {st st1 st2 : EvmState} {fn : Ident}
    {args : List (Expr Op)} {argvals : List U256}
    {decl : YulSemantics.FDecl yulD}
    {doneFuncs : Array (Option Func)}
    {hfuncs : FuncTableComplete P doneFuncs}
    (hlk : YulSemantics.lookupFun funs fn = some (decl, cenv))
    (harity : argvals.length = decl.params.length)
    (iha : Motive (model := model) P f funs V st doneFuncs hfuncs
      (.args args) (.eres (.vals argvals st1)))
    (ihb : ∀ {g : Func}, Motive (model := model) P g cenv
      (decl.params.zip argvals ++ YulSemantics.bindZeros yulD decl.rets) st1
      doneFuncs hfuncs (.stmt (.block decl.body)) (.sres Vend st2 .halt)) :
    Motive (model := model) P f funs V st doneFuncs hfuncs
      (.expr (.call fn args)) (.eres (.halt st2)) := by
    have calleeHalt : ∀ (fenv : FMap),
        FEnvOK (model := model) P funs fenv →
        ∃ (fid : FuncId) (g : Func) (eb : Block),
          FMap.get fenv fn = some fid ∧ P.funcs[fid]? = some g
          ∧ g.params.length = argvals.length
          ∧ g.blocks[g.entry]? = some eb
          ∧ Exec (model := model) P g (Regs.empty.setMany g.params argvals) st1
              ⟨eb.instrs, eb.term⟩ (.halt st2) :=
      sim_callEntry hlk harity ihb fun _ _ _ _ _ _ hsout => hsout
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
end Semantics
end YulEvmCompiler.SsaCfg
