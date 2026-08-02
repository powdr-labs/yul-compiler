import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.BlockSim
import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.LoopStepSim
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.OfYulSound.Sim

The simulation theorem, and construction soundness.

`sim` — the one mutual induction over the statement classes that all the
preceding modules feed — plus `trScope_sim_of_fresh` and the top-level
`ofBlock_sound'`.

The fat clauses live in their own modules and are dispatched to from here:
`CallSim` (builtin and user-call expressions), `CondSim` (`if`/`switch`),
`BlockSim` (sequencing and the `for` wrapper), `Switch` (the switch dispatch
chain), `LoopSim` and `LoopStepSim` (the loop-iteration class).  What is left
inline is the leaf clauses and the plumbing that reads the same way as the
`Motive` it discharges.
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
    exact sim_builtinOk hb iha
  | @builtinHalt funs V st op args argvals st1 st2 hargs hb iha =>
    exact sim_builtinHalt hb iha
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
  | @callOk funs V st fn args argvals st1 decl cenv Vend st2 o
      hargs hlk harity hbody ho iha ihb =>
    exact sim_callOk hlk harity ho iha ihb
  | @callHalt funs V st fn args argvals st1 decl cenv Vend st2
      hargs hlk harity hbody iha ihb =>
    exact sim_callHalt hlk harity iha ihb
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
    exact sim_ifTrue hnz hbody ihc ihb
  | @ifFalse funs V st c body cv st1 hc hz ihc =>
    exact sim_ifFalse hz ihc
  | @ifHalt funs V st c body st1 hc ihc =>
    exact sim_ifHalt ihc
  | switchExec hc hsel ihc ihs => exact sim_switchExec hsel ihc ihs
  | @switchHalt funs V st c cases dflt st1 hc ihc =>
    exact sim_switchHalt ihc
  | @forLoop funs V st init c post body Vinit stinit Vend stend o
      hinit hloop ihi ihl =>
    exact sim_forLoop hinit hloop ihi ihl
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
    exact sim_seqCons h1 ih1 ih2
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
    exact sim_loopDone hz ihc
  | @loopCondHalt funs V st c post body st1 hc ihc =>
    exact sim_loopCondHalt ihc
  | @loopStep funs V st c post body cv st1 Vb stb ob Vp stp Vend stend o
      hc hnz hbodyStep hob hpost hloop ihc ihb ihpost ihloop =>
    exact sim_loopStep ihc hnz hbodyStep hob hpost ihb ihpost ihloop
  | @loopPostHalt funs V st c post body cv st1 Vb stb ob Vp stp
      hc hnz hbodyStep hob hpost ihc ihb ihpost =>
    exact sim_loopPostHalt ihc hnz hbodyStep hob ihb ihpost

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
