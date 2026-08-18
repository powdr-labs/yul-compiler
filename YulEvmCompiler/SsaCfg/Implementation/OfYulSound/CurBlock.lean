import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.ModStmts
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.OfYulSound.CurBlock

Current-block bookkeeping.

`CurFinal`, the non-normal statement leaves (`sim_leave`/`sim_break`/
`sim_continue`), `NoShadow`, the `SOut` combinators, the reserved-block edges
as `SimS` steps, and the `CurPlaced`/`CurSame`/`CurMoved`/`CurSealed`/
`CurOpen`/`CurClosed`/`CurValid` algebra.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics (Ident Literal Expr Stmt VEnv Outcome)
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal evmWithExternal)

section Semantics
variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates YulSemantics.EVM.ExternalGas.any

/-! ### Statement-class leaves

Per-case pieces of the main induction, each usable on its own. -/

/-- The block a *diverting* statement seals is final in the finished function.
`Completes.sealed` deliberately exempts the current block, so the diverting
leaves take this separately; the enclosing `cond`/`switch`/`forLoop` supplies
it, because each `moveTo`s a fresh join/exit block afterwards and its own
`Completes` then covers the sealed one. -/
def CurFinal (f : Func) (fn : FnState) : Prop :=
  ∀ b : Block, fn.blocks[fn.curId]? = some b → f.blocks[fn.curId]? = some b

omit model in
/-- After leaving a sealed block, statement-level growth preserves it: it is
no longer the exceptional current block in `SGrows.keep`. -/
theorem curFinal_of_move_grows {f : Func} {s sM sEnd : BState}
    {bid : BlockId} {u : Unit} {joins : List BlockId}
    (hmv : moveTo bid s = some (u, sM)) (hne : s.fn.curId ≠ bid)
    (hprot : s.fn.curId ∉ joins)
    (hg : SGrows sM sEnd) (hcompl : Completes f sEnd.fn joins) :
    CurFinal f s.fn := by
  rw [M.moveTo_apply] at hmv
  obtain ⟨-, rfl⟩ := M.some_pair_inj hmv
  intro b hb
  have hlt : s.fn.curId < s.fn.blocks.size := lt_size_of_getElem? hb
  have hkeep : sEnd.fn.blocks[s.fn.curId]? = some b :=
    hg.keep s.fn.curId b hlt hne hb
  have hneEnd : s.fn.curId ≠ sEnd.fn.curId := by
    rcases hg.curId with heq | hge
    · simpa [heq] using hne
    · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hlt (by simpa using hge))
  exact hcompl.sealed s.fn.curId b hprot hneEnd hkeep

omit model in
/-- Variant of `curFinal_of_move_grows` for a surrounding structured
translation.  Its later current block may be another block reserved by the
same construct, so freshness is measured against the construct's base `N`.
The block being left predates that base and therefore remains protected by
`SGrowsAt.keep`. -/
theorem curFinal_of_move_sgrowsAt {f : Func} {N : Nat} {s sM sEnd : BState}
    {bid : BlockId} {u : Unit} {joins : List BlockId}
    (hold : s.fn.curId < N)
    (hmv : moveTo bid s = some (u, sM)) (hne : s.fn.curId ≠ bid)
    (hprot : s.fn.curId ∉ joins)
    (hg : SGrowsAt N sM sEnd) (hcompl : Completes f sEnd.fn joins) :
    CurFinal f s.fn := by
  rw [M.moveTo_apply] at hmv
  obtain ⟨-, rfl⟩ := M.some_pair_inj hmv
  intro b hb
  have hkeep : sEnd.fn.blocks[s.fn.curId]? = some b :=
    hg.keep s.fn.curId b hold hne hb
  have hneEnd : s.fn.curId ≠ sEnd.fn.curId := by
    rcases hg.curId with heq | hge
    · simpa [heq] using hne
    · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hold hge)
  exact hcompl.sealed s.fn.curId b hprot hneEnd hkeep

omit model in
/-- What `sealCur` leaves behind: same current block id, empty pending list, and
the block now carrying the emitted instructions and the terminator. -/
theorem sealCur_cur {t : Term} {s s' : BState} {u : Unit}
    (h : sealCur t s = some (u, s')) :
    ∃ b : Block, s'.fn.curId = s.fn.curId ∧ s'.fn.cur = []
      ∧ s'.fn.blocks[s'.fn.curId]? = some ⟨b.params, s.fn.cur.reverse, t⟩ := by
  obtain ⟨b, hb, rfl⟩ := M.sealCur_inv h
  refine ⟨b, rfl, rfl, ?_⟩
  dsimp only
  rw [Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds_self_of_lt (lt_size_of_getElem? hb)]

omit model in
/-- …hence the sealed block *is* the rest of the fragment's current block. -/
theorem curOK_of_sealCur {f : Func} {t : Term} {s s' : BState} {u : Unit}
    (hfin : CurFinal f s'.fn) (h : sealCur t s = some (u, s')) :
    CurOK f s.fn ⟨[], t⟩ := by
  obtain ⟨b, hc, -, hg⟩ := sealCur_cur h
  refine ⟨⟨b.params, s.fn.cur.reverse, t⟩, ?_, by simp, rfl⟩
  rw [← hc]
  exact hfin _ hg

/-- **`leave`** — the construction reads the return variables and seals with
`ret`; the source rule leaves the environment and machine state alone. -/
theorem sim_leave {P : Prog} {f : Func} {fenv : FMap} {env : VMap} {R : Regs}
    {V : VEnv yulD} {lctx : Option LoopCtx} {rs : List Ident} {s₀ s₁ : BState}
    {renv : Option VMap} {yst : EvmState}
    (henv : EnvOK (model := model) env V R)
    (hfin : CurFinal f s₁.fn)
    (htr : trStmt fenv env lctx (some rs) .leave s₀ = some (renv, s₁)) :
    SOut (model := model) P f lctx (some rs) s₀ s₁ R renv V yst yst .leave := by
  rw [trStmt] at htr
  obtain ⟨ids, sA, h1, htr⟩ := M.bind_inv htr
  obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
  obtain ⟨hsA, vals, hget, hforall⟩ := edgeArgs_ok henv h1
  subst hsA
  obtain ⟨-, hs₁⟩ := M.pure_inv h3
  rw [hs₁] at hfin
  refine ⟨rs, vals, rfl, hforall, ?_⟩
  exact execFrom_ret (curOK_of_sealCur hfin h2) hget

/-- **`break`** — seal a jump to the loop's exit block carrying the loop's
variable set; `edgeArgs_ok` says the ids it passes hold the source values. -/
theorem sim_break {P : Prog} {f : Func} {fenv : FMap} {env : VMap} {R : Regs}
    {V : VEnv yulD} {l : LoopCtx} {rets : Option (List Ident)} {s₀ s₁ : BState}
    {renv : Option VMap} {yst : EvmState}
    (henv : EnvOK (model := model) env V R)
    (hfresh : RegsFresh R s₁.fn)
    (hfin : CurFinal f s₁.fn)
    (htr : trStmt fenv env (some l) rets .break s₀ = some (renv, s₁)) :
    SOut (model := model) P f (some l) rets s₀ s₁ R renv V yst yst .break := by
  rw [trStmt] at htr
  obtain ⟨ids, sA, h1, htr⟩ := M.bind_inv htr
  obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
  obtain ⟨hsA, vals, hget, hforall⟩ := edgeArgs_ok henv h1
  subst hsA
  obtain ⟨-, hs₁⟩ := M.pure_inv h3
  rw [hs₁] at hfin
  refine ⟨l, R, vals, rfl, Regs.Le.rfl R, Regs.BelowEq.rfl _ _, hfresh,
    hforall, fun res hjmp => ?_⟩
  exact execFrom_jump (curOK_of_sealCur hfin h2) hget hjmp

/-- **`continue`** — the same, to the loop's `post` block. -/
theorem sim_continue {P : Prog} {f : Func} {fenv : FMap} {env : VMap} {R : Regs}
    {V : VEnv yulD} {l : LoopCtx} {rets : Option (List Ident)} {s₀ s₁ : BState}
    {renv : Option VMap} {yst : EvmState}
    (henv : EnvOK (model := model) env V R)
    (hfresh : RegsFresh R s₁.fn)
    (hfin : CurFinal f s₁.fn)
    (htr : trStmt fenv env (some l) rets .continue s₀ = some (renv, s₁)) :
    SOut (model := model) P f (some l) rets s₀ s₁ R renv V yst yst .continue := by
  rw [trStmt] at htr
  obtain ⟨ids, sA, h1, htr⟩ := M.bind_inv htr
  obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
  obtain ⟨hsA, vals, hget, hforall⟩ := edgeArgs_ok henv h1
  subst hsA
  obtain ⟨-, hs₁⟩ := M.pure_inv h3
  rw [hs₁] at hfin
  refine ⟨l, R, vals, rfl, Regs.Le.rfl R, Regs.BelowEq.rfl _ _, hfresh,
    hforall, fun res hjmp => ?_⟩
  exact execFrom_jump (curOK_of_sealCur hfin h2) hget hjmp

/-- The construction rejects shadowing (`letDecl` checks `VMap.mem`), so the
names a scope declares are disjoint from the ones already visible. This is what
makes scope exit transparent to the outer environment. -/
def NoShadow (V Vb : VEnv yulD) : Prop :=
  ∀ x ∈ VEnv.names (Vb.take (Vb.length - V.length)), x ∉ VEnv.names V

/-- **Scope exit is transparent to outer names.** An outer variable reads the
same before and after `restore` — the bindings `restore` drops are the scope's
own declarations, whose names no outer variable shares. This is what the
`block`/`cond`/`switch`/`for` cases need to carry a non-local exit's edge values
(read at the divert point, inside the scope) out through the source's
`restore`. -/
theorem get_restore_of_noShadow {V Vb : VEnv yulD} (hns : NoShadow V Vb)
    {x : Ident} (hx : x ∈ VEnv.names V) :
    YulSemantics.VEnv.get (YulSemantics.restore V Vb) x
      = YulSemantics.VEnv.get Vb x := by
  have hsplit : Vb = Vb.take (Vb.length - V.length)
      ++ YulSemantics.restore V Vb := by
    rw [VEnv.restore_def, List.take_append_drop]
  conv_rhs => rw [hsplit]
  rw [VEnv.get_append_of_not_mem (fun hmem => hns x hmem hx)]

/-- Transport a *non-normal* `SOut` across a later builder state. The diverting
outcomes never mention the fragment's output environment — only its freshness
bound — so a fragment that diverts keeps its meaning when the construction goes
on to translate the dead code after it. -/
theorem SOut.of_nonNormal {P : Prog} {f : Func} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {s₀ s₁ s₁' : BState} {R : Regs}
    {renv renv' : Option VMap} {V' : VEnv yulD} {yst yst' : EvmState}
    {o : Outcome} (ho : o ≠ .normal)
    (hgrow : s₁.fn.nextVal ≤ s₁'.fn.nextVal)
    (h : SOut (model := model) P f lctx rets s₀ s₁ R renv V' yst yst' o) :
    SOut (model := model) P f lctx rets s₀ s₁' R renv' V' yst yst' o := by
  cases o with
  | normal => exact absurd rfl ho
  | halt => exact h
  | «break» =>
    obtain ⟨lc, R₁, vals, hlc, hle, hbelow, hfr, hforall, hcont⟩ := h
    exact ⟨lc, R₁, vals, hlc, hle, hbelow, hfr.mono hgrow, hforall, hcont⟩
  | «continue» =>
    obtain ⟨lc, R₁, vals, hlc, hle, hbelow, hfr, hforall, hcont⟩ := h
    exact ⟨lc, R₁, vals, hlc, hle, hbelow, hfr.mono hgrow, hforall, hcont⟩
  | leave => exact h

/-- Prepend a straight-line simulation to a statement result.  Structured
control uses this for the expression/dispatch edge before the selected body. -/
theorem SOut.prefix {P : Prog} {f : Func} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {s₀ sA s₁ : BState} {R₀ RA : Regs}
    {renv : Option VMap} {V' : VEnv yulD} {yst ystA yst' : EvmState}
    {o : Outcome}
    (hle : Regs.Le R₀ RA)
    (hbelow : Regs.BelowEq s₀.fn.nextVal R₀ RA)
    (hgrow : s₀.fn.nextVal ≤ sA.fn.nextVal)
    (hsim : SimS (model := model) P f s₀.fn R₀ yst sA.fn RA ystA)
    (h : SOut (model := model) P f lctx rets sA s₁ RA renv V' ystA yst' o) :
    SOut (model := model) P f lctx rets s₀ s₁ R₀ renv V' yst yst' o := by
  cases o with
  | normal =>
    obtain ⟨env', R₁, hr, hle1, hbelow1, hfr, henv, huniq, hsim1⟩ := h
    exact ⟨env', R₁, hr, hle.trans hle1,
      hbelow.trans (hbelow1.mono hgrow), hfr, henv, huniq,
      hsim.trans hsim1⟩
  | halt => exact hsim _ h
  | «break» =>
    obtain ⟨lc, R₁, vals, hlc, hle1, hbelow1, hfr, hvals, hcont⟩ := h
    exact ⟨lc, R₁, vals, hlc, hle.trans hle1,
      hbelow.trans (hbelow1.mono hgrow), hfr, hvals,
      fun res hj => hsim res (hcont res hj)⟩
  | «continue» =>
    obtain ⟨lc, R₁, vals, hlc, hle1, hbelow1, hfr, hvals, hcont⟩ := h
    exact ⟨lc, R₁, vals, hlc, hle.trans hle1,
      hbelow.trans (hbelow1.mono hgrow), hfr, hvals,
      fun res hj => hsim res (hcont res hj)⟩
  | leave =>
    obtain ⟨rs, vals, hrs, hvals, hex⟩ := h
    exact ⟨rs, vals, hrs, hvals, hsim _ hex⟩

/-- **`seqCons`** — the sequence combinator. A statement that completes
normally hands its register file, environment correspondence and freshness
bound to the rest of the list, and the two fragments' `SimS`s compose; every
non-normal outcome of the tail is carried back through the head's `SimS`.

This is a pure `SOut` combinator: it needs no construction inversion, which is
why the `seqCons` case of the main induction is a one-liner. -/
theorem SOut.seq {P : Prog} {f : Func} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {s₀ sA s₁ : BState} {R : Regs}
    {renv : Option VMap} {env' : VMap} {V1 V2 : VEnv yulD}
    {yst yst1 yst2 : EvmState} {o : Outcome}
    (hgrow : s₀.fn.nextVal ≤ sA.fn.nextVal)
    (hhead : SOut (model := model) P f lctx rets s₀ sA R (some env') V1 yst yst1 .normal)
    (htail : ∀ R₁ : Regs, Regs.Le R R₁ → RegsFresh R₁ sA.fn →
        EnvOK (model := model) env' V1 R₁ →
        env'.Unique →
        SOut (model := model) P f lctx rets sA s₁ R₁ renv V2 yst1 yst2 o) :
    SOut (model := model) P f lctx rets s₀ s₁ R renv V2 yst yst2 o := by
  obtain ⟨e', R₁, he', hle, hbelow, hfr, henv', huniq', hsim⟩ := hhead
  obtain rfl : e' = env' := (Option.some.inj he').symm
  have ht := htail R₁ hle hfr henv' huniq'
  cases o with
  | normal =>
    obtain ⟨e2, R₂, hr2, hle2, hbelow2, hfr2, henv2, huniq2, hsim2⟩ := ht
    exact ⟨e2, R₂, hr2, hle.trans hle2,
      hbelow.trans (hbelow2.mono hgrow), hfr2, henv2, huniq2,
      hsim.trans hsim2⟩
  | halt => exact hsim _ ht
  | «break» =>
    obtain ⟨lc, R₂, vals, hlc, hle2, hbelow2, hfr2, hforall, hcont⟩ := ht
    exact ⟨lc, R₂, vals, hlc, hle.trans hle2,
      hbelow.trans (hbelow2.mono hgrow), hfr2, hforall,
      fun res hj => hsim res (hcont res hj)⟩
  | «continue» =>
    obtain ⟨lc, R₂, vals, hlc, hle2, hbelow2, hfr2, hforall, hcont⟩ := ht
    exact ⟨lc, R₂, vals, hlc, hle.trans hle2,
      hbelow.trans (hbelow2.mono hgrow), hfr2, hforall,
      fun res hj => hsim res (hcont res hj)⟩
  | leave =>
    obtain ⟨rs, vals, hrs, hforall, hex⟩ := ht
    exact ⟨rs, vals, hrs, hforall, hsim _ hex⟩

/-- **Scope exit** — the `block` combinator. The construction drops the scope's
own `VMap` entries; the source `restore`s. `EnvOK.restore` matches the two, and
`get_restore_of_noShadow` carries a non-local exit's edge values (read inside
the scope) out through the `restore`. -/
theorem SOut.scope {P : Prog} {f : Func} {lctx : Option LoopCtx}
    {rets : Option (List Ident)} {s₀ s₁ : BState} {R : Regs}
    {renv : Option VMap} {env : VMap} {V Vb : VEnv yulD}
    {yst yst' : EvmState} {o : Outcome}
    (hlen : env.length = V.length) (hns : NoShadow V Vb)
    (hvars : ∀ lc : LoopCtx, lctx = some lc → ∀ x ∈ lc.vars, x ∈ VEnv.names V)
    (hrets : ∀ rs, rets = some rs → ∀ x ∈ rs, x ∈ VEnv.names V)
    (h : SOut (model := model) P f lctx rets s₀ s₁ R renv Vb yst yst' o) :
    SOut (model := model) P f lctx rets s₀ s₁ R
      (renv.map (fun e => e.drop (e.length - env.length)))
      (YulSemantics.restore V Vb) yst yst' o := by
  cases o with
  | normal =>
    obtain ⟨e', R₁, hr, hle, hbelow, hfr, henv', huniq, hsim⟩ := h
    exact ⟨e'.drop (e'.length - env.length), R₁, by rw [hr]; rfl, hle,
      hbelow, hfr,
      henv'.restore hlen, huniq.drop _, hsim⟩
  | halt => exact h
  | «break» =>
    obtain ⟨lc, R₁, vals, hlc, hle, hbelow, hfr, hforall, hcont⟩ := h
    exact ⟨lc, R₁, vals, hlc, hle, hbelow, hfr,
      List.Forall₂.imp_mem hforall (fun x hx v hv => by
        rw [get_restore_of_noShadow hns (hvars lc hlc x hx)]; exact hv), hcont⟩
  | «continue» =>
    obtain ⟨lc, R₁, vals, hlc, hle, hbelow, hfr, hforall, hcont⟩ := h
    exact ⟨lc, R₁, vals, hlc, hle, hbelow, hfr,
      List.Forall₂.imp_mem hforall (fun x hx v hv => by
        rw [get_restore_of_noShadow hns (hvars lc hlc x hx)]; exact hv), hcont⟩
  | leave =>
    obtain ⟨rs, vals, hrs, hforall, hex⟩ := h
    exact ⟨rs, vals, hrs,
      List.Forall₂.imp_mem hforall (fun x hx v hv => by
        rw [get_restore_of_noShadow hns (hrets rs hrs x hx)]; exact hv), hex⟩

/-- **`seqNil`** — the empty live statement list emits nothing. -/
theorem sim_seqNil {P : Prog} {f : Func} {fenv : FMap} {env : VMap} {R : Regs}
    {V : VEnv yulD} {lctx : Option LoopCtx} {rets : Option (List Ident)}
    {s₀ s₁ : BState} {renv : Option VMap} {yst : EvmState}
    (henv : EnvOK (model := model) env V R) (huniq : env.Unique)
    (hfresh : RegsFresh R s₀.fn)
    (htr : trStmts fenv env lctx rets false [] s₀ = some (renv, s₁)) :
    SOut (model := model) P f lctx rets s₀ s₁ R renv V yst yst .normal := by
  rw [trStmts] at htr
  obtain ⟨hrenv, hs₁⟩ := M.pure_inv htr
  subst hs₁
  exact ⟨env, R, by simpa using hrenv, Regs.Le.rfl R, Regs.BelowEq.rfl _ _,
    hfresh, henv, huniq,
    SimS.rfl'⟩

/-- **The edge into a reserved join block.** `cond`'s join, `switch`'s join and
the loop's header/exit/post blocks are all *reserved* (`newBlock`) before the
edges into them are sealed, so the construction never sees their finished
bodies — only their parameter lists. `Completes.params` is exactly the
strengthening that bridges that gap: it fixes the finished block's parameters,
which is what `Exec`'s jump/branch rules need to bind the edge arguments. -/
theorem jumpTo_of_completes {P : Prog} {f : Func} {sRes sCont : BState}
    {bid : BlockId} {b : Block} {vals : List U256} {R : Regs} {st : EvmState}
    {res : FRes} {joins : List BlockId}
    (hcompl : Completes f sRes.fn joins)
    (hres : sRes.fn.blocks[bid]? = some b)
    (hcur : sCont.fn.curId = bid) (hcur0 : sCont.fn.cur = [])
    (hlen : b.params.length = vals.length)
    (hex : ExecFrom (model := model) P f sCont.fn (R.setMany b.params vals) st res) :
    JumpTo (model := model) P f bid vals R st res := by
  obtain ⟨rest, ⟨jb, hjb, hi, ht⟩, hexec⟩ := hex
  rw [hcur] at hjb
  rw [hcur0] at hi
  simp only [List.reverse_nil, List.nil_append] at hi
  obtain ⟨bf, hbf, hbp⟩ := hcompl.params bid b hres
  have heq : jb = bf := (Option.some.inj (hbf.symm.trans hjb)).symm
  rw [heq] at hi ht
  refine ⟨jb, hjb, by rw [heq, hbp]; exact hlen, ?_⟩
  rw [heq, hbp, hi, ht]
  cases rest
  exact hexec

/-! ### Edges into reserved blocks, as `SimS` steps

`cond`, `switch` and the loop family all end a block with an edge into a block
the construction reserved earlier. These three steps are the whole content of
those cases; what is left for the induction shell is the (mechanical) inversion
of the corresponding `trStmt` equation. -/

/-- A fall-through `jump` into a reserved join block. -/
theorem simS_jump_join {P : Prog} {f : Func} {R : Regs} {sEnd s₁ : BState}
    {joinId : BlockId} {xv : List ValId} {vals : List U256} {jb : Block}
    {st : EvmState} {joins : List BlockId}
    (hcompl : Completes f s₁.fn joins)
    (hseal : CurOK f sEnd.fn ⟨[], .jump ⟨joinId, xv⟩⟩)
    (hres : s₁.fn.blocks[joinId]? = some jb)
    (hcur : s₁.fn.curId = joinId) (hcur0 : s₁.fn.cur = [])
    (hg : R.getMany xv = some vals)
    (hlen : jb.params.length = vals.length) :
    SimS (model := model) P f sEnd.fn R st s₁.fn
      (R.setMany jb.params vals) st := by
  intro res hex
  exact execFrom_jump hseal hg
    (jumpTo_of_completes hcompl hres hcur hcur0 hlen hex)

/-- The *false* edge of an `if`: straight to the join, carrying the current
values of the join's variable set. -/
theorem simS_branchFalse_join {P : Prog} {f : Func} {R : Regs} {sA s₁ : BState}
    {cv0 : ValId} {bodyId joinId : BlockId} {xvals : List ValId}
    {vals : List U256} {jb : Block} {st : EvmState} {joins : List BlockId}
    (hcompl : Completes f s₁.fn joins)
    (hbranch : CurOK f sA.fn ⟨[], .branch cv0 ⟨bodyId, []⟩ ⟨joinId, xvals⟩⟩)
    (hc : R cv0 = some 0)
    (hres : s₁.fn.blocks[joinId]? = some jb)
    (hcur : s₁.fn.curId = joinId) (hcur0 : s₁.fn.cur = [])
    (hg : R.getMany xvals = some vals)
    (hlen : jb.params.length = vals.length) :
    SimS (model := model) P f sA.fn R st s₁.fn
      (R.setMany jb.params vals) st := by
  intro res hex
  exact execFrom_branchFalse hbranch hc hg
    (jumpTo_of_completes hcompl hres hcur hcur0 hlen hex)

/-- The *true* edge of an `if`: into the body block, which takes no arguments,
so the register file is unchanged. -/
theorem simS_branchTrue_body {P : Prog} {f : Func} {R : Regs} {sA sB s₁ : BState}
    {cv0 : ValId} {v : U256} {bodyId joinId : BlockId} {xvals : List ValId}
    {bb : Block} {st : EvmState} {joins : List BlockId}
    (hcompl : Completes f s₁.fn joins)
    (hbranch : CurOK f sA.fn ⟨[], .branch cv0 ⟨bodyId, []⟩ ⟨joinId, xvals⟩⟩)
    (hc : R cv0 = some v) (hv : v ≠ 0)
    (hres : s₁.fn.blocks[bodyId]? = some bb) (hbp : bb.params = [])
    (hcur : sB.fn.curId = bodyId) (hcur0 : sB.fn.cur = []) :
    SimS (model := model) P f sA.fn R st sB.fn R st := by
  intro res hex
  refine execFrom_branchTrue (vals := []) hbranch hc hv (by simp) ?_
  refine jumpTo_of_completes hcompl hres hcur hcur0 (by rw [hbp]; simp) ?_
  rw [hbp]
  simpa using hex

/-- The finished function's current block continues where the builder left off.

The *normal* path never needs this — `SimS` is continuation-passing, so it
consumes an `ExecFrom` at the output state and produces one at the input. A
*halting* fragment has no continuation to consume, so it has to exhibit the
block itself; this is that witness. -/
def CurPlaced (f : Func) (fn : FnState) : Prop := ∃ rest, CurOK f fn rest

omit model in
/-- If an empty current block is left by `moveTo`, completion of the moved-to
state places that former current block in the finished function. -/
theorem CurPlaced.of_moveTo_empty {f : Func} {s s' : BState} {bid : BlockId}
    {u : Unit} {joins : List BlockId}
    (hv : s.fn.curId < s.fn.blocks.size) (hcur : s.fn.cur = [])
    (hne : s.fn.curId ≠ bid) (hmv : moveTo bid s = some (u, s'))
    (hprot : s.fn.curId ∉ joins)
    (hcompl : Completes f s'.fn joins) : CurPlaced f s.fn := by
  rw [M.moveTo_apply] at hmv
  obtain ⟨-, rfl⟩ := M.some_pair_inj hmv
  let b := s.fn.blocks[s.fn.curId]
  have hb : s.fn.blocks[s.fn.curId]? = some b :=
    Array.getElem?_eq_getElem hv
  have hf : f.blocks[s.fn.curId]? = some b :=
    hcompl.sealed _ b hprot hne hb
  exact ⟨⟨b.instrs, b.term⟩, b, hf, by rw [hcur]; simp, rfl⟩

omit model in
/-- `CurPlaced` travels backwards along instructions emitted into the same
block. -/
theorem CurPlaced.ofPrefix {f : Func} {fn fn' : FnState} (h : CurPlaced f fn')
    (hc : fn'.curId = fn.curId) (Δ : List Instr) (hcur : fn'.cur = Δ ++ fn.cur) :
    CurPlaced f fn := by
  obtain ⟨rest, b, hb, hi, ht⟩ := h
  refine ⟨⟨Δ.reverse ++ rest.instrs, rest.term⟩, b, by rw [← hc]; exact hb, ?_, ht⟩
  rw [hi, hcur]
  simp

omit model in
/-- A fragment that leaves its incoming block open.  Besides the pending-list
prefix, remember that the reserved block at the current id was not overwritten;
this is what lets an already-sealed predecessor survive the dead-code walk. -/
def CurSame (s s' : BState) : Prop :=
  s'.fn.curId = s.fn.curId
    ∧ (∃ Δ : List Instr, s'.fn.cur = Δ ++ s.fn.cur)
    ∧ ∀ b : Block, s.fn.blocks[s.fn.curId]? = some b →
        s'.fn.blocks[s.fn.curId]? = some b

/-- The incoming block was sealed and the construction moved to another block. -/
def CurMoved (s s' : BState) : Prop :=
  s.fn.curId ≠ s'.fn.curId ∧ ∃ b : Block,
    s'.fn.blocks[s.fn.curId]? = some b
      ∧ ∃ Δ : List Instr, b.instrs = s.fn.cur.reverse ++ Δ

/-- The incoming block was sealed but remains current.  This is the shape of a
bare `break`/`continue`/`leave`/halting expression before an enclosing construct
moves to its join. -/
def CurSealed (s s' : BState) : Prop :=
  s'.fn.curId = s.fn.curId ∧ ∃ b : Block,
    s'.fn.blocks[s.fn.curId]? = some b
      ∧ ∃ Δ : List Instr, b.instrs = s.fn.cur.reverse ++ Δ

/-- A fall-through fragment is either still filling its incoming block or has
sealed it and moved to a fresh continuation. -/
def CurOpen (s s' : BState) : Prop := CurSame s s' ∨ CurMoved s s'

/-- A diverting fragment has sealed its incoming block, with or without a later
move performed by an enclosing structured construct. -/
def CurClosed (s s' : BState) : Prop := CurMoved s s' ∨ CurSealed s s'

/-- The result-sensitive form threaded through the construction induction.
Fall-through must be open; diversion must be closed. -/
def CurResult : Option VMap → BState → BState → Prop
  | some _, s, s' => CurOpen s s'
  | none, s, s' => CurClosed s s'

/-- The builder's current id names a reserved block.  This premise is true at
the top-level entry and is the validity fact that must be threaded through the
mutual construction induction. -/
def CurValid (s : BState) : Prop := s.fn.curId < s.fn.blocks.size

namespace CurValid

omit model in
theorem of_grows {s s' : BState} (hv : CurValid s) (hg : Grows s s') :
    CurValid s' := by
  rw [CurValid, ← hg.curId, ← hg.blocks]
  exact hv

omit model in
theorem of_same_sgrows {N : Nat} {s s' : BState} (hv : CurValid s)
    (hg : SGrowsAt N s s') (hc : s'.fn.curId = s.fn.curId) : CurValid s' := by
  rw [CurValid, hc]
  exact Nat.lt_of_lt_of_le hv hg.size

omit model in
theorem of_moveTo {bid : BlockId} {s s' : BState} {u : Unit}
    (hlt : bid < s.fn.blocks.size) (h : moveTo bid s = some (u, s')) :
    CurValid s' := by
  rw [M.moveTo_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  exact hlt

end CurValid

namespace CurSame

omit model in
theorem rfl' (s : BState) : CurSame s s :=
  ⟨rfl, ⟨[], rfl⟩, fun _ hb => hb⟩

omit model in
theorem of_grows {s s' : BState} (h : Grows s s') : CurSame s s' :=
  ⟨h.curId.symm, h.cur, fun b hb => by rw [← h.blocks]; exact hb⟩

omit model in
theorem of_fnEq {s s' : BState} (h : s'.fn = s.fn) : CurSame s s' := by
  rw [CurSame, h]
  exact ⟨rfl, ⟨[], rfl⟩, fun _ hb => hb⟩

omit model in
theorem trans {s s₁ s₂ : BState} (h₁ : CurSame s s₁) (h₂ : CurSame s₁ s₂) :
    CurSame s s₂ := by
  rcases h₁ with ⟨hc1, ⟨Δ1, hi1⟩, hb1⟩
  rcases h₂ with ⟨hc2, ⟨Δ2, hi2⟩, hb2⟩
  refine ⟨hc2.trans hc1, ⟨Δ2 ++ Δ1, by rw [hi2, hi1, List.append_assoc]⟩,
    fun b hb => ?_⟩
  rw [← hc1]
  exact hb2 b (by simpa only [hc1] using hb1 b hb)

omit model in
theorem of_newBlock {ps : List ValId} {s s' : BState} {bid : BlockId}
    (h : newBlock ps s = some (bid, s')) : CurSame s s' := by
  rw [M.newBlock_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  refine ⟨rfl, ⟨[], rfl⟩, fun b hb => ?_⟩
  have hlt := lt_size_of_getElem? hb
  dsimp only
  rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hlt)]
  exact hb

omit model in
theorem transMoved {s s₁ s₂ : BState} (h₁ : CurSame s s₁)
    (h₂ : CurMoved s₁ s₂) : CurMoved s s₂ := by
  rcases h₁ with ⟨hc1, ⟨Δ1, hi1⟩, -⟩
  rcases h₂ with ⟨hne2, b, hb, Δ2, hi2⟩
  refine ⟨by rw [← hc1]; exact hne2, b, by simpa only [hc1] using hb,
    Δ1.reverse ++ Δ2, ?_⟩
  rw [hi2, hi1]
  simp

omit model in
/-- Backward transfer of current-block placement through builder steps that
leave the current block open. -/
theorem placed_back {f : Func} {s s' : BState} (h : CurSame s s')
    (hp : CurPlaced f s'.fn) : CurPlaced f s.fn := by
  obtain ⟨hc, ⟨Δ, hcur⟩, -⟩ := h
  exact hp.ofPrefix hc Δ hcur

end CurSame

omit model in
theorem curSealed_of_sealCur {t : Term} {s s' : BState} {u : Unit}
    (h : sealCur t s = some (u, s')) : CurSealed s s' := by
  obtain ⟨b, hc, -, hb⟩ := sealCur_cur h
  exact ⟨hc, ⟨b.params, s.fn.cur.reverse, t⟩, by simpa only [hc] using hb,
    [], by simp⟩

omit model in
theorem curMoved_of_seal_move {t : Term} {bid : BlockId} {s sA s' : BState}
    {u v : Unit} (hne : s.fn.curId ≠ bid)
    (hseal : sealCur t s = some (u, sA))
    (hmove : moveTo bid sA = some (v, s')) : CurMoved s s' := by
  obtain ⟨b, hc, -, hb⟩ := sealCur_cur hseal
  rw [M.moveTo_apply] at hmove
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj hmove
  refine ⟨hne, ⟨b.params, s.fn.cur.reverse, t⟩, ?_, [], by simp⟩
  simpa only [hc] using hb

omit model in
/-- **Backward transfer of `CurPlaced`.** The placement of the current block
travels from a fragment's output state to its input state, given the
fragment's `CurResult`.
This is the primitive `seqCons`/`seqStop` need in order to hand their head IH a
`CurPlaced` at the intermediate state: `Completes` already travels backwards
(`SGrowsAt.completes_of`), and this closes the gap for `CurPlaced`. -/
theorem curPlaced_back {f : Func} {s s' : BState} {renv : Option VMap}
    {joins : List BlockId}
    (hk : CurResult renv s s') (hprot : s.fn.curId ∉ joins)
    (hcompl : Completes f s'.fn joins)
    (hfin : renv = none → CurFinal f s'.fn) (hcp : CurPlaced f s'.fn) :
    CurPlaced f s.fn := by
  cases renv with
  | some env =>
    rcases hk with ⟨hc, ⟨Δ, hcur⟩, -⟩ | ⟨hne, b, hb, Δ, hi⟩
    · exact hcp.ofPrefix hc Δ hcur
    · exact ⟨⟨Δ, b.term⟩, b, hcompl.sealed _ b hprot hne hb, hi, rfl⟩
  | none =>
    rcases hk with ⟨hne, b, hb, Δ, hi⟩ | ⟨hc, b, hb, Δ, hi⟩
    · exact ⟨⟨Δ, b.term⟩, b, hcompl.sealed _ b hprot hne hb, hi, rfl⟩
    · have hf : f.blocks[s.fn.curId]? = some b := by
        rw [← hc]
        exact hfin rfl b (by simpa only [hc] using hb)
      exact ⟨⟨Δ, b.term⟩, b, hf, hi, rfl⟩

omit model in
/-- `CurOpen` composes along a chain of fragments. The `SGrowsAt` witnesses
supply the two facts the composition needs: that the block array only grows, and
that a fragment which moves the current block moves it to a *fresh* one — so a
block left behind is never returned to. -/
theorem CurOpen.trans {N : Nat} {s s₁ s₂ : BState}
    (hcur : s.fn.curId < s.fn.blocks.size)
    (hg₁ : SGrowsAt N s s₁) (hg₂ : SGrowsAt s₁.fn.blocks.size s₁ s₂)
    (h₁ : CurOpen s s₁) (h₂ : CurOpen s₁ s₂) : CurOpen s s₂ := by
  rcases h₁ with ⟨hc1, ⟨Δ1, hcur1⟩, hbcur1⟩ | ⟨hne1, b1, hb1, Δ1, hi1⟩
  · rcases h₂ with ⟨hc2, ⟨Δ2, hcur2⟩, hbcur2⟩ | ⟨hne2, b2, hb2, Δ2, hi2⟩
    · exact Or.inl ⟨hc2.trans hc1, ⟨Δ2 ++ Δ1,
        by rw [hcur2, hcur1, List.append_assoc]⟩, fun b hb => by
          rw [← hc1]
          apply hbcur2
          simpa only [hc1] using hbcur1 b hb⟩
    · refine Or.inr ⟨by rw [← hc1]; exact hne2, b2, by rw [← hc1]; exact hb2,
        Δ1.reverse ++ Δ2, ?_⟩
      rw [hi2, hcur1]
      simp
  · have hne2' : s.fn.curId ≠ s₂.fn.curId := by
      rcases hg₂.curId with hc2 | hge2
      · rw [hc2]; exact hne1
      · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le
          (Nat.lt_of_lt_of_le hcur hg₁.size) hge2)
    exact Or.inr ⟨hne2', b1,
      hg₂.keep s.fn.curId b1 (Nat.lt_of_lt_of_le hcur hg₁.size) hne1 hb1, Δ1, hi1⟩

omit model in
/-- An open prefix composes with a diverting suffix. -/
theorem CurOpen.transClosed {N : Nat} {s s₁ s₂ : BState}
  (hcur : s.fn.curId < s.fn.blocks.size)
    (hg₁ : SGrowsAt N s s₁) (hg₂ : SGrowsAt s₁.fn.blocks.size s₁ s₂)
    (h₁ : CurOpen s s₁) (h₂ : CurClosed s₁ s₂) : CurClosed s s₂ := by
  rcases h₂ with hmove | hseal
  · rcases h₁ with ⟨hc1, ⟨Δ1, hcur1⟩, -⟩ | ⟨hne1, b1, hb1, Δ1, hi1⟩
    · rcases hmove with ⟨hne2, b2, hb2, Δ2, hi2⟩
      refine Or.inl ⟨by rw [← hc1]; exact hne2, b2, by simpa only [hc1] using hb2,
        Δ1.reverse ++ Δ2, ?_⟩
      rw [hi2, hcur1]
      simp
    · have hne2' : s.fn.curId ≠ s₂.fn.curId := by
        rcases hg₂.curId with hc2 | hge2
        · rw [hc2]; exact hne1
        · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le
            (Nat.lt_of_lt_of_le hcur hg₁.size) hge2)
      exact Or.inl ⟨hne2', b1,
        hg₂.keep s.fn.curId b1 (Nat.lt_of_lt_of_le hcur hg₁.size) hne1 hb1,
        Δ1, hi1⟩
  rcases h₁ with ⟨hc1, ⟨Δ1, hcur1⟩, -⟩ | ⟨hne1, b1, hb1, Δ1, hi1⟩
  · rcases hseal with ⟨hc2, b2, hb2, Δ2, hi2⟩
    refine Or.inr ⟨hc2.trans hc1, b2, by simpa only [hc1] using hb2,
      Δ1.reverse ++ Δ2, ?_⟩
    rw [hi2, hcur1]
    simp
  · have hne2' : s.fn.curId ≠ s₂.fn.curId := by
      rcases hg₂.curId with hc2 | hge2
      · rw [hc2]; exact hne1
      · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le
          (Nat.lt_of_lt_of_le hcur hg₁.size) hge2)
    exact Or.inl ⟨hne2', b1,
      hg₂.keep s.fn.curId b1 (Nat.lt_of_lt_of_le hcur hg₁.size) hne1 hb1, Δ1, hi1⟩

omit model in
theorem CurOpen.transMoved {N : Nat} {s s₁ s₂ : BState}
    (hcur : CurValid s) (hg₁ : SGrowsAt N s s₁)
    (hg₂ : SGrowsAt s₁.fn.blocks.size s₁ s₂)
    (h₁ : CurOpen s s₁) (h₂ : CurMoved s₁ s₂) : CurMoved s s₂ := by
  rcases h₁ with hs | hm
  · exact hs.transMoved h₂
  · rcases hm with ⟨hne1, b, hb, Δ, hi⟩
    have hne2 : s.fn.curId ≠ s₂.fn.curId := by
      rcases hg₂.curId with hc | hge
      · rw [hc]; exact hne1
      · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le
          (Nat.lt_of_lt_of_le hcur hg₁.size) hge)
    exact ⟨hne2, b,
      hg₂.keep s.fn.curId b (Nat.lt_of_lt_of_le hcur hg₁.size) hne1 hb,
      Δ, hi⟩

omit model in
/-- Dead-code traversal leaves `fn` unchanged, so it preserves a preceding
closed fragment. -/
theorem CurClosed.transSame {N : Nat} {s s₁ s₂ : BState}
    (hcur : s.fn.curId < s.fn.blocks.size)
    (hg₁ : SGrowsAt N s s₁) (hg₂ : SGrowsAt s₁.fn.blocks.size s₁ s₂)
    (h₁ : CurClosed s s₁) (h₂ : CurSame s₁ s₂) : CurClosed s s₂ := by
  rcases h₁ with ⟨hne1, b1, hb1, Δ1, hi1⟩ | ⟨hc1, b1, hb1, Δ1, hi1⟩
  · have hne2 : s.fn.curId ≠ s₂.fn.curId := by rw [h₂.1]; exact hne1
    exact Or.inl ⟨hne2, b1,
      hg₂.keep s.fn.curId b1 (Nat.lt_of_lt_of_le hcur hg₁.size) hne1 hb1, Δ1, hi1⟩
  · exact Or.inr ⟨h₂.1.trans hc1, b1, by
      rw [← hc1]
      exact h₂.2.2 b1 (by simpa only [hc1] using hb1), Δ1, hi1⟩

omit model in
/-- Once the incoming block has been sealed and the builder has moved to a
fresh block, any later statement-level growth preserves that sealed block and
cannot return to its id. -/
theorem CurMoved.forward {s s₁ s₂ : BState}
    (hcur : CurValid s) (_hg₁ : SGrows s s₁)
    (hg₂ : SGrowsAt s.fn.blocks.size s₁ s₂) (hm : CurMoved s s₁) :
    CurMoved s s₂ := by
  rcases hm with ⟨hne1, b, hb, Δ, hi⟩
  have hne2 : s.fn.curId ≠ s₂.fn.curId := by
    rcases hg₂.curId with hc | hge
    · rw [hc]; exact hne1
    · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hcur hge)
  exact ⟨hne2, b,
    hg₂.keep s.fn.curId b hcur hne1 hb, Δ, hi⟩

omit model in
theorem newBlock_size {ps : List ValId} {s s' : BState} {bid : BlockId}
    (h : newBlock ps s = some (bid, s')) :
    s'.fn.blocks.size = s.fn.blocks.size + 1 := by
  rw [M.newBlock_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  simp

omit model in
theorem newBlock_target_lt {ps : List ValId} {s s' : BState} {bid : BlockId}
    (h : newBlock ps s = some (bid, s')) : bid < s'.fn.blocks.size := by
  rw [SGrowsAt.newBlock_id h, newBlock_size h]
  exact Nat.lt_succ_self _

omit model in
/-- The block just reserved by `newBlock` is present with exactly the supplied
parameter list. -/
theorem newBlock_target_get {ps : List ValId} {s s' : BState} {bid : BlockId}
    (h : newBlock ps s = some (bid, s')) :
    s'.fn.blocks[bid]? = some ⟨ps, [], .ret []⟩ := by
  rw [M.newBlock_apply] at h
  obtain ⟨rfl, rfl⟩ := M.some_pair_inj h
  simp

/-! ### Current-block validity and shape of the mutual translation -/

def ScopeCur (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (body : List (Stmt Op)) : Prop :=
  ∀ (s : BState) (r : Option VMap) (s' : BState), CurValid s →
    trScope fenv env lctx rets body s = some (r, s') →
      CurValid s' ∧ CurResult r s s'

def StmtsCur (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (d : Bool) (ss : List (Stmt Op)) : Prop :=
  if d then True else
    ∀ (s : BState) (r : Option VMap) (s' : BState), CurValid s →
      trStmts fenv env lctx rets d ss s = some (r, s') →
        CurValid s' ∧ CurResult r s s'

def StmtCur (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (st : Stmt Op) : Prop :=
  ∀ (s : BState) (r : Option VMap) (s' : BState), CurValid s →
    trStmt fenv env lctx rets st s = some (r, s') →
      CurValid s' ∧ CurResult r s s'

def CasesCur (fenv : FMap) (env : VMap) (lctx : Option LoopCtx)
    (rets : Option (List Ident)) (_sv : ValId) (_X : List Ident)
    (_joinId : BlockId) (cases : List (Literal × List (Stmt Op)))
    (dflt : Option (List (Stmt Op))) : Prop :=
  ∀ (sv : ValId) (X : List Ident) (joinId : BlockId) (s : BState) (u : Unit)
    (s' : BState), CurValid s →
    trCases fenv env lctx rets sv X joinId cases dflt s = some (u, s') →
      CurValid s' ∧ CurClosed s s'

end Semantics
end YulEvmCompiler.SsaCfg
