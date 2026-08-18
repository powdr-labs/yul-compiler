import YulEvmCompiler.SsaCfg.Implementation.OfYulSound.Monotonicity
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.OfYulSound.Leaves

Dialect facts and the simulation leaves.

`yulD` unfolding lemmas, the `CurOK`/`ExecFrom`/`SimS`/`JumpTo` shapes, one
`SimS` step per emitted instruction and per terminator, the `RegsFresh`
invariant, and the expression-class leaves (`sim_lit`, `sim_var`,
`sim_args_*`).
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics (Ident Literal Expr Stmt VEnv Outcome)
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal evmWithExternal)

section Semantics
variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates YulSemantics.EVM.ExternalGas.any

/-! ## Dialect facts the construction relies on -/

/-- The dialect zero is the machine zero (so `bindZeros` matches `const _ 0`). -/
theorem yulD_zero : YulSemantics.Dialect.zero yulD = (0 : U256) := rfl

set_option linter.unnecessarySeqFocus false in
/-- `isHaltingOp` is sound: the operations the construction turns into a
`Term.halt` really do always halt, so sealing the block with them loses no
behavior. This is the fact that makes `trStmt`'s `exprStmt` case correct. -/
theorem isHaltingOp_halts {op : Op} (hop : isHaltingOp op = true)
    {args : List U256} {st : EvmState} {r : YulSemantics.BuiltinResult U256 EvmState}
    (hb : builtinWithExternal model.calls model.creates .any op args st r) :
    ∃ st', r = .halt st' := by
  -- the five halting ops are outside the CALL/CREATE/GAS families, so the
  -- open-world relation is `stepOp`, whose result for them is always a `.halt`
  have hop' : op = .stop ∨ op = .ret ∨ op = .revert ∨ op = .invalid
      ∨ op = .selfdestruct := by
    cases op <;> simp_all [isHaltingOp]
  have hstep : YulSemantics.EVM.stepOp op args st = some r := by
    rcases hop' with rfl | rfl | rfl | rfl | rfl <;> exact hb
  rcases hop' with rfl | rfl | rfl | rfl | rfl
  · rcases args with _ | ⟨a, l⟩ <;>
      simp_all [YulSemantics.EVM.stepOp] <;> exact ⟨_, hstep.symm⟩
  · rcases args with _ | ⟨a, _ | ⟨b, _ | l⟩⟩ <;>
      simp_all [YulSemantics.EVM.stepOp] <;> exact ⟨_, hstep.symm⟩
  · rcases args with _ | ⟨a, _ | ⟨b, _ | l⟩⟩ <;>
      simp_all [YulSemantics.EVM.stepOp] <;> exact ⟨_, hstep.symm⟩
  · rcases args with _ | ⟨a, l⟩ <;>
      simp_all [YulSemantics.EVM.stepOp] <;> exact ⟨_, hstep.symm⟩
  · rcases args with _ | ⟨a, _ | l⟩ <;>
      simp_all [YulSemantics.EVM.stepOp, YulSemantics.EVM.guardStatic] <;>
      by_cases hs : st.env.static <;> simp_all <;> exact ⟨_, hstep.symm⟩

/-- The `eq` test the switch chain emits. -/
theorem builtin_eq (a b : U256) (st : EvmState) :
    builtinWithExternal model.calls model.creates .any .eq [a, b] st
      (.ok [YulSemantics.EVM.b2w (a = b)] st) := rfl

/-! ## The simulation shapes

The construction fills one basic block at a time, so a fragment's meaning is
*continuation-passing*: "whatever the rest of the finished block does from the
second configuration, it also does from the first". That is the SSA analogue of
`SimAsm`'s `ASimS`, with `FnState` in place of a list position. -/

/-- `CurOK f fn rest`: in the finished function `f`, the block the builder is
currently filling continues with `rest` after the instructions it has already
emitted (`fn.cur`, reversed). -/
def CurOK (f : Func) (fn : FnState) (rest : Rest) : Prop :=
  ∃ b, f.blocks[fn.curId]? = some b
    ∧ b.instrs = fn.cur.reverse ++ rest.instrs ∧ b.term = rest.term

omit model in
/-- Exact backward transport of a finished current block when builder-only
steps changed neither its id nor its pending instruction list. -/
theorem CurOK.back_of_cur_eq {f : Func} {fn fn' : FnState} {rest : Rest}
    (hid : fn'.curId = fn.curId) (hcur : fn'.cur = fn.cur)
    (h : CurOK f fn' rest) : CurOK f fn rest := by
  obtain ⟨b, hb, hi, ht⟩ := h
  exact ⟨b, by simpa only [hid] using hb, by simpa only [hcur] using hi, ht⟩

/-- Execution of the rest of the block the builder is currently filling. -/
def ExecFrom (P : Prog) (f : Func) (fn : FnState) (R : Regs) (st : EvmState)
    (res : FRes) : Prop :=
  ∃ rest, CurOK f fn rest ∧ Exec (model := model) P f R st rest res

/-- `SimS`: the fragment the builder laid down between `fn₀` and `fn₁` carries
⟨`R₀`, `st`⟩ to ⟨`R₁`, `st'`⟩ — every continuation of the second configuration
is realized from the first. -/
def SimS (P : Prog) (f : Func) (fn₀ : FnState) (R₀ : Regs) (st : EvmState)
    (fn₁ : FnState) (R₁ : Regs) (st' : EvmState) : Prop :=
  ∀ res, ExecFrom (model := model) P f fn₁ R₁ st' res
    → ExecFrom (model := model) P f fn₀ R₀ st res

/-- Taking a control-flow edge to `bid` that carries `vals`. -/
def JumpTo (P : Prog) (f : Func) (bid : BlockId) (vals : List U256) (R : Regs)
    (st : EvmState) (res : FRes) : Prop :=
  ∃ tb, f.blocks[bid]? = some tb ∧ tb.params.length = vals.length
    ∧ Exec (model := model) P f (R.setMany tb.params vals) st
        ⟨tb.instrs, tb.term⟩ res

/-- SSA execution is monotone in already-defined registers.  The generated
code only reads registers and applies the same bindings on both sides, so
extra bindings cannot invalidate an execution.  Loop iterations use this to
re-enter a statically shared header with the register facts accumulated by the
previous iteration. -/
theorem Exec.mono {P : Prog} {f : Func} {R R' : Regs} {st : EvmState}
    {rest : Rest} {res : FRes} (hle : Regs.Le R R')
    (h : Exec (model := model) P f R st rest res) :
    Exec (model := model) P f R' st rest res := by
  induction h generalizing R' with
  | const h ih =>
    exact .const (ih (hle.setBoth _ _))
  | op hargs hb hlen hrest ih =>
    exact .op (Regs.getMany_mono hle hargs) hb hlen
      (ih (hle.setManyBoth))
  | opHalt hargs hb =>
    exact .opHalt (Regs.getMany_mono hle hargs) hb
  | call hg hargs hparams heb hbody hlen hrest _ihbody ihrest =>
    exact .call hg (Regs.getMany_mono hle hargs) hparams heb hbody hlen
      (ihrest hle.setManyBoth)
  | callHalt hg hargs hparams heb hbody =>
    exact .callHalt hg (Regs.getMany_mono hle hargs) hparams heb hbody
  | jump htarget hargs hlen hbody ih =>
    exact .jump htarget (Regs.getMany_mono hle hargs) hlen
      (ih hle.setManyBoth)
  | branchTrue hc hnz htarget hargs hlen hbody ih =>
    exact .branchTrue (hle _ _ hc) hnz htarget
      (Regs.getMany_mono hle hargs) hlen (ih hle.setManyBoth)
  | branchFalse hc htarget hargs hlen hbody ih =>
    exact .branchFalse (hle _ _ hc) htarget
      (Regs.getMany_mono hle hargs) hlen (ih hle.setManyBoth)
  | ret hvals => exact .ret (Regs.getMany_mono hle hvals)
  | halt hargs hb => exact .halt (Regs.getMany_mono hle hargs) hb

theorem ExecFrom.mono {P : Prog} {f : Func} {fn : FnState} {R R' : Regs}
    {st : EvmState} {res : FRes} (hle : Regs.Le R R')
    (h : ExecFrom (model := model) P f fn R st res) :
    ExecFrom (model := model) P f fn R' st res := by
  obtain ⟨rest, hcur, hex⟩ := h
  exact ⟨rest, hcur, hex.mono hle⟩

namespace SimS

theorem rfl' {P : Prog} {f : Func} {fn : FnState} {R : Regs} {st : EvmState} :
    SimS (model := model) P f fn R st fn R st := fun _ h => h

theorem trans {P : Prog} {f : Func} {fn₀ fn₁ fn₂ : FnState} {R₀ R₁ R₂ : Regs}
    {st₀ st₁ st₂ : EvmState}
    (h₁ : SimS (model := model) P f fn₀ R₀ st₀ fn₁ R₁ st₁)
    (h₂ : SimS (model := model) P f fn₁ R₁ st₁ fn₂ R₂ st₂) :
    SimS (model := model) P f fn₀ R₀ st₀ fn₂ R₂ st₂ :=
  fun res h => h₁ res (h₂ res h)

end SimS

/-! ### Leaves: prepending an emitted instruction

Each `emit` in the construction is one of these three steps. They are the only
place `Exec`'s instruction rules are used, and they are unconditional. -/

/-- `emit (.const d v)`. -/
theorem simS_const {P : Prog} {f : Func} {fn fn' : FnState} {R : Regs}
    {st : EvmState} {d : ValId} {v : U256}
    (hc : fn'.curId = fn.curId) (hcur : fn'.cur = .const d v :: fn.cur) :
    SimS (model := model) P f fn R st fn' (R.set d v) st := by
  intro res h
  obtain ⟨rest, ⟨b, hb, hinstrs, hterm⟩, hexec⟩ := h
  rw [hc] at hb
  rw [hcur] at hinstrs
  refine ⟨⟨.const d v :: rest.instrs, rest.term⟩, ⟨b, hb, ?_, hterm⟩, .const hexec⟩
  simpa using hinstrs

/-- `emit (.op ds yop as)` on the returning path. -/
theorem simS_op {P : Prog} {f : Func} {fn : FnState} {R : Regs}
    {st st' : EvmState} {ds : List ValId} {yop : Op} {as : List ValId}
    {args rets : List U256}
    (hargs : R.getMany as = some args)
    (hb : builtinWithExternal model.calls model.creates .any yop args st (.ok rets st'))
    (hlen : ds.length = rets.length)
    {fn' : FnState} (hc : fn'.curId = fn.curId)
    (hcur : fn'.cur = .op ds yop as :: fn.cur) :
    SimS (model := model) P f fn R st fn' (R.setMany ds rets) st' := by
  intro res h
  obtain ⟨rest, ⟨b, hbl, hinstrs, hterm⟩, hexec⟩ := h
  rw [hc] at hbl
  rw [hcur] at hinstrs
  refine ⟨⟨.op ds yop as :: rest.instrs, rest.term⟩, ⟨b, hbl, ?_, hterm⟩,
    .op hargs hb hlen hexec⟩
  simpa using hinstrs

/-- `emit (.op ds yop as)` where the built-in halts. -/
theorem execFrom_opHalt {P : Prog} {f : Func} {fn : FnState} {R : Regs}
    {st st' : EvmState} {ds : List ValId} {yop : Op} {as : List ValId}
    {args : List U256} {rest : Rest}
    (hcur : CurOK f { fn with cur := .op ds yop as :: fn.cur } rest)
    (hargs : R.getMany as = some args)
    (hb : builtinWithExternal model.calls model.creates .any yop args st (.halt st')) :
    ExecFrom (model := model) P f fn R st (.halt st') := by
  obtain ⟨b, hbl, hinstrs, hterm⟩ := hcur
  exact ⟨⟨.op ds yop as :: rest.instrs, rest.term⟩, ⟨b, hbl, by simpa using hinstrs, hterm⟩,
    .opHalt hargs hb⟩

/-- `emit (.call ds fid as)` on the returning path. -/
theorem simS_call {P : Prog} {f g : Func} {fn : FnState} {R : Regs}
    {st st' : EvmState} {ds as : List ValId} {fid : FuncId}
    {args rvals : List U256} {eb : Block}
    (hg : P.funcs[fid]? = some g)
    (hargs : R.getMany as = some args)
    (hparams : g.params.length = args.length)
    (heb : g.blocks[g.entry]? = some eb)
    (hbody : Exec (model := model) P g (Regs.empty.setMany g.params args) st
      ⟨eb.instrs, eb.term⟩ (.ret rvals st'))
    (hlen : ds.length = rvals.length)
    {fn' : FnState} (hc : fn'.curId = fn.curId)
    (hcur : fn'.cur = .call ds fid as :: fn.cur) :
    SimS (model := model) P f fn R st fn' (R.setMany ds rvals) st' := by
  intro res h
  obtain ⟨rest, ⟨b, hbl, hinstrs, hterm⟩, hexec⟩ := h
  rw [hc] at hbl
  rw [hcur] at hinstrs
  refine ⟨⟨.call ds fid as :: rest.instrs, rest.term⟩, ⟨b, hbl, ?_, hterm⟩,
    .call hg hargs hparams heb hbody hlen hexec⟩
  simpa using hinstrs

/-- `emit (.call ds fid as)` where the callee halts. -/
theorem execFrom_callHalt {P : Prog} {f g : Func} {fn : FnState} {R : Regs}
    {st st' : EvmState} {ds as : List ValId} {fid : FuncId} {args : List U256}
    {eb : Block} {rest : Rest}
    (hcur : CurOK f { fn with cur := .call ds fid as :: fn.cur } rest)
    (hg : P.funcs[fid]? = some g)
    (hargs : R.getMany as = some args)
    (hparams : g.params.length = args.length)
    (heb : g.blocks[g.entry]? = some eb)
    (hbody : Exec (model := model) P g (Regs.empty.setMany g.params args) st
      ⟨eb.instrs, eb.term⟩ (.halt st')) :
    ExecFrom (model := model) P f fn R st (.halt st') := by
  obtain ⟨b, hbl, hinstrs, hterm⟩ := hcur
  exact ⟨⟨.call ds fid as :: rest.instrs, rest.term⟩,
    ⟨b, hbl, by simpa using hinstrs, hterm⟩, .callHalt hg hargs hparams heb hbody⟩

/-- No instructions emitted. -/
theorem simS_id {P : Prog} {f : Func} {fn fn' : FnState} {R : Regs}
    {st : EvmState} (hc : fn'.curId = fn.curId) (hcur : fn'.cur = fn.cur) :
    SimS (model := model) P f fn R st fn' R st := by
  intro res h
  obtain ⟨rest, ⟨b, hb, hinstrs, hterm⟩, hexec⟩ := h
  rw [hc] at hb
  rw [hcur] at hinstrs
  exact ⟨rest, ⟨b, hb, hinstrs, hterm⟩, hexec⟩

/-- A whole block of zero-initialising `const`s — `let x` without a value, and
`trFunc`'s return variables. -/
theorem simS_consts {P : Prog} {f : Func} {st : EvmState} :
    ∀ (ids : List ValId) (R : Regs) (fn fn' : FnState), fn'.curId = fn.curId →
      fn'.cur = (ids.map (fun v => Instr.const v 0)).reverse ++ fn.cur →
      SimS (model := model) P f fn R st fn'
        (R.setMany ids (List.replicate ids.length 0)) st := by
  intro ids
  induction ids with
  | nil => intro R fn fn' hc hcur; simpa using simS_id hc (by simpa using hcur)
  | cons v ids ih =>
    intro R fn fn' hc hcur
    have hstep : SimS (model := model) P f fn R st
        { fn with cur := .const v 0 :: fn.cur } (R.set v 0) st :=
      simS_const rfl rfl
    have htail := ih (R.set v 0) { fn with cur := .const v 0 :: fn.cur } fn' hc (by
      rw [hcur]; simp)
    rw [List.length_cons, List.replicate_succ, Regs.setMany_cons]
    exact hstep.trans htail

/-! ### Leaves: the terminators the construction seals with -/

/-- A block sealed with `ret xs` returns. -/
theorem execFrom_ret {P : Prog} {f : Func} {fn : FnState} {R : Regs}
    {st : EvmState} {xs : List ValId} {vals : List U256}
    (hcur : CurOK f fn ⟨[], .ret xs⟩) (hg : R.getMany xs = some vals) :
    ExecFrom (model := model) P f fn R st (.ret vals st) :=
  ⟨⟨[], .ret xs⟩, hcur, .ret hg⟩

/-- A block sealed with `halt yop as` halts. -/
theorem execFrom_halt {P : Prog} {f : Func} {fn : FnState} {R : Regs}
    {st st' : EvmState} {yop : Op} {as : List ValId} {args : List U256}
    (hcur : CurOK f fn ⟨[], .halt yop as⟩) (hg : R.getMany as = some args)
    (hb : builtinWithExternal model.calls model.creates .any yop args st (.halt st')) :
    ExecFrom (model := model) P f fn R st (.halt st') :=
  ⟨⟨[], .halt yop as⟩, hcur, .halt hg hb⟩

/-- A block sealed with `jump e` transfers along `e`. -/
theorem execFrom_jump {P : Prog} {f : Func} {fn : FnState} {R : Regs}
    {st : EvmState} {e : Edge} {vals : List U256} {res : FRes}
    (hcur : CurOK f fn ⟨[], .jump e⟩) (hg : R.getMany e.args = some vals)
    (hjmp : JumpTo (model := model) P f e.target vals R st res) :
    ExecFrom (model := model) P f fn R st res := by
  obtain ⟨tb, htb, hlen, hexec⟩ := hjmp
  exact ⟨⟨[], .jump e⟩, hcur, .jump htb hg hlen hexec⟩

/-- A block sealed with `branch c t f`, true edge. -/
theorem execFrom_branchTrue {P : Prog} {f : Func} {fn : FnState} {R : Regs}
    {st : EvmState} {c : ValId} {v : U256} {et ef : Edge} {vals : List U256}
    {res : FRes} (hcur : CurOK f fn ⟨[], .branch c et ef⟩)
    (hc : R c = some v) (hnz : v ≠ 0)
    (hg : R.getMany et.args = some vals)
    (hjmp : JumpTo (model := model) P f et.target vals R st res) :
    ExecFrom (model := model) P f fn R st res := by
  obtain ⟨tb, htb, hlen, hexec⟩ := hjmp
  exact ⟨⟨[], .branch c et ef⟩, hcur, .branchTrue hc hnz htb hg hlen hexec⟩

/-- A block sealed with `branch c t f`, false edge. -/
theorem execFrom_branchFalse {P : Prog} {f : Func} {fn : FnState} {R : Regs}
    {st : EvmState} {c : ValId} {et ef : Edge} {vals : List U256} {res : FRes}
    (hcur : CurOK f fn ⟨[], .branch c et ef⟩) (hc : R c = some 0)
    (hg : R.getMany ef.args = some vals)
    (hjmp : JumpTo (model := model) P f ef.target vals R st res) :
    ExecFrom (model := model) P f fn R st res := by
  obtain ⟨tb, htb, hlen, hexec⟩ := hjmp
  exact ⟨⟨[], .branch c et ef⟩, hcur, .branchFalse hc htb hg hlen hexec⟩

/-! ### The freshness invariant

The register file only ever binds ids the builder has already handed out. This
is what makes `Regs.Le` available at every `freshVal`: the id just allocated is
provably unbound, so binding it *extends* the register file and every earlier
fact survives (`EnvOK.mono`). -/

/-- `R` binds nothing the builder has not yet allocated. -/
def RegsFresh (R : Regs) (fn : FnState) : Prop :=
  ∀ i : ValId, fn.nextVal ≤ i → R i = none

namespace RegsFresh

omit model in
theorem mono {R : Regs} {fn fn' : FnState} (h : RegsFresh R fn)
    (hle : fn.nextVal ≤ fn'.nextVal) : RegsFresh R fn' :=
  fun i hi => h i (Nat.le_trans hle hi)

omit model in
/-- The id `freshVal` is about to hand out is unbound. -/
theorem unbound {R : Regs} {fn : FnState} (h : RegsFresh R fn) :
    R fn.nextVal = none := h _ (Nat.le_refl _)

omit model in
theorem set {R : Regs} {fn fn' : FnState} (h : RegsFresh R fn) (v : U256)
    (hnv : fn.nextVal + 1 ≤ fn'.nextVal) :
    RegsFresh (R.set fn.nextVal v) fn' := by
  intro i hi
  have hlt : fn.nextVal < i := Nat.lt_of_lt_of_le hnv hi
  rw [Regs.set_other R v (Nat.ne_of_gt hlt)]
  exact h i (Nat.le_of_lt hlt)

omit model in
/-- A whole `mapM freshVal` block of ids. -/
theorem setMany {R : Regs} {fn fn' : FnState} (h : RegsFresh R fn) {n : Nat}
    {vs : List U256} (hnv : fn.nextVal + n ≤ fn'.nextVal) :
    RegsFresh (R.setMany (List.range' fn.nextVal n) vs) fn' := by
  intro i hi
  have hchain : fn.nextVal + n ≤ i := Nat.le_trans hnv hi
  have hnm : i ∉ List.range' fn.nextVal n := by
    intro hmem
    obtain ⟨-, hb2⟩ := M.mem_range'_bounds hmem
    exact absurd (Nat.lt_of_lt_of_le hb2 hchain) (Nat.lt_irrefl i)
  rw [Regs.setMany_other hnm]
  exact h i (Nat.le_trans (Nat.le_add_right _ n) hchain)

end RegsFresh

/-! ### Expression-class simulation

The motive the `.expr` / `.args` cases of the main induction carry: the fragment
the construction laid down transports the machine state, defines the
expression's `ValId`, and *extends* the register file (single assignment). -/

/-- One expression: `i` holds `v` in the extended register file. -/
def EOut (P : Prog) (f : Func) (s₀ s₁ : BState) (R₀ : Regs) (i : ValId)
    (v : U256) (yst yst' : EvmState) : Prop :=
  ∃ R₁ : Regs, Regs.Le R₀ R₁ ∧ Regs.BelowEq s₀.fn.nextVal R₀ R₁
    ∧ RegsFresh R₁ s₁.fn ∧ R₁ i = some v
    ∧ SimS (model := model) P f s₀.fn R₀ yst s₁.fn R₁ yst'

/-- An argument list: the ids read back as the value list, in source order. -/
def EOutL (P : Prog) (f : Func) (s₀ s₁ : BState) (R₀ : Regs)
    (ids : List ValId) (vs : List U256) (yst yst' : EvmState) : Prop :=
  ∃ R₁ : Regs, Regs.Le R₀ R₁ ∧ Regs.BelowEq s₀.fn.nextVal R₀ R₁
    ∧ RegsFresh R₁ s₁.fn ∧ R₁.getMany ids = some vs
    ∧ SimS (model := model) P f s₀.fn R₀ yst s₁.fn R₁ yst'

/-- **`lit`** — the construction emits a `const`; the source rule leaves the
machine state alone. -/
theorem sim_lit {P : Prog} {f : Func} {fenv : FMap} {env : VMap} {R : Regs}
    {l : Literal} {s₀ s₁ : BState} {i : ValId} {yst : EvmState}
    (hfresh : RegsFresh R s₀.fn)
    (htr : trExpr fenv env (.lit l) s₀ = some (i, s₁)) :
    EOut (model := model) P f s₀ s₁ R i (YulSemantics.EVM.litValue l) yst yst := by
  rw [trExpr] at htr
  obtain ⟨w, sA, h1, htr⟩ := M.bind_inv htr
  obtain ⟨u, sB, h2, h3⟩ := M.bind_inv htr
  rw [M.freshVal_apply] at h1
  obtain ⟨hw, hsA⟩ := M.some_pair_inj h1
  subst hw
  subst hsA
  rw [M.emit_apply] at h2
  obtain ⟨-, hsB⟩ := M.some_pair_inj h2
  subst hsB
  obtain ⟨hi, hs₁⟩ := M.pure_inv h3
  subst hi
  subst hs₁
  exact ⟨R.set s₀.fn.nextVal (YulSemantics.EVM.litValue l),
    Regs.Le.set _ hfresh.unbound, Regs.BelowEq.set _ (Nat.le_refl _),
    hfresh.set _ (Nat.le_refl _),
    Regs.set_same .., simS_const rfl rfl⟩

/-- **`var`** — the construction resolves the name in its `VMap`; `EnvOK` says
the id it finds holds the value the source environment records. -/
theorem sim_var {P : Prog} {f : Func} {fenv : FMap} {env : VMap} {R : Regs}
    {V : VEnv yulD} {x : Ident} {v : U256} {s₀ s₁ : BState} {i : ValId}
    {yst : EvmState}
    (hfresh : RegsFresh R s₀.fn) (henv : EnvOK (model := model) env V R)
    (hget : YulSemantics.VEnv.get V x = some v)
    (htr : trExpr fenv env (.var x) s₀ = some (i, s₁)) :
    EOut (model := model) P f s₀ s₁ R i v yst yst := by
  rw [trExpr] at htr
  obtain ⟨hlk, hs₁⟩ := M.liftO_inv htr
  obtain ⟨j, hj, hRj⟩ := henv.get_rev hget
  obtain rfl : i = j := Option.some.inj (hlk.symm.trans hj)
  subst hs₁
  exact ⟨R, Regs.Le.rfl R, Regs.BelowEq.rfl _ _, hfresh, hRj, SimS.rfl'⟩

/-- **`args []`** — nothing emitted. -/
theorem sim_args_nil {P : Prog} {f : Func} {fenv : FMap} {env : VMap} {R : Regs}
    {s₀ s₁ : BState} {ids : List ValId} {yst : EvmState}
    (hfresh : RegsFresh R s₀.fn)
    (htr : trArgs fenv env [] s₀ = some (ids, s₁)) :
    EOutL (model := model) P f s₀ s₁ R ids [] yst yst := by
  rw [trArgs] at htr
  obtain ⟨hids, hs₁⟩ := M.pure_inv htr
  subst hs₁; subst hids
  exact ⟨R, Regs.Le.rfl R, Regs.BelowEq.rfl _ _, hfresh, rfl, SimS.rfl'⟩

/-- **`args (e :: rest)`** — the construction translates `rest` first, matching
the source's right-to-left evaluation order; the two fragments compose and the
earlier ids survive because the register file only extends. -/
theorem sim_args_cons {P : Prog} {f : Func} {s₀ sA s₁ : BState} {R : Regs}
    {restIds : List ValId} {i : ValId} {restvals : List U256} {v : U256}
    {yst yst1 yst2 : EvmState}
    (hrest : EOutL (model := model) P f s₀ sA R restIds restvals yst yst1)
    (hgrow : s₀.fn.nextVal ≤ sA.fn.nextVal)
    (hhead : ∀ R', Regs.Le R R' → RegsFresh R' sA.fn →
      EOut (model := model) P f sA s₁ R' i v yst1 yst2) :
    EOutL (model := model) P f s₀ s₁ R (i :: restIds) (v :: restvals) yst yst2 := by
  obtain ⟨Ra, hle, hbelow, hfr, hget, hsim⟩ := hrest
  obtain ⟨Rb, hle2, hbelow2, hfr2, hi, hsim2⟩ := hhead Ra hle hfr
  refine ⟨Rb, hle.trans hle2,
    hbelow.trans (hbelow2.mono hgrow), hfr2, ?_, hsim.trans hsim2⟩
  rw [Regs.getMany_cons, hi, Regs.getMany_mono hle2 hget]
  simp

end Semantics
end YulEvmCompiler.SsaCfg
