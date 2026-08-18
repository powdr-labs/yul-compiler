import YulEvmCompiler.SsaCfg.Implementation.PassesSound.ElimParams
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.PassesSound.ConstFold

Pass 2 soundness: constant folding.

The `ConstRegs` execution invariant — every value a `ConstDef` certificate
names really holds that constant at runtime — and `constFold_sound`.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal stepOp ExternalCalls
  ExternalCreates)
open YulSemantics (Outcome)
variable [model : ExternalModel]

/-! ### Constant-folding execution invariant -/

omit model in
theorem wfCheck_defs_nodup {f : Func} {n : Nat} (h : f.wfCheck n = true) :
    f.allDefs.Nodup := by
  unfold Func.wfCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

omit model in
theorem wfCheck_op_arity {f : Func} {n : Nat} (h : f.wfCheck n = true)
    {b : Block} (hb : b ∈ f.blocks.toList) {ds : List ValId} {yop : Op} {as : List ValId}
    (hi : .op ds yop as ∈ b.instrs) : ds.length ≤ 1 := by
  unfold Func.wfCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have hb' : b ∈ f.blocks := by simpa using hb
  have hblock := Array.all_eq_true_iff_forall_mem.mp h.2 b hb'
  simp only [Bool.and_eq_true] at hblock
  have hins := List.all_eq_true.mp hblock.2 (Instr.op ds yop as) hi
  simpa using hins

/-- Register consistency consumes the static certificates constructed by the
folder. -/
def ConstRegs (f : Func) (R : Regs) : Prop :=
  ∀ {d v w}, Passes.ConstDef f d v → R d = some w → w = v

omit model in
theorem constRegs_entry {f : Func} (hnd : f.allDefs.Nodup) (args : List U256) :
    ConstRegs f (Regs.empty.setMany f.params args) := by
  intro d v w hc hr
  obtain ⟨b, hb, i, hi, hd⟩ := hc.site
  have hnot : d ∉ f.params := by
    intro hp
    exact funcParam_not_instr_def hnd hb hi hp hd
  rw [Regs.setMany_of_not_mem _ f.params args hnot] at hr
  simp [Regs.empty] at hr

omit model in
theorem constRegs_setMany_params {f : Func} (hnd : f.allDefs.Nodup)
    {R : Regs} (hR : ConstRegs f R) {b : Block} (hb : b ∈ f.blocks.toList)
    (vs : List U256) : ConstRegs f (R.setMany b.params vs) := by
  intro d v w hc hr
  obtain ⟨b', hb', i, hi, hd⟩ := hc.site
  have hnot : d ∉ b.params := by
    intro hp
    exact param_not_instr_def hnd hb hb' hi hp hd
  rw [Regs.setMany_of_not_mem _ b.params vs hnot] at hr
  exact hR hc hr

/-- The exact rewrite of an arbitrary instruction suffix and its terminator. -/
def Passes.cfRest (is : List Instr) (t : Term) (m : Std.HashMap ValId U256) : Rest :=
  let r := is.foldl (fun s i => Passes.cfInstrStep i s) ⟨m, []⟩
  ⟨r.2.reverse, Passes.cfTerm { params := [], instrs := is, term := t } r.1⟩

omit model in
theorem Passes.cfRest_cons (i : Instr) (is : List Instr) (t : Term)
    (m : Std.HashMap ValId U256) :
    cfRest (i :: is) t m =
      ⟨cfInstrOut i m :: (cfRest is t (cfInstrMap i m)).instrs,
        (cfRest is t (cfInstrMap i m)).term⟩ := by
  simp only [cfRest]
  rw [cfInstr_fold_cons, cfInstr_foldMap_cons]
  cases t <;> rfl

omit model in
theorem Passes.cfRest_nil (t : Term) (m : Std.HashMap ValId U256) :
    cfRest [] t m = ⟨[], cfTerm { params := [], instrs := [], term := t } m⟩ := rfl

omit model in
theorem Passes.cfBlockOut_rest (b : Block) (m : Std.HashMap ValId U256) :
    Rest.mk (cfBlockOut b m).instrs (cfBlockOut b m).term = cfRest b.instrs b.term m := by
  rfl

omit model in
/-- A certified destination's unique instruction site determines which kind of
certificate it carries. -/
theorem constDef_instr_cases {f : Func} (hnd : f.allDefs.Nodup)
    {b : Block} (hb : b ∈ f.blocks.toList) {i : Instr} (hi : i ∈ b.instrs)
    {d : ValId} (hd : d ∈ i.defs) {v : U256} (hc : Passes.ConstDef f d v) :
    i = .const d v ∨
      ∃ yop as vs, i = .op [d] yop as ∧ Passes.pureOp yop = true ∧
        YulSemantics.Forall₂ (Passes.ConstDef f) as vs ∧ Passes.evalPure yop vs = some v := by
  cases hc with
  | @const b' _ _ hb' hi' =>
    have heq := instr_def_unique hnd hb hb' hi hi' hd (by simp [Instr.defs])
    exact Or.inl heq
  | @op b' _ yop as vs _ hb' hi' hp hvs he =>
    have heq := instr_def_unique hnd hb hb' hi hi' hd (by simp [Instr.defs])
    exact Or.inr ⟨yop, as, vs, heq, hp, hvs, he⟩

omit model in
theorem constRegs_getMany {f : Func} {R : Regs} (hR : ConstRegs f R)
    {as : List ValId} {vs args : List U256}
    (hc : YulSemantics.Forall₂ (Passes.ConstDef f) as vs) (hg : R.getMany as = some args) :
    args = vs := by
  induction hc generalizing args with
  | nil => simp at hg; exact hg
  | @cons a v as vs hav htail ih =>
    rw [Regs.getMany_cons] at hg
    cases ha : R a with
    | none => simp [ha] at hg
    | some w =>
      cases hs : R.getMany as with
      | none => simp [ha, hs] at hg
      | some ws =>
        simp [ha, hs] at hg
        subst args
        rw [hR hav ha, ih hs]

omit model in
theorem constRegs_const {f : Func} (hnd : f.allDefs.Nodup)
    {b : Block} (hb : b ∈ f.blocks.toList) {d : ValId} {v : U256}
    (hi : .const d v ∈ b.instrs) {R : Regs} (hR : ConstRegs f R) :
    ConstRegs f (R.set d v) := by
  intro x u w hc hr
  by_cases hxd : x = d
  · subst x
    simp at hr
    subst w
    rcases constDef_instr_cases hnd hb hi (by simp [Instr.defs]) hc with h | ⟨yop, as, vs, h, -⟩
    · injection h
    · cases h
  · rw [Regs.set_other _ _ hxd] at hr
    exact hR hc hr

omit model in
theorem constRegs_call {f : Func} (hnd : f.allDefs.Nodup)
    {b : Block} (hb : b ∈ f.blocks.toList) {ds : List ValId} {fid : FuncId}
    {as : List ValId} (hi : .call ds fid as ∈ b.instrs) {R : Regs}
    (hR : ConstRegs f R) (rets : List U256) : ConstRegs f (R.setMany ds rets) := by
  intro d v w hc hr
  have hnot : d ∉ ds := by
    intro hd
    rcases constDef_instr_cases hnd hb hi (by simpa [Instr.defs] using hd) hc with h | ⟨yop, as', vs, h, -⟩
    · cases h
    · cases h
  rw [Regs.setMany_of_not_mem _ ds rets hnot] at hr
  exact hR hc hr

theorem constRegs_op {f : Func} (hwf : f.wfCheck n = true) (hnd : f.allDefs.Nodup)
    {b : Block} (hb : b ∈ f.blocks.toList) {ds : List ValId} {yop : Op}
    {as : List ValId} (hi : .op ds yop as ∈ b.instrs) {R : Regs} (hR : ConstRegs f R)
    {st st' : EvmState} {args rets : List U256} (hg : R.getMany as = some args)
    (hbi : builtinWithExternal model.calls model.creates .any yop args st (.ok rets st'))
    (hlen : ds.length = rets.length) : ConstRegs f (R.setMany ds rets) := by
  have harity := wfCheck_op_arity hwf hb hi
  cases ds with
  | nil =>
    intro d v w hc hr
    exact hR hc hr
  | cons d ds =>
    cases ds with
    | cons e es => simp at harity
    | nil =>
      cases rets with
      | nil => simp at hlen
      | cons r rs =>
        cases rs with
        | cons s ss => simp at hlen
        | nil =>
          intro x u w hc hr
          by_cases hxd : x = d
          · subst x
            simp [Regs.setMany, Regs.set] at hr
            subst w
            rcases constDef_instr_cases hnd hb hi (by simp [Instr.defs]) hc with h | ⟨yop', as', vs, h, hp, hvs, he⟩
            · cases h
            · injection h with _ hyop has
              subst yop'
              subst as'
              have hargs : args = vs := constRegs_getMany hR hvs hg
              subst args
              have hv := (Passes.evalPure_transport hp he hbi).1
              simpa using hv
          · rw [Regs.setMany_of_not_mem _ [d] [r] (by simp [hxd])] at hr
            exact hR hc hr

theorem Passes.pure_no_halt {yop : Op} (hp : pureOp yop = true) {args : List U256}
    {st st' : EvmState}
    (h : builtinWithExternal model.calls model.creates .any yop args st (.halt st')) : False := by
  have hn := (YulSemantics.EVM.effects_sound_withExternal model.calls model.creates .any).halt yop
    (pureOp_flags hp).2.2.2 args st (.halt st') h
  simp [YulSemantics.BuiltinResult.isHalt] at hn

/-- Lockstep simulation of an arbitrary suffix.  `CFMapSound` was established
statically by the fold-order induction; `ConstRegs` merely records that the
original execution has respected those certificates so far. -/
theorem constFold_exec_aux {P : Prog} {f : Func} {R : Regs} {st : EvmState}
    {rest : Rest} {res : FRes} (hwf : f.wfCheck n = true) (hnd : f.allDefs.Nodup)
    (h : Exec (model := model) P f R st rest res) :
    ∀ {b}, b ∈ f.blocks.toList → (∀ i ∈ rest.instrs, i ∈ b.instrs) →
      ∀ {m}, Passes.CFMapSound f m → ConstRegs f R →
        Exec (model := model) P (Passes.constFold f) R st
          (Passes.cfRest rest.instrs rest.term m) res := by
  induction h with
  | @const f R st d v is t res htail ih =>
    intro b hb hmem m hm hR
    rw [Passes.cfRest_cons]
    simp only [Passes.cfInstrOut, Passes.cfInstrMap]
    have hi0 : Instr.const d v ∈ b.instrs := hmem _ (by simp)
    refine Exec.const (ih hwf hnd hb
      (fun i hi => hmem i (List.mem_cons_of_mem _ hi))
      (Passes.cfInstrMap_sound hb hi0 hm)
      (constRegs_const hnd hb hi0 hR))
  | @op f R st st' ds yop as args rets is t res hg hbi hlen htail ih =>
    intro b hb hmem m hm hR
    rw [Passes.cfRest_cons]
    have hi : Instr.op ds yop as ∈ b.instrs := hmem _ (by simp)
    have hR' : ConstRegs f (R.setMany ds rets) :=
      constRegs_op hwf hnd hb hi hR hg hbi hlen
    cases ds with
    | nil =>
      simp only [Passes.cfInstrOut, Passes.cfInstrMap]
      exact Exec.op hg hbi hlen
        (ih hwf hnd hb (fun i hi' => hmem i (List.mem_cons_of_mem _ hi')) hm hR')
    | cons d ds =>
      cases ds with
      | cons e es =>
        simp only [Passes.cfInstrOut, Passes.cfInstrMap]
        exact Exec.op hg hbi hlen
          (ih hwf hnd hb (fun i hi' => hmem i (List.mem_cons_of_mem _ hi')) hm hR')
      | nil =>
        simp only [Passes.cfInstrOut, Passes.cfInstrMap]
        split
        · rename_i v hfold
          have hp : Passes.pureOp yop = true := by
            by_contra hp
            have hp' : Passes.pureOp yop = false := Bool.eq_false_of_not_eq_true hp
            simp [hp'] at hfold
          cases hs : as.mapM (m[·]?) with
          | none => simp [hp, hs] at hfold
          | some vs =>
            have hargs : args = vs := constRegs_getMany hR
              (Passes.cfMapSound_mapM hm hs) hg
            subst args
            have hv := Passes.evalPure_transport hp (by simpa [hp, hs] using hfold) hbi
            have hre : rets = [v] := hv.1
            have hst : st' = st := hv.2
            subst rets
            subst st'
            refine Exec.const ?_
            have hm' : Passes.CFMapSound f (m.insert d v) := by
              have hsnd : Passes.CFMapSound f
                  (Passes.cfInstrMap (.op [d] yop as) m) :=
                Passes.cfInstrMap_sound hb hi hm
              intro x u hx
              apply hsnd
              simpa [Passes.cfInstrMap, hfold] using hx
            exact ih hwf hnd hb (fun i hi' => hmem i (List.mem_cons_of_mem _ hi'))
              hm' hR'
        · exact Exec.op hg hbi hlen
            (ih hwf hnd hb (fun i hi' => hmem i (List.mem_cons_of_mem _ hi')) hm hR')
  | @opHalt f R st st' ds yop as args is t hg hbi =>
    intro b hb hmem m hm hR
    rw [Passes.cfRest_cons]
    cases ds with
    | nil =>
      simp only [Passes.cfInstrOut, Passes.cfInstrMap]
      exact Exec.opHalt hg hbi
    | cons d ds =>
      cases ds with
      | cons e es =>
        simp only [Passes.cfInstrOut, Passes.cfInstrMap]
        exact Exec.opHalt hg hbi
      | nil =>
        simp only [Passes.cfInstrOut, Passes.cfInstrMap]
        split
        · rename_i v hfold
          have hp : Passes.pureOp yop = true := by
            by_contra hp
            have hp' : Passes.pureOp yop = false := Bool.eq_false_of_not_eq_true hp
            simp [hp'] at hfold
          exact absurd hbi (Passes.pure_no_halt hp)
        · exact Exec.opHalt hg hbi
  | @call f g R st st' ds as fid args rvals eb is t res hfid hg hplen heb hbody hlen htail
      ihbody ih =>
    intro b hb hmem m hm hR
    rw [Passes.cfRest_cons]
    simp only [Passes.cfInstrOut, Passes.cfInstrMap]
    have hi : Instr.call ds fid as ∈ b.instrs := hmem _ (by simp)
    refine Exec.call hfid hg hplen heb hbody hlen ?_
    exact ih hwf hnd hb (fun i hi' => hmem i (List.mem_cons_of_mem _ hi')) hm
      (constRegs_call hnd hb hi hR rvals)
  | @callHalt f g R st st' ds as fid args eb is t hfid hg hplen heb hbody ihbody =>
    intro b hb hmem m hm hR
    rw [Passes.cfRest_cons]
    simp only [Passes.cfInstrOut, Passes.cfInstrMap]
    exact Exec.callHalt hfid hg hplen heb hbody
  | @jump f R st e tb args res htb hg hplen hbody ih =>
    intro b hb hmem m hm hR
    rw [Passes.cfRest_nil]
    obtain ⟨m', htb', hm'⟩ := Passes.constFold_block_get_sound htb
    have htbmem : tb ∈ f.blocks.toList := by
      obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp htb
      exact List.mem_iff_getElem.mpr ⟨e.target, by simpa using hlt, by simpa using hget⟩
    refine Exec.jump htb' hg hplen ?_
    rw [Passes.cfBlockOut_rest]
    exact ih hwf hnd htbmem (fun i hi => hi) hm'
      (constRegs_setMany_params hnd hR htbmem args)
  | @branchTrue f R st c v et ef tb args res hc hv htb hg hplen hbody ih =>
    intro b hb hmem m hm hR
    rw [Passes.cfRest_nil]
    obtain ⟨m', htb', hm'⟩ := Passes.constFold_block_get_sound htb
    have htbmem : tb ∈ f.blocks.toList := by
      obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp htb
      exact List.mem_iff_getElem.mpr ⟨et.target, by simpa using hlt, by simpa using hget⟩
    have hnext := ih hwf hnd htbmem (fun i hi => hi) hm'
      (constRegs_setMany_params hnd hR htbmem args)
    simp only [Passes.cfTerm]
    split
    · rename_i w hw
      have hwv : v = w := hR (hm hw) hc
      subst w
      have hvb : ¬ (v == 0) = true := by simpa [beq_iff_eq] using hv
      rw [if_neg hvb]
      rw [← Passes.cfBlockOut_rest] at hnext
      exact Exec.jump htb' hg hplen hnext
    · exact Exec.branchTrue hc hv htb' hg hplen
        (by rw [← Passes.cfBlockOut_rest] at hnext; exact hnext)
  | @branchFalse f R st c et ef tb args res hc htb hg hplen hbody ih =>
    intro b hb hmem m hm hR
    rw [Passes.cfRest_nil]
    obtain ⟨m', htb', hm'⟩ := Passes.constFold_block_get_sound htb
    have htbmem : tb ∈ f.blocks.toList := by
      obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp htb
      exact List.mem_iff_getElem.mpr ⟨ef.target, by simpa using hlt, by simpa using hget⟩
    have hnext := ih hwf hnd htbmem (fun i hi => hi) hm'
      (constRegs_setMany_params hnd hR htbmem args)
    simp only [Passes.cfTerm]
    split
    · rename_i w hw
      have hw0 : w = 0 := (hR (hm hw) hc).symm
      subst w
      rw [if_pos (by simp)]
      rw [← Passes.cfBlockOut_rest] at hnext
      exact Exec.jump htb' hg hplen hnext
    · exact Exec.branchFalse hc htb' hg hplen
        (by rw [← Passes.cfBlockOut_rest] at hnext; exact hnext)
  | @ret f R st xs vals hg =>
    intro b hb hmem m hm hR
    rw [Passes.cfRest_nil]
    exact Exec.ret hg
  | @halt f R st st' yop as args hg hbi =>
    intro b hb hmem m hm hR
    rw [Passes.cfRest_nil]
    exact Exec.halt hg hbi

/-- **Pass 2 (constant folding) soundness.** No dominance hypothesis.

`constFold_blocks_eq` turns the loop into a `List.foldl` over `cfBlockStep`, and
`constFold_spec` relates output blocks to input blocks index by index — that is
what closes `constFold_dom`.

The soundness proof rests on the single-assignment lemmas
(`instr_def_unique`, `param_not_instr_def`, `funcParam_not_instr_def`), the
step-by-step correspondence (`Passes.cfInstrStep_eq`, `cfInstr_fold_cons`,
`cfInstr_foldMap_cons`), and the following consistency invariant tying them
together.

* The invariant is **consistency**, not containment: `m[d]? = some v → R d =
  some w → w = v`. Entries for not-yet-executed definitions are unconstrained
  (`R d = none`), and a use of such a `d` is stuck in the original too.
* Consistency is used in *both* directions, and both are already available:
  forward at a folded op (`args.mapM (m[·]?) = some vs` together with
  `R.getMany args = some argvals` forces `argvals = vs`, and then
  `Passes.evalPure_transport` gives the value and leaves the state alone), and
  backward at a binding (`instr_def_unique` says the instruction now binding `d`
  *is* `d`'s only definition site, and `param_not_instr_def` /
  `funcParam_not_instr_def` rule out a jump or a function parameter re-binding
  something in the map's domain).
* The subtlety is that the map is **not flow-sensitive**: `constFold`
  threads it in *block-index* order while an execution visits blocks in
  *control-flow* order, so the map in force at block `k` was computed from blocks
  `0..k-1` whether or not the execution visited them. Consistency therefore
  cannot be carried by the forward simulation alone; it has to be established
  once, by induction over the **fold order** (block index, then instruction
  index), and only then consumed by the simulation. That induction is
  well-founded because a folded op's arguments are entered into the map strictly
  earlier in the same fold — `cfInstr_foldMap_cons` is the step lemma it needs.
* With consistency in hand the simulation itself is routine: register files stay
  *equal* on the two sides (a folded op binds the same destination to the same
  word), so the register side is a congruence and the machine state is
  untouched. -/
theorem constFold_sound {P : Prog} {f : Func} {args : List U256} {st : EvmState} {res : FRes}
    {eb eb' : Block} (hwf : f.wfCheck P.funcs.size = true)
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.constFold f).blocks[f.entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P (Passes.constFold f) (Regs.empty.setMany f.params args) st
      ⟨eb'.instrs, eb'.term⟩ res := by
  have hnd : f.allDefs.Nodup := wfCheck_defs_nodup hwf
  obtain ⟨m, hebo, hm⟩ := Passes.constFold_block_get_sound heb
  rw [heb'] at hebo
  have heq : eb' = Passes.cfBlockOut eb m := Option.some.inj hebo
  subst eb'
  have hebmem : eb ∈ f.blocks.toList := by
    obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp heb
    exact List.mem_iff_getElem.mpr ⟨f.entry, by simpa using hlt, by simpa using hget⟩
  rw [Passes.cfBlockOut_rest]
  exact constFold_exec_aux hwf hnd hexec hebmem (fun i hi => hi) hm
    (constRegs_entry hnd args)

end YulEvmCompiler.SsaCfg
