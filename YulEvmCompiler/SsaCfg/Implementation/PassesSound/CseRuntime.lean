import YulEvmCompiler.SsaCfg.Implementation.PassesSound.ConstFold
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.PassesSound.CseRuntime

Pass 3's runtime invariants.

`CseTabRuntime`/`CseExprRuntime` (the table's entries hold the values they
claim), the alias/domination zone `cseAvail_strict_dom`, the seen-set guard
`CseSeen`, and the register invariants `CseAgree`/`CseConstAgree`.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal stepOp ExternalCalls
  ExternalCreates)
open YulSemantics (Outcome)
variable [model : ExternalModel]

/-! ### CSE execution invariant -/

/-- Runtime meaning of a CSE expression.  For an operation entry we retain one
actual evaluation of the pure operation.  Its arguments are read through the
final substitution, exactly as they are in the emitted block, and the entry's
representative contains its (necessarily singleton) result.  Keeping the
historic state in the witness is intentional: `pure_rets_eq` transports the
result to a later occurrence without requiring the two machine states to be
equal. -/
def CseExprRuntime (τ : Passes.Subst) (R : Regs) :
    Passes.CseExpr → ValId → Prop
  | .const v, d => R d = some v
  | .op yop as, d =>
      ∃ vals w s s',
        R.getMany (Passes.substVs τ as) = some vals ∧
        builtinWithExternal model.calls model.creates yop vals s (.ok [w] s') ∧
        R d = some w

/-- Every entry in the currently available CSE table has its advertised
runtime meaning.  This is the semantic counterpart of `CseTabDefSound`: the
latter supplies the definition-site certificate, while this predicate records
that the certified representative has actually executed on the current path. -/
def CseTabRuntime (τ : Passes.Subst) (R : Regs) (tab : Passes.CseTab) : Prop :=
  (∀ {yop as d}, ((yop, as), d) ∈ tab.ops →
    CseExprRuntime τ R (.op yop as) d) ∧
  (∀ {v d}, (v, d) ∈ tab.consts → CseExprRuntime τ R (.const v) d)

/-- Registers read by the operation expressions in a runtime CSE table, after
the final use substitution. -/
def cseTabRuntimeUses (τ : Passes.Subst) (tab : Passes.CseTab) : List ValId :=
  tab.ops.flatMap fun e => Passes.substVs τ e.1.2

theorem CseTabRuntime.empty (τ : Passes.Subst) (R : Regs) :
    CseTabRuntime τ R {} := by
  simp [CseTabRuntime]

theorem CseTabRuntime.inheritTab {τ : Passes.Subst} {R : Regs}
    {tab : Passes.CseTab} (h : CseTabRuntime τ R tab) (ps : List ValId) :
    CseTabRuntime τ R (Passes.inheritTab tab ps) := by
  refine ⟨?_, ?_⟩
  · intro yop as d hm
    exact h.1 (List.mem_filter.mp hm).1
  · intro v d hm
    exact h.2 (List.mem_filter.mp hm).1

omit model in
theorem Passes.substV_not_blockParam {f : Func} {τ : Passes.Subst}
    (hnd : f.allDefs.Nodup) (hsub : Passes.CseSubDefSound f τ)
    {b : Block} (hb : b ∈ f.blocks.toList) {x : ValId}
    (hx : x ∉ b.params) : Passes.substV τ x ∉ b.params := by
  intro hp
  unfold Passes.substV at hp
  cases ht : τ[x]? with
  | none =>
      simp [Std.HashMap.getD_eq_getD_getElem?, ht] at hp
      exact hx hp
  | some y =>
      simp [Std.HashMap.getD_eq_getD_getElem?, ht] at hp
      obtain ⟨e, -, hy⟩ := hsub ht
      obtain ⟨b0, hb0, i, hi, hyd⟩ := hy.site
      exact param_not_instr_def hnd hb hb0 hi hp hyd

/-- Binding a register outside both the table representatives and the
substituted expression arguments preserves the runtime table invariant. -/
theorem CseTabRuntime.set_of_fresh {τ : Passes.Subst} {R : Regs}
    {tab : Passes.CseTab} (h : CseTabRuntime τ R tab) {d : ValId} {w : U256}
    (hvals : d ∉ Passes.cseTabVals tab) (huses : d ∉ cseTabRuntimeUses τ tab) :
    CseTabRuntime τ (R.set d w) tab := by
  refine ⟨?_, ?_⟩
  · intro yop as d0 hm
    obtain ⟨vals, v, s, s', hg, hb, hd0⟩ := h.1 hm
    have hd0ne : d0 ≠ d := by
      intro heq
      apply hvals
      subst d0
      exact List.mem_append_left _ (List.mem_map.mpr ⟨((yop, as), d), hm, rfl⟩)
    have harg : ∀ x ∈ Passes.substVs τ as, x ≠ d := by
      intro x hx heq
      apply huses
      subst x
      exact List.mem_flatMap.mpr ⟨((yop, as), d0), hm, hx⟩
    refine ⟨vals, v, s, s', ?_, hb, ?_⟩
    · rw [← Regs.getMany_congr (R1 := R) (R2 := R.set d w) (by
        intro x hx
        rw [Regs.set_other _ _ (harg x hx)])]
      exact hg
    · rw [Regs.set_other _ _ hd0ne]
      exact hd0
  · intro v d0 hm
    have hd0ne : d0 ≠ d := by
      intro heq
      apply hvals
      subst d0
      exact List.mem_append_right _ (List.mem_map.mpr ⟨(v, d), hm, rfl⟩)
    rw [CseExprRuntime, Regs.set_other _ _ hd0ne]
    exact h.2 hm

theorem CseTabRuntime.setMany_of_fresh {τ : Passes.Subst} {R : Regs}
    {tab : Passes.CseTab} (h : CseTabRuntime τ R tab)
    {ds : List ValId} {vals : List U256}
    (hfresh : ∀ d ∈ ds, d ∉ Passes.cseTabVals tab ∧
      d ∉ cseTabRuntimeUses τ tab) :
    CseTabRuntime τ (R.setMany ds vals) tab := by
  induction ds generalizing R vals with
  | nil => exact h
  | cons d ds ih =>
      cases vals with
      | nil => rw [Regs.setMany_nil_right]; exact h
      | cons v vals =>
          rw [Regs.setMany_cons]
          apply ih (h := h.set_of_fresh (hfresh d (by simp)).1
            (hfresh d (by simp)).2)
          intro x hx
          exact hfresh x (by simp [hx])

theorem CseTabRuntime.setMany_inheritTab {f : Func} {τ : Passes.Subst}
    {R : Regs} {tab : Passes.CseTab} {b : Block}
    (hnd : f.allDefs.Nodup) (hsub : Passes.CseSubDefSound f τ)
    (hb : b ∈ f.blocks.toList) (h : CseTabRuntime τ R tab)
    (vs : List U256) :
    CseTabRuntime τ (R.setMany b.params vs)
      (Passes.inheritTab tab b.params) := by
  have h0 := h.inheritTab b.params
  have hvals : ∀ p ∈ b.params,
      p ∉ Passes.cseTabVals (Passes.inheritTab tab b.params) := by
    intro p hp hmem
    simp only [Passes.cseTabVals, Passes.inheritTab, List.mem_append,
      List.mem_map, List.mem_filter] at hmem
    rcases hmem with ⟨e, ⟨-, he⟩, rfl⟩ | ⟨e, ⟨-, he⟩, rfl⟩ <;>
      simp [hp] at he
  have huses : ∀ p ∈ b.params,
      p ∉ cseTabRuntimeUses τ (Passes.inheritTab tab b.params) := by
    intro p hp hmem
    simp only [cseTabRuntimeUses, List.mem_flatMap] at hmem
    obtain ⟨⟨⟨yop, as⟩, d⟩, he, hx⟩ := hmem
    have he0 := (List.mem_filter.mp he).2
    rw [Bool.not_eq_true', Bool.or_eq_false_iff] at he0
    have hstored : ∀ x ∈ as, x ∉ b.params := by
      intro x hxa hxp
      exact (List.any_eq_false.mp he0.1 x hxa) (by simpa using hxp)
    have hxmem : ∃ x ∈ as, Passes.substV τ x = p := by
      simpa [Passes.substVs] using hx
    obtain ⟨x, hxa, hxp⟩ := hxmem
    exact (Passes.substV_not_blockParam hnd hsub hb (hstored x hxa)) (hxp ▸ hp)
  have go : ∀ (qs : List ValId) (vs : List U256) (R0 : Regs),
      (∀ q ∈ qs, q ∈ b.params) →
      CseTabRuntime τ R0 (Passes.inheritTab tab b.params) →
      CseTabRuntime τ (R0.setMany qs vs) (Passes.inheritTab tab b.params) := by
    intro qs
    induction qs with
    | nil => intro vs R0 hqs hr; exact hr
    | cons p ps ih =>
        intro vs R0 hqs hr
        cases vs with
        | nil => rw [Regs.setMany_nil_right]; exact hr
        | cons v vs =>
            rw [Regs.setMany_cons]
            apply ih vs (R0.set p v) (fun q hq => hqs q (by simp [hq]))
            exact CseTabRuntime.set_of_fresh hr
              (hvals p (hqs p (by simp))) (huses p (hqs p (by simp)))
  exact go b.params vs R (fun q hq => hq) h0

theorem CseTabRuntime.addConst {τ : Passes.Subst} {R : Regs}
    {tab : Passes.CseTab} (h : CseTabRuntime τ R tab) {d : ValId} {v : U256}
    (hvals : d ∉ Passes.cseTabVals tab) (huses : d ∉ cseTabRuntimeUses τ tab) :
    CseTabRuntime τ (R.set d v) { tab with consts := (v, d) :: tab.consts } := by
  have hold := h.set_of_fresh hvals huses (w := v)
  refine ⟨hold.1, ?_⟩
  intro v0 d0 hm
  rcases List.mem_cons.mp hm with hhead | htail
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hhead
    simp [CseExprRuntime]
  · exact hold.2 htail

theorem CseTabRuntime.addOp {τ : Passes.Subst} {R : Regs}
    {tab : Passes.CseTab} (h : CseTabRuntime τ R tab)
    {d : ValId} {yop : Op} {as : List ValId} {vals : List U256} {w : U256}
    {s s' : EvmState}
    (hvals : d ∉ Passes.cseTabVals tab) (huses : d ∉ cseTabRuntimeUses τ tab)
    (hg : (R.set d w).getMany (Passes.substVs τ as) = some vals)
    (hb : builtinWithExternal model.calls model.creates yop vals s (.ok [w] s')) :
    CseTabRuntime τ (R.set d w) { tab with ops := ((yop, as), d) :: tab.ops } := by
  have hold := h.set_of_fresh hvals huses (w := w)
  refine ⟨?_, hold.2⟩
  intro yop0 as0 d0 hm
  rcases List.mem_cons.mp hm with hhead | htail
  · obtain ⟨hkey, rfl⟩ := Prod.mk.inj hhead
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkey
    exact ⟨vals, w, s, s', hg, hb, by simp⟩
  · exact hold.1 htail

theorem CseTabRuntime.const_of_find {τ : Passes.Subst} {R : Regs}
    {tab : Passes.CseTab} (h : CseTabRuntime τ R tab)
    {v v0 : U256} {d : ValId}
    (hf : tab.consts.find? (fun x => x.1 == v) = some (v0, d)) :
    v0 = v ∧ R d = some v := by
  have hm : (v0, d) ∈ tab.consts := List.mem_of_find?_eq_some hf
  have hv : v0 = v := beq_iff_eq.mp (List.find?_some
    (p := fun x : U256 × ValId => x.1 == v) (a := (v0, d)) hf)
  subst v0
  exact ⟨rfl, h.2 hm⟩

theorem CseTabRuntime.op_of_find {τ : Passes.Subst} {R : Regs}
    {tab : Passes.CseTab} (h : CseTabRuntime τ R tab)
    {yop yop0 : Op} {as as0 : List ValId} {d : ValId}
    (hf : tab.ops.find? (fun x => x.1 == (yop, as)) = some ((yop0, as0), d)) :
    yop0 = yop ∧ as0 = as ∧ CseExprRuntime τ R (.op yop as) d := by
  have hm : ((yop0, as0), d) ∈ tab.ops := List.mem_of_find?_eq_some hf
  have heq : (yop0, as0) = (yop, as) :=
    beq_iff_eq.mp (List.find?_some
      (p := fun x : (Op × List ValId) × ValId => x.1 == (yop, as))
      (a := ((yop0, as0), d)) hf)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  exact ⟨rfl, rfl, h.1 hm⟩

/-- Consume an operation-table runtime certificate at a repeated pure
operation.  The stored and current evaluations have the same arguments, so
purity fixes the result; well-formed CSE operations have one destination and
therefore one result. -/
theorem CseExprRuntime.op_result {τ : Passes.Subst} {R : Regs}
    {yop : Op} {as : List ValId} {d : ValId}
    (hr : CseExprRuntime τ R (.op yop as) d)
    (hp : Passes.pureOp yop = true) {vals rets : List U256} {st st' : EvmState}
    (hg : R.getMany (Passes.substVs τ as) = some vals)
    (hb : builtinWithExternal model.calls model.creates yop vals st (.ok rets st')) :
    ∃ w, rets = [w] ∧ R d = some w := by
  obtain ⟨vals0, w0, s, s', hg0, hb0, hd⟩ := hr
  have hvals : vals0 = vals := Option.some.inj (hg0.symm.trans hg)
  subst vals0
  have hrets : [w0] = rets := Passes.pure_rets_eq hp hb0 hb
  exact ⟨w0, hrets.symm, hd⟩

/-! The executable view of the instruction fold.  Keeping this recursive
form separate from `cseBlockOut` makes the semantic induction follow the
source instruction list one constructor at a time; the lemma below reconnects
it to the accumulator/reverse implementation used by the pass. -/

namespace Passes

def cseInstrsOut (τ : Subst) :
    List Instr → CseTab → Std.HashSet ValId → Subst →
      Std.HashSet ValId → Std.HashSet ValId → List Instr
  | [], _, _, _, _, _ => []
  | i :: is, tab, used, σ, defined, blockDefs =>
      let s := cseInstrStep i ⟨[], tab, used, σ, defined, blockDefs⟩
      s.1.reverse.map (substInstr τ) ++
        cseInstrsOut τ is s.2.1 s.2.2.1 s.2.2.2.1
          s.2.2.2.2.1 s.2.2.2.2.2

omit model in
theorem cseInstrStep_acc_eq (i : Instr) (acc : List Instr)
    (tab : CseTab) (used : Std.HashSet ValId) (σ : Subst)
    (defined blockDefs : Std.HashSet ValId) :
    cseInstrStep i ⟨acc, tab, used, σ, defined, blockDefs⟩ =
      let s := cseInstrStep i ⟨[], tab, used, σ, defined, blockDefs⟩
      ⟨s.1 ++ acc, s.2.1, s.2.2.1, s.2.2.2.1,
        s.2.2.2.2.1, s.2.2.2.2.2⟩ := by
  cases i with
  | const d v =>
      simp only [cseInstrStep, substInstr]
      split <;> rfl
  | op ds yop args =>
      cases ds with
      | nil => rfl
      | cons d rest =>
          cases rest with
          | cons e es => rfl
          | nil =>
              simp only [cseInstrStep, substInstr]
              split <;> (try split <;> (try split)) <;> rfl
  | call ds fid args => rfl

omit model in
theorem cseInstrFold_acc_state (l : List Instr) (acc : List Instr)
    (tab : CseTab) (used : Std.HashSet ValId) (σ : Subst)
    (defined blockDefs : Std.HashSet ValId) :
    let r := l.foldl (fun s i => cseInstrStep i s)
      ⟨acc, tab, used, σ, defined, blockDefs⟩
    let r0 := l.foldl (fun s i => cseInstrStep i s)
      ⟨[], tab, used, σ, defined, blockDefs⟩
    r = ⟨r0.1 ++ acc, r0.2.1, r0.2.2.1, r0.2.2.2.1,
      r0.2.2.2.2.1, r0.2.2.2.2.2⟩ := by
  induction l generalizing acc tab used σ defined blockDefs with
  | nil => rfl
  | cons i is ih =>
      rw [List.foldl_cons, List.foldl_cons, cseInstrStep_acc_eq]
      let s := cseInstrStep i ⟨[], tab, used, σ, defined, blockDefs⟩
      rw [ih (acc := s.1 ++ acc), ih (acc := s.1)]
      simp [List.append_assoc]

omit model in
theorem cseInstrFold_acc (τ : Subst) (l : List Instr) (acc : List Instr)
    (tab : CseTab) (used : Std.HashSet ValId) (σ : Subst)
    (defined blockDefs : Std.HashSet ValId) :
    let r := l.foldl (fun s i => cseInstrStep i s)
      ⟨acc, tab, used, σ, defined, blockDefs⟩
    let r0 := l.foldl (fun s i => cseInstrStep i s)
      ⟨[], tab, used, σ, defined, blockDefs⟩
    r.1.reverse.map (substInstr τ) =
      acc.reverse.map (substInstr τ) ++ r0.1.reverse.map (substInstr τ)
      ∧ r.2 = r0.2 := by
  rw [cseInstrFold_acc_state]
  simp [List.reverse_append, List.map_append]

omit model in
theorem cseInstrsOut_eq_fold (τ : Subst) (l : List Instr) (tab : CseTab)
    (used : Std.HashSet ValId) (σ : Subst)
    (defined blockDefs : Std.HashSet ValId) :
    cseInstrsOut τ l tab used σ defined blockDefs =
      (l.foldl (fun s i => cseInstrStep i s)
        ⟨[], tab, used, σ, defined, blockDefs⟩).1.reverse.map
        (substInstr τ) := by
  induction l generalizing tab used σ defined blockDefs with
  | nil => rfl
  | cons i is ih =>
      rw [cseInstrsOut]
      let s := cseInstrStep i ⟨[], tab, used, σ, defined, blockDefs⟩
      rw [ih]
      have hacc := cseInstrFold_acc τ is s.1 s.2.1 s.2.2.1 s.2.2.2.1
        s.2.2.2.2.1 s.2.2.2.2.2
      rw [List.foldl_cons]
      exact hacc.1.symm

end Passes

namespace Passes

omit model in
theorem cseInstrFold_defs_source (l : List Instr) (acc : List Instr)
    (tab : CseTab) (used : Std.HashSet ValId) (σ : Subst)
    (defined blockDefs : Std.HashSet ValId) {x : ValId}
    (hx : x ∈ (l.foldl (fun s i => cseInstrStep i s)
      ⟨acc, tab, used, σ, defined, blockDefs⟩).1.flatMap Instr.defs) :
    x ∈ acc.flatMap Instr.defs ∨ x ∈ l.flatMap Instr.defs := by
  induction l generalizing acc tab used σ defined blockDefs with
  | nil => exact Or.inl hx
  | cons i is ih =>
      rw [List.foldl_cons] at hx
      rcases ih _ _ _ _ _ _ hx with hold | htail
      · rcases cseInstrStep_out (i := i) (acc := acc) (tab := tab)
          (used := used) (σ := σ) with hs | hs
        · change x ∈ (cseInstrStep i
            ⟨acc, tab, used, σ, defined, blockDefs⟩).1.flatMap Instr.defs at hold
          rw [hs] at hold
          exact Or.inl hold
        · change x ∈ (cseInstrStep i
            ⟨acc, tab, used, σ, defined, blockDefs⟩).1.flatMap Instr.defs at hold
          rw [hs, List.flatMap_cons] at hold
          rcases List.mem_append.mp hold with hnew | hold
          · exact Or.inr (by
              rw [List.flatMap_cons]
              apply List.mem_append_left
              simpa using hnew)
          · exact Or.inl hold
      · exact Or.inr (by
          rw [List.flatMap_cons]
          exact List.mem_append_right _ htail)

omit model in
theorem cseBlockOut_def_source {f : Func} {i : BlockId} {b : Block}
    (hb : f.blocks[i]? = some b) {x : ValId}
    (hx : x ∈ ToAsm.blockDefs
      (substBlock (csePrefix f f.blocks.size).2.2 (cseBlockOut f i))) :
    x ∈ ToAsm.blockDefs b := by
  have hi : i < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hbang : f.blocks[i]! = b := by
    rw [getElem!_eq_getElem hi]
    exact (Array.getElem?_eq_some_iff.mp hb).2
  rw [ToAsm.mem_blockDefs] at hx ⊢
  rcases hx with hp | hd
  · exact Or.inl (by simpa [substBlock, cseBlockOut, hbang] using hp)
  · right
    simp only [substBlock, List.mem_flatMap] at hd
    obtain ⟨j, hj, hxj⟩ := hd
    obtain ⟨j0, hj0, rfl⟩ := List.mem_map.mp hj
    have hxj0 : x ∈ j0.defs := by simpa using hxj
    let st := csePrefix f i
    let tab := cseEntryTab f (inEdgeSources f) st.2.1 i
    let r := b.instrs.foldl (fun s ins => cseInstrStep ins s)
      ⟨[], tab, ∅, st.2.2, ∅, cseBlockDefs b⟩
    have hjr : j0 ∈ r.1 := by
      simpa [cseBlockOut, hbang, st, tab, r] using hj0
    have hflat : x ∈ r.1.flatMap Instr.defs :=
      List.mem_flatMap.mpr ⟨j0, hjr, hxj0⟩
    rcases cseInstrFold_defs_source b.instrs [] tab ∅ st.2.2 ∅
        (cseBlockDefs b) hflat with hnil | hout
    · simp at hnil
    · exact hout

end Passes

omit model in
/-- Runtime-independent stale-zone fact for inherited CSE entries: the
representative's unique defining block strictly dominates the block at which
the entry is available. -/
theorem cseAvail_strict_dom {f : Func} (hnd : f.allDefs.Nodup)
    (hwf : f.wfCheck n = true) {di : BlockId} {db : Block}
    (hdb : f.blocks[di]? = some db) {x : ValId}
    (hxdef : x ∈ ToAsm.blockDefs db) {i : BlockId}
    (hx : x ∈ Passes.cseAvail f i) : StrictBlockDom f di i := by
  intro path hp
  induction hp with
  | entry =>
      rw [Passes.cseAvail_entry] at hx
      simp at hx
  | @edge path j b e hp hb he ih =>
      rcases Passes.cseAvail_succ hnd hwf hb he hx with hlocal | havail
      · have horigin := Passes.cseBlockOut_def_source hb hlocal
        have hji := Passes.block_def_index_unique hnd hdb hb hxdef horigin
        subst j
        exact List.mem_append_right _ (by simp)
      · exact List.mem_append_left _ (ih havail)

omit model in
/-- Every final CSE alias is either represented earlier in the same block or
by a definition in a strict predecessor chain. -/
theorem cse_alias_zone {f : Func} (hnd : f.allDefs.Nodup)
    (hwf : f.wfCheck n = true) {d d0 : ValId}
    (hmap : (Passes.csePrefix f f.blocks.size).2.2[d]? = some d0)
    {di : BlockId} {db : Block} (hdb : f.blocks[di]? = some db)
    (hddef : d ∈ ToAsm.blockDefs db) {ri : BlockId} {rb : Block}
    (hrb : f.blocks[ri]? = some rb) (hrdef : d0 ∈ ToAsm.blockDefs rb) :
    ri = di ∨ StrictBlockDom f ri di := by
  let τ := (Passes.csePrefix f f.blocks.size).2.2
  have hsubst : Passes.substV τ d = d0 := by
    simp [τ, Passes.substV, Std.HashMap.getD_eq_getD_getElem?, hmap]
  have hresolve := (Passes.cseBlock_spec hnd hdb).2.1 d hddef
  rw [hsubst] at hresolve
  rcases hresolve with hlocal | havail
  · have horigin := Passes.cseBlockOut_def_source hdb hlocal
    exact Or.inl (Passes.block_def_index_unique hnd hrb hdb hrdef horigin)
  · exact Or.inr (cseAvail_strict_dom hnd hwf hrb hrdef havail)

namespace Passes

def Before (a b : ValId) (xs : List ValId) : Prop :=
  ∃ pre mid post, xs = pre ++ a :: mid ++ b :: post

omit model in
theorem Before.asymm {a b : ValId} {xs : List ValId} (hn : xs.Nodup)
    (hab : Before a b xs) : ¬ Before b a xs := by
  rcases hab with ⟨pre, mid, post, rfl⟩
  rintro ⟨pre', mid', post', heq⟩
  let ia := pre.length
  let ib := pre.length + 1 + mid.length
  let ib' := pre'.length
  let ia' := pre'.length + 1 + mid'.length
  have hiaQ : (pre ++ a :: mid ++ b :: post)[ia]? = some a := by
    simp [ia]
  have hibQ : (pre ++ a :: mid ++ b :: post)[ib]? = some b := by
    rw [show pre ++ a :: mid ++ b :: post =
      (pre ++ [a] ++ mid) ++ (b :: post) by simp [List.append_assoc]]
    have hib_eq : ib = (pre ++ [a] ++ mid).length := by
      simp [ib]
      omega
    rw [hib_eq]
    simp
  have hibQ' : (pre ++ a :: mid ++ b :: post)[ib']? = some b := by
    rw [heq]
    simp [ib']
  have hiaQ' : (pre ++ a :: mid ++ b :: post)[ia']? = some a := by
    rw [heq]
    rw [show pre' ++ b :: mid' ++ a :: post' =
      (pre' ++ [b] ++ mid') ++ (a :: post') by simp [List.append_assoc]]
    have hia_eq : ia' = (pre' ++ [b] ++ mid').length := by
      simp [ia']
      omega
    rw [hia_eq]
    simp
  obtain ⟨hia_lt, hia⟩ := List.getElem?_eq_some_iff.mp hiaQ
  obtain ⟨hib_lt, hib⟩ := List.getElem?_eq_some_iff.mp hibQ
  obtain ⟨hib'_lt, hib'⟩ := List.getElem?_eq_some_iff.mp hibQ'
  obtain ⟨hia'_lt, hia'⟩ := List.getElem?_eq_some_iff.mp hiaQ'
  have hea : ia = ia' :=
    (hn.getElem_inj_iff (hi := hia_lt) (hj := hia'_lt)).mp (hia.trans hia'.symm)
  have heb : ib = ib' :=
    (hn.getElem_inj_iff (hi := hib_lt) (hj := hib'_lt)).mp (hib.trans hib'.symm)
  dsimp [ia, ib, ia', ib'] at hea heb
  omega

omit model in
theorem substInstr_use_source_of_rangeFree {sigma tau : Subst}
    (hext : SubstExt sigma tau) (hrange : RangeFree tau)
    {d d0 : ValId} (hmap : tau[d]? = some d0)
    {i : Instr} (hd : d ∈ (substInstr sigma i).uses) : d ∈ i.uses := by
  obtain ⟨x, hx, hxd⟩ := substInstr_use hd
  unfold substV at hxd
  cases hsx : sigma[x]? with
  | none =>
      simp [Std.HashMap.getD_eq_getD_getElem?, hsx] at hxd
      simpa [hxd] using hx
  | some y =>
      have hty : tau[x]? = some y := hext hsx
      have hynone : tau[y]? = none := hrange hty
      simp [Std.HashMap.getD_eq_getD_getElem?, hsx] at hxd
      subst y
      rw [hmap] at hynone
      contradiction

omit model in
theorem instr_order_before {f : Func} {b : Block}
    (hb : b ∈ f.blocks.toList) {pre mid post : List Instr} {i j : Instr}
    (his : b.instrs = pre ++ i :: mid ++ j :: post)
    {d e : ValId} (hdi : i.defs = [d]) (hej : j.defs = [e]) :
    Before d e (cseSeen f f.blocks.size) := by
  obtain ⟨bs, bt, hbs⟩ := List.mem_iff_append.mp hb
  refine ⟨bs.flatMap (fun b : Block => b.instrs.flatMap Instr.defs) ++
      pre.flatMap Instr.defs,
    mid.flatMap Instr.defs,
    post.flatMap Instr.defs ++
      bt.flatMap (fun b : Block => b.instrs.flatMap Instr.defs), ?_⟩
  have htake : f.blocks.toList.take f.blocks.size = f.blocks.toList := by simp
  rw [cseSeen, htake, hbs]
  simp [his, hdi, hej, List.append_assoc]

omit model in
theorem instr_order_before_mem {f : Func} {b : Block}
    (hb : b ∈ f.blocks.toList) {pre mid post : List Instr} {i j : Instr}
    (his : b.instrs = pre ++ i :: mid ++ j :: post)
    {d e : ValId} (hdi : d ∈ i.defs) (hej : e ∈ j.defs) :
    Before d e (cseSeen f f.blocks.size) := by
  obtain ⟨bs, bt, hbs⟩ := List.mem_iff_append.mp hb
  obtain ⟨di0, di1, hdiSplit⟩ := List.mem_iff_append.mp hdi
  obtain ⟨ej0, ej1, hejSplit⟩ := List.mem_iff_append.mp hej
  refine ⟨bs.flatMap (fun b : Block => b.instrs.flatMap Instr.defs) ++
      pre.flatMap Instr.defs ++ di0,
    di1 ++ mid.flatMap Instr.defs ++ ej0,
    ej1 ++ post.flatMap Instr.defs ++
      bt.flatMap (fun b : Block => b.instrs.flatMap Instr.defs), ?_⟩
  have htake : f.blocks.toList.take f.blocks.size = f.blocks.toList := by simp
  rw [cseSeen, htake, hbs]
  simp only [List.flatMap_append, List.flatMap_cons]
  rw [his]
  simp only [List.flatMap_append, List.flatMap_cons]
  rw [hdiSplit, hejSplit]
  simp [List.append_assoc]

omit model in
theorem source_use_mem_substInstr_of_none {sigma : Subst} {i : Instr}
    {x : ValId} (hn : sigma[x]? = none) (hx : x ∈ i.uses) :
    x ∈ (substInstr sigma i).uses := by
  cases i with
  | const d v => simp [Instr.uses] at hx
  | op ds yop args =>
      simp only [Instr.uses] at hx ⊢
      simp only [substInstr, substVs, List.mem_map]
      exact ⟨x, hx, by simp [substV, Std.HashMap.getD_eq_getD_getElem?, hn]⟩
  | call ds fid args =>
      simp only [Instr.uses] at hx ⊢
      simp only [substInstr, substVs, List.mem_map]
      exact ⟨x, hx, by simp [substV, Std.HashMap.getD_eq_getD_getElem?, hn]⟩

omit model in
theorem cse_drop_not_self_use {f : Func} {li : Array (List ValId)}
    (hnd : f.allDefs.Nodup) (hwf : f.wfCheck n = true)
    (hli : ToAsm.liveInSets f = some li) (hdom : ToAsm.Func.domCheck f = true)
    (hrange : RangeFree (csePrefix f f.blocks.size).2.2)
    (horder : AliasOrdered (cseSeen f f.blocks.size) (csePrefix f f.blocks.size).2.2)
    {d d0 : ValId} (hmap : (csePrefix f f.blocks.size).2.2[d]? = some d0)
    {yop : Op} {args : List ValId}
    (hdrop : CseDropPos f (.op yop args) d)
    (hentry : CseEntryPos f (csePrefix f f.blocks.size).2.2 (.op yop args) d0)
    {di : BlockId} {db : Block} (hdb : f.blocks[di]? = some db)
    {path : List BlockId} (hpath : EntryPath f path di) :
    ∀ {i : Instr}, i ∈ db.instrs → d ∈ i.defs → d ∉ i.uses := by
  intro i hi hddef hdUse
  cases hdrop with
  | @op b pre post idrop sigmaDrop _ _ _ hbDrop hseqDrop hsubstDrop
      hdropNone hprefix =>
    have hidropDef : idrop.defs = [d] := by
      rw [← substInstr_defs sigmaDrop idrop, hsubstDrop]
      rfl
    have hiEq : i = idrop := instr_def_unique hnd
      (block_mem_of_getElem? hdb) hbDrop hi (by
        rw [hseqDrop]
        simp) hddef (by simp [hidropDef])
    subst i
    have hbIndex : b = db := by
      obtain ⟨bi, hblt, hbget⟩ := List.mem_iff_getElem.mp hbDrop
      have hbg : f.blocks[bi]? = some b := Array.getElem?_eq_some_iff.mpr
        ⟨by simpa using hblt, by simpa using hbget⟩
      have hbDef : d ∈ ToAsm.blockDefs b := ToAsm.mem_blockDefs.mpr
        (Or.inr (List.mem_flatMap.mpr ⟨idrop, by rw [hseqDrop]; simp,
          by rw [hidropDef]; simp⟩))
      have hdbDef : d ∈ ToAsm.blockDefs db := ToAsm.mem_blockDefs.mpr
        (Or.inr (List.mem_flatMap.mpr ⟨idrop, hi, by rw [hidropDef]; simp⟩))
      have hbi : bi = di := block_def_index_unique hnd hbg hdb hbDef hdbDef
      subst bi
      exact Option.some.inj (hbg.symm.trans hdb)
    subst b
    have hdArgs : d ∈ args := by
      have hs := source_use_mem_substInstr_of_none hdropNone hdUse
      rw [hsubstDrop] at hs
      simpa [Instr.uses] using hs
    cases hentry with
    | @op br preR postR irep sigmaRep _ _ _ hbRep hseqRep hsubstRep _ hextRep =>
      have hiRep : irep ∈ br.instrs := by rw [hseqRep]; simp
      have hdUseRep : d ∈ irep.uses := by
        refine substInstr_use_source_of_rangeFree hextRep hrange hmap ?_
        rw [hsubstRep]
        simpa [Instr.uses] using hdArgs
      have hiRepDef : irep.defs = [d0] := by
        rw [← substInstr_defs sigmaRep irep, hsubstRep]
        rfl
      obtain ⟨ri, hrlt, hrget⟩ := List.mem_iff_getElem.mp hbRep
      have hrb : f.blocks[ri]? = some br := by
        apply Array.getElem?_eq_some_iff.mpr
        exact ⟨by simpa using hrlt, by simpa using hrget⟩
      have hdBlockDef : d ∈ ToAsm.blockDefs db :=
        ToAsm.mem_blockDefs.mpr (Or.inr (List.mem_flatMap.mpr
          ⟨idrop, hi, by simp [hidropDef]⟩))
      have hrBlockDef : d0 ∈ ToAsm.blockDefs br :=
        ToAsm.mem_blockDefs.mpr (Or.inr (List.mem_flatMap.mpr
          ⟨irep, hiRep, by simp [hiRepDef]⟩))
      rcases cse_alias_zone hnd hwf hmap hdb hdBlockDef hrb hrBlockDef with hre | hrs
      · subst ri
        have hbr : br = db := Option.some.inj (hrb.symm.trans hdb)
        rw [hbr] at hiRep
        have hirep : irep ∈ pre := by
          have hm : irep ∈ pre ++ idrop :: post := by
            simpa [hseqDrop] using hiRep
          rcases List.mem_append.mp hm with hp | ht
          · exact hp
          · rcases List.mem_cons.mp ht with heq | hpost
            · subst irep
              have hdd0 : d = d0 := by simpa [hidropDef] using hiRepDef
              subst d0
              exact False.elim (by have := hrange hmap; rw [hmap] at this; contradiction)
            · obtain ⟨mid, tail, hpostEq⟩ := List.mem_iff_append.mp hpost
              have hrev : Before d d0 (cseSeen f f.blocks.size) :=
                instr_order_before (block_mem_of_getElem? hdb)
                  (pre := pre) (mid := mid) (post := tail)
                  (i := idrop) (j := irep) (by
                    rw [hseqDrop, hpostEq]
                    simp [List.append_assoc])
                  hidropDef hiRepDef
              obtain ⟨a, m, z, hord⟩ := horder d d0 hmap
              have hforward : Before d0 d (cseSeen f f.blocks.size) :=
                ⟨a, m, z, hord⟩
              have hseenNodup : (cseSeen f f.blocks.size).Nodup := by
                have htake : f.blocks.toList.take f.blocks.size = f.blocks.toList := by simp
                simpa [cseSeen, htake] using instrDefs_nodup hnd
              exact False.elim ((Before.asymm hseenNodup hforward) hrev)
        exact hprefix (List.mem_flatMap.mpr ⟨irep, hirep, hdUseRep⟩)
      · have hduseBlock : d ∈ ToAsm.blockUses br :=
          instr_use_mem_blockUses hiRep hdUseRep
        have hdr : BlockDom f di ri :=
          blockDef_dominates_use hnd hli hdom hdb hdBlockDef hrb hduseBlock
        have hrmem : ri ∈ path := hrs path hpath
        obtain ⟨prePath, hpRi, -, -⟩ := hpath.prefix_of_mem hrmem
        exact False.elim ((hrs.not_reverse hpRi) hdr)

end Passes

/-! ### The CSE substitution, its seen-set guard, and the register invariant

These are the pieces of the `cse_sound` lockstep that are independent of the
instruction fold: what the final substitution can contain, when a dropped
definition's site has already been passed, and how the two register files are
related at every point.  See the note above `cse_sound` for how they compose. -/

namespace Passes

/-- The final CSE substitution of `f`: the dropped-definition map accumulated
after every block has been processed.  `Passes.cse f` applies it to all uses. -/
def cseSub (f : Func) : Subst := (csePrefix f f.blocks.size).2.2

omit model in
theorem cseSub_inv {f : Func} (hnd : f.allDefs.Nodup) :
    CSEInv f (cseSeen f f.blocks.size) {} (cseSub f) :=
  (csePrefixInv hnd f.blocks.size (Nat.le_refl _)).1

omit model in
theorem cseSub_rangeFree {f : Func} (hnd : f.allDefs.Nodup) :
    RangeFree (cseSub f) := (cseSub_inv hnd).2.2.1

omit model in
/-- Both ends of a final alias are instruction destinations. -/
theorem cseSub_def_site {f : Func} (hnd : f.allDefs.Nodup) {d d0 : ValId}
    (h : (cseSub f)[d]? = some d0) :
    (∃ b ∈ f.blocks.toList, ∃ i ∈ b.instrs, d ∈ i.defs) ∧
      (∃ b ∈ f.blocks.toList, ∃ i ∈ b.instrs, d0 ∈ i.defs) := by
  obtain ⟨e, hd, hd0⟩ := (cseSub_inv hnd).2.1 h
  exact ⟨hd.site, hd0.site⟩

omit model in
theorem block_index_of_mem {f : Func} {b : Block} (hb : b ∈ f.blocks.toList) :
    ∃ i : Nat, f.blocks[i]? = some b := by
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hb
  refine ⟨i, ?_⟩
  rw [Array.getElem?_eq_getElem (by simpa using hi)]
  simpa using hget

omit model in
/-- The substitution in force at a mid-block fold position is a restriction of
the final one.  With `Passes.substVs_absorb` this is what lets a stored (already
substituted) table argument be replaced by the corresponding *source* use. -/
theorem cseFold_substExt {f : Func} (hnd : f.allDefs.Nodup)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {pre post : List Instr} (hsplit : b.instrs = pre ++ post) :
    SubstExt (pre.foldl (fun s i => cseInstrStep i s)
      ⟨[], cseEntryTab f (inEdgeSources f) (csePrefix f cur).2.1 cur, ∅,
        (csePrefix f cur).2.2, ∅, cseBlockDefs b⟩).2.2.2.1 (cseSub f) := by
  have hcur : cur < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hbmem : b ∈ f.blocks.toList := block_mem_of_getElem? hb
  have hseenSucc : cseSeen f (cur + 1) = cseSeen f cur ++ b.instrs.flatMap Instr.defs :=
    cseSeen_succ hb
  have hseenNodup : (cseSeen f cur ++ b.instrs.flatMap Instr.defs).Nodup := by
    rw [← hseenSucc]
    exact (instrDefs_nodup hnd).sublist (cseSeen_sublist f (cur + 1))
  have hflat : b.instrs.flatMap Instr.defs =
      pre.flatMap Instr.defs ++ post.flatMap Instr.defs := by
    rw [hsplit, List.flatMap_append]
  have hpreNodup : (cseSeen f cur ++ pre.flatMap Instr.defs).Nodup := by
    refine hseenNodup.sublist ?_
    exact (List.Sublist.refl _).append (by rw [hflat]; exact List.sublist_append_left _ _)
  have hpostNodup : ((cseSeen f cur ++ pre.flatMap Instr.defs) ++
      post.flatMap Instr.defs).Nodup := by
    rw [List.append_assoc, ← hflat]
    exact hseenNodup
  have hpreInv := csePrefixInv hnd cur (Nat.le_of_lt hcur)
  have htab : CSEInv f (cseSeen f cur)
      (cseEntryTab f (inEdgeSources f) (csePrefix f cur).2.1 cur)
      (csePrefix f cur).2.2 := cseEntryTab_inv hpreInv
  have hpreMem : ∀ i ∈ pre, i ∈ b.instrs := by
    intro i hi; rw [hsplit]; exact List.mem_append_left _ hi
  have hpostMem : ∀ i ∈ post, i ∈ b.instrs := by
    intro i hi; rw [hsplit]; exact List.mem_append_right _ hi
  have hr1 := cseInstrFold_inv hbmem htab pre hpreMem hpreNodup [] ∅ ∅ (cseBlockDefs b)
  set s1 := pre.foldl (fun s i => cseInstrStep i s)
    (⟨[], cseEntryTab f (inEdgeSources f) (csePrefix f cur).2.1 cur, ∅,
      (csePrefix f cur).2.2, ∅, cseBlockDefs b⟩ : CSEInner) with hs1
  have hr2 := cseInstrFold_inv hbmem hr1.1 post hpostMem hpostNodup
    s1.1 s1.2.2.1 s1.2.2.2.2.1 s1.2.2.2.2.2
  have hfull : post.foldl (fun s i => cseInstrStep i s)
      (⟨s1.1, s1.2.1, s1.2.2.1, s1.2.2.2.1, s1.2.2.2.2.1, s1.2.2.2.2.2⟩ : CSEInner) =
      b.instrs.foldl (fun s i => cseInstrStep i s)
        (⟨[], cseEntryTab f (inEdgeSources f) (csePrefix f cur).2.1 cur, ∅,
          (csePrefix f cur).2.2, ∅, cseBlockDefs b⟩ : CSEInner) := by
    rw [hsplit, List.foldl_append, ← hs1]
  have hend : SubstExt s1.2.2.2.1 (csePrefix f (cur + 1)).2.2 := by
    have h2 : SubstExt s1.2.2.2.1
        (post.foldl (fun s i => cseInstrStep i s)
          (⟨s1.1, s1.2.1, s1.2.2.1, s1.2.2.2.1, s1.2.2.2.2.1, s1.2.2.2.2.2⟩ :
            CSEInner)).2.2.2.1 := hr2.2
    rw [hfull] at h2
    have hbBang : f.blocks[cur]! = b := by
      rw [getElem!_eq_getElem hcur]
      exact (Array.getElem?_eq_some_iff.mp hb).2
    rw [csePrefix_succ]
    simp only [cseBlockStep, hbBang]
    intro x y hxy
    exact h2 hxy
  intro x y hxy
  exact csePrefix_ext_to hnd (Nat.succ_le_of_lt hcur) (Nat.le_refl _) (hend hxy)

end Passes

/-! ### Dominance plumbing -/

omit model in
theorem BlockDom.trans {f : Func} {a b c : BlockId}
    (hab : BlockDom f a b) (hbc : BlockDom f b c) : BlockDom f a c := by
  intro path hp
  rcases hbc path hp with rfl | hb
  · exact hab path hp
  · obtain ⟨pre, hpre, -, hsub⟩ := hp.prefix_of_mem hb
    rcases hab pre hpre with rfl | ha
    · exact Or.inr hb
    · exact Or.inr (hsub _ ha)

omit model in
theorem StrictBlockDom.blockDom {f : Func} {a b : BlockId}
    (h : StrictBlockDom f a b) : BlockDom f a b := fun path hp => Or.inr (h path hp)

/-! ### Two list lemmas for the intra-block alias order -/

omit model in
/-- In a duplicate-free list, an element occurring before a member of an initial
segment lies in that initial segment itself. -/
theorem mem_left_of_before {α : Type} {x y : α} :
    ∀ {l1 l2 p q : List α}, (l1 ++ l2).Nodup → l1 ++ l2 = p ++ x :: q →
      y ∈ q → y ∈ l1 → x ∈ l1 := by
  intro l1
  induction l1 with
  | nil => intro l2 p q _ _ _ hy; simp at hy
  | cons a l1 ih =>
      intro l2 p q hnd heq hyq hy1
      cases p with
      | nil =>
          have hax : a = x := by simpa using congrArg (·.head?) heq
          simp [hax]
      | cons a' p' =>
          have ha : a' = a := by simpa using (congrArg (·.head?) heq).symm
          subst ha
          have heq' : l1 ++ l2 = p' ++ x :: q := by
            simpa using congrArg (·.tail) heq
          have hnd' : (l1 ++ l2).Nodup := (List.nodup_cons.mp hnd).2
          have hane : y ≠ a' := by
            intro hya
            subst y
            have hmem : a' ∈ l1 ++ l2 := by
              rw [heq']
              exact List.mem_append_right _ (List.mem_cons_of_mem _ hyq)
            exact (List.nodup_cons.mp hnd).1 hmem
          have hy1' : y ∈ l1 := by
            rcases List.mem_cons.mp hy1 with h | h
            · exact absurd h hane
            · exact h
          exact List.mem_cons_of_mem _ (ih hnd' heq' hyq hy1')

omit model in
theorem Passes.sublist_flatMap_of_mem {α β : Type} (g : α → List β) :
    ∀ {l : List α} {a : α}, a ∈ l → (g a).Sublist (l.flatMap g)
  | [], _, h => absurd h (by simp)
  | c :: cs, a, h => by
      rw [List.flatMap_cons]
      rcases List.mem_cons.mp h with rfl | h'
      · exact List.sublist_append_left _ _
      · exact (Passes.sublist_flatMap_of_mem g h').trans
          (List.sublist_append_right _ _)

omit model in
/-- Comparing two decompositions of the same list: if `j` occurs after the
distinguished `i`, but not at or before it, then `i` belongs to the prefix of
the decomposition distinguished at `j`. -/
theorem mem_prefix_of_later {α : Type} {l pre post pre' post' : List α}
    {i j : α} (h : l = pre ++ i :: post) (_hj : j ∈ post)
    (hjpre : j ∉ pre) (hji : j ≠ i) (h' : l = pre' ++ j :: post') :
    i ∈ pre' := by
  subst l
  induction pre generalizing pre' with
  | nil =>
      cases pre' with
      | nil =>
          have heq : i = j := by simpa using congrArg List.head? h'
          exact absurd heq.symm hji
      | cons a as =>
          have heq : a = i := by simpa using (congrArg List.head? h').symm
          simp [heq]
  | cons a pre ih =>
      cases pre' with
      | nil =>
          have heq : a = j := by simpa using congrArg List.head? h'
          exact absurd (by simp [heq] : j ∈ a :: pre) hjpre
      | cons a' pre' =>
          have heq : a' = a := by simpa using (congrArg List.head? h').symm
          subst a'
          have htail : pre ++ i :: post = pre' ++ j :: post' := by
            simpa using congrArg List.tail h'
          exact List.mem_cons_of_mem _
            (ih (fun hm => hjpre (by simp [hm])) htail)

omit model in
theorem blockInstrDefs_nodup {f : Func} (hnd : f.allDefs.Nodup)
    {b : Block} (hb : b ∈ f.blocks.toList) :
    (b.instrs.flatMap Instr.defs).Nodup :=
  (Passes.instrDefs_nodup hnd).sublist
    (Passes.sublist_flatMap_of_mem (fun c => c.instrs.flatMap Instr.defs) hb)

omit model in
/-- Within a block, the representative of a final CSE alias is produced by a
strictly earlier instruction than the alias itself.  This is the intra-block
projection of `Passes.csePrefix_ordered`. -/
theorem cseSub_rep_before {f : Func} (hnd : f.allDefs.Nodup)
    {d d0 : ValId} (hmap : (Passes.cseSub f)[d]? = some d0)
    {b : Block} (hb : b ∈ f.blocks.toList)
    {pre post : List Instr} (hsplit : b.instrs = pre ++ post)
    (hd : d ∈ pre.flatMap Instr.defs)
    (hd0 : d0 ∈ b.instrs.flatMap Instr.defs) :
    d0 ∈ pre.flatMap Instr.defs := by
  classical
  set g : Block → List ValId := fun c => c.instrs.flatMap Instr.defs with hgdef
  have hLnd : (f.blocks.toList.flatMap g).Nodup := Passes.instrDefs_nodup hnd
  have htake : f.blocks.toList.take f.blocks.size = f.blocks.toList := by simp
  have hseenEq : Passes.cseSeen f f.blocks.size = f.blocks.toList.flatMap g := by
    simp only [Passes.cseSeen, htake, hgdef]
  obtain ⟨p, m, q, hord⟩ :=
    Passes.csePrefix_ordered hnd f.blocks.size (Nat.le_refl _) d d0 hmap
  rw [hseenEq] at hord
  obtain ⟨s, t, hst⟩ := List.append_of_mem hb
  have hLsplit : f.blocks.toList.flatMap g =
      (s.flatMap g ++ pre.flatMap Instr.defs) ++
        (post.flatMap Instr.defs ++ t.flatMap g) := by
    rw [hst]
    simp only [List.flatMap_append, List.flatMap_cons]
    have hgb : g b = pre.flatMap Instr.defs ++ post.flatMap Instr.defs := by
      simp [hgdef, hsplit, List.flatMap_append]
    rw [hgb]
    simp [List.append_assoc]
  have hnd2 : ((s.flatMap g ++ pre.flatMap Instr.defs) ++
      (post.flatMap Instr.defs ++ t.flatMap g)).Nodup := by
    rw [← hLsplit]; exact hLnd
  have heq2 : (s.flatMap g ++ pre.flatMap Instr.defs) ++
      (post.flatMap Instr.defs ++ t.flatMap g) = p ++ d0 :: (m ++ d :: q) := by
    rw [← hLsplit, hord]
    simp [List.append_assoc]
  have hdq : d ∈ m ++ d :: q := List.mem_append_right _ (by simp)
  have hd1 : d ∈ s.flatMap g ++ pre.flatMap Instr.defs :=
    List.mem_append_right _ hd
  have hmem := mem_left_of_before hnd2 heq2 hdq hd1
  rcases List.mem_append.mp hmem with hs | hpre
  · exfalso
    have hLsplit2 : f.blocks.toList.flatMap g =
        s.flatMap g ++ (g b ++ t.flatMap g) := by
      rw [hst]; simp [List.flatMap_append, List.flatMap_cons]
    have hnd3 : (s.flatMap g ++ (g b ++ t.flatMap g)).Nodup := by
      rw [← hLsplit2]; exact hLnd
    exact (List.nodup_append.mp hnd3).2.2 d0 hs d0
      (List.mem_append_left _ hd0) rfl
  · exact hpre

/-! ### The CSE register invariant -/

/-- `d`'s definition site has already been passed when block `cur` is being
executed with processed instruction prefix `pre`: the unique block defining `d`
dominates `cur`, and when that block *is* `cur` the defining instruction lies in
the processed prefix. -/
def CseSeen (f : Func) (cur : BlockId) (pre : List Instr) (d : ValId) : Prop :=
  ∃ di db, f.blocks[di]? = some db ∧ d ∈ db.instrs.flatMap Instr.defs ∧
    BlockDom f di cur ∧ (di = cur → d ∈ pre.flatMap Instr.defs)

omit model in
/-- Nothing is seen before the first instruction of the entry block. -/
theorem CseSeen.entry_elim {f : Func} {d : ValId}
    (h : CseSeen f f.entry [] d) : False := by
  obtain ⟨di, db, hdb, hdef, hdom, hloc⟩ := h
  rcases hdom [] EntryPath.entry with heq | hmem
  · simpa using hloc heq
  · simp at hmem

omit model in
/-- A value read in block `cur` is seen there: its defining block dominates
`cur`, and the caller supplies the same-block prefix guard. -/
theorem cseSeen_of_use {f : Func} {li : Array (List ValId)}
    (hnd : f.allDefs.Nodup) (hli : ToAsm.liveInSets f = some li)
    (hdom : ToAsm.Func.domCheck f = true)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {pre : List Instr} {x d0 : ValId}
    (hmap : (Passes.cseSub f)[x]? = some d0)
    (hxuse : x ∈ ToAsm.blockUses b)
    (hlocal : x ∈ b.instrs.flatMap Instr.defs → x ∈ pre.flatMap Instr.defs) :
    CseSeen f cur pre x := by
  obtain ⟨⟨b1, hb1, i, hi, hxd⟩, -⟩ := Passes.cseSub_def_site hnd hmap
  obtain ⟨di, hdi⟩ := Passes.block_index_of_mem hb1
  have hxflat : x ∈ b1.instrs.flatMap Instr.defs := List.mem_flatMap.mpr ⟨i, hi, hxd⟩
  have hxdef : x ∈ ToAsm.blockDefs b1 := ToAsm.mem_blockDefs.mpr (Or.inr hxflat)
  refine ⟨di, b1, hdi, hxflat,
    blockDef_dominates_use hnd hli hdom hdi hxdef hb hxuse, ?_⟩
  intro heq
  subst di
  have hbb : b1 = b := Option.some.inj (hdi.symm.trans hb)
  subst b1
  exact hlocal hxflat

omit model in
/-- A seen definition is not produced by any instruction still ahead of it in
its own block. -/
theorem CseSeen.not_defined_later {f : Func} (hnd : f.allDefs.Nodup)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {pre post : List Instr} (hsplit : b.instrs = pre ++ post)
    {d : ValId} (h : CseSeen f cur pre d) : d ∉ post.flatMap Instr.defs := by
  intro hd
  obtain ⟨di, db, hdb, hddef, hdom, hloc⟩ := h
  have hdb1 : d ∈ ToAsm.blockDefs db := ToAsm.mem_blockDefs.mpr (Or.inr hddef)
  have hdb2 : d ∈ ToAsm.blockDefs b := by
    refine ToAsm.mem_blockDefs.mpr (Or.inr ?_)
    rw [hsplit, List.flatMap_append]
    exact List.mem_append_right _ hd
  have heq : di = cur := Passes.block_def_index_unique hnd hdb hb hdb1 hdb2
  have hpre := hloc heq
  have hnodup : (b.instrs.flatMap Instr.defs).Nodup :=
    blockInstrDefs_nodup hnd (block_mem_of_getElem? hb)
  rw [hsplit, List.flatMap_append, List.nodup_append] at hnodup
  exact hnodup.2.2 d hpre d hd rfl

omit model in
/-- Whenever a dropped definition is seen, so is its representative.  Same-block
representatives use the intra-block alias order; inherited ones use the
dominance zone of `cse_alias_zone`. -/
theorem CseSeen.rep {f : Func} {n : Nat} (hnd : f.allDefs.Nodup)
    (hwf : f.wfCheck n = true)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {path : List BlockId} (hpath : EntryPath f path cur)
    {pre post : List Instr} (hsplit : b.instrs = pre ++ post)
    {d d0 : ValId} (hmap : (Passes.cseSub f)[d]? = some d0)
    (h : CseSeen f cur pre d) : CseSeen f cur pre d0 := by
  obtain ⟨di, db, hdb, hddef, hdom, hloc⟩ := h
  obtain ⟨-, ⟨rb, hrbmem, i0, hi0, hr0⟩⟩ := Passes.cseSub_def_site hnd hmap
  obtain ⟨ri, hrb⟩ := Passes.block_index_of_mem hrbmem
  have hrflat : d0 ∈ rb.instrs.flatMap Instr.defs := List.mem_flatMap.mpr ⟨i0, hi0, hr0⟩
  have hzone := cse_alias_zone hnd hwf hmap hdb
    (ToAsm.mem_blockDefs.mpr (Or.inr hddef)) hrb
    (ToAsm.mem_blockDefs.mpr (Or.inr hrflat))
  rcases hzone with heq | hs
  · subst heq
    have hrbdb : rb = db := Option.some.inj (hrb.symm.trans hdb)
    subst rb
    refine ⟨ri, db, hdb, hrflat, hdom, ?_⟩
    intro hcur
    have hdbb : db = b := by
      subst hcur
      exact Option.some.inj (hdb.symm.trans hb)
    subst db
    exact cseSub_rep_before hnd hmap (block_mem_of_getElem? hb) hsplit
      (hloc hcur) hrflat
  · refine ⟨ri, rb, hrb, hrflat, BlockDom.trans hs.blockDom hdom, ?_⟩
    intro hcur
    subst hcur
    exact absurd hdom (hs.not_reverse hpath)

/-- Register agreement between the source function and its CSE'd form.  Off the
substitution's domain the two register files are *equal*; on it, a dropped
definition agrees with its representative once its definition site is passed. -/
def CseAgree (f : Func) (cur : BlockId) (pre : List Instr) (R R' : Regs) : Prop :=
  (∀ x, (Passes.cseSub f)[x]? = none → R x = R' x) ∧
  (∀ {d d0 : ValId}, (Passes.cseSub f)[d]? = some d0 → CseSeen f cur pre d →
    R d = R' d0)

omit model in
theorem CseAgree.of_entry {f : Func} {cur : BlockId} {R : Regs}
    (hcur : cur = f.entry) : CseAgree f cur [] R R := by
  refine ⟨fun x _ => rfl, ?_⟩
  intro d d0 _ hseen
  subst hcur
  exact absurd hseen (fun h => h.entry_elim)


omit model in
/-- Stepping past a *kept* instruction: both sides bind the same destinations to
the same words. -/
theorem CseAgree.step_kept {f : Func} {n : Nat} (hnd : f.allDefs.Nodup)
    (hwf : f.wfCheck n = true)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {path : List BlockId} (hpath : EntryPath f path cur)
    {pre post : List Instr} {i : Instr} (hsplit : b.instrs = pre ++ i :: post)
    {R R' : Regs} (ha : CseAgree f cur pre R R')
    (hkept : ∀ x ∈ i.defs, (Passes.cseSub f)[x]? = none) (vs : List U256) :
    CseAgree f cur (pre ++ [i]) (R.setMany i.defs vs) (R'.setMany i.defs vs) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact Regs.setMany_congr (S := fun y => (Passes.cseSub f)[y]? = none)
      ha.1 _ _ x hx
  · intro d d0 hmap hseen
    have hdold : CseSeen f cur pre d := by
      obtain ⟨di, db, hdb, hddef, hdom, hloc⟩ := hseen
      refine ⟨di, db, hdb, hddef, hdom, ?_⟩
      intro heq
      have hmem := hloc heq
      rw [List.flatMap_append] at hmem
      rcases List.mem_append.mp hmem with h | h
      · exact h
      · exfalso
        have hdi : d ∈ i.defs := by simpa using h
        rw [hkept d hdi] at hmap
        exact absurd hmap (by simp)
    have hd0old : CseSeen f cur pre d0 :=
      CseSeen.rep hnd hwf hb hpath hsplit hmap hdold
    have hdnot : d ∉ i.defs := fun hdi =>
      (CseSeen.not_defined_later hnd hb hsplit hdold) (by simp [hdi])
    have hd0not : d0 ∉ i.defs := fun hdi =>
      (CseSeen.not_defined_later hnd hb hsplit hd0old) (by simp [hdi])
    rw [Regs.setMany_of_not_mem R i.defs vs hdnot,
      Regs.setMany_of_not_mem R' i.defs vs hd0not]
    exact ha.2 hmap hdold

omit model in
/-- Stepping past a *dropped* instruction: only the source binds its
destination, and the representative already holds the value. -/
theorem CseAgree.step_dropped {f : Func} {cur : BlockId}
    {pre : List Instr} {i : Instr} {d d0 : ValId} {w : U256}
    (hidefs : i.defs = [d]) (hmapd : (Passes.cseSub f)[d]? = some d0)
    {R R' : Regs} (ha : CseAgree f cur pre R R') (hval : R' d0 = some w) :
    CseAgree f cur (pre ++ [i]) (R.set d w) R' := by
  refine ⟨?_, ?_⟩
  · intro x hx
    have hxd : x ≠ d := by
      intro heq; subst x; rw [hmapd] at hx; exact absurd hx (by simp)
    rw [Regs.set_other _ _ hxd]
    exact ha.1 x hx
  · intro d1 d1' hmap1 hseen1
    by_cases hd1 : d1 = d
    · subst d1
      have : d1' = d0 := Option.some.inj (hmap1.symm.trans hmapd)
      subst d1'
      rw [Regs.set_same]
      exact hval.symm
    · have hold : CseSeen f cur pre d1 := by
        obtain ⟨di, db, hdb, hddef, hdom, hloc⟩ := hseen1
        refine ⟨di, db, hdb, hddef, hdom, ?_⟩
        intro heq
        have hmem := hloc heq
        rw [List.flatMap_append] at hmem
        rcases List.mem_append.mp hmem with h | h
        · exact h
        · exact absurd (by simpa [hidefs] using h) hd1
      rw [Regs.set_other _ _ hd1]
      exact ha.2 hmap1 hold

omit model in
/-- Crossing an edge: block parameters are never dropped, so the two register
files are extended identically, and the target's seen set is transported back
across the edge by `BlockDom.pred`. -/
theorem CseAgree.jump {f : Func} (hnd : f.allDefs.Nodup)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {path : List BlockId} (hpath : EntryPath f path cur)
    {e : Edge} (he : e ∈ b.term.edges)
    {tb : Block} (htb : f.blocks[e.target]? = some tb)
    {R R' : Regs} (ha : CseAgree f cur b.instrs R R') (vals : List U256) :
    CseAgree f e.target [] (R.setMany tb.params vals) (R'.setMany tb.params vals) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact Regs.setMany_congr (S := fun y => (Passes.cseSub f)[y]? = none)
      ha.1 _ _ x hx
  · intro d d0 hmap hseen
    obtain ⟨di, db, hdb, hddef, hdom, hloc⟩ := hseen
    have hne : di ≠ e.target := by
      intro heq; simpa using hloc heq
    have hcur : CseSeen f cur b.instrs d := by
      refine ⟨di, db, hdb, hddef, hdom.pred hpath hb he rfl hne, ?_⟩
      intro heq
      subst heq
      have hdbb : db = b := Option.some.inj (hdb.symm.trans hb)
      subst db
      exact hddef
    have hdnot : d ∉ tb.params := by
      intro hp
      obtain ⟨i1, hi1, hd1⟩ := List.mem_flatMap.mp hddef
      exact param_not_instr_def hnd (block_mem_of_getElem? htb)
        (block_mem_of_getElem? hdb) hi1 hp hd1
    have hd0not : d0 ∉ tb.params := by
      intro hp
      obtain ⟨-, ⟨rb, hrbmem, i0, hi0, hr0⟩⟩ := Passes.cseSub_def_site hnd hmap
      exact param_not_instr_def hnd (block_mem_of_getElem? htb) hrbmem hi0 hp hr0
    rw [Regs.setMany_of_not_mem R tb.params vals hdnot,
      Regs.setMany_of_not_mem R' tb.params vals hd0not]
    exact ha.2 hmap hcur

omit model in
/-- The block defining the representative of a rewritten use dominates the block
that reads it: this is the runtime counterpart of `cse_dom`. -/
theorem cseSub_use_dom {f : Func} {li : Array (List ValId)} {n : Nat}
    (hnd : f.allDefs.Nodup) (hli : ToAsm.liveInSets f = some li)
    (hdomc : ToAsm.Func.domCheck f = true) (hwf : f.wfCheck n = true)
    {i : BlockId} {b : Block} (hb : f.blocks[i]? = some b)
    {x d0 : ValId} (hmap : (Passes.cseSub f)[x]? = some d0)
    (hx : x ∈ ToAsm.blockUses b)
    {ri : BlockId} {rb : Block} (hrb : f.blocks[ri]? = some rb)
    (hrdef : d0 ∈ ToAsm.blockDefs rb) : BlockDom f ri i := by
  obtain ⟨⟨b1, hb1, i1, hi1, hxd⟩, -⟩ := Passes.cseSub_def_site hnd hmap
  obtain ⟨xi, hxi⟩ := Passes.block_index_of_mem hb1
  have hxdef : x ∈ ToAsm.blockDefs b1 :=
    ToAsm.mem_blockDefs.mpr (Or.inr (List.mem_flatMap.mpr ⟨i1, hi1, hxd⟩))
  have hdomx : BlockDom f xi i := blockDef_dominates_use hnd hli hdomc hxi hxdef hb hx
  rcases cse_alias_zone hnd hwf hmap hxi hxdef hrb hrdef with rfl | hs
  · exact hdomx
  · exact BlockDom.trans hs.blockDom hdomx

omit model in
/-- Every representative available at a mid-block fold position has already been
defined: either by an already-processed instruction of the current block, or in
a block that strictly dominates it.  This is the mid-block refinement of
`Passes.cseBlock_spec`'s table clause, and it is what supplies `CseSeen` for a
representative at the moment its alias is dropped. -/
theorem cseSeen_of_tabVal {f : Func} {n : Nat} (hnd : f.allDefs.Nodup)
    (hwf : f.wfCheck n = true)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {path : List BlockId} (hpath : EntryPath f path cur)
    {pre post : List Instr} (hsplit : b.instrs = pre ++ post)
    {used defined blockDefs : Std.HashSet ValId} {σ : Passes.Subst}
    {x : ValId}
    (hx : x ∈ Passes.cseTabVals (pre.foldl (fun s i => Passes.cseInstrStep i s)
      ⟨[], Passes.cseEntryTab f (Passes.inEdgeSources f)
        (Passes.csePrefix f cur).2.1 cur, used, σ, defined, blockDefs⟩).2.1) :
    CseSeen f cur pre x := by
  have hcur : cur < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  rcases Passes.cseInstrFold_tabVals pre [] _ used σ defined blockDefs hx with
    havail | hout
  · -- inherited from a strictly dominating block
    have hsound := Passes.cseEntryTab_sound hnd (Nat.le_of_lt hcur)
    have hdef : ∃ e, Passes.CseDef f e x := by
      rcases List.mem_append.mp havail with h | h
      · obtain ⟨⟨⟨yop, as⟩, d⟩, hm, hxd⟩ := List.mem_map.mp h
        have hd : d = x := hxd
        subst hd
        exact ⟨_, hsound.1 hm⟩
      · obtain ⟨⟨v, d⟩, hm, hxd⟩ := List.mem_map.mp h
        have hd : d = x := hxd
        subst hd
        exact ⟨_, hsound.2 hm⟩
    obtain ⟨e, hcd⟩ := hdef
    obtain ⟨b1, hb1, i1, hi1, hxd⟩ := hcd.site
    obtain ⟨di, hdi⟩ := Passes.block_index_of_mem hb1
    have hxflat : x ∈ b1.instrs.flatMap Instr.defs := List.mem_flatMap.mpr ⟨i1, hi1, hxd⟩
    have hs : StrictBlockDom f di cur := cseAvail_strict_dom hnd hwf hdi
      (ToAsm.mem_blockDefs.mpr (Or.inr hxflat)) havail
    refine ⟨di, b1, hdi, hxflat, hs.blockDom, ?_⟩
    intro heq
    subst heq
    exact absurd (BlockDom.refl f di) (hs.not_reverse hpath)
  · rcases Passes.cseInstrFold_defs_source pre [] _ used σ defined blockDefs hout with
      hnil | hlocal
    · simp at hnil
    · refine ⟨cur, b, hb, ?_, BlockDom.refl f cur, fun _ => hlocal⟩
      rw [hsplit, List.flatMap_append]
      exact List.mem_append_left _ hlocal

/-- Values whose CSE certificate is a literal constant can only contain that
literal once bound.  This is the small value-sensitive companion to the
site-only definition-provenance invariant. -/
def CseConstRegs (f : Func) (R : Regs) : Prop :=
  ∀ {d v w}, Passes.CseDef f (.const v) d → R d = some w → w = v

omit model in
theorem cseConstRegs_entry {f : Func} (hnd : f.allDefs.Nodup)
    (args : List U256) : CseConstRegs f (Regs.empty.setMany f.params args) := by
  intro d v w hc hr
  obtain ⟨b, hb, i, hi, hd⟩ := hc.site
  have hnot : d ∉ f.params := by
    intro hp
    exact funcParam_not_instr_def hnd hb hi hp hd
  rw [Regs.setMany_of_not_mem _ f.params args hnot] at hr
  simp [Regs.empty] at hr

omit model in
theorem CseConstRegs.params {f : Func} (hnd : f.allDefs.Nodup)
    {R : Regs} (hR : CseConstRegs f R) {b : Block}
    (hb : b ∈ f.blocks.toList) (vals : List U256) :
    CseConstRegs f (R.setMany b.params vals) := by
  intro d v w hc hr
  obtain ⟨b0, hb0, i, hi, hd⟩ := hc.site
  have hnot : d ∉ b.params := by
    intro hp
    exact param_not_instr_def hnd hb hb0 hi hp hd
  rw [Regs.setMany_of_not_mem _ b.params vals hnot] at hr
  exact hR hc hr

omit model in
theorem CseConstRegs.const {f : Func} (hnd : f.allDefs.Nodup)
    {b : Block} (hb : b ∈ f.blocks.toList) {d : ValId} {v : U256}
    (hi : .const d v ∈ b.instrs) {R : Regs} (hR : CseConstRegs f R) :
    CseConstRegs f (R.set d v) := by
  intro x u w hc hr
  by_cases hxd : x = d
  · subst x
    simp at hr
    subst w
    cases hc with
    | @const b0 _ u hb0 hi0 =>
        have heq : Instr.const d v = Instr.const d u :=
          instr_def_unique (d := d) hnd hb hb0 hi hi0
          (by simp [Instr.defs]) (by simp [Instr.defs])
        injection heq
  · rw [Regs.set_other _ _ hxd] at hr
    exact hR hc hr

omit model in
theorem CseConstRegs.nonconst {f : Func} (hnd : f.allDefs.Nodup)
    {b : Block} (hb : b ∈ f.blocks.toList) {i : Instr} (hi : i ∈ b.instrs)
    (hn : ∀ d v, i ≠ .const d v) {R : Regs} (hR : CseConstRegs f R)
    (vals : List U256) : CseConstRegs f (R.setMany i.defs vals) := by
  intro d v w hc hr
  have hnot : d ∉ i.defs := by
    intro hd
    cases hc with
    | @const b0 _ v hb0 hi0 =>
        have heq := instr_def_unique hnd hb hb0 hi hi0 hd (by simp [Instr.defs])
        exact hn _ _ heq
  rw [Regs.setMany_of_not_mem _ i.defs vals hnot] at hr
  exact hR hc hr

/-- Constant aliases agree globally, including the stale interval before their
definition on a loop revisit.  Operation aliases use `CseSeen`; constants need
this stronger clause because re-executing their representative writes the same
literal and therefore cannot invalidate an already-bound alias. -/
def CseConstAgree (f : Func) (R R' : Regs) : Prop :=
  ∀ {d d0 v}, (Passes.cseSub f)[d]? = some d0 →
    Passes.CseDef f (.const v) d → Passes.CseDef f (.const v) d0 →
    R d = none ∨ R d = R' d0

omit model in
theorem cseConstAgree_entry {f : Func} (hnd : f.allDefs.Nodup)
    (args : List U256) :
    CseConstAgree f (Regs.empty.setMany f.params args)
      (Regs.empty.setMany f.params args) := by
  intro d d0 v hmap hd hd0
  obtain ⟨b, hb, i, hi, hdd⟩ := hd.site
  have hnot : d ∉ f.params := by
    intro hp
    exact funcParam_not_instr_def hnd hb hi hp hdd
  left
  rw [Regs.setMany_of_not_mem _ f.params args hnot]
  rfl

omit model in
theorem CseConstAgree.params {f : Func} (hnd : f.allDefs.Nodup)
    {R R' : Regs} (ha : CseConstAgree f R R') {b : Block}
    (hb : b ∈ f.blocks.toList) (vals : List U256) :
    CseConstAgree f (R.setMany b.params vals) (R'.setMany b.params vals) := by
  intro d d0 v hmap hd hd0
  obtain ⟨bd, hbd, id, hid, hdd⟩ := hd.site
  obtain ⟨br, hbr, ir, hir, hdr⟩ := hd0.site
  have hdn : d ∉ b.params := fun hp => param_not_instr_def hnd hb hbd hid hp hdd
  have hd0n : d0 ∉ b.params := fun hp => param_not_instr_def hnd hb hbr hir hp hdr
  rw [Regs.setMany_of_not_mem _ b.params vals hdn,
    Regs.setMany_of_not_mem _ b.params vals hd0n]
  exact ha hmap hd hd0

omit model in
theorem CseConstAgree.nonconst {f : Func} (hnd : f.allDefs.Nodup)
    {R R' : Regs} (ha : CseConstAgree f R R')
    {b : Block} (hb : b ∈ f.blocks.toList) {i : Instr} (hi : i ∈ b.instrs)
    (hn : ∀ d v, i ≠ .const d v) (vals : List U256) :
    CseConstAgree f (R.setMany i.defs vals) (R'.setMany i.defs vals) := by
  intro d d0 v hmap hd hd0
  have hdn : d ∉ i.defs := by
    intro hdi
    cases hd with
    | @const bd _ v hbd hid =>
        exact hn _ _ (instr_def_unique hnd hb hbd hi hid hdi (by simp [Instr.defs]))
  have hd0n : d0 ∉ i.defs := by
    intro hdi
    cases hd0 with
    | @const br _ v hbr hir =>
        exact hn _ _ (instr_def_unique hnd hb hbr hi hir hdi (by simp [Instr.defs]))
  rw [Regs.setMany_of_not_mem _ i.defs vals hdn,
    Regs.setMany_of_not_mem _ i.defs vals hd0n]
  exact ha hmap hd hd0

omit model in
theorem CseConstAgree.nonconst_left {f : Func} (hnd : f.allDefs.Nodup)
    {R R' : Regs} (ha : CseConstAgree f R R')
    {b : Block} (hb : b ∈ f.blocks.toList) {i : Instr} (hi : i ∈ b.instrs)
    (hn : ∀ d v, i ≠ .const d v) (vals : List U256) :
    CseConstAgree f (R.setMany i.defs vals) R' := by
  intro d d0 v hmap hd hd0
  have hdn : d ∉ i.defs := by
    intro hdi
    cases hd with
    | @const bd _ v hbd hid =>
        exact hn _ _ (instr_def_unique hnd hb hbd hi hid hdi (by simp [Instr.defs]))
  rw [Regs.setMany_of_not_mem _ i.defs vals hdn]
  exact ha hmap hd hd0

omit model in
theorem CseConstAgree.const_kept {f : Func} (hnd : f.allDefs.Nodup)
    {R R' : Regs} (ha : CseConstAgree f R R') (hR : CseConstRegs f R)
    {b : Block} (hb : b ∈ f.blocks.toList) {d : ValId} {v : U256}
    (hi : .const d v ∈ b.instrs) (hdnone : (Passes.cseSub f)[d]? = none) :
    CseConstAgree f (R.set d v) (R'.set d v) := by
  intro x x0 u hmap hx hx0
  have hxd : x ≠ d := by
    intro heq
    subst x
    rw [hdnone] at hmap
    contradiction
  by_cases hx0d : x0 = d
  · subst x0
    have huv : u = v := by
      cases hx0 with
      | @const b0 _ u hb0 hi0 =>
          have heq : Instr.const d v = Instr.const d u :=
            instr_def_unique (d := d) hnd hb hb0 hi hi0
              (by simp [Instr.defs]) (by simp [Instr.defs])
          cases heq
          rfl
    subst u
    cases hrx : R x with
    | none =>
        left
        simpa [Regs.set, hxd] using hrx
    | some w =>
        have hw : w = v := hR hx hrx
        subst w
        right
        rw [Regs.set_other _ _ hxd, Regs.set_same]
        exact hrx
  · rw [Regs.set_other _ _ hxd, Regs.set_other _ _ hx0d]
    exact ha hmap hx hx0

omit model in
theorem CseConstAgree.const_dropped {f : Func} (hnd : f.allDefs.Nodup)
    {R R' : Regs} (ha : CseConstAgree f R R')
    {b : Block} (hb : b ∈ f.blocks.toList) {d d0 : ValId} {v : U256}
    (hi : .const d v ∈ b.instrs) (hmapd : (Passes.cseSub f)[d]? = some d0)
    (hval : R' d0 = some v) : CseConstAgree f (R.set d v) R' := by
  intro x x0 u hmap hx hx0
  by_cases hxd : x = d
  · subst x
    have hx0eq : x0 = d0 := Option.some.inj (hmap.symm.trans hmapd)
    subst x0
    have huv : u = v := by
      cases hx with
      | @const b0 _ u hb0 hi0 =>
          have heq : Instr.const d v = Instr.const d u :=
            instr_def_unique (d := d) hnd hb hb0 hi hi0
              (by simp [Instr.defs]) (by simp [Instr.defs])
          cases heq
          rfl
    subst u
    right
    simpa using hval.symm
  · rw [Regs.set_other _ _ hxd]
    exact ha hmap hx hx0

omit model in
/-- Successful reads consume the two register clauses: operation aliases must
be past their certified site, while constant aliases use global literal
agreement and therefore also cover a loop's stale pre-definition interval. -/
theorem cseGetMany {f : Func} (hnd : f.allDefs.Nodup)
    {cur : BlockId} {pre : List Instr} {R R' : Regs}
    (ha : CseAgree f cur pre R R') (hc : CseConstAgree f R R')
    {xs : List ValId} {vals : List U256}
    (hseen : ∀ {x d0 yop as}, x ∈ xs → (Passes.cseSub f)[x]? = some d0 →
      Passes.CseDef f (.op yop as) x → CseSeen f cur pre x)
    (hg : R.getMany xs = some vals) :
    R'.getMany (Passes.substVs (Passes.cseSub f) xs) = some vals := by
  apply Regs.getMany_substVs (R := R) (R' := R')
  · intro x hx
    cases hm : (Passes.cseSub f)[x]? with
    | none =>
        rw [Passes.substV, Std.HashMap.getD_eq_getD_getElem?, hm]
        exact ha.1 x hm
    | some d0 =>
        rw [Passes.substV, Std.HashMap.getD_eq_getD_getElem?, hm]
        obtain ⟨e, hdx, hd0⟩ := Passes.cseFinalSubDefSound hnd hm
        cases e with
        | const v =>
            rcases hc hm hdx hd0 with hn | heq
            · obtain ⟨w, hw⟩ := Regs.eq_some_of_getMany hg hx
              rw [hn] at hw
              contradiction
            · exact heq
        | op yop as => exact ha.2 hm (hseen hx hm hdx)
  · exact hg

omit model in
/-- A read of an operation alias is past its certified drop site.  The only
borderline case is a self-read at that site; the caller supplies exactly the
`cse_drop_not_self_use` consequence for the current fold step. -/
theorem cseSeen_of_op_use {f : Func} {li : Array (List ValId)} {n : Nat}
    (hnd : f.allDefs.Nodup) (hli : ToAsm.liveInSets f = some li)
    (hdom : ToAsm.Func.domCheck f = true) (_hwf : f.wfCheck n = true)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {pre post : List Instr} {i : Instr} (hsplit : b.instrs = pre ++ i :: post)
    {x d0 yop as} (huse : x ∈ i.uses)
    (hmap : (Passes.cseSub f)[x]? = some d0)
    (hdef : Passes.CseDef f (.op yop as) x)
    (hself : x ∈ i.defs → x ∉ i.uses) : CseSeen f cur pre x := by
  apply cseSeen_of_use hnd hli hdom hb hmap
  · rw [ToAsm.mem_blockUses]
    exact Or.inl (List.mem_flatMap.mpr ⟨i, by rw [hsplit]; simp, huse⟩)
  · intro hlocal
    obtain ⟨e, hdrop⟩ := Passes.cseFinalSubPosSound hnd hmap
    cases hdrop with
    | @const bd preD postD idrop sigma d v hbD hseqD hsubstD =>
        cases hdef with
        | @op b0 _ yop0 args0 sigma0 hb0 hi0 hp =>
            have hiddefs : idrop.defs = [x] := by
              calc
                idrop.defs = (Passes.substInstr sigma idrop).defs :=
                  (Passes.substInstr_defs sigma idrop).symm
                _ = (Instr.const x v).defs := congrArg Instr.defs hsubstD
                _ = [x] := rfl
            have hidmem : idrop ∈ bd.instrs := by rw [hseqD]; simp
            have heq := instr_def_unique (d := x) hnd hbD hb0 hidmem hi0
              (by rw [hiddefs]; simp) (by simp [Instr.defs])
            subst idrop
            simp [Passes.substInstr] at hsubstD
    | @op bd preD postD idrop sigma d yopD argsD hbD hseqD hsubstD hnone hprefix =>
        have hiddefs : idrop.defs = [x] := by
          rw [← Passes.substInstr_defs sigma idrop, hsubstD]
          rfl
        obtain ⟨di, hdi⟩ := Passes.block_index_of_mem hbD
        have hxbd : x ∈ ToAsm.blockDefs bd := ToAsm.mem_blockDefs.mpr
          (Or.inr (List.mem_flatMap.mpr ⟨idrop, by rw [hseqD]; simp,
            by rw [hiddefs]; simp⟩))
        have hxb : x ∈ ToAsm.blockDefs b := ToAsm.mem_blockDefs.mpr (Or.inr hlocal)
        have hdicur : di = cur := Passes.block_def_index_unique hnd hdi hb hxbd hxb
        subst di
        have hbdb : bd = b := Option.some.inj (hdi.symm.trans hb)
        subst bd
        have hidmem : idrop ∈ pre ++ i :: post := by
          rw [← hsplit, hseqD]
          simp
        rcases List.mem_append.mp hidmem with hidpre | hidtail
        · exact List.mem_flatMap.mpr ⟨idrop, hidpre, by rw [hiddefs]; simp⟩
        · rcases List.mem_cons.mp hidtail with hideq | hidpost
          · subst idrop
            exfalso
            exact hself (by simp [hiddefs]) huse
          · by_cases hidpre : idrop ∈ pre
            · exact List.mem_flatMap.mpr ⟨idrop, hidpre, by rw [hiddefs]; simp⟩
            · have hne : idrop ≠ i := by
                intro heq
                subst idrop
                exact hself (by simp [hiddefs]) huse
              have himem : i ∈ preD :=
                mem_prefix_of_later hsplit hidpost hidpre hne hseqD
              exact False.elim (hprefix (List.mem_flatMap.mpr ⟨i, himem, huse⟩))

/-- Runtime entry-table transport along an actually taken CFG edge.  The only
nonempty case of `cseEntryTab` is a unique lower-index predecessor; the source
collector identifies that predecessor with the block just executed. -/
theorem CseTabRuntime.entry_of_edge {f : Func} (hnd : f.allDefs.Nodup)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {e : Edge} (he : e ∈ b.term.edges) {tb : Block}
    (htb : f.blocks[e.target]? = some tb)
    {R : Regs}
    (hr : CseTabRuntime (model := model) (Passes.cseSub f) R
      (Passes.cseBlockTabOut f cur))
    (vals : List U256) :
    CseTabRuntime (model := model) (Passes.cseSub f) (R.setMany tb.params vals)
      (Passes.cseEntryTab f (Passes.inEdgeSources f)
        (Passes.csePrefix f e.target).2.1 e.target) := by
  have ht : e.target < f.blocks.size := (Array.getElem?_eq_some_iff.mp htb).1
  have htbang : f.blocks[e.target]! = tb := by
    rw [Passes.getElem!_eq_getElem ht]
    exact (Array.getElem?_eq_some_iff.mp htb).2
  rw [Passes.cseEntryTab]
  split
  · exact CseTabRuntime.empty _ _
  · rename_i hentry
    cases hs : (Passes.inEdgeSources f)[e.target]! with
    | nil => exact CseTabRuntime.empty _ _
    | cons p ps =>
        cases ps with
        | cons q qs => exact CseTabRuntime.empty _ _
        | nil =>
            by_cases hp : p < e.target
            · simp only [hp, if_true]
              have hcurp : cur = p := Passes.inEdgeSources_single_eq hb he ht hs
              subst p
              rw [Passes.csePrefix_table_to hnd hp (Nat.le_of_lt ht)]
              simpa [Passes.cseSub, htbang] using
                (CseTabRuntime.setMany_inheritTab hnd
                  (Passes.cseFinalSubDefSound hnd) (block_mem_of_getElem? htb) hr vals)
            · simp only [hp, if_false]
              exact CseTabRuntime.empty _ _

end YulEvmCompiler.SsaCfg
