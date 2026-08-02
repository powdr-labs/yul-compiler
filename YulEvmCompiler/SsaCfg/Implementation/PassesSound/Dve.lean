import YulEvmCompiler.SsaCfg.Implementation.PassesSound.Cse
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.PassesSound.Dve

Pass 4 soundness: dead value elimination.

The filtered `getMany`/`setMany` lemmas for the pruned block parameters,
the block execution induction `dve_exec_aux`, and `dve_sound`.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal stepOp ExternalCalls
  ExternalCreates)
open YulSemantics (Outcome)
variable [model : ExternalModel]

/- **Pass 4 (dead value elimination) soundness.** No dominance hypothesis.

The proved simulation uses the invariant "`R` (original) and `R'` (optimized)
agree on every value in `Passes.liveSet f`"; the deleted instructions are
exactly those whose destinations nothing reads, so the invariant is preserved by
construction and no dominance is needed. `liveSet_closed` and
`dveBlock_uses_live` discharge the static liveness half.  The runtime half is
edge/parameter alignment: `dve` masks target parameters, incoming argument ids,
and hence the values returned by `Regs.getMany` at the same positions, so the
two filtered lists have equal length and `Regs.setMany` preserves agreement on
the live set. -/

namespace Passes

/-- The positional parameter predicate used by DVE on every incoming edge. -/
def dveKeepParam (f : Func) (bi : BlockId) (i : Nat) : Bool :=
  match f.blocks[bi]? with
  | some b =>
    match b.params[i]? with
    | some p => (liveSet f).contains p
    | none => true
  | none => true

/-- The edge and terminator portions of `dveBlock`, named for the execution
simulation below. -/
def dveEdge (f : Func) (e : Edge) : Edge :=
  { e with args :=
      (e.args.zipIdx.filter fun ai => dveKeepParam f e.target ai.2).map (·.1) }

def dveTerm (f : Func) (t : Term) : Term := mapEdges (dveEdge f) t

omit model in
theorem dveBlock_term (f : Func) (bi : BlockId) (b : Block) :
    (dveBlock f bi b).term = dveTerm f b.term := by
  rfl

omit model in
theorem dveBlock_instrs (f : Func) (bi : BlockId) (b : Block) :
    (dveBlock f bi b).instrs = b.instrs.filter (dveKeepInstr (liveSet f)) := by
  rfl

omit model in
/-- The slightly unusual `zipIdx` presentation of an edge mask is extensionally
the ordinary filtering of the zipped target parameters and edge arguments. -/
theorem dveEdge_args_eq_zip {f : Func} {e : Edge} {tb : Block}
    (htb : f.blocks[e.target]? = some tb)
    (hlen : e.args.length = tb.params.length) :
    (dveEdge f e).args =
      (tb.params.zip e.args |>.filter fun pa => (liveSet f).contains pa.1).map (·.2) := by
  simp only [dveEdge, dveKeepParam, htb]
  generalize tb.params = ps at hlen ⊢
  generalize e.args = xs at hlen ⊢
  induction xs generalizing ps with
  | nil =>
    have : ps = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    simp [this]
  | cons a as ih =>
    cases ps with
    | nil => simp at hlen
    | cons p ps =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp only [List.zipIdx_cons]
      rw [show as.zipIdx 1 = as.zipIdx.map (fun ai => (ai.1, 1 + ai.2)) by
        simpa using (List.zipIdx_eq_map_add (l := as) (i := 1))]
      simp only [List.getElem?_cons_zero, List.filter_cons, List.zip_cons_cons]
      simp only [List.filter_map]
      have hpred :
          ((fun ai : ValId × Nat =>
              match (p :: ps)[ai.2]? with
              | some p => (liveSet f).contains p
              | none => true) ∘ fun ai => (ai.1, 1 + ai.2)) =
            (fun ai : ValId × Nat =>
              match ps[ai.2]? with
              | some p => (liveSet f).contains p
              | none => true) := by
        funext ai
        simp [Nat.add_comm]
      rw [hpred]
      have hmap : ((fun x : ValId × Nat => x.1) ∘
          fun ai : ValId × Nat => (ai.1, 1 + ai.2)) =
          (fun x : ValId × Nat => x.1) := by rfl
      split
      · simp only [List.map_cons, List.map_map, hmap]
        exact congrArg (a :: ·) (ih ps hlen)
      · simp only [List.map_map, hmap]
        exact ih ps hlen

omit model in
/-- Reading an edge after masking it returns the correspondingly masked values. -/
theorem filterGetMany {live : Std.HashSet ValId} {R R' : Regs}
    {ps xs : List ValId} {vs : List U256}
    (hlen : xs.length = ps.length) (hget : R.getMany xs = some vs)
    (hagree : ∀ x ∈ live, R x = R' x)
    (hselected : ∀ x ∈ (ps.zip xs |>.filter fun pa => live.contains pa.1).map (·.2),
      x ∈ live) :
    R'.getMany ((ps.zip xs |>.filter fun pa => live.contains pa.1).map (·.2)) =
      some ((ps.zip vs |>.filter fun pv => live.contains pv.1).map (·.2)) := by
  induction ps generalizing xs vs with
  | nil =>
    have hxs : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst xs
    simp only [Regs.getMany_nil, Option.some.injEq] at hget
    subst vs
    rfl
  | cons p ps ih =>
    cases xs with
    | nil => simp at hlen
    | cons a xs =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      rw [Regs.getMany_cons] at hget
      cases ha : R a with
      | none => simp [ha] at hget
      | some v =>
        cases htail : R.getMany xs with
        | none => simp [ha, htail] at hget
        | some vals =>
          simp only [ha, htail, Option.bind_some, Option.map_some, Option.some.injEq] at hget
          subst vs
          by_cases hp : p ∈ live
          · have hpB : live.contains p = true := Std.HashSet.mem_iff_contains.mp hp
            have haLive : a ∈ live := hselected a (by simp [hpB])
            have ha' : R' a = some v := by rw [← hagree a haLive, ha]
            simpa [hpB, Regs.getMany_cons, ha'] using
              ih hlen htail (fun x hx => hselected x (by simp [hpB, hx]))
          · have hpB : live.contains p = false := by
              exact Bool.eq_false_of_not_eq_true (fun h => hp (Std.HashSet.contains_iff_mem.mp h))
            simpa [hpB] using ih hlen htail
              (fun x hx => hselected x (by simp [hpB, hx]))

omit model in
/-- Parallel binding by all target parameters agrees on live values with
binding only the live parameters and their positionally filtered values. -/
theorem filterSetMany {live : Std.HashSet ValId} {R R' : Regs}
    {ps : List ValId} {vs : List U256} (hnodup : ps.Nodup)
    (hlen : vs.length = ps.length) (hagree : ∀ x ∈ live, R x = R' x) :
    (ps.filter live.contains).length =
        ((ps.zip vs |>.filter fun pv => live.contains pv.1).map (·.2)).length
    ∧ ∀ x ∈ live,
      (R.setMany ps vs) x =
        (R'.setMany (ps.filter live.contains)
          ((ps.zip vs |>.filter fun pv => live.contains pv.1).map (·.2))) x := by
  induction ps generalizing R R' vs with
  | nil =>
    have hvs : vs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst vs
    exact ⟨rfl, hagree⟩
  | cons p ps ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      rw [List.nodup_cons] at hnodup
      by_cases hp : p ∈ live
      · have hpB : live.contains p = true := Std.HashSet.mem_iff_contains.mp hp
        obtain ⟨hlen', hagree'⟩ := ih hnodup.2 hlen (Regs.set_congr hagree p v)
        exact ⟨by simp [hpB, hlen'], by simpa [hpB, Regs.setMany_cons] using hagree'⟩
      · have hpB : live.contains p = false := by
          exact Bool.eq_false_of_not_eq_true (fun h => hp (Std.HashSet.contains_iff_mem.mp h))
        have hagreeHead : ∀ x ∈ live, (R.set p v) x = R' x := by
          intro x hx
          rw [Regs.set_other _ _ (by intro heq; subst x; exact hp hx)]
          exact hagree x hx
        obtain ⟨hlen', hagree'⟩ := ih hnodup.2 hlen hagreeHead
        exact ⟨by simpa [hpB] using hlen',
          by simpa [hpB, Regs.setMany_cons] using hagree'⟩

omit model in
theorem dveBlock_params {f : Func} {n : Nat} (hwf : f.wfCheck n = true)
    {bi : BlockId} {b : Block} (hb : f.blocks[bi]? = some b) :
    (dveBlock f bi b).params = b.params.filter (liveSet f).contains := by
  by_cases hi : bi = f.entry
  · subst bi
    unfold Func.wfCheck at hwf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
    have he := hwf.1.2
    rw [hb] at he
    have hempty : b.params = [] := List.isEmpty_iff.mp he
    simp [dveBlock, hempty]
  · simp [dveBlock, hi]

omit model in
theorem blockParams_nodup {f : Func} {n : Nat} (hwf : f.wfCheck n = true)
    {bi : BlockId} {b : Block} (hb : f.blocks[bi]? = some b) : b.params.Nodup := by
  have hnd := wfCheck_defs_nodup hwf
  have hbmem : b ∈ f.blocks.toList :=
    List.mem_of_getElem? (Array.getElem?_toList.trans hb)
  rw [List.nodup_iff_count_le_one]
  intro d
  have hall := List.nodup_iff_count_le_one.mp hnd d
  rw [allDefs_eq, List.count_append] at hall
  have hblock := count_le_count_flatMap
    (g := fun b : Block => blockAllDefs b) (d := d) hbmem
  change (b.params ++ b.instrs.flatMap Instr.defs).count d ≤
    (f.blocks.toList.flatMap blockAllDefs).count d at hblock
  rw [List.count_append] at hblock
  omega

omit model in
theorem dveInstr_uses_live {f : Func} {n : Nat} (hwf : f.wfCheck n = true)
    {bi : BlockId} {b : Block} (hb : f.blocks[bi]? = some b)
    {i : Instr} (hi : i ∈ b.instrs) (hkeep : dveKeepInstr (liveSet f) i = true)
    {x : ValId} (hx : x ∈ i.uses) : x ∈ liveSet f := by
  apply dveBlock_uses_live hwf hb
  rw [ToAsm.mem_blockUses]
  exact Or.inl (List.mem_flatMap.mpr
    ⟨i, List.mem_filter.mpr ⟨hi, hkeep⟩, hx⟩)

omit model in
theorem dveTerm_uses_live {f : Func} {n : Nat} (hwf : f.wfCheck n = true)
    {bi : BlockId} {b : Block} (hb : f.blocks[bi]? = some b)
    {x : ValId} (hx : x ∈ (dveTerm f b.term).uses) : x ∈ liveSet f := by
  apply dveBlock_uses_live hwf hb
  rw [ToAsm.mem_blockUses]
  exact Or.inr (by simpa [dveBlock_term] using hx)

omit model in
theorem dveEdge_args_live {f : Func} {n : Nat} (hwf : f.wfCheck n = true)
    {bi : BlockId} {b : Block} (hb : f.blocks[bi]? = some b)
    {e : Edge} (he : e ∈ b.term.edges) {x : ValId} (hx : x ∈ (dveEdge f e).args) :
    x ∈ liveSet f := by
  apply dveTerm_uses_live hwf hb
  cases ht : b.term with
  | jump ej =>
    simp only [ht, Term.edges, List.mem_singleton] at he
    subst ej
    simpa [dveTerm, mapEdges, Term.uses] using hx
  | branch c et ef =>
    simp only [ht, Term.edges, List.mem_cons] at he
    rcases he with rfl | he
    · simp [dveTerm, mapEdges, Term.uses, hx]
    · have he' : e = ef := by simpa using he
      subst e
      simp [dveTerm, mapEdges, Term.uses, hx]
  | ret vs => simp [ht, Term.edges] at he
  | halt yop as => simp [ht, Term.edges] at he

omit model in
theorem getMany_length_dve {R : Regs} {xs : List ValId} {vs : List U256}
    (h : R.getMany xs = some vs) : xs.length = vs.length := by
  induction xs generalizing vs with
  | nil => simp only [Regs.getMany_nil, Option.some.injEq] at h; subst vs; rfl
  | cons x xs ih =>
    rw [Regs.getMany_cons] at h
    cases hx : R x with
    | none => simp [hx] at h
    | some v =>
      cases hxs : R.getMany xs with
      | none => simp [hx, hxs] at h
      | some vals =>
        simp only [hx, hxs, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst vs
        simp [ih hxs]

/-- DVE simulates any suffix of a source block while the two register files
agree on the closed live set. -/
theorem dve_exec_aux {P : Prog} {f : Func} (hwf : f.wfCheck P.funcs.size = true)
    {R : Regs} {st : EvmState} {rest : Rest} {res : FRes}
    (hexec : Exec (model := model) P f R st rest res) :
    ∀ {bi : BlockId} {b : Block} {R' : Regs},
      f.blocks[bi]? = some b → rest.term = b.term → rest.instrs <:+ b.instrs →
      (∀ x ∈ liveSet f, R x = R' x) →
      Exec (model := model) P (dve f) R' st
        ⟨rest.instrs.filter (dveKeepInstr (liveSet f)), dveTerm f rest.term⟩ res := by
  induction hexec with
  | @const f R st d v is t res hnext ih =>
    intro bi b R' hb ht hs hagree
    have hs' : is <:+ b.instrs :=
      List.IsSuffix.trans (show is <:+ .const d v :: is from ⟨[.const d v], rfl⟩) hs
    by_cases hd : d ∈ liveSet f
    · have hdB : (liveSet f).contains d = true := Std.HashSet.mem_iff_contains.mp hd
      simp only [List.filter_cons, dveKeepInstr, hdB, if_true]
      exact Exec.const (ih hwf hb ht hs' (Regs.set_congr hagree d v))
    · have hdB : (liveSet f).contains d = false := by
        exact Bool.eq_false_of_not_eq_true (fun h => hd (Std.HashSet.contains_iff_mem.mp h))
      simp only [List.filter_cons, dveKeepInstr, hdB]
      apply ih hwf hb ht hs'
      intro x hx
      rw [Regs.set_other _ _ (by intro heq; subst x; exact hd hx)]
      exact hagree x hx
  | @op f R st st' ds yop as args rets is t res hget hbi hlen hnext ih =>
    intro bi b R' hb ht hs hagree
    have hs' : is <:+ b.instrs :=
      List.IsSuffix.trans (show is <:+ .op ds yop as :: is from ⟨[.op ds yop as], rfl⟩) hs
    have hi : .op ds yop as ∈ b.instrs := hs.mem (by simp)
    by_cases hk : (!pureOp yop || ds.any (liveSet f).contains) = true
    · have hargs : ∀ x ∈ as, x ∈ liveSet f := by
        intro x hx
        exact dveInstr_uses_live hwf hb hi (by simpa [dveKeepInstr] using hk)
          (by simpa [Instr.uses] using hx)
      have hget' : R'.getMany as = some args := by
        rw [← Regs.getMany_congr (R1 := R) (R2 := R')
          (fun x hx => hagree x (hargs x hx))]
        exact hget
      simp only [List.filter_cons, dveKeepInstr, hk, if_true]
      exact Exec.op hget' hbi hlen
        (ih hwf hb ht hs' (Regs.setMany_congr hagree ds rets))
    · have hk' : (!pureOp yop || ds.any (liveSet f).contains) = false :=
        Bool.eq_false_of_not_eq_true hk
      have hp : pureOp yop = true := by
        cases hpy : pureOp yop <;> simp_all
      have hds : ∀ x ∈ liveSet f, x ∉ ds := by
        intro x hx hxd
        have : ds.any (liveSet f).contains = true :=
          List.any_eq_true.mpr ⟨x, hxd, Std.HashSet.mem_iff_contains.mp hx⟩
        simp [this] at hk'
      have hst : st' = st := pure_state_eq hp hbi
      subst st'
      simp only [List.filter_cons, dveKeepInstr, hk']
      apply ih hwf hb ht hs'
      intro x hx
      rw [Regs.setMany_of_not_mem _ ds rets (hds x hx)]
      exact hagree x hx
  | @opHalt f R st st' ds yop as args is t hget hbi =>
    intro bi b R' hb ht hs hagree
    have hi : .op ds yop as ∈ b.instrs := hs.mem (by simp)
    have hkeep : (!pureOp yop || ds.any (liveSet f).contains) = true := by
      by_contra hk
      have hk' : (!pureOp yop || ds.any (liveSet f).contains) = false := by
        exact Bool.eq_false_of_not_eq_true hk
      have hp : pureOp yop = true := by
        cases hpy : pureOp yop <;> simp_all
      exact Passes.pure_no_halt hp hbi
    have hargs : ∀ x ∈ as, x ∈ liveSet f := by
      intro x hx
      exact dveInstr_uses_live hwf hb hi (by simpa [dveKeepInstr] using hkeep)
        (by simpa [Instr.uses] using hx)
    have hget' : R'.getMany as = some args := by
      rw [← Regs.getMany_congr (R1 := R) (R2 := R')
        (fun x hx => hagree x (hargs x hx))]
      exact hget
    simp only [List.filter_cons, dveKeepInstr, hkeep, if_true]
    exact Exec.opHalt hget' hbi
  | @call f g R st st' ds as fid args rvals eb is t res hfid hget hplen heb hbody hlen hnext ihbody ih =>
    intro bi b R' hb ht hs hagree
    have hs' : is <:+ b.instrs :=
      List.IsSuffix.trans (show is <:+ .call ds fid as :: is from ⟨[.call ds fid as], rfl⟩) hs
    have hi : .call ds fid as ∈ b.instrs := hs.mem (by simp)
    have hargs : ∀ x ∈ as, x ∈ liveSet f := by
      intro x hx
      exact dveInstr_uses_live hwf hb hi (by simp [dveKeepInstr])
        (by simpa [Instr.uses] using hx)
    have hget' : R'.getMany as = some args := by
      rw [← Regs.getMany_congr (R1 := R) (R2 := R')
        (fun x hx => hagree x (hargs x hx))]
      exact hget
    simp only [List.filter_cons, dveKeepInstr, if_true]
    exact Exec.call hfid hget' hplen heb hbody hlen
      (ih hwf hb ht hs' (Regs.setMany_congr hagree ds rvals))
  | @callHalt f g R st st' ds as fid args eb is t hfid hget hplen heb hbody ihbody =>
    intro bi b R' hb ht hs hagree
    have hi : .call ds fid as ∈ b.instrs := hs.mem (by simp)
    have hargs : ∀ x ∈ as, x ∈ liveSet f := by
      intro x hx
      exact dveInstr_uses_live hwf hb hi (by simp [dveKeepInstr])
        (by simpa [Instr.uses] using hx)
    have hget' : R'.getMany as = some args := by
      rw [← Regs.getMany_congr (R1 := R) (R2 := R')
        (fun x hx => hagree x (hargs x hx))]
      exact hget
    simp only [List.filter_cons, dveKeepInstr, if_true]
    exact Exec.callHalt hfid hget' hplen heb hbody
  | @jump f R st e tb vals res htb hget hlen hnext ih =>
    intro bi b R' hb ht hs hagree
    have he : e ∈ b.term.edges := by rw [← ht]; simp [Term.edges]
    have harity : e.args.length = tb.params.length := by
      rw [getMany_length_dve hget, hlen]
    have hedge := dveEdge_args_eq_zip htb harity
    have hselected :
        ∀ x ∈ (tb.params.zip e.args |>.filter fun pa => (liveSet f).contains pa.1).map (·.2),
          x ∈ liveSet f := by
      intro x hx
      apply dveEdge_args_live hwf hb he
      rw [hedge]
      exact hx
    have hget' := filterGetMany harity hget hagree hselected
    obtain ⟨hlen', hagree'⟩ := filterSetMany (blockParams_nodup hwf htb) hlen.symm hagree
    have htb' : (dve f).blocks[e.target]? = some (dveBlock f e.target tb) := by
      rw [dve_blocks_get, htb]
      rfl
    have hbody := ih hwf htb rfl (show tb.instrs <:+ tb.instrs from ⟨[], rfl⟩) hagree'
    have hout : Exec (model := model) P (dve f) R' st
        ⟨[], .jump (dveEdge f e)⟩ res := by
      refine Exec.jump (args :=
        (tb.params.zip vals |>.filter fun pv => (liveSet f).contains pv.1).map (·.2))
        htb' ?_ ?_ ?_
      · rw [hedge]
        exact hget'
      · rw [dveBlock_params hwf htb]
        exact hlen'
      · rw [dveBlock_params hwf htb]
        simpa [dveBlock_instrs, dveBlock_term] using hbody
    simpa [dveTerm, mapEdges] using hout
  | @branchTrue f R st c v et ef tb vals res hc hv htb hget hlen hnext ih =>
    intro bi b R' hb ht hs hagree
    have hcLive : c ∈ liveSet f := by
      apply dveTerm_uses_live hwf hb
      rw [← ht]
      simp [dveTerm, mapEdges, Term.uses]
    have hc' : R' c = some v := by rw [← hagree c hcLive]; exact hc
    have he : et ∈ b.term.edges := by rw [← ht]; simp [Term.edges]
    have harity : et.args.length = tb.params.length := by
      rw [getMany_length_dve hget, hlen]
    have hedge := dveEdge_args_eq_zip htb harity
    have hselected :
        ∀ x ∈ (tb.params.zip et.args |>.filter fun pa => (liveSet f).contains pa.1).map (·.2),
          x ∈ liveSet f := by
      intro x hx
      apply dveEdge_args_live hwf hb he
      rw [hedge]
      exact hx
    have hget' := filterGetMany harity hget hagree hselected
    obtain ⟨hlen', hagree'⟩ := filterSetMany (blockParams_nodup hwf htb) hlen.symm hagree
    have htb' : (dve f).blocks[et.target]? = some (dveBlock f et.target tb) := by
      rw [dve_blocks_get, htb]
      rfl
    have hbody := ih hwf htb rfl (show tb.instrs <:+ tb.instrs from ⟨[], rfl⟩) hagree'
    have hout : Exec (model := model) P (dve f) R' st
        ⟨[], .branch c (dveEdge f et) (dveEdge f ef)⟩ res := by
      refine Exec.branchTrue (v := v) (args :=
        (tb.params.zip vals |>.filter fun pv => (liveSet f).contains pv.1).map (·.2))
        hc' hv htb' ?_ ?_ ?_
      · rw [hedge]
        exact hget'
      · rw [dveBlock_params hwf htb]
        exact hlen'
      · rw [dveBlock_params hwf htb]
        simpa [dveBlock_instrs, dveBlock_term] using hbody
    simpa [dveTerm, mapEdges] using hout
  | @branchFalse f R st c et ef tb vals res hc htb hget hlen hnext ih =>
    intro bi b R' hb ht hs hagree
    have hcLive : c ∈ liveSet f := by
      apply dveTerm_uses_live hwf hb
      rw [← ht]
      simp [dveTerm, mapEdges, Term.uses]
    have hc' : R' c = some 0 := by rw [← hagree c hcLive]; exact hc
    have he : ef ∈ b.term.edges := by rw [← ht]; simp [Term.edges]
    have harity : ef.args.length = tb.params.length := by
      rw [getMany_length_dve hget, hlen]
    have hedge := dveEdge_args_eq_zip htb harity
    have hselected :
        ∀ x ∈ (tb.params.zip ef.args |>.filter fun pa => (liveSet f).contains pa.1).map (·.2),
          x ∈ liveSet f := by
      intro x hx
      apply dveEdge_args_live hwf hb he
      rw [hedge]
      exact hx
    have hget' := filterGetMany harity hget hagree hselected
    obtain ⟨hlen', hagree'⟩ := filterSetMany (blockParams_nodup hwf htb) hlen.symm hagree
    have htb' : (dve f).blocks[ef.target]? = some (dveBlock f ef.target tb) := by
      rw [dve_blocks_get, htb]
      rfl
    have hbody := ih hwf htb rfl (show tb.instrs <:+ tb.instrs from ⟨[], rfl⟩) hagree'
    have hout : Exec (model := model) P (dve f) R' st
        ⟨[], .branch c (dveEdge f et) (dveEdge f ef)⟩ res := by
      refine Exec.branchFalse (args :=
        (tb.params.zip vals |>.filter fun pv => (liveSet f).contains pv.1).map (·.2))
        hc' htb' ?_ ?_ ?_
      · rw [hedge]
        exact hget'
      · rw [dveBlock_params hwf htb]
        exact hlen'
      · rw [dveBlock_params hwf htb]
        simpa [dveBlock_instrs, dveBlock_term] using hbody
    simpa [dveTerm, mapEdges] using hout
  | @ret f R st xs vals hget =>
    intro bi b R' hb ht hs hagree
    have hxs : ∀ x ∈ xs, x ∈ liveSet f := by
      intro x hx
      apply dveTerm_uses_live hwf hb
      rw [← ht]
      simpa [dveTerm, mapEdges, Term.uses] using hx
    have hget' : R'.getMany xs = some vals := by
      rw [← Regs.getMany_congr (R1 := R) (R2 := R')
        (fun x hx => hagree x (hxs x hx))]
      exact hget
    simpa [dveTerm, mapEdges] using (Exec.ret (P := P) (f := dve f) hget')
  | @halt f R st st' yop as args hget hbi =>
    intro bi b R' hb ht hs hagree
    have has : ∀ x ∈ as, x ∈ liveSet f := by
      intro x hx
      apply dveTerm_uses_live hwf hb
      rw [← ht]
      simpa [dveTerm, mapEdges, Term.uses] using hx
    have hget' : R'.getMany as = some args := by
      rw [← Regs.getMany_congr (R1 := R) (R2 := R')
        (fun x hx => hagree x (has x hx))]
      exact hget
    simpa [dveTerm, mapEdges] using
      (Exec.halt (P := P) (f := dve f) hget' hbi)

end Passes

theorem dve_sound {P : Prog} {f : Func} {args : List U256} {st : EvmState} {res : FRes}
    {eb eb' : Block} (hwf : f.wfCheck P.funcs.size = true)
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.dve f).blocks[f.entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P (Passes.dve f) (Regs.empty.setMany f.params args) st
      ⟨eb'.instrs, eb'.term⟩ res := by
  rw [Passes.dve_blocks_get, heb] at heb'
  have hebEq : eb' = Passes.dveBlock f f.entry eb := by
    simpa using (Option.some.inj heb').symm
  subst eb'
  have hsim := Passes.dve_exec_aux hwf hexec heb rfl
    (show eb.instrs <:+ eb.instrs from ⟨[], rfl⟩)
    (fun _ _ => rfl)
  simpa [Passes.dveBlock_instrs, Passes.dveBlock_term] using hsim

end YulEvmCompiler.SsaCfg
