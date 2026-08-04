import YulEvmCompiler.SsaCfg.Implementation.PassesSound.Invert
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.PassesSound.CoalesceSound

Soundness of **straight-line block coalescing** (`Passes.coalesce`).

After the pass's restrictions the two sides are remarkably close: the
absorbed block `t` takes **no parameters**, so the edge into it carries no
parallel copy, and the merge only appends `t`'s instructions to `bi` and
adopts `t`'s terminator. The register file is therefore *identical* on both
sides, and the entire content of the proof is that one `Exec.jump` step is
elided:

```
  f:  … bi.instrs …  jump t   ↝   … t.instrs …  t.term
  g:  … bi.instrs        …………………… t.instrs …  t.term
```

The simulation carries one bit — whether we are currently inside `bi`,
whose remaining configuration in `g` is the original's with `t`'s body
appended. `mergeOK`'s sole-predecessor clause is what guarantees no other
edge ever reaches the blanked block.
-/

namespace YulEvmCompiler.SsaCfg

open YulSemantics.EVM (U256 EvmState Op builtinWithExternal stepOp ExternalCalls
  ExternalCreates)
open YulSemantics (Outcome)
variable [model : ExternalModel]

namespace Passes

/-- The `g`-side configuration corresponding to an `f`-side one: inside
`bi`, the absorbed block's body is still to come. -/
def coRest (f : Func) (t : BlockId) (inb : Bool) (rest : Rest) : Rest :=
  if inb then ⟨rest.instrs ++ f.blocks[t]!.instrs, f.blocks[t]!.term⟩ else rest

/-- What the current configuration must satisfy for the flag to be honest:
inside `bi` it is a suffix of `bi` ending in the `jump` to `t`; outside, no
outgoing edge may reach `t`. -/
def coInv (f : Func) (bi t : BlockId) (inb : Bool) (rest : Rest) : Prop :=
  if inb then rest.instrs <:+ f.blocks[bi]!.instrs ∧ rest.term = .jump ⟨t, []⟩
  else ∀ e ∈ rest.term.edges, e.target ≠ t

omit model in
@[simp] theorem coRest_false (f : Func) (t : BlockId) (rest : Rest) :
    coRest f t false rest = rest := rfl

omit model in
@[simp] theorem coRest_true (f : Func) (t : BlockId) (rest : Rest) :
    coRest f t true rest =
      ⟨rest.instrs ++ f.blocks[t]!.instrs, f.blocks[t]!.term⟩ := rfl

/-- The merged block: `bi`'s body followed by `t`'s, ending in `t`'s
terminator. -/
def mergedBlock (f : Func) (bi t : BlockId) : Block :=
  Block.mk f.blocks[bi]!.params (f.blocks[bi]!.instrs ++ f.blocks[t]!.instrs)
    f.blocks[t]!.term

omit model in
/-- The blocks `g` presents at each index. -/
theorem mergeOnce_block_get {f g : Func} {bi t : BlockId} (hok : mergeOK f bi t)
    (hgdef : g = { f with
      blocks := (f.blocks.set! bi (mergedBlock f bi t)).set! t blankBlock })
    {k : BlockId} {b : Block} (hk : f.blocks[k]? = some b) :
    g.blocks[k]? =
      some (if k = t then blankBlock else if k = bi then mergedBlock f bi t else b) := by
  obtain ⟨hbi, ht, -, hne, -, -, -⟩ := hok
  subst hgdef
  have hklt : k < f.blocks.size := (Array.getElem?_eq_some_iff.mp hk).1
  by_cases hkt : k = t
  · subst hkt
    simp [Array.set!, ht]
  · by_cases hkb : k = bi
    · subst hkb
      rw [if_neg hkt, if_pos rfl]
      simp only [Array.set!]
      rw [Array.getElem?_setIfInBounds_ne (Ne.symm hkt)]
      simp [hklt]
    · rw [if_neg hkt, if_neg hkb]
      simp only [Array.set!]
      rw [Array.getElem?_setIfInBounds_ne (Ne.symm hkt),
        Array.getElem?_setIfInBounds_ne (Ne.symm hkb)]
      exact hk

omit model in
theorem block_bang_of_get {f : Func} {k : BlockId} {b : Block}
    (h : f.blocks[k]? = some b) : f.blocks[k]! = b := by
  have hlt : k < f.blocks.size := (Array.getElem?_eq_some_iff.mp h).1
  rw [getElem!_eq_getElem hlt]
  exact Option.some.inj ((Array.getElem?_eq_getElem hlt).symm.trans h)

omit model in
/-- Entering block `k` afresh, the flag and invariant are determined by
whether `k` is the merge's source. -/
theorem coInv_entry {f : Func} {bi t : BlockId} (hok : mergeOK f bi t)
    {k : BlockId} {b : Block} (hk : f.blocks[k]? = some b) :
    coInv f bi t (decide (k = bi)) ⟨b.instrs, b.term⟩ := by
  obtain ⟨hbi, ht, -, hne, hjump, -, hsole⟩ := hok
  have hklt : k < f.blocks.size := (Array.getElem?_eq_some_iff.mp hk).1
  have hbk : f.blocks[k]! = b := by
    rw [getElem!_eq_getElem hklt, Array.getElem?_eq_getElem hklt] at *
    exact Option.some.inj hk
  by_cases hkb : k = bi
  · subst hkb
    simp only [decide_true, coInv, if_true]
    rw [← hbk]
    exact ⟨List.suffix_refl _, hjump⟩
  · simp only [hkb, decide_false, coInv]
    intro e he hetarget
    exact hsole k hklt hkb e (by rw [hbk]; exact he) hetarget

end Passes

open Passes in
/-- **The merge simulation.** One `Exec.jump` is elided: inside `bi` the
`g`-side configuration already carries `t`'s body, so when the original
takes that edge the two sides coincide with no step consumed. -/
theorem mergeOnce_exec_aux {P : Prog} {bi t : BlockId} {f : Func}
    {R : Regs} {st : EvmState} {rest : Rest} {res : FRes}
    (h : Exec (model := model) P f R st rest res) :
    ∀ (g : Func), mergeOK f bi t →
      g = { f with
        blocks := (f.blocks.set! bi (mergedBlock f bi t)).set! t blankBlock } →
      ∀ inb : Bool, coInv f bi t inb rest →
        Exec (model := model) P g R st (coRest f t inb rest) res := by
  induction h with
  | @const f R st d v is tm res htail ih =>
    intro g hok hgdef inb hinv
    cases inb
    · exact Exec.const (ih g hok hgdef false (by simpa [coInv] using hinv))
    · have hinv' : (Instr.const d v :: is) <:+ f.blocks[bi]!.instrs
          ∧ tm = Term.jump ⟨t, []⟩ := by simpa [coInv] using hinv
      exact Exec.const (ih g hok hgdef true
        ⟨(List.suffix_cons _ _).trans hinv'.1, hinv'.2⟩)
  | @op f R st st' ds yop as argsv rets is tm res hg hbi' hlen htail ih =>
    intro g hok hgdef inb hinv
    cases inb
    · exact Exec.op hg hbi' hlen (ih g hok hgdef false (by simpa [coInv] using hinv))
    · have hinv' : (Instr.op ds yop as :: is) <:+ f.blocks[bi]!.instrs
          ∧ tm = Term.jump ⟨t, []⟩ := by simpa [coInv] using hinv
      exact Exec.op hg hbi' hlen (ih g hok hgdef true
        ⟨(List.suffix_cons _ _).trans hinv'.1, hinv'.2⟩)
  | @opHalt f R st st' ds yop as argsv is tm hg hbi' =>
    intro g hok hgdef inb hinv
    cases inb <;> exact Exec.opHalt hg hbi'
  | @call f gf R st st' ds as fid argsv rvals eb is tm res hfid hg hplen heb hbody
      hlen htail ihbody ih =>
    intro g hok hgdef inb hinv
    cases inb
    · exact Exec.call hfid hg hplen heb hbody hlen
        (ih g hok hgdef false (by simpa [coInv] using hinv))
    · have hinv' : (Instr.call ds fid as :: is) <:+ f.blocks[bi]!.instrs
          ∧ tm = Term.jump ⟨t, []⟩ := by simpa [coInv] using hinv
      exact Exec.call hfid hg hplen heb hbody hlen
        (ih g hok hgdef true ⟨(List.suffix_cons _ _).trans hinv'.1, hinv'.2⟩)
  | @callHalt f gf R st st' ds as fid argsv eb is tm hfid hg hplen heb hbody ihbody =>
    intro g hok hgdef inb hinv
    cases inb <;> exact Exec.callHalt hfid hg hplen heb hbody
  | @jump f R st e tb argsv res htb hga hlen htail ih =>
    intro g hok hgdef inb hinv
    have htlt : t < f.blocks.size := hok.2.1
    have htne : t ≠ bi := hok.2.2.2.1
    cases inb
    · -- an ordinary edge; by `mergeOK` it cannot reach the blanked block
      have hall : ∀ x ∈ (Term.jump e).edges, x.target ≠ t := by simpa [coInv] using hinv
      have hne : e.target ≠ t := hall e (by simp [Term.edges])
      have hkb := mergeOnce_block_get hok hgdef htb
      rw [if_neg hne] at hkb
      have hentry := coInv_entry hok htb
      by_cases hbi2 : e.target = bi
      · rw [if_pos hbi2] at hkb
        have hbik : f.blocks[bi]! = tb :=
          block_bang_of_get (by rw [← hbi2]; exact htb)
        have hpar : (mergedBlock f bi t).params = tb.params := by
          simp [mergedBlock, hbik]
        refine Exec.jump hkb hga (by rw [hpar]; exact hlen) ?_
        have hih := ih g hok hgdef true (by simpa [coInv, hbi2] using hentry)
        rw [hpar]
        simpa [coRest, mergedBlock, hbik] using hih
      · rw [if_neg hbi2] at hkb
        exact Exec.jump hkb hga hlen
          (ih g hok hgdef false (by simpa [coInv, hbi2] using hentry))
    · -- inside `bi`: this is the merged edge, and it disappears
      have hinv' : ([] : List Instr) <:+ f.blocks[bi]!.instrs
          ∧ Term.jump e = Term.jump ⟨t, []⟩ := by simpa [coInv] using hinv
      obtain ⟨-, htm⟩ := hinv'
      have hetarget : e = ⟨t, []⟩ := by injection htm
      subst hetarget
      have htbeq : f.blocks[t]! = tb := block_bang_of_get htb
      have hargs : argsv = [] := by simpa using hga.symm
      subst hargs
      have hpar : tb.params = [] := by
        have := hok.2.2.2.2.2.1
        rw [htbeq] at this; exact this
      have hih := ih g hok hgdef false (by
        simpa [coInv, htne] using coInv_entry hok htb)
      simp only [coRest, if_true, List.nil_append, htbeq]
      simpa [hpar, Regs.setMany] using hih
  | @branchTrue f R st c v et ef tb argsv res hc hv htb hga hlen htail ih =>
    intro g hok hgdef inb hinv
    cases inb
    · have hne : et.target ≠ t :=
        (by simpa [coInv] using hinv :
            ∀ x ∈ (Term.branch c et ef).edges, x.target ≠ t)
          et (by simp [Term.edges])
      have hkb := mergeOnce_block_get hok hgdef htb
      rw [if_neg hne] at hkb
      have hentry := coInv_entry hok htb
      by_cases hbi2 : et.target = bi
      · rw [if_pos hbi2] at hkb
        have hbik : f.blocks[bi]! = tb :=
          block_bang_of_get (by rw [← hbi2]; exact htb)
        have hpar : (mergedBlock f bi t).params = tb.params := by
          simp [mergedBlock, hbik]
        refine Exec.branchTrue hc hv hkb hga (by rw [hpar]; exact hlen) ?_
        have hih := ih g hok hgdef true (by simpa [coInv, hbi2] using hentry)
        rw [hpar]
        simpa [coRest, mergedBlock, hbik] using hih
      · rw [if_neg hbi2] at hkb
        exact Exec.branchTrue hc hv hkb hga hlen
          (ih g hok hgdef false (by simpa [coInv, hbi2] using hentry))
    · simp [coInv] at hinv
  | @branchFalse f R st c et ef tb argsv res hc htb hga hlen htail ih =>
    intro g hok hgdef inb hinv
    cases inb
    · have hne : ef.target ≠ t :=
        (by simpa [coInv] using hinv :
            ∀ x ∈ (Term.branch c et ef).edges, x.target ≠ t)
          ef (by simp [Term.edges])
      have hkb := mergeOnce_block_get hok hgdef htb
      rw [if_neg hne] at hkb
      have hentry := coInv_entry hok htb
      by_cases hbi2 : ef.target = bi
      · rw [if_pos hbi2] at hkb
        have hbik : f.blocks[bi]! = tb :=
          block_bang_of_get (by rw [← hbi2]; exact htb)
        have hpar : (mergedBlock f bi t).params = tb.params := by
          simp [mergedBlock, hbik]
        refine Exec.branchFalse hc hkb hga (by rw [hpar]; exact hlen) ?_
        have hih := ih g hok hgdef true (by simpa [coInv, hbi2] using hentry)
        rw [hpar]
        simpa [coRest, mergedBlock, hbik] using hih
      · rw [if_neg hbi2] at hkb
        exact Exec.branchFalse hc hkb hga hlen
          (ih g hok hgdef false (by simpa [coInv, hbi2] using hentry))
    · simp [coInv] at hinv
  | @ret f R st xs vals hv =>
    intro g hok hgdef inb hinv
    cases inb
    · exact Exec.ret hv
    · simp [coInv] at hinv
  | @halt f R st st' yop as argsv hga hbi' =>
    intro g hok hgdef inb hinv
    cases inb
    · exact Exec.halt hga hbi'
    · simp [coInv] at hinv

open Passes in
/-- One merge preserves the function's observable execution. -/
theorem mergeOnce_sound {P : Prog} {f g : Func} {args : List U256}
    {st : EvmState} {res : FRes} {eb eb' : Block}
    (hmg : Passes.mergeOnce f = some g)
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : g.blocks[g.entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P g (Regs.empty.setMany g.params args) st
      ⟨eb'.instrs, eb'.term⟩ res := by
  obtain ⟨bi, t, hok, hgdef⟩ := Passes.mergeOnce_inv hmg
  have hent : g.entry = f.entry := Passes.mergeOnce_entry hmg
  have hpar : g.params = f.params := (Passes.mergeOnce_fields hmg).1
  have hgb := Passes.mergeOnce_block_get hok hgdef heb
  rw [hent] at heb'
  have hte : f.entry ≠ t := fun hc => hok.2.2.1 hc.symm
  rw [if_neg (fun hc : f.entry = t => hte hc)] at hgb
  have haux := mergeOnce_exec_aux hexec g hok hgdef (decide (f.entry = bi))
    (Passes.coInv_entry hok heb)
  rw [hpar]
  by_cases hbi : f.entry = bi
  · rw [if_pos hbi] at hgb
    obtain rfl : eb' = Passes.mergedBlock f bi t :=
      Option.some.inj (heb'.symm.trans hgb)
    have hbik : f.blocks[bi]! = eb := Passes.block_bang_of_get (by rw [← hbi]; exact heb)
    simpa [hbi, Passes.coRest, Passes.mergedBlock, hbik] using haux
  · rw [if_neg hbi] at hgb
    obtain rfl : eb' = eb := Option.some.inj (heb'.symm.trans hgb)
    simpa [hbi, Passes.coRest] using haux

/-- The simulation property lifted along the coalescing loop. -/
def ExecSim (f g : Func) : Prop :=
  ∀ {P : Prog} {args : List U256} {st : EvmState} {res : FRes} {eb eb' : Block},
    f.blocks[f.entry]? = some eb → g.blocks[g.entry]? = some eb' →
    Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res →
    Exec (model := model) P g (Regs.empty.setMany g.params args) st
      ⟨eb'.instrs, eb'.term⟩ res

open Passes in
theorem coalesceRaw_sound {f : Func} (hentry : ∃ b, f.blocks[f.entry]? = some b) :
    (∃ b, (coalesceRaw f).blocks[(coalesceRaw f).entry]? = some b)
      ∧ ExecSim (model := model) f (coalesceRaw f) := by
  refine coalesceRaw_induction
    (motive := fun g => (∃ b, g.blocks[g.entry]? = some b)
      ∧ ExecSim (model := model) f g) f ⟨hentry, ?_⟩ ?_
  · intro P args st res eb eb' h1 h2 hx
    obtain rfl : eb' = eb := Option.some.inj (h2.symm.trans h1)
    exact hx
  · rintro g g' ⟨⟨b, hb⟩, hsim⟩ hmg
    have hent : g'.entry = g.entry := mergeOnce_entry hmg
    obtain ⟨bi, t, hok, hgdef⟩ := Passes.mergeOnce_inv hmg
    have hgb := mergeOnce_block_get hok hgdef hb
    refine ⟨⟨_, by rw [hent]; exact hgb⟩, ?_⟩
    intro P args st res eb eb' h1 h2 hx
    exact mergeOnce_sound hmg hb h2 (hsim h1 hb hx)

open Passes in
/-- **Soundness of straight-line block coalescing.** -/
theorem coalesce_sound {P : Prog} {f : Func} {args : List U256}
    {st : EvmState} {res : FRes} {eb eb' : Block}
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.coalesce f).blocks[(Passes.coalesce f).entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P (Passes.coalesce f)
      (Regs.empty.setMany (Passes.coalesce f).params args) st
      ⟨eb'.instrs, eb'.term⟩ res := by
  rcases Passes.coalesce_cases f with ⟨hcoal, -, -⟩ | hcoal
  · rw [hcoal] at heb' ⊢
    exact (coalesceRaw_sound (model := model) ⟨eb, heb⟩).2 heb heb' hexec
  · rw [hcoal] at heb' ⊢
    obtain rfl : eb' = eb := Option.some.inj (heb'.symm.trans heb)
    exact hexec

end YulEvmCompiler.SsaCfg
