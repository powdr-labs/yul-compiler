import YulEvmCompiler.SsaCfg.Implementation.PassesSound.Invert
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.PassesSound.Pipeline

Dominance preservation, and the pipeline theorem.

`elimTrivialParams_dom`, `constFold_dom`, `cse_dom`, `dve_dom` (with the
counterexample showing `dve` can *lose* `domCheck`), the whole-program
replay `runOnceProg_sound`, and `optimizeProg_sound'`.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal stepOp ExternalCalls
  ExternalCreates)
open YulSemantics (Outcome)
variable [model : ExternalModel]

/-! ### Dominance preservation

Not needed for top-level soundness — `optimizeProg`'s gate re-checks
`wfCheck && domCheck` on the output and falls back otherwise
(`optimizeProg_sound_of_fallback`, proved) — but needed to *compose* the four
pass lemmas inside `runOnce`, and the reason the gate essentially never fires in
practice. Each pass only ever removes definitions or reroutes a use to a value
that already dominates it, so `liveIn(entry)` can only shrink; the proofs are
computations on `ToAsm.liveInSets` of the rewritten function, in the same style
as `ToAsm.liveIn_of_uses`/`liveIn_of_succ`. -/

omit model in
/-- One removal uses a custom pre-fixed point: the substituted old live-in
sets, plus `v` at the selected block.  `_edge` supplies `v` as an old use on
non-self predecessors and carries the added availability around self loops;
`block_def_index_unique` handles the removed definition.  The public theorem
below iterates this fact while preserving `allDefs.Nodup`. -/
private theorem elimTrivialParam_one_dom {f : Func} (hnd : f.allDefs.Nodup)
    (hdom : ToAsm.Func.domCheck f = true) {bi i p v : Nat}
    (hfind : Passes.findTrivialParam f = some (bi, i, p, v)) :
    ToAsm.Func.domCheck (Passes.substFunc ((∅ : Passes.Subst).insert p v)
      (Passes.removeParam f bi i)) = true := by
  let σ : ValId → ValId := Passes.substV ((∅ : Passes.Subst).insert p v)
  let g := Passes.substFunc ((∅ : Passes.Subst).insert p v)
    (Passes.removeParam f bi i)
  obtain ⟨hbi, hbientry, hi, hpget, -, -, hsingle, -⟩ :=
    Passes.findTrivialParam_inv hfind
  have hbang : f.blocks[bi]! = f.blocks[bi] := by
    rw [Passes.getElem!_eq_getElem hbi]
  have hi' : i < f.blocks[bi].params.length := by simpa [hbang] using hi
  have hpEq : f.blocks[bi].params[i] = p := by
    have hpget' := hpget
    rw [hbang] at hpget'
    simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi'] using hpget'
  have hpgetQ : f.blocks[bi].params[i]? = some p := by
    rw [List.getElem?_eq_getElem hi', hpEq]
  have hbsel : f.blocks[bi]? = some f.blocks[bi] :=
    Array.getElem?_eq_getElem hbi
  have hpmem : p ∈ ToAsm.blockDefs f.blocks[bi] := by
    rw [ToAsm.mem_blockDefs]
    left
    rw [← hpEq]
    exact List.getElem_mem hi'
  have hpnot : p ∉ f.params := by
    intro hp
    have hpflat : p ∈ f.blocks.toList.flatMap blockAllDefs := by
      apply List.mem_flatMap.mpr
      refine ⟨f.blocks[bi], ?_, ?_⟩
      · exact List.mem_iff_getElem.mpr ⟨bi, by simpa using hbi, rfl⟩
      · apply List.mem_append_left
        rw [← hpEq]
        exact List.getElem_mem hi'
    exact (List.nodup_append.mp hnd).2.2 p hp p hpflat rfl
  have hσparam : ∀ x ∈ f.params, σ x = x := by
    intro x hx
    have hxp : x ≠ p := fun h => hpnot (h ▸ hx)
    simp [σ, Passes.substV_single, hxp]
  have hvp : v ≠ p := by
    intro hvp
    subst v
    have hm : p ∈ (((Passes.inEdgeArgs f)[bi]!.filterMap (·[i]?)).filter
        (· != p)).eraseDups := by simp [hsingle]
    have hm' := List.mem_filter.mp (List.mem_eraseDups.mp hm)
    simpa using hm'.2
  obtain ⟨li, hli⟩ := ToAsm.liveInSets_isSome f
  obtain ⟨li', hli'⟩ := ToAsm.liveInSets_isSome g
  let ub : Array (List ValId) := Array.ofFn fun j : Fin f.blocks.size =>
    ToAsm.unionS ((li[j.1]?.getD []).map σ) (if j.1 = bi then [v] else [])
  have mem_ub (j : Nat) (x : ValId) :
      x ∈ ub[j]?.getD [] ↔ j < f.blocks.size ∧
        ((∃ y ∈ li[j]?.getD [], σ y = x) ∨ (j = bi ∧ x = v)) := by
    by_cases hj : j < f.blocks.size
    · rw [Array.getElem?_eq_getElem (by simpa [ub] using hj)]
      simp only [Option.getD_some, ub, Array.getElem_ofFn, ToAsm.mem_unionS,
        List.mem_map]
      constructor
      · intro hx
        refine ⟨hj, ?_⟩
        by_cases hji : j = bi
        · simpa [hji] using hx
        · simpa [hji] using hx
      · rintro ⟨-, hx⟩
        by_cases hji : j = bi
        · simpa [hji] using hx
        · simpa [hji] using hx
    · rw [Array.getElem?_eq_none_iff.mpr (by simpa [ub] using Nat.not_lt.mp hj)]
      simp [hj]
  have hsize : g.blocks.size = f.blocks.size := by simp [g, Passes.substFunc,
    Passes.removeParam]
  have hub : ToAsm.Sub (ToAsm.liveStep g ub) ub := by
    intro j x hx
    rcases hb' : g.blocks[j]? with _ | b'
    · rw [ToAsm.liveStep_get_none hb'] at hx
      simp at hx
    · have hjg : j < g.blocks.size := (Array.getElem?_eq_some_iff.mp hb').1
      have hj : j < f.blocks.size := by simpa [hsize] using hjg
      let b := f.blocks[j]
      have hb : f.blocks[j]? = some b := Array.getElem?_eq_getElem hj
      have hbraw := Passes.elimStep_blocks_get (bi := bi) (i := i) (p := p) (v := v) hb
      rw [hb'] at hbraw
      have hb'eq : b' = Passes.substBlock ((∅ : Passes.Subst).insert p v)
          (Passes.removedBlock bi i j b) := Option.some.inj hbraw
      subst b'
      rw [ToAsm.liveStep_get_eq hb', ToAsm.mem_diffS] at hx
      rw [mem_ub]
      refine ⟨hj, ?_⟩
      have resolveDef {y : ValId} (hydef : y ∈ ToAsm.blockDefs b)
          (hσyx : σ y = x) :
          (∃ z ∈ li[j]?.getD [], σ z = x) ∨ (j = bi ∧ x = v) := by
        by_cases hyp : y = p
        · subst y
          have hji := Passes.block_def_index_unique hnd hb hbsel hydef hpmem
          exact Or.inr ⟨hji, by simpa [σ, Passes.substV_single] using hσyx.symm⟩
        · have hyraw : y ∈ ToAsm.blockDefs (Passes.removedBlock bi i j b) := by
            by_cases hji : j = bi
            · subst j
              have hbeq : b = f.blocks[bi] := Option.some.inj (hb.symm.trans hbsel)
              subst b
              apply Passes.mem_removedBlock_defs (x := y) (p := p)
              · exact hpgetQ
              · exact hydef
              · exact hyp
            · rw [ToAsm.mem_blockDefs] at hydef ⊢
              simpa [Passes.removedBlock, hji] using hydef
          have hyout := Passes.mem_substBlock_defs
            (σ := ((∅ : Passes.Subst).insert p v)) hyraw
          have hσy : σ y = y := by simp [σ, Passes.substV_single, hyp]
          exact absurd (hσy ▸ hyout) (hσyx ▸ hx.2)
      rcases ToAsm.mem_unionS.mp hx.1 with hu | hl
      · obtain ⟨y, hyraw, hσyx⟩ := Passes.substBlock_use hu
        have hyuse := Passes.removedBlock_use hyraw
        by_cases hydef : y ∈ ToAsm.blockDefs b
        · exact resolveDef hydef hσyx
        · exact Or.inl ⟨y, ToAsm.liveIn_of_uses hli hb hyuse hydef, hσyx⟩
      · rcases ToAsm.mem_lout.mp hl with ⟨e, he, hxe⟩ | hnil
        · have het : ∃ e0 ∈ b.term.edges, e0.target = e.target := by
            obtain ⟨er, her, hert⟩ := Passes.substTerm_edge
              (t := (Passes.removedBlock bi i j b).term) he
            obtain ⟨e0, he0, he0t⟩ := Passes.removedBlock_edge her
            exact ⟨e0, he0, he0t.trans hert⟩
          obtain ⟨e0, he0, he0t⟩ := het
          rw [mem_ub] at hxe
          rcases hxe.2 with ⟨y, hy, hσyx⟩ | ⟨hetbi, hxv⟩
          · by_cases hydef : y ∈ ToAsm.blockDefs b
            · exact resolveDef hydef hσyx
            · exact Or.inl ⟨y, ToAsm.liveIn_of_succ hli hb he0
                (by rw [he0t]; exact hy) hydef, hσyx⟩
          · by_cases hji : j = bi
            · exact Or.inr ⟨hji, hxv⟩
            · have he0bi : e0.target = bi := he0t.trans hetbi
              obtain ⟨a, ha, hapv, hapself⟩ :=
                Passes.findTrivialParam_edge hfind hb he0 he0bi
              have hav : a = v := by
                rcases hapv with rfl | hav
                · exact absurd (hapself rfl) hji
                · exact hav
              have hvuse : v ∈ ToAsm.blockUses b := by
                rw [ToAsm.mem_blockUses]
                right
                have : v ∈ e0.args := by
                  subst a
                  exact List.mem_iff_getElem?.mpr ⟨i, ha⟩
                cases ht : b.term with
                | jump ej =>
                    simp only [ht, Term.edges, List.mem_singleton] at he0
                    subst e0
                    simpa [ht, Term.uses] using this
                | branch c et ef =>
                    simp only [ht, Term.edges, List.mem_cons] at he0
                    rcases he0 with rfl | he0
                    · simp [Term.uses, this]
                    · have : e0 = ef := by simpa using he0
                      subst e0
                      simp [Term.uses, this]
                | ret xs => simp [ht, Term.edges] at he0
                | halt yop as => simp [ht, Term.edges] at he0
              by_cases hvdef : v ∈ ToAsm.blockDefs b
              · have hvraw : v ∈ ToAsm.blockDefs
                    (Passes.removedBlock bi i j b) := by
                  rw [ToAsm.mem_blockDefs] at hvdef ⊢
                  simpa [Passes.removedBlock, hji] using hvdef
                have hvout := Passes.mem_substBlock_defs
                  (σ := ((∅ : Passes.Subst).insert p v)) hvraw
                exact absurd (hxv ▸ hvout) hx.2
              · exact Or.inl ⟨v, ToAsm.liveIn_of_uses hli hb hvuse hvdef,
                  by simpa [σ, Passes.substV_single, hvp] using hxv.symm⟩
        · simp at hnil
  have hsub : ToAsm.Sub li' ub := ToAsm.liveInSets_least hli' hub
  unfold ToAsm.Func.domCheck
  rw [hli']
  simp only [decide_eq_true_eq]
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  rw [ToAsm.mem_diffS] at hx
  have hxub := hsub _ _ hx.1
  rw [mem_ub] at hxub
  rcases hxub.2 with ⟨y, hy, hσyx⟩ | ⟨hentry, -⟩
  · have hyp := ToAsm.domCheck_entry hli hdom hy
    have hyx : y = x := (hσparam y hyp).symm.trans hσyx
    exact hx.2 (by simpa [g, Passes.substFunc, Passes.removeParam] using hyx ▸ hyp)
  · exact hbientry hentry.symm

omit model in
theorem elimTrivialParams_dom {f : Func} (hwf : f.wfCheck n = true)
    (hdom : ToAsm.Func.domCheck f = true) :
    ToAsm.Func.domCheck (Passes.elimTrivialParams f) = true := by
  have hnd : f.allDefs.Nodup := by
    unfold Func.wfCheck at hwf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
    exact hwf.1.1.1
  have loopInv : ∀ (xs : List Nat) (r : Passes.ElimTrivialLoopState),
      r.2.allDefs.Nodup → ToAsm.Func.domCheck r.2 = true →
      r.1.getD r.2 = r.2 →
      let out := loopWith Passes.elimTrivialStep xs r
      out.2.allDefs.Nodup ∧ ToAsm.Func.domCheck out.2 = true ∧
        out.1.getD out.2 = out.2 := by
    intro xs
    induction xs with
    | nil =>
        intro r hrnd hrdom hr
        exact ⟨hrnd, hrdom, hr⟩
    | cons k ks ih =>
        intro r hrnd hrdom hr
        rw [loopWith_cons]
        unfold Passes.elimTrivialStep
        cases hfind : Passes.findTrivialParam r.2 with
        | none =>
            exact ⟨hrnd, hrdom, by simp⟩
        | some q =>
            obtain ⟨bi, i, p, v⟩ := q
            apply ih
            · rw [Passes.substFunc_allDefs]
              exact hrnd.sublist (Passes.removeParam_allDefs_sublist r.2 bi i)
            · exact elimTrivialParam_one_dom hrnd hrdom hfind
            · rfl
  rw [Passes.elimTrivialParams_eq_loop]
  let r := loopWith Passes.elimTrivialStep
    (List.range' 0 (Passes.elimTrivialFuel f) 1) ⟨none, f⟩
  have hr := loopInv (List.range' 0 (Passes.elimTrivialFuel f) 1)
    (⟨none, f⟩ : Passes.ElimTrivialLoopState) hnd hdom rfl
  change r.2.allDefs.Nodup ∧ ToAsm.Func.domCheck r.2 = true ∧
    r.1.getD r.2 = r.2 at hr
  rw [hr.2.2]
  exact hr.2.1

/-- **Pass 1 (trivial block-parameter elimination) soundness.**  The loop
threads the one-removal lockstep theorem together with single-assignment and
dominance preservation. -/
theorem elimTrivialParams_sound {P : Prog} {f : Func} {args : List U256}
    {st : EvmState} {res : FRes} {eb eb' : Block}
    (hwf : f.wfCheck P.funcs.size = true)
    (hdom : ToAsm.Func.domCheck f = true)
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.elimTrivialParams f).blocks[f.entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P (Passes.elimTrivialParams f)
      (Regs.empty.setMany f.params args) st ⟨eb'.instrs, eb'.term⟩ res := by
  have hnd : f.allDefs.Nodup := wfCheck_defs_nodup hwf
  have loopSound : ∀ (xs : List Nat) (r : Passes.ElimTrivialLoopState),
      r.2.params = f.params → r.2.entry = f.entry →
      r.2.allDefs.Nodup → ToAsm.Func.domCheck r.2 = true →
      r.1.getD r.2 = r.2 →
      ∀ {b : Block}, r.2.blocks[f.entry]? = some b →
        Exec (model := model) P r.2 (Regs.empty.setMany f.params args) st
          ⟨b.instrs, b.term⟩ res →
        let out := loopWith Passes.elimTrivialStep xs r
        ∃ b', out.2.blocks[f.entry]? = some b' ∧
          Exec (model := model) P out.2 (Regs.empty.setMany f.params args) st
            ⟨b'.instrs, b'.term⟩ res ∧
          out.1.getD out.2 = out.2 := by
    intro xs
    induction xs with
    | nil =>
        intro r hparams hentry hrnd hrdom hr b hb hrun
        exact ⟨b, hb, hrun, hr⟩
    | cons n ns ih =>
        intro r hparams hentry hrnd hrdom hr b hb hrun
        rw [loopWith_cons]
        unfold Passes.elimTrivialStep
        cases hfind : Passes.findTrivialParam r.2 with
        | none =>
            exact ⟨b, hb, hrun, by simp⟩
        | some q =>
            obtain ⟨bi, k, p, v⟩ := q
            let g := Passes.substFunc ((∅ : Passes.Subst).insert p v)
              (Passes.removeParam r.2 bi k)
            have hentryCur : r.2.entry = f.entry := hentry
            have hbcur : r.2.blocks[r.2.entry]? = some b := by simpa [hentryCur] using hb
            have hrunCur : Exec (model := model) P r.2
                (Regs.empty.setMany r.2.params args) st ⟨b.instrs, b.term⟩ res := by
              simpa [hparams] using hrun
            have hentrylt : r.2.entry < g.blocks.size := by
              simpa [g, Passes.substFunc, Passes.removeParam] using
                (Array.getElem?_eq_some_iff.mp hbcur).1
            let b' := g.blocks[r.2.entry]
            have hb' : g.blocks[r.2.entry]? = some b' := by
              exact Array.getElem?_eq_getElem hentrylt
            have hrun' := elimTrivialParam_one_sound hrnd hrdom hfind
              hbcur hb' hrunCur
            apply ih (⟨none, g⟩ : Passes.ElimTrivialLoopState)
            · simpa [g, Passes.substFunc, Passes.removeParam] using hparams
            · simpa [g, Passes.substFunc, Passes.removeParam] using hentry
            · change g.allDefs.Nodup
              simp only [g, Passes.substFunc_allDefs]
              exact hrnd.sublist (Passes.removeParam_allDefs_sublist r.2 bi k)
            · exact elimTrivialParam_one_dom hrnd hrdom hfind
            · rfl
            · simpa [hentry] using hb'
            · simpa [hparams] using hrun'
  rw [Passes.elimTrivialParams_eq_loop] at heb' ⊢
  let r := loopWith Passes.elimTrivialStep
    (List.range' 0 (Passes.elimTrivialFuel f) 1)
    (⟨none, f⟩ : Passes.ElimTrivialLoopState)
  have hs := loopSound (List.range' 0 (Passes.elimTrivialFuel f) 1)
    (⟨none, f⟩ : Passes.ElimTrivialLoopState) rfl rfl hnd hdom rfl heb hexec
  change ∃ b', r.2.blocks[f.entry]? = some b' ∧
    Exec (model := model) P r.2 (Regs.empty.setMany f.params args) st
      ⟨b'.instrs, b'.term⟩ res ∧ r.1.getD r.2 = r.2 at hs
  obtain ⟨bout, hbout, hrunout, hr⟩ := hs
  rw [hr] at heb' ⊢
  have heq : eb' = bout := Option.some.inj (heb'.symm.trans hbout)
  subst eb'
  exact hrunout

omit model in
/-- **Dominance preservation for pass 2** — proved. `ToAsm.domCheck_of_shrinking`
reduces it to `Passes.CFRel` block by block, and `Passes.constFold_spec`
(the pass's structural specification, obtained from the `forIn`-to-`foldl`
bridge) supplies exactly that. -/
theorem constFold_dom {f : Func} (hdom : ToAsm.Func.domCheck f = true) :
    ToAsm.Func.domCheck (Passes.constFold f) = true := by
  refine ToAsm.domCheck_of_shrinking hdom rfl rfl ?_
  intro i b' hb'
  obtain ⟨b, hb, hrel⟩ := Passes.constFold_spec f i b' hb'
  exact ⟨b, hb, hrel.1, hrel.2.1, hrel.2.2⟩

omit model in
theorem cse_dom {f : Func} (hwf : f.wfCheck n = true)
    (hdom : ToAsm.Func.domCheck f = true) :
    ToAsm.Func.domCheck (Passes.cse f) = true := by
  let τ := (Passes.csePrefix f f.blocks.size).2.2
  have hnd : f.allDefs.Nodup := by
    have hwf' := hwf
    unfold Func.wfCheck at hwf'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf'
    exact hwf'.1.1.1
  have hfinalInv := (Passes.csePrefixInv hnd f.blocks.size (Nat.le_refl _)).1
  have hparam (p : ValId) (hp : p ∈ f.params) : Passes.substV τ p = p := by
    have hpnone : τ[p]? = none := by
      by_contra hn
      obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hn
      have hpseen := (hfinalInv.2.2.2.1 hq).1
      unfold Passes.cseSeen at hpseen
      have htake : f.blocks.toList.take f.blocks.size = f.blocks.toList := by simp
      rw [htake] at hpseen
      simp only [List.mem_flatMap] at hpseen
      obtain ⟨b, hb, ins, hins, hpdef⟩ := hpseen
      exact funcParam_not_instr_def hnd hb hins hp hpdef
    simp [Passes.substV, Std.HashMap.getD_eq_getD_getElem?, hpnone]
  apply ToAsm.domCheck_of_substitution (f := f) (g := Passes.cse f)
    (Passes.substV τ) (Passes.cseAvail f)
    hdom rfl rfl hparam (Passes.cseAvail_entry f)
  intro i b' hb'
  have hi : i < f.blocks.size := by
    have hi' : i < (Passes.cse f).blocks.size :=
      (Array.getElem?_eq_some_iff.mp hb').1
    simpa using hi'
  let b := f.blocks[i]
  have hb : f.blocks[i]? = some b := Array.getElem?_eq_getElem hi
  have hbout := Passes.cse_block_get hb
  rw [hb'] at hbout
  have heq : b' = Passes.substBlock τ (Passes.cseBlockOut f i) := by
    simpa [τ] using Option.some.inj hbout
  subst b'
  have hspec := Passes.cseBlock_spec hnd hb
  refine ⟨b, hb, hspec.1, hspec.2.1, hspec.2.2.1, ?_⟩
  intro e he x hx
  obtain ⟨e0, he0, htarget⟩ := hspec.2.2.1 e he
  have hs := Passes.cseAvail_succ hnd hwf hb he0 (x := x) (by
    rw [htarget]
    exact hx)
  simpa [τ] using hs

private def dveDomCounterexample : Func :=
  { params := [], nrets := 0, entry := 0
    blocks := #[
      ⟨[], [.const 0 0], .jump ⟨1, [0]⟩⟩,
      ⟨[], [], .ret []⟩] }

private example :
    ToAsm.Func.domCheck dveDomCounterexample = true ∧
      ToAsm.Func.domCheck (Passes.dve dveDomCounterexample) = false := by
  native_decide

omit model in
/-- `wfCheck` is required here because DVE filters edge arguments positionally;
without matching edge/target arities the documented counterexample applies. -/
theorem dve_dom {f : Func} (hwf : f.wfCheck n = true)
    (hdom : ToAsm.Func.domCheck f = true) :
    ToAsm.Func.domCheck (Passes.dve f) = true := by
  obtain ⟨li, hli⟩ := ToAsm.liveInSets_isSome f
  obtain ⟨li', hli'⟩ := ToAsm.liveInSets_isSome (Passes.dve f)
  let ub := li.map (fun xs => xs.filter (Passes.liveSet f).contains)
  have mem_ub (i : Nat) (x : ValId) :
      x ∈ ub[i]?.getD [] ↔ x ∈ li[i]?.getD [] ∧ x ∈ Passes.liveSet f := by
    by_cases hi : i < li.size
    · have hiub : i < ub.size := by simpa [ub] using hi
      rw [Array.getElem?_eq_getElem hiub, Array.getElem?_eq_getElem hi]
      simp only [Option.getD_some, ub, Array.getElem_map, List.mem_filter]
      exact and_congr_right (fun _ => Std.HashSet.contains_iff_mem)
    · have hge : li.size ≤ i := Nat.not_lt.mp hi
      have hgeub : ub.size ≤ i := by simpa [ub] using hge
      rw [Array.getElem?_eq_none_iff.mpr hge, Array.getElem?_eq_none_iff.mpr hgeub]
      simp
  have hub : ToAsm.Sub (ToAsm.liveStep (Passes.dve f) ub) ub := by
    intro i x hx
    rcases hb' : (Passes.dve f).blocks[i]? with _ | b'
    · rw [ToAsm.liveStep_get_none hb'] at hx
      simp at hx
    · rw [ToAsm.liveStep_get_eq hb', ToAsm.mem_diffS] at hx
      rw [Passes.dve_blocks_get] at hb'
      rcases hb : f.blocks[i]? with _ | b
      · simp [hb] at hb'
      · have hb'eq : b' = Passes.dveBlock f i b := by
          symm
          simpa [hb] using hb'
        subst b'
        rw [mem_ub]
        have finish (hxLive : x ∈ Passes.liveSet f) (hxOld : x ∈ li[i]?.getD []) :
            x ∈ li[i]?.getD [] ∧ x ∈ Passes.liveSet f := ⟨hxOld, hxLive⟩
        rcases ToAsm.mem_unionS.mp hx.1 with hu | hl
        · have hxLive := Passes.dveBlock_uses_live hwf hb hu
          have huOld := Passes.dveBlock_uses_sub hu
          have hnot : x ∉ ToAsm.blockDefs b := by
            intro hd
            have hd' := Passes.dveBlock_defs_of_live (i := i)
              (Std.HashSet.mem_iff_contains.mp hxLive) hd
            exact hx.2 hd'
          exact finish hxLive (ToAsm.liveIn_of_uses hli hb huOld hnot)
        · rcases ToAsm.mem_lout.mp hl with ⟨e, he, hxe⟩ | hnil
          · rw [mem_ub] at hxe
            obtain ⟨e0, he0, htarget⟩ := Passes.dveBlock_edge_target he
            have hnot : x ∉ ToAsm.blockDefs b := by
              intro hd
              have hd' := Passes.dveBlock_defs_of_live (i := i)
                (Std.HashSet.mem_iff_contains.mp hxe.2) hd
              exact hx.2 hd'
            exact finish hxe.2 (ToAsm.liveIn_of_succ hli hb he0
              (by rw [htarget]; exact hxe.1) hnot)
          · simp at hnil
  have hsub : ToAsm.Sub li' ub := ToAsm.liveInSets_least hli' hub
  unfold ToAsm.Func.domCheck
  rw [hli']
  simp only [decide_eq_true_eq]
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  rw [ToAsm.mem_diffS] at hx
  have hxub := hsub _ _ hx.1
  rw [mem_ub] at hxub
  exact hx.2 (ToAsm.domCheck_entry hli hdom hxub.1)

omit model in
/-- **Dominance preservation for block coalescing** — read off the pass's
own guard. Merging *grows* a block's use set (it absorbs the target's), so
this is the one pass `domCheck_of_shrinking` cannot serve; rather than
re-derive the liveness fixed point, `Passes.coalesce` checks dominance on
its result and falls back to its input, which is behavior-neutral and never
fires in practice. -/
theorem coalesce_dom {f : Func}
    (hdom : ToAsm.Func.domCheck f = true) :
    ToAsm.Func.domCheck (Passes.coalesce f) = true := by
  rcases Passes.coalesce_cases f with ⟨h, -, hd⟩ | h
  · rw [h]; exact hd
  · rw [h]; exact hdom

omit model in
/-- **Dominance preservation for branch-sense normalization** — proved. The
rewrite replaces a branch condition by the argument of the `iszero` that
defined it, and that `iszero` lives in the *same block*, so the block's use
set only shrinks; `ToAsm.domCheck_of_shrinking` does the rest. (This is
exactly why the pass is restricted to same-block `iszero`s: a cross-block
condition could make a value newly live into the branch's block, and the
liveness fixed point would have to be re-derived.) -/
theorem invertBranches_dom {f : Func}
    (hdom : ToAsm.Func.domCheck f = true) :
    ToAsm.Func.domCheck (Passes.invertBranches f) = true := by
  refine ToAsm.domCheck_of_shrinking hdom rfl rfl ?_
  intro i b' hb'
  have hi : i < f.blocks.size := by
    have hi' : i < (Passes.invertBranches f).blocks.size :=
      (Array.getElem?_eq_some_iff.mp hb').1
    simpa using hi'
  have hb : f.blocks[i]? = some f.blocks[i] := Array.getElem?_eq_getElem hi
  have heq : b' = { f.blocks[i] with
      term := Passes.invertTerm (Passes.blockIszeroSources (Passes.useCounts f)
        f.blocks[i]) f.blocks[i].term } :=
    Option.some.inj (hb'.symm.trans (Passes.invertBranches_get hb))
  subst b'
  refine ⟨f.blocks[i], hb, ?_, ?_, ?_⟩
  · exact fun x hx => Passes.invertBranches_blockUses hx
  · intro x hx
    simpa [ToAsm.blockDefs] using hx
  · intro e he
    exact ⟨e, Passes.invertTerm_mem_edges he, rfl⟩

omit model in
/-- Dominance preservation for one pipeline round, including the intermediate
`wfCheck` facts supplied by the preservation lemmas above. -/
theorem runOnce_dom {f : Func} {n : Nat} (hwf : f.wfCheck n = true)
    (hdom : ToAsm.Func.domCheck f = true) :
    ToAsm.Func.domCheck (Passes.runOnce f) = true := by
  have hwf1 := Passes.elimTrivialParams_wf hwf
  have hwf2 := Passes.coalesce_wf hwf1
  have hwf3 := Passes.invertBranches_wf hwf2
  have hwf4 := Passes.constFold_wf hwf3
  unfold Passes.runOnce
  exact dve_dom hwf4 (constFold_dom (invertBranches_dom
    (coalesce_dom (elimTrivialParams_dom hwf hdom))))

omit model in
theorem Passes.elimTrivialParams_params_entry (f : Func) :
    (elimTrivialParams f).params = f.params ∧
      (elimTrivialParams f).entry = f.entry := by
  have loopInv : ∀ (xs : List Nat) (r : ElimTrivialLoopState),
      r.2.params = f.params → r.2.entry = f.entry →
      r.1.getD r.2 = r.2 →
      let out := loopWith elimTrivialStep xs r
      out.2.params = f.params ∧ out.2.entry = f.entry ∧
        out.1.getD out.2 = out.2 := by
    intro xs
    induction xs with
    | nil =>
        intro r hp he hr
        exact ⟨hp, he, hr⟩
    | cons k ks ih =>
        intro r hp he hr
        rw [loopWith_cons]
        unfold elimTrivialStep
        cases hfind : findTrivialParam r.2 with
        | none => exact ⟨hp, he, by simp⟩
        | some q =>
            obtain ⟨bi, i, p, v⟩ := q
            apply ih
            · simpa [substFunc, removeParam] using hp
            · simpa [substFunc, removeParam] using he
            · rfl
  rw [elimTrivialParams_eq_loop]
  let r := loopWith elimTrivialStep
    (List.range' 0 (elimTrivialFuel f) 1) (⟨none, f⟩ : ElimTrivialLoopState)
  have hr := loopInv (List.range' 0 (elimTrivialFuel f) 1)
    (⟨none, f⟩ : ElimTrivialLoopState) rfl rfl rfl
  change r.2.params = f.params ∧ r.2.entry = f.entry ∧
    r.1.getD r.2 = r.2 at hr
  rw [hr.2.2]
  exact ⟨hr.1, hr.2.1⟩

set_option warningAsError false in
/-- Straight-line block coalescing preserves the function's observable
execution.

TODO(proof): the merged block runs `bi`'s instructions and then `t`'s,
which is exactly the two-block execution with the intervening `jump`
elided; the `jump`'s parallel copy (`args → t.params`) is realized by the
global substitution instead. Blocks dropped by `dropUnreachable` are
unreachable, so no execution visits them. -/
theorem coalesce_sound {P : Prog} {f : Func} {args : List U256}
    {st : EvmState} {res : FRes} {eb eb' : Block}
    (hwf : f.wfCheck P.funcs.size = true)
    (hdom : ToAsm.Func.domCheck f = true)
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.coalesce f).blocks[(Passes.coalesce f).entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P (Passes.coalesce f)
      (Regs.empty.setMany (Passes.coalesce f).params args) st
      ⟨eb'.instrs, eb'.term⟩ res := by
  sorry

/-- The local simulations composed in the order used by `runOnce`. -/
theorem runOnce_sound {P : Prog} {f : Func} {args : List U256}
    {st : EvmState} {res : FRes} {eb eb' : Block}
    (hwf : f.wfCheck P.funcs.size = true)
    (hdom : ToAsm.Func.domCheck f = true)
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.runOnce f).blocks[(Passes.runOnce f).entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P (Passes.runOnce f)
      (Regs.empty.setMany (Passes.runOnce f).params args) st
      ⟨eb'.instrs, eb'.term⟩ res := by
  let f1 := Passes.elimTrivialParams f
  let f2 := Passes.coalesce f1
  let f3 := Passes.invertBranches f2
  let f4 := Passes.constFold f3
  have hwf1 : f1.wfCheck P.funcs.size = true := Passes.elimTrivialParams_wf hwf
  have hwf2 : f2.wfCheck P.funcs.size = true := Passes.coalesce_wf hwf1
  have hwf3 : f3.wfCheck P.funcs.size = true := Passes.invertBranches_wf hwf2
  have hwf4 : f4.wfCheck P.funcs.size = true := Passes.constFold_wf hwf3
  have hdom1 : ToAsm.Func.domCheck f1 = true := elimTrivialParams_dom hwf hdom
  have hdom2 : ToAsm.Func.domCheck f2 = true := coalesce_dom hdom1
  have hdom3 : ToAsm.Func.domCheck f3 = true := invertBranches_dom hdom2
  obtain ⟨-, -, ⟨eb1, heb1, -⟩, -⟩ := Passes.func_wfCheck_iff.mp hwf1
  obtain ⟨-, -, ⟨eb2, heb2, -⟩, -⟩ := Passes.func_wfCheck_iff.mp hwf2
  obtain ⟨-, -, ⟨eb3, heb3, -⟩, -⟩ := Passes.func_wfCheck_iff.mp hwf3
  obtain ⟨-, -, ⟨eb4, heb4, -⟩, -⟩ := Passes.func_wfCheck_iff.mp hwf4
  have hfields1 := Passes.elimTrivialParams_params_entry f
  have hparams1 : f1.params = f.params := by simpa [f1] using hfields1.1
  have hentry1 : f1.entry = f.entry := by simpa [f1] using hfields1.2
  have hparams2 : f2.params = f1.params := Passes.coalesce_params f1
  have hparams3 : f3.params = f2.params := by rfl
  have hentry3 : f3.entry = f2.entry := by rfl
  have hparams4 : f4.params = f3.params := by rfl
  have hentry4 : f4.entry = f3.entry := by rfl
  have heb1' : (Passes.elimTrivialParams f).blocks[f.entry]? = some eb1 := by
    simpa [f1, hentry1] using heb1
  have heb2' : (Passes.coalesce f1).blocks[(Passes.coalesce f1).entry]? = some eb2 := by
    simpa [f2] using heb2
  have heb3' : (Passes.invertBranches f2).blocks[f2.entry]? = some eb3 := by
    simpa [f3, hentry3] using heb3
  have heb4' : (Passes.constFold f3).blocks[f3.entry]? = some eb4 := by
    simpa [f4, hentry4] using heb4
  have h1 := elimTrivialParams_sound hwf hdom heb heb1' hexec
  have h1' : Exec (model := model) P f1 (Regs.empty.setMany f1.params args) st
      ⟨eb1.instrs, eb1.term⟩ res := by simpa [f1, hparams1] using h1
  have h2 := coalesce_sound hwf1 hdom1 heb1 heb2' h1'
  have h2' : Exec (model := model) P f2 (Regs.empty.setMany f2.params args) st
      ⟨eb2.instrs, eb2.term⟩ res := by simpa [f2] using h2
  have h3 := invertBranches_sound heb2 heb3' h2'
  have h3' : Exec (model := model) P f3 (Regs.empty.setMany f3.params args) st
      ⟨eb3.instrs, eb3.term⟩ res := by simpa [f3, hparams3] using h3
  have h4 := constFold_sound hwf3 heb3 heb4' h3'
  have h4' : Exec (model := model) P f4 (Regs.empty.setMany f4.params args) st
      ⟨eb4.instrs, eb4.term⟩ res := by simpa [f4, hparams4] using h4
  have heb5 : (Passes.dve f4).blocks[f4.entry]? = some eb' := by
    simpa [Passes.runOnce, f1, f2, f3, f4, Passes.dve_entry] using heb'
  have h5 := dve_sound hwf4 heb4 heb5 h4'
  simpa [Passes.runOnce, f1, f2, f3, f4, Passes.dve_params] using h5

omit model in
theorem Passes.runOnce_params (f : Func) : (runOnce f).params = f.params := by
  unfold runOnce
  rw [dve_params]
  change (invertBranches (coalesce (elimTrivialParams f))).params = f.params
  rw [invertBranches_params, coalesce_params]
  exact (elimTrivialParams_params_entry f).1

omit model in
theorem Passes.runOnce_nrets (f : Func) : (runOnce f).nrets = f.nrets := by
  have loopInv : ∀ (xs : List Nat) (r : ElimTrivialLoopState),
      r.2.nrets = f.nrets → r.1.getD r.2 = r.2 →
      let out := loopWith elimTrivialStep xs r
      out.2.nrets = f.nrets ∧ out.1.getD out.2 = out.2 := by
    intro xs
    induction xs with
    | nil => intro r hn hr; exact ⟨hn, hr⟩
    | cons k ks ih =>
        intro r hn hr
        rw [loopWith_cons]
        unfold elimTrivialStep
        cases hfind : findTrivialParam r.2 with
        | none => exact ⟨hn, by simp⟩
        | some q =>
            obtain ⟨bi, i, p, v⟩ := q
            apply ih
            · simpa [substFunc, removeParam] using hn
            · rfl
  have he : (elimTrivialParams f).nrets = f.nrets := by
    rw [elimTrivialParams_eq_loop]
    let r := loopWith elimTrivialStep
      (List.range' 0 (elimTrivialFuel f) 1) (⟨none, f⟩ : ElimTrivialLoopState)
    have hr := loopInv (List.range' 0 (elimTrivialFuel f) 1)
      (⟨none, f⟩ : ElimTrivialLoopState) rfl rfl
    change r.2.nrets = f.nrets ∧ r.1.getD r.2 = r.2 at hr
    rw [hr.2]
    exact hr.1
  unfold runOnce
  change (coalesce (elimTrivialParams f)).nrets = f.nrets
  rw [coalesce_nrets]
  exact he

/-- Map one local pipeline round over every function without changing function
indices. -/
def Passes.runOnceProg (P : Prog) : Prog :=
  { main := runOnce P.main, funcs := P.funcs.map runOnce }

omit model in
theorem Passes.runOnceProg_lookup {P : Prog} {fid : FuncId} {g : Func}
    (h : P.funcs[fid]? = some g) :
    (runOnceProg P).funcs[fid]? = some (runOnce g) := by
  simp [runOnceProg, h]

omit model in
theorem Passes.runOnceProg_wf {P : Prog} (hwf : P.wfCheck = true) :
    (runOnceProg P).wfCheck = true := by
  have hparts := hwf
  simp only [Prog.wfCheck, Bool.and_eq_true] at hparts ⊢
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simpa [runOnceProg, runOnce_params] using hparts.1.1.1
  · simpa [runOnceProg, runOnce_nrets] using hparts.1.1.2
  · simpa [runOnceProg] using runOnce_wf hparts.1.2
  · rw [Array.all_eq_true]
    intro i hi
    have hi' : i < P.funcs.size := by simpa [runOnceProg] using hi
    have hfi : P.funcs[i].wfCheck P.funcs.size = true := by
      rw [Array.all_eq_true] at hparts
      exact hparts.2 i hi'
    simpa [runOnceProg] using runOnce_wf hfi

omit model in
set_option maxHeartbeats 800000 in
theorem Passes.runOnceProg_dom {P : Prog} (hwf : P.wfCheck = true)
    (hdom : ToAsm.Prog.domCheck P = true) :
    ToAsm.Prog.domCheck (runOnceProg P) = true := by
  have hparts := hwf
  have hdom0 := hdom
  simp only [Prog.wfCheck, Bool.and_eq_true] at hparts
  unfold ToAsm.Prog.domCheck at hdom ⊢
  simp only [Bool.and_eq_true] at hdom ⊢
  refine ⟨?_, ?_⟩
  · exact runOnce_dom (f := P.main) (n := P.funcs.size) hparts.1.2 hdom.1
  · rw [Array.all_eq_true_iff_forall_mem]
    intro g' hg'
    obtain ⟨g, hg, rfl⟩ := Array.mem_map.mp hg'
    have hfi : g.wfCheck P.funcs.size = true :=
      Array.all_eq_true_iff_forall_mem.mp hparts.2 g hg
    have hdi : ToAsm.Func.domCheck g = true :=
      ToAsm.Prog.domCheck_funcs hdom0 hg
    exact runOnce_dom (f := g) (n := P.funcs.size) hfi hdi

/-- Change the ambient program to its one-round map while leaving the current
function text fixed.  At calls, the structural induction first replays the
callee under the mapped ambient program and `runOnce_sound` then rewrites that
callee's entry execution. -/
theorem Passes.runOnceProg_exec {P : Prog} (hPwf : P.wfCheck = true)
    (hPdom : ToAsm.Prog.domCheck P = true) {f : Func} {R : Regs}
    {st : EvmState} {rest : Rest} {res : FRes}
    (hexec : Exec (model := model) P f R st rest res) :
    Exec (model := model) (runOnceProg P) f R st rest res := by
  induction hexec with
  | const htail ih => exact Exec.const ih
  | op hget hop hlen htail ih => exact Exec.op hget hop hlen ih
  | opHalt hget hop => exact Exec.opHalt hget hop
  | @call f g R st st' ds as fid args rvals eb is t res
      hfid hget hplen heb hbody hlen htail ihbody ih =>
      have hgwf0 := progWf_func hPwf hfid
      have hgwf : g.wfCheck (runOnceProg P).funcs.size = true := by
        simpa [runOnceProg] using hgwf0
      have hgmem : g ∈ P.funcs := by
        obtain ⟨hi, hget⟩ := Array.getElem?_eq_some_iff.mp hfid
        exact Array.mem_iff_getElem.mpr ⟨fid, hi, hget⟩
      have hgdom : ToAsm.Func.domCheck g = true :=
        ToAsm.Prog.domCheck_funcs hPdom hgmem
      obtain ⟨-, -, ⟨eb', heb', -⟩, -⟩ :=
        func_wfCheck_iff.mp (runOnce_wf hgwf)
      have hbody' := runOnce_sound hgwf hgdom heb heb' ihbody
      refine Exec.call (g := runOnce g) (eb := eb') (runOnceProg_lookup hfid)
        hget ?_ heb' hbody' hlen ih
      simpa [runOnce_params] using hplen
  | @callHalt f g R st st' ds as fid args eb is t
      hfid hget hplen heb hbody ihbody =>
      have hgwf0 := progWf_func hPwf hfid
      have hgwf : g.wfCheck (runOnceProg P).funcs.size = true := by
        simpa [runOnceProg] using hgwf0
      have hgmem : g ∈ P.funcs := by
        obtain ⟨hi, hget⟩ := Array.getElem?_eq_some_iff.mp hfid
        exact Array.mem_iff_getElem.mpr ⟨fid, hi, hget⟩
      have hgdom : ToAsm.Func.domCheck g = true :=
        ToAsm.Prog.domCheck_funcs hPdom hgmem
      obtain ⟨-, -, ⟨eb', heb', -⟩, -⟩ :=
        func_wfCheck_iff.mp (runOnce_wf hgwf)
      have hbody' := runOnce_sound hgwf hgdom heb heb' ihbody
      refine Exec.callHalt (g := runOnce g) (eb := eb')
        (runOnceProg_lookup hfid) hget ?_ heb' hbody'
      simpa [runOnce_params] using hplen
  | jump htb hget hplen htail ih => exact Exec.jump htb hget hplen ih
  | branchTrue hc hv htb hget hplen htail ih =>
      exact Exec.branchTrue hc hv htb hget hplen ih
  | branchFalse hc htb hget hplen htail ih =>
      exact Exec.branchFalse hc htb hget hplen ih
  | ret hget => exact Exec.ret hget
  | halt hget hop => exact Exec.halt hget hop

theorem Passes.runOnceProg_sound {P : Prog} {yst0 yst' : EvmState}
    {o : Outcome} (hwf : P.wfCheck = true)
    (hdom : ToAsm.Prog.domCheck P = true)
    (hrun : Run (model := model) P yst0 yst' o) :
    Run (model := model) (runOnceProg P) yst0 yst' o := by
  have hparts := hwf
  simp only [Prog.wfCheck, Bool.and_eq_true] at hparts
  have hmainWf : P.main.wfCheck (runOnceProg P).funcs.size = true := by
    simpa [runOnceProg] using hparts.1.2
  have hmainDom := ToAsm.Prog.domCheck_main hdom
  have hmainParams : P.main.params = [] := List.isEmpty_iff.mp hparts.1.1.1
  cases hrun with
  | normal heb hexec =>
      rename_i eb
      obtain ⟨-, -, ⟨eb', heb', -⟩, -⟩ :=
        func_wfCheck_iff.mp (runOnce_wf hmainWf)
      have hamb := runOnceProg_exec hwf hdom hexec
      have hlocal := runOnce_sound (args := []) hmainWf hmainDom heb heb'
        (by simpa [hmainParams, Regs.setMany_nil_left] using hamb)
      exact Run.normal (by simpa [runOnceProg] using heb')
        (by simpa [runOnceProg, runOnce_params, hmainParams,
          Regs.setMany_nil_left] using hlocal)
  | halt heb hexec =>
      rename_i eb
      obtain ⟨-, -, ⟨eb', heb', -⟩, -⟩ :=
        func_wfCheck_iff.mp (runOnce_wf hmainWf)
      have hamb := runOnceProg_exec hwf hdom hexec
      have hlocal := runOnce_sound (args := []) hmainWf hmainDom heb heb'
        (by simpa [hmainParams, Regs.setMany_nil_left] using hamb)
      exact Run.halt (by simpa [runOnceProg] using heb')
        (by simpa [runOnceProg, runOnce_params, hmainParams,
          Regs.setMany_nil_left] using hlocal)

def Passes.runOnceProgN : Nat → Prog → Prog
  | 0, P => P
  | n + 1, P => runOnceProgN n (runOnceProg P)

theorem Passes.runOnceProgN_sound : ∀ (n : Nat) {P : Prog}
    {yst0 yst' : EvmState} {o : Outcome},
    P.wfCheck = true → ToAsm.Prog.domCheck P = true →
      Run (model := model) P yst0 yst' o →
      Run (model := model) (runOnceProgN n P) yst0 yst' o := by
  intro n
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih =>
      intro P yst0 yst' o hwf hdom hrun
      exact ih (runOnceProg_wf hwf) (runOnceProg_dom hwf hdom)
        (runOnceProg_sound hwf hdom hrun)

omit model in
theorem Passes.optimizeFunc_eq_runOnce3 (f : Func) :
    optimizeFunc f = runOnce (runOnce (runOnce f)) := by
  simp only [optimizeFunc, pipelineRounds,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [show (3 - 0 + 1 - 1) / 1 = 3 from rfl]
  rw [show List.range' 0 3 1 = [0, 1, 2] from rfl]
  rfl

omit model in
theorem optimizeCandidate_eq_rounds (P : Prog) :
    optimizeCandidate P = Passes.runOnceProgN 3 (optimizeInput P) := by
  simp [optimizeCandidate, optimizeInput, Passes.runOnceProgN, Passes.runOnceProg,
    Passes.optimizeFunc_eq_runOnce3, Array.map_map, Function.comp_def]

/-! ### The top-level statement -/

/-- **`SsaCfg.optimizeProg_sound`, reproduced verbatim** (post-fix signature:
`hwf` *and* `hdom`).

The intermediate gate supplies the exact hypotheses required by the
per-function pipeline: if it accepts the inlined program, inlining soundness
provides the corresponding run and the gate provides well-formedness and
dominance; if it rejects, the original program and the theorem hypotheses are
used instead. The final gate either returns that proved candidate or falls back
to the original program. -/
theorem optimizeProg_sound' {P : Prog} {yst0 yst' : EvmState} {o : Outcome}
    (hwf : P.wfCheck = true) (hdom : ToAsm.Prog.domCheck P = true)
    (hrun : Run (model := model) P yst0 yst' o) :
    Run (model := model) (optimizeProg P) yst0 yst' o := by
  by_cases hgate : ((optimizeCandidate P).wfCheck
      && ToAsm.Prog.domCheck (optimizeCandidate P)) = true
  · -- the gate accepted the pipeline's output: this is the real content
    rw [optimizeProg_of_gate_true hgate]
    rw [optimizeCandidate_eq_rounds]
    by_cases hinlineGate : ((Passes.inlineProg P).wfCheck
        && ToAsm.Prog.domCheck (Passes.inlineProg P)) = true
    · simp only [optimizeInput, hinlineGate, if_true]
      have hchecks := (Bool.and_eq_true _ _).mp hinlineGate
      exact Passes.runOnceProgN_sound 3 hchecks.1 hchecks.2
        (inlineProg_sound hwf hrun)
    · simp only [optimizeInput, hinlineGate]
      exact Passes.runOnceProgN_sound 3 hwf hdom hrun
  · -- the gate rejected it: `optimizeProg` returned `P` unchanged
    simp only [Bool.not_eq_true] at hgate
    exact optimizeProg_sound_of_fallback hgate hrun

#print axioms optimizeProg_sound'

end YulEvmCompiler.SsaCfg
