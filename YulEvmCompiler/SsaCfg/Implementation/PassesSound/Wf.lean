import YulEvmCompiler.SsaCfg.Implementation.PassesSound.Dve
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.PassesSound.Wf

Well-formedness preservation for the four local passes.

`substFunc_wf`, `removeParam_wf`, `elimTrivialParams_wf`, `constFold_wf`,
`cse_wf`, `dve_wf`, and their composition `runOnce_wf`.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal stepOp ExternalCalls
  ExternalCreates)
open YulSemantics (Outcome)
variable [model : ExternalModel]

/-! ### Well-formedness preservation for the four local passes -/

namespace Passes

omit model in
@[simp] theorem substTerm_edges_eq (σ : Subst) (t : Term) :
    (substTerm σ t).edges = t.edges.map (substEdge σ) := by
  cases t <;> rfl

omit model in
theorem BlockWF.subst {σ : Subst} {f : Func} {b : Block} {n : Nat}
    (h : BlockWF f.blocks f.nrets n b) :
    BlockWF (substFunc σ f).blocks (substFunc σ f).nrets n (substBlock σ b) := by
  refine ⟨?_, ?_, ?_⟩
  · have hh := h.1
    rcases ht : b.term with e | ⟨c, et, ef⟩ | xs | ⟨yop, as⟩ <;>
      simp_all [substBlock, substTerm, substVs, substFunc]
  · intro e he
    simp only [substBlock, substTerm_edges_eq, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    obtain ⟨tb, htb, hlen⟩ := h.2.1 e0 he0
    refine ⟨substBlock σ tb, ?_, ?_⟩
    · change (f.blocks.map (substBlock σ))[e0.target]? = some (substBlock σ tb)
      rw [Array.getElem?_map, htb]
      rfl
    · simp [substEdge, substVs, substBlock]
      exact hlen
  · intro i hi
    simp only [substBlock, List.mem_map] at hi
    obtain ⟨i0, hi0, rfl⟩ := hi
    have hw := h.2.2 i0 hi0
    cases i0 <;> simp_all [substInstr]

omit model in
theorem substFunc_wf {σ : Subst} {f : Func} {n : Nat}
    (hwf : f.wfCheck n = true) : (substFunc σ f).wfCheck n = true := by
  obtain ⟨hnd, hentry, ⟨eb, heb, hempty⟩, hall⟩ := func_wfCheck_iff.mp hwf
  apply func_wfCheck_iff.mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [substFunc_allDefs] using hnd
  · simpa [substFunc] using hentry
  · refine ⟨substBlock σ eb, ?_, ?_⟩
    · simp [substFunc, heb]
    · simpa [substBlock] using hempty
  · intro b' hb'
    simp only [substFunc, Array.toList_map, List.mem_map] at hb'
    obtain ⟨b, hb, rfl⟩ := hb'
    exact (hall b hb).subst

omit model in
theorem removedBlock_instrs (bi i j : Nat) (b : Block) :
    (removedBlock bi i j b).instrs = b.instrs := by
  by_cases h : j = bi <;> simp only [removedBlock, h, if_true, if_false]

omit model in
theorem removedBlock_term (bi i j : Nat) (b : Block) :
    (removedBlock bi i j b).term = mapEdges (elimEdge bi i) b.term := by
  by_cases h : j = bi <;> simp only [removedBlock, h, if_true, if_false]
  all_goals rfl

omit model in
theorem removeParam_wf {f : Func} {n bi i p v : Nat}
    (hwf : f.wfCheck n = true)
    (hfind : findTrivialParam f = some (bi, i, p, v)) :
    (removeParam f bi i).wfCheck n = true := by
  obtain ⟨hbi, hbientry, hi, hp, -, -, -, -⟩ := findTrivialParam_inv hfind
  obtain ⟨hnd, hentry, ⟨eb, heb, hempty⟩, hall⟩ := func_wfCheck_iff.mp hwf
  have hpb : f.blocks[bi]? = some f.blocks[bi] := Array.getElem?_eq_getElem hbi
  have hi' : i < f.blocks[bi].params.length := by
    simpa [getElem!_eq_getElem hbi] using hi
  apply func_wfCheck_iff.mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hnd.sublist (removeParam_allDefs_sublist f bi i)
  · simpa [removeParam] using hentry
  · refine ⟨removedBlock bi i f.entry eb, removeParam_blocks_get heb, ?_⟩
    simpa [removedBlock, Ne.symm hbientry] using hempty
  · intro b' hb'
    have hbmem : b' ∈ (removeParam f bi i).blocks := by simpa using hb'
    obtain ⟨j, hjlt, rfl⟩ := Array.mem_iff_getElem.mp hbmem
    have hjlt' : j < f.blocks.size := by simpa [removeParam] using hjlt
    let b := f.blocks[j]
    have hb : f.blocks[j]? = some b := Array.getElem?_eq_getElem hjlt'
    have hbout := removeParam_blocks_get (bi := bi) (i := i) hb
    have hb'eq : (removeParam f bi i).blocks[j] = removedBlock bi i j b := by
      have hget : (removeParam f bi i).blocks[j]? =
          some (removeParam f bi i).blocks[j] := Array.getElem?_eq_getElem hjlt
      exact Option.some.inj (hget.symm.trans hbout)
    rw [hb'eq]
    have hbwf := hall b (block_mem_of_getElem? hb)
    refine ⟨?_, ?_, ?_⟩
    · have hh := hbwf.1
      cases ht : b.term <;>
        simp_all [removedBlock_term, removeParam, mapEdges]
    · intro e he
      rw [removedBlock_term] at he
      obtain ⟨e0, he0, rfl⟩ := mapEdges_edges b.term he
      obtain ⟨tb, htb, hlen⟩ := hbwf.2.1 e0 he0
      refine ⟨removedBlock bi i e0.target tb, ?_, ?_⟩
      · have htarget : (elimEdge bi i e0).target = e0.target := by
          unfold elimEdge
          split <;> rfl
        rw [htarget]
        exact removeParam_blocks_get htb
      · by_cases het : e0.target = bi
        · rw [het] at htb
          have htbeq : tb = f.blocks[bi] := Option.some.inj (htb.symm.trans hpb)
          subst tb
          have hargs : (elimEdge bi i e0).args = e0.args.eraseIdx i := by
            simp [elimEdge, het]
          rw [hargs, List.length_eraseIdx, hlen]
          rw [if_pos hi']
          unfold removedBlock
          dsimp only
          rw [if_pos het]
          rw [List.length_eraseIdx, if_pos hi']
        · simpa [elimEdge, removedBlock, het] using hlen
    · intro ins hins
      rw [removedBlock_instrs] at hins
      exact hbwf.2.2 ins hins

omit model in
/-- Pass 1 preserves the backend well-formedness check at every removal. -/
theorem elimTrivialParams_wf {f : Func} {n : Nat}
    (hwf : f.wfCheck n = true) :
    (elimTrivialParams f).wfCheck n = true := by
  have loopInv : ∀ (xs : List Nat) (r : ElimTrivialLoopState),
      r.2.wfCheck n = true → r.1.getD r.2 = r.2 →
      let out := loopWith elimTrivialStep xs r
      out.2.wfCheck n = true ∧ out.1.getD out.2 = out.2 := by
    intro xs
    induction xs with
    | nil => intro r hr hrout; exact ⟨hr, hrout⟩
    | cons k ks ih =>
        intro r hr hrout
        rw [loopWith_cons]
        unfold elimTrivialStep
        cases hfind : findTrivialParam r.2 with
        | none => exact ⟨hr, by simp⟩
        | some q =>
            obtain ⟨bi, i, p, v⟩ := q
            apply ih
            · exact substFunc_wf (removeParam_wf hr hfind)
            · rfl
  rw [elimTrivialParams_eq_loop]
  let r := loopWith elimTrivialStep
    (List.range' 0 (elimTrivialFuel f) 1) (⟨none, f⟩ : ElimTrivialLoopState)
  have hr := loopInv (List.range' 0 (elimTrivialFuel f) 1)
    (⟨none, f⟩ : ElimTrivialLoopState) hwf rfl
  change r.2.wfCheck n = true ∧ r.1.getD r.2 = r.2 at hr
  rw [hr.2]
  exact hr.1

omit model in
theorem cfInstrOut_defs (i : Instr) (m : Std.HashMap ValId U256) :
    (cfInstrOut i m).defs = i.defs := by
  cases i with
  | const => rfl
  | call => rfl
  | op ds yop as =>
      cases ds with
      | nil => rfl
      | cons d ds =>
          cases ds with
          | nil => simp only [cfInstrOut]; split <;> rfl
          | cons e es => rfl

omit model in
theorem cfInstrs_defs (is : List Instr) (m : Std.HashMap ValId U256) :
    (is.foldl (fun s i => cfInstrStep i s) ⟨m, []⟩).2.reverse.flatMap Instr.defs =
      is.flatMap Instr.defs := by
  induction is generalizing m with
  | nil => rfl
  | cons i is ih =>
      rw [cfInstr_fold_cons, List.flatMap_cons, List.flatMap_cons,
        cfInstrOut_defs, ih]

omit model in
theorem cfBlockOut_allDefs (b : Block) (m : Std.HashMap ValId U256) :
    blockAllDefs (cfBlockOut b m) = blockAllDefs b := by
  simp only [blockAllDefs, cfBlockOut]
  rw [cfInstrs_defs]

omit model in
theorem cfBlock_fold_allDefs (bs : List Block) (st : CFOuter) :
    ((bs.foldl (fun s b => cfBlockStep b s) st).1.toList.flatMap blockAllDefs) =
      st.1.toList.flatMap blockAllDefs ++ bs.flatMap blockAllDefs := by
  induction bs generalizing st with
  | nil => simp
  | cons b bs ih =>
      rw [List.foldl_cons, ih]
      simp only [cfBlockStep_eq', Array.toList_push, List.flatMap_append,
        List.flatMap_singleton, cfBlockOut_allDefs, List.append_assoc]
      simp [blockAllDefs, List.append_assoc]

omit model in
theorem constFold_allDefs (f : Func) : (constFold f).allDefs = f.allDefs := by
  unfold Func.allDefs
  rw [constFold_blocks_eq, cfBlock_fold_allDefs]
  rfl

omit model in
theorem cfBlock_fold_size (bs : List Block) (st : CFOuter) :
    (bs.foldl (fun s b => cfBlockStep b s) st).1.size = st.1.size + bs.length := by
  induction bs generalizing st with
  | nil => simp
  | cons b bs ih =>
      rw [List.foldl_cons, ih]
      simp only [cfBlockStep_eq', Array.size_push, List.length_cons]
      omega

omit model in
theorem constFold_size (f : Func) : (constFold f).blocks.size = f.blocks.size := by
  rw [constFold_blocks_eq, cfBlock_fold_size]
  simp

omit model in
theorem cfInstrOut_check {n : Nat} {i : Instr} {m : Std.HashMap ValId U256}
    (h : match i with
      | .op ds _ _ => ds.length ≤ 1
      | .call _ g _ => g < n
      | _ => True) :
    match cfInstrOut i m with
    | .op ds _ _ => ds.length ≤ 1
    | .call _ g _ => g < n
    | _ => True := by
  cases i with
  | const => trivial
  | call => exact h
  | op ds yop as =>
      cases ds with
      | nil => exact h
      | cons d ds =>
          cases ds with
          | nil =>
              simp only [cfInstrOut]
              split <;> grind
          | cons e es => exact h

omit model in
theorem cfInstrs_check {n : Nat} {is : List Instr} {m : Std.HashMap ValId U256}
    (h : ∀ i ∈ is, match i with
      | .op ds _ _ => ds.length ≤ 1
      | .call _ g _ => g < n
      | _ => True) :
    ∀ i ∈ (is.foldl (fun s i => cfInstrStep i s) ⟨m, []⟩).2.reverse,
      match i with
      | .op ds _ _ => ds.length ≤ 1
      | .call _ g _ => g < n
      | _ => True := by
  induction is generalizing m with
  | nil => simp
  | cons i is ih =>
      rw [cfInstr_fold_cons]
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact cfInstrOut_check (h i (by simp))
      · exact ih (fun k hk => h k (by simp [hk])) j hj

omit model in
theorem cfTerm_edge_mem (b : Block) (m : Std.HashMap ValId U256) {e : Edge}
    (he : e ∈ (cfTerm b m).edges) : e ∈ b.term.edges := by
  rcases cfTerm_cases b m with h | ⟨e0, he0, h⟩
  · simpa [h] using he
  · have heq : e = e0 := by simpa [h, Term.edges] using he
    simpa [heq] using he0

omit model in
theorem cfBlockOut_wf {f : Func} {b : Block} {m : Std.HashMap ValId U256}
    {n : Nat} (_hwf : f.wfCheck n = true) (_hb : b ∈ f.blocks.toList)
    (h : BlockWF f.blocks f.nrets n b) :
    BlockWF (constFold f).blocks (constFold f).nrets n (cfBlockOut b m) := by
  refine ⟨?_, ?_, ?_⟩
  · rcases ht : b.term with e | ⟨c, et, ef⟩ | xs | ⟨yop, as⟩
    · simp [cfBlockOut, cfTerm, ht]
    · cases hc : (b.instrs.foldl (fun s i => cfInstrStep i s) ⟨m, []⟩).1[c]?
        <;> simp [cfBlockOut, cfTerm, ht, hc]
    · simpa [cfBlockOut, cfTerm, constFold, ht] using h.1
    · simp [cfBlockOut, cfTerm, ht]
  · intro e he
    have hecf : e ∈ (cfTerm b
        (b.instrs.foldl (fun s i => cfInstrStep i s) ⟨m, []⟩).1).edges := by
      simpa [cfBlockOut] using he
    have he0 := cfTerm_edge_mem b _ hecf
    obtain ⟨tb, htb, hlen⟩ := h.2.1 e he0
    obtain ⟨mt, htb', -⟩ := constFold_block_get_sound htb
    refine ⟨cfBlockOut tb mt, htb', ?_⟩
    simpa [cfBlockOut] using hlen
  · intro i hi
    apply cfInstrs_check h.2.2 i
    simpa [cfBlockOut] using hi

omit model in
/-- Pass 2 preserves the backend well-formedness check. -/
theorem constFold_wf {f : Func} {n : Nat} (hwf : f.wfCheck n = true) :
    (constFold f).wfCheck n = true := by
  obtain ⟨hnd, hentry, ⟨eb, heb, hempty⟩, hall⟩ := func_wfCheck_iff.mp hwf
  apply func_wfCheck_iff.mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [constFold_allDefs] using hnd
  · change f.entry < (constFold f).blocks.size
    rw [constFold_size]
    exact hentry
  · obtain ⟨m, heb', -⟩ := constFold_block_get_sound heb
    refine ⟨cfBlockOut eb m, heb', ?_⟩
    simpa [cfBlockOut] using hempty
  · intro b' hb'
    have hbmem : b' ∈ (constFold f).blocks := by simpa using hb'
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hbmem
    have hout : (constFold f).blocks[i]? = some (constFold f).blocks[i] :=
      Array.getElem?_eq_getElem hi
    obtain ⟨b, hb, hrel⟩ := constFold_spec f i (constFold f).blocks[i] hout
    obtain ⟨m, hbout, -⟩ := constFold_block_get_sound hb
    have heq : (constFold f).blocks[i] = cfBlockOut b m :=
      Option.some.inj (hout.symm.trans hbout)
    rw [heq]
    exact cfBlockOut_wf hwf (block_mem_of_getElem? hb) (hall b (block_mem_of_getElem? hb))

omit model in
@[simp] theorem substInstr_defs_eq (σ : Subst) (i : Instr) :
    (substInstr σ i).defs = i.defs := by
  cases i <;> rfl

omit model in
@[simp] theorem flatMap_substInstr_defs (σ : Subst) (is : List Instr) :
    (is.map (substInstr σ)).flatMap Instr.defs = is.flatMap Instr.defs := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [ih]

omit model in
theorem substInstr_check {n : Nat} {σ : Subst} {i : Instr}
    (h : match i with
      | .op ds _ _ => ds.length ≤ 1
      | .call _ g _ => g < n
      | _ => True) :
    match substInstr σ i with
    | .op ds _ _ => ds.length ≤ 1
    | .call _ g _ => g < n
    | _ => True := by
  cases i <;> exact h

omit model in
theorem cseInstrsOut_defs_sublist (τ : Subst) (is : List Instr)
    (tab : CseTab) (used : Std.HashSet ValId) (σ : Subst)
    (defined blockDefs : Std.HashSet ValId) :
    List.Sublist
      ((cseInstrsOut τ is tab used σ defined blockDefs).flatMap Instr.defs)
      (is.flatMap Instr.defs) := by
  induction is generalizing tab used σ defined blockDefs with
  | nil => exact .slnil
  | cons i is ih =>
      let s := cseInstrStep i ⟨[], tab, used, σ, defined, blockDefs⟩
      have hs : s.1 = [] ∨ s.1 = [substInstr σ i] := by
        simpa [s] using (cseInstrStep_out (i := i) (acc := []) (tab := tab)
          (used := used) (σ := σ) (defined := defined) (blockDefs := blockDefs))
      rw [cseInstrsOut]
      rcases hs with hs | hs
      · rw [hs]
        simp only [List.reverse_nil, List.map_nil, List.nil_append, List.flatMap_cons]
        exact (ih s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2).trans
          (List.sublist_append_right _ _)
      · rw [hs]
        simp only [List.reverse_singleton, List.map_singleton, List.singleton_append,
          List.flatMap_cons, substInstr_defs_eq]
        exact (List.Sublist.refl i.defs).append
          (ih s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2)

omit model in
theorem cseInstrsOut_check {n : Nat} (τ : Subst) (is : List Instr)
    (tab : CseTab) (used : Std.HashSet ValId) (σ : Subst)
    (defined blockDefs : Std.HashSet ValId)
    (h : ∀ i ∈ is, match i with
      | .op ds _ _ => ds.length ≤ 1
      | .call _ g _ => g < n
      | _ => True) :
    ∀ i ∈ cseInstrsOut τ is tab used σ defined blockDefs,
      match i with
      | .op ds _ _ => ds.length ≤ 1
      | .call _ g _ => g < n
      | _ => True := by
  induction is generalizing tab used σ defined blockDefs with
  | nil => simp [cseInstrsOut]
  | cons i is ih =>
      let s := cseInstrStep i ⟨[], tab, used, σ, defined, blockDefs⟩
      have hs : s.1 = [] ∨ s.1 = [substInstr σ i] := by
        simpa [s] using (cseInstrStep_out (i := i) (acc := []) (tab := tab)
          (used := used) (σ := σ) (defined := defined) (blockDefs := blockDefs))
      rw [cseInstrsOut]
      intro j hj
      rw [List.mem_append] at hj
      rcases hj with hj | hj
      · have hj' : j ∈ s.1.reverse.map (substInstr τ) := by simpa [s] using hj
        rcases hs with hs | hs
        · simp [hs] at hj'
        · simp only [hs, List.reverse_singleton, List.map_singleton,
            List.mem_singleton] at hj'
          have hj := hj'
          subst j
          exact substInstr_check (substInstr_check (h i (by simp)))
      · exact ih s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2
          (fun k hk => h k (by simp [hk])) j hj

omit model in
theorem cseBlockOut_defs_sublist (f : Func) (i : BlockId) :
    List.Sublist (blockAllDefs (cseBlockOut f i)) (blockAllDefs f.blocks[i]!) := by
  let b := f.blocks[i]!
  let st := csePrefix f i
  let tab := cseEntryTab f (inEdgeSources f) st.2.1 i
  have hs := cseInstrsOut_defs_sublist (∅ : Subst) b.instrs tab ∅ st.2.2 ∅
    (cseBlockDefs b)
  rw [cseInstrsOut_eq_fold] at hs
  simp only [flatMap_substInstr_defs] at hs
  unfold cseBlockOut
  dsimp only
  apply List.Sublist.append (.refl _)
  simpa [b, st, tab] using hs

omit model in
theorem flatMap_sublist_of_getElem? {α β : Type} (F G : α → List β)
    {xs ys : List α} (hlen : xs.length = ys.length)
    (h : ∀ (i : Nat) (a b : α), xs[i]? = some a → ys[i]? = some b →
      List.Sublist (F a) (G b)) :
    List.Sublist (xs.flatMap F) (ys.flatMap G) := by
  induction xs generalizing ys with
  | nil =>
      have hy : ys = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst ys
      exact .slnil
  | cons a xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons b ys =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          simp only [List.flatMap_cons]
          exact (h 0 a b (by simp) (by simp)).append
            (ih hlen (fun i x y hx hy => h (i + 1) x y (by simpa using hx)
              (by simpa using hy)))

omit model in
theorem cseRaw_allDefs_sublist (f : Func) :
    let raw : Func := { f with blocks := (csePrefix f f.blocks.size).1 }
    List.Sublist raw.allDefs f.allDefs := by
  dsimp only
  unfold Func.allDefs
  apply List.Sublist.append (.refl _)
  apply flatMap_sublist_of_getElem? blockAllDefs blockAllDefs
  · simp
  · intro i b' b hb' hb
    have hi : i < f.blocks.size := (List.getElem?_eq_some_iff.mp hb).1
    have hbraw : (csePrefix f f.blocks.size).1.toList[i]? =
        some (cseBlockOut f i) := by
      simpa using cseFinal_raw_block (f := f) hi
    have heq' : b' = cseBlockOut f i := Option.some.inj (hb'.symm.trans hbraw)
    have hbang : f.blocks[i]! = b := by
      rw [getElem!_eq_getElem hi]
      exact (List.getElem?_eq_some_iff.mp hb).2
    subst b'
    rw [← hbang]
    exact cseBlockOut_defs_sublist f i

omit model in
theorem cseBlockOut_wf {f : Func} {n : Nat} (_hwf : f.wfCheck n = true)
    {i : BlockId} {b : Block} (hb : f.blocks[i]? = some b)
    (h : BlockWF f.blocks f.nrets n b) :
    let raw : Func := { f with blocks := (csePrefix f f.blocks.size).1 }
    BlockWF raw.blocks raw.nrets n (cseBlockOut f i) := by
  let raw : Func := { f with blocks := (csePrefix f f.blocks.size).1 }
  have hi : i < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hbang : f.blocks[i]! = b := by
    rw [getElem!_eq_getElem hi]
    exact (Array.getElem?_eq_some_iff.mp hb).2
  let st := csePrefix f i
  let tab := cseEntryTab f (inEdgeSources f) st.2.1 i
  let r := b.instrs.foldl (fun s ins => cseInstrStep ins s)
    ⟨[], tab, ∅, st.2.2, ∅, cseBlockDefs b⟩
  have hout : cseBlockOut f i = { b with instrs := r.1.reverse } := by
    simp [cseBlockOut, hbang, st, tab, r]
  rw [hout]
  refine ⟨h.1, ?_, ?_⟩
  · intro e he
    obtain ⟨tb, htb, hlen⟩ := h.2.1 e he
    have ht : e.target < f.blocks.size := (Array.getElem?_eq_some_iff.mp htb).1
    have htbang : f.blocks[e.target]! = tb := by
      rw [getElem!_eq_getElem ht]
      exact (Array.getElem?_eq_some_iff.mp htb).2
    refine ⟨cseBlockOut f e.target, ?_, ?_⟩
    · exact cseFinal_raw_block ht
    · simpa [raw, cseBlockOut, htbang] using hlen
  · intro ins hins
    have hc := cseInstrsOut_check (n := n) (∅ : Subst) b.instrs tab ∅ st.2.2 ∅
      (cseBlockDefs b) h.2.2
    rw [cseInstrsOut_eq_fold] at hc
    have hmapped : substInstr (∅ : Subst) ins ∈ r.1.reverse.map (substInstr ∅) :=
      List.mem_map.mpr ⟨ins, hins, rfl⟩
    have houtcheck := hc (substInstr ∅ ins) (by simpa [r] using hmapped)
    cases ins <;> simp_all [substInstr]

omit model in
/-- Pass 3 preserves the backend well-formedness check. -/
theorem cse_wf {f : Func} {n : Nat} (hwf : f.wfCheck n = true) :
    (cse f).wfCheck n = true := by
  let raw : Func := { f with blocks := (csePrefix f f.blocks.size).1 }
  have hraw : raw.wfCheck n = true := by
    obtain ⟨hnd, hentry, ⟨eb, heb, hempty⟩, hall⟩ := func_wfCheck_iff.mp hwf
    apply func_wfCheck_iff.mpr
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hnd.sublist (cseRaw_allDefs_sublist f)
    · simpa [raw] using hentry
    · have hi : f.entry < f.blocks.size := hentry
      refine ⟨cseBlockOut f f.entry, cseFinal_raw_block hi, ?_⟩
      have hbang : f.blocks[f.entry]! = eb := by
        rw [getElem!_eq_getElem hi]
        exact (Array.getElem?_eq_some_iff.mp heb).2
      simpa [cseBlockOut, hbang] using hempty
    · intro b' hb'
      have hbmem : b' ∈ raw.blocks := by simpa using hb'
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hbmem
      have hi' : i < f.blocks.size := by simpa [raw] using hi
      let b := f.blocks[i]
      have hb : f.blocks[i]? = some b := Array.getElem?_eq_getElem hi'
      have hbraw := cseFinal_raw_block (f := f) hi'
      have hget : raw.blocks[i]? = some raw.blocks[i] := Array.getElem?_eq_getElem hi
      have heq : raw.blocks[i] = cseBlockOut f i := Option.some.inj (hget.symm.trans hbraw)
      rw [heq]
      exact cseBlockOut_wf hwf hb (hall b (block_mem_of_getElem? hb))
  rw [cse_eq]
  change (substFunc (csePrefix f f.blocks.size).2.2 raw).wfCheck n = true
  exact substFunc_wf hraw

omit model in
theorem dveBlock_allDefs_sublist (f : Func) (i : BlockId) (b : Block) :
    List.Sublist (blockAllDefs (dveBlock f i b)) (blockAllDefs b) := by
  unfold blockAllDefs dveBlock
  apply List.Sublist.append
  · split
    · exact List.Sublist.refl _
    · exact List.filter_sublist
  · exact (List.filter_sublist (l := b.instrs)).flatMap Instr.defs

omit model in
theorem dve_allDefs_sublist (f : Func) : (dve f).allDefs.Sublist f.allDefs := by
  unfold Func.allDefs
  apply List.Sublist.append (.refl _)
  apply flatMap_sublist_of_getElem? blockAllDefs blockAllDefs
  · simp [dve]
  · intro i b' b hb' hb
    have hi : i < f.blocks.size := (List.getElem?_eq_some_iff.mp hb).1
    have hbA : f.blocks[i]? = some b := by simpa using hb
    have hbout := dve_blocks_get f i
    rw [hbA] at hbout
    have hbout' : (dve f).blocks.toList[i]? = some (dveBlock f i b) := by
      simpa using hbout
    have heq : b' = dveBlock f i b := Option.some.inj (hb'.symm.trans hbout')
    subst b'
    exact dveBlock_allDefs_sublist f i b

omit model in
theorem filterZip_length {α β : Type} (p : α → Bool)
    {xs : List α} {ys : List β} (hlen : xs.length = ys.length) :
    ((xs.zip ys).filter fun xy => p xy.1).length = (xs.filter p).length := by
  induction xs generalizing ys with
  | nil =>
      have hy : ys = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst ys
      rfl
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          simp only [List.zip_cons_cons, List.filter_cons]
          split <;> simp [ih hlen]

omit model in
theorem dveBlock_wf {f : Func} {n : Nat} (hwf : f.wfCheck n = true)
    {i : BlockId} {b : Block} (_hb : f.blocks[i]? = some b)
    (h : BlockWF f.blocks f.nrets n b) :
    BlockWF (dve f).blocks (dve f).nrets n (dveBlock f i b) := by
  refine ⟨?_, ?_, ?_⟩
  · have hh := h.1
    rcases ht : b.term with e | ⟨c, et, ef⟩ | xs | ⟨yop, as⟩ <;>
      simp_all [dveBlock, mapEdges, dve]
  · intro e he
    obtain ⟨e0, he0, heq⟩ := mapEdges_edges b.term (by simpa [dveBlock] using he)
    have heqD : e = dveEdge f e0 := by
      rw [← heq]
      rfl
    obtain ⟨tb, htb, hlen⟩ := h.2.1 e0 he0
    rw [heqD]
    refine ⟨dveBlock f e0.target tb, ?_, ?_⟩
    · change (dve f).blocks[e0.target]? = some (dveBlock f e0.target tb)
      rw [dve_blocks_get, htb]
      rfl
    · rw [dveEdge_args_eq_zip htb hlen, dveBlock_params hwf htb,
        List.length_map, filterZip_length (liveSet f).contains hlen.symm]
  · intro ins hins
    have hins' : ins ∈ b.instrs := by
      change ins ∈ b.instrs.filter (dveKeepInstr (liveSet f)) at hins
      exact List.mem_of_mem_filter hins
    exact h.2.2 ins hins'

omit model in
/-- Pass 4 preserves the backend well-formedness check. -/
theorem dve_wf {f : Func} {n : Nat} (hwf : f.wfCheck n = true) :
    (dve f).wfCheck n = true := by
  obtain ⟨hnd, hentry, ⟨eb, heb, hempty⟩, hall⟩ := func_wfCheck_iff.mp hwf
  apply func_wfCheck_iff.mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hnd.sublist (dve_allDefs_sublist f)
  · simpa [dve_entry, dve_size] using hentry
  · have heb' := dve_blocks_get f f.entry
    rw [heb] at heb'
    refine ⟨dveBlock f f.entry eb, heb', ?_⟩
    rw [dveBlock_params hwf heb]
    simp [hempty]
  · intro b' hb'
    have hbmem : b' ∈ (dve f).blocks := by simpa using hb'
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hbmem
    have hi' : i < f.blocks.size := by simpa [dve_size] using hi
    let b := f.blocks[i]
    have hb : f.blocks[i]? = some b := Array.getElem?_eq_getElem hi'
    have hbout := dve_blocks_get f i
    rw [hb] at hbout
    have hget : (dve f).blocks[i]? = some (dve f).blocks[i] :=
      Array.getElem?_eq_getElem hi
    have heq : (dve f).blocks[i] = dveBlock f i b :=
      Option.some.inj (hget.symm.trans (by simpa using hbout))
    rw [heq]
    exact dveBlock_wf hwf hb (hall b (block_mem_of_getElem? hb))

set_option warningAsError false in
omit model in
/-- Straight-line block coalescing preserves `Func.wfCheck`.

TODO(proof): merging appends the absorbed block's instructions and adopts
its terminator, so single assignment is preserved (no definition is
duplicated — the absorbed block is dropped) and every edge is either
untouched or remapped by `dropUnreachable`'s reachability-preserving
renumbering. -/
theorem coalesce_wf {f : Func} {n : Nat} (hwf : f.wfCheck n = true) :
    (coalesce f).wfCheck n = true := by
  sorry

set_option warningAsError false in
omit model in
/-- Branch-sense normalization preserves `Func.wfCheck`.

TODO(proof): only a `branch`'s condition and the *order* of its two edges
change; the edge set, their argument lists, and every definition are
untouched, so every `wfCheck` conjunct is preserved componentwise. -/
theorem invertBranches_wf {f : Func} {n : Nat} (hwf : f.wfCheck n = true) :
    (invertBranches f).wfCheck n = true := by
  sorry

omit model in
/-- One complete local pipeline round preserves `Func.wfCheck`. -/
theorem runOnce_wf {f : Func} {n : Nat} (hwf : f.wfCheck n = true) :
    (runOnce f).wfCheck n = true := by
  exact dve_wf (constFold_wf (invertBranches_wf (coalesce_wf (elimTrivialParams_wf hwf))))

end Passes

end YulEvmCompiler.SsaCfg
