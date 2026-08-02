import YulEvmCompiler.SsaCfg.Implementation.PassesSound.CseRuntime
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.PassesSound.Cse

Pass 3 soundness: local common-subexpression elimination.

The positional view `cseAt` and its freshness certificate, the block
execution induction `cse_exec_aux`, and `cse_sound`.
-/

namespace YulEvmCompiler.SsaCfg
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal stepOp ExternalCalls
  ExternalCreates)
open YulSemantics (Outcome)
variable [model : ExternalModel]

namespace Passes

/-- The CSE fold state at a source instruction boundary, with the emitted-list
accumulator reset (only the other five projections affect subsequent steps). -/
def cseAt (f : Func) (cur : BlockId) (b : Block) (pre : List Instr) : CSEInner :=
  let r := pre.foldl (fun s i => cseInstrStep i s)
    ⟨[], cseEntryTab f (inEdgeSources f) (csePrefix f cur).2.1 cur, ∅,
      (csePrefix f cur).2.2, ∅, cseBlockDefs b⟩
  ⟨[], r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2⟩

def CseFresh (f : Func) : Prop :=
  ∀ {cur : BlockId} {b : Block}, f.blocks[cur]? = some b →
    ∀ {path : List BlockId}, EntryPath f path cur →
    ∀ {pre post : List Instr} {i : Instr}, b.instrs = pre ++ i :: post →
    ∀ d ∈ i.defs,
      (∀ v, i ≠ .const d v) →
      d ∉ cseTabVals (cseAt f cur b pre).2.1 ∧
      d ∉ cseTabRuntimeUses (cseSub f) (cseAt f cur b pre).2.1 ∧
      ((cseInstrStep i (cseAt f cur b pre)).2.1 ≠
        (cseAt f cur b pre).2.1 → d ∉ (substInstr (cseSub f) i).uses)

omit model in
theorem cseAt_nil (f : Func) (cur : BlockId) (b : Block) :
    cseAt f cur b [] =
      ⟨[], cseEntryTab f (inEdgeSources f) (csePrefix f cur).2.1 cur, ∅,
      (csePrefix f cur).2.2, ∅, cseBlockDefs b⟩ := rfl

omit model in
@[simp] theorem cseAt_fst (f : Func) (cur : BlockId) (b : Block)
    (pre : List Instr) : (cseAt f cur b pre).1 = [] := rfl

omit model in
theorem cseAt_full {f : Func} {cur : BlockId} {b : Block}
    (hb : f.blocks[cur]? = some b) :
    (cseAt f cur b b.instrs).2.1 = cseBlockTabOut f cur := by
  have hcur : cur < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hbang : f.blocks[cur]! = b := by
    rw [getElem!_eq_getElem hcur]
    exact (Array.getElem?_eq_some_iff.mp hb).2
  simp [cseAt, cseBlockTabOut, hbang]

omit model in
theorem cseAt_snoc (f : Func) (cur : BlockId) (b : Block)
    (pre : List Instr) (i : Instr) :
    cseAt f cur b (pre ++ [i]) =
      let s := cseInstrStep i (cseAt f cur b pre)
      ⟨[], s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2⟩ := by
  unfold cseAt
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  let r := pre.foldl (fun s i => cseInstrStep i s)
    ⟨[], cseEntryTab f (inEdgeSources f) (csePrefix f cur).2.1 cur, ∅,
      (csePrefix f cur).2.2, ∅, cseBlockDefs b⟩
  have hs := cseInstrStep_state i r.1 r.2.1 r.2.2.1 r.2.2.2.1
    r.2.2.2.2.1 r.2.2.2.2.2
  change
    (⟨[], (cseInstrStep i r).2.1, (cseInstrStep i r).2.2.1,
      (cseInstrStep i r).2.2.2.1, (cseInstrStep i r).2.2.2.2.1,
      (cseInstrStep i r).2.2.2.2.2⟩ : CSEInner) =
    ⟨[], (cseInstrStep i
      ⟨[], r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2⟩).2.1,
      (cseInstrStep i
        ⟨[], r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2⟩).2.2.1,
      (cseInstrStep i
        ⟨[], r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2⟩).2.2.2.1,
      (cseInstrStep i
        ⟨[], r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2⟩).2.2.2.2.1,
      (cseInstrStep i
        ⟨[], r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2⟩).2.2.2.2.2⟩
  rw [hs]

def CseTabLE (a b : CseTab) : Prop :=
  (∀ e, e ∈ a.ops → e ∈ b.ops) ∧ (∀ e, e ∈ a.consts → e ∈ b.consts)

omit model in
theorem CseTabLE.refl (a : CseTab) : CseTabLE a a :=
  ⟨fun _ h => h, fun _ h => h⟩

omit model in
theorem CseTabLE.trans {a b c : CseTab} (hab : CseTabLE a b)
    (hbc : CseTabLE b c) : CseTabLE a c :=
  ⟨fun e h => hbc.1 e (hab.1 e h), fun e h => hbc.2 e (hab.2 e h)⟩

omit model in
theorem cseInstrStep_tab_mono (i : Instr) (st : CSEInner) :
    CseTabLE st.2.1 (cseInstrStep i st).2.1 := by
  cases i with
  | const d v =>
      simp only [cseInstrStep, substInstr]
      split
      · exact CseTabLE.refl _
      · exact ⟨fun _ h => h, fun e h => by simp [h]⟩
  | call ds fid as => exact CseTabLE.refl _
  | op ds yop as =>
      cases ds with
      | nil => exact CseTabLE.refl _
      | cons d ds =>
          cases ds with
          | cons e es => exact CseTabLE.refl _
          | nil =>
              simp only [cseInstrStep, substInstr]
              split
              · split
                · split <;> exact CseTabLE.refl _
                · split
                  · exact ⟨fun e h => by simp [h], fun _ h => h⟩
                  · exact CseTabLE.refl _
              · exact CseTabLE.refl _

omit model in
theorem cseInstrFold_tab_mono (l : List Instr) (st : CSEInner) :
    CseTabLE st.2.1 (l.foldl (fun s i => cseInstrStep i s) st).2.1 := by
  induction l generalizing st with
  | nil => exact CseTabLE.refl _
  | cons i is ih =>
      rw [List.foldl_cons]
      exact (cseInstrStep_tab_mono i st).trans (ih _)

omit model in
theorem cseInstrFold_snd_congr (l : List Instr) {a b : CSEInner}
    (h : a.2 = b.2) :
    (l.foldl (fun s i => cseInstrStep i s) a).2 =
      (l.foldl (fun s i => cseInstrStep i s) b).2 := by
  induction l generalizing a b with
  | nil => exact h
  | cons i is ih =>
      rw [List.foldl_cons, List.foldl_cons]
      apply ih
      rcases a with ⟨acca, taba, useda, siga, defa, blocka⟩
      rcases b with ⟨accb, tabb, usedb, sigb, defb, blockb⟩
      simp only at h
      cases h
      exact (cseInstrStep_state i acca taba useda siga defa blocka).trans
        (cseInstrStep_state i accb taba useda siga defa blocka).symm

omit model in
theorem CseTabSound.mono {f : Func} {a b : CseTab}
    (h : CseTabSound f b) (hle : CseTabLE a b) : CseTabSound f a := by
  exact ⟨⟨fun hm => h.1.1 (hle.1 _ hm), fun hm => h.1.2 (hle.2 _ hm)⟩,
    fun hm => h.2 (hle.1 _ hm)⟩

omit model in
theorem cseAt_tab_le {f : Func} {cur : BlockId} {b : Block}
    (hb : f.blocks[cur]? = some b) {pre post : List Instr}
    (hsplit : b.instrs = pre ++ post) :
    CseTabLE (cseAt f cur b pre).2.1 (cseBlockTabOut f cur) := by
  have hcur : cur < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hbang : f.blocks[cur]! = b := by
    rw [getElem!_eq_getElem hcur]
    exact (Array.getElem?_eq_some_iff.mp hb).2
  let base : CSEInner :=
    ⟨[], cseEntryTab f (inEdgeSources f) (csePrefix f cur).2.1 cur, ∅,
      (csePrefix f cur).2.2, ∅, cseBlockDefs b⟩
  let r := pre.foldl (fun s i => cseInstrStep i s) base
  let q : CSEInner := ⟨[], r.2.1, r.2.2.1, r.2.2.2.1,
    r.2.2.2.2.1, r.2.2.2.2.2⟩
  have hacc := cseInstrFold_acc_state post r.1 r.2.1 r.2.2.1 r.2.2.2.1
    r.2.2.2.2.1 r.2.2.2.2.2
  have htab : (post.foldl (fun s i => cseInstrStep i s) q).2.1 =
      (b.instrs.foldl (fun s i => cseInstrStep i s) base).2.1 := by
    rw [hsplit, List.foldl_append]
    change (post.foldl (fun s i => cseInstrStep i s) q).2.1 =
      (post.foldl (fun s i => cseInstrStep i s) r).2.1
    have htabeq := congrArg (fun s : CSEInner => s.2.1) hacc
    simpa [q] using htabeq.symm
  have hm := cseInstrFold_tab_mono post q
  simpa [cseAt, cseBlockTabOut, hbang, base, r, q, htab] using hm

omit model in
theorem cseAt_tab_sound {f : Func} (hnd : f.allDefs.Nodup)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {pre post : List Instr} (hsplit : b.instrs = pre ++ post) :
    CseTabSound f (cseAt f cur b pre).2.1 := by
  have hcur : cur < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  exact (cseBlockTabOut_sound hnd hcur).mono (cseAt_tab_le hb hsplit)

omit model in
theorem cseAt_inv {f : Func} (hnd : f.allDefs.Nodup)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {pre post : List Instr} (hsplit : b.instrs = pre ++ post) :
    CSEInv f (cseSeen f cur ++ pre.flatMap Instr.defs)
      (cseAt f cur b pre).2.1 (cseAt f cur b pre).2.2.2.1 := by
  have hcur : cur < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hbmem : b ∈ f.blocks.toList := block_mem_of_getElem? hb
  have hpre := csePrefixInv hnd cur (Nat.le_of_lt hcur)
  have hentry := cseEntryTab_inv hpre
  have hseenNodup : (cseSeen f cur ++ pre.flatMap Instr.defs).Nodup := by
    have hall : (cseSeen f cur ++ b.instrs.flatMap Instr.defs).Nodup := by
      rw [← cseSeen_succ hb]
      exact (instrDefs_nodup hnd).sublist (cseSeen_sublist f (cur + 1))
    refine hall.sublist ?_
    rw [hsplit, List.flatMap_append]
    exact (List.Sublist.refl _).append (List.sublist_append_left _ _)
  have hr := cseInstrFold_inv hbmem hentry pre
    (fun i hi => by rw [hsplit]; exact List.mem_append_left _ hi)
    hseenNodup [] ∅ ∅ (cseBlockDefs b)
  simpa [cseAt] using hr.1

omit model in
theorem cseAt_dest_none {f : Func} (hnd : f.allDefs.Nodup)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {pre post : List Instr} {i : Instr} (hsplit : b.instrs = pre ++ i :: post)
    {d : ValId} (hd : d ∈ i.defs) : (cseAt f cur b pre).2.2.2.1[d]? = none := by
  have hinv := cseAt_inv hnd hb
    (show b.instrs = pre ++ (i :: post) from hsplit)
  by_contra hn
  obtain ⟨d0, hmap⟩ := Option.ne_none_iff_exists'.mp hn
  have hseen := (hinv.2.2.2.1 hmap).1
  have hall : (cseSeen f cur ++ b.instrs.flatMap Instr.defs).Nodup := by
    rw [← cseSeen_succ hb]
    exact (instrDefs_nodup hnd).sublist (cseSeen_sublist f (cur + 1))
  have hall' : ((cseSeen f cur ++ pre.flatMap Instr.defs) ++
      (i.defs ++ post.flatMap Instr.defs)).Nodup := by
    simpa [hsplit, List.flatMap_append, List.flatMap_cons, List.append_assoc] using hall
  have hcurNot : d ∉ cseSeen f cur ++ pre.flatMap Instr.defs := by
    rw [List.nodup_append] at hall'
    intro hm
    exact hall'.2.2 d hm d (List.mem_append_left _ hd) rfl
  exact hcurNot hseen

omit model in
theorem cseAt_substExt {f : Func} (hnd : f.allDefs.Nodup)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {pre post : List Instr} (hsplit : b.instrs = pre ++ post) :
    SubstExt (cseAt f cur b pre).2.2.2.1 (cseSub f) := by
  change SubstExt
    (pre.foldl (fun s i => cseInstrStep i s)
      ⟨[], cseEntryTab f (inEdgeSources f) (csePrefix f cur).2.1 cur, ∅,
        (csePrefix f cur).2.2, ∅, cseBlockDefs b⟩).2.2.2.1 (cseSub f)
  exact cseFold_substExt hnd hb hsplit

omit model in
theorem cseInstrsOut_at_drop {f : Func} {cur : BlockId} {b : Block}
    {pre : List Instr} {i : Instr} {is : List Instr}
    (hs : (cseInstrStep i (cseAt f cur b pre)).1 = []) :
    cseInstrsOut (cseSub f) (i :: is) (cseAt f cur b pre).2.1
        (cseAt f cur b pre).2.2.1 (cseAt f cur b pre).2.2.2.1
        (cseAt f cur b pre).2.2.2.2.1 (cseAt f cur b pre).2.2.2.2.2 =
      cseInstrsOut (cseSub f) is (cseAt f cur b (pre ++ [i])).2.1
        (cseAt f cur b (pre ++ [i])).2.2.1
        (cseAt f cur b (pre ++ [i])).2.2.2.1
        (cseAt f cur b (pre ++ [i])).2.2.2.2.1
        (cseAt f cur b (pre ++ [i])).2.2.2.2.2 := by
  have hs' : (cseInstrStep i
      ⟨[], (cseAt f cur b pre).2.1, (cseAt f cur b pre).2.2.1,
        (cseAt f cur b pre).2.2.2.1, (cseAt f cur b pre).2.2.2.2.1,
        (cseAt f cur b pre).2.2.2.2.2⟩).1 = [] := by
    simpa only [cseAt] using hs
  rw [cseInstrsOut, hs']
  simp only [List.reverse_nil, List.map_nil, List.nil_append, cseAt_snoc]
  rfl

omit model in
theorem cseInstrsOut_at_keep {f : Func} (hnd : f.allDefs.Nodup)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {pre : List Instr} {i : Instr} {is post : List Instr}
    (hsplit : b.instrs = pre ++ i :: post)
    (hs : (cseInstrStep i (cseAt f cur b pre)).1 =
      [substInstr (cseAt f cur b pre).2.2.2.1 i]) :
    cseInstrsOut (cseSub f) (i :: is) (cseAt f cur b pre).2.1
        (cseAt f cur b pre).2.2.1 (cseAt f cur b pre).2.2.2.1
        (cseAt f cur b pre).2.2.2.2.1 (cseAt f cur b pre).2.2.2.2.2 =
      substInstr (cseSub f) i ::
        cseInstrsOut (cseSub f) is (cseAt f cur b (pre ++ [i])).2.1
          (cseAt f cur b (pre ++ [i])).2.2.1
          (cseAt f cur b (pre ++ [i])).2.2.2.1
          (cseAt f cur b (pre ++ [i])).2.2.2.2.1
          (cseAt f cur b (pre ++ [i])).2.2.2.2.2 := by
  have hs' : (cseInstrStep i
      ⟨[], (cseAt f cur b pre).2.1, (cseAt f cur b pre).2.2.1,
        (cseAt f cur b pre).2.2.2.1, (cseAt f cur b pre).2.2.2.2.1,
        (cseAt f cur b pre).2.2.2.2.2⟩).1 =
      [substInstr (cseAt f cur b pre).2.2.2.1 i] := by
    simpa only [cseAt] using hs
  rw [cseInstrsOut, hs']
  simp only [List.reverse_singleton, List.map_singleton, List.singleton_append,
    cseAt_snoc]
  rw [substInstr_absorb (cseAt_substExt hnd hb
    (show b.instrs = pre ++ (i :: post) from hsplit)) (cseSub_rangeFree hnd)]
  rfl

omit model in
theorem cseAt_tab_domain {f : Func} (hnd : f.allDefs.Nodup)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {pre post : List Instr} (hsplit : b.instrs = pre ++ post) :
    CseTabDomainSound f (cseSub f) (cseAt f cur b pre).2.1 := by
  have hcur : cur < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hinv : CSEPrefixDomainInv f (cseSub f) (cur + 1) :=
    csePrefixDomainInv hnd (cur + 1) (Nat.succ_le_of_lt hcur)
  have hfull : CseTabDomainSound f (cseSub f)
      (csePrefix f (cur + 1)).2.1[cur]! := hinv cur (by omega)
  rw [csePrefix_table_next hnd hcur] at hfull
  intro yop args d hm
  exact hfull ((cseAt_tab_le hb hsplit).1 _ hm)

omit model in
/-- Once the unique instruction defining `d` has been stepped, no later fold
step can change its substitution entry. -/
theorem cseAt_dest_final {f : Func} (hnd : f.allDefs.Nodup)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {pre post : List Instr} {i : Instr} (hsplit : b.instrs = pre ++ i :: post)
    {d : ValId} (hd : d ∈ i.defs) :
    (cseSub f)[d]? =
      (cseInstrStep i (cseAt f cur b pre)).2.2.2.1[d]? := by
  have hcur : cur < f.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  have hbmem : b ∈ f.blocks.toList := block_mem_of_getElem? hb
  have hbang : f.blocks[cur]! = b := by
    rw [getElem!_eq_getElem hcur]
    exact (Array.getElem?_eq_some_iff.mp hb).2
  let base : CSEInner :=
    ⟨[], cseEntryTab f (inEdgeSources f) (csePrefix f cur).2.1 cur, ∅,
      (csePrefix f cur).2.2, ∅, cseBlockDefs b⟩
  let r := pre.foldl (fun s i => cseInstrStep i s) base
  let q : CSEInner := ⟨[], r.2.1, r.2.2.1, r.2.2.2.1,
    r.2.2.2.2.1, r.2.2.2.2.2⟩
  let s := cseInstrStep i q
  have hpre0 := csePrefixInv hnd cur (Nat.le_of_lt hcur)
  have hentry : CSEInv f (cseSeen f cur) base.2.1 base.2.2.2.1 := by
    simpa [base] using cseEntryTab_inv hpre0
  have hseenNodup :
      (cseSeen f cur ++ b.instrs.flatMap Instr.defs).Nodup := by
    rw [← cseSeen_succ hb]
    exact (instrDefs_nodup hnd).sublist (cseSeen_sublist f (cur + 1))
  have hpreNodup :
      (cseSeen f cur ++ pre.flatMap Instr.defs).Nodup := by
    refine hseenNodup.sublist ?_
    rw [hsplit, List.flatMap_append, List.flatMap_cons]
    exact (List.Sublist.refl _).append (List.sublist_append_left _ _)
  have hrInv := cseInstrFold_inv hbmem hentry pre
    (fun j hj => by rw [hsplit]; exact List.mem_append_left _ hj)
    hpreNodup [] ∅ ∅ (cseBlockDefs b)
  have hqInv : CSEInv f (cseSeen f cur ++ pre.flatMap Instr.defs)
      q.2.1 q.2.2.2.1 := by simpa [q, r, base] using hrInv.1
  have hstepNodup :
      ((cseSeen f cur ++ pre.flatMap Instr.defs) ++ i.defs).Nodup := by
    refine hseenNodup.sublist ?_
    rw [hsplit, List.flatMap_append, List.flatMap_cons]
    simp [List.append_assoc]
  have hsInv := cseInstrStep_inv hbmem
    (used := q.2.2.1) (defined := q.2.2.2.2.1)
    (blockDefs := q.2.2.2.2.2) hqInv i
    (by rw [hsplit]; simp) hstepNodup
  have hsState := cseInstrStep_state i q.1 q.2.1 q.2.2.1 q.2.2.2.1
    q.2.2.2.2.1 q.2.2.2.2.2
  have hsInv' : CSEInv f
      ((cseSeen f cur ++ pre.flatMap Instr.defs) ++ i.defs) s.2.1 s.2.2.2.1 := by
    dsimp only [s]
    rw [hsState]
    exact hsInv.1
  have htailNodup :
      (((cseSeen f cur ++ pre.flatMap Instr.defs) ++ i.defs) ++
        post.flatMap Instr.defs).Nodup := by
    simpa [hsplit, List.flatMap_append, List.flatMap_cons, List.append_assoc] using
      hseenNodup
  have htailStable := cseInstrFold_stable hbmem hsInv' post
    (fun j hj => by rw [hsplit]; simp [hj]) htailNodup
    s.1 s.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2
  let rend := post.foldl (fun z j => cseInstrStep j z) s
  have hdseen : d ∈ (cseSeen f cur ++ pre.flatMap Instr.defs) ++ i.defs := by
    simp [hd]
  have htailD : rend.2.2.2.1[d]? = s.2.2.2.1[d]? := by
    exact htailStable d hdseen
  have hfullSigma : (csePrefix f (cur + 1)).2.2 = rend.2.2.2.1 := by
    rw [csePrefix_succ]
    simp only [cseBlockStep, hbang]
    rw [hsplit, List.foldl_append, List.foldl_cons]
    change (post.foldl (fun z j => cseInstrStep j z)
      (cseInstrStep i (pre.foldl (fun z j => cseInstrStep j z) base))).2.2.2.1 =
        rend.2.2.2.1
    have hstepSecond := cseInstrStep_state i r.1 r.2.1 r.2.2.1 r.2.2.2.1
      r.2.2.2.2.1 r.2.2.2.2.2
    have hfoldSecond :
        (post.foldl (fun z j => cseInstrStep j z) (cseInstrStep i r)).2 =
          (post.foldl (fun z j => cseInstrStep j z) s).2 := by
      apply cseInstrFold_snd_congr
      simpa [s, q] using hstepSecond
    exact congrArg (fun z => z.2.2.1) hfoldSecond
  have hprefixStable := csePrefix_stable_to hnd (Nat.succ_le_of_lt hcur)
    (Nat.le_refl f.blocks.size)
  have hdSeenGlobal : d ∈ cseSeen f (cur + 1) := by
    rw [cseSeen_succ hb, hsplit, List.flatMap_append, List.flatMap_cons]
    simp [hd]
  rw [cseSub, hprefixStable d hdSeenGlobal, hfullSigma, htailD]
  rfl

omit model in
theorem cseAt_rep_fresh {f : Func} {n : Nat} (hnd : f.allDefs.Nodup)
    (hwf : f.wfCheck n = true) {cur : BlockId} {b : Block}
    (hb : f.blocks[cur]? = some b) {path : List BlockId}
    (hpath : EntryPath f path cur) {pre post : List Instr} {i : Instr}
    (hsplit : b.instrs = pre ++ i :: post) {d : ValId} (hd : d ∈ i.defs) :
    d ∉ cseTabVals (cseAt f cur b pre).2.1 := by
  intro hm
  have hseen := cseSeen_of_tabVal hnd hwf hb hpath
    (show b.instrs = pre ++ (i :: post) from hsplit) (used := ∅)
    (defined := ∅) (blockDefs := cseBlockDefs b)
    (σ := (csePrefix f cur).2.2) (x := d) (by
      simpa [cseAt] using hm)
  exact hseen.not_defined_later hnd hb hsplit (by
    rw [List.flatMap_cons]
    exact List.mem_append_left _ hd)

omit model in
/-- The defining instruction of an operation-table representative is either
already in the current prefix or lies in a block dominating the current one. -/
theorem cseAt_entry_before {f : Func} {n : Nat} (hnd : f.allDefs.Nodup)
    (hwf : f.wfCheck n = true) {cur : BlockId} {b : Block}
    (hb : f.blocks[cur]? = some b) {path : List BlockId}
    (hpath : EntryPath f path cur) {pre post : List Instr}
    (hsplit : b.instrs = pre ++ post) {yop : Op} {args : List ValId}
    {r : ValId} (hm : ((yop, args), r) ∈ (cseAt f cur b pre).2.1.ops)
    (he : CseEntryPos f (.op yop args) r) :
    ∃ ri rb j, f.blocks[ri]? = some rb ∧ j ∈ rb.instrs ∧ r ∈ j.defs ∧
      BlockDom f ri cur ∧ (ri = cur → j ∈ pre) := by
  cases he with
  | @op rb preR postR j sigma _ _ _ hbR hseq hsubst hstable =>
      obtain ⟨ri, hri⟩ := block_index_of_mem hbR
      have hjmem : j ∈ rb.instrs := by rw [hseq]; simp
      have hjdef : r ∈ j.defs := by
        rw [← substInstr_defs sigma j, hsubst]
        simp [Instr.defs]
      have hrTab : r ∈ cseTabVals (cseAt f cur b pre).2.1 :=
        List.mem_append_left _ (List.mem_map.mpr ⟨_, hm, rfl⟩)
      obtain ⟨di, db, hdb, hrdef, hrdom, hloc⟩ :=
        cseSeen_of_tabVal hnd hwf hb hpath hsplit (used := ∅)
          (defined := ∅) (blockDefs := cseBlockDefs b)
          (σ := (csePrefix f cur).2.2) hrTab
      have hrbDef : r ∈ ToAsm.blockDefs rb := ToAsm.mem_blockDefs.mpr
        (Or.inr (List.mem_flatMap.mpr ⟨j, hjmem, hjdef⟩))
      have hdbDef : r ∈ ToAsm.blockDefs db :=
        ToAsm.mem_blockDefs.mpr (Or.inr hrdef)
      have hir : ri = di := block_def_index_unique hnd hri hdb hrbDef hdbDef
      subst di
      refine ⟨ri, rb, j, hri, hjmem, hjdef, hrdom, ?_⟩
      intro hcur
      have hrpre := hloc hcur
      obtain ⟨k, hkpre, hkdef⟩ := List.mem_flatMap.mp hrpre
      have hkBlock : k ∈ rb.instrs := by
        have hrbb : rb = b := by
          subst ri
          exact Option.some.inj (hri.symm.trans hb)
        subst rb
        rw [hsplit]
        exact List.mem_append_left _ hkpre
      have heq := instr_def_unique (d := r) hnd hbR hbR hjmem hkBlock hjdef hkdef
      simpa [heq] using hkpre

omit model in
/-- A non-constant destination cannot overwrite an argument read by an
operation entry already live at the current CSE boundary. -/
theorem cseAt_runtimeUse_fresh_nonconst {f : Func} {li : Array (List ValId)}
    {n : Nat} (hnd : f.allDefs.Nodup) (hwf : f.wfCheck n = true)
    (hli : ToAsm.liveInSets f = some li) (hdom : ToAsm.Func.domCheck f = true)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {path : List BlockId} (hpath : EntryPath f path cur)
    {pre post : List Instr} {i : Instr}
    (hsplit : b.instrs = pre ++ i :: post) {d : ValId} (hd : d ∈ i.defs)
    (hnconst : ∀ v, i ≠ .const d v) :
    d ∉ cseTabRuntimeUses (cseSub f) (cseAt f cur b pre).2.1 := by
  intro huseTab
  simp only [cseTabRuntimeUses, List.mem_flatMap] at huseTab
  obtain ⟨⟨⟨yop, sargs⟩, r⟩, hm, hdargs⟩ := huseTab
  have htabSound := cseAt_tab_sound hnd hb
    (show b.instrs = pre ++ (i :: post) from hsplit)
  have hentry := htabSound.2 hm
  have hdomain := cseAt_tab_domain hnd hb
    (show b.instrs = pre ++ (i :: post) from hsplit) hm
  have hbefore := cseAt_entry_before hnd hwf hb hpath
    (show b.instrs = pre ++ (i :: post) from hsplit) hm hentry
  cases hentry with
  | @op rb preR postR j sigma r yop sargs hbR hseq hsubst hstable =>
      obtain ⟨ri, rb0, j0, hri, hj0mem, hj0def, hrdom, hj0pre⟩ := hbefore
      obtain ⟨rbi, hrbi⟩ := block_index_of_mem hbR
      have hjmem : j ∈ rb.instrs := by rw [hseq]; simp
      have hjdef : r ∈ j.defs := by
        rw [← substInstr_defs sigma j, hsubst]
        simp [Instr.defs]
      have hrbDef : r ∈ ToAsm.blockDefs rb := ToAsm.mem_blockDefs.mpr
        (Or.inr (List.mem_flatMap.mpr ⟨j, hjmem, hjdef⟩))
      have hrb0Def : r ∈ ToAsm.blockDefs rb0 := ToAsm.mem_blockDefs.mpr
        (Or.inr (List.mem_flatMap.mpr ⟨j0, hj0mem, hj0def⟩))
      have hrbiEq : rbi = ri :=
        block_def_index_unique hnd hrbi hri hrbDef hrb0Def
      subst rbi
      have hrbeq : rb = rb0 := Option.some.inj (hrbi.symm.trans hri)
      subst rb0
      have hjeq : j = j0 :=
        instr_def_unique (d := r) hnd hbR hbR hjmem hj0mem hjdef hj0def
      subst j0
      cases hdomain with
      | @op bu ju sigmaU r yop sargs hbU hju hsubstU hdirect horigin =>
          obtain ⟨ui, hui⟩ := block_index_of_mem hbU
          have hjuDef : r ∈ ju.defs := by
            rw [← substInstr_defs sigmaU ju, hsubstU]
            simp [Instr.defs]
          have hbuDef : r ∈ ToAsm.blockDefs bu := ToAsm.mem_blockDefs.mpr
            (Or.inr (List.mem_flatMap.mpr ⟨ju, hju, hjuDef⟩))
          have huiEq : ui = ri :=
            block_def_index_unique hnd hui hri hbuDef hrbDef
          subst ui
          have hbueq : bu = rb := Option.some.inj (hui.symm.trans hri)
          subst bu
          have hjueq : ju = j :=
            instr_def_unique (d := r) hnd hbR hbR hju hjmem hjuDef hjdef
          subst ju
          have hpathRi : ∃ p, EntryPath f p ri := by
            by_cases heq : ri = cur
            · subst ri; exact ⟨path, hpath⟩
            · have hs : StrictBlockDom f ri cur := by
                intro p hp
                exact (hrdom p hp).resolve_left heq
              have hrmem := hs path hpath
              obtain ⟨p, hp, -, -⟩ := hpath.prefix_of_mem hrmem
              exact ⟨p, hp⟩
          obtain ⟨pathRi, hpathRi⟩ := hpathRi
          have hseenNodup : (cseSeen f f.blocks.size).Nodup := by
            have htake : f.blocks.toList.take f.blocks.size = f.blocks.toList := by simp
            simpa [cseSeen, htake] using instrDefs_nodup hnd
          have local_bad (heq : ri = cur)
              (hdpreR : d ∈ preR.flatMap Instr.defs) : False := by
            have hrbb : rb = b := by
              subst ri
              exact Option.some.inj (hri.symm.trans hb)
            have hjpre : j ∈ pre := hj0pre heq
            obtain ⟨k, hkpreR, hkdef⟩ := List.mem_flatMap.mp hdpreR
            have hkBlock : k ∈ b.instrs := by
              rw [← hrbb, hseq]
              exact List.mem_append_left _ hkpreR
            have hieq : i = k :=
              instr_def_unique (d := d) hnd (block_mem_of_getElem? hb)
                (block_mem_of_getElem? hb) (by rw [hsplit]; simp) hkBlock hd hkdef
            have hipreR : i ∈ preR := by simpa [hieq] using hkpreR
            obtain ⟨pa, qa, hpa⟩ := List.mem_iff_append.mp hipreR
            obtain ⟨pb, qb, hpb⟩ := List.mem_iff_append.mp hjpre
            have hDR : Before d r (cseSeen f f.blocks.size) :=
              instr_order_before_mem (block_mem_of_getElem? hb)
                (pre := pa) (mid := qa) (post := postR) (i := i) (j := j)
                (by rw [← hrbb, hseq, hpa]) hd hjdef
            have hRD : Before r d (cseSeen f f.blocks.size) :=
              instr_order_before_mem (block_mem_of_getElem? hb)
                (pre := pb) (mid := qb) (post := post) (i := j) (j := i)
                (by rw [hsplit, hpb]) hjdef hd
            exact (Before.asymm hseenNodup hDR) hRD
          have cross_bad (hne : ri ≠ cur) (hrev : BlockDom f cur ri) : False := by
            have hs : StrictBlockDom f ri cur := by
              intro p hp
              exact (hrdom p hp).resolve_left hne
            exact (hs.not_reverse hpathRi) hrev
          simp only [substVs, List.mem_map] at hdargs
          obtain ⟨a, ha, had⟩ := hdargs
          cases hma : (cseSub f)[a]? with
          | none =>
              have had' : a = d := by
                simpa [substV, Std.HashMap.getD_eq_getD_getElem?, hma] using had
              subst a
              have hnotTail := hstable d ha
              by_cases heq : ri = cur
              · apply local_bad heq
                have hrbb : rb = b := by
                  subst ri
                  exact Option.some.inj (hri.symm.trans hb)
                have hiBlock : i ∈ rb.instrs := by
                  rw [hrbb, hsplit]
                  simp
                rw [hseq] at hiBlock
                rcases List.mem_append.mp hiBlock with hipre | hitail
                · exact List.mem_flatMap.mpr ⟨i, hipre, hd⟩
                · exact False.elim (hnotTail
                    (List.mem_flatMap.mpr ⟨i, hitail, hd⟩))
              · obtain ⟨x, hxj, hxd⟩ := horigin d ha
                have hrev : BlockDom f cur ri := by
                  cases hmx : (cseSub f)[x]? with
                  | none =>
                      have hxeq : x = d := by
                        have := hxd.trans had
                        simpa [substV, Std.HashMap.getD_eq_getD_getElem?,
                          hmx, hma] using this
                      subst x
                      exact blockDef_dominates_use hnd hli hdom hb
                        (ToAsm.mem_blockDefs.mpr (Or.inr
                          (List.mem_flatMap.mpr ⟨i, by rw [hsplit]; simp, hd⟩)))
                        hri (instr_use_mem_blockUses hjmem hxj)
                  | some y =>
                      have hyeq : y = d := by
                        have := hxd.trans had
                        simpa [substV, Std.HashMap.getD_eq_getD_getElem?,
                          hmx, hma] using this
                      subst y
                      exact cseSub_use_dom hnd hli hdom hwf hri hmx
                        (instr_use_mem_blockUses hjmem hxj) hb
                        (ToAsm.mem_blockDefs.mpr (Or.inr
                          (List.mem_flatMap.mpr ⟨i, by rw [hsplit]; simp, hd⟩)))
                exact False.elim (cross_bad heq hrev)
          | some d0 =>
              have hd0 : d0 = d := by
                simpa [substV, Std.HashMap.getD_eq_getD_getElem?, hma] using had
              subst d0
              obtain ⟨e, hdefA, hdefD⟩ := (cseFinalSubSound hnd).1 hma
              cases e with
              | const v =>
                  cases hdefD with
                  | @const bd _ v hbd hid =>
                      have heqi := instr_def_unique (d := d) hnd
                        (block_mem_of_getElem? hb) hbd (by rw [hsplit]; simp) hid
                        hd (by simp [Instr.defs])
                      exact hnconst v heqi
              | op yo aa =>
                  have haju : a ∈ j.uses := hdirect a ha (by rw [hma]; simp)
                  have hself : a ∈ j.defs → a ∉ j.uses := by
                    intro hajdef hajuse
                    exact (hstable a ha)
                      (List.mem_flatMap.mpr ⟨j, by simp, hajdef⟩)
                  have hseenA := cseSeen_of_op_use hnd hli hdom hwf hri hseq
                    haju hma hdefA hself
                  have hseenD := CseSeen.rep hnd hwf hri hpathRi
                    hseq hma hseenA
                  obtain ⟨di, db, hdb, hdflat, hdomD, hlocD⟩ := hseenD
                  have hdcur : d ∈ ToAsm.blockDefs b := ToAsm.mem_blockDefs.mpr
                    (Or.inr (List.mem_flatMap.mpr
                      ⟨i, by rw [hsplit]; simp, hd⟩))
                  have hddb : d ∈ ToAsm.blockDefs db :=
                    ToAsm.mem_blockDefs.mpr (Or.inr hdflat)
                  have hdicur : di = cur :=
                    block_def_index_unique hnd hdb hb hddb hdcur
                  subst di
                  by_cases heq : ri = cur
                  · apply local_bad heq
                    exact hlocD heq.symm
                  · exact False.elim (cross_bad heq hdomD)

omit model in
/-- If a non-constant instruction grows the operation table, its destination
is not among the final-substituted operands of that newly recorded entry. -/
theorem cseStep_dest_use_fresh_nonconst {f : Func} {li : Array (List ValId)}
    {n : Nat} (hnd : f.allDefs.Nodup) (hwf : f.wfCheck n = true)
    (hli : ToAsm.liveInSets f = some li) (hdom : ToAsm.Func.domCheck f = true)
    {cur : BlockId} {b : Block} (hb : f.blocks[cur]? = some b)
    {path : List BlockId} (hpath : EntryPath f path cur)
    {pre post : List Instr} {i : Instr}
    (hsplit : b.instrs = pre ++ i :: post) {d : ValId} (hd : d ∈ i.defs)
    (hnconst : ∀ v, i ≠ .const d v)
    (hchg : (cseInstrStep i (cseAt f cur b pre)).2.1 ≠
      (cseAt f cur b pre).2.1) :
    d ∉ (substInstr (cseSub f) i).uses := by
  cases i with
  | const d0 v =>
      have heq : d = d0 := by simpa [Instr.defs] using hd
      subst d0
      exact False.elim (hnconst v rfl)
  | call ds fid as =>
      exact False.elim (hchg rfl)
  | op ds yop as =>
      cases ds with
      | nil => simp [Instr.defs] at hd
      | cons d0 ds =>
          cases ds with
          | cons e es => exact False.elim (hchg rfl)
          | nil =>
              have heq : d = d0 := by simpa [Instr.defs] using hd
              subst d0
              let q := cseAt f cur b pre
              have hdpre : q.2.2.2.1[d]? = none :=
                cseAt_dest_none hnd hb hsplit (by simp [Instr.defs])
              by_cases hp : pureOp yop = true
              · cases hfind : q.2.1.ops.find? (fun x => x.1 ==
                    (yop, substVs q.2.2.2.1 as)) with
                | some entry =>
                    by_cases hu : q.2.2.1.contains d = true
                    · exfalso
                      apply hchg
                      simp [q, cseInstrStep, substInstr, hp, hfind, hu]
                    · exfalso
                      apply hchg
                      simp [q, cseInstrStep, substInstr, hp, hfind, hu]
                | none =>
                    by_cases hgadd : (substVs q.2.2.2.1 as).all (fun a =>
                        q.2.2.2.2.1.contains a ||
                          !q.2.2.2.2.2.contains a) = true
                    · intro hdUse
                      simp only [substInstr, Instr.uses, substVs,
                        List.mem_map] at hdUse
                      obtain ⟨x, hx, hxd⟩ := hdUse
                      cases hmx : (cseSub f)[x]? with
                      | none =>
                          have hxeq : x = d := by
                            simpa [substV, Std.HashMap.getD_eq_getD_getElem?,
                              hmx] using hxd
                          subst x
                          have hdBlock : d ∈ q.2.2.2.2.2 := by
                            have hdb : d ∈ cseBlockDefs b := by
                              rw [mem_cseBlockDefs]
                              rw [hsplit, List.flatMap_append, List.flatMap_cons]
                              simp [hd]
                            dsimp only [q, cseAt]
                            rw [cseInstrFold_blockDefs]
                            exact hdb
                          have hdNotDefined : d ∉ q.2.2.2.2.1 := by
                            intro hm
                            have hdPre : d ∈ pre.flatMap Instr.defs := by
                              simpa [q, cseAt] using
                                ((cseInstrFold_defined pre
                                  (⟨[], cseEntryTab f (inEdgeSources f)
                                    (csePrefix f cur).2.1 cur, ∅,
                                    (csePrefix f cur).2.2, ∅, cseBlockDefs b⟩ :
                                      CSEInner)).1 hm)
                            have hndb := blockInstrDefs_nodup hnd
                              (block_mem_of_getElem? hb)
                            rw [hsplit, List.flatMap_append, List.flatMap_cons,
                              List.nodup_append] at hndb
                            exact hndb.2.2 d hdPre d
                              (List.mem_append_left _ hd) rfl
                          have hdMid : d ∈ substVs q.2.2.2.1 as := by
                            simp only [substVs, List.mem_map]
                            exact ⟨d, hx, by
                              simp [substV, Std.HashMap.getD_eq_getD_getElem?,
                                hdpre]⟩
                          have hg := List.all_eq_true.mp hgadd d hdMid
                          rw [Bool.or_eq_true] at hg
                          rcases hg with hdefined | hout
                          · exact hdNotDefined
                              (Std.HashSet.contains_iff_mem.mp hdefined)
                          · have hc := Std.HashSet.mem_iff_contains.mp hdBlock
                            rw [hc] at hout
                            simp at hout
                      | some y =>
                          have hyeq : y = d := by
                            simpa [substV, Std.HashMap.getD_eq_getD_getElem?,
                              hmx] using hxd
                          subst y
                          obtain ⟨expr, hdefX, hdefD⟩ :=
                            (cseFinalSubSound hnd).1 hmx
                          cases expr with
                          | const v =>
                              cases hdefD with
                              | @const bd _ v hbd hid =>
                                  have heqi := instr_def_unique (d := d) hnd
                                    (block_mem_of_getElem? hb) hbd
                                    (by rw [hsplit]; simp) hid hd
                                    (by simp [Instr.defs])
                                  exact hnconst v heqi
                          | op yo aa =>
                              have hself : x ∈ (Instr.op [d] yop as).defs →
                                  x ∉ (Instr.op [d] yop as).uses := by
                                intro hxdef
                                have hxeq : x = d := by
                                  simpa [Instr.defs] using hxdef
                                subst x
                                have := cseSub_rangeFree hnd hmx
                                rw [hmx] at this
                                contradiction
                              have hseenX := cseSeen_of_op_use hnd hli hdom hwf
                                hb hsplit (by simpa [Instr.uses] using hx)
                                hmx hdefX hself
                              have hseenD := CseSeen.rep hnd hwf
                                hb hpath hsplit hmx hseenX
                              exact hseenD.not_defined_later hnd hb
                                (show b.instrs = pre ++ (Instr.op [d] yop as :: post)
                                  from hsplit)
                                (by rw [List.flatMap_cons]
                                    exact List.mem_append_left _ hd)
                    · exfalso
                      apply hchg
                      simp [q, cseInstrStep, substInstr, hp, hfind, hgadd]
              · exfalso
                apply hchg
                simp [cseInstrStep, substInstr, hp]

omit model in
theorem cseFresh {f : Func} {li : Array (List ValId)} {n : Nat}
    (hnd : f.allDefs.Nodup) (hwf : f.wfCheck n = true)
    (hli : ToAsm.liveInSets f = some li) (hdom : ToAsm.Func.domCheck f = true) :
    CseFresh f := by
  intro cur b hb path hpath pre post i hsplit d hd hnconst
  exact ⟨cseAt_rep_fresh hnd hwf hb hpath hsplit hd,
    cseAt_runtimeUse_fresh_nonconst hnd hwf hli hdom hb hpath hsplit hd hnconst,
    fun hchg => cseStep_dest_use_fresh_nonconst hnd hwf hli hdom hb hpath
      hsplit hd hnconst hchg⟩

end Passes

/-- Rebinding a certified constant destination preserves old table entries even
when a loop revisit has made that destination occur in an expression key: if it
is already bound, constant provenance says that it already contains the same
literal; if it is unbound, no successfully-readable runtime expression can use
it. -/
theorem CseTabRuntime.addConst_rebind {f : Func} {R R' : Regs}
    {tab : Passes.CseTab} {d : ValId} {v : U256}
    (h : CseTabRuntime (model := model) (Passes.cseSub f) R' tab)
    (hvals : d ∉ Passes.cseTabVals tab)
    (hdnone : (Passes.cseSub f)[d]? = none)
    (ha : R d = R' d) (hconst : CseConstRegs f R)
    (hdef : Passes.CseDef f (.const v) d) :
    CseTabRuntime (model := model) (Passes.cseSub f) (R'.set d v)
      {tab with consts := (v, d) :: tab.consts} := by
  cases hrd : R' d with
  | none =>
      apply h.addConst hvals
      intro hu
      simp only [cseTabRuntimeUses, List.mem_flatMap] at hu
      obtain ⟨⟨⟨yop, as⟩, d0⟩, hm, hx⟩ := hu
      obtain ⟨vals, w, s, s', hg, -, -⟩ := h.1 hm
      obtain ⟨wd, hwd⟩ := Regs.eq_some_of_getMany hg hx
      rw [hrd] at hwd
      contradiction
  | some w =>
      have hr : R d = some w := ha.trans hrd
      have hw : w = v := hconst hdef hr
      subst w
      have hset : R'.set d v = R' := by
        funext x
        by_cases hxd : x = d
        · subst x
          rw [Regs.set_same, hrd]
        · rw [Regs.set_other _ _ hxd]
      rw [hset]
      refine ⟨h.1, ?_⟩
      intro v0 d0 hm
      rcases List.mem_cons.mp hm with hhead | htail
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hhead
        simpa [CseExprRuntime] using hrd
      · exact h.2 htail

namespace Passes

/-- Lockstep execution of a source suffix against the CSE fold state at the
corresponding source boundary.  `CseFresh` is the static fold certificate used
only when a kept instruction binds registers while table entries remain live. -/
theorem cse_exec_aux {P : Prog} {f : Func} (hwf : f.wfCheck P.funcs.size = true)
    (hnd : f.allDefs.Nodup) {li : Array (List ValId)}
    (hli : ToAsm.liveInSets f = some li) (hdom : ToAsm.Func.domCheck f = true)
    (hfresh : CseFresh f) {R : Regs} {st : EvmState} {rest : Rest} {res : FRes}
    (hexec : Exec (model := model) P f R st rest res) :
    ∀ {cur : BlockId} {b : Block} {path : List BlockId} {pre : List Instr}
      {R' : Regs},
      f.blocks[cur]? = some b → EntryPath f path cur →
      b.instrs = pre ++ rest.instrs → rest.term = b.term →
      CseAgree f cur pre R R' → CseConstAgree f R R' →
      CseConstRegs f R →
      CseTabRuntime (model := model) (cseSub f) R' (cseAt f cur b pre).2.1 →
      Exec (model := model) P (cse f) R' st
        ⟨cseInstrsOut (cseSub f) rest.instrs (cseAt f cur b pre).2.1
          (cseAt f cur b pre).2.2.1 (cseAt f cur b pre).2.2.2.1
          (cseAt f cur b pre).2.2.2.2.1 (cseAt f cur b pre).2.2.2.2.2,
          substTerm (cseSub f) rest.term⟩ res := by
  induction hexec with
  | @const f R st d v is t res htail ih =>
      intro cur b path pre R' hb hpath hsplit ht ha hc hconst htab
      have hi : Instr.const d v ∈ b.instrs := by rw [hsplit]; simp
      have hbmem := block_mem_of_getElem? hb
      let q := cseAt f cur b pre
      have hdpre : q.2.2.2.1[d]? = none := cseAt_dest_none hnd hb hsplit
        (by simp [Instr.defs])
      cases hfind : q.2.1.consts.find? (fun x => x.1 == v) with
      | some entry =>
          obtain ⟨v0, d0⟩ := entry
          obtain ⟨hv0, hval⟩ := htab.const_of_find hfind
          subst v0
          have hsout : (cseInstrStep (.const d v) q).1 = [] := by
            simp [q, cseInstrStep, substInstr, hfind]
          have hmap : (cseSub f)[d]? = some d0 := by
            rw [cseAt_dest_final hnd hb hsplit (by simp [Instr.defs])]
            simp [q, cseInstrStep, substInstr, hfind]
          have hsplit' : b.instrs = (pre ++ [.const d v]) ++ is := by
            simpa [List.append_assoc] using hsplit
          have hnext := ih hwf hnd hli hdom hfresh hb hpath hsplit' ht
            (CseAgree.step_dropped (i := .const d v) (by simp [Instr.defs])
              hmap ha hval)
            (hc.const_dropped hnd hbmem hi hmap hval)
            (hconst.const hnd hbmem hi)
            (by simpa [cseAt_snoc, q, cseInstrStep, substInstr,
                hfind] using htab)
          rw [cseInstrsOut_at_drop hsout]
          simpa [Regs.setMany, Instr.defs] using hnext
      | none =>
          have hsout : (cseInstrStep (.const d v) q).1 =
              [substInstr q.2.2.2.1 (.const d v)] := by
            simp [q, cseInstrStep, substInstr, hfind]
          have hdnone : (cseSub f)[d]? = none := by
            rw [cseAt_dest_final hnd hb hsplit (by simp [Instr.defs])]
            simp [q, cseInstrStep, substInstr, hfind, hdpre]
          have hfr := cseAt_rep_fresh hnd hwf hb hpath hsplit
            (d := d) (by simp [Instr.defs])
          have hsplit' : b.instrs = (pre ++ [.const d v]) ++ is := by
            simpa [List.append_assoc] using hsplit
          have hnext := ih hwf hnd hli hdom hfresh hb hpath hsplit' ht
            (by simpa [Regs.setMany, Instr.defs] using
              (ha.step_kept hnd hwf hb hpath hsplit
                (fun x hx => by
                  have : x = d := by simpa [Instr.defs] using hx
                  subst x
                  exact hdnone) [v]))
            (hc.const_kept hnd hconst hbmem hi hdnone)
            (hconst.const hnd hbmem hi)
            (by simpa [cseAt_snoc, q, cseInstrStep, substInstr, hfind,
                Regs.setMany, Instr.defs] using
              (htab.addConst_rebind hfr hdnone (ha.1 d hdnone) hconst
                (.const hbmem hi)))
          rw [cseInstrsOut_at_keep hnd hb hsplit hsout]
          exact Exec.const hnext
  | @op f R st st' ds yop as args rets is t res hg hbi hlen htail ih =>
      intro cur b path pre R' hb hpath hsplit ht ha hc hconst htab
      have hi : Instr.op ds yop as ∈ b.instrs := by rw [hsplit]; simp
      have hbmem := block_mem_of_getElem? hb
      have harity := wfCheck_op_arity hwf hbmem hi
      cases ds with
      | nil =>
          let q := cseAt f cur b pre
          have hsout : (cseInstrStep (.op [] yop as) q).1 =
              [substInstr q.2.2.2.1 (.op [] yop as)] := by rfl
          have hget' := cseGetMany hnd ha hc (xs := as) (by
            intro x d0 yo aa hx hm hd
            apply cseSeen_of_op_use hnd hli hdom hwf hb hsplit
              (by simpa [Instr.uses] using hx) hm hd
            simp [Instr.defs]) hg
          have hsplit' : b.instrs = (pre ++ [.op [] yop as]) ++ is := by
            simpa [List.append_assoc] using hsplit
          have hnext := ih hwf hnd hli hdom hfresh hb hpath hsplit' ht
            (ha.step_kept hnd hwf hb hpath hsplit (by simp [Instr.defs]) rets)
            (hc.nonconst hnd hbmem hi (by intro d v h; cases h) rets)
            (hconst.nonconst hnd hbmem hi (by intro d v h; cases h) rets)
            (by simpa [cseAt_snoc, q, cseInstrStep, substInstr,
                Regs.setMany, Instr.defs] using htab)
          rw [cseInstrsOut_at_keep hnd hb hsplit hsout]
          exact Exec.op hget' hbi hlen hnext
      | cons d ds =>
          cases ds with
          | cons e es => simp at harity
          | nil =>
              let q := cseAt f cur b pre
              have hdpre : q.2.2.2.1[d]? = none := cseAt_dest_none hnd hb hsplit
                (by simp [Instr.defs])
              by_cases hp : pureOp yop = true
              · cases hfind : q.2.1.ops.find? (fun x => x.1 ==
                    (yop, substVs q.2.2.2.1 as)) with
                | some entry =>
                    obtain ⟨⟨yop0, as0⟩, d0⟩ := entry
                    by_cases hu : q.2.2.1.contains d = true
                    · have hsout : (cseInstrStep (.op [d] yop as) q).1 =
                          [substInstr q.2.2.2.1 (.op [d] yop as)] := by
                        simp [q, cseInstrStep, substInstr, hp, hfind, hu]
                      have hdnone : (cseSub f)[d]? = none := by
                        rw [cseAt_dest_final hnd hb hsplit (by simp [Instr.defs])]
                        simp [q, cseInstrStep, substInstr, hp, hfind, hu, hdpre]
                      have hget' := cseGetMany hnd ha hc (xs := as) (by
                        intro x d1 yo aa hx hm hd
                        apply cseSeen_of_op_use hnd hli hdom hwf hb hsplit
                          (by simpa [Instr.uses] using hx) hm hd
                        intro hxd
                        have : x = d := by simpa [Instr.defs] using hxd
                        subst x
                        rw [hdnone] at hm
                        contradiction) hg
                      have hfr := hfresh hb hpath hsplit d (by simp [Instr.defs])
                        (by intro v h; cases h)
                      have hsplit' : b.instrs = (pre ++ [.op [d] yop as]) ++ is := by
                        simpa [List.append_assoc] using hsplit
                      have hnext := ih hwf hnd hli hdom hfresh hb hpath hsplit' ht
                        (ha.step_kept hnd hwf hb hpath hsplit
                          (fun x hx => by
                            have : x = d := by simpa [Instr.defs] using hx
                            subst x
                            exact hdnone) rets)
                        (hc.nonconst hnd hbmem hi (by intro x v h; cases h) rets)
                        (hconst.nonconst hnd hbmem hi (by intro x v h; cases h) rets)
                        (by
                          have hr := htab.setMany_of_fresh (ds := [d])
                            (vals := rets) (fun x hx => by
                              have : x = d := by simpa using hx
                              subst x
                              exact ⟨hfr.1, hfr.2.1⟩)
                          simpa [cseAt_snoc, q, cseInstrStep,
                            substInstr, hp, hfind, hu, Instr.defs] using hr)
                      rw [cseInstrsOut_at_keep hnd hb hsplit hsout]
                      exact Exec.op hget' hbi hlen hnext
                    · have hsout : (cseInstrStep (.op [d] yop as) q).1 = [] := by
                        simp [q, cseInstrStep, substInstr, hp, hfind, hu]
                      have hmap : (cseSub f)[d]? = some d0 := by
                        rw [cseAt_dest_final hnd hb hsplit (by simp [Instr.defs])]
                        simp [q, cseInstrStep, substInstr, hp, hfind, hu]
                      obtain ⟨hyop0, has0, hrt⟩ := htab.op_of_find hfind
                      subst yop0
                      subst as0
                      have htabSound := cseAt_tab_sound hnd hb
                        (show b.instrs = pre ++ (.op [d] yop as :: is) from hsplit)
                      have hentry := htabSound.2 (List.mem_of_find?_eq_some hfind)
                      have hdomain := cseAt_tab_domain hnd hb
                        (show b.instrs = pre ++ (.op [d] yop as :: is) from hsplit)
                        (List.mem_of_find?_eq_some hfind)
                      have hdrop : CseDropPos f
                          (.op yop (substVs q.2.2.2.1 as)) d :=
                        .op hbmem hsplit rfl hdpre (by
                          intro hm
                          apply hu
                          apply Std.HashSet.mem_iff_contains.mp
                          have hmUsed : d ∈ q.2.2.1 := by
                            simpa [q, cseAt] using
                              ((cseInstrFold_used pre
                                (⟨[], cseEntryTab f (inEdgeSources f)
                                  (csePrefix f cur).2.1 cur, ∅,
                                  (csePrefix f cur).2.2, ∅, cseBlockDefs b⟩ :
                                    CSEInner)).2 (Or.inr hm))
                          exact hmUsed)
                      have hself : d ∉ (Instr.op [d] yop as).uses :=
                        cse_drop_not_self_use hnd hwf hli hdom (cseSub_rangeFree hnd)
                          (csePrefix_ordered hnd f.blocks.size (Nat.le_refl _))
                          hmap hdrop hentry hdomain hb hpath hi (by simp [Instr.defs])
                      have hget' := cseGetMany hnd ha hc (xs := as) (by
                        intro x d1 yo aa hx hm hd
                        apply cseSeen_of_op_use hnd hli hdom hwf hb hsplit
                          (by simpa [Instr.uses] using hx) hm hd
                        intro hxd
                        have : x = d := by simpa [Instr.defs] using hxd
                        subst x
                        exact hself) hg
                      have hgStored : R'.getMany
                          (substVs (cseSub f) (substVs q.2.2.2.1 as)) = some args := by
                        rw [substVs_absorb (cseAt_substExt hnd hb
                          (show b.instrs = pre ++ (Instr.op [d] yop as :: is)
                            from hsplit)) (cseSub_rangeFree hnd)]
                        exact hget'
                      obtain ⟨w, hrets, hval⟩ :=
                        CseExprRuntime.op_result hrt hp hgStored hbi
                      subst rets
                      have hst : st' = st := pure_state_eq hp hbi
                      subst st'
                      have hsplit' : b.instrs = (pre ++ [.op [d] yop as]) ++ is := by
                        simpa [List.append_assoc] using hsplit
                      have hnext := ih hwf hnd hli hdom hfresh hb hpath hsplit' ht
                        (by simpa [Regs.setMany, Instr.defs] using
                          (CseAgree.step_dropped (i := .op [d] yop as)
                            (by simp [Instr.defs]) hmap ha hval))
                        (hc.nonconst_left hnd hbmem hi (by intro x v h; cases h) [w])
                        (hconst.nonconst hnd hbmem hi (by intro x v h; cases h) [w])
                        (by simpa [cseAt_snoc, q, cseInstrStep,
                            substInstr, hp, hfind, hu] using htab)
                      rw [cseInstrsOut_at_drop hsout]
                      simpa [Regs.setMany, Instr.defs] using hnext
                | none =>
                    by_cases hgadd : (substVs q.2.2.2.1 as).all (fun a =>
                        q.2.2.2.2.1.contains a || !q.2.2.2.2.2.contains a) = true
                    · have hsout : (cseInstrStep (.op [d] yop as) q).1 =
                          [substInstr q.2.2.2.1 (.op [d] yop as)] := by
                        simp [q, cseInstrStep, substInstr, hp, hfind, hgadd]
                      have hdnone : (cseSub f)[d]? = none := by
                        rw [cseAt_dest_final hnd hb hsplit (by simp [Instr.defs])]
                        simp [q, cseInstrStep, substInstr, hp, hfind, hgadd, hdpre]
                      have hget' := cseGetMany hnd ha hc (xs := as) (by
                        intro x d1 yo aa hx hm hd
                        apply cseSeen_of_op_use hnd hli hdom hwf hb hsplit
                          (by simpa [Instr.uses] using hx) hm hd
                        intro hxd
                        have : x = d := by simpa [Instr.defs] using hxd
                        subst x
                        rw [hdnone] at hm
                        contradiction) hg
                      cases rets with
                      | nil => simp at hlen
                      | cons w ws =>
                          cases ws with
                          | cons z zs => simp at hlen
                          | nil =>
                              have hfr := hfresh hb hpath hsplit d (by simp [Instr.defs])
                                (by intro v h; cases h)
                              have hgetSet : (R'.set d w).getMany
                                  (substVs (cseSub f) (substVs q.2.2.2.1 as)) = some args := by
                                rw [substVs_absorb (cseAt_substExt hnd hb
                                  (show b.instrs = pre ++ (.op [d] yop as :: is)
                                    from hsplit)) (cseSub_rangeFree hnd)]
                                rw [← hget']
                                apply Regs.getMany_congr
                                intro x hx
                                rw [Regs.set_other]
                                intro heq
                                subst x
                                exact hfr.2.2 (by
                                  intro heqTab
                                  have hlenTab := congrArg
                                    (fun tab : CseTab => tab.ops.length) heqTab
                                  simp [q, cseInstrStep, substInstr, hp, hfind,
                                    hgadd] at hlenTab)
                                  (by simpa [substInstr, Instr.uses] using hx)
                              have hsplit' : b.instrs = (pre ++ [.op [d] yop as]) ++ is := by
                                simpa [List.append_assoc] using hsplit
                              have hnext := ih hwf hnd hli hdom hfresh hb hpath hsplit' ht
                                (by simpa [Regs.setMany, Instr.defs] using
                                  (ha.step_kept hnd hwf hb hpath hsplit
                                    (fun x hx => by
                                      have : x = d := by simpa [Instr.defs] using hx
                                      subst x
                                      exact hdnone) [w]))
                                (hc.nonconst hnd hbmem hi (by intro x v h; cases h) [w])
                                (hconst.nonconst hnd hbmem hi (by intro x v h; cases h) [w])
                                (by
                                  have hr := htab.addOp hfr.1 hfr.2.1 hgetSet (by
                                    simpa [substVs_absorb (cseAt_substExt hnd hb
                                      (show b.instrs = pre ++ (.op [d] yop as :: is)
                                        from hsplit)) (cseSub_rangeFree hnd)] using hbi)
                                  simpa [cseAt_snoc, q, cseInstrStep,
                                    substInstr, hp, hfind, hgadd, Instr.defs,
                                    Regs.setMany] using hr)
                              rw [cseInstrsOut_at_keep hnd hb hsplit hsout]
                              exact Exec.op hget' hbi hlen hnext
                    · have hsout : (cseInstrStep (.op [d] yop as) q).1 =
                          [substInstr q.2.2.2.1 (.op [d] yop as)] := by
                        simp [q, cseInstrStep, substInstr, hp, hfind, hgadd]
                      have hdnone : (cseSub f)[d]? = none := by
                        rw [cseAt_dest_final hnd hb hsplit (by simp [Instr.defs])]
                        simp [q, cseInstrStep, substInstr, hp, hfind, hgadd, hdpre]
                      have hget' := cseGetMany hnd ha hc (xs := as) (by
                        intro x d1 yo aa hx hm hd
                        apply cseSeen_of_op_use hnd hli hdom hwf hb hsplit
                          (by simpa [Instr.uses] using hx) hm hd
                        intro hxd
                        have : x = d := by simpa [Instr.defs] using hxd
                        subst x
                        rw [hdnone] at hm
                        contradiction) hg
                      have hfr := hfresh hb hpath hsplit d (by simp [Instr.defs])
                        (by intro v h; cases h)
                      have hsplit' : b.instrs = (pre ++ [.op [d] yop as]) ++ is := by
                        simpa [List.append_assoc] using hsplit
                      have hnext := ih hwf hnd hli hdom hfresh hb hpath hsplit' ht
                        (ha.step_kept hnd hwf hb hpath hsplit
                          (fun x hx => by
                            have : x = d := by simpa [Instr.defs] using hx
                            subst x
                            exact hdnone) rets)
                        (hc.nonconst hnd hbmem hi (by intro x v h; cases h) rets)
                        (hconst.nonconst hnd hbmem hi (by intro x v h; cases h) rets)
                        (by
                          have hr := htab.setMany_of_fresh (ds := [d])
                            (vals := rets) (fun x hx => by
                              have : x = d := by simpa using hx
                              subst x
                              exact ⟨hfr.1, hfr.2.1⟩)
                          simpa [cseAt_snoc, q, cseInstrStep,
                            substInstr, hp, hfind, hgadd, Instr.defs] using hr)
                      rw [cseInstrsOut_at_keep hnd hb hsplit hsout]
                      exact Exec.op hget' hbi hlen hnext
              · have hsout : (cseInstrStep (.op [d] yop as) q).1 =
                    [substInstr q.2.2.2.1 (.op [d] yop as)] := by
                  simp [q, cseInstrStep, substInstr, hp]
                have hdnone : (cseSub f)[d]? = none := by
                  rw [cseAt_dest_final hnd hb hsplit (by simp [Instr.defs])]
                  simp [q, cseInstrStep, substInstr, hp, hdpre]
                have hget' := cseGetMany hnd ha hc (xs := as) (by
                  intro x d1 yo aa hx hm hd
                  apply cseSeen_of_op_use hnd hli hdom hwf hb hsplit
                    (by simpa [Instr.uses] using hx) hm hd
                  intro hxd
                  have : x = d := by simpa [Instr.defs] using hxd
                  subst x
                  rw [hdnone] at hm
                  contradiction) hg
                have hfr := hfresh hb hpath hsplit d (by simp [Instr.defs])
                  (by intro v h; cases h)
                have hsplit' : b.instrs = (pre ++ [.op [d] yop as]) ++ is := by
                  simpa [List.append_assoc] using hsplit
                have hnext := ih hwf hnd hli hdom hfresh hb hpath hsplit' ht
                  (ha.step_kept hnd hwf hb hpath hsplit
                    (fun x hx => by
                      have : x = d := by simpa [Instr.defs] using hx
                      subst x
                      exact hdnone) rets)
                  (hc.nonconst hnd hbmem hi (by intro x v h; cases h) rets)
                  (hconst.nonconst hnd hbmem hi (by intro x v h; cases h) rets)
                  (by
                    have hr := htab.setMany_of_fresh (ds := [d])
                      (vals := rets) (fun x hx => by
                        have : x = d := by simpa using hx
                        subst x
                        exact ⟨hfr.1, hfr.2.1⟩)
                    simpa [cseAt_snoc, q, cseInstrStep,
                      substInstr, hp, Instr.defs] using hr)
                rw [cseInstrsOut_at_keep hnd hb hsplit hsout]
                exact Exec.op hget' hbi hlen hnext
  | @opHalt f R st st' ds yop as args is t hg hbi =>
      intro cur b path pre R' hb hpath hsplit ht ha hc hconst htab
      have hi : Instr.op ds yop as ∈ b.instrs := by rw [hsplit]; simp
      have hpureFalse : pureOp yop = false := by
        by_contra hp
        exact pure_no_halt (Bool.eq_true_of_not_eq_false hp) hbi
      let q := cseAt f cur b pre
      have hsout : (cseInstrStep (.op ds yop as) q).1 =
          [substInstr q.2.2.2.1 (.op ds yop as)] := by
        cases ds with
        | nil => rfl
        | cons d ds =>
            cases ds with
            | nil => simp [q, cseInstrStep, substInstr, hpureFalse]
            | cons e es => rfl
      have hget' := cseGetMany hnd ha hc (xs := as) (by
        intro x d0 yo aa hx hm hd
        apply cseSeen_of_op_use hnd hli hdom hwf hb hsplit
          (by simpa [Instr.uses] using hx) hm hd
        intro hxd
        have hdnone : (cseSub f)[x]? = none := by
          rw [cseAt_dest_final hnd hb hsplit hxd]
          cases ds with
          | nil => simp [Instr.defs] at hxd
          | cons d ds =>
              cases ds with
              | nil =>
                  simpa [q, cseInstrStep, substInstr, hpureFalse] using
                    (cseAt_dest_none hnd hb hsplit hxd)
              | cons e es => simp [cseInstrStep, substInstr,
                  cseAt_dest_none hnd hb hsplit hxd]
        rw [hdnone] at hm
        contradiction) hg
      rw [cseInstrsOut_at_keep hnd hb hsplit hsout]
      exact Exec.opHalt hget' hbi
  | @call f g R st st' ds as fid args rvals eb is t res hfid hg hplen heb hbody hlen htail ihbody ih =>
      intro cur b path pre R' hb hpath hsplit ht ha hc hconst htab
      let q := cseAt f cur b pre
      have hi : Instr.call ds fid as ∈ b.instrs := by rw [hsplit]; simp
      have hsout : (cseInstrStep (.call ds fid as) q).1 =
          [substInstr q.2.2.2.1 (.call ds fid as)] := by
        simp [q, cseInstrStep, substInstr]
      have hget' := cseGetMany hnd ha hc (xs := as) (by
        intro x d0 yo aa hx hm hd
        apply cseSeen_of_op_use hnd hli hdom hwf hb hsplit
          (by simpa [Instr.uses] using hx) hm hd
        intro hxd
        have hdnone : (cseSub f)[x]? = none := by
          rw [cseAt_dest_final hnd hb hsplit hxd]
          simp [cseInstrStep, substInstr,
            cseAt_dest_none hnd hb hsplit hxd]
        rw [hdnone] at hm
        contradiction) hg
      have hkept : ∀ x ∈ (Instr.call ds fid as).defs, (cseSub f)[x]? = none := by
        intro x hx
        rw [cseAt_dest_final hnd hb hsplit hx]
        simp [cseInstrStep, substInstr,
          cseAt_dest_none hnd hb hsplit hx]
      have hfr : ∀ x ∈ ds, x ∉ cseTabVals q.2.1 ∧
          x ∉ cseTabRuntimeUses (cseSub f) q.2.1 := by
        intro x hx
        have h := hfresh hb hpath hsplit x (by simpa [Instr.defs] using hx)
          (by intro v h; cases h)
        exact ⟨h.1, h.2.1⟩
      have hsplit' : b.instrs = (pre ++ [.call ds fid as]) ++ is := by
        simpa [List.append_assoc] using hsplit
      have hnext := ih hwf hnd hli hdom hfresh hb hpath hsplit' ht
        (ha.step_kept hnd hwf hb hpath hsplit hkept rvals)
        (hc.nonconst hnd (block_mem_of_getElem? hb) hi (by intro x v h; cases h) rvals)
        (hconst.nonconst hnd (block_mem_of_getElem? hb) hi
          (by intro x v h; cases h) rvals)
        (by
          have hr := htab.setMany_of_fresh (ds := ds) (vals := rvals) hfr
          simpa [cseAt_snoc, q, cseInstrStep, substInstr,
            Instr.defs] using hr)
      rw [cseInstrsOut_at_keep hnd hb hsplit hsout]
      exact Exec.call hfid hget' hplen heb hbody hlen hnext
  | @callHalt f g R st st' ds as fid args eb is t hfid hg hplen heb hbody ihbody =>
      intro cur b path pre R' hb hpath hsplit ht ha hc hconst htab
      let q := cseAt f cur b pre
      have hsout : (cseInstrStep (.call ds fid as) q).1 =
          [substInstr q.2.2.2.1 (.call ds fid as)] := by
        simp [q, cseInstrStep, substInstr]
      have hget' := cseGetMany hnd ha hc (xs := as) (by
        intro x d0 yo aa hx hm hd
        apply cseSeen_of_op_use hnd hli hdom hwf hb hsplit
          (by simpa [Instr.uses] using hx) hm hd
        intro hxd
        have hdnone : (cseSub f)[x]? = none := by
          rw [cseAt_dest_final hnd hb hsplit hxd]
          simp [cseInstrStep, substInstr,
            cseAt_dest_none hnd hb hsplit hxd]
        rw [hdnone] at hm
        contradiction) hg
      rw [cseInstrsOut_at_keep hnd hb hsplit hsout]
      exact Exec.callHalt hfid hget' hplen heb hbody
  | @jump f R st e tb vals res htb hg hplen hbody ih =>
      intro cur b path pre R' hb hpath hsplit ht ha hc hconst htab
      have hpre : pre = b.instrs := by simpa using hsplit.symm
      subst pre
      have he : e ∈ b.term.edges := by rw [← ht]; simp [Term.edges]
      have hget' := cseGetMany hnd ha hc (xs := e.args) (by
        intro x d0 yo aa hx hm hd
        apply cseSeen_of_use hnd hli hdom hb hm
        · rw [ToAsm.mem_blockUses]
          exact Or.inr (by rw [← ht]; simpa [Term.uses] using hx)
        · intro hlocal
          exact hlocal) hg
      let tb' := substBlock (csePrefix f f.blocks.size).2.2
        (cseBlockOut f e.target)
      have htb' : (cse f).blocks[e.target]? = some tb' := cse_block_get htb
      have htbBang : f.blocks[e.target]! = tb := by
        have hlt := (Array.getElem?_eq_some_iff.mp htb).1
        rw [getElem!_eq_getElem hlt]
        exact (Array.getElem?_eq_some_iff.mp htb).2
      have hpath' := EntryPath.edge hpath hb he
      have ha' := ha.jump hnd hb hpath he htb vals
      have hc' : CseConstAgree f (R.setMany tb.params vals)
          (R'.setMany tb.params vals) :=
        hc.params hnd (block_mem_of_getElem? htb) vals
      have hconst' : CseConstRegs f (R.setMany tb.params vals) :=
        hconst.params hnd (block_mem_of_getElem? htb) vals
      have htab' := CseTabRuntime.entry_of_edge hnd hb he htb
        (by simpa [cseAt_full hb] using htab) vals
      have hnext := ih hwf hnd hli hdom hfresh htb hpath' rfl rfl ha' hc'
        hconst' htab'
      have hnext' : Exec (model := model) P (cse f)
          (R'.setMany tb'.params vals) st ⟨tb'.instrs, tb'.term⟩ res := by
        simpa [tb', substBlock, cseBlockOut, htbBang, cseAt_nil,
          cseInstrsOut_eq_fold, cseSub] using hnext
      simpa [substTerm, substEdge, substVs, cseAt_nil, cseBlockOut,
        cseInstrsOut_eq_fold, cseSub] using
        (Exec.jump (P := P) (f := cse f) (e := substEdge (cseSub f) e)
          (args := vals) htb' (by simpa [substEdge] using hget')
          (by simpa [tb', substBlock, cseBlockOut, htbBang] using hplen) hnext')
  | @branchTrue f R st c v et ef tb vals res hc0 hv htb hg hplen hbody ih =>
      intro cur b path pre R' hb hpath hsplit ht ha hc hconst htab
      have hpre : pre = b.instrs := by simpa using hsplit.symm
      subst pre
      have he : et ∈ b.term.edges := by rw [← ht]; simp [Term.edges]
      have hread (xs : List ValId) (hxs : ∀ x ∈ xs, x ∈ b.term.uses) {vs}
          (hget : R.getMany xs = some vs) := cseGetMany hnd ha hc (xs := xs) (by
            intro x d0 yo aa hx hm hd
            apply cseSeen_of_use hnd hli hdom hb hm
            · rw [ToAsm.mem_blockUses]; exact Or.inr (hxs x hx)
            · intro hlocal; exact hlocal) hget
      have hc' : R' (substV (cseSub f) c) = some v := by
        have hg1 : R.getMany [c] = some [v] := by simp [Regs.getMany, hc0]
        have := hread [c] (by
          intro x hx
          have hxc : x = c := by simpa using hx
          subst x
          rw [← ht]
          simp [Term.uses]) hg1
        cases hcse : R' (substV (cseSub f) c) with
        | none => simp [Regs.getMany, substVs, hcse] at this
        | some w =>
            simp [Regs.getMany, substVs, hcse] at this
            subst w
            rfl
      have hget' := hread et.args (by intro x hx; rw [← ht]; simp [Term.uses, hx]) hg
      let tb' := substBlock (csePrefix f f.blocks.size).2.2
        (cseBlockOut f et.target)
      have htb' : (cse f).blocks[et.target]? = some tb' := cse_block_get htb
      have htbBang : f.blocks[et.target]! = tb := by
        have hlt := (Array.getElem?_eq_some_iff.mp htb).1
        rw [getElem!_eq_getElem hlt]
        exact (Array.getElem?_eq_some_iff.mp htb).2
      have hpath' := EntryPath.edge hpath hb he
      have ha' := ha.jump hnd hb hpath he htb vals
      have hcA : CseConstAgree f (R.setMany tb.params vals)
          (R'.setMany tb.params vals) :=
        hc.params hnd (block_mem_of_getElem? htb) vals
      have hconst' : CseConstRegs f (R.setMany tb.params vals) :=
        hconst.params hnd (block_mem_of_getElem? htb) vals
      have htab' := CseTabRuntime.entry_of_edge hnd hb he htb
        (by simpa [cseAt_full hb] using htab) vals
      have hnext := ih hwf hnd hli hdom hfresh htb hpath' rfl rfl ha' hcA
        hconst' htab'
      have hnext' : Exec (model := model) P (cse f)
          (R'.setMany tb'.params vals) st ⟨tb'.instrs, tb'.term⟩ res := by
        simpa [tb', substBlock, cseBlockOut, htbBang, cseAt_nil,
          cseInstrsOut_eq_fold, cseSub] using hnext
      simpa [substTerm, substEdge, substVs, cseAt_nil, cseBlockOut,
        cseInstrsOut_eq_fold, cseSub] using
        (Exec.branchTrue (P := P) (f := cse f)
          (c := substV (cseSub f) c) (et := substEdge (cseSub f) et)
          (ef := substEdge (cseSub f) ef) (args := vals) hc' hv htb'
          (by simpa [substEdge] using hget')
          (by simpa [tb', substBlock, cseBlockOut, htbBang] using hplen) hnext')
  | @branchFalse f R st c et ef tb vals res hc0 htb hg hplen hbody ih =>
      intro cur b path pre R' hb hpath hsplit ht ha hc hconst htab
      have hpre : pre = b.instrs := by simpa using hsplit.symm
      subst pre
      have he : ef ∈ b.term.edges := by rw [← ht]; simp [Term.edges]
      have hread (xs : List ValId) (hxs : ∀ x ∈ xs, x ∈ b.term.uses) {vs}
          (hget : R.getMany xs = some vs) := cseGetMany hnd ha hc (xs := xs) (by
            intro x d0 yo aa hx hm hd
            apply cseSeen_of_use hnd hli hdom hb hm
            · rw [ToAsm.mem_blockUses]; exact Or.inr (hxs x hx)
            · intro hlocal; exact hlocal) hget
      have hc' : R' (substV (cseSub f) c) = some 0 := by
        have hg1 : R.getMany [c] = some [0] := by simp [Regs.getMany, hc0]
        have := hread [c] (by
          intro x hx
          have hxc : x = c := by simpa using hx
          subst x
          rw [← ht]
          simp [Term.uses]) hg1
        cases hcse : R' (substV (cseSub f) c) with
        | none => simp [Regs.getMany, substVs, hcse] at this
        | some w =>
            simp [Regs.getMany, substVs, hcse] at this
            subst w
            rfl
      have hget' := hread ef.args (by intro x hx; rw [← ht]; simp [Term.uses, hx]) hg
      let tb' := substBlock (csePrefix f f.blocks.size).2.2
        (cseBlockOut f ef.target)
      have htb' : (cse f).blocks[ef.target]? = some tb' := cse_block_get htb
      have htbBang : f.blocks[ef.target]! = tb := by
        have hlt := (Array.getElem?_eq_some_iff.mp htb).1
        rw [getElem!_eq_getElem hlt]
        exact (Array.getElem?_eq_some_iff.mp htb).2
      have hpath' := EntryPath.edge hpath hb he
      have ha' := ha.jump hnd hb hpath he htb vals
      have hcA : CseConstAgree f (R.setMany tb.params vals)
          (R'.setMany tb.params vals) :=
        hc.params hnd (block_mem_of_getElem? htb) vals
      have hconst' : CseConstRegs f (R.setMany tb.params vals) :=
        hconst.params hnd (block_mem_of_getElem? htb) vals
      have htab' := CseTabRuntime.entry_of_edge hnd hb he htb
        (by simpa [cseAt_full hb] using htab) vals
      have hnext := ih hwf hnd hli hdom hfresh htb hpath' rfl rfl ha' hcA
        hconst' htab'
      have hnext' : Exec (model := model) P (cse f)
          (R'.setMany tb'.params vals) st ⟨tb'.instrs, tb'.term⟩ res := by
        simpa [tb', substBlock, cseBlockOut, htbBang, cseAt_nil,
          cseInstrsOut_eq_fold, cseSub] using hnext
      simpa [substTerm, substEdge, substVs, cseAt_nil, cseBlockOut,
        cseInstrsOut_eq_fold, cseSub] using
        (Exec.branchFalse (P := P) (f := cse f)
          (c := substV (cseSub f) c) (et := substEdge (cseSub f) et)
          (ef := substEdge (cseSub f) ef) (args := vals) hc' htb'
          (by simpa [substEdge] using hget')
          (by simpa [tb', substBlock, cseBlockOut, htbBang] using hplen) hnext')
  | @ret f R st xs vals hg =>
      intro cur b path pre R' hb hpath hsplit ht ha hc hconst htab
      have hpre : pre = b.instrs := by simpa using hsplit.symm
      subst pre
      have hget' := cseGetMany hnd ha hc (xs := xs) (by
        intro x d0 yo aa hx hm hd
        apply cseSeen_of_use hnd hli hdom hb hm
        · rw [ToAsm.mem_blockUses]; exact Or.inr (by rw [← ht]; simpa [Term.uses] using hx)
        · intro hlocal; exact hlocal) hg
      simpa [substTerm, cseInstrsOut, substVs] using
        (Exec.ret (P := P) (f := cse f) hget')
  | @halt f R st st' yop as args hg hbi =>
      intro cur b path pre R' hb hpath hsplit ht ha hc hconst htab
      have hpre : pre = b.instrs := by simpa using hsplit.symm
      subst pre
      have hget' := cseGetMany hnd ha hc (xs := as) (by
        intro x d0 yo aa hx hm hd
        apply cseSeen_of_use hnd hli hdom hb hm
        · rw [ToAsm.mem_blockUses]; exact Or.inr (by rw [← ht]; simpa [Term.uses] using hx)
        · intro hlocal; exact hlocal) hg
      simpa [substTerm, cseInstrsOut, substVs] using
        (Exec.halt (P := P) (f := cse f) hget' hbi)

end Passes

/-! ### Historical non-positional witness

The positional def-before-use lemma cannot be proved from the present
`wfCheck` and `domCheck` alone.  `ToAsm.liveStep` computes

    blockUses b \\ blockDefs b

after collecting the uses of *all* instructions in the block.  Consequently a
use before a later definition is removed by that later definition and never
reaches `liveIn(entry)`.  The following checked witness is deliberately kept
next to the blocked theorem: value `1` is read by the first instruction and
defined by the second, yet both checks accept and the sole live-in set is
empty.  The implementation's `usedSoFar` guard now prevents this witness from
creating a dropped *operation* destination: after the first instruction,
`usedSoFar.contains 1` is true.  The witness remains useful for documenting
why the proof must consume that guard rather than ask `domCheck` for a
sequential fact it does not establish. -/

private def cseLaterDefCounterexampleBlock : Block :=
  ⟨[], [.op [0] .add [1, 1], .const 1 0], .ret []⟩

private def cseLaterDefCounterexample : Func :=
  { params := [], nrets := 0, entry := 0
    blocks := #[cseLaterDefCounterexampleBlock] }

omit model in
private theorem cseLaterDefCounterexample_checks :
    cseLaterDefCounterexample.wfCheck 0 = true ∧
    ToAsm.Func.domCheck cseLaterDefCounterexample = true ∧
    ToAsm.liveInSets cseLaterDefCounterexample = some #[[]] ∧
    1 ∈ cseLaterDefCounterexampleBlock.instrs[0]!.uses ∧
    1 ∈ cseLaterDefCounterexampleBlock.instrs[1]!.defs := by
  native_decide

/-- **Pass 3 (local CSE) soundness**, under dominance.

The proof uses the same register-agreement invariant as pass 1, with `σ` the
accumulated dropped-definition substitution `d ↦ d₀`. The value-level obligation — that the
two computations agree — is `Passes.pure_rets_eq` (proved: a pure op's results
are a function of its arguments alone, in any state). What dominance buys is that
`d₀`'s binding is still the *current* one at every use of `d`: the pass only
inherits a table across a **single**-predecessor edge (`Passes.inEdgeSources`
returning `[p]` with `p < bi`), so `d₀`'s block dominates `d`'s block, and
`ToAsm.liveIn_of_succ` propagates that into the invariant. Without dominance the
substituted use can read a stale `d₀`, exactly as in the counterexample.

The static provenance half is `Passes.cseBlock_spec`, which resolves every
dropped definition to either an earlier emitted definition in the same block or
`cseAvail`, together with `Passes.cseAvail_succ`, which proves that inherited
availability comes from the actual unique predecessor; these facts also close
`cse_dom`.  Their runtime analogue carries, alongside the register substitution
invariant, that every entry-table representative contains the value certified by
its `CseDef`.  A kept instruction then steps on substituted arguments, while a
dropped `const`/pure op is skipped using that table fact and `pure_rets_eq`;
jumps hand the end-table fact to `cseAvail_succ`.

The runtime predicate and its lookup leaf are explicit above as
`CseTabRuntime` and `CseExprRuntime.op_result`.  Inherited tables are
filtered by `Passes.inheritTab`.  `CseTabRuntime.setMany_inheritTab` proves the
corresponding jump frame directly: filter membership excludes target parameters
from both representatives and stored expression arguments, and
`Passes.substV_not_blockParam` shows that the final substitution cannot map an
avoided argument back to a target parameter.  Thus `Regs.setMany` preserves the
whole inherited runtime table without a reachability/path witness.

`cseInstrsOut`/`cseInstrsOut_eq_fold` above expose the intra-block fold as a
recursive instruction list, so the kept/dropped cases can be matched directly
against `Exec`; the fold also tracks `blockDefs` and `definedSoFar`. -/

theorem cse_sound {P : Prog} {f : Func} {args : List U256} {st : EvmState} {res : FRes}
    {eb eb' : Block} (hwf : f.wfCheck P.funcs.size = true)
    (hdom : ToAsm.Func.domCheck f = true)
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.cse f).blocks[f.entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P (Passes.cse f) (Regs.empty.setMany f.params args) st
      ⟨eb'.instrs, eb'.term⟩ res := by
  have hnd : f.allDefs.Nodup := wfCheck_defs_nodup hwf
  obtain ⟨li, hli⟩ := ToAsm.liveInSets_isSome f
  have hfresh : Passes.CseFresh f := Passes.cseFresh hnd hwf hli hdom
  have hbout := Passes.cse_block_get heb
  rw [heb'] at hbout
  have heb'eq : eb' = Passes.substBlock (Passes.cseSub f)
      (Passes.cseBlockOut f f.entry) := by
    simpa [Passes.cseSub] using Option.some.inj hbout
  subst eb'
  have htab : CseTabRuntime (model := model) (Passes.cseSub f)
      (Regs.empty.setMany f.params args)
      (Passes.cseAt f f.entry eb []).2.1 := by
    simp [Passes.cseAt_nil, Passes.cseEntryTab, CseTabRuntime]
  have hsim := Passes.cse_exec_aux hwf hnd hli hdom hfresh hexec heb
    EntryPath.entry rfl rfl (CseAgree.of_entry rfl)
    (cseConstAgree_entry hnd args) (cseConstRegs_entry hnd args) htab
  have hentry : f.entry < f.blocks.size :=
    (Array.getElem?_eq_some_iff.mp heb).1
  have hbang : f.blocks[f.entry]! = eb := by
    rw [Passes.getElem!_eq_getElem hentry]
    exact (Array.getElem?_eq_some_iff.mp heb).2
  simpa [Passes.substBlock, Passes.cseBlockOut, hbang,
    Passes.cseInstrsOut_eq_fold, Passes.cseAt_nil,
    Passes.cseEntryTab] using hsim

end YulEvmCompiler.SsaCfg
