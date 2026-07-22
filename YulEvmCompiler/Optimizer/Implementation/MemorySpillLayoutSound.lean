import YulEvmCompiler.Optimizer.Implementation.MemorySpillSelect
set_option warningAsError true
/-!
# Memory-spill layout certificates

Proof-facing facts about the executable boundary check retained by every
successful spill layout.  The deeper lexical/call-path liveness proof builds
on these address-containment and coverage lemmas.
-/

namespace YulEvmCompiler.Optimizer.MemorySpillSelect

open YulSemantics
open YulSemantics.EVM

/-! ## Lexical allocator bounds

`LocalAlloc.slots` deliberately retains assignments made in scopes that have
already ended, while `next` is restored at scope exit.  The invariant below
is therefore phrased over every historical assignment: every color ever
issued is below `peak`, and the next live color is at most `peak`.
-/

def LocalAlloc.WF (st : LocalAlloc) : Prop :=
  st.next ≤ st.peak ∧ ∀ key color, (key, color) ∈ st.slots → color < st.peak

theorem localAlloc_empty_wf : LocalAlloc.WF {} := by
  simp [LocalAlloc.WF]

theorem allocName_wf_peak {selected : SpillSet} {owner : Owner}
    {st : LocalAlloc} (hst : st.WF) (x : Ident) :
    (allocName selected owner st x).WF ∧
      st.peak ≤ (allocName selected owner st x).peak := by
  by_cases hselected : selected.contains { owner, name := x } = true
  · unfold allocName
    simp only
    rw [if_pos hselected]
    simp only [LocalAlloc.WF, List.mem_cons]
    constructor
    · constructor
      · omega
      · intro itemKey color hmem
        rcases hmem with hnew | hold
        · cases hnew
          omega
        · exact lt_of_lt_of_le (hst.2 itemKey color hold) (Nat.le_max_left ..)
    · exact Nat.le_max_left ..
  · unfold allocName
    simp only
    rw [if_neg hselected]
    exact And.intro hst (le_refl st.peak)

theorem allocNames_wf_peak {selected : SpillSet} {owner : Owner}
    {st : LocalAlloc} (hst : st.WF) (xs : List Ident) :
    (allocNames selected owner st xs).WF ∧
      st.peak ≤ (allocNames selected owner st xs).peak := by
  induction xs generalizing st with
  | nil => simp [allocNames, hst]
  | cons x xs ih =>
      simp only [allocNames]
      have hx := allocName_wf_peak (selected := selected) (owner := owner) hst x
      have hxs := ih hx.1
      exact ⟨hxs.1, le_trans hx.2 hxs.2⟩

theorem allocScope_next (selected : SpillSet) (owner : Owner)
    (st : LocalAlloc) (body : Block Op) :
    (allocScope selected owner st body).next = st.next := by
  rw [allocScope.eq_1]

theorem allocCases_next (selected : SpillSet) (owner : Owner)
    (st : LocalAlloc) (cases : List (Literal × Block Op)) :
    (allocCases selected owner st cases).next = st.next := by
  induction cases generalizing st with
  | nil => rw [allocCases.eq_1]
  | cons item rest ih =>
      obtain ⟨lit, body⟩ := item
      rw [allocCases.eq_2, ih, allocScope_next]

mutual
  theorem allocStmt_wf_peak {selected : SpillSet} {owner : Owner}
      {st : LocalAlloc} (hst : st.WF) (stmt : Stmt Op) :
      (allocStmt selected owner st stmt).WF ∧
        st.peak ≤ (allocStmt selected owner st stmt).peak := by
    cases stmt with
    | letDecl xs val => rw [allocStmt.eq_1]; exact
        allocNames_wf_peak (selected := selected) (owner := owner) hst xs
    | block body => rw [allocStmt.eq_2]; exact
        allocScope_wf_peak (selected := selected) (owner := owner) hst body
    | cond c body => rw [allocStmt.eq_3]; exact
        allocScope_wf_peak (selected := selected) (owner := owner) hst body
    | switch e cases dflt =>
        have hcases := allocCases_wf_peak (selected := selected) (owner := owner) hst cases
        cases dflt with
        | none => rw [allocStmt.eq_5]; exact hcases
        | some body =>
            rw [allocStmt.eq_4]
            have hbody := allocScope_wf_peak (selected := selected) (owner := owner)
              hcases.1 body
            exact ⟨hbody.1, le_trans hcases.2 hbody.2⟩
    | forLoop init cond post body =>
        rw [allocStmt.eq_6]
        have hinit := allocStmts_wf_peak (selected := selected) (owner := owner) hst init
        have hbody := allocScope_wf_peak (selected := selected) (owner := owner)
          hinit.1 body
        have hpost := allocScope_wf_peak (selected := selected) (owner := owner)
          hbody.1 post
        constructor
        · refine ⟨?_, ?_⟩
          · exact le_trans hst.1 (le_trans hinit.2 (le_trans hbody.2 hpost.2))
          · intro key color hmem
            exact hpost.1.2 key color hmem
        · exact le_trans hinit.2 (le_trans hbody.2 hpost.2)
    | funDef f ps rs body => rw [allocStmt.eq_7]; exact And.intro hst (le_refl st.peak)
    | assign xs e => simpa [allocStmt] using And.intro hst (le_refl st.peak)
    | exprStmt e => simpa [allocStmt] using And.intro hst (le_refl st.peak)
    | _ => simpa [allocStmt] using And.intro hst (le_refl st.peak)
    termination_by 2 * sizeOf stmt

  theorem allocStmts_wf_peak {selected : SpillSet} {owner : Owner}
      {st : LocalAlloc} (hst : st.WF) (body : Block Op) :
      (allocStmts selected owner st body).WF ∧
        st.peak ≤ (allocStmts selected owner st body).peak := by
    cases body with
    | nil => simp [allocStmts, hst]
    | cons stmt rest =>
        simp only [allocStmts]
        have hstmt := allocStmt_wf_peak (selected := selected) (owner := owner) hst stmt
        have hrest := allocStmts_wf_peak (selected := selected) (owner := owner)
          hstmt.1 rest
        exact ⟨hrest.1, le_trans hstmt.2 hrest.2⟩
    termination_by 2 * sizeOf body

  theorem allocScope_wf_peak {selected : SpillSet} {owner : Owner}
      {st : LocalAlloc} (hst : st.WF) (body : Block Op) :
      (allocScope selected owner st body).WF ∧
        st.peak ≤ (allocScope selected owner st body).peak := by
    simp only [allocScope]
    have hbody := allocStmts_wf_peak (selected := selected) (owner := owner) hst body
    constructor
    · refine ⟨le_trans hst.1 hbody.2, ?_⟩
      intro key color hmem
      exact hbody.1.2 key color hmem
    · exact hbody.2
    termination_by 2 * sizeOf body + 1

  theorem allocCases_wf_peak {selected : SpillSet} {owner : Owner}
      {st : LocalAlloc} (hst : st.WF) (cases : List (Literal × Block Op)) :
      (allocCases selected owner st cases).WF ∧
        st.peak ≤ (allocCases selected owner st cases).peak := by
    cases cases with
    | nil => simp [allocCases, hst]
    | cons item rest =>
        obtain ⟨lit, body⟩ := item
        simp only [allocCases]
        have hbody := allocScope_wf_peak (selected := selected) (owner := owner) hst body
        have hrest := allocCases_wf_peak (selected := selected) (owner := owner)
          hbody.1 rest
        exact ⟨hrest.1, le_trans hbody.2 hrest.2⟩
    termination_by 2 * sizeOf cases + 1
end

theorem frameInfo_alloc_wf (selected : SpillSet) (defined : List Ident)
    (frame : Frame) : (frameInfo selected defined frame).alloc.WF := by
  simp only [frameInfo]
  let initial := allocNames selected frame.owner {} (frame.params ++ frame.returns)
  have hinitial : initial.WF :=
    (allocNames_wf_peak (selected := selected) (owner := frame.owner)
      localAlloc_empty_wf (frame.params ++ frame.returns)).1
  exact (allocStmts_wf_peak (selected := selected) (owner := frame.owner)
    hinitial frame.body).1

theorem frameInfos_alloc_wf {selected : SpillSet} {body : Block Op}
    {info : FrameInfo} (hmem : info ∈ frameInfos selected body) : info.alloc.WF := by
  simp only [frameInfos, List.mem_map] at hmem
  obtain ⟨frame, hframe, rfl⟩ := hmem
  exact frameInfo_alloc_wf selected ((frames body).filterMap (fun frame => frame.owner)) frame

/-! ## Frame placement intervals

The callee region starts at word zero.  A frame's own lexical colors start at
`maxCached cache info.callees`, above the largest direct-callee requirement.
These facts state that separation directly, independently of `layoutCheck`.
-/

private theorem maxCached_fold_ge_start (cache : NeedCache) (owners : List Owner)
    (start : Nat) :
    start ≤ owners.foldl
      (fun peak owner => max peak ((cachedNeed? cache owner).getD 0)) start := by
  induction owners generalizing start with
  | nil => exact le_rfl
  | cons owner rest ih =>
      simp only [List.foldl]
      exact le_trans (Nat.le_max_left ..) (ih _)

private theorem maxCached_fold_ge_mem (cache : NeedCache) {owners : List Owner}
    {owner : Owner} (hmem : owner ∈ owners) (start : Nat) :
    (cachedNeed? cache owner).getD 0 ≤ owners.foldl
      (fun peak item => max peak ((cachedNeed? cache item).getD 0)) start := by
  induction owners generalizing start with
  | nil => simp at hmem
  | cons head rest ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldl]
      rcases hmem with rfl | htail
      · exact le_trans (Nat.le_max_right ..)
          (maxCached_fold_ge_start cache rest _)
      · exact ih htail _

theorem maxCached_ge_of_mem {cache : NeedCache} {owners : List Owner}
    {owner : Owner} (hmem : owner ∈ owners) :
    (cachedNeed? cache owner).getD 0 ≤ maxCached cache owners := by
  exact maxCached_fold_ge_mem cache hmem 0

theorem placeFrame_slot_interval {base : Nat} {cache : NeedCache}
    {info : FrameInfo} (hwf : info.alloc.WF)
    {key : SpillKey} {address : Nat}
    (hmem : (key, address) ∈ placeFrame base cache info) :
    base + 32 * maxCached cache info.callees ≤ address ∧
      address + 32 ≤
        base + 32 * (maxCached cache info.callees + info.alloc.peak) := by
  unfold placeFrame at hmem
  simp only [List.mem_map] at hmem
  obtain ⟨⟨slotKey, color⟩, hcolor, heq⟩ := hmem
  cases heq
  have hlt := hwf.2 slotKey color hcolor
  omega

theorem placeFrame_above_callee {base : Nat} {cache : NeedCache}
    {info : FrameInfo} {callee : Owner} {need : Nat}
    (hwf : info.alloc.WF)
    (hcallee : callee ∈ info.callees)
    (hneed : cachedNeed? cache callee = some need)
    {key : SpillKey} {callerAddress calleeEnd : Nat}
    (hcaller : (key, callerAddress) ∈ placeFrame base cache info)
    (hcalleeEnd : calleeEnd ≤ base + 32 * need) :
    calleeEnd ≤ callerAddress := by
  have hstart := (placeFrame_slot_interval
    (info := info) (base := base) (cache := cache)
    (key := key) (address := callerAddress) hwf hcaller).1
  have hmax := maxCached_ge_of_mem (cache := cache) hcallee
  simp only [hneed, Option.getD_some] at hmax
  omega

/-- Direct caller/callee spill slots are disjoint once the cache entry is the
callee recurrence.  This is the exact arithmetic separation used by the
allocator: the complete callee interval ends where the caller's local interval
begins. -/
theorem placeFrame_call_edge_disjoint {base : Nat} {cache : NeedCache}
    {caller callee : FrameInfo} {need : Nat}
    (hcallerWF : caller.alloc.WF) (hcalleeWF : callee.alloc.WF)
    (hcallee : callee.owner ∈ caller.callees)
    (hcached : cachedNeed? cache callee.owner = some need)
    (hrecurrence : need =
      maxCached cache callee.callees + callee.alloc.peak)
    {callerKey calleeKey : SpillKey} {callerAddress calleeAddress : Nat}
    (hcaller : (callerKey, callerAddress) ∈ placeFrame base cache caller)
    (hcalleeSlot : (calleeKey, calleeAddress) ∈ placeFrame base cache callee) :
    calleeAddress + 32 ≤ callerAddress := by
  have hcalleeEnd :=
    (placeFrame_slot_interval hcalleeWF hcalleeSlot).2
  have hwithinNeed : calleeAddress + 32 ≤ base + 32 * need := by
    rw [hrecurrence]
    exact hcalleeEnd
  exact placeFrame_above_callee hcallerWF hcallee hcached hcaller hwithinNeed

theorem mem_placeFrames {base : Nat} {cache : NeedCache} {infos : List FrameInfo}
    {key : SpillKey} {address : Nat}
    (hmem : (key, address) ∈ placeFrames base cache infos) :
    ∃ info ∈ infos, (key, address) ∈ placeFrame base cache info := by
  exact List.mem_flatMap.mp hmem

/-- Every address emitted by `buildLayout` lies in the local interval of the
frame that emitted it.  The interval starts after all direct callee regions
and has exactly the frame's lexical peak width. -/
theorem buildLayout_slot_frame_interval {base : Nat} {selected : SpillSet}
    {body : Block Op} {layout : Layout}
    (hbuild : buildLayout base selected body = some layout)
    {key : SpillKey} {address : Nat} (hmem : (key, address) ∈ layout.slots) :
    ∃ info ∈ layout.infos,
      (key, address) ∈ placeFrame base layout.cache info ∧
      base + 32 * maxCached layout.cache info.callees ≤ address ∧
      address + 32 ≤
        base + 32 * (maxCached layout.cache info.callees + info.alloc.peak) := by
  unfold buildLayout at hbuild
  obtain ⟨⟨words, cache⟩, _, hresult⟩ :=
    Option.bind_eq_some_iff.mp hbuild
  cases hresult
  obtain ⟨info, hinfo, hplaced⟩ := mem_placeFrames hmem
  have hwf : info.alloc.WF := frameInfos_alloc_wf hinfo
  have hinter := placeFrame_slot_interval hwf hplaced
  exact ⟨info, hinfo, hplaced, hinter⟩

/-! ## Call-path need bounds -/

inductive AllNeedsTrace (infos : List FrameInfo) (fuel : Nat) :
    List Owner → NeedCache → Nat → NeedCache → Prop
  | nil (cache : NeedCache) : AllNeedsTrace infos fuel [] cache 0 cache
  | cons (owner : Owner) (rest : List Owner)
      (cache intermediate finalCache : NeedCache) (need restPeak : Nat)
      (head : needFrame infos fuel [] cache owner = some (need, intermediate))
      (tail : AllNeedsTrace infos fuel rest intermediate restPeak finalCache) :
      AllNeedsTrace infos fuel (owner :: rest) cache
        (max need restPeak) finalCache

theorem allNeeds_trace {infos : List FrameInfo} {fuel : Nat}
    {owners : List Owner} {cache finalCache : NeedCache} {words : Nat}
    (hneeds : allNeeds infos fuel owners cache = some (words, finalCache)) :
    AllNeedsTrace infos fuel owners cache words finalCache := by
  induction owners generalizing cache words finalCache with
  | nil =>
      rw [allNeeds.eq_1] at hneeds
      cases hneeds
      exact .nil cache
  | cons owner rest ih =>
      rw [allNeeds.eq_2] at hneeds
      cases hframe : needFrame infos fuel [] cache owner with
      | none => simp [hframe] at hneeds
      | some frameResult =>
          obtain ⟨need, intermediate⟩ := frameResult
          simp only [hframe] at hneeds
          change (allNeeds infos fuel rest intermediate).bind (fun tail =>
            some (max need tail.1, tail.2)) = some (words, finalCache) at hneeds
          cases hrest : allNeeds infos fuel rest intermediate with
          | none => simp [hrest] at hneeds
          | some restResult =>
              obtain ⟨restPeak, restCache⟩ := restResult
              rw [hrest] at hneeds
              cases hneeds
              exact .cons owner rest cache intermediate restCache need restPeak
                hframe (ih hrest)

theorem AllNeedsTrace.owner_bound {infos : List FrameInfo} {fuel : Nat}
    {owners : List Owner} {cache finalCache : NeedCache} {words : Nat}
    (htrace : AllNeedsTrace infos fuel owners cache words finalCache)
    {owner : Owner} (hmem : owner ∈ owners) :
    ∃ before need after,
      needFrame infos fuel [] before owner = some (need, after) ∧
      need ≤ words := by
  induction htrace with
  | nil => simp at hmem
  | cons head rest before intermediate finalCache need restPeak hhead htail ih =>
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hrest
      · exact ⟨before, need, intermediate, hhead, Nat.le_max_left ..⟩
      · obtain ⟨tailBefore, tailNeed, tailAfter, htailCall, htailBound⟩ := ih hrest
        exact ⟨tailBefore, tailNeed, tailAfter, htailCall,
          le_trans htailBound (Nat.le_max_right ..)⟩

/-- The first frame processed by `allNeeds` contributes a need no larger than
the reported global word bound.  The recursive theorem applies again to each
tail invocation, so the `max` aggregation cannot silently discard a frame. -/
theorem allNeeds_cons_bound {infos : List FrameInfo} {fuel : Nat}
    {owner : Owner} {rest : List Owner} {cache finalCache : NeedCache}
    {words : Nat}
    (hneeds : allNeeds infos fuel (owner :: rest) cache =
      some (words, finalCache)) :
    ∃ need intermediate,
      needFrame infos fuel [] cache owner = some (need, intermediate) ∧
      need ≤ words := by
  rw [allNeeds.eq_2] at hneeds
  cases hframe : needFrame infos fuel [] cache owner with
  | none => simp [hframe] at hneeds
  | some frameResult =>
      obtain ⟨need, intermediate⟩ := frameResult
      simp only [hframe] at hneeds
      change (allNeeds infos fuel rest intermediate).bind (fun tail =>
        some (max need tail.1, tail.2)) = some (words, finalCache) at hneeds
      cases hrest : allNeeds infos fuel rest intermediate with
      | none => simp [hrest] at hneeds
      | some restResult =>
          obtain ⟨restPeak, restCache⟩ := restResult
          rw [hrest] at hneeds
          cases hneeds
          exact ⟨need, intermediate, rfl, by omega⟩

/-- A freshly computed frame need includes its whole lexical peak.  This is
the additive part of the call-path recurrence (`childPeak + localPeak`). -/
theorem needFrame_uncached_ge_local {infos : List FrameInfo} {fuel : Nat}
    {visiting : List Owner} {cache finalCache : NeedCache} {owner : Owner}
    {need : Nat}
    (huncached : cachedNeed? cache owner = none)
    (hneed : needFrame infos (fuel + 1) visiting cache owner =
      some (need, finalCache)) :
    ∃ info, findInfo? infos owner = some info ∧ info.alloc.peak ≤ need := by
  rw [needFrame.eq_2] at hneed
  simp only [huncached] at hneed
  split at hneed
  · contradiction
  · cases hinfo : findInfo? infos owner with
    | none => simp [hinfo] at hneed
    | some info =>
        simp only [hinfo] at hneed
        let step := fun (state : Nat × NeedCache) (callee : Owner) => do
          let (childNeed, cache') ←
            needFrame infos fuel (owner :: visiting) state.2 callee
          pure (max state.1 childNeed, cache')
        change (info.callees.foldlM step (0, cache)).bind (fun child =>
          some (child.1 + info.alloc.peak,
            (owner, child.1 + info.alloc.peak) :: child.2)) =
          some (need, finalCache) at hneed
        cases hchildren : info.callees.foldlM step (0, cache) with
        | none =>
            rw [hchildren] at hneed
            simp at hneed
        | some childResult =>
            obtain ⟨childPeak, childCache⟩ := childResult
            rw [hchildren] at hneed
            simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hneed
            exact ⟨info, rfl, by omega⟩

/-! ## Executable recurrence certificate extraction -/

theorem layoutCheck_needLayout {base reserved : Nat} {selected : SpillSet}
    {layout : Layout} (hcheck : layoutCheck base reserved selected layout = true) :
    needLayoutCheck layout = true := by
  unfold layoutCheck at hcheck
  simp only [Bool.and_eq_true] at hcheck
  exact hcheck.1.1.1.1

theorem layoutCheck_selected_nodup {base reserved : Nat} {selected : SpillSet}
    {layout : Layout} (hcheck : layoutCheck base reserved selected layout = true) :
    selected.Nodup := by
  unfold layoutCheck at hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact hcheck.1.2

theorem layoutCheck_slotKeys_nodup {base reserved : Nat} {selected : SpillSet}
    {layout : Layout} (hcheck : layoutCheck base reserved selected layout = true) :
    (layout.slots.map Prod.fst).Nodup := by
  unfold layoutCheck at hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact hcheck.2

theorem needLayoutCheck_infoOwners_nodup {layout : Layout}
    (hcheck : needLayoutCheck layout = true) :
    (layout.infos.map fun info => info.owner).Nodup := by
  unfold needLayoutCheck at hcheck
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcheck
  exact hcheck.1.1.1.1

theorem needLayoutCheck_cacheOwners_nodup {layout : Layout}
    (hcheck : needLayoutCheck layout = true) :
    (layout.cache.map Prod.fst).Nodup := by
  unfold needLayoutCheck at hcheck
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcheck
  exact hcheck.1.1.1.2

theorem needLayoutCheck_words {layout : Layout}
    (hcheck : needLayoutCheck layout = true) :
    layout.words = maxCached layout.cache
      (layout.infos.map fun info => info.owner) := by
  unfold needLayoutCheck at hcheck
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcheck
  exact hcheck.1.2

theorem localAllocCheck_wf {alloc : LocalAlloc}
    (hcheck : localAllocCheck alloc = true) : alloc.WF := by
  unfold localAllocCheck at hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  refine ⟨hcheck.1, ?_⟩
  intro key color hmem
  have hcolor := List.all_eq_true.mp hcheck.2 (key, color) hmem
  simpa only [decide_eq_true_eq] using hcolor

theorem needLayoutCheck_info {layout : Layout}
    (hcheck : needLayoutCheck layout = true) {info : FrameInfo}
    (hmem : info ∈ layout.infos) :
    info.alloc.WF ∧
      (∀ callee ∈ info.callees, ∃ need,
        cachedNeed? layout.cache callee = some need) ∧
      cachedNeed? layout.cache info.owner =
        some (maxCached layout.cache info.callees + info.alloc.peak) := by
  unfold needLayoutCheck at hcheck
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcheck
  have hinfo := List.all_eq_true.mp hcheck.1.1.2 info hmem
  simp only [Bool.and_eq_true, beq_iff_eq] at hinfo
  refine ⟨localAllocCheck_wf hinfo.1, ?_, hinfo.2.2.2⟩
  intro callee hcallee
  have hsome := List.all_eq_true.mp hinfo.2.2.1 callee hcallee
  simpa only [Option.isSome_iff_exists] using hsome

theorem needLayoutCheck_slot_owner {layout : Layout}
    (hcheck : needLayoutCheck layout = true) {info : FrameInfo}
    (hinfoMem : info ∈ layout.infos) {key : SpillKey} {color : Nat}
    (hslot : (key, color) ∈ info.alloc.slots) : key.owner = info.owner := by
  unfold needLayoutCheck at hcheck
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcheck
  have hinfo := List.all_eq_true.mp hcheck.1.1.2 info hinfoMem
  simp only [Bool.and_eq_true, beq_iff_eq] at hinfo
  have howner := List.all_eq_true.mp hinfo.2.1 (key, color) hslot
  simpa only [beq_iff_eq] using howner

theorem layoutCheck_placeFrame_call_edge_disjoint
    {base reserved : Nat} {selected : SpillSet} {layout : Layout}
    (hcheck : layoutCheck base reserved selected layout = true)
    {caller callee : FrameInfo}
    (hcallerInfo : caller ∈ layout.infos)
    (hcalleeInfo : callee ∈ layout.infos)
    (hcallee : callee.owner ∈ caller.callees)
    {callerKey calleeKey : SpillKey} {callerAddress calleeAddress : Nat}
    (hcaller : (callerKey, callerAddress) ∈
      placeFrame base layout.cache caller)
    (hcalleeSlot : (calleeKey, calleeAddress) ∈
      placeFrame base layout.cache callee) :
    calleeAddress + 32 ≤ callerAddress := by
  have hneedCheck := layoutCheck_needLayout hcheck
  have hcallerCert := needLayoutCheck_info hneedCheck hcallerInfo
  have hcalleeCert := needLayoutCheck_info hneedCheck hcalleeInfo
  exact placeFrame_call_edge_disjoint hcallerCert.1 hcalleeCert.1 hcallee
    hcalleeCert.2.2 rfl hcaller hcalleeSlot

def frameCutoff (base : Nat) (layout : Layout) (info : FrameInfo) : Nat :=
  base + 32 * (maxCached layout.cache info.callees + info.alloc.peak)

theorem layoutCheck_placeFrame_slot_end_le_cutoff
    {base reserved : Nat} {selected : SpillSet} {layout : Layout}
    (hcheck : layoutCheck base reserved selected layout = true)
    {info : FrameInfo} (hinfo : info ∈ layout.infos)
    {key : SpillKey} {address : Nat}
    (hslot : (key, address) ∈ placeFrame base layout.cache info) :
    address + 32 ≤ frameCutoff base layout info := by
  exact (placeFrame_slot_interval
    (needLayoutCheck_info (layoutCheck_needLayout hcheck) hinfo).1 hslot).2

theorem layoutCheck_callee_cutoff_le_caller_slot
    {base reserved : Nat} {selected : SpillSet} {layout : Layout}
    (hcheck : layoutCheck base reserved selected layout = true)
    {caller callee : FrameInfo}
    (hcallerInfo : caller ∈ layout.infos)
    (hcalleeInfo : callee ∈ layout.infos)
    (hcallee : callee.owner ∈ caller.callees)
    {callerKey : SpillKey} {callerAddress : Nat}
    (hcaller : (callerKey, callerAddress) ∈
      placeFrame base layout.cache caller) :
    frameCutoff base layout callee ≤ callerAddress := by
  have hneed := layoutCheck_needLayout hcheck
  have hcallerCert := needLayoutCheck_info hneed hcallerInfo
  have hcalleeCert := needLayoutCheck_info hneed hcalleeInfo
  exact placeFrame_above_callee hcallerCert.1 hcallee hcalleeCert.2.2
    hcaller (by simp [frameCutoff])

/-- A direct child's complete frame need is included in its caller's cached
child peak, even when the caller has no local spill slot. -/
theorem layoutCheck_callee_cutoff_le_caller_cutoff
    {base reserved : Nat} {selected : SpillSet} {layout : Layout}
    (hcheck : layoutCheck base reserved selected layout = true)
    {caller callee : FrameInfo}
    (hcallerInfo : caller ∈ layout.infos)
    (hcalleeInfo : callee ∈ layout.infos)
    (hcallee : callee.owner ∈ caller.callees) :
    frameCutoff base layout callee ≤ frameCutoff base layout caller := by
  have hneed := layoutCheck_needLayout hcheck
  have hcallerCert := needLayoutCheck_info hneed hcallerInfo
  have hcalleeCert := needLayoutCheck_info hneed hcalleeInfo
  obtain ⟨need, hcached⟩ := hcallerCert.2.1 callee.owner hcallee
  have hmax := maxCached_ge_of_mem (cache := layout.cache) hcallee
  rw [hcached] at hmax
  simp only [Option.getD_some] at hmax
  have hneedEq : need =
      maxCached layout.cache callee.callees + callee.alloc.peak := by
    exact Option.some.inj (hcached.symm.trans hcalleeCert.2.2)
  simp only [frameCutoff]
  omega

theorem buildLayout_slot_frame_owner {base reserved : Nat}
    {selected : SpillSet} {body : Block Op} {layout : Layout}
    (hbuild : buildLayout base selected body = some layout)
    (hcheck : layoutCheck base reserved selected layout = true)
    {key : SpillKey} {address : Nat} (hmem : (key, address) ∈ layout.slots) :
    ∃ info ∈ layout.infos,
      info.owner = key.owner ∧
        (key, address) ∈ placeFrame base layout.cache info := by
  obtain ⟨info, hinfo, hplaced, _⟩ :=
    buildLayout_slot_frame_interval hbuild hmem
  unfold placeFrame at hplaced
  obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hplaced
  obtain ⟨slotKey, color⟩ := item
  simp only at heq
  have hkey : slotKey = key := congrArg Prod.fst heq
  subst slotKey
  have howner := needLayoutCheck_slot_owner
    (layoutCheck_needLayout hcheck) hinfo hitem
  exact ⟨info, hinfo, howner.symm, by
    unfold placeFrame
    exact List.mem_map.mpr ⟨(key, color), hitem, heq⟩⟩

theorem layoutCheck_frame_need_le_words
    {base reserved : Nat} {selected : SpillSet} {layout : Layout}
    (hcheck : layoutCheck base reserved selected layout = true)
    {info : FrameInfo} (hinfo : info ∈ layout.infos) :
    maxCached layout.cache info.callees + info.alloc.peak ≤ layout.words := by
  have hneedCheck := layoutCheck_needLayout hcheck
  have hcert := needLayoutCheck_info hneedCheck hinfo
  have howner : info.owner ∈ layout.infos.map (fun frame => frame.owner) := by
    exact List.mem_map.mpr ⟨info, hinfo, rfl⟩
  have hmax := maxCached_ge_of_mem (cache := layout.cache) howner
  rw [hcert.2.2] at hmax
  simp only [Option.getD_some] at hmax
  rw [needLayoutCheck_words hneedCheck]
  exact hmax

/-- Every certified frame cutoff lies within the layout's peak call-path
reservation, including frames with no locally allocated spill cell. -/
theorem layoutCheck_frameCutoff_le_words
    {base reserved : Nat} {selected : SpillSet} {layout : Layout}
    (hcheck : layoutCheck base reserved selected layout = true)
    {info : FrameInfo} (hinfo : info ∈ layout.infos) :
    frameCutoff base layout info ≤ base + 32 * layout.words := by
  have hneed := layoutCheck_frame_need_le_words hcheck hinfo
  simp only [frameCutoff]
  omega

theorem layoutCheck_placeFrame_within_words
    {base reserved : Nat} {selected : SpillSet} {layout : Layout}
    (hcheck : layoutCheck base reserved selected layout = true)
    {info : FrameInfo} (hinfo : info ∈ layout.infos)
    {key : SpillKey} {address : Nat}
    (hslot : (key, address) ∈ placeFrame base layout.cache info) :
    address + 32 ≤ base + 32 * layout.words := by
  have hcert := needLayoutCheck_info (layoutCheck_needLayout hcheck) hinfo
  have hlocal := (placeFrame_slot_interval hcert.1 hslot).2
  have hwords := layoutCheck_frame_need_le_words hcheck hinfo
  omega

theorem layoutCheck_slot {base reserved : Nat} {selected : SpillSet}
    {layout : Layout} (hcheck : layoutCheck base reserved selected layout = true)
    {key : SpillKey} {address : Nat} (hmem : (key, address) ∈ layout.slots) :
    key ∈ selected ∧ base ≤ address ∧ address + 32 ≤ reserved ∧
      (address - base) % 32 = 0 := by
  unfold layoutCheck at hcheck
  simp only [Bool.and_eq_true] at hcheck
  have hslots := hcheck.1.1.1.2
  have hitem := List.all_eq_true.mp hslots (key, address) hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hitem
  refine ⟨?_, hitem.1.1.2, hitem.1.2, hitem.2⟩
  simpa using hitem.1.1.1

theorem layoutCheck_distinct_slots_disjoint
    {base reserved : Nat} {selected : SpillSet} {layout : Layout}
    (hcheck : layoutCheck base reserved selected layout = true)
    {leftKey rightKey : SpillKey} {left right : Nat}
    (hleft : (leftKey, left) ∈ layout.slots)
    (hright : (rightKey, right) ∈ layout.slots)
    (hne : left ≠ right) :
    left + 32 ≤ right ∨ right + 32 ≤ left := by
  have hl := layoutCheck_slot hcheck hleft
  have hr := layoutCheck_slot hcheck hright
  have hldvd : 32 ∣ left - base :=
    (Nat.dvd_iff_mod_eq_zero).2 hl.2.2.2
  have hrdvd : 32 ∣ right - base :=
    (Nat.dvd_iff_mod_eq_zero).2 hr.2.2.2
  obtain ⟨leftWord, hleftWord⟩ := hldvd
  obtain ⟨rightWord, hrightWord⟩ := hrdvd
  have hleftForm : left = base + 32 * leftWord := by omega
  have hrightForm : right = base + 32 * rightWord := by omega
  omega

theorem layoutCheck_covers {base reserved : Nat} {selected : SpillSet}
    {layout : Layout} (hcheck : layoutCheck base reserved selected layout = true)
    {key : SpillKey} (hmem : key ∈ selected) :
    ∃ address, (key, address) ∈ layout.slots := by
  unfold layoutCheck at hcheck
  simp only [Bool.and_eq_true] at hcheck
  have hselected := hcheck.1.1.2
  have hsome := List.all_eq_true.mp hselected key hmem
  simp only [Option.isSome_iff_exists] at hsome
  obtain ⟨⟨itemKey, itemAddress⟩, hfind⟩ := hsome
  have hmemItem := List.mem_of_find?_eq_some hfind
  have hkey : itemKey = key := by
    have := List.find?_some hfind
    simpa using this
  subst itemKey
  exact ⟨itemAddress, hmemItem⟩

theorem slotFor_mem_of_eq_some {slots : SlotMap} {owner : Owner}
    {name : Ident} {address : Nat}
    (hslot : slotFor? slots owner name = some address) :
    ({ owner, name }, address) ∈ slots := by
  unfold slotFor? slotForKey? at hslot
  cases hfind : slots.find? (fun item => item.1 = { owner, name }) with
  | none => simp [hfind] at hslot
  | some item =>
      obtain ⟨key, foundAddress⟩ := item
      simp only [hfind, Option.map_some, Option.some.injEq] at hslot
      subst foundAddress
      have hmem := List.mem_of_find?_eq_some hfind
      have hkey := List.find?_some hfind
      have hkey' := of_decide_eq_true hkey
      clear hkey
      change key = { owner, name } at hkey'
      subst key
      exact hmem

theorem layoutCheck_selected_slot {base reserved : Nat} {selected : SpillSet}
    {layout : Layout} (hcheck : layoutCheck base reserved selected layout = true)
    {owner : Owner} {name : Ident} (hselected : { owner, name } ∈ selected) :
    ∃ address, slotFor? layout.slots owner name = some address := by
  obtain ⟨address, hmem⟩ := layoutCheck_covers hcheck hselected
  unfold slotFor? slotForKey?
  have hsome :
      (layout.slots.find? fun item => item.1 = { owner, name }).isSome = true := by
    rw [List.find?_isSome]
    exact ⟨({ owner, name }, address), hmem, by simp⟩
  cases hfind : layout.slots.find? (fun item => item.1 = { owner, name }) with
  | none => simp [hfind] at hsome
  | some item =>
      exact ⟨item.2, by simp only [Option.map_some]⟩

theorem layoutCheck_slot_selected {base reserved : Nat} {selected : SpillSet}
    {layout : Layout} (hcheck : layoutCheck base reserved selected layout = true)
    {owner : Owner} {name : Ident} {address : Nat}
    (hslot : slotFor? layout.slots owner name = some address) :
    { owner, name } ∈ selected :=
  (layoutCheck_slot hcheck (slotFor_mem_of_eq_some hslot)).1

theorem layoutCheck_slotFor_bounds {base reserved : Nat}
    {selected : SpillSet} {layout : Layout}
    (hcheck : layoutCheck base reserved selected layout = true)
    {owner : Owner} {name : Ident} {address : Nat}
    (hslot : slotFor? layout.slots owner name = some address) :
    base ≤ address ∧ address + 32 ≤ reserved := by
  have hcert := layoutCheck_slot hcheck (slotFor_mem_of_eq_some hslot)
  exact ⟨hcert.2.1, hcert.2.2.1⟩

/-! ## Lexical-lifetime certificate extraction

These are the proof-facing facts used by the rewrite simulation.  The
structural simulation shows that its current selected environment is one of
the `frameLives` snapshots retained by `buildLayout`; the first theorem below
ties those snapshots back to the source block.  The executable check then
supplies a lockstep address list with no duplicates.
-/

theorem liveStmt_entry_subset_out (selected : SpillSet) (owner : Owner)
    (live : SpillSet) (stmt : Stmt Op) :
    ∀ key ∈ live, key ∈ (liveStmt selected owner live stmt).2 := by
  intro key hkey
  cases stmt with
  | letDecl xs val =>
      simpa only [liveStmt] using
        List.mem_append_right (selectedKeys selected owner xs) hkey
  | exprStmt _ => simpa only [liveStmt] using hkey
  | assign _ _ => simpa only [liveStmt] using hkey
  | block _ => simpa only [liveStmt] using hkey
  | cond _ _ => simpa only [liveStmt] using hkey
  | switch _ _ dflt => cases dflt <;> simpa only [liveStmt] using hkey
  | forLoop _ _ _ _ => simpa only [liveStmt] using hkey
  | funDef _ _ _ _ => simpa only [liveStmt] using hkey
  | _ => simpa only [liveStmt] using hkey

theorem liveStmts_entry_subset_out (selected : SpillSet) (owner : Owner) :
    ∀ (body : Block Op) (live : SpillSet),
      ∀ key ∈ live, key ∈ (liveStmts selected owner live body).2 := by
  intro body
  induction body with
  | nil => simp [liveStmts]
  | cons stmt rest ih =>
      intro live key hkey
      simp only [liveStmts]
      apply ih
      exact liveStmt_entry_subset_out selected owner live stmt key hkey

theorem liveStmts_out_mem_sets (selected : SpillSet) (owner : Owner) :
    ∀ (body : Block Op) (live : SpillSet),
      (liveStmts selected owner live body).2 ∈
        (liveStmts selected owner live body).1 := by
  intro body
  induction body with
  | nil => simp [liveStmts]
  | cons stmt rest ih =>
      intro live
      simp only [liveStmts]
      apply List.mem_append_right
      exact ih (liveStmt selected owner live stmt).2

/-- Every entry environment of a lexical statement sequence is contained in
one retained maximal set.  Structural simulation applies this theorem at each
nested block; append-membership in the defining `liveStmt` equation lifts that
set into the enclosing frame trace. -/
theorem liveStmts_entry_covered (selected : SpillSet) (owner : Owner)
    (body : Block Op) (live : SpillSet) :
    ∃ maxLive ∈ (liveStmts selected owner live body).1,
      ∀ key ∈ live, key ∈ maxLive := by
  refine ⟨(liveStmts selected owner live body).2,
    liveStmts_out_mem_sets selected owner body live, ?_⟩
  exact liveStmts_entry_subset_out selected owner body live

theorem buildLayout_lives {base : Nat} {selected : SpillSet}
    {body : Block Op} {layout : Layout}
    (hbuild : buildLayout base selected body = some layout) :
    layout.lives = (frames body).map (frameLives selected) := by
  unfold buildLayout at hbuild
  obtain ⟨result, _, hresult⟩ := Option.bind_eq_some_iff.mp hbuild
  cases hresult
  rfl

theorem buildLayout_infos {base : Nat} {selected : SpillSet}
    {body : Block Op} {layout : Layout}
    (hbuild : buildLayout base selected body = some layout) :
    layout.infos = frameInfos selected body := by
  unfold buildLayout at hbuild
  obtain ⟨result, _, hresult⟩ := Option.bind_eq_some_iff.mp hbuild
  cases hresult
  rfl

theorem buildLayout_frameInfo_mem {base : Nat} {selected : SpillSet}
    {body : Block Op} {layout : Layout}
    (hbuild : buildLayout base selected body = some layout)
    {frame : Frame} (hframe : frame ∈ frames body) :
    frameInfo selected ((frames body).filterMap (·.owner)) frame ∈ layout.infos := by
  rw [buildLayout_infos hbuild]
  unfold frameInfos
  exact List.mem_map.mpr ⟨frame, hframe, rfl⟩

private theorem eq_of_mem_of_map_nodup {α β : Type} {items : List α}
    {project : α → β} [DecidableEq β] {left right : α}
    (hnodup : (items.map project).Nodup)
    (hleft : left ∈ items) (hright : right ∈ items)
    (heq : project left = project right) : left = right := by
  induction items generalizing left right with
  | nil => simp at hleft
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hleft hright
      rcases hleft with rfl | hleft
      · rcases hright with rfl | hright
        · rfl
        · exact False.elim (hnodup.1 (heq ▸
            List.mem_map.mpr ⟨right, hright, rfl⟩))
      · rcases hright with rfl | hright
        · exact False.elim (hnodup.1 (heq.symm ▸
            List.mem_map.mpr ⟨left, hleft, rfl⟩))
        · exact ih hnodup.2 hleft hright heq

/-- A selected key owned by a source frame is placed in that exact frame's
interval.  Owner uniqueness in the executable layout rules out a different
same-owner frame. -/
theorem buildLayout_slot_in_frame {base reserved : Nat}
    {selected : SpillSet} {body : Block Op} {layout : Layout}
    (hbuild : buildLayout base selected body = some layout)
    (hcheck : layoutCheck base reserved selected layout = true)
    {frame : Frame} (hframe : frame ∈ frames body)
    {key : SpillKey} {address : Nat}
    (howner : key.owner = frame.owner)
    (hslot : slotForKey? layout.slots key = some address) :
    (key, address) ∈ placeFrame base layout.cache
      (frameInfo selected ((frames body).filterMap (·.owner)) frame) := by
  have hmem := slotFor_mem_of_eq_some hslot
  obtain ⟨found, hfoundInfo, hfoundOwner, hfoundSlot⟩ :=
    buildLayout_slot_frame_owner hbuild hcheck hmem
  have hexpected := buildLayout_frameInfo_mem hbuild hframe
  have howners := needLayoutCheck_infoOwners_nodup
    (layoutCheck_needLayout hcheck)
  have heq : found = frameInfo selected ((frames body).filterMap (·.owner)) frame :=
    eq_of_mem_of_map_nodup howners hfoundInfo hexpected (by
      simpa [frameInfo, howner] using hfoundOwner)
  simpa [heq] using hfoundSlot

theorem buildLayout_slotFor_end_le_frameCutoff {base reserved : Nat}
    {selected : SpillSet} {body : Block Op} {layout : Layout}
    (hbuild : buildLayout base selected body = some layout)
    (hcheck : layoutCheck base reserved selected layout = true)
    {frame : Frame} (hframe : frame ∈ frames body)
    {name : Ident} {address : Nat}
    (hslot : slotFor? layout.slots frame.owner name = some address) :
    address + 32 ≤ frameCutoff base layout
      (frameInfo selected ((frames body).filterMap (·.owner)) frame) := by
  let info := frameInfo selected ((frames body).filterMap (·.owner)) frame
  have hinfo : info ∈ layout.infos := buildLayout_frameInfo_mem hbuild hframe
  have hplaced : ({ owner := frame.owner, name }, address) ∈
      placeFrame base layout.cache info :=
    buildLayout_slot_in_frame hbuild hcheck hframe rfl hslot
  exact layoutCheck_placeFrame_slot_end_le_cutoff hcheck hinfo hplaced

theorem buildLayout_frameLives_mem {base : Nat} {selected : SpillSet}
    {body : Block Op} {layout : Layout}
    (hbuild : buildLayout base selected body = some layout)
    {frame : Frame} (hframe : frame ∈ frames body) :
    frameLives selected frame ∈ layout.lives := by
  rw [buildLayout_lives hbuild]
  exact List.mem_map.mpr ⟨frame, hframe, rfl⟩

theorem lexicalLayoutCheck_owners_nodup {layout : Layout}
    (hcheck : lexicalLayoutCheck layout = true) :
    (layout.lives.map fun trace => trace.owner).Nodup := by
  unfold lexicalLayoutCheck at hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact hcheck.1

theorem lexicalLayoutCheck_liveSet {layout : Layout}
    (hcheck : lexicalLayoutCheck layout = true)
    {trace : FrameLives} (htrace : trace ∈ layout.lives)
    {live : SpillSet} (hlive : live ∈ trace.sets) :
    ∃ addresses,
      slotsForKeys? layout.slots live = some addresses ∧
      live.Nodup ∧ addresses.Nodup := by
  unfold lexicalLayoutCheck at hcheck
  simp only [Bool.and_eq_true] at hcheck
  have htraceCheck := List.all_eq_true.mp hcheck.2 trace htrace
  have hliveCheck := List.all_eq_true.mp htraceCheck live hlive
  unfold liveSetCheck at hliveCheck
  cases hslots : slotsForKeys? layout.slots live with
  | none => simp [hslots] at hliveCheck
  | some addresses =>
      simp only [hslots, Bool.and_eq_true, decide_eq_true_eq] at hliveCheck
      exact ⟨addresses, rfl, hliveCheck⟩

theorem needLayoutCheck_lexical {layout : Layout}
    (hcheck : needLayoutCheck layout = true) :
    lexicalLayoutCheck layout = true := by
  unfold needLayoutCheck at hcheck
  simp only [Bool.and_eq_true] at hcheck
  exact hcheck.2

theorem layoutCheck_liveSet {base reserved : Nat} {selected : SpillSet}
    {layout : Layout} (hcheck : layoutCheck base reserved selected layout = true)
    {trace : FrameLives} (htrace : trace ∈ layout.lives)
    {live : SpillSet} (hlive : live ∈ trace.sets) :
    ∃ addresses,
      slotsForKeys? layout.slots live = some addresses ∧
      live.Nodup ∧ addresses.Nodup := by
  exact lexicalLayoutCheck_liveSet
    (needLayoutCheck_lexical (layoutCheck_needLayout hcheck)) htrace hlive

private theorem slotForKey_mem_addresses {slots : SlotMap} {keys : SpillSet}
    {addresses : List Nat} (hslots : slotsForKeys? slots keys = some addresses)
    {key : SpillKey} (hkey : key ∈ keys) {address : Nat}
    (haddress : slotForKey? slots key = some address) :
    address ∈ addresses := by
  induction keys generalizing addresses key address with
  | nil => simp at hkey
  | cons head rest ih =>
      rw [slotsForKeys?.eq_2] at hslots
      cases hhead : slotForKey? slots head with
      | none => simp [hhead] at hslots
      | some headAddress =>
          simp only [hhead] at hslots
          cases hrest : slotsForKeys? slots rest with
          | none => simp [hrest] at hslots
          | some tailAddresses =>
              rw [hrest] at hslots
              cases hslots
              simp only [List.mem_cons] at hkey ⊢
              rcases hkey with rfl | hkey
              · rw [hhead] at haddress
                cases haddress
                exact Or.inl rfl
              · exact Or.inr (ih hrest hkey haddress)

private theorem slotsForKeys_ne {slots : SlotMap} {keys : SpillSet}
    {addresses : List Nat} (hslots : slotsForKeys? slots keys = some addresses)
    (hkeys : keys.Nodup) (haddresses : addresses.Nodup)
    {leftKey rightKey : SpillKey}
    (hleftMem : leftKey ∈ keys) (hrightMem : rightKey ∈ keys)
    (hkeysNe : leftKey ≠ rightKey)
    {leftAddress rightAddress : Nat}
    (hleft : slotForKey? slots leftKey = some leftAddress)
    (hright : slotForKey? slots rightKey = some rightAddress) :
    leftAddress ≠ rightAddress := by
  induction keys generalizing addresses leftKey rightKey with
  | nil => simp at hleftMem
  | cons head rest ih =>
      rw [slotsForKeys?.eq_2] at hslots
      cases hhead : slotForKey? slots head with
      | none => simp [hhead] at hslots
      | some headAddress =>
          simp only [hhead] at hslots
          cases hrest : slotsForKeys? slots rest with
          | none => simp [hrest] at hslots
          | some tailAddresses =>
              rw [hrest] at hslots
              cases hslots
              simp only [List.nodup_cons] at hkeys haddresses
              simp only [List.mem_cons] at hleftMem hrightMem
              rcases hleftMem with rfl | hleftTail
              · have hleftEq : leftAddress = headAddress := by
                  rw [hhead] at hleft
                  exact (Option.some.inj hleft).symm
                subst leftAddress
                have hrightTail : rightKey ∈ rest := by
                  rcases hrightMem with hrightHead | hrightTail
                  · exact False.elim (hkeysNe hrightHead.symm)
                  · exact hrightTail
                have hrightAddressMem :=
                  slotForKey_mem_addresses hrest hrightTail hright
                exact fun heq => haddresses.1 (heq ▸ hrightAddressMem)
              · rcases hrightMem with rfl | hrightTail
                · have hrightEq : rightAddress = headAddress := by
                    rw [hhead] at hright
                    exact (Option.some.inj hright).symm
                  subst rightAddress
                  have hleftAddressMem :=
                    slotForKey_mem_addresses hrest hleftTail hleft
                  exact fun heq => haddresses.1 (heq.symm ▸ hleftAddressMem)
                · exact ih hrest hkeys.2 haddresses.2 hleftTail hrightTail
                    hkeysNe hleft hright

/-- Two distinct selected bindings in one executable lexical-live snapshot
cannot name the same spill word.  Sibling snapshots are intentionally not
related by this theorem and may reuse an address. -/
theorem layoutCheck_live_slots_ne {base reserved : Nat} {selected : SpillSet}
    {layout : Layout} (hcheck : layoutCheck base reserved selected layout = true)
    {trace : FrameLives} (htrace : trace ∈ layout.lives)
    {live : SpillSet} (hlive : live ∈ trace.sets)
    {leftKey rightKey : SpillKey}
    (hleftMem : leftKey ∈ live) (hrightMem : rightKey ∈ live)
    (hkeysNe : leftKey ≠ rightKey)
    {leftAddress rightAddress : Nat}
    (hleft : slotForKey? layout.slots leftKey = some leftAddress)
    (hright : slotForKey? layout.slots rightKey = some rightAddress) :
    leftAddress ≠ rightAddress := by
  obtain ⟨addresses, hslots, hkeys, haddresses⟩ :=
    layoutCheck_liveSet hcheck htrace hlive
  exact slotsForKeys_ne hslots hkeys haddresses hleftMem hrightMem hkeysNe
    hleft hright

/-- Source-indexed form consumed by the structural rewrite proof.  Its live
environment need only be a subset of one maximal set in `frameLives`; the two
bindings below are supplied by that subset invariant. -/
theorem buildLayout_live_slots_ne {base reserved : Nat} {selected : SpillSet}
    {body : Block Op} {layout : Layout}
    (hbuild : buildLayout base selected body = some layout)
    (hcheck : layoutCheck base reserved selected layout = true)
    {frame : Frame} (hframe : frame ∈ frames body)
    {maxLive : SpillSet} (hmax : maxLive ∈ (frameLives selected frame).sets)
    {leftKey rightKey : SpillKey}
    (hleftMem : leftKey ∈ maxLive) (hrightMem : rightKey ∈ maxLive)
    (hkeysNe : leftKey ≠ rightKey)
    {leftAddress rightAddress : Nat}
    (hleft : slotForKey? layout.slots leftKey = some leftAddress)
    (hright : slotForKey? layout.slots rightKey = some rightAddress) :
    leftAddress ≠ rightAddress := by
  exact layoutCheck_live_slots_ne hcheck
    (buildLayout_frameLives_mem hbuild hframe) hmax hleftMem hrightMem hkeysNe
    hleft hright

theorem groupsClosedCheck_group {groups : List SpillSet}
    {selected group : SpillSet}
    (hcheck : groupsClosedCheck groups selected = true)
    (hgroup : group ∈ groups) :
    group.Nodup ∧
      (group.any selected.contains = true →
        group.all selected.contains = true) := by
  unfold groupsClosedCheck at hcheck
  have hitem := List.all_eq_true.mp hcheck group hgroup
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hitem
  refine ⟨hitem.1, ?_⟩
  intro hany
  simpa [hany] using hitem.2

theorem groupsClosedCheck_group_dichotomy {groups : List SpillSet}
    {selected group : SpillSet}
    (hcheck : groupsClosedCheck groups selected = true)
    (hgroup : group ∈ groups) :
    group.Nodup ∧
      ((∀ key ∈ group, key ∈ selected) ∨
        (∀ key ∈ group, key ∉ selected)) := by
  have hcert := groupsClosedCheck_group hcheck hgroup
  refine ⟨hcert.1, ?_⟩
  cases hany : group.any selected.contains with
  | true =>
      left
      have hall := hcert.2 hany
      intro key hmem
      have hkey := List.all_eq_true.mp hall key hmem
      simpa [List.contains_eq_mem] using hkey
  | false =>
      right
      intro key hmem hselected
      have hcontains : selected.contains key = true := by
        simpa [List.contains_eq_mem] using hselected
      have : group.any selected.contains = true := by
        simp only [List.any_eq_true]
        exact ⟨key, hmem, hcontains⟩
      rw [this] at hany
      contradiction

/-- Every successful spilling result retains the executable allocation
certificate checked by `spillBlock?`.  Downstream simulation theorems consume
this fact rather than re-running or trusting the allocator. -/
theorem spillBlock_layoutCheck {body : Block Op} {result : Result}
    (hspill : spillBlock? body = some result) :
    layoutCheck result.base result.reserved result.selection result.layout = true := by
  unfold spillBlock? at hspill
  simp at hspill
  obtain ⟨guards, _, hguards⟩ := Option.bind_eq_some_iff.mp hspill.2
  obtain ⟨base, _, hbase⟩ := Option.bind_eq_some_iff.mp hguards
  simp at hbase
  obtain ⟨selected, _, hselected⟩ := Option.bind_eq_some_iff.mp hbase.2
  obtain ⟨provisional, _, hprovisional⟩ := Option.bind_eq_some_iff.mp hselected
  simp at hprovisional
  obtain ⟨_, _, _, _, _, _, hlayoutBind⟩ := hprovisional
  obtain ⟨layout, _, hlayout⟩ := Option.bind_eq_some_iff.mp hlayoutBind
  simp at hlayout
  rcases hlayout with ⟨_, hcheck, _, _, rfl⟩
  exact hcheck

/-- Proof-facing decomposition of every policy gate crossed by a successful
spill.  It records the raw guard authority, the selected layout, freshness,
the address bound, and the final compiler-pressure check in one reusable
certificate. -/
structure SpillFacts (body : Block Op) (result : Result) (guards : List Nat) : Prop where
  no_msize : MemorySpill.containsMsizeStmts body = false
  guards_collected : MemorySpill.collectMemoryGuardsStmts? body = some guards
  guards_head : guards.head? = some result.base
  guards_nonempty : guards ≠ []
  guards_consistent : ∀ value ∈ guards, value = result.base
  frames_wf : framesWF (frames
    (resolveMemoryGuardStmts result.base result.reserved body)) = true
  signatures_wf : frameSignaturesWF (frames
    (resolveMemoryGuardStmts result.base result.reserved body)) = true
  selected : selectSpills body = some result.selection
  selected_wf : selectedWF (frames
    (resolveMemoryGuardStmts result.base result.reserved body)) result.selection = true
  groups_closed :
    groupsClosedCheck (coupledStmts none
      (resolveMemoryGuardStmts result.base result.reserved body))
      result.selection = true
  layout_built : buildLayout result.base result.selection
    (resolveMemoryGuardStmts result.base result.reserved body) = some result.layout
  words_nonzero : result.layout.words ≠ 0
  reserved_eq : result.reserved = result.base + 32 * result.layout.words
  reserved_lt : result.reserved < 2 ^ 256
  layout_check :
    layoutCheck result.base result.reserved result.selection result.layout = true
  temps_fresh : ∀ name ∈ MemorySpill.declaredStmts
      (resolveMemoryGuardStmts result.base result.reserved body),
    ¬tempPrefix.toList <+: String.toList name
  pressure_clean :
    firstPressure []
      (rewriteStmts result.layout.slots none []
        (resolveMemoryGuardStmts result.base result.reserved body)) = none
  block_eq : result.block =
    rewriteStmts result.layout.slots none []
      (resolveMemoryGuardStmts result.base result.reserved body)

theorem frameSignaturesWF_frame {allFrames : List Frame} {frame : Frame}
    (hcheck : frameSignaturesWF allFrames = true)
    (hframe : frame ∈ allFrames) :
    (frame.params ++ frame.returns).Nodup := by
  have hitem := List.all_eq_true.mp hcheck frame hframe
  simpa only [decide_eq_true_eq] using hitem

theorem SpillFacts.frameCutoff_le_reserved {body : Block Op} {result : Result}
    {guards : List Nat} (hfacts : SpillFacts body result guards)
    {frame : Frame}
    (hframe : frame ∈ frames
      (resolveMemoryGuardStmts result.base result.reserved body)) :
    frameCutoff result.base result.layout
        (frameInfo result.selection
          ((frames (resolveMemoryGuardStmts result.base result.reserved body)).filterMap
            (·.owner)) frame) ≤ result.reserved := by
  have hinfo := buildLayout_frameInfo_mem hfacts.layout_built hframe
  have hcutoff := layoutCheck_frameCutoff_le_words hfacts.layout_check hinfo
  rwa [← hfacts.reserved_eq] at hcutoff

theorem spillBlock_facts {body : Block Op} {result : Result}
    (hspill : spillBlock? body = some result) :
    ∃ guards, SpillFacts body result guards := by
  unfold spillBlock? at hspill
  simp at hspill
  obtain ⟨guards, hcollect, hguards⟩ := Option.bind_eq_some_iff.mp hspill.2
  obtain ⟨base, hhead, hbase⟩ := Option.bind_eq_some_iff.mp hguards
  simp at hbase
  obtain ⟨selection, hselection, hselected⟩ :=
    Option.bind_eq_some_iff.mp hbase.2
  obtain ⟨provisional, hprovisionalBuild, hprovisional⟩ :=
    Option.bind_eq_some_iff.mp hselected
  simp at hprovisional
  rcases hprovisional with
    ⟨hwords, hreserved, hframes, hsignatures, hselectedWF, hgroups, hlayoutBind⟩
  obtain ⟨layout, hbuild, hlayout⟩ := Option.bind_eq_some_iff.mp hlayoutBind
  simp at hlayout
  rcases hlayout with
    ⟨hwordEq, hcheck, hfresh, hpressure, hresult⟩
  subst result
  refine ⟨guards, ?_⟩
  exact {
    no_msize := hspill.1
    guards_collected := hcollect
    guards_head := hhead
    guards_nonempty := hbase.1.1
    guards_consistent := hbase.1.2
    frames_wf := hframes
    signatures_wf := hsignatures
    selected := hselection
    selected_wf := hselectedWF
    groups_closed := hgroups
    layout_built := hbuild
    words_nonzero := by rw [hwordEq]; exact hwords
    reserved_eq := by simp only; rw [hwordEq]
    reserved_lt := hreserved
    layout_check := hcheck
    temps_fresh := hfresh
    pressure_clean := hpressure
    block_eq := rfl
  }

end YulEvmCompiler.Optimizer.MemorySpillSelect
