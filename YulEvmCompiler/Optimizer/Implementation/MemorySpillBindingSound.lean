import YulEvmCompiler.Optimizer.Implementation.MemorySpillRewriteSound
set_option warningAsError true
/-!
# Binding cases for memory spilling

This module isolates the tuple-binding facts needed by the statement
simulation: closure of coupled spill groups, freshness of generated tuple
temporaries, and exact environment transport for the all-unselected path.
-/

namespace YulEvmCompiler.Optimizer.MemorySpillBindingSound

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer
open MemorySpill
open MemorySpillSelect
open MemorySpillStateSound
open MemorySpillRewriteSound

variable {base reserved : Nat}
variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "G" => guardedEvm calls creates base reserved
local notation "D" => evmWithExternal calls creates

theorem coupledGroup_dichotomy {raw : Block Op} {result : Result}
    {guards : List Nat} (hfacts : SpillFacts raw result guards)
    {owner : Owner} {names : List Ident}
    (hgroup : names.map (fun name => ({ owner, name } : SpillKey)) ∈
      coupledStmts none
        (resolveMemoryGuardStmts result.base result.reserved raw)) :
    names.Nodup ∧
      ((∀ name ∈ names, { owner, name } ∈ result.selection) ∨
       (∀ name ∈ names, { owner, name } ∉ result.selection)) := by
  have hclosed := groupsClosedCheck_group_dichotomy hfacts.groups_closed hgroup
  constructor
  · exact List.Nodup.of_map _ hclosed.1
  · rcases hclosed.2 with hall | hall
    · left
      intro name hmem
      exact hall { owner, name } (by simp [hmem])
    · right
      intro name hmem
      exact hall { owner, name } (by simp [hmem])

private theorem tempPrefix_prefix_tempName (owner : Owner) (name : Ident) :
    tempPrefix.toList <+: (tempName owner name).toList := by
  simp [tempName, tempPrefix]

theorem tempName_fresh {raw : Block Op} {result : Result} {guards : List Nat}
    (hfacts : SpillFacts raw result guards) {owner : Owner} {name : Ident}
    {declared : Ident}
    (hdeclared : declared ∈ declaredStmts
      (resolveMemoryGuardStmts result.base result.reserved raw)) :
    tempName owner name ≠ declared := by
  intro heq
  subst declared
  exact hfacts.temps_fresh (tempName owner name) hdeclared
    (tempPrefix_prefix_tempName owner name)

theorem tempNames_fresh {raw : Block Op} {result : Result} {guards : List Nat}
    (hfacts : SpillFacts raw result guards) {owner : Owner} {names : List Ident} :
    ∀ temp ∈ names.map (tempName owner),
      temp ∉ declaredStmts
        (resolveMemoryGuardStmts result.base result.reserved raw) := by
  intro temp htemp hdeclared
  obtain ⟨name, hname, rfl⟩ := List.mem_map.mp htemp
  exact tempName_fresh hfacts hdeclared rfl

theorem tempName_injective (owner : Owner) :
    Function.Injective (tempName owner) := by
  intro left right heq
  unfold tempName at heq
  exact (String.append_right_inj _).mp heq

theorem tempNames_nodup {owner : Owner} {names : List Ident}
    (hnodup : names.Nodup) : (names.map (tempName owner)).Nodup :=
  hnodup.map (tempName_injective owner)

private theorem targetSlots_length {slots : SlotMap} {owner : Owner} :
    ∀ {names : List Ident} {targets : List Nat},
      targetSlots? slots owner names = some targets →
        targets.length = names.length
  | [], targets, h => by simp [targetSlots?] at h; subst targets; rfl
  | name :: names, targets, h => by
      cases hslot : slotFor? slots owner name with
      | none => simp [targetSlots?, hslot] at h
      | some slot =>
          cases hrest : targetSlots? slots owner names with
          | none => simp [targetSlots?, hslot, hrest] at h
          | some rest =>
              simp [targetSlots?, hslot, hrest] at h
              subst targets
              simp [targetSlots_length hrest]

private theorem targetSlots_mem {slots : SlotMap} {owner : Owner} :
    ∀ {names : List Ident} {targets : List Nat},
      targetSlots? slots owner names = some targets →
      ∀ {slot}, slot ∈ targets →
        ∃ name ∈ names, slotFor? slots owner name = some slot
  | [], targets, h, slot, hmem => by
      simp [targetSlots?] at h
      subst targets
      simp at hmem
  | name :: names, targets, h, slot, hmem => by
      cases hslot : slotFor? slots owner name with
      | none => simp [targetSlots?, hslot] at h
      | some head =>
          cases hrest : targetSlots? slots owner names with
          | none => simp [targetSlots?, hslot, hrest] at h
          | some rest =>
              simp [targetSlots?, hslot, hrest] at h
              subst targets
              simp only [List.mem_cons] at hmem
              rcases hmem with rfl | hmem
              · exact ⟨name, by simp, hslot⟩
              · obtain ⟨other, hother, hotherSlot⟩ :=
                  targetSlots_mem hrest hmem
                exact ⟨other, by simp [hother], hotherSlot⟩

theorem selectedTuple_targets {raw : Block Op} {result : Result}
    {guards : List Nat} (hfacts : SpillFacts raw result guards)
    {owner : Owner} {names : List Ident}
    (hall : ∀ name ∈ names, { owner, name } ∈ result.selection) :
    ∃ targets,
      targetSlots? result.layout.slots owner names = some targets ∧
      targets.length = names.length := by
  obtain ⟨targets, htargets⟩ := targetSlots_some_of_all_selected
    hfacts.layout_check owner names hall
  exact ⟨targets, htargets, targetSlots_length htargets⟩

theorem unselectedTuple_noTargets {raw : Block Op} {result : Result}
    {guards : List Nat} (hfacts : SpillFacts raw result guards)
    {owner : Owner} {name : Ident} {rest : List Ident}
    (hall : ∀ item ∈ name :: rest,
      { owner, name := item } ∉ result.selection) :
    targetSlots? result.layout.slots owner (name :: rest) = none :=
  targetSlots_none_of_all_unselected hfacts.layout_check owner rest hall

private theorem mem_map_fst_zip_left {name : Ident} {names : List Ident}
    {values : List U256} (hmem : name ∈ (names.zip values).map Prod.fst) :
    name ∈ names := by
  induction names generalizing values with
  | nil => simp at hmem
  | cons head rest ih =>
      cases values with
      | nil => simp at hmem
      | cons value values =>
          simp only [List.zip_cons_cons, List.map_cons, List.mem_cons] at hmem ⊢
          exact hmem.elim Or.inl (fun h => Or.inr (ih h))

/-- All tuple bindings are certified in one allocator live set, so distinct
tuple names have disjoint spill words. -/
theorem selectedTuple_slots_disjoint {selected : SpillSet} {raw : Block Op}
    {layout : MemorySpillSelect.Layout} {frame : Frame} {live : SpillSet}
    (hbuild : buildLayout base selected raw = some layout)
    (hcheck : layoutCheck base reserved selected layout = true)
    (hframe : frame ∈ frames raw)
    (hcertified : LiveCertified selected frame live)
    {names : List Ident}
    (hlive : ∀ name ∈ names, { owner := frame.owner, name } ∈ live) :
    ∀ {left right : Ident}, left ∈ names → right ∈ names → left ≠ right →
      ∀ {leftSlot rightSlot : Nat},
        slotFor? layout.slots frame.owner left = some leftSlot →
        slotFor? layout.slots frame.owner right = some rightSlot →
        leftSlot + 32 ≤ rightSlot ∨ rightSlot + 32 ≤ leftSlot := by
  obtain ⟨maxLive, hmax, hsubset⟩ := hcertified.covered
  intro left right hleft hright hne leftSlot rightSlot hleftSlot hrightSlot
  have hleftMax := hsubset _ (hlive left hleft)
  have hrightMax := hsubset _ (hlive right hright)
  have hkeysNe : ({ owner := frame.owner, name := left } : SpillKey) ≠
      { owner := frame.owner, name := right } := by
    intro heq
    exact hne (congrArg SpillKey.name heq)
  have hslotsNe : leftSlot ≠ rightSlot :=
    buildLayout_live_slots_ne hbuild hcheck hframe hmax hleftMax hrightMax
      hkeysNe hleftSlot hrightSlot
  exact layoutCheck_distinct_slots_disjoint hcheck
    (slotFor_mem_of_eq_some hleftSlot) (slotFor_mem_of_eq_some hrightSlot)
    hslotsNe

/-! ## Target execution of the selected temporary/distribution path -/

def storeTupleValues : EvmState → List Nat → List U256 → EvmState
  | state, slot :: slots, value :: values =>
      storeTupleValues (MemorySpillStateSound.slotState state slot value)
        slots values
  | state, _, _ => state

private theorem envGet_zip_append {target : WordEnv}
    {temps : List Ident} {values : List U256}
    (hnodup : temps.Nodup) {temp : Ident} {value : U256}
    (hmem : (temp, value) ∈ temps.zip values) :
    envGet (temps.zip values ++ target) temp = some value := by
  induction temps generalizing values with
  | nil => simp at hmem
  | cons head rest ih =>
      cases values with
      | nil => simp at hmem
      | cons first values =>
          simp only [List.zip_cons_cons, List.mem_cons] at hmem
          rcases hmem with hhead | htail
          · cases hhead
            simp [envGet_cons]
          · have htempRest : temp ∈ rest :=
              mem_map_fst_zip_left (List.mem_map.mpr ⟨(temp, value), htail, rfl⟩)
            have hne : head ≠ temp := fun heq =>
              (List.nodup_cons.mp hnodup).1 (heq ▸ htempRest)
            simp only [List.zip_cons_cons, List.cons_append, envGet_cons,
              if_neg hne]
            exact ih (List.nodup_cons.mp hnodup).2 htail

theorem execDistributeTemps {funs : FunEnv D} {vars : WordEnv}
    {state : EvmState} {targets : List Nat} {temps : List Ident}
    {values : List U256}
    (htargets : targets.length = temps.length)
    (hvalues : values.length = temps.length)
    (hnodup : temps.Nodup)
    (hlookup : ∀ {temp : Ident} {value : U256},
      (temp, value) ∈ temps.zip values → envGet vars temp = some value)
    (hbounds : ∀ slot ∈ targets, slot < 2 ^ 256) :
    ExecStmts D funs vars state
      (distributeTemps targets temps) vars
      (storeTupleValues state targets values) .normal := by
  induction targets generalizing temps values state with
  | nil =>
      have htemps : temps = [] := by simpa using htargets.symm
      subst temps
      have hvals : values = [] := by simpa using hvalues
      subst values
      simpa [distributeTemps, storeTupleValues] using
        (Step.seqNil : ExecStmts D funs vars state [] vars state .normal)
  | cons slot slots ih =>
      cases temps with
      | nil => simp at htargets
      | cons temp temps =>
          cases values with
          | nil => simp at hvalues
          | cons value values =>
              have hlens : slots.length = temps.length := by simpa using htargets
              have hlenv : values.length = temps.length := by simpa using hvalues
              have hslot : slot < 2 ^ 256 := hbounds slot (by simp)
              have hrestBounds : ∀ restSlot ∈ slots, restSlot < 2 ^ 256 := by
                intro restSlot hmem
                exact hbounds restSlot (by simp [hmem])
              have hget : envGet vars temp = some value := hlookup (by simp)
              have heval : EvalExpr D funs vars state
                  (.var temp) (.vals [value] state) := Step.var hget
              have hstore := execStoreSlot hslot heval
              have htailLookup : ∀ {restTemp : Ident} {restValue : U256},
                  (restTemp, restValue) ∈ temps.zip values →
                    envGet vars restTemp = some restValue := by
                intro restTemp restValue hmem
                exact hlookup (by simp [hmem])
              have htail := ih hlens hlenv (List.nodup_cons.mp hnodup).2
                htailLookup hrestBounds
                (state := MemorySpillStateSound.slotState state slot value)
              simpa [distributeTemps, storeTupleValues] using
                Step.seqCons hstore htail

theorem execDistributeTemps_zip {funs : FunEnv D} {target : WordEnv}
    {state : EvmState} {targets : List Nat} {temps : List Ident}
    {values : List U256}
    (htargets : targets.length = temps.length)
    (hvalues : values.length = temps.length)
    (hnodup : temps.Nodup)
    (hbounds : ∀ slot ∈ targets, slot < 2 ^ 256) :
    ExecStmts D funs (temps.zip values ++ target) state
      (distributeTemps targets temps) (temps.zip values ++ target)
      (storeTupleValues state targets values) .normal := by
  apply execDistributeTemps htargets hvalues hnodup
  · intro temp value hmem
    exact envGet_zip_append hnodup hmem
  · exact hbounds

private theorem restore_zip_append {target : WordEnv}
    {names : List Ident} {values : List U256}
    (hlength : values.length = names.length) :
    @restore D target (names.zip values ++ target) = target := by
  simp [restore, List.length_zip, hlength]

private theorem hoist_tempDistribution (names : List Ident)
    (expression : Expr Op) (targets : List Nat) :
    hoist D (.letDecl names (some expression) ::
      distributeTemps targets names) = [] := by
  induction targets generalizing names with
  | nil => simp [hoist, distributeTemps]
  | cons target targets ih =>
      cases names with
      | nil => simp [hoist, distributeTemps]
      | cons name names =>
          simp [hoist, distributeTemps, MemorySpill.store]

/-- Execute the generated selected-tuple block without changing the outer
target environment.  The values first exist only under fresh temporary names;
the block then copies them left-to-right into the selected spill words and
restores the temporary prefix on exit. -/
theorem execSelectedTempBlock {funs : FunEnv D} {target : WordEnv}
    {targetInitial targetState : EvmState} {targets : List Nat}
    {temps : List Ident} {values : List U256} {expression : Expr Op}
    (heval : EvalExpr D ([] :: funs) target targetInitial expression
      (.vals values targetState))
    (htargets : targets.length = temps.length)
    (hvalues : values.length = temps.length)
    (hnodup : temps.Nodup)
    (hbounds : ∀ slot ∈ targets, slot < 2 ^ 256) :
    ExecStmts D funs target targetInitial
      [.block (.letDecl temps (some expression) ::
        distributeTemps targets temps)]
      target (storeTupleValues targetState targets values) .normal := by
  have hlet : ExecStmt D ([] :: funs) target targetInitial
      (.letDecl temps (some expression)) (temps.zip values ++ target)
      targetState .normal := Step.letVal heval hvalues
  have hstores := execDistributeTemps_zip (funs := [] :: funs)
    (target := target) (state := targetState) htargets hvalues hnodup hbounds
  have hbody : ExecStmts D ([] :: funs) target targetInitial
      (.letDecl temps (some expression) :: distributeTemps targets temps)
      (temps.zip values ++ target)
      (storeTupleValues targetState targets values) .normal :=
    Step.seqCons hlet hstores
  have hhoist := hoist_tempDistribution (calls := calls) (creates := creates)
    temps expression targets
  have hbody' : ExecStmts D
      (hoist D (.letDecl temps (some expression) ::
        distributeTemps targets temps) :: funs)
      target targetInitial
      (.letDecl temps (some expression) :: distributeTemps targets temps)
      (temps.zip values ++ target)
      (storeTupleValues targetState targets values) .normal := by
    rw [hhoist]
    exact hbody
  have hblock : ExecStmt D funs target targetInitial
      (.block (.letDecl temps (some expression) ::
        distributeTemps targets temps))
      target (storeTupleValues targetState targets values) .normal := by
    have hstep := Step.block hbody'
    simpa only [restore_zip_append hvalues] using hstep
  exact Step.seqCons hblock Step.seqNil

theorem execSelectedTempBlockHalt {funs : FunEnv D} {target : WordEnv}
    {targetInitial targetState : EvmState} {targets : List Nat}
    {temps : List Ident} {expression : Expr Op}
    (heval : EvalExpr D ([] :: funs) target targetInitial expression
      (.halt targetState)) :
    ExecStmts D funs target targetInitial
      [.block (.letDecl temps (some expression) ::
        distributeTemps targets temps)] target targetState .halt := by
  have hlet : ExecStmt D ([] :: funs) target targetInitial
      (.letDecl temps (some expression)) target targetState .halt :=
    Step.letHalt heval
  have hbody : ExecStmts D ([] :: funs) target targetInitial
      (.letDecl temps (some expression) :: distributeTemps targets temps)
      target targetState .halt := Step.seqStop hlet (by decide)
  have hhoist := hoist_tempDistribution (calls := calls) (creates := creates)
    temps expression targets
  have hbody' : ExecStmts D
      (hoist D (.letDecl temps (some expression) ::
        distributeTemps targets temps) :: funs)
      target targetInitial
      (.letDecl temps (some expression) :: distributeTemps targets temps)
      target targetState .halt := by
    rw [hhoist]
    exact hbody
  have hblock := Step.block hbody'
  have hblock' : ExecStmt D funs target targetInitial
      (.block (.letDecl temps (some expression) ::
        distributeTemps targets temps)) target targetState .halt := by
    simpa [restore] using hblock
  exact Step.seqStop hblock' (by decide)

/-! The relational fold for selected assignment targets deliberately keeps the
target environment fixed until every store has completed.  This matches the
temporary-block rewrite and makes source `setMany` order explicit. -/

theorem selectedSetMany_storeTuple {selected : SpillSet} {raw : Block Op}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {source target : WordEnv} {sourceState targetState : EvmState}
    (hbuild : buildLayout base selected raw = some layout)
    (hcheck : layoutCheck base reserved selected layout = true)
    (hframe : frame ∈ frames raw)
    (hrel : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (names : List Ident) (values : List U256) (targets : List Nat)
    (htargets : targetSlots? layout.slots frame.owner names = some targets)
    (hvalues : values.length = names.length)
    (hlive : ∀ name ∈ names, { owner := frame.owner, name } ∈ live)
    {cutoff : Nat}
    (hslotCutoff : ∀ name ∈ names, ∀ slot,
      slotFor? layout.slots frame.owner name = some slot → slot + 32 ≤ cutoff) :
    LiveFrameRel (base := base) (reserved := reserved)
        selected layout frame signature cuts live
        (@VEnv.setMany G source names values) sourceState target
        (storeTupleValues targetState targets values) ∧
      AboveUnchanged cutoff reserved targetState
        (storeTupleValues targetState targets values) := by
  induction names generalizing source targetState targets values with
  | nil =>
      simp [targetSlots?] at htargets
      subst targets
      have hvals : values = [] := by simpa using hvalues
      subst values
      exact ⟨by simpa [VEnv.setMany, storeTupleValues] using hrel,
        AboveUnchanged.refl cutoff reserved targetState⟩
  | cons name names ih =>
      cases hslot : slotFor? layout.slots frame.owner name with
      | none => simp [targetSlots?, hslot] at htargets
      | some slot =>
          cases hrestTargets : targetSlots? layout.slots frame.owner names with
          | none => simp [targetSlots?, hslot, hrestTargets] at htargets
          | some restTargets =>
              simp [targetSlots?, hslot, hrestTargets] at htargets
              subst targets
              cases values with
              | nil => simp at hvalues
              | cons value values =>
                  have hrestValues : values.length = names.length := by
                    simpa using hvalues
                  obtain ⟨maxLive, hmax, hsubset⟩ := hrel.certified.covered
                  have hnameLive := hlive name (by simp)
                  have hfresh : SlotFreshForEnv layout.slots frame.owner
                      source name slot :=
                    slotFreshForEnv_of_live hbuild hcheck hframe hmax hsubset
                      hrel.bound (hsubset _ hnameLive) hslot
                  have hslotBounds := layoutCheck_slotFor_bounds hcheck hslot
                  let nextState := MemorySpillStateSound.slotState
                    targetState slot value
                  have hnext : LiveFrameRel (base := base) (reserved := reserved)
                      selected layout frame signature cuts live
                      (envSet source name value) sourceState target nextState := {
                    frameRel := {
                      env := hrel.frameRel.env.setSelected hslot value
                      loaded := hrel.frameRel.loaded.setSelected_store
                        hslot value hfresh
                      scratch := hrel.frameRel.scratch.trans
                        (slotState_scratch_rel hslotBounds targetState) }
                    bound := hrel.bound.set name value
                    certified := hrel.certified }
                  have hrestLive : ∀ other ∈ names,
                      { owner := frame.owner, name := other } ∈ live := by
                    intro other hmem
                    exact hlive other (by simp [hmem])
                  have hrestCutoff : ∀ other ∈ names, ∀ otherSlot,
                      slotFor? layout.slots frame.owner other = some otherSlot →
                        otherSlot + 32 ≤ cutoff := by
                    intro other hmem
                    exact hslotCutoff other (by simp [hmem])
                  obtain ⟨hfinal, haboveRest⟩ := ih hnext values restTargets
                    hrestTargets hrestValues hrestLive hrestCutoff
                  have haboveHead := AboveUnchanged.slotState
                    (cutoff := cutoff) (reserved := reserved) (value := value)
                    (hslotCutoff name (by simp) slot hslot)
                    targetState
                  rw [envSet_eq (base := base) (reserved := reserved)
                    source name value] at hfinal
                  exact ⟨by
                      simpa [VEnv.setMany, storeTupleValues, nextState] using hfinal,
                    by
                      simpa [storeTupleValues, nextState] using
                        haboveHead.trans haboveRest⟩

/-- The complete selected multi-assignment path: evaluate once inside the
generated block, bind the tuple to fresh temporaries, distribute it to spill
words in source order, restore the temporary environment, and only then relate
the source `setMany` update to the final target memory. -/
theorem execSelectedMultiAssign {selected : SpillSet} {raw : Block Op}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {source target : WordEnv} {sourceState targetInitial targetState : EvmState}
    {sourceFuns : FunEnv G} {names : List Ident} {values : List U256}
    {targets : List Nat} {expression : Expr Op}
    (hbuild : buildLayout base selected raw = some layout)
    (hcheck : layoutCheck base reserved selected layout = true)
    (hreserved : reserved < 2 ^ 256)
    (hframe : frame ∈ frames raw)
    (hrel : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (heval : EvalExpr D ([] :: spillFuns layout.slots sourceFuns)
      target targetInitial expression (.vals values targetState))
    (htargets : targetSlots? layout.slots frame.owner names = some targets)
    (hvalues : values.length = names.length)
    (hnodup : names.Nodup)
    (hlive : ∀ name ∈ names, { owner := frame.owner, name } ∈ live)
    {cutoff : Nat}
    (haboveExpr : AboveUnchanged cutoff reserved targetInitial targetState)
    (hslotCutoff : ∀ name ∈ names, ∀ slot,
      slotFor? layout.slots frame.owner name = some slot → slot + 32 ≤ cutoff) :
    ExecStmts D (spillFuns layout.slots sourceFuns) target targetInitial
        [.block (.letDecl (names.map (tempName frame.owner))
          (some expression) ::
          distributeTemps targets (names.map (tempName frame.owner)))]
        target (storeTupleValues targetState targets values) .normal ∧
      LiveFrameRel (base := base) (reserved := reserved)
        selected layout frame signature cuts live
        (@VEnv.setMany G source names values) sourceState target
        (storeTupleValues targetState targets values) ∧
      AboveUnchanged cutoff reserved targetInitial
        (storeTupleValues targetState targets values) := by
  have htargetLength : targets.length = names.length :=
    targetSlots_length htargets
  have htempLength : (names.map (tempName frame.owner)).length = names.length := by
    simp
  have htargetsTemps : targets.length =
      (names.map (tempName frame.owner)).length := by omega
  have hvaluesTemps : values.length =
      (names.map (tempName frame.owner)).length := by omega
  have hbounds : ∀ slot ∈ targets, slot < 2 ^ 256 := by
    intro slot hmem
    obtain ⟨name, hname, hslot⟩ := targetSlots_mem htargets hmem
    have hend := (layoutCheck_slotFor_bounds hcheck hslot).2
    omega
  have hexec := execSelectedTempBlock
    (funs := spillFuns layout.slots sourceFuns)
    heval htargetsTemps hvaluesTemps (tempNames_nodup hnodup) hbounds
  obtain ⟨hfinal, haboveStores⟩ := selectedSetMany_storeTuple
    hbuild hcheck hframe hrel names values targets htargets hvalues hlive
      hslotCutoff
  exact ⟨hexec, hfinal, haboveExpr.trans haboveStores⟩

private theorem loadWord_storeTupleValues_other {state : EvmState}
    {targets : List Nat} {values : List U256} {protectedSlot : Nat}
    (hdisjoint : ∀ slot ∈ targets,
      slot + 32 ≤ protectedSlot ∨ protectedSlot + 32 ≤ slot) :
    loadWord (storeTupleValues state targets values).memory protectedSlot =
      loadWord state.memory protectedSlot := by
  induction targets generalizing state values with
  | nil => simp [storeTupleValues]
  | cons slot slots ih =>
      cases values with
      | nil => simp [storeTupleValues]
      | cons value values =>
          have htail := ih
            (state := MemorySpillStateSound.slotState state slot value)
            (values := values) (by
              intro other hmem
              exact hdisjoint other (by simp [hmem]))
          rw [storeTupleValues, htail]
          simpa [MemorySpillStateSound.slotState] using
            loadWord_storeWord_other state.memory slot protectedSlot value
              (hdisjoint slot (by simp))

/-- Loading invariants for a selected declaration are established only after
all generated stores have run.  This theorem is deliberately independent of
the temporary target environment used while executing the block. -/
theorem SlotsLoaded.prependSelectedTuple {slots : SlotMap} {owner : Owner}
    {source : WordEnv} {state : EvmState}
    (hloaded : SlotsLoaded slots owner source state)
    (names : List Ident) (values : List U256) (targets : List Nat)
    (htargets : targetSlots? slots owner names = some targets)
    (hvalues : values.length = names.length)
    (hnodup : names.Nodup)
    (hfreshNames : ∀ name ∈ names, name ∉ source.map Prod.fst)
    (hfreshSlots : ∀ name ∈ names, ∀ slot,
      slotFor? slots owner name = some slot →
        SlotFreshForEnv slots owner source name slot)
    (hpairwise : ∀ {left right : Ident}, left ∈ names → right ∈ names →
      left ≠ right → ∀ {leftSlot rightSlot : Nat},
      slotFor? slots owner left = some leftSlot →
      slotFor? slots owner right = some rightSlot →
        leftSlot + 32 ≤ rightSlot ∨ rightSlot + 32 ≤ leftSlot) :
    SlotsLoaded slots owner (names.zip values ++ source)
      (storeTupleValues state targets values) := by
  induction names generalizing state targets values with
  | nil =>
      simp [targetSlots?] at htargets
      subst targets
      have hvals : values = [] := by simpa using hvalues
      subst values
      simpa [storeTupleValues] using hloaded
  | cons name names ih =>
      cases hslot : slotFor? slots owner name with
      | none => simp [targetSlots?, hslot] at htargets
      | some slot =>
          cases hrestTargets : targetSlots? slots owner names with
          | none => simp [targetSlots?, hslot, hrestTargets] at htargets
          | some restTargets =>
              simp [targetSlots?, hslot, hrestTargets] at htargets
              subst targets
              cases values with
              | nil => simp at hvalues
              | cons value values =>
                  have hrestValues : values.length = names.length := by
                    simpa using hvalues
                  have hnameFresh := hfreshNames name (by simp)
                  have hfresh := hfreshSlots name (by simp) slot hslot
                  let nextState := MemorySpillStateSound.slotState state slot value
                  have hloadedNext : SlotsLoaded slots owner source nextState := by
                    intro other otherSlot otherValue hotherSlot hget
                    have hne : other ≠ name := by
                      intro heq
                      subst other
                      exact hnameFresh (envGet_name_mem hget)
                    exact SlotsLoaded.slotState_other hloaded hfresh other
                      otherSlot otherValue hne hotherSlot hget
                  have htailFreshNames : ∀ other ∈ names,
                      other ∉ source.map Prod.fst := by
                    intro other hmem
                    exact hfreshNames other (by simp [hmem])
                  have htailFreshSlots : ∀ other ∈ names, ∀ otherSlot,
                      slotFor? slots owner other = some otherSlot →
                        SlotFreshForEnv slots owner source other otherSlot := by
                    intro other hmem
                    exact hfreshSlots other (by simp [hmem])
                  have htailPairwise : ∀ {left right : Ident},
                      left ∈ names → right ∈ names → left ≠ right →
                      ∀ {leftSlot rightSlot : Nat},
                      slotFor? slots owner left = some leftSlot →
                      slotFor? slots owner right = some rightSlot →
                        leftSlot + 32 ≤ rightSlot ∨
                          rightSlot + 32 ≤ leftSlot := by
                    intro left right hleft hright hne leftSlot rightSlot
                    exact hpairwise (by simp [hleft]) (by simp [hright]) hne
                  have htailLoaded := ih hloadedNext values restTargets
                    hrestTargets hrestValues (List.nodup_cons.mp hnodup).2
                    htailFreshNames htailFreshSlots htailPairwise
                  have hheadDisjoint : ∀ otherSlot ∈ restTargets,
                      otherSlot + 32 ≤ slot ∨ slot + 32 ≤ otherSlot := by
                    intro otherSlot hmem
                    obtain ⟨other, hother, hotherSlot⟩ :=
                      targetSlots_mem hrestTargets hmem
                    have hne : name ≠ other := fun heq =>
                      (List.nodup_cons.mp hnodup).1 (heq ▸ hother)
                    exact (hpairwise (by simp) (by simp [hother]) hne hslot
                      hotherSlot).symm
                  have hheadLoaded : loadWord
                      (storeTupleValues nextState restTargets values).memory slot =
                      value := by
                    rw [loadWord_storeTupleValues_other hheadDisjoint]
                    exact slotState_load state slot value
                  intro other otherSlot found hotherSlot hget
                  simp only [List.zip_cons_cons, List.cons_append] at hget ⊢
                  rw [envGet_cons] at hget
                  by_cases heq : name = other
                  · subst other
                    have hfound : found = value := by simpa using hget.symm
                    subst found
                    rw [hslot] at hotherSlot
                    cases hotherSlot
                    simpa [storeTupleValues, nextState] using hheadLoaded
                  · simp only [if_neg heq] at hget
                    simpa [storeTupleValues, nextState] using
                      htailLoaded other otherSlot found hotherSlot hget

theorem VRel.prependSelectedTuple {slots : SlotMap} {owner : Owner}
    {signature : List Ident} {source target : WordEnv}
    (hrel : VRel slots owner signature source target)
    (names : List Ident) (values : List U256) (targets : List Nat)
    (htargets : targetSlots? slots owner names = some targets)
    (hvalues : values.length = names.length)
    (hnotSignature : ∀ name ∈ names, name ∉ signature) :
    VRel slots owner signature (names.zip values ++ source) target := by
  induction names generalizing targets values with
  | nil => simpa using hrel
  | cons name names ih =>
      cases hslot : slotFor? slots owner name with
      | none => simp [targetSlots?, hslot] at htargets
      | some slot =>
          cases hrest : targetSlots? slots owner names with
          | none => simp [targetSlots?, hslot, hrest] at htargets
          | some rest =>
              simp [targetSlots?, hslot, hrest] at htargets
              subst targets
              cases values with
              | nil => simp at hvalues
              | cons value values =>
                  have hlen : values.length = names.length := by
                    simpa using hvalues
                  have htail := ih values rest hrest hlen (by
                    intro other hmem
                    exact hnotSignature other (by simp [hmem]))
                  simpa using VRel.selectedLocal hslot
                    (hnotSignature name (by simp)) htail

private theorem scratchRel_storeTupleValues {state : EvmState}
    {targets : List Nat} {values : List U256}
    (hbounds : ∀ slot ∈ targets, base ≤ slot ∧ slot + 32 ≤ reserved) :
    ScratchRel base reserved state (storeTupleValues state targets values) := by
  induction targets generalizing state values with
  | nil => simpa [storeTupleValues] using ScratchRel.refl base reserved state
  | cons slot slots ih =>
      cases values with
      | nil => simpa [storeTupleValues] using ScratchRel.refl base reserved state
      | cons value values =>
          have hhead := slotState_scratch_rel (value := value)
            (hbounds slot (by simp)) state
          have htail := ih
            (state := MemorySpillStateSound.slotState state slot value)
            (values := values) (by
              intro other hmem
              exact hbounds other (by simp [hmem]))
          exact hhead.trans (by simpa [storeTupleValues] using htail)

private theorem aboveUnchanged_storeTupleValues {state : EvmState}
    {targets : List Nat} {values : List U256} {cutoff : Nat}
    (hends : ∀ slot ∈ targets, slot + 32 ≤ cutoff) :
    AboveUnchanged cutoff reserved state
      (storeTupleValues state targets values) := by
  induction targets generalizing state values with
  | nil => simpa [storeTupleValues] using
      AboveUnchanged.refl cutoff reserved state
  | cons slot slots ih =>
      cases values with
      | nil => simpa [storeTupleValues] using
          AboveUnchanged.refl cutoff reserved state
      | cons value values =>
          have hhead := AboveUnchanged.slotState
            (reserved := reserved) (value := value)
            (hends slot (by simp)) state
          have htail := ih
            (state := MemorySpillStateSound.slotState state slot value)
            (values := values) (by
              intro other hmem
              exact hends other (by simp [hmem]))
          exact hhead.trans (by simpa [storeTupleValues] using htail)

/-- Final relation for a selected tuple declaration.  Target execution has
already restored its temporary environment; all newly declared source names
are represented solely by their final memory words. -/
theorem selectedPrepend_storeTuple {selected : SpillSet} {raw : Block Op}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live nextLive : SpillSet}
    {source target : WordEnv} {sourceState targetState : EvmState}
    (hbuild : buildLayout base selected raw = some layout)
    (hcheck : layoutCheck base reserved selected layout = true)
    (hframe : frame ∈ frames raw)
    (hrel : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (names : List Ident) (values : List U256) (targets : List Nat)
    (htargets : targetSlots? layout.slots frame.owner names = some targets)
    (hvalues : values.length = names.length)
    (hnodup : names.Nodup)
    (hfreshNames : ∀ name ∈ names, name ∉ source.map Prod.fst)
    (hnotSignature : ∀ name ∈ names, name ∉ signature)
    (holdLive : ∀ key ∈ live, key ∈ nextLive)
    (hnamesLive : ∀ name ∈ names,
      { owner := frame.owner, name } ∈ nextLive)
    (hnextCertified : LiveCertified selected frame nextLive) :
    LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts nextLive
      (names.zip values ++ source) sourceState target
      (storeTupleValues targetState targets values) := by
  obtain ⟨maxLive, hmax, hsubset⟩ := hnextCertified.covered
  have hfreshSlots : ∀ name ∈ names, ∀ slot,
      slotFor? layout.slots frame.owner name = some slot →
        SlotFreshForEnv layout.slots frame.owner source name slot := by
    intro name hname slot hslot
    exact slotFreshForEnv_of_live hbuild hcheck hframe hmax
      (fun key hkey => hsubset key (holdLive key hkey)) hrel.bound
      (hsubset _ (hnamesLive name hname)) hslot
  have hpairwise : ∀ {left right : Ident},
      left ∈ names → right ∈ names → left ≠ right →
      ∀ {leftSlot rightSlot : Nat},
      slotFor? layout.slots frame.owner left = some leftSlot →
      slotFor? layout.slots frame.owner right = some rightSlot →
        leftSlot + 32 ≤ rightSlot ∨ rightSlot + 32 ≤ leftSlot := by
    intro left right hleft hright hne leftSlot rightSlot hleftSlot hrightSlot
    exact selectedTuple_slots_disjoint hbuild hcheck hframe
      hnextCertified hnamesLive hleft hright hne hleftSlot hrightSlot
  have hvars := VRel.prependSelectedTuple hrel.frameRel.env.vars
    names values targets htargets hvalues hnotSignature
  have henv := EnvRel.prepend (names.zip values) [] hrel.frameRel.env (by
    simpa using hvars)
  have hloaded := SlotsLoaded.prependSelectedTuple hrel.frameRel.loaded
    names values targets htargets hvalues hnodup hfreshNames hfreshSlots hpairwise
  have hbounds : ∀ slot ∈ targets,
      base ≤ slot ∧ slot + 32 ≤ reserved := by
    intro slot hmem
    obtain ⟨name, hname, hslot⟩ := targetSlots_mem htargets hmem
    exact layoutCheck_slotFor_bounds hcheck hslot
  have hscratch := hrel.frameRel.scratch.trans
    (scratchRel_storeTupleValues (values := values) hbounds)
  have hbound : BoundSelectedIn layout.slots frame.owner
      (names.zip values ++ source) nextLive := by
    apply BoundSelectedIn.prepend (front := names.zip values)
      (nextLive := nextLive) hrel.bound
    · intro name hmem slot hslot
      exact hnamesLive name (mem_map_fst_zip_left hmem)
    · exact holdLive
  exact {
    frameRel := { env := henv, loaded := hloaded, scratch := hscratch }
    bound := hbound
    certified := hnextCertified }

theorem execSelectedStoresZero {funs : FunEnv D} {target : WordEnv}
    {state : EvmState} (targets : List Nat)
    (hbounds : ∀ slot ∈ targets, slot < 2 ^ 256) :
    ExecStmts D funs target state
      (targets.map fun slot => MemorySpill.store slot (word 0)) target
      (storeTupleValues state targets (List.replicate targets.length 0))
      .normal := by
  induction targets generalizing state with
  | nil => simpa [storeTupleValues] using
      (Step.seqNil : ExecStmts D funs target state [] target state .normal)
  | cons slot slots ih =>
      have hzero : Dialect.litValue D (.number 0) = (0 : U256) := by
        change litValue (.number 0) = (0 : U256)
        decide
      have heval : EvalExpr D funs target state (word 0) (.vals [0] state) := by
        have hlit := (Step.lit : EvalExpr D funs target state
          (.lit (.number 0)) (.vals [Dialect.litValue D (.number 0)] state))
        rw [hzero] at hlit
        exact hlit
      have hstore := execStoreSlot (hbounds slot (by simp)) heval
      have htail := ih
        (state := MemorySpillStateSound.slotState state slot 0) (by
          intro other hmem
          exact hbounds other (by simp [hmem]))
      simpa [storeTupleValues, List.replicate_succ] using
        Step.seqCons hstore htail

theorem execSelectedMultiLetVal {selected : SpillSet} {raw : Block Op}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live nextLive : SpillSet}
    {source target : WordEnv} {sourceState targetInitial targetState : EvmState}
    {sourceFuns : FunEnv G} {names : List Ident} {values : List U256}
    {targets : List Nat} {expression : Expr Op}
    (hbuild : buildLayout base selected raw = some layout)
    (hcheck : layoutCheck base reserved selected layout = true)
    (hreserved : reserved < 2 ^ 256)
    (hframe : frame ∈ frames raw)
    (hrel : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (heval : EvalExpr D ([] :: spillFuns layout.slots sourceFuns)
      target targetInitial expression (.vals values targetState))
    (htargets : targetSlots? layout.slots frame.owner names = some targets)
    (hvalues : values.length = names.length)
    (hnodup : names.Nodup)
    (hfreshNames : ∀ name ∈ names, name ∉ source.map Prod.fst)
    (hnotSignature : ∀ name ∈ names, name ∉ signature)
    (holdLive : ∀ key ∈ live, key ∈ nextLive)
    (hnamesLive : ∀ name ∈ names,
      { owner := frame.owner, name } ∈ nextLive)
    (hnextCertified : LiveCertified selected frame nextLive)
    {cutoff : Nat}
    (haboveExpr : AboveUnchanged cutoff reserved targetInitial targetState)
    (hslotCutoff : ∀ name ∈ names, ∀ slot,
      slotFor? layout.slots frame.owner name = some slot → slot + 32 ≤ cutoff) :
    ExecStmts D (spillFuns layout.slots sourceFuns) target targetInitial
        [.block (.letDecl (names.map (tempName frame.owner))
          (some expression) ::
          distributeTemps targets (names.map (tempName frame.owner)))]
        target (storeTupleValues targetState targets values) .normal ∧
      LiveFrameRel (base := base) (reserved := reserved)
        selected layout frame signature cuts nextLive
        (names.zip values ++ source) sourceState target
        (storeTupleValues targetState targets values) ∧
      AboveUnchanged cutoff reserved targetInitial
        (storeTupleValues targetState targets values) := by
  have htargetLength := targetSlots_length htargets
  have htargetsTemps : targets.length =
      (names.map (tempName frame.owner)).length := by simpa using htargetLength
  have hvaluesTemps : values.length =
      (names.map (tempName frame.owner)).length := by simpa using hvalues
  have hbounds : ∀ slot ∈ targets, slot < 2 ^ 256 := by
    intro slot hmem
    obtain ⟨name, hname, hslot⟩ := targetSlots_mem htargets hmem
    have hend := (layoutCheck_slotFor_bounds hcheck hslot).2
    omega
  have hexec := execSelectedTempBlock
    (funs := spillFuns layout.slots sourceFuns)
    heval htargetsTemps hvaluesTemps (tempNames_nodup hnodup) hbounds
  have hfinal := selectedPrepend_storeTuple hbuild hcheck hframe hrel
    names values targets htargets hvalues hnodup hfreshNames hnotSignature
    holdLive hnamesLive hnextCertified
  have hends : ∀ slot ∈ targets, slot + 32 ≤ cutoff := by
    intro slot hmem
    obtain ⟨name, hname, hslot⟩ := targetSlots_mem htargets hmem
    exact hslotCutoff name hname slot hslot
  have haboveStores := aboveUnchanged_storeTupleValues
    (reserved := reserved) (state := targetState) (values := values) hends
  exact ⟨hexec, hfinal, haboveExpr.trans haboveStores⟩

theorem execSelectedMultiLetZero {selected : SpillSet} {raw : Block Op}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live nextLive : SpillSet}
    {source target : WordEnv} {sourceState targetState : EvmState}
    {sourceFuns : FunEnv G} {names : List Ident} {targets : List Nat}
    (hbuild : buildLayout base selected raw = some layout)
    (hcheck : layoutCheck base reserved selected layout = true)
    (hreserved : reserved < 2 ^ 256)
    (hframe : frame ∈ frames raw)
    (hrel : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (htargets : targetSlots? layout.slots frame.owner names = some targets)
    (hnodup : names.Nodup)
    (hfreshNames : ∀ name ∈ names, name ∉ source.map Prod.fst)
    (hnotSignature : ∀ name ∈ names, name ∉ signature)
    (holdLive : ∀ key ∈ live, key ∈ nextLive)
    (hnamesLive : ∀ name ∈ names,
      { owner := frame.owner, name } ∈ nextLive)
    (hnextCertified : LiveCertified selected frame nextLive)
    {cutoff : Nat}
    (hslotCutoff : ∀ name ∈ names, ∀ slot,
      slotFor? layout.slots frame.owner name = some slot → slot + 32 ≤ cutoff) :
    let values : List U256 := List.replicate names.length 0
    ExecStmts D (spillFuns layout.slots sourceFuns) target targetState
        (targets.map fun slot => MemorySpill.store slot (word 0))
        target (storeTupleValues targetState targets values) .normal ∧
      LiveFrameRel (base := base) (reserved := reserved)
        selected layout frame signature cuts nextLive
        (names.zip values ++ source) sourceState target
        (storeTupleValues targetState targets values) ∧
      AboveUnchanged cutoff reserved targetState
        (storeTupleValues targetState targets values) := by
  dsimp only
  have htargetLength := targetSlots_length htargets
  have hbounds : ∀ slot ∈ targets, slot < 2 ^ 256 := by
    intro slot hmem
    obtain ⟨name, hname, hslot⟩ := targetSlots_mem htargets hmem
    have hend := (layoutCheck_slotFor_bounds hcheck hslot).2
    omega
  have hexec := execSelectedStoresZero
    (funs := spillFuns layout.slots sourceFuns) (target := target)
    (state := targetState) targets hbounds
  rw [htargetLength] at hexec
  have hvalues : (List.replicate names.length (0 : U256)).length =
      names.length := by simp
  have hfinal := selectedPrepend_storeTuple hbuild hcheck hframe hrel
    names (List.replicate names.length 0) targets htargets hvalues hnodup
    hfreshNames hnotSignature holdLive hnamesLive hnextCertified
  have hends : ∀ slot ∈ targets, slot + 32 ≤ cutoff := by
    intro slot hmem
    obtain ⟨name, hname, hslot⟩ := targetSlots_mem htargets hmem
    exact hslotCutoff name hname slot hslot
  have habove := aboveUnchanged_storeTupleValues
    (reserved := reserved) (state := targetState)
    (values := List.replicate names.length 0) hends
  exact ⟨hexec, hfinal, habove⟩

/-! ## All-unselected environment transport -/

theorem VRel.prependZipNoSlots {slots : SlotMap} {owner : Owner}
    {signature : List Ident} {source target : WordEnv}
    (hrel : VRel slots owner signature source target) :
    ∀ (names : List Ident) (values : List U256),
      (∀ name ∈ names, slotFor? slots owner name = none) →
      VRel slots owner signature
        (names.zip values ++ source) (names.zip values ++ target)
  | [], _, _ => by simpa using hrel
  | _ :: _, [], _ => by simpa using hrel
  | name :: names, value :: values, hall => by
      have hhead := hall name (by simp)
      have htail : ∀ other ∈ names, slotFor? slots owner other = none := by
        intro other hmem
        exact hall other (by simp [hmem])
      exact .unselected hhead (VRel.prependZipNoSlots hrel names values htail)

theorem SlotsLoaded.prependZipNoSlots {slots : SlotMap} {owner : Owner}
    {source : WordEnv} {state : EvmState}
    (hloaded : SlotsLoaded slots owner source state) :
    ∀ (names : List Ident) (values : List U256),
      (∀ name ∈ names, slotFor? slots owner name = none) →
      SlotsLoaded slots owner (names.zip values ++ source) state
  | [], _, _ => by simpa using hloaded
  | _ :: _, [], _ => by simpa using hloaded
  | name :: names, value :: values, hall => by
      have hhead := hall name (by simp)
      have htail : ∀ other ∈ names, slotFor? slots owner other = none := by
        intro other hmem
        exact hall other (by simp [hmem])
      exact SlotsLoaded.prependNoSlot
        (SlotsLoaded.prependZipNoSlots hloaded names values htail) hhead value

theorem EnvRel.setManyNoSlots {slots : SlotMap} {owner : Owner}
    {signature : List Ident} {source target : WordEnv} {cuts : List CutMark}
    (hrel : EnvRel slots owner signature source target cuts) :
    ∀ (names : List Ident) (values : List U256),
      (∀ name ∈ names, slotFor? slots owner name = none) →
      EnvRel slots owner signature
        (@VEnv.setMany G source names values)
        (@VEnv.setMany D target names values) cuts
  | [], _, _ => by simpa [VEnv.setMany] using hrel
  | _ :: _, [], _ => by simpa [VEnv.setMany] using hrel
  | name :: names, value :: values, hall => by
      have hhead := hall name (by simp)
      have htail : ∀ other ∈ names, slotFor? slots owner other = none := by
        intro other hmem
        exact hall other (by simp [hmem])
      have hnext :=
        EnvRel.setManyNoSlots (hrel.setNoSlot hhead value) names values htail
      rw [envSet_eq, envSet_eq_ordinary] at hnext
      simpa only [VEnv.setMany, List.zip_cons_cons, List.foldl_cons] using hnext

theorem SlotsLoaded.setManyNoSlots {slots : SlotMap} {owner : Owner}
    {source : WordEnv} {state : EvmState}
    (hloaded : SlotsLoaded slots owner source state) :
    ∀ (names : List Ident) (values : List U256),
      (∀ name ∈ names, slotFor? slots owner name = none) →
      SlotsLoaded slots owner (@VEnv.setMany G source names values) state
  | [], _, _ => by simpa [VEnv.setMany] using hloaded
  | _ :: _, [], _ => by simpa [VEnv.setMany] using hloaded
  | name :: names, value :: values, hall => by
      have hhead := hall name (by simp)
      have htail : ∀ other ∈ names, slotFor? slots owner other = none := by
        intro other hmem
        exact hall other (by simp [hmem])
      have hnext := SlotsLoaded.setManyNoSlots (hloaded.setNoSlot hhead value)
        names values htail
      rw [envSet_eq] at hnext
      simpa only [VEnv.setMany, List.zip_cons_cons, List.foldl_cons] using hnext

theorem BoundSelectedIn.setMany {slots : SlotMap} {owner : Owner}
    {source : WordEnv} {live : SpillSet}
    (hbound : BoundSelectedIn slots owner source live)
    (names : List Ident) (values : List U256) :
    BoundSelectedIn slots owner (@VEnv.setMany G source names values) live := by
  apply BoundSelectedIn.of_keys_eq hbound
  exact @YulEvmCompiler.Optimizer.VEnv.setMany_keys G inferInstance
    source names values

theorem LiveFrameRel.prependZipNoSlots {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live nextLive : SpillSet}
    {source target : WordEnv} {sourceState targetState : EvmState}
    (hrel : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (names : List Ident) (values : List U256)
    (hall : ∀ name ∈ names,
      slotFor? layout.slots frame.owner name = none)
    (hlive : ∀ key ∈ live, key ∈ nextLive)
    (hcertified : LiveCertified selected frame nextLive) :
    LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts nextLive
      (names.zip values ++ source) sourceState
      (names.zip values ++ target) targetState := by
  have hvars := VRel.prependZipNoSlots hrel.frameRel.env.vars names values hall
  have henv := EnvRel.prepend (names.zip values) (names.zip values)
    hrel.frameRel.env hvars
  have hloaded := SlotsLoaded.prependZipNoSlots hrel.frameRel.loaded
    names values hall
  have hbound : BoundSelectedIn layout.slots frame.owner
      (names.zip values ++ source) nextLive := by
    apply BoundSelectedIn.prepend (front := names.zip values)
      (nextLive := nextLive) hrel.bound
    · intro name hmem slot hslot
      have hname : name ∈ names := mem_map_fst_zip_left hmem
      rw [hall name hname] at hslot
      contradiction
    · exact hlive
  let hframeRel : ScopedFrameRel (base := base) (reserved := reserved)
      layout.slots frame.owner signature cuts
      (names.zip values ++ source) sourceState
      (names.zip values ++ target) targetState := {
    env := henv
    loaded := hloaded
    scratch := hrel.frameRel.scratch }
  exact {
    frameRel := hframeRel
    bound := hbound
    certified := hcertified }

theorem LiveFrameRel.setManyNoSlots {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {source target : WordEnv} {sourceState targetState : EvmState}
    (hrel : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (names : List Ident) (values : List U256)
    (hall : ∀ name ∈ names,
      slotFor? layout.slots frame.owner name = none) :
    LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      (@VEnv.setMany G source names values) sourceState
      (@VEnv.setMany D target names values) targetState := by
  exact {
    frameRel := {
      env := EnvRel.setManyNoSlots hrel.frameRel.env names values hall
      loaded := SlotsLoaded.setManyNoSlots hrel.frameRel.loaded names values hall
      scratch := hrel.frameRel.scratch }
    bound := MemorySpillBindingSound.BoundSelectedIn.setMany
      hrel.bound names values
    certified := hrel.certified }

/-! ## Ordinary all-unselected binding execution -/

private theorem zip_replicate (names : List Ident) (value : U256) :
    names.zip (List.replicate names.length value) =
      names.map fun name => (name, value) := by
  induction names with
  | nil => rfl
  | cons name rest => simp [List.replicate_succ, *]

theorem execUnselectedMultiLetZero {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live nextLive : SpillSet}
    {source target : WordEnv} {sourceState targetState : EvmState}
    {sourceFuns : FunEnv G} {names : List Ident}
    (hrel : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (hall : ∀ name ∈ names,
      slotFor? layout.slots frame.owner name = none)
    (hlive : ∀ key ∈ live, key ∈ nextLive)
    (hcertified : LiveCertified selected frame nextLive) :
    ExecStmts D (spillFuns layout.slots sourceFuns) target targetState
        [.letDecl names none]
        (bindZeros D names ++ target) targetState .normal ∧
      LiveFrameRel (base := base) (reserved := reserved)
        selected layout frame signature cuts nextLive
        (bindZeros G names ++ source) sourceState
        (bindZeros D names ++ target) targetState ∧
      ∀ cutoff, AboveUnchanged cutoff reserved targetState targetState := by
  have hstmt : ExecStmt D (spillFuns layout.slots sourceFuns) target targetState
      (.letDecl names none) (bindZeros D names ++ target) targetState .normal :=
    Step.letZero
  refine ⟨Step.seqCons hstmt Step.seqNil, ?_, fun cutoff =>
    AboveUnchanged.refl cutoff reserved targetState⟩
  have hnext := MemorySpillBindingSound.LiveFrameRel.prependZipNoSlots hrel
    names (List.replicate names.length (Dialect.zero G)) hall hlive hcertified
  have hG : names.zip (List.replicate names.length (Dialect.zero G)) =
      bindZeros G names := by
    simpa [bindZeros] using zip_replicate names (Dialect.zero G)
  rw [hG] at hnext
  have hbind : bindZeros G names = bindZeros D names := rfl
  rw [← hbind]
  exact hnext

theorem execUnselectedMultiLetVal {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live nextLive : SpillSet}
    {source target : WordEnv} {sourceState targetInitial targetState : EvmState}
    {sourceFuns : FunEnv G} {names : List Ident} {values : List U256}
    {expression : Expr Op}
    (hrel : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (heval : EvalExpr D (spillFuns layout.slots sourceFuns) target targetInitial
      expression (.vals values targetState))
    (hlength : values.length = names.length)
    (hall : ∀ name ∈ names,
      slotFor? layout.slots frame.owner name = none)
    (hlive : ∀ key ∈ live, key ∈ nextLive)
    (hcertified : LiveCertified selected frame nextLive)
    {cutoff : Nat} (habove : AboveUnchanged cutoff reserved targetInitial targetState) :
    ExecStmts D (spillFuns layout.slots sourceFuns) target targetInitial
        [.letDecl names (some expression)]
        (names.zip values ++ target) targetState .normal ∧
      LiveFrameRel (base := base) (reserved := reserved)
        selected layout frame signature cuts nextLive
        (names.zip values ++ source) sourceState
        (names.zip values ++ target) targetState ∧
      AboveUnchanged cutoff reserved targetInitial targetState := by
  have hstmt : ExecStmt D (spillFuns layout.slots sourceFuns) target targetInitial
      (.letDecl names (some expression)) (names.zip values ++ target)
      targetState .normal := Step.letVal heval hlength
  exact ⟨Step.seqCons hstmt Step.seqNil,
    MemorySpillBindingSound.LiveFrameRel.prependZipNoSlots hrel
      names values hall hlive hcertified, habove⟩

theorem execUnselectedMultiAssign {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {source target : WordEnv} {sourceState targetInitial targetState : EvmState}
    {sourceFuns : FunEnv G} {names : List Ident} {values : List U256}
    {expression : Expr Op}
    (hrel : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (heval : EvalExpr D (spillFuns layout.slots sourceFuns) target targetInitial
      expression (.vals values targetState))
    (hlength : values.length = names.length)
    (hall : ∀ name ∈ names,
      slotFor? layout.slots frame.owner name = none)
    {cutoff : Nat} (habove : AboveUnchanged cutoff reserved targetInitial targetState) :
    ExecStmts D (spillFuns layout.slots sourceFuns) target targetInitial
        [.assign names expression]
        (@VEnv.setMany D target names values) targetState .normal ∧
      LiveFrameRel (base := base) (reserved := reserved)
        selected layout frame signature cuts live
        (@VEnv.setMany G source names values) sourceState
        (@VEnv.setMany D target names values) targetState ∧
      AboveUnchanged cutoff reserved targetInitial targetState := by
  have hstmt : ExecStmt D (spillFuns layout.slots sourceFuns) target targetInitial
      (.assign names expression) (@VEnv.setMany D target names values)
      targetState .normal := Step.assignVal heval hlength
  exact ⟨Step.seqCons hstmt Step.seqNil,
    MemorySpillBindingSound.LiveFrameRel.setManyNoSlots hrel
      names values hall, habove⟩

theorem execMultiLetHalt {layout : MemorySpillSelect.Layout}
    {sourceFuns : FunEnv G} {target : WordEnv} {targetInitial targetState : EvmState}
    {names : List Ident} {expression : Expr Op}
    (heval : EvalExpr D (spillFuns layout.slots sourceFuns) target targetInitial
      expression (.halt targetState)) :
    ExecStmts D (spillFuns layout.slots sourceFuns) target targetInitial
      [.letDecl names (some expression)] target targetState .halt :=
  Step.seqStop (Step.letHalt heval) (by decide)

theorem execMultiAssignHalt {layout : MemorySpillSelect.Layout}
    {sourceFuns : FunEnv G} {target : WordEnv} {targetInitial targetState : EvmState}
    {names : List Ident} {expression : Expr Op}
    (heval : EvalExpr D (spillFuns layout.slots sourceFuns) target targetInitial
      expression (.halt targetState)) :
    ExecStmts D (spillFuns layout.slots sourceFuns) target targetInitial
      [.assign names expression] target targetState .halt :=
  Step.seqStop (Step.assignHalt heval) (by decide)

end YulEvmCompiler.Optimizer.MemorySpillBindingSound
