import YulEvmCompiler.Optimizer.Implementation.MemorySpillFrameSound
set_option warningAsError true
/-!
# Lexical-exit preservation for memory spilling

Lexical blocks restore the source and target variable environments at
different numeric depths: selected locals are absent from the target stack.
`EnvRel` aligns those two cuts.  This module supplies the remaining generic
facts needed by the control-flow simulation at a block exit:

* names bound in the outer source environment remain bound after source
  `restore`, once the ordinary source key-preservation theorem is available;
* synchronized signature values remain synchronized after the aligned source
  and target restores, provided selected names have no shadowing occurrence.

The latter uniqueness premise is intentionally stated only for names that
have slots.  Unselected names agree directly through the restored `VRel`.
-/

namespace YulEvmCompiler.Optimizer.MemorySpillExitSound

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer
open MemorySpillSelect
open MemorySpillRewriteSound
open MemorySpillFrameSound

variable {base reserved : Nat}
variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "G" => guardedEvm calls creates base reserved
local notation "D" => evmWithExternal calls creates

/-! ## Environment lookup through suffix restoration -/

theorem envGet_exists_of_name_mem {source : WordEnv} {name : Ident}
    (hmem : name ∈ source.map Prod.fst) :
    ∃ value, envGet source name = some value := by
  induction source with
  | nil => simp at hmem
  | cons item rest ih =>
      obtain ⟨head, value⟩ := item
      simp only [List.map_cons, List.mem_cons] at hmem
      rcases hmem with rfl | hrest
      · exact ⟨value, by simp [envGet_cons]⟩
      · obtain ⟨restValue, hget⟩ := ih hrest
        by_cases heq : head = name
        · subst head
          exact ⟨value, by simp [envGet_cons]⟩
        · exact ⟨restValue, by simpa [envGet_cons, heq] using hget⟩

theorem envGet_drop_of_count_le_one {source : WordEnv} {name : Ident}
    (hcount : (source.map Prod.fst).count name ≤ 1) :
    ∀ (drop : Nat) {value : U256},
      envGet (source.drop drop) name = some value →
        envGet source name = some value := by
  induction source with
  | nil => intro drop value hget; simp [envGet] at hget
  | cons item rest ih =>
      intro drop value hget
      cases drop with
      | zero => simpa using hget
      | succ drop =>
          obtain ⟨head, headValue⟩ := item
          have hrestGet : envGet (rest.drop drop) name = some value := by
            simpa using hget
          have hrestCount : (rest.map Prod.fst).count name ≤ 1 := by
            simp only [List.map_cons, List.count_cons] at hcount
            split at hcount <;> omega
          have hnameRest : name ∈ rest.map Prod.fst :=
            envGet_name_mem (ih hrestCount drop hrestGet)
          have hhead : head ≠ name := by
            intro heq
            subst head
            simp only [List.map_cons, List.count_cons, beq_self_eq_true,
              if_true] at hcount
            have : 0 < (rest.map Prod.fst).count name :=
              List.count_pos_iff.mpr hnameRest
            omega
          rw [envGet_cons]
          simp only [if_neg hhead]
          exact ih hrestCount drop hrestGet

theorem envGet_restore_of_count_le_one {outer source : WordEnv}
    {name : Ident} (hcount : (source.map Prod.fst).count name ≤ 1)
    {value : U256}
    (hget : envGet (@YulSemantics.restore G outer source) name = some value) :
    envGet source name = some value := by
  unfold YulSemantics.restore at hget
  exact envGet_drop_of_count_le_one hcount _ hget

/-! ## Bound exit names -/

theorem NamesBound.of_keys_eq {names : List Ident} {outer restored : WordEnv}
    (hbound : NamesBound names outer)
    (hkeys : restored.map Prod.fst = outer.map Prod.fst) :
    NamesBound names restored := by
  intro name hname
  obtain ⟨value, hget⟩ := hbound name hname
  apply envGet_exists_of_name_mem
  rw [hkeys]
  exact envGet_name_mem hget

theorem NamesBound.restore {names : List Ident} {outer source : WordEnv}
    (hbound : NamesBound names outer)
    (hkeys : (@YulSemantics.restore G outer source).map Prod.fst =
      outer.map Prod.fst) :
    NamesBound names (@YulSemantics.restore G outer source) := by
  exact NamesBound.of_keys_eq hbound hkeys

/-! ## Synchronized return values -/

/-- A target `VRel` environment cannot contain more occurrences of a name
than its source environment. -/
theorem VRel.target_count_le_source {slots : SlotMap} {owner : Owner}
    {signature : List Ident} {source target : WordEnv}
    (hrel : VRel slots owner signature source target) (name : Ident) :
    (target.map Prod.fst).count name ≤
      (source.map Prod.fst).count name := by
  induction hrel with
  | nil => simp
  | @unselected head value source target hslot tail ih =>
      simp only [List.map_cons, List.count_cons]
      split <;> omega
  | @selectedSignature head sourceValue targetValue source target slot
      hslot hsignature tail ih =>
      simp only [List.map_cons, List.count_cons]
      split <;> omega
  | @selectedLocal head value source target slot hslot hsignature tail ih =>
      simp only [List.map_cons, List.count_cons]
      split <;> omega

/-- Aligned lexical restoration preserves return synchronization.  Selected
exit names need source-side uniqueness because their retained target stack
cell may otherwise line up with a different shadowing occurrence. -/
theorem ReturnsSynced.restore_of_envRel
    {slots : SlotMap} {owner : Owner} {signature returns : List Ident}
    {cuts : List CutMark}
    {outerSource outerTarget source target : WordEnv}
    (hrel : EnvRel slots owner signature source target
      ({ sourceLen := outerSource.length,
          targetLen := outerTarget.length } :: cuts))
    (hsynced : ReturnsSynced returns source target)
    (hbound : NamesBound returns outerSource)
    (hkeys : (@YulSemantics.restore G outerSource source).map Prod.fst =
      outerSource.map Prod.fst)
    (hsignature : ∀ name ∈ returns, name ∈ signature)
    (hunique : ∀ name slot, slotFor? slots owner name = some slot →
      (source.map Prod.fst).count name ≤ 1) :
    ReturnsSynced returns
      (@YulSemantics.restore G outerSource source)
      (@YulSemantics.restore D outerTarget target) := by
  let restoredSource := @YulSemantics.restore G outerSource source
  let restoredTarget := @YulSemantics.restore D outerTarget target
  have hrestoredRel : EnvRel slots owner signature restoredSource
      restoredTarget cuts := by
    exact EnvRel.pop (hsource := rfl) (htarget := rfl) hrel
  have hrestoredBound : NamesBound returns restoredSource := by
    exact NamesBound.restore hbound hkeys
  intro name hname
  obtain ⟨sourceValue, hsourceRestored⟩ := hrestoredBound name hname
  cases hslot : slotFor? slots owner name with
  | none =>
      exact hrestoredRel.vars.get_of_no_slot hslot
  | some slot =>
      have hsourceCount : (source.map Prod.fst).count name ≤ 1 :=
        hunique name slot hslot
      have hsourceInner : envGet source name = some sourceValue :=
        envGet_restore_of_count_le_one hsourceCount hsourceRestored
      have htargetInner : envGet target name = some sourceValue := by
        rw [← hsynced name hname]
        exact hsourceInner
      obtain ⟨targetValue, htargetRestored⟩ :=
        hrestoredRel.vars.targetGet_of_selectedSignature hslot
          (hsignature name hname) hsourceRestored
      have htargetCount : (target.map Prod.fst).count name ≤ 1 :=
        le_trans
          (MemorySpillExitSound.VRel.target_count_le_source hrel.vars name)
          hsourceCount
      have htargetInner' : envGet target name = some targetValue := by
        unfold restoredTarget at htargetRestored
        exact envGet_drop_of_count_le_one htargetCount _ htargetRestored
      have hvalue : targetValue = sourceValue := by
        rw [htargetInner] at htargetInner'
        exact (Option.some.inj htargetInner').symm
      rw [hsourceRestored, htargetRestored, hvalue]

/-- `ScopedFrameRel` wrapper used directly by the statement simulation. -/
theorem returnsSynced_restore_of_scopedFrameRel
    {slots : SlotMap} {owner : Owner} {signature returns : List Ident}
    {cuts : List CutMark}
    {outerSource outerTarget source target : WordEnv}
    {sourceState targetState : EvmState}
    (hrel : ScopedFrameRel (base := base) (reserved := reserved)
      slots owner signature
      ({ sourceLen := outerSource.length,
          targetLen := outerTarget.length } :: cuts)
      source sourceState target targetState)
    (hsynced : ReturnsSynced returns source target)
    (hbound : NamesBound returns outerSource)
    (hkeys : (@YulSemantics.restore G outerSource source).map Prod.fst =
      outerSource.map Prod.fst)
    (hsignature : ∀ name ∈ returns, name ∈ signature)
    (hunique : ∀ name slot, slotFor? slots owner name = some slot →
      (source.map Prod.fst).count name ≤ 1) :
    ReturnsSynced returns
      (@YulSemantics.restore G outerSource source)
      (@YulSemantics.restore D outerTarget target) := by
  exact ReturnsSynced.restore_of_envRel hrel.env hsynced hbound hkeys
    hsignature hunique

end YulEvmCompiler.Optimizer.MemorySpillExitSound
