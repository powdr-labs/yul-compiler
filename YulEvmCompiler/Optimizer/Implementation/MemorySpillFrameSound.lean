import YulEvmCompiler.Optimizer.Implementation.MemorySpillRewriteSound
set_option warningAsError true
/-!
# Function-entry execution for memory spilling

The function calling convention enters with ordinary parameter and return
bindings still present on the target stack.  The spill rewrite then executes
`initParams ++ initReturns`: selected parameters are copied to their slots and
selected returns are initialized to zero.  This module proves that mechanical
entry sequence independently of the main syntax induction.
-/

namespace YulEvmCompiler.Optimizer.MemorySpillFrameSound

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer
open MemorySpillSelect
open MemorySpillStateSound
open MemorySpillRewriteSound

variable {base reserved : Nat}
variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "G" => guardedEvm calls creates base reserved
local notation "D" => evmWithExternal calls creates

/-- Concrete target state after copying the selected parameters in order. -/
def afterInitParams (slots : SlotMap) (owner : Owner) (target : WordEnv) :
    List Ident → EvmState → EvmState
  | [], state => state
  | name :: rest, state =>
      match slotFor? slots owner name, envGet target name with
      | some slot, some value =>
          afterInitParams slots owner target rest (slotState state slot value)
      | _, _ => afterInitParams slots owner target rest state

/-- Concrete target state after zero-initializing selected returns in order. -/
def afterInitReturns (slots : SlotMap) (owner : Owner) :
    List Ident → EvmState → EvmState
  | [], state => state
  | name :: rest, state =>
      match slotFor? slots owner name with
      | some slot => afterInitReturns slots owner rest (slotState state slot 0)
      | none => afterInitReturns slots owner rest state

def NamesBound (names : List Ident) (target : WordEnv) : Prop :=
  ∀ name, name ∈ names → ∃ value, envGet target name = some value

/-- Selected signature slots are pairwise disjoint.  This is exactly the
allocator fact needed to retain earlier parameter writes while later
parameter/return stores execute. -/
def SignatureSlotsDisjoint (slots : SlotMap) (owner : Owner)
    (signature : List Ident) : Prop :=
  ∀ left ∈ signature, ∀ right ∈ signature, left ≠ right →
    ∀ leftSlot rightSlot,
      slotFor? slots owner left = some leftSlot →
      slotFor? slots owner right = some rightSlot →
      leftSlot + 32 ≤ rightSlot ∨ rightSlot + 32 ≤ leftSlot

private theorem execStmts_append_normal {funs : FunEnv D}
    {pre suffix : Block Op} {vars vars' vars'' : WordEnv}
    {state state' state'' : EvmState} {outcome : Outcome}
    (hpre : ExecStmts D funs vars state pre vars' state' .normal)
    (hsuffix : ExecStmts D funs vars' state' suffix vars'' state'' outcome) :
    ExecStmts D funs vars state (pre ++ suffix) vars'' state'' outcome := by
  induction pre generalizing vars state with
  | nil => cases hpre with | seqNil => exact hsuffix
  | cons statement rest ih =>
      cases hpre with
      | seqCons hstatement hrest =>
          exact Step.seqCons hstatement (ih hrest)
      | seqStop _ hne => exact False.elim (hne rfl)

theorem execInitParams {slots : SlotMap} {owner : Owner}
    {sourceFuns : FunEnv G} {target : WordEnv} {state : EvmState}
    (hbounds : ∀ name slot, slotFor? slots owner name = some slot →
      slot + 32 ≤ reserved)
    (hreserved : reserved < 2 ^ 256) :
    ∀ params : List Ident, NamesBound params target →
      ExecStmts D (spillFuns slots sourceFuns) target state
        (initParams slots owner params) target
        (afterInitParams slots owner target params state) .normal := by
  intro params
  induction params generalizing state with
  | nil =>
      intro _
      exact Step.seqNil
  | cons name rest ih =>
      intro hbound
      have hrest : NamesBound rest target := by
        intro other hmem
        exact hbound other (by simp [hmem])
      cases hslot : slotFor? slots owner name with
      | none =>
          simpa [initParams, afterInitParams, hslot] using ih hrest
      | some slot =>
          obtain ⟨value, hget⟩ := hbound name (by simp)
          have hslotLt : slot < 2 ^ 256 := by
            have := hbounds name slot hslot
            omega
          have heval : EvalExpr D (spillFuns slots sourceFuns) target state
              (.var name) (.vals [value] state) := Step.var hget
          have hhead := execStoreSlot hslotLt heval
          have htail := ih (state := slotState state slot value) hrest
          simpa [initParams, afterInitParams, hslot, hget] using
            Step.seqCons hhead htail

theorem execInitReturns {slots : SlotMap} {owner : Owner}
    {sourceFuns : FunEnv G} {target : WordEnv} {state : EvmState}
    (hbounds : ∀ name slot, slotFor? slots owner name = some slot →
      slot + 32 ≤ reserved)
    (hreserved : reserved < 2 ^ 256) :
    ∀ returns : List Ident,
      ExecStmts D (spillFuns slots sourceFuns) target state
        (initReturns slots owner returns) target
        (afterInitReturns slots owner returns state) .normal := by
  intro returns
  induction returns generalizing state with
  | nil => exact Step.seqNil
  | cons name rest ih =>
      cases hslot : slotFor? slots owner name with
      | none =>
          simpa [initReturns, afterInitReturns, hslot] using ih
      | some slot =>
          have hslotLt : slot < 2 ^ 256 := by
            have := hbounds name slot hslot
            omega
          have heval : EvalExpr D (spillFuns slots sourceFuns) target state
              (MemorySpill.word 0) (.vals [0] state) := by
            have hzero : Dialect.litValue D (.number 0) = (0 : U256) := by
              change litValue (.number 0) = (0 : U256)
              decide
            change EvalExpr D (spillFuns slots sourceFuns) target state
              (.lit (.number 0)) (.vals [0] state)
            rw [← hzero]
            exact Step.lit
          have hhead := execStoreSlot hslotLt heval
          have htail := ih (state := slotState state slot 0)
          simpa [initReturns, afterInitReturns, hslot] using
            Step.seqCons hhead htail

theorem execEntryPrologue {slots : SlotMap} {owner : Owner}
    {sourceFuns : FunEnv G} {target : WordEnv} {state : EvmState}
    {params returns : List Ident}
    (hbound : NamesBound params target)
    (hbounds : ∀ name slot, slotFor? slots owner name = some slot →
      slot + 32 ≤ reserved)
    (hreserved : reserved < 2 ^ 256) :
    let afterParams := afterInitParams slots owner target params state
    let finalState := afterInitReturns slots owner returns afterParams
    ExecStmts D (spillFuns slots sourceFuns) target state
      (initParams slots owner params ++ initReturns slots owner returns)
      target finalState .normal := by
  dsimp only
  exact execStmts_append_normal (execInitParams hbounds hreserved params hbound)
    (execInitReturns (state := afterInitParams slots owner target params state)
      hbounds hreserved returns)

theorem afterInitParams_scratch {slots : SlotMap} {owner : Owner}
    {target : WordEnv}
    (hbounds : ∀ name slot, slotFor? slots owner name = some slot →
      base ≤ slot ∧ slot + 32 ≤ reserved) :
    ∀ params state,
      ScratchRel base reserved state
        (afterInitParams slots owner target params state) := by
  intro params
  induction params with
  | nil => intro state; exact ScratchRel.refl base reserved state
  | cons name rest ih =>
      intro state
      cases hslot : slotFor? slots owner name with
      | none =>
          simp [afterInitParams, hslot]
          exact ih state
      | some slot =>
          cases hget : envGet target name with
          | none =>
              simp [afterInitParams, hslot, hget]
              exact ih state
          | some value =>
              simp only [afterInitParams, hslot, hget]
              exact (slotState_scratch_rel (hbounds name slot hslot) state).trans
                (ih (slotState state slot value))

theorem afterInitReturns_scratch {slots : SlotMap} {owner : Owner}
    (hbounds : ∀ name slot, slotFor? slots owner name = some slot →
      base ≤ slot ∧ slot + 32 ≤ reserved) :
    ∀ returns state,
      ScratchRel base reserved state
        (afterInitReturns slots owner returns state) := by
  intro returns
  induction returns with
  | nil => intro state; exact ScratchRel.refl base reserved state
  | cons name rest ih =>
      intro state
      cases hslot : slotFor? slots owner name with
      | none =>
          simp [afterInitReturns, hslot]
          exact ih state
      | some slot =>
          simp only [afterInitReturns, hslot]
          exact (slotState_scratch_rel (hbounds name slot hslot) state).trans
            (ih (slotState state slot 0))

theorem afterInitParams_above {slots : SlotMap} {owner : Owner}
    {target : WordEnv} {cutoff : Nat}
    (hbounds : ∀ name slot, slotFor? slots owner name = some slot →
      slot + 32 ≤ cutoff) :
    ∀ params state,
      AboveUnchanged cutoff reserved state
        (afterInitParams slots owner target params state) := by
  intro params
  induction params with
  | nil => intro state; exact AboveUnchanged.refl cutoff reserved state
  | cons name rest ih =>
      intro state
      cases hslot : slotFor? slots owner name with
      | none => simpa [afterInitParams, hslot] using ih state
      | some slot =>
          cases hget : envGet target name with
          | none => simpa [afterInitParams, hslot, hget] using ih state
          | some value =>
              simp only [afterInitParams, hslot, hget]
              exact (AboveUnchanged.slotState (reserved := reserved)
                (hbounds name slot hslot) state).trans
                (ih (slotState state slot value))

theorem afterInitReturns_above {slots : SlotMap} {owner : Owner}
    {cutoff : Nat}
    (hbounds : ∀ name slot, slotFor? slots owner name = some slot →
      slot + 32 ≤ cutoff) :
    ∀ returns state,
      AboveUnchanged cutoff reserved state
        (afterInitReturns slots owner returns state) := by
  intro returns
  induction returns with
  | nil => intro state; exact AboveUnchanged.refl cutoff reserved state
  | cons name rest ih =>
      intro state
      cases hslot : slotFor? slots owner name with
      | none => simpa [afterInitReturns, hslot] using ih state
      | some slot =>
          simp only [afterInitReturns, hslot]
          exact (AboveUnchanged.slotState (reserved := reserved)
            (hbounds name slot hslot) state).trans
            (ih (slotState state slot 0))

/-! ## Readback from the completed prologue -/

theorem afterInitParams_preserves {slots : SlotMap} {owner : Owner}
    {target : WordEnv} {protectedSlot : Nat}
    (hdisjoint : ∀ name ∈ params, ∀ slot,
      slotFor? slots owner name = some slot →
      slot + 32 ≤ protectedSlot ∨ protectedSlot + 32 ≤ slot) :
    ∀ state,
      loadWord (afterInitParams slots owner target params state).memory protectedSlot =
        loadWord state.memory protectedSlot := by
  induction params with
  | nil => intro state; rfl
  | cons name rest ih =>
      intro state
      have hrest : ∀ other ∈ rest, ∀ slot,
          slotFor? slots owner other = some slot →
          slot + 32 ≤ protectedSlot ∨ protectedSlot + 32 ≤ slot := by
        intro other hmem
        exact hdisjoint other (by simp [hmem])
      cases hslot : slotFor? slots owner name with
      | none => simpa [afterInitParams, hslot] using ih hrest state
      | some slot =>
          cases hget : envGet target name with
          | none => simpa [afterInitParams, hslot, hget] using ih hrest state
          | some value =>
              rw [afterInitParams, hslot, hget, ih hrest]
              simp only [slotState]
              rw [loadWord_storeWord_other state.memory slot protectedSlot value
                (hdisjoint name (by simp) slot hslot)]

theorem afterInitReturns_preserves {slots : SlotMap} {owner : Owner}
    {protectedSlot : Nat}
    (hdisjoint : ∀ name ∈ returns, ∀ slot,
      slotFor? slots owner name = some slot →
      slot + 32 ≤ protectedSlot ∨ protectedSlot + 32 ≤ slot) :
    ∀ state,
      loadWord (afterInitReturns slots owner returns state).memory protectedSlot =
        loadWord state.memory protectedSlot := by
  induction returns with
  | nil => intro state; rfl
  | cons name rest ih =>
      intro state
      have hrest : ∀ other ∈ rest, ∀ slot,
          slotFor? slots owner other = some slot →
          slot + 32 ≤ protectedSlot ∨ protectedSlot + 32 ≤ slot := by
        intro other hmem
        exact hdisjoint other (by simp [hmem])
      cases hslot : slotFor? slots owner name with
      | none => simpa [afterInitReturns, hslot] using ih hrest state
      | some slot =>
          rw [afterInitReturns, hslot, ih hrest]
          simp only [slotState]
          rw [loadWord_storeWord_other state.memory slot protectedSlot 0
            (hdisjoint name (by simp) slot hslot)]

theorem afterInitParams_load {slots : SlotMap} {owner : Owner}
    {target : WordEnv} {signature : List Ident}
    (hbound : NamesBound params target)
    (hnodup : params.Nodup)
    (hsignature : ∀ name ∈ params, name ∈ signature)
    (hdisjoint : SignatureSlotsDisjoint slots owner signature) :
    ∀ {name slot value}, name ∈ params →
      slotFor? slots owner name = some slot →
      envGet target name = some value →
      ∀ state,
        loadWord (afterInitParams slots owner target params state).memory slot = value := by
  induction params with
  | nil => intro name slot value hmem; simp at hmem
  | cons head rest ih =>
      intro name slot value hmem hslot hget state
      have hparts := List.nodup_cons.mp hnodup
      have hrestBound : NamesBound rest target := by
        intro other hother
        exact hbound other (by simp [hother])
      have hrestSignature : ∀ other ∈ rest, other ∈ signature := by
        intro other hother
        exact hsignature other (by simp [hother])
      rcases List.mem_cons.mp hmem with hnameEq | hnameRest
      · subst name
        cases hheadSlot : slotFor? slots owner head with
        | none => rw [hheadSlot] at hslot; contradiction
        | some headSlot =>
            have hslotEq : headSlot = slot := by
              rw [hslot] at hheadSlot
              exact (Option.some.inj hheadSlot).symm
            subst headSlot
            have hrestDisjoint : ∀ other ∈ rest, ∀ otherSlot,
                slotFor? slots owner other = some otherSlot →
                otherSlot + 32 ≤ slot ∨ slot + 32 ≤ otherSlot := by
              intro other hother otherSlot hotherSlot
              exact hdisjoint other (hrestSignature other hother) head
                (hsignature head (by simp))
                (fun heq => hparts.1 (heq ▸ hother))
                otherSlot slot hotherSlot hslot
            rw [afterInitParams, hheadSlot, hget]
            rw [afterInitParams_preserves hrestDisjoint]
            exact slotState_load state slot value
      · cases hheadSlot : slotFor? slots owner head with
        | none =>
            simp only [afterInitParams, hheadSlot]
            exact ih hrestBound hparts.2 hrestSignature hnameRest hslot hget state
        | some headSlot =>
            obtain ⟨headValue, hheadGet⟩ := hbound head (by simp)
            simp only [afterInitParams, hheadSlot, hheadGet]
            exact ih hrestBound hparts.2 hrestSignature hnameRest hslot hget
              (slotState state headSlot headValue)

theorem afterInitReturns_load {slots : SlotMap} {owner : Owner}
    {signature : List Ident}
    (hnodup : returns.Nodup)
    (hsignature : ∀ name ∈ returns, name ∈ signature)
    (hdisjoint : SignatureSlotsDisjoint slots owner signature) :
    ∀ {name slot}, name ∈ returns →
      slotFor? slots owner name = some slot →
      ∀ state,
        loadWord (afterInitReturns slots owner returns state).memory slot = 0 := by
  induction returns with
  | nil => intro name slot hmem; simp at hmem
  | cons head rest ih =>
      intro name slot hmem hslot state
      have hparts := List.nodup_cons.mp hnodup
      have hrestSignature : ∀ other ∈ rest, other ∈ signature := by
        intro other hother
        exact hsignature other (by simp [hother])
      rcases List.mem_cons.mp hmem with hnameEq | hnameRest
      · subst name
        cases hheadSlot : slotFor? slots owner head with
        | none => rw [hheadSlot] at hslot; contradiction
        | some headSlot =>
            have hslotEq : headSlot = slot := by
              rw [hslot] at hheadSlot
              exact (Option.some.inj hheadSlot).symm
            subst headSlot
            have hrestDisjoint : ∀ other ∈ rest, ∀ otherSlot,
                slotFor? slots owner other = some otherSlot →
                otherSlot + 32 ≤ slot ∨ slot + 32 ≤ otherSlot := by
              intro other hother otherSlot hotherSlot
              exact hdisjoint other (hrestSignature other hother) head
                (hsignature head (by simp))
                (fun heq => hparts.1 (heq ▸ hother))
                otherSlot slot hotherSlot hslot
            rw [afterInitReturns, hheadSlot]
            rw [afterInitReturns_preserves hrestDisjoint]
            exact slotState_load state slot 0
      · cases hheadSlot : slotFor? slots owner head with
        | none =>
            simp only [afterInitReturns, hheadSlot]
            exact ih hparts.2 hrestSignature hnameRest hslot state
        | some headSlot =>
            simp only [afterInitReturns, hheadSlot]
            exact ih hparts.2 hrestSignature hnameRest hslot
              (slotState state headSlot 0)

def ParamsSynced (params : List Ident) (source target : WordEnv) : Prop :=
  ∀ name, name ∈ params → envGet source name = envGet target name

def ReturnsZero (returns : List Ident) (source : WordEnv) : Prop :=
  ∀ name, name ∈ returns → envGet source name = some 0

def EnvNamesIn (source : WordEnv) (names : List Ident) : Prop :=
  ∀ name, name ∈ source.map Prod.fst → name ∈ names

theorem entryPrologue_slotsLoaded {slots : SlotMap} {owner : Owner}
    {params returns : List Ident} {source target : WordEnv}
    (hbound : NamesBound params target)
    (hnodup : (params ++ returns).Nodup)
    (hdisjoint : SignatureSlotsDisjoint slots owner (params ++ returns))
    (hsynced : ParamsSynced params source target)
    (hzero : ReturnsZero returns source)
    (hnames : EnvNamesIn source (params ++ returns)) :
    let afterParams := afterInitParams slots owner target params
    ∀ initial,
      SlotsLoaded slots owner source
        (afterInitReturns slots owner returns (afterParams initial)) := by
  dsimp only
  intro initial name slot value hslot hget
  have hname : name ∈ params ++ returns := by
    apply hnames name
    unfold envGet at hget
    cases hfind : source.find? (fun item => item.1 = name) with
    | none => simp [hfind] at hget
    | some item =>
        have hmem := List.mem_of_find?_eq_some hfind
        have hkey := List.find?_some hfind
        have hitemName : item.1 = name := by simpa using hkey
        exact List.mem_map.mpr ⟨item, hmem, hitemName⟩
  have hparts := List.nodup_append.mp hnodup
  rcases List.mem_append.mp hname with hparam | hreturn
  · have hreturnDisjoint : ∀ other ∈ returns, ∀ otherSlot,
        slotFor? slots owner other = some otherSlot →
        otherSlot + 32 ≤ slot ∨ slot + 32 ≤ otherSlot := by
      intro other hother otherSlot hotherSlot
      exact hdisjoint other (by simp [hother]) name (by simp [hparam])
        (fun heq => hparts.2.2 name hparam other hother heq.symm)
        otherSlot slot hotherSlot hslot
    rw [afterInitReturns_preserves hreturnDisjoint]
    have htarget : envGet target name = some value := by
      rw [← hsynced name hparam]
      exact hget
    exact afterInitParams_load hbound hparts.1 (by
      intro item hmem; exact List.mem_append_left _ hmem) hdisjoint
      hparam hslot htarget initial
  · have hvalue : value = 0 := by
      rw [hzero name hreturn] at hget
      exact (Option.some.inj hget).symm
    subst value
    exact afterInitReturns_load hparts.2.1 (by
      intro item hmem; exact List.mem_append_right _ hmem) hdisjoint
      hreturn hslot (afterInitParams slots owner target params initial)

theorem layout_signatureSlotsDisjoint {selected : SpillSet}
    {policyBody : Block Op} {layout : MemorySpillSelect.Layout}
    {frame : Frame}
    (hbuild : buildLayout base selected policyBody = some layout)
    (hcheck : layoutCheck base reserved selected layout = true)
    (hframe : frame ∈ frames policyBody) :
    SignatureSlotsDisjoint layout.slots frame.owner
      (frame.params ++ frame.returns) := by
  intro left hleft right hright hne leftSlot rightSlot hleftSlot hrightSlot
  have hleftSelected := layoutCheck_slot_selected hcheck hleftSlot
  have hrightSelected := layoutCheck_slot_selected hcheck hrightSlot
  have hleftLive : { owner := frame.owner, name := left } ∈
      frameInitialLive selected frame := by
    unfold frameInitialLive selectedKeys
    simp only [List.mem_filterMap]
    refine ⟨left, hleft, ?_⟩
    simp [hleftSelected, List.contains_eq_mem]
  have hrightLive : { owner := frame.owner, name := right } ∈
      frameInitialLive selected frame := by
    unfold frameInitialLive selectedKeys
    simp only [List.mem_filterMap]
    refine ⟨right, hright, ?_⟩
    simp [hrightSelected, List.contains_eq_mem]
  obtain ⟨maxLive, hmax, hsubset⟩ :=
    (liveCertified_initial selected frame).covered
  have hkeysNe : ({ owner := frame.owner, name := left } : SpillKey) ≠
      { owner := frame.owner, name := right } := by
    intro heq
    exact hne (congrArg SpillKey.name heq)
  have hslotsNe : leftSlot ≠ rightSlot :=
    buildLayout_live_slots_ne hbuild hcheck hframe hmax
      (hsubset _ hleftLive) (hsubset _ hrightLive) hkeysNe
      hleftSlot hrightSlot
  exact layoutCheck_distinct_slots_disjoint hcheck
    (slotFor_mem_of_eq_some hleftSlot)
    (slotFor_mem_of_eq_some hrightSlot) hslotsNe

theorem entryBoundSelected {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame} {source : WordEnv}
    (hcheck : layoutCheck base reserved selected layout = true)
    (hnames : EnvNamesIn source (frame.params ++ frame.returns)) :
    BoundSelectedIn layout.slots frame.owner source
      (frameInitialLive selected frame) := by
  intro name hname slot hslot
  have hsignature := hnames name hname
  have hselected := layoutCheck_slot_selected hcheck hslot
  unfold frameInitialLive selectedKeys
  simp only [List.mem_filterMap]
  refine ⟨name, hsignature, ?_⟩
  simp [hselected, List.contains_eq_mem]

/-- Complete function-entry theorem consumed by the call simulation.  It
executes the inserted prologue, establishes authoritative slot contents for
the source call environment, and packages the initial lexical-live
certificate. -/
theorem execEntryPrologue_live {selected : SpillSet}
    {policyBody : Block Op} {layout : MemorySpillSelect.Layout}
    {frame : Frame} {source target : WordEnv}
    {sourceState targetState : EvmState} {sourceFuns : FunEnv G}
    (hbuild : buildLayout base selected policyBody = some layout)
    (hcheck : layoutCheck base reserved selected layout = true)
    (hframe : frame ∈ frames policyBody)
    (hentry : EntryFrameRel (base := base) (reserved := reserved)
      layout.slots frame.owner (frame.params ++ frame.returns)
      source sourceState target targetState)
    (hbound : NamesBound frame.params target)
    (hnodup : (frame.params ++ frame.returns).Nodup)
    (hsynced : ParamsSynced frame.params source target)
    (hzero : ReturnsZero frame.returns source)
    (hnames : EnvNamesIn source (frame.params ++ frame.returns))
    (hreserved : reserved < 2 ^ 256)
    (cutoff : Nat)
    (hcutoff : ∀ name slot,
      slotFor? layout.slots frame.owner name = some slot →
      slot + 32 ≤ cutoff) :
    let afterParams := afterInitParams layout.slots frame.owner target
      frame.params targetState
    let finalState := afterInitReturns layout.slots frame.owner
      frame.returns afterParams
    ExecStmts D (spillFuns layout.slots sourceFuns) target targetState
      (initParams layout.slots frame.owner frame.params ++
        initReturns layout.slots frame.owner frame.returns)
      target finalState .normal ∧
    LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame (frame.params ++ frame.returns) []
      (frameInitialLive selected frame)
      source sourceState target finalState ∧
    AboveUnchanged cutoff reserved targetState finalState := by
  dsimp only
  have hbounds : ∀ name slot,
      slotFor? layout.slots frame.owner name = some slot →
      base ≤ slot ∧ slot + 32 ≤ reserved := by
    intro name slot hslot
    exact layoutCheck_slotFor_bounds hcheck hslot
  have hexec := execEntryPrologue (sourceFuns := sourceFuns)
    (state := targetState) (returns := frame.returns)
    hbound (fun name slot hslot => (hbounds name slot hslot).2) hreserved
  dsimp only at hexec
  have hscratchParams := afterInitParams_scratch
    (target := target) hbounds frame.params targetState
  have hscratchReturns := afterInitReturns_scratch hbounds frame.returns
    (afterInitParams layout.slots frame.owner target frame.params targetState)
  have hscratch := hscratchParams.trans hscratchReturns
  have hdisjoint := layout_signatureSlotsDisjoint hbuild hcheck hframe
  have hloaded := entryPrologue_slotsLoaded hbound hnodup hdisjoint
    hsynced hzero hnames targetState
  have hscoped : ScopedFrameRel (base := base) (reserved := reserved)
      layout.slots frame.owner (frame.params ++ frame.returns) []
      source sourceState target
      (afterInitReturns layout.slots frame.owner frame.returns
        (afterInitParams layout.slots frame.owner target frame.params targetState)) := {
    env := hentry.env
    loaded := hloaded
    scratch := hentry.scratch.trans hscratch }
  have hlive : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame (frame.params ++ frame.returns) []
      (frameInitialLive selected frame) source sourceState target
      (afterInitReturns layout.slots frame.owner frame.returns
        (afterInitParams layout.slots frame.owner target frame.params targetState)) := {
    frameRel := hscoped
    bound := entryBoundSelected hcheck hnames
    certified := liveCertified_initial selected frame }
  have haboveParams := afterInitParams_above (reserved := reserved)
    (target := target) hcutoff frame.params targetState
  have haboveReturns := afterInitReturns_above (reserved := reserved)
    hcutoff frame.returns
    (afterInitParams layout.slots frame.owner target frame.params targetState)
  exact ⟨hexec, hlive, haboveParams.trans haboveReturns⟩

/-! The execution, scratch, and high-memory results above are unconditional
once parameter lookup and slot bounds are supplied.  The remaining conversion
from `EntryFrameRel` to `ScopedFrameRel` is exposed with its precise missing
piece: `SlotsLoaded` for the completed state.  The readback lemmas immediately
above are intended to discharge it from signature `Nodup` plus the allocator's
live-set non-alias certificate. -/

theorem entryToScopedAfterPrologue {slots : SlotMap} {owner : Owner}
    {signature : List Ident} {source target : WordEnv}
    {sourceState targetState finalState : EvmState}
    (hentry : EntryFrameRel (base := base) (reserved := reserved)
      slots owner signature source sourceState target targetState)
    (hloaded : SlotsLoaded slots owner source finalState)
    (hscratch : ScratchRel base reserved targetState finalState) :
    ScopedFrameRel (base := base) (reserved := reserved)
      slots owner signature [] source sourceState target finalState := by
  exact {
    env := hentry.env
    loaded := hloaded
    scratch := hentry.scratch.trans hscratch }

theorem scopedToInitialLive {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {source target : WordEnv} {sourceState targetState : EvmState}
    (hscoped : ScopedFrameRel (base := base) (reserved := reserved)
      layout.slots frame.owner (frame.params ++ frame.returns) []
      source sourceState target targetState)
    (hbound : BoundSelectedIn layout.slots frame.owner source
      (frameInitialLive selected frame)) :
    LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame (frame.params ++ frame.returns) []
      (frameInitialLive selected frame)
      source sourceState target targetState := by
  exact {
    frameRel := hscoped
    bound := hbound
    certified := liveCertified_initial selected frame }

end YulEvmCompiler.Optimizer.MemorySpillFrameSound
