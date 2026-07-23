import YulEvmCompiler.Optimizer.Implementation.MemorySpillFrameSound
import YulEvmCompiler.Optimizer.Implementation.MemorySpillOriginSound
import YulEvmCompiler.Optimizer.Implementation.MemorySpillResolveSound
set_option warningAsError true
/-!
# User-call shell for memory spilling

This module isolates the change of spill-frame owner at a user-function call.
It transports dynamic lookup to the rewritten function environment, identifies
the exact allocator frame, establishes and executes the callee entry prologue,
and provides constructors that close the ordinary and halting call rules from
an explicit simulation of the rewritten callee body.
-/

namespace YulEvmCompiler.Optimizer.MemorySpillCallSound

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer
open MemorySpillSelect
open MemorySpillStateSound
open MemorySpillRewriteSound
open MemorySpillFrameSound
open MemorySpillOriginSound

variable {base reserved : Nat}
variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "G" => guardedEvm calls creates base reserved
local notation "D" => evmWithExternal calls creates

/-! ## Lookup and exact frame selection -/

def calleeFrame (name : Ident) (decl : FDecl G) : Frame :=
  { owner := some name
    params := decl.params
    returns := decl.rets
    body := decl.body }

/-- Dynamic source lookup transports to the mechanically spilled declaration,
while the origin certificate identifies the declaration's exact policy frame
and preserves coverage for the captured closure. -/
theorem lookupSpilledCallee {slots : SlotMap} {allFrames : List Frame}
    {sourceFuns : FunEnv G} {name : Ident} {decl : FDecl G}
    {closure : FunEnv G}
    (hcovered : FunsCovered G (fun body => body) allFrames sourceFuns)
    (hlookup : lookupFun sourceFuns name = some (decl, closure)) :
    lookupFun (spillFuns slots sourceFuns) name =
        some (spillDecl slots name decl, spillFuns slots closure) ∧
      (∃ frame ∈ allFrames,
        frame.owner = some name ∧
        frame.params = decl.params ∧
        frame.returns = decl.rets ∧
        frame.body = decl.body) ∧
      FunsCovered G (fun body => body) allFrames closure := by
  have htransport := spillFuns_lookup_some slots hlookup
  obtain ⟨hdecl, hclosure⟩ := hcovered.lookup hlookup
  exact ⟨htransport, hdecl, hclosure⟩

theorem covered_calleeFrame_mem {allFrames : List Frame}
    {sourceFuns : FunEnv G} {name : Ident} {decl : FDecl G}
    {closure : FunEnv G}
    (hcovered : FunsCovered G (fun body => body) allFrames sourceFuns)
    (hlookup : lookupFun sourceFuns name = some (decl, closure)) :
    calleeFrame name decl ∈ allFrames := by
  obtain ⟨_, hdecl, _⟩ :=
    lookupSpilledCallee (slots := []) hcovered hlookup
  obtain ⟨frame, hframe, howner, hparams, hreturns, hbody⟩ := hdecl
  have heq : frame = calleeFrame name decl := by
    cases frame
    simp_all [calleeFrame]
  exact heq ▸ hframe

/-! ## Calling-convention environment -/

def callEnv (params returns : List Ident) (argvals : List U256) : WordEnv :=
  params.zip argvals ++ returns.map (fun name => (name, (0 : U256)))

private theorem envGet_zip_append_of_mem {names : List Ident}
    (hnodup : names.Nodup) :
    ∀ {values : List U256}, values.length = names.length →
      ∀ {name value tail}, (name, value) ∈ names.zip values →
        envGet (names.zip values ++ tail) name = some value := by
  induction names with
  | nil => simp
  | cons head rest ih =>
      intro values hlength name value tail hmem
      cases values with
      | nil => simp at hlength
      | cons first values =>
          simp only [List.zip_cons_cons, List.mem_cons] at hmem
          rcases hmem with heq | hmem
          · cases heq
            simp [envGet_cons]
          · have hhead : head ≠ name := by
              intro heq
              apply (List.nodup_cons.mp hnodup).1
              rw [heq]
              exact (List.of_mem_zip hmem).1
            change envGet ((head, first) :: (rest.zip values ++ tail)) name =
              some value
            rw [envGet_cons]
            simp only [if_neg hhead]
            exact ih (List.nodup_cons.mp hnodup).2 (by simpa using hlength) hmem

private theorem envGet_append_of_name_not_mem {pre tail : WordEnv}
    {name : Ident} (hname : name ∉ pre.map Prod.fst) :
    envGet (pre ++ tail) name = envGet tail name := by
  induction pre with
  | nil => rfl
  | cons item rest ih =>
      obtain ⟨head, value⟩ := item
      have hhead : head ≠ name := by
        intro heq
        exact hname (by simp [heq])
      have hrest : name ∉ rest.map Prod.fst := by
        intro hmem
        exact hname (by simp [hmem])
      simp [envGet_cons, hhead, ih hrest]

private theorem envGet_bindZeros_of_mem {returns : List Ident}
    (hnodup : returns.Nodup) {name : Ident} (hname : name ∈ returns) :
    envGet (returns.map (fun item => (item, (0 : U256)))) name = some 0 := by
  induction returns with
  | nil => simp at hname
  | cons head rest ih =>
      rcases List.mem_cons.mp hname with rfl | hrest
      · simp [envGet_cons]
      · have hne : head ≠ name := by
          intro heq
          exact (List.nodup_cons.mp hnodup).1 (heq ▸ hrest)
        simp only [List.map_cons, envGet_cons, if_neg hne]
        exact ih (List.nodup_cons.mp hnodup).2 hrest

private theorem exists_mem_zip_of_mem {names : List Ident} :
    ∀ {values : List U256}, values.length = names.length →
      ∀ {name}, name ∈ names → ∃ value, (name, value) ∈ names.zip values := by
  induction names with
  | nil => simp
  | cons head rest ih =>
      intro values hlength name hname
      cases values with
      | nil => simp at hlength
      | cons value values =>
          rcases List.mem_cons.mp hname with rfl | hrest
          · exact ⟨value, by simp⟩
          · obtain ⟨found, hfound⟩ := ih (by simpa using hlength) hrest
            exact ⟨found, by simp [hfound]⟩

/-- The exact environment installed by `Step.callOk` has all parameters
bound, equal source/target parameter views, zeroed returns, and no names
outside the signature. -/
structure CallEntryFacts (params returns : List Ident) (argvals : List U256) :
    Prop where
  bound : NamesBound params (callEnv params returns argvals)
  synced : ParamsSynced params (callEnv params returns argvals)
    (callEnv params returns argvals)
  zero : ReturnsZero returns (callEnv params returns argvals)
  names : EnvNamesIn (callEnv params returns argvals) (params ++ returns)

theorem callEntryFacts {params returns : List Ident} {argvals : List U256}
    (hlength : argvals.length = params.length)
    (hnodup : (params ++ returns).Nodup) :
    CallEntryFacts params returns argvals := by
  have hparts := List.nodup_append.mp hnodup
  constructor
  · intro name hname
    have hpair := exists_mem_zip_of_mem hlength hname
    obtain ⟨value, hvalue⟩ := hpair
    refine ⟨value, ?_⟩
    unfold callEnv
    exact envGet_zip_append_of_mem hparts.1 hlength hvalue
  · intro name _
    rfl
  · intro name hname
    unfold callEnv
    rw [envGet_append_of_name_not_mem]
    · exact envGet_bindZeros_of_mem hparts.2.1 hname
    · rw [List.map_fst_zip (by omega)]
      exact fun hparam => hparts.2.2 name hparam name hname rfl
  · intro name hname
    unfold callEnv at hname
    rw [List.map_append, List.map_fst_zip (by omega)] at hname
    simpa using hname

/-- Entry relation for the exact call environment.  It is intentionally
separate from the prologue theorem so callers can compose an argument-state
scratch relation first. -/
theorem callEntryRel (slots : SlotMap) (owner : Owner)
    {params returns : List Ident} {argvals : List U256}
    (sourceState targetState : EvmState)
    (hscratch : ScratchRel base reserved sourceState targetState) :
    EntryFrameRel (base := base) (reserved := reserved) slots owner
      (params ++ returns) (callEnv params returns argvals) sourceState
      (callEnv params returns argvals) targetState := by
  apply EntryFrameRel.exactSignature
  · intro item hitem
    unfold callEnv at hitem
    rcases List.mem_append.mp hitem with hparam | hreturn
    · exact List.mem_append_left _ (List.of_mem_zip hparam).1
    · obtain ⟨name, hname, heq⟩ := List.mem_map.mp hreturn
      cases heq
      exact List.mem_append_right _ hname
  · exact hscratch

/-- Execute the full callee entry sequence from the exact semantic call
environment and establish the initial live-frame certificate. -/
theorem enterCallee {selected : SpillSet} {policyBody : Block Op}
    {layout : MemorySpillSelect.Layout} {name : Ident} {decl : FDecl G}
    {closure : FunEnv G} {argvals : List U256}
    {sourceState targetState : EvmState}
    (hbuild : buildLayout base selected policyBody = some layout)
    (hcheck : layoutCheck base reserved selected layout = true)
    (hframe : calleeFrame name decl ∈ frames policyBody)
    (hlength : argvals.length = decl.params.length)
    (hnodup : (decl.params ++ decl.rets).Nodup)
    (hscratch : ScratchRel base reserved sourceState targetState)
    (hreserved : reserved < 2 ^ 256)
    (cutoff : Nat)
    (hcutoff : ∀ localName slot,
      slotFor? layout.slots (some name) localName = some slot →
        slot + 32 ≤ cutoff) :
    let entry := callEnv decl.params decl.rets argvals
    let afterParams := afterInitParams layout.slots (some name) entry
      decl.params targetState
    let afterEntry := afterInitReturns layout.slots (some name) decl.rets
      afterParams
    ExecStmts D (spillFuns layout.slots ([] :: closure)) entry targetState
      (initParams layout.slots (some name) decl.params ++
        initReturns layout.slots (some name) decl.rets)
      entry afterEntry .normal ∧
    LiveFrameRel (base := base) (reserved := reserved)
      selected layout (calleeFrame name decl) (decl.params ++ decl.rets) []
      (frameInitialLive selected (calleeFrame name decl))
      entry sourceState entry afterEntry ∧
    AboveUnchanged cutoff reserved targetState afterEntry := by
  dsimp only
  have hfacts := callEntryFacts hlength hnodup
  have hentry := callEntryRel (params := decl.params) (returns := decl.rets)
    (argvals := argvals) layout.slots (some name)
    sourceState targetState hscratch
  simpa [calleeFrame] using
    (execEntryPrologue_live hbuild hcheck hframe hentry hfacts.bound
      hnodup hfacts.synced hfacts.zero hfacts.names hreserved cutoff hcutoff)

/-! ## Allocator call-path separation -/

/-- Every callee slot ends below its certified frame cutoff. -/
theorem calleeSlotEnd_le_cutoff {selected : SpillSet} {policyBody : Block Op}
    {layout : MemorySpillSelect.Layout}
    (hbuild : buildLayout base selected policyBody = some layout)
    (hcheck : layoutCheck base reserved selected layout = true)
    {callee : Frame} (hcallee : callee ∈ frames policyBody)
    {name : Ident} {slot : Nat}
    (hslot : slotFor? layout.slots callee.owner name = some slot) :
    slot + 32 ≤ frameCutoff base layout
      (frameInfo selected ((frames policyBody).filterMap (·.owner)) callee) :=
  buildLayout_slotFor_end_le_frameCutoff hbuild hcheck hcallee hslot

/-- A direct callee's complete frame interval lies below every allocated
caller slot.  This is the caller/callee cutoff fact used to preserve the
caller's spilled locals across the call. -/
theorem calleeCutoff_le_callerSlot {selected : SpillSet}
    {policyBody : Block Op} {layout : MemorySpillSelect.Layout}
    (hbuild : buildLayout base selected policyBody = some layout)
    (hcheck : layoutCheck base reserved selected layout = true)
    {caller callee : Frame}
    (hcaller : caller ∈ frames policyBody)
    (hcallee : callee ∈ frames policyBody)
    {name : Ident} (howner : callee.owner = some name)
    (hcall : name ∈ frameCallsStmts caller.body)
    {callerName : Ident} {callerSlot : Nat}
    (hslot : slotFor? layout.slots caller.owner callerName = some callerSlot) :
    frameCutoff base layout
        (frameInfo selected ((frames policyBody).filterMap (·.owner)) callee) ≤
      callerSlot := by
  let callerInfo :=
    frameInfo selected ((frames policyBody).filterMap (·.owner)) caller
  let calleeInfo :=
    frameInfo selected ((frames policyBody).filterMap (·.owner)) callee
  have hdefined : name ∈ (frames policyBody).filterMap (·.owner) := by
    simp only [List.mem_filterMap]
    exact ⟨callee, hcallee, howner⟩
  have hedge : some name ∈ callerInfo.callees := by
    exact call_mem_callees_of_frame_mem hcaller hcall hdefined
  have hcallerInfo : callerInfo ∈ layout.infos :=
    buildLayout_frameInfo_mem hbuild hcaller
  have hcalleeInfo : calleeInfo ∈ layout.infos :=
    buildLayout_frameInfo_mem hbuild hcallee
  have hplaced : ({ owner := caller.owner, name := callerName }, callerSlot) ∈
      placeFrame base layout.cache callerInfo :=
    buildLayout_slot_in_frame hbuild hcheck hcaller rfl hslot
  apply layoutCheck_callee_cutoff_le_caller_slot hcheck hcallerInfo hcalleeInfo
  · simpa [calleeInfo, frameInfo, howner] using hedge
  · exact hplaced

/-- Named direct-call form of cached frame-need monotonicity.  Unlike
`calleeCutoff_le_callerSlot`, this remains useful for callers with no selected
local slot. -/
theorem calleeCutoff_le_callerCutoff {selected : SpillSet}
    {policyBody : Block Op} {layout : MemorySpillSelect.Layout}
    (hbuild : buildLayout base selected policyBody = some layout)
    (hcheck : layoutCheck base reserved selected layout = true)
    {caller callee : Frame}
    (hcaller : caller ∈ frames policyBody)
    (hcallee : callee ∈ frames policyBody)
    {name : Ident} (howner : callee.owner = some name)
    (hcall : name ∈ frameCallsStmts caller.body) :
    frameCutoff base layout
        (frameInfo selected ((frames policyBody).filterMap (·.owner)) callee) ≤
      frameCutoff base layout
        (frameInfo selected ((frames policyBody).filterMap (·.owner)) caller) := by
  let callerInfo :=
    frameInfo selected ((frames policyBody).filterMap (·.owner)) caller
  let calleeInfo :=
    frameInfo selected ((frames policyBody).filterMap (·.owner)) callee
  have hdefined : name ∈ (frames policyBody).filterMap (·.owner) := by
    simp only [List.mem_filterMap]
    exact ⟨callee, hcallee, howner⟩
  have hedge : some name ∈ callerInfo.callees :=
    call_mem_callees_of_frame_mem hcaller hcall hdefined
  have hcallerInfo : callerInfo ∈ layout.infos :=
    buildLayout_frameInfo_mem hbuild hcaller
  have hcalleeInfo : calleeInfo ∈ layout.infos :=
    buildLayout_frameInfo_mem hbuild hcallee
  apply layoutCheck_callee_cutoff_le_caller_cutoff hcheck hcallerInfo hcalleeInfo
  simpa [calleeInfo, frameInfo, howner] using hedge

theorem frameCutoff_le_reserved {selected : SpillSet}
    {policyBody : Block Op} {layout : MemorySpillSelect.Layout}
    (hbuild : buildLayout base selected policyBody = some layout)
    (hcheck : layoutCheck base reserved selected layout = true)
    (hreserved : reserved = base + 32 * layout.words)
    {frame : Frame} (hframe : frame ∈ frames policyBody) :
    frameCutoff base layout
      (frameInfo selected ((frames policyBody).filterMap (·.owner)) frame) ≤
        reserved := by
  have hinfo := buildLayout_frameInfo_mem hbuild hframe
  have hneed := layoutCheck_frame_need_le_words hcheck hinfo
  simp only [frameCutoff]
  omega

/-! ## Generated callee-body closure -/

private theorem hoist_append (left right : Block Op) :
    hoist D (left ++ right) = hoist D left ++ hoist D right := by
  simp [hoist]

private theorem hoist_initParams (slots : SlotMap) (owner : Owner) :
    ∀ params, hoist D (initParams slots owner params) = [] := by
  intro params
  induction params with
  | nil => rfl
  | cons name rest ih =>
      cases hslot : slotFor? slots owner name with
      | none =>
          have heq : initParams slots owner (name :: rest) =
              initParams slots owner rest := by simp [initParams, hslot]
          rw [heq]
          exact ih
      | some slot =>
          have heq : initParams slots owner (name :: rest) =
              MemorySpill.store slot (.var name) :: initParams slots owner rest := by
            simp [initParams, hslot]
          rw [heq]
          simpa [hoist, MemorySpill.store] using ih

private theorem hoist_initReturns (slots : SlotMap) (owner : Owner) :
    ∀ returns, hoist D (initReturns slots owner returns) = [] := by
  intro returns
  induction returns with
  | nil => rfl
  | cons name rest ih =>
      cases hslot : slotFor? slots owner name with
      | none =>
          have heq : initReturns slots owner (name :: rest) =
              initReturns slots owner rest := by simp [initReturns, hslot]
          rw [heq]
          exact ih
      | some slot =>
          have heq : initReturns slots owner (name :: rest) =
              MemorySpill.store slot (MemorySpill.word 0) ::
                initReturns slots owner rest := by
            simp [initReturns, hslot]
          rw [heq]
          simpa [hoist, MemorySpill.store] using ih

private theorem hoist_copyBackReturns (slots : SlotMap) (owner : Owner) :
    ∀ returns, hoist D (copyBackReturns slots owner returns) = [] := by
  intro returns
  induction returns with
  | nil => rfl
  | cons name rest ih =>
      cases hslot : slotFor? slots owner name with
      | none =>
          have heq : copyBackReturns slots owner (name :: rest) =
              copyBackReturns slots owner rest := by simp [copyBackReturns, hslot]
          rw [heq]
          exact ih
      | some slot =>
          have heq : copyBackReturns slots owner (name :: rest) =
              .assign [name] (MemorySpill.load slot) ::
                copyBackReturns slots owner rest := by
            simp [copyBackReturns, hslot]
          rw [heq]
          simpa [hoist] using ih

@[simp] theorem hoist_spillDecl_body (slots : SlotMap) (name : Ident)
    (decl : FDecl G) :
    hoist D (spillDecl slots name decl).body = [] := by
  simp only [spillDecl]
  repeat rw [hoist_append]
  rw [hoist_initParams, hoist_initReturns, hoist_copyBackReturns]
  rfl

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

/-- Assemble the generated outer function block on the normal path.  The
inner rewrite returns normally, so the trailing return copyback executes. -/
theorem closeSpillDeclBody_normal {slots : SlotMap} {name : Ident}
    {decl : FDecl G} {closure : FunEnv G}
    {entry afterEntry afterBody final : WordEnv}
    {entryState afterEntryState afterBodyState finalState : EvmState}
    (hentry : ExecStmts D (spillFuns slots ([] :: closure)) entry entryState
      (initParams slots (some name) decl.params ++
        initReturns slots (some name) decl.rets)
      afterEntry afterEntryState .normal)
    (hbody : ExecStmt D (spillFuns slots ([] :: closure))
      afterEntry afterEntryState
      (.block (rewriteStmts slots (some name)
        (copyBackReturns slots (some name) decl.rets) decl.body))
      afterBody afterBodyState .normal)
    (hcopies : ExecStmts D (spillFuns slots ([] :: closure))
      afterBody afterBodyState (copyBackReturns slots (some name) decl.rets)
      final finalState .normal) :
    ExecStmt D (spillFuns slots closure) entry entryState
      (.block (spillDecl slots name decl).body)
      (restore entry final) finalState .normal := by
  apply Step.block
  rw [hoist_spillDecl_body]
  simpa [spillDecl, spillFuns, spillScope] using
    execStmts_append_normal hentry (Step.seqCons hbody hcopies)

/-- Assemble a generated callee body when the rewritten inner body leaves.
The rewrite has already executed `exitCopies` at the leave site, and ordinary
statement sequencing correctly skips the trailing copyback. -/
theorem closeSpillDeclBody_leave {slots : SlotMap} {name : Ident}
    {decl : FDecl G} {closure : FunEnv G}
    {entry afterEntry afterBody : WordEnv}
    {entryState afterEntryState afterBodyState : EvmState}
    (hentry : ExecStmts D (spillFuns slots ([] :: closure)) entry entryState
      (initParams slots (some name) decl.params ++
        initReturns slots (some name) decl.rets)
      afterEntry afterEntryState .normal)
    (hbody : ExecStmt D (spillFuns slots ([] :: closure))
      afterEntry afterEntryState
      (.block (rewriteStmts slots (some name)
        (copyBackReturns slots (some name) decl.rets) decl.body))
      afterBody afterBodyState .leave) :
    ExecStmt D (spillFuns slots closure) entry entryState
      (.block (spillDecl slots name decl).body)
      (restore entry afterBody) afterBodyState .leave := by
  apply Step.block
  rw [hoist_spillDecl_body]
  simpa [spillDecl, spillFuns, spillScope] using
    execStmts_append_normal hentry
      (Step.seqStop (rest := copyBackReturns slots (some name) decl.rets)
        hbody (by decide))

/-- Assemble the halting generated callee body. -/
theorem closeSpillDeclBody_halt {slots : SlotMap} {name : Ident}
    {decl : FDecl G} {closure : FunEnv G}
    {entry afterEntry afterBody : WordEnv}
    {entryState afterEntryState afterBodyState : EvmState}
    (hentry : ExecStmts D (spillFuns slots ([] :: closure)) entry entryState
      (initParams slots (some name) decl.params ++
        initReturns slots (some name) decl.rets)
      afterEntry afterEntryState .normal)
    (hbody : ExecStmt D (spillFuns slots ([] :: closure))
      afterEntry afterEntryState
      (.block (rewriteStmts slots (some name)
        (copyBackReturns slots (some name) decl.rets) decl.body))
      afterBody afterBodyState .halt) :
    ExecStmt D (spillFuns slots closure) entry entryState
      (.block (spillDecl slots name decl).body)
      (restore entry afterBody) afterBodyState .halt := by
  apply Step.block
  rw [hoist_spillDecl_body]
  simpa [spillDecl, spillFuns, spillScope] using
    execStmts_append_normal hentry
      (Step.seqStop (rest := copyBackReturns slots (some name) decl.rets)
        hbody (by decide))

private theorem block_result_keys {funs : FunEnv G} {entry result : WordEnv}
    {entryState resultState : EvmState} {body : Block Op} {outcome : Outcome}
    (hbody : ExecStmt G funs entry entryState (.block body)
      result resultState outcome) :
    result.map Prod.fst = entry.map Prod.fst := by
  cases hbody with
  | block hstmts =>
      exact restore_keys (venvKeys_suffix hstmts rfl)
        (venvLen_mono hstmts rfl)

/-- A final frame relation retains every calling-convention cell, so the
outer generated block's `restore` is definitionally a no-op on that exact
callee environment. -/
theorem restore_callEnv_of_frameRel {slots : SlotMap} {owner : Owner}
    {signature : List Ident} {cuts : List CutMark}
    {entry sourceFinal targetFinal : WordEnv}
    {entryState sourceFinalState targetFinalState : EvmState}
    {sourceFuns : FunEnv G} {body : Block Op} {outcome : Outcome}
    (hentryKeys : entry.map Prod.fst = signature)
    (hbody : ExecStmt G sourceFuns entry entryState (.block body)
      sourceFinal sourceFinalState outcome)
    (hrel : ScopedFrameRel (base := base) (reserved := reserved)
      slots owner signature cuts sourceFinal sourceFinalState
      targetFinal targetFinalState) :
    @restore D entry targetFinal = targetFinal := by
  have hsourceKeys : sourceFinal.map Prod.fst = signature := by
    rw [block_result_keys hbody, hentryKeys]
  have htargetKeys := hrel.env.vars.keys
  have hfilter :
      (sourceFinal.map Prod.fst).filter
          (retainedBinding slots owner signature) =
        sourceFinal.map Prod.fst := by
    apply List.filter_eq_self.mpr
    intro item hitem
    have hsignature : item ∈ signature := by
      rw [← hsourceKeys]
      exact hitem
    unfold retainedBinding
    cases hslot : slotFor? slots owner item with
    | none => simp
    | some slot => simp [List.contains_eq_mem, hsignature]
  rw [hfilter] at htargetKeys
  have hlength : targetFinal.length = entry.length := by
    have := congrArg List.length htargetKeys
    have hsourceLength := congrArg List.length (block_result_keys hbody)
    simpa using this.trans hsourceLength
  simp [restore, hlength]

private theorem callEnv_keys {params returns : List Ident}
    {argvals : List U256} (hlength : argvals.length = params.length) :
    (callEnv params returns argvals).map Prod.fst = params ++ returns := by
  unfold callEnv
  rw [List.map_append, List.map_fst_zip (by omega)]
  congr 1
  rw [List.map_map]
  induction returns with
  | nil => rfl
  | cons name rest ih =>
      change name :: List.map (Prod.fst ∘ fun item => (item, (0 : U256))) rest =
        name :: rest
      rw [ih]

private theorem target_zero :
    Dialect.zero (evmWithExternal calls creates) = (0 : U256) := by
  change litValue (.number 0) = (0 : U256)
  decide

private theorem guarded_zero :
    Dialect.zero (guardedEvm calls creates base reserved) = (0 : U256) := by
  change litValue (.number 0) = (0 : U256)
  decide

private theorem returnValues_eq {returns : List Ident}
    {source target : WordEnv} (hsynced : ReturnsSynced returns source target) :
    returns.map (fun name =>
        ((@VEnv.get D target name).getD (Dialect.zero D))) =
      returns.map (fun name => (envGet source name).getD (0 : U256)) := by
  apply List.map_congr_left
  intro name hname
  rw [target_zero]
  change (envGet target name).getD 0 = (envGet source name).getD 0
  rw [← hsynced name hname]

/-! ## Closing semantic call rules -/

/-- Normal body premise plus the mechanical entry/copyback shells reconstruct
an exact target `callOk`.  The resulting value vector is definitionally the
source callee's return vector; the state retains both the scratch relation and
the caller-selected high-memory cutoff. -/
theorem closeCallOk_normal {slots : SlotMap} {name : Ident}
    {decl : FDecl G} {callerFuns closure : FunEnv G}
    {target : WordEnv} {targetState : EvmState}
    {targetArgs : List (Expr Op)} {argvals : List U256}
    {sourceArgState targetArgState sourceFinalState : EvmState}
    {sourceFinal afterBody : WordEnv}
    {afterEntryState afterBodyState : EvmState}
    {cuts : List CutMark} {cutoff : Nat}
    (hlookup : lookupFun callerFuns name = some (decl, closure))
    (hlength : argvals.length = decl.params.length)
    (hargs : EvalArgs D (spillFuns slots callerFuns) target targetState
      targetArgs (.vals argvals targetArgState))
    (hsourceBody : ExecStmt G closure
      (callEnv decl.params decl.rets argvals) sourceArgState
      (.block decl.body) sourceFinal sourceFinalState .normal)
    (hentry : ExecStmts D (spillFuns slots ([] :: closure))
      (callEnv decl.params decl.rets argvals) targetArgState
      (initParams slots (some name) decl.params ++
        initReturns slots (some name) decl.rets)
      (callEnv decl.params decl.rets argvals) afterEntryState .normal)
    (hbody : ExecStmt D (spillFuns slots ([] :: closure))
      (callEnv decl.params decl.rets argvals) afterEntryState
      (.block (rewriteStmts slots (some name)
        (copyBackReturns slots (some name) decl.rets) decl.body))
      afterBody afterBodyState .normal)
    (hbodyRel : ScopedFrameRel (base := base) (reserved := reserved)
      slots (some name) (decl.params ++ decl.rets) cuts sourceFinal sourceFinalState
      afterBody afterBodyState)
    (hreturns : ∀ ret ∈ decl.rets,
      ∃ value, envGet sourceFinal ret = some value)
    (hnodup : decl.rets.Nodup)
    (hbounds : ∀ localName slot,
      slotFor? slots (some name) localName = some slot →
        slot + 32 ≤ reserved)
    (hreserved : reserved < 2 ^ 256)
    (haboveEntry : AboveUnchanged cutoff reserved targetArgState afterEntryState)
    (haboveBody : AboveUnchanged cutoff reserved afterEntryState afterBodyState) :
    ∃ finalState,
      EvalExpr D (spillFuns slots callerFuns) target targetState
        (.call name targetArgs)
        (.vals (decl.rets.map (fun ret =>
          (envGet sourceFinal ret).getD (0 : U256))) finalState) ∧
      ScratchRel base reserved sourceFinalState finalState ∧
      AboveUnchanged cutoff reserved targetArgState finalState := by
  obtain ⟨final, finalState, hcopies, hfinalRel, hsynced, _, haboveCopies⟩ :=
    execCopyBackReturns hbodyRel hnodup (by
      intro ret hret
      exact List.mem_append_right _ hret) hreturns hbounds hreserved
  have htargetBody := closeSpillDeclBody_normal hentry hbody hcopies
  have hrestore : @restore D (callEnv decl.params decl.rets argvals) final = final :=
    restore_callEnv_of_frameRel (callEnv_keys hlength) hsourceBody hfinalRel
  rw [hrestore] at htargetBody
  have htargetCall := Step.callOk hargs (spillFuns_lookup_some slots hlookup)
    hlength (by
      simpa [spillDecl, callEnv, bindZeros, target_zero] using htargetBody)
    (Or.inl rfl)
  have htargetCall' :
      EvalExpr D (spillFuns slots callerFuns) target targetState
        (.call name targetArgs)
        (.vals (decl.rets.map (fun ret =>
          (@VEnv.get D final ret).getD (Dialect.zero D))) finalState) := by
    simpa only [spillDecl] using htargetCall
  have hvalues := returnValues_eq (calls := calls) (creates := creates) hsynced
  rw [hvalues] at htargetCall'
  refine ⟨finalState, ?_, hfinalRel.scratch, ?_⟩
  · simpa [guarded_zero] using htargetCall'
  · exact (haboveEntry.trans haboveBody).trans (haboveCopies cutoff)

/-- `leave` is the second successful call path.  Its rewritten site has
already copied return slots before producing `leave`, so no trailing copyback
is executed. -/
theorem closeCallOk_leave {slots : SlotMap} {name : Ident}
    {decl : FDecl G} {callerFuns closure : FunEnv G}
    {target : WordEnv} {targetState : EvmState}
    {targetArgs : List (Expr Op)} {argvals : List U256}
    {sourceArgState targetArgState sourceFinalState : EvmState}
    {sourceFinal afterBody : WordEnv}
    {afterEntryState afterBodyState : EvmState}
    {cuts : List CutMark} {cutoff : Nat}
    (hlookup : lookupFun callerFuns name = some (decl, closure))
    (hlength : argvals.length = decl.params.length)
    (hargs : EvalArgs D (spillFuns slots callerFuns) target targetState
      targetArgs (.vals argvals targetArgState))
    (hsourceBody : ExecStmt G closure
      (callEnv decl.params decl.rets argvals) sourceArgState
      (.block decl.body) sourceFinal sourceFinalState .leave)
    (hentry : ExecStmts D (spillFuns slots ([] :: closure))
      (callEnv decl.params decl.rets argvals) targetArgState
      (initParams slots (some name) decl.params ++
        initReturns slots (some name) decl.rets)
      (callEnv decl.params decl.rets argvals) afterEntryState .normal)
    (hbody : ExecStmt D (spillFuns slots ([] :: closure))
      (callEnv decl.params decl.rets argvals) afterEntryState
      (.block (rewriteStmts slots (some name)
        (copyBackReturns slots (some name) decl.rets) decl.body))
      afterBody afterBodyState .leave)
    (hbodyRel : ScopedFrameRel (base := base) (reserved := reserved)
      slots (some name) (decl.params ++ decl.rets) cuts sourceFinal sourceFinalState
      afterBody afterBodyState)
    (hsynced : ReturnsSynced decl.rets sourceFinal afterBody)
    (haboveEntry : AboveUnchanged cutoff reserved targetArgState afterEntryState)
    (haboveBody : AboveUnchanged cutoff reserved afterEntryState afterBodyState) :
    EvalExpr D (spillFuns slots callerFuns) target targetState
        (.call name targetArgs)
        (.vals (decl.rets.map (fun ret =>
          (envGet sourceFinal ret).getD (0 : U256))) afterBodyState) ∧
      ScratchRel base reserved sourceFinalState afterBodyState ∧
      AboveUnchanged cutoff reserved targetArgState afterBodyState := by
  have htargetBody := closeSpillDeclBody_leave hentry hbody
  have hrestore : @restore D (callEnv decl.params decl.rets argvals) afterBody =
      afterBody :=
    restore_callEnv_of_frameRel (callEnv_keys hlength) hsourceBody hbodyRel
  rw [hrestore] at htargetBody
  have htargetCall := Step.callOk hargs (spillFuns_lookup_some slots hlookup)
    hlength (by
      simpa [spillDecl, callEnv, bindZeros, target_zero] using htargetBody)
    (Or.inr rfl)
  have htargetCall' :
      EvalExpr D (spillFuns slots callerFuns) target targetState
        (.call name targetArgs)
        (.vals (decl.rets.map (fun ret =>
          (@VEnv.get D afterBody ret).getD (Dialect.zero D))) afterBodyState) := by
    simpa only [spillDecl] using htargetCall
  have hvalues := returnValues_eq (calls := calls) (creates := creates) hsynced
  rw [hvalues] at htargetCall'
  exact ⟨by
      simpa [guarded_zero] using htargetCall',
    hbodyRel.scratch, haboveEntry.trans haboveBody⟩

/-- Halting bodies reconstruct `callHalt`; no return synchronization premise is
needed, but scratch and caller-high-memory preservation remain exact. -/
theorem closeCallHalt {slots : SlotMap} {name : Ident}
    {decl : FDecl G} {callerFuns closure : FunEnv G}
    {target : WordEnv} {targetState : EvmState}
    {targetArgs : List (Expr Op)} {argvals : List U256}
    {sourceArgState targetArgState sourceFinalState : EvmState}
    {sourceFinal afterBody : WordEnv}
    {afterEntryState afterBodyState : EvmState}
    {cuts : List CutMark} {cutoff : Nat}
    (hlookup : lookupFun callerFuns name = some (decl, closure))
    (hlength : argvals.length = decl.params.length)
    (hargs : EvalArgs D (spillFuns slots callerFuns) target targetState
      targetArgs (.vals argvals targetArgState))
    (hsourceBody : ExecStmt G closure
      (callEnv decl.params decl.rets argvals) sourceArgState
      (.block decl.body) sourceFinal sourceFinalState .halt)
    (hentry : ExecStmts D (spillFuns slots ([] :: closure))
      (callEnv decl.params decl.rets argvals) targetArgState
      (initParams slots (some name) decl.params ++
        initReturns slots (some name) decl.rets)
      (callEnv decl.params decl.rets argvals) afterEntryState .normal)
    (hbody : ExecStmt D (spillFuns slots ([] :: closure))
      (callEnv decl.params decl.rets argvals) afterEntryState
      (.block (rewriteStmts slots (some name)
        (copyBackReturns slots (some name) decl.rets) decl.body))
      afterBody afterBodyState .halt)
    (hbodyRel : ScopedFrameRel (base := base) (reserved := reserved)
      slots (some name) (decl.params ++ decl.rets) cuts sourceFinal sourceFinalState
      afterBody afterBodyState)
    (haboveEntry : AboveUnchanged cutoff reserved targetArgState afterEntryState)
    (haboveBody : AboveUnchanged cutoff reserved afterEntryState afterBodyState) :
    EvalExpr D (spillFuns slots callerFuns) target targetState
        (.call name targetArgs) (.halt afterBodyState) ∧
      ScratchRel base reserved sourceFinalState afterBodyState ∧
      AboveUnchanged cutoff reserved targetArgState afterBodyState := by
  have htargetBody := closeSpillDeclBody_halt hentry hbody
  have hrestore : @restore D (callEnv decl.params decl.rets argvals) afterBody =
      afterBody :=
    restore_callEnv_of_frameRel (callEnv_keys hlength) hsourceBody hbodyRel
  rw [hrestore] at htargetBody
  have htargetCall := Step.callHalt hargs (spillFuns_lookup_some slots hlookup)
    hlength (by
      simpa [spillDecl, callEnv, bindZeros, target_zero] using htargetBody)
  exact ⟨by simpa [spillDecl] using htargetCall,
    hbodyRel.scratch, haboveEntry.trans haboveBody⟩

/-- Argument-list halting never enters a callee frame; the existing caller
relations therefore pass through unchanged. -/
theorem closeCallArgsHalt {slots : SlotMap} {name : Ident}
    {callerFuns : FunEnv G} {target : WordEnv}
    {targetState haltedState : EvmState} {targetArgs : List (Expr Op)}
    (hargs : EvalArgs D (spillFuns slots callerFuns) target targetState
      targetArgs (.halt haltedState)) :
    EvalExpr D (spillFuns slots callerFuns) target targetState
      (.call name targetArgs) (.halt haltedState) :=
  Step.callArgsHalt hargs

end YulEvmCompiler.Optimizer.MemorySpillCallSound
