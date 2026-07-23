import YulEvmCompiler.Optimizer.Implementation.MemorySpillCallSound
import YulEvmCompiler.Optimizer.Implementation.MemorySpillTraceResolveSound
set_option warningAsError true
set_option maxHeartbeats 800000
/-!
# Full expression simulation for memory spilling

This module extends the call-free expression layer with user calls, without
depending on the statement/control-flow simulation.  The only recursive
statement obligation is exposed as `CalleeBodySim`: a caller supplies a
simulation of the strictly smaller callee-body derivation.  This breaks the
otherwise circular expression/statement dependency while retaining the exact
entry and call-closing shells proved in `MemorySpillCallSound`.
-/

namespace YulEvmCompiler.Optimizer.MemorySpillExprCallSound

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer
open MemorySpillSelect
open MemorySpillStateSound
open MemorySpillRewriteSound
open MemorySpillFrameSound
open MemorySpillOriginSound
open MemorySpillCallSound
open MemorySpillTraceResolveSound

variable {base reserved : Nat}
variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "G" => guardedEvm calls creates base reserved
local notation "D" => evmWithExternal calls creates

/-! ## Static call origin and cutoff budget -/

def ExprCallsFrom (frame : Frame) (expression : Expr Op) : Prop :=
  ∀ name, name ∈ callsExpr expression → name ∈ frameCallsStmts frame.body

def ArgsCallsFrom (frame : Frame) (args : List (Expr Op)) : Prop :=
  ∀ name, name ∈ callsArgs args → name ∈ frameCallsStmts frame.body

def ExprCutoffCovers (policyRoot : Block Op)
    (selected : SpillSet) (layout : MemorySpillSelect.Layout)
    (cutoff : Nat) (expression : Expr Op) : Prop :=
  ∀ name policyCallee,
    name ∈ callsExpr expression →
    policyCallee ∈ frames policyRoot →
    policyCallee.owner = some name →
    frameCutoff base layout
      (frameInfo selected ((frames policyRoot).filterMap (·.owner)) policyCallee) ≤ cutoff

def ArgsCutoffCovers (policyRoot : Block Op)
    (selected : SpillSet) (layout : MemorySpillSelect.Layout)
    (cutoff : Nat) (args : List (Expr Op)) : Prop :=
  ∀ name policyCallee,
    name ∈ callsArgs args →
    policyCallee ∈ frames policyRoot →
    policyCallee.owner = some name →
    frameCutoff base layout
      (frameInfo selected ((frames policyRoot).filterMap (·.owner)) policyCallee) ≤ cutoff

/-! ## Statement callback -/

def CallShellFacts (returns : List Ident) (sourceFinal targetFinal : WordEnv) :
    Outcome → Prop
  | .normal => ∀ ret ∈ returns, ∃ value, envGet sourceFinal ret = some value
  | .leave => ReturnsSynced returns sourceFinal targetFinal
  | .break | .continue | .halt => True

/-- Result supplied by the recursive statement proof for one callee body.
The target judgment is exactly the premise consumed by the three call-closing
lemmas in `MemorySpillCallSound`. -/
structure CalleeBodyResult (selected : SpillSet)
    (layout : MemorySpillSelect.Layout) (policyCallee : Frame)
    (name : Ident) (decl : FDecl G) (closure : FunEnv G) (argvals : List U256)
    (sourceFinal : WordEnv) (sourceFinalState : EvmState) (outcome : Outcome)
    (afterEntryState : EvmState) (cutoff : Nat) where
  targetFinal : WordEnv
  targetFinalState : EvmState
  cuts : List CutMark
  body : ExecStmt D (spillFuns layout.slots ([] :: closure))
    (callEnv decl.params decl.rets argvals) afterEntryState
    (.block (rewriteStmts layout.slots (some name)
      (copyBackReturns layout.slots (some name) decl.rets)
      decl.body)) targetFinal targetFinalState outcome
  rel : ScopedFrameRel (base := base) (reserved := reserved)
    layout.slots policyCallee.owner (decl.params ++ decl.rets) cuts
    sourceFinal sourceFinalState targetFinal targetFinalState
  above : AboveUnchanged cutoff reserved afterEntryState targetFinalState
  shell : CallShellFacts decl.rets sourceFinal targetFinal outcome

/-- Non-circular callback for one exact callee-body judgment. -/
def CalleeBodySimFor (mode : OriginMode) (policyRoot : Block Op)
    (selected : SpillSet) (layout : MemorySpillSelect.Layout)
    (name : Ident) (decl : FDecl G) (closure : FunEnv G)
    (argvals : List U256) (sourceArgState : EvmState)
    (sourceFinal : WordEnv) (sourceFinalState : EvmState)
    (outcome : Outcome) : Prop :=
  ∀ {policyCallee : Frame} {afterEntryState : EvmState} {cutoff : Nat},
    FunsCovered G (fun body => body) ((frames policyRoot).map mode.execFrame)
      closure →
    policyCallee ∈ frames policyRoot →
    mode.execFrame policyCallee = calleeFrame name decl →
    LiveFrameRel (base := base) (reserved := reserved) selected layout
      policyCallee (decl.params ++ decl.rets) []
      (frameInitialLive selected policyCallee)
      (callEnv decl.params decl.rets argvals) sourceArgState
      (callEnv decl.params decl.rets argvals) afterEntryState →
    frameCutoff base layout
      (frameInfo selected ((frames policyRoot).filterMap (·.owner)) policyCallee) ≤ cutoff →
    Nonempty (CalleeBodyResult (base := base) (reserved := reserved)
      selected layout policyCallee name decl closure argvals sourceFinal
      sourceFinalState outcome afterEntryState cutoff)

/- Exact-judgment evidence consumed by the indexed simulator below.
At a call it stores a callback only for that constructor's body premise. -/
mutual
  inductive ExprBodyEvidence (mode : OriginMode) (policyRoot : Block Op)
      (selected : SpillSet) (layout : MemorySpillSelect.Layout) :
      ∀ {funs source state expression result},
        EvalExpr G funs source state expression result → Prop
    | lit : ExprBodyEvidence mode policyRoot selected layout Step.lit
    | var {hget : envGet source name = some value} :
        ExprBodyEvidence mode policyRoot selected layout (Step.var hget)
    | builtinOk {hargs : EvalArgs G funs source state args (.vals argvals state')}
        {hbuiltin : (guardedEvm calls creates base reserved).Builtin
          op argvals state' (.ok values finalState)} :
        ArgsBodyEvidence mode policyRoot selected layout hargs →
        ExprBodyEvidence mode policyRoot selected layout
          (Step.builtinOk hargs hbuiltin)
    | builtinHalt
        {hargs : EvalArgs G funs source state args (.vals argvals state')}
        {hbuiltin : (guardedEvm calls creates base reserved).Builtin
          op argvals state' (.halt finalState)} :
        ArgsBodyEvidence mode policyRoot selected layout hargs →
        ExprBodyEvidence mode policyRoot selected layout
          (Step.builtinHalt hargs hbuiltin)
    | builtinArgsHalt
        {hargs : EvalArgs G funs source state args (.halt finalState)} :
        ArgsBodyEvidence mode policyRoot selected layout hargs →
        ExprBodyEvidence mode policyRoot selected layout
          (Step.builtinArgsHalt hargs)
    | callOk
        {name : Ident} {decl : FDecl G} {closure : FunEnv G}
        {hargs : EvalArgs G funs source state args (.vals argvals argState)}
        {hlookup : lookupFun funs name = some (decl, closure)}
        {hlength : argvals.length = decl.params.length}
        {hbody : ExecStmt G closure
          (decl.params.zip argvals ++ bindZeros G decl.rets) argState
          (.block decl.body) sourceFinal sourceFinalState outcome}
        {houtcome : outcome = .normal ∨ outcome = .leave} :
        ArgsBodyEvidence mode policyRoot selected layout hargs →
        CalleeBodySimFor (base := base) (reserved := reserved) mode policyRoot
          selected layout name decl closure argvals argState sourceFinal
          sourceFinalState outcome →
        ExprBodyEvidence mode policyRoot selected layout
          (Step.callOk (fn := name) hargs hlookup hlength hbody houtcome)
    | callHalt
        {name : Ident} {decl : FDecl G} {closure : FunEnv G}
        {hargs : EvalArgs G funs source state args (.vals argvals argState)}
        {hlookup : lookupFun funs name = some (decl, closure)}
        {hlength : argvals.length = decl.params.length}
        {hbody : ExecStmt G closure
          (decl.params.zip argvals ++ bindZeros G decl.rets) argState
          (.block decl.body) sourceFinal sourceFinalState .halt} :
        ArgsBodyEvidence mode policyRoot selected layout hargs →
        CalleeBodySimFor (base := base) (reserved := reserved) mode policyRoot
          selected layout name decl closure argvals argState sourceFinal
          sourceFinalState .halt →
        ExprBodyEvidence mode policyRoot selected layout
          (Step.callHalt (fn := name) hargs hlookup hlength hbody)
    | callArgsHalt
        {hargs : EvalArgs G funs source state args (.halt finalState)} :
        ArgsBodyEvidence mode policyRoot selected layout hargs →
        ExprBodyEvidence mode policyRoot selected layout
          (Step.callArgsHalt hargs)

  inductive ArgsBodyEvidence (mode : OriginMode) (policyRoot : Block Op)
      (selected : SpillSet) (layout : MemorySpillSelect.Layout) :
      ∀ {funs source state args result}, EvalArgs G funs source state args result → Prop
    | nil : ArgsBodyEvidence mode policyRoot selected layout Step.argsNil
    | cons
        {hrest : EvalArgs G funs source state rest (.vals restValues restState)}
        {hhead : EvalExpr G funs source restState expression
          (.vals [value] finalState)} :
        ArgsBodyEvidence mode policyRoot selected layout hrest →
        ExprBodyEvidence mode policyRoot selected layout hhead →
        ArgsBodyEvidence mode policyRoot selected layout
          (Step.argsCons hrest hhead)
    | restHalt {hrest : EvalArgs G funs source state rest (.halt finalState)} :
        ArgsBodyEvidence mode policyRoot selected layout hrest →
        ArgsBodyEvidence mode policyRoot selected layout
          (Step.argsRestHalt hrest)
    | headHalt
        {hrest : EvalArgs G funs source state rest (.vals restValues restState)}
        {hhead : EvalExpr G funs source restState expression (.halt finalState)} :
        ArgsBodyEvidence mode policyRoot selected layout hrest →
        ExprBodyEvidence mode policyRoot selected layout hhead →
        ArgsBodyEvidence mode policyRoot selected layout
          (Step.argsHeadHalt hrest hhead)
end

theorem ExprBodyEvidence.cast
    {mode : OriginMode} {policyRoot : Block Op} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout}
    {h₁ h₂ : EvalExpr G funs source state expression result}
    (hevidence : ExprBodyEvidence (base := base) (reserved := reserved)
      mode policyRoot selected layout h₁) :
    ExprBodyEvidence (base := base) (reserved := reserved)
      mode policyRoot selected layout h₂ := by
  have heq : h₁ = h₂ := Subsingleton.elim _ _
  subst h₂
  exact hevidence

theorem ArgsBodyEvidence.cast
    {mode : OriginMode} {policyRoot : Block Op} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout}
    {h₁ h₂ : EvalArgs G funs source state args result}
    (hevidence : ArgsBodyEvidence (base := base) (reserved := reserved)
      mode policyRoot selected layout h₁) :
    ArgsBodyEvidence (base := base) (reserved := reserved)
      mode policyRoot selected layout h₂ := by
  have heq : h₁ = h₂ := Subsingleton.elim _ _
  subst h₂
  exact hevidence

/-! ## Mode-aware entry and caller preservation -/

theorem enterPolicyCallee {selected : SpillSet} {policyRoot : Block Op}
    {layout : MemorySpillSelect.Layout} {policyCallee : Frame}
    {name : Ident} {decl : FDecl G} {closure : FunEnv G}
    {argvals : List U256} {sourceState targetState : EvmState}
    (hbuild : buildLayout base selected policyRoot = some layout)
    (hcheck : layoutCheck base reserved selected layout = true)
    (hframe : policyCallee ∈ frames policyRoot)
    (howner : policyCallee.owner = some name)
    (hparams : policyCallee.params = decl.params)
    (hreturns : policyCallee.returns = decl.rets)
    (hlength : argvals.length = decl.params.length)
    (hnodup : (decl.params ++ decl.rets).Nodup)
    (hscratch : ScratchRel base reserved sourceState targetState)
    (hreserved : reserved < 2 ^ 256) (cutoff : Nat)
    (hcutoff : ∀ localName slot,
      slotFor? layout.slots policyCallee.owner localName = some slot →
        slot + 32 ≤ cutoff) :
    let entry := callEnv decl.params decl.rets argvals
    let afterParams := afterInitParams layout.slots policyCallee.owner entry
      policyCallee.params targetState
    let afterEntry := afterInitReturns layout.slots policyCallee.owner
      policyCallee.returns afterParams
    ExecStmts D (spillFuns layout.slots ([] :: closure)) entry targetState
      (initParams layout.slots (some name) decl.params ++
        initReturns layout.slots (some name) decl.rets)
      entry afterEntry .normal ∧
    LiveFrameRel (base := base) (reserved := reserved) selected layout
      policyCallee (decl.params ++ decl.rets) []
      (frameInitialLive selected policyCallee)
      entry sourceState entry afterEntry ∧
    AboveUnchanged cutoff reserved targetState afterEntry := by
  dsimp only
  rw [howner] at hcutoff ⊢
  rw [hparams, hreturns]
  have hfacts := callEntryFacts hlength hnodup
  have hentry := callEntryRel (params := decl.params) (returns := decl.rets)
    (argvals := argvals) layout.slots policyCallee.owner
    sourceState targetState hscratch
  have hentryPolicy : EntryFrameRel (base := base) (reserved := reserved)
      layout.slots policyCallee.owner
      (policyCallee.params ++ policyCallee.returns)
      (callEnv decl.params decl.rets argvals) sourceState
      (callEnv decl.params decl.rets argvals) targetState := by
    simpa [hparams, hreturns] using hentry
  have hcutoffPolicy : ∀ localName slot,
      slotFor? layout.slots policyCallee.owner localName = some slot →
        slot + 32 ≤ cutoff := by
    simpa [howner] using hcutoff
  have hresult := execEntryPrologue_live (calls := calls) (creates := creates)
    (sourceFuns := [] :: closure) hbuild hcheck hframe hentryPolicy
    (by simpa [hparams] using hfacts.bound)
    (by simpa [hparams, hreturns] using hnodup)
    (by simpa [hparams] using hfacts.synced)
    (by simpa [hreturns] using hfacts.zero)
    (by simpa [hparams, hreturns] using hfacts.names)
    hreserved cutoff hcutoffPolicy
  simpa [howner, hparams, hreturns] using hresult

theorem slotsLoaded_preserveAbove {slots : SlotMap} {owner : Owner}
    {source : WordEnv} {before after : EvmState} {cutoff : Nat}
    (hloaded : SlotsLoaded slots owner source before)
    (hslotCutoff : ∀ name slot,
      slotFor? slots owner name = some slot → cutoff ≤ slot)
    (hslotReserved : ∀ name slot,
      slotFor? slots owner name = some slot → slot + 32 ≤ reserved)
    (habove : AboveUnchanged cutoff reserved before after) :
    SlotsLoaded slots owner source after := by
  intro name slot value hslot hget
  have hread : readBytes after.memory slot 32 =
      readBytes before.memory slot 32 := by
    unfold readBytes
    apply List.map_congr_left
    intro index hindex
    have hi : index < 32 := by simpa using hindex
    apply habove
    · have := hslotCutoff name slot hslot
      omega
    · have := hslotReserved name slot hslot
      omega
  have hform (memory : Nat → UInt8) :
      loadWord memory slot = (readBytes memory slot 32).foldl
        (fun (acc : U256) byte =>
          (acc <<< (8 : Nat)) ||| BitVec.ofNat 256 byte.toNat) 0 := by
    unfold loadWord readBytes
    rw [List.foldl_map]
  have hold := hloaded name slot value hslot hget
  rw [hform before.memory] at hold
  rw [hform after.memory, hread]
  exact hold

theorem liveFrameRel_afterCall {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {source target : WordEnv}
    {sourceState targetState sourceState' targetState' : EvmState}
    {cutoff : Nat}
    (hrel : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (hscratch : ScratchRel base reserved sourceState' targetState')
    (hslotCutoff : ∀ name slot,
      slotFor? layout.slots frame.owner name = some slot → cutoff ≤ slot)
    (hslotReserved : ∀ name slot,
      slotFor? layout.slots frame.owner name = some slot → slot + 32 ≤ reserved)
    (habove : AboveUnchanged cutoff reserved targetState targetState') :
    LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState' target targetState' := by
  exact {
    frameRel := {
      env := hrel.frameRel.env
      loaded := slotsLoaded_preserveAbove hrel.frameRel.loaded hslotCutoff
        hslotReserved habove
      scratch := hscratch }
    bound := hrel.bound
    certified := hrel.certified }


end YulEvmCompiler.Optimizer.MemorySpillExprCallSound
