import YulEvmCompiler.Optimizer.Implementation.MemorySpillControlSound
import YulEvmCompiler.Optimizer.Implementation.MemorySpillExprCallSound
import YulEvmCompiler.Optimizer.Implementation.MemorySpillExitSound
import YulEvmCompiler.Optimizer.Implementation.MemorySpillObjectSound
import YulEvmCompiler.Optimizer.Implementation.StackLayoutSound
set_option warningAsError true
set_option maxHeartbeats 1600000
/-!
# Structural big-step simulation for memory spilling

This module closes the syntax-directed part of the spilling proof.  The
induction is over the concrete guarded `Step` derivation, including the body
premise of every user call.  In particular, function calls do not rely on a
universal semantic callback: their body simulation is the induction
hypothesis for that exact premise.
-/

namespace YulEvmCompiler.Optimizer.MemorySpillStepSound

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open YulEvmCompiler.Optimizer
open MemorySpill
open MemorySpillSelect
open MemorySpillStateSound
open MemorySpillRewriteSound
open MemorySpillFrameSound
open MemorySpillOriginSound
open MemorySpillCallSound
open MemorySpillBindingSound
open MemorySpillTraceResolveSound
open MemorySpillExitSound
open MemorySpillControlSound
open MemorySpillExprCallSound

variable {base reserved : Nat}
variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "G" => guardedEvm calls creates base reserved
local notation "D" => evmWithExternal calls creates

/-- The result package produced by every branch of the `Step` induction. -/
def StepSimResult (globalDeclared : List Ident) (selected : SpillSet)
    (layout : MemorySpillSelect.Layout) (frame : Frame)
    (signature : List Ident) (cuts : List CutMark) (live : SpillSet)
    (exitNames : List Ident) (source target : WordEnv)
    (policyCode executedCode : Code Op) (sourceResult : Res G)
    (sourceFuns : FunEnv G) (targetState : EvmState)
    (exitCopies : Block Op) (cutoff : Nat) : Prop :=
  ∃ targetResult : Res D,
    Step D (spillFuns layout.slots sourceFuns) target targetState
        (rewriteCode layout.slots frame.owner exitCopies executedCode) targetResult ∧
      ResultControlRel (base := base) (reserved := reserved)
          globalDeclared selected layout frame signature cuts live exitNames
          source target policyCode sourceResult targetResult ∧
        ResAboveUnchanged cutoff reserved targetState targetResult

/-- Common allocator bounds used by expression and inserted-memory steps. -/
theorem SpillFacts.slotBounds {raw : Block Op} {result : Result}
    {guards : List Nat} (hfacts : SpillFacts raw result guards)
    {owner : Owner} {name : Ident} {slot : Nat}
    (hslot : slotFor? result.layout.slots owner name = some slot) :
    result.base ≤ slot ∧ slot + 32 ≤ result.reserved :=
  layoutCheck_slotFor_bounds hfacts.layout_check hslot

/-- Every current-frame cutoff is above the global scratch base. -/
theorem frameCutoff_base_le (base : Nat) (layout : MemorySpillSelect.Layout)
    (info : FrameInfo) : base ≤ frameCutoff base layout info := by
  unfold frameCutoff
  omega

/-- Invert the singleton sequence introduced by `rewriteCode` for statements. -/
theorem execStmt_of_singleton {funs : FunEnv D} {vars final : WordEnv}
    {state finalState : EvmState} {statement : Stmt Op} {outcome : Outcome}
    (hstep : ExecStmts D funs vars state [statement] final finalState outcome) :
    ExecStmt D funs vars state statement final finalState outcome := by
  cases hstep with
  | seqCons hstatement hrest =>
      cases hrest with
      | seqNil => exact hstatement
  | seqStop hstatement _ => exact hstatement

/-- Rewriting every switch branch commutes with deterministic case selection. -/
theorem rewrite_selectSwitch (slots : SlotMap) (owner : Owner)
    (exitCopies : Block Op) (value : U256)
    (cases : List (Literal × Block Op)) (dflt : Option (Block Op)) :
    selectSwitch D value (rewriteCases slots owner exitCopies cases)
        (dflt.map (rewriteStmts slots owner exitCopies)) =
      rewriteStmts slots owner exitCopies (selectSwitch G value cases dflt) := by
  induction cases with
  | nil => cases dflt <;> simp [selectSwitch, rewriteCases, rewriteStmts]
  | cons head rest ih =>
      rcases head with ⟨literal, body⟩
      by_cases h : decide (value = litValue literal) = true
      · simp [selectSwitch, rewriteCases, h]
      · simpa [selectSwitch, rewriteCases, h] using ih

/-- Strong motive for the single structural induction.  It is generalized
over the dynamic target environment and all lexical/call contexts, so the
induction hypothesis for a call's body premise can be instantiated at the
callee owner after its entry prologue. -/
def StepSimMotive {raw : Block Op} {result : Result} {guards : List Nat}
    (_hfacts : SpillFacts raw result guards)
    (_hexternals : GuardedExternals calls creates result.base result.reserved)
    (mode : OriginMode)
    {sourceFuns : FunEnv (guardedEvm calls creates result.base result.reserved)}
    {source sourceState executedCode sourceResult}
    (_hsource : Step (guardedEvm calls creates result.base result.reserved)
      sourceFuns source sourceState executedCode sourceResult) : Prop :=
  let policyRoot := resolveMemoryGuardStmts result.base result.reserved raw
  ∀ {policyFrame executedFrame : Frame} {live : SpillSet}
    {policyCode : Code Op} {exitNames : List Ident}
    {target : WordEnv} {targetState : EvmState} {cuts : List CutMark}
    {exitCopies : Block Op} {cutoff : Nat},
    ControlStepContext mode policyRoot result.selection policyFrame executedFrame live
        policyCode executedCode exitNames source →
      ControlLiveRel (base := result.base) (reserved := result.reserved)
        result.selection result.layout policyFrame
        (policyFrame.params ++ policyFrame.returns) cuts live
        source sourceState target targetState →
      FunsCovered (guardedEvm calls creates result.base result.reserved)
        (fun body => body) ((frames policyRoot).map mode.execFrame) sourceFuns →
      exitCopies = copyBackReturns result.layout.slots policyFrame.owner exitNames →
      frameCutoff result.base result.layout
          (frameInfo result.selection
            ((frames policyRoot).filterMap (·.owner)) policyFrame) ≤ cutoff →
      StepSimResult (base := result.base) (reserved := result.reserved)
        (MemorySpill.declaredStmts policyRoot) result.selection result.layout
        policyFrame (policyFrame.params ++ policyFrame.returns) cuts live exitNames
        source target policyCode executedCode sourceResult sourceFuns targetState
        exitCopies cutoff

/-! ## Leaf statement branches -/

theorem simulateCallFreeExprBranch
    {raw : Block Op} {result : Result} {guards : List Nat}
    (hfacts : SpillFacts raw result guards)
    (hexternals : GuardedExternals calls creates result.base result.reserved)
    {mode : OriginMode}
    {policyFrame executedFrame : Frame} {cuts : List CutMark}
    {live : SpillSet} {exitNames : List Ident}
    {policyExpr executedExpr : Expr Op} {sourceResult : EResult
      (guardedEvm calls creates result.base result.reserved)}
    {source target : WordEnv} {sourceState targetState : EvmState}
    {sourceFuns : FunEnv (guardedEvm calls creates result.base result.reserved)}
    {exitCopies : Block Op} {cutoff : Nat}
    (hctx : ControlStepContext mode
      (resolveMemoryGuardStmts result.base result.reserved raw)
      result.selection policyFrame executedFrame live
      (.expr policyExpr) (.expr executedExpr) exitNames source)
    (hsource : EvalExpr (guardedEvm calls creates result.base result.reserved)
      sourceFuns source sourceState executedExpr sourceResult)
    (hsyntax : SpillExpr executedExpr)
    (hrel : ControlLiveRel (base := result.base) (reserved := result.reserved)
      result.selection result.layout policyFrame
      (policyFrame.params ++ policyFrame.returns) cuts live
      source sourceState target targetState)
    (hcutoff : frameCutoff result.base result.layout
      (frameInfo result.selection
        ((frames (resolveMemoryGuardStmts result.base result.reserved raw)).filterMap
          (·.owner)) policyFrame) ≤ cutoff) :
    StepSimResult (base := result.base) (reserved := result.reserved)
      (MemorySpill.declaredStmts
        (resolveMemoryGuardStmts result.base result.reserved raw))
      result.selection result.layout policyFrame
      (policyFrame.params ++ policyFrame.returns) cuts live exitNames source target
      (.expr policyExpr) (.expr executedExpr) (.eres sourceResult) sourceFuns
      targetState exitCopies cutoff := by
  have hbaseCutoff : result.base ≤ cutoff :=
    le_trans (frameCutoff_base_le result.base result.layout _) hcutoff
  obtain ⟨targetResult, htarget, hresult, habove⟩ :=
    simulateCallFreeExpr hctx.motive hsource hsyntax hrel hctx.exitsBound
      hctx.exitsInSignature hexternals
      (fun _ _ hslot => layoutCheck_slotFor_bounds hfacts.layout_check hslot)
      hfacts.reserved_lt
      exitCopies cutoff hbaseCutoff
  exact ⟨.eres targetResult, htarget, hresult, habove⟩

theorem simulateCallFreeArgsBranch
    {raw : Block Op} {result : Result} {guards : List Nat}
    (hfacts : SpillFacts raw result guards)
    (hexternals : GuardedExternals calls creates result.base result.reserved)
    {mode : OriginMode}
    {policyFrame executedFrame : Frame} {cuts : List CutMark}
    {live : SpillSet} {exitNames : List Ident}
    {policyArgs executedArgs : List (Expr Op)} {sourceResult : EResult
      (guardedEvm calls creates result.base result.reserved)}
    {source target : WordEnv} {sourceState targetState : EvmState}
    {sourceFuns : FunEnv (guardedEvm calls creates result.base result.reserved)}
    {exitCopies : Block Op} {cutoff : Nat}
    (hctx : ControlStepContext mode
      (resolveMemoryGuardStmts result.base result.reserved raw)
      result.selection policyFrame executedFrame live
      (.args policyArgs) (.args executedArgs) exitNames source)
    (hsource : EvalArgs (guardedEvm calls creates result.base result.reserved)
      sourceFuns source sourceState executedArgs sourceResult)
    (hsyntax : SpillArgs executedArgs)
    (hrel : ControlLiveRel (base := result.base) (reserved := result.reserved)
      result.selection result.layout policyFrame
      (policyFrame.params ++ policyFrame.returns) cuts live
      source sourceState target targetState)
    (hcutoff : frameCutoff result.base result.layout
      (frameInfo result.selection
        ((frames (resolveMemoryGuardStmts result.base result.reserved raw)).filterMap
          (·.owner)) policyFrame) ≤ cutoff) :
    StepSimResult (base := result.base) (reserved := result.reserved)
      (MemorySpill.declaredStmts
        (resolveMemoryGuardStmts result.base result.reserved raw))
      result.selection result.layout policyFrame
      (policyFrame.params ++ policyFrame.returns) cuts live exitNames source target
      (.args policyArgs) (.args executedArgs) (.eres sourceResult) sourceFuns
      targetState exitCopies cutoff := by
  have hbaseCutoff : result.base ≤ cutoff :=
    le_trans (frameCutoff_base_le result.base result.layout _) hcutoff
  obtain ⟨targetResult, htarget, hresult, habove⟩ :=
    simulateCallFreeArgs hctx.motive hsource hsyntax hrel hctx.exitsBound
      hctx.exitsInSignature hexternals
      (fun _ _ hslot => layoutCheck_slotFor_bounds hfacts.layout_check hslot)
      hfacts.reserved_lt
      exitCopies cutoff hbaseCutoff
  exact ⟨.eres targetResult, htarget, hresult, habove⟩

/-- A call whose right-to-left argument evaluation halts never enters the
callee.  This closure is shared by the direct call branch of the main
induction and nested calls inside builtin arguments. -/
theorem closeCallArgsHaltBranch
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {policyName executedName : Ident}
    {policyArgs executedArgs : List (Expr Op)}
    {source target : WordEnv} {sourceFinalState targetState : EvmState}
    {sourceFuns : FunEnv G} {exitCopies : Block Op} {cutoff : Nat}
    (hargs : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.args policyArgs) (.args executedArgs)
      (.eres (.halt sourceFinalState)) sourceFuns targetState exitCopies cutoff) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.expr (.call policyName policyArgs))
      (.expr (.call executedName executedArgs))
      (.eres (.halt sourceFinalState)) sourceFuns targetState exitCopies cutoff := by
  obtain ⟨targetResult, htarget, hresult, habove⟩ := hargs
  cases targetResult with
  | sres targetFinal targetFinalState targetOutcome =>
      simp [ResultControlRel] at hresult
  | eres targetArgsResult =>
      cases targetArgsResult with
      | vals targetValues targetFinalState => simp [ResultControlRel] at hresult
      | halt targetFinalState =>
          rcases hresult with
            ⟨hcontrol, horigin, hexitBound, hexitSignature⟩
          refine ⟨.eres (.halt targetFinalState), ?_, ?_, habove⟩
          · simpa [rewriteCode, rewriteExpr] using
              (closeCallArgsHalt
                (slots := layout.slots) (name := executedName)
                (callerFuns := sourceFuns) (target := target)
                (targetState := targetState) (haltedState := targetFinalState)
                (targetArgs := rewriteArgs layout.slots frame.owner executedArgs)
                htarget)
          · exact ⟨hcontrol, horigin, hexitBound, hexitSignature⟩

/-- Close a successful user call after the callee-specific entry/body/copyback
shell has produced the exact target call judgment.  The only caller-specific
work left is preserving loaded spill cells above the callee cutoff. -/
theorem closeCallOkBranch
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {policyName executedName : Ident}
    {policyArgs executedArgs : List (Expr Op)} {argvals returnValues : List U256}
    {source target : WordEnv}
    {sourceArgState sourceFinalState targetState : EvmState}
    {sourceFuns : FunEnv G} {exitCopies : Block Op}
    {outerCutoff callCutoff : Nat}
    (hargs : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.args policyArgs) (.args executedArgs)
      (.eres (.vals argvals sourceArgState)) sourceFuns targetState
      exitCopies outerCutoff)
    (hclose : ∀ {targetArgState : EvmState},
      EvalArgs D (spillFuns layout.slots sourceFuns) target targetState
        (rewriteArgs layout.slots frame.owner executedArgs)
        (.vals argvals targetArgState) →
      ScratchRel base reserved sourceArgState targetArgState →
      ∃ targetFinalState,
        EvalExpr D (spillFuns layout.slots sourceFuns)
            target targetState (rewriteExpr layout.slots frame.owner
              (.call executedName executedArgs))
            (.vals returnValues targetFinalState) ∧
          ScratchRel base reserved sourceFinalState targetFinalState ∧
          AboveUnchanged callCutoff reserved targetArgState targetFinalState)
    (hslotCutoff : ∀ name slot,
      slotFor? layout.slots frame.owner name = some slot → callCutoff ≤ slot)
    (hslotReserved : ∀ name slot,
      slotFor? layout.slots frame.owner name = some slot → slot + 32 ≤ reserved)
    (hcallOuter : callCutoff ≤ outerCutoff) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.expr (.call policyName policyArgs))
      (.expr (.call executedName executedArgs))
      (.eres (.vals returnValues sourceFinalState)) sourceFuns targetState
      exitCopies outerCutoff := by
  obtain ⟨targetArgsResult, htargetArgs, hargsResult, haboveArgs⟩ := hargs
  cases targetArgsResult with
  | sres targetFinal targetFinalState' targetOutcome =>
      simp [ResultControlRel] at hargsResult
  | eres targetArgsResult' =>
      cases targetArgsResult' with
      | halt targetArgsState => simp [ResultControlRel] at hargsResult
      | vals targetArgvals targetArgsState =>
          rcases hargsResult with
            ⟨hvalues, hcontrol, horigin, hexitBound, hexitSignature⟩
          subst targetArgvals
          obtain ⟨targetFinalState, htargetCall, hscratch, hcallAbove⟩ :=
            hclose htargetArgs hcontrol.liveRel.frameRel.scratch
          have hcontrol' := hcontrol.afterCall hscratch hslotCutoff
            hslotReserved hcallAbove
          exact ⟨.eres (.vals returnValues targetFinalState), htargetCall,
            ⟨rfl, hcontrol', horigin, hexitBound, hexitSignature⟩,
            haboveArgs.trans (hcallAbove.mono hcallOuter)⟩

theorem closeCallHaltBranch
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {policyName executedName : Ident}
    {policyArgs executedArgs : List (Expr Op)} {argvals : List U256}
    {source target : WordEnv}
    {sourceArgState sourceFinalState targetState : EvmState}
    {sourceFuns : FunEnv G} {exitCopies : Block Op}
    {outerCutoff callCutoff : Nat}
    (hargs : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.args policyArgs) (.args executedArgs)
      (.eres (.vals argvals sourceArgState)) sourceFuns targetState
      exitCopies outerCutoff)
    (hclose : ∀ {targetArgState : EvmState},
      EvalArgs D (spillFuns layout.slots sourceFuns) target targetState
        (rewriteArgs layout.slots frame.owner executedArgs)
        (.vals argvals targetArgState) →
      ScratchRel base reserved sourceArgState targetArgState →
      ∃ targetFinalState,
        EvalExpr D (spillFuns layout.slots sourceFuns)
            target targetState (rewriteExpr layout.slots frame.owner
              (.call executedName executedArgs)) (.halt targetFinalState) ∧
          ScratchRel base reserved sourceFinalState targetFinalState ∧
          AboveUnchanged callCutoff reserved targetArgState targetFinalState)
    (hslotCutoff : ∀ name slot,
      slotFor? layout.slots frame.owner name = some slot → callCutoff ≤ slot)
    (hslotReserved : ∀ name slot,
      slotFor? layout.slots frame.owner name = some slot → slot + 32 ≤ reserved)
    (hcallOuter : callCutoff ≤ outerCutoff) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.expr (.call policyName policyArgs))
      (.expr (.call executedName executedArgs))
      (.eres (.halt sourceFinalState)) sourceFuns targetState
      exitCopies outerCutoff := by
  obtain ⟨targetArgsResult, htargetArgs, hargsResult, haboveArgs⟩ := hargs
  cases targetArgsResult with
  | sres targetFinal targetFinalState' targetOutcome =>
      simp [ResultControlRel] at hargsResult
  | eres targetArgsResult' =>
      cases targetArgsResult' with
      | halt targetArgsState => simp [ResultControlRel] at hargsResult
      | vals targetArgvals targetArgsState =>
          rcases hargsResult with
            ⟨hvalues, hcontrol, horigin, hexitBound, hexitSignature⟩
          subst targetArgvals
          obtain ⟨targetFinalState, htargetCall, hscratch, hcallAbove⟩ :=
            hclose htargetArgs hcontrol.liveRel.frameRel.scratch
          have hcontrol' := hcontrol.afterCall hscratch hslotCutoff
            hslotReserved hcallAbove
          exact ⟨.eres (.halt targetFinalState), htargetCall,
            ⟨hcontrol', horigin, hexitBound, hexitSignature⟩,
            haboveArgs.trans (hcallAbove.mono hcallOuter)⟩

/-! ## Exact callee-body adapters for the call-result shells -/

/-- Convert the ordinary block-statement induction result into the exact
callee-body package consumed by the call shells.  The only semantic transport
is insertion of the empty function scope introduced by the rewritten
declaration's prologue block. -/
theorem calleeBodyResult_of_stepSim
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {policyCallee : Frame}
    {name : Ident} {decl : FDecl G} {closure : FunEnv G}
    {argvals : List U256} {sourceFinal : WordEnv}
    {sourceFinalState afterEntryState : EvmState} {outcome : Outcome}
    {cuts : List CutMark} {live : SpillSet} {cutoff : Nat}
    (hbody : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout policyCallee
      (decl.params ++ decl.rets) cuts live decl.rets
      (callEnv decl.params decl.rets argvals)
      (callEnv decl.params decl.rets argvals)
      (.stmt (.block policyCallee.body)) (.stmt (.block decl.body))
      (.sres sourceFinal sourceFinalState outcome) closure afterEntryState
      (copyBackReturns layout.slots policyCallee.owner decl.rets) cutoff)
    (howner : policyCallee.owner = some name) :
    Nonempty (CalleeBodyResult (base := base) (reserved := reserved)
      selected layout policyCallee name decl closure argvals sourceFinal
      sourceFinalState outcome afterEntryState cutoff) := by
  obtain ⟨targetResult, htarget, hresult, habove⟩ := hbody
  cases targetResult with
  | eres targetExpressionResult => simp [ResultControlRel] at hresult
  | sres targetFinal targetFinalState targetOutcome =>
      rcases hresult with
        ⟨finalLive, houtcome, hcontrol, horigin, hexitBound,
          hexitSignature, hleave, hblock, hnormal⟩
      subst targetOutcome
      have htarget' : ExecStmts D (spillFuns layout.slots closure)
          (callEnv decl.params decl.rets argvals) afterEntryState
          [.block (rewriteStmts layout.slots (some name)
            (copyBackReturns layout.slots (some name) decl.rets) decl.body)]
          targetFinal targetFinalState outcome := by
        simpa [rewriteCode, rewriteStmt, howner] using htarget
      have htargetBlock : ExecStmt D (spillFuns layout.slots closure)
          (callEnv decl.params decl.rets argvals) afterEntryState
          (.block (rewriteStmts layout.slots (some name)
            (copyBackReturns layout.slots (some name) decl.rets) decl.body))
          targetFinal targetFinalState outcome :=
        execStmt_of_singleton htarget'
      have htargetBlock' :=
        YulEvmCompiler.Optimizer.Step.emptyScope_congr htargetBlock
          (YulEvmCompiler.Optimizer.EmptyScopeRel.add _)
      have htargetBody : ExecStmt D (spillFuns layout.slots ([] :: closure))
          (callEnv decl.params decl.rets argvals) afterEntryState
          (.block (rewriteStmts layout.slots (some name)
            (copyBackReturns layout.slots (some name) decl.rets) decl.body))
          targetFinal targetFinalState outcome := by
        simpa [spillFuns, spillScope] using htargetBlock'
      have hshell : CallShellFacts decl.rets sourceFinal targetFinal outcome := by
        cases outcome with
        | normal => simpa [CallShellFacts, NamesBound] using hexitBound
        | «break» => simp [CallShellFacts]
        | «continue» => simp [CallShellFacts]
        | «leave» => simpa [CallShellFacts] using hleave rfl
        | halt => simp [CallShellFacts]
      exact ⟨{
        targetFinal := targetFinal
        targetFinalState := targetFinalState
        cuts := cuts
        body := htargetBody
        rel := hcontrol.liveRel.frameRel
        above := habove
        shell := hshell }⟩

theorem closeNormalCalleeBody
    {selected : SpillSet} {layout : MemorySpillSelect.Layout}
    {policyCallee : Frame} {name : Ident} {decl : FDecl G}
    {callerFuns closure : FunEnv G} {argvals : List U256}
    {sourceArgState sourceFinalState : EvmState} {sourceFinal : WordEnv}
    {targetState targetArgState afterEntryState : EvmState}
    {targetEnv : WordEnv} {targetArgs : List (Expr Op)} {cutoff : Nat}
    (hlookup : lookupFun callerFuns name = some (decl, closure))
    (hlength : argvals.length = decl.params.length)
    (hsourceBody : ExecStmt G closure
      (callEnv decl.params decl.rets argvals) sourceArgState
      (.block decl.body) sourceFinal sourceFinalState .normal)
    (hargs : EvalArgs D (spillFuns layout.slots callerFuns)
      targetEnv targetState targetArgs (.vals argvals targetArgState))
    (hentry : ExecStmts D (spillFuns layout.slots ([] :: closure))
      (callEnv decl.params decl.rets argvals) targetArgState
      (initParams layout.slots (some name) decl.params ++
        initReturns layout.slots (some name) decl.rets)
      (callEnv decl.params decl.rets argvals) afterEntryState .normal)
    (hentryAbove : AboveUnchanged cutoff reserved targetArgState afterEntryState)
    (hbody : CalleeBodyResult (base := base) (reserved := reserved)
      selected layout policyCallee name decl closure argvals sourceFinal
      sourceFinalState .normal afterEntryState cutoff)
    (howner : policyCallee.owner = some name)
    (hnodup : decl.rets.Nodup)
    (hbounds : ∀ localName slot,
      slotFor? layout.slots (some name) localName = some slot →
        slot + 32 ≤ reserved)
    (hreserved : reserved < 2 ^ 256) :
    ∃ targetFinalState,
      EvalExpr D (spillFuns layout.slots callerFuns) targetEnv targetState
          (.call name targetArgs)
          (.vals (decl.rets.map (fun ret =>
            (envGet sourceFinal ret).getD (0 : U256))) targetFinalState) ∧
        ScratchRel base reserved sourceFinalState targetFinalState ∧
        AboveUnchanged cutoff reserved targetArgState targetFinalState := by
  have hrel : ScopedFrameRel (base := base) (reserved := reserved)
      layout.slots (some name) (decl.params ++ decl.rets) hbody.cuts
      sourceFinal sourceFinalState hbody.targetFinal hbody.targetFinalState := by
    simpa [howner] using hbody.rel
  have hreturns : ∀ ret ∈ decl.rets,
      ∃ value, envGet sourceFinal ret = some value := by
    simpa [CallShellFacts] using hbody.shell
  exact closeCallOk_normal hlookup hlength hargs hsourceBody hentry hbody.body
    hrel hreturns hnodup hbounds hreserved hentryAbove hbody.above

theorem closeLeaveCalleeBody
    {selected : SpillSet} {layout : MemorySpillSelect.Layout}
    {policyCallee : Frame} {name : Ident} {decl : FDecl G}
    {callerFuns closure : FunEnv G} {argvals : List U256}
    {sourceArgState sourceFinalState : EvmState} {sourceFinal : WordEnv}
    {targetState targetArgState afterEntryState : EvmState}
    {targetEnv : WordEnv} {targetArgs : List (Expr Op)} {cutoff : Nat}
    (hlookup : lookupFun callerFuns name = some (decl, closure))
    (hlength : argvals.length = decl.params.length)
    (hsourceBody : ExecStmt G closure
      (callEnv decl.params decl.rets argvals) sourceArgState
      (.block decl.body) sourceFinal sourceFinalState .leave)
    (hargs : EvalArgs D (spillFuns layout.slots callerFuns)
      targetEnv targetState targetArgs (.vals argvals targetArgState))
    (hentry : ExecStmts D (spillFuns layout.slots ([] :: closure))
      (callEnv decl.params decl.rets argvals) targetArgState
      (initParams layout.slots (some name) decl.params ++
        initReturns layout.slots (some name) decl.rets)
      (callEnv decl.params decl.rets argvals) afterEntryState .normal)
    (hentryAbove : AboveUnchanged cutoff reserved targetArgState afterEntryState)
    (hbody : CalleeBodyResult (base := base) (reserved := reserved)
      selected layout policyCallee name decl closure argvals sourceFinal
      sourceFinalState .leave afterEntryState cutoff)
    (howner : policyCallee.owner = some name) :
    ∃ targetFinalState,
      EvalExpr D (spillFuns layout.slots callerFuns) targetEnv targetState
          (.call name targetArgs)
          (.vals (decl.rets.map (fun ret =>
            (envGet sourceFinal ret).getD (0 : U256))) targetFinalState) ∧
        ScratchRel base reserved sourceFinalState targetFinalState ∧
        AboveUnchanged cutoff reserved targetArgState targetFinalState := by
  have hrel : ScopedFrameRel (base := base) (reserved := reserved)
      layout.slots (some name) (decl.params ++ decl.rets) hbody.cuts
      sourceFinal sourceFinalState hbody.targetFinal hbody.targetFinalState := by
    simpa [howner] using hbody.rel
  have hsynced : ReturnsSynced decl.rets sourceFinal hbody.targetFinal := by
    simpa [CallShellFacts] using hbody.shell
  obtain ⟨hcall, hscratch, habove⟩ := closeCallOk_leave hlookup hlength
    hargs hsourceBody hentry hbody.body hrel hsynced hentryAbove hbody.above
  exact ⟨hbody.targetFinalState, hcall, hscratch, habove⟩

theorem closeHaltingCalleeBody
    {selected : SpillSet} {layout : MemorySpillSelect.Layout}
    {policyCallee : Frame} {name : Ident} {decl : FDecl G}
    {callerFuns closure : FunEnv G} {argvals : List U256}
    {sourceArgState sourceFinalState : EvmState} {sourceFinal : WordEnv}
    {targetState targetArgState afterEntryState : EvmState}
    {targetEnv : WordEnv} {targetArgs : List (Expr Op)} {cutoff : Nat}
    (hlookup : lookupFun callerFuns name = some (decl, closure))
    (hlength : argvals.length = decl.params.length)
    (hsourceBody : ExecStmt G closure
      (callEnv decl.params decl.rets argvals) sourceArgState
      (.block decl.body) sourceFinal sourceFinalState .halt)
    (hargs : EvalArgs D (spillFuns layout.slots callerFuns)
      targetEnv targetState targetArgs (.vals argvals targetArgState))
    (hentry : ExecStmts D (spillFuns layout.slots ([] :: closure))
      (callEnv decl.params decl.rets argvals) targetArgState
      (initParams layout.slots (some name) decl.params ++
        initReturns layout.slots (some name) decl.rets)
      (callEnv decl.params decl.rets argvals) afterEntryState .normal)
    (hentryAbove : AboveUnchanged cutoff reserved targetArgState afterEntryState)
    (hbody : CalleeBodyResult (base := base) (reserved := reserved)
      selected layout policyCallee name decl closure argvals sourceFinal
      sourceFinalState .halt afterEntryState cutoff)
    (howner : policyCallee.owner = some name) :
    ∃ targetFinalState,
      EvalExpr D (spillFuns layout.slots callerFuns) targetEnv targetState
          (.call name targetArgs) (.halt targetFinalState) ∧
        ScratchRel base reserved sourceFinalState targetFinalState ∧
        AboveUnchanged cutoff reserved targetArgState targetFinalState := by
  have hrel : ScopedFrameRel (base := base) (reserved := reserved)
      layout.slots (some name) (decl.params ++ decl.rets) hbody.cuts
      sourceFinal sourceFinalState hbody.targetFinal hbody.targetFinalState := by
    simpa [howner] using hbody.rel
  obtain ⟨hcall, hscratch, habove⟩ := closeCallHalt hlookup hlength hargs
    hsourceBody hentry hbody.body hrel hentryAbove hbody.above
  exact ⟨hbody.targetFinalState, hcall, hscratch, habove⟩

/-! ## Builtin branches after arbitrary (possibly calling) arguments -/

theorem closeBuiltinOkBranch
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {policyOp executedOp : Op}
    {policyArgs executedArgs : List (Expr Op)} {argvals values : List U256}
    {source target : WordEnv}
    {sourceArgState sourceFinalState targetState : EvmState}
    {sourceFuns : FunEnv G} {exitCopies : Block Op} {cutoff : Nat}
    (hargs : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.args policyArgs) (.args executedArgs)
      (.eres (.vals argvals sourceArgState)) sourceFuns targetState
      exitCopies cutoff)
    (hbuiltin : (guardedEvm calls creates base reserved).Builtin
      executedOp argvals sourceArgState
      (.ok values sourceFinalState))
    (hexternals : GuardedExternals calls creates base reserved)
    (hbounds : ∀ name slot,
      slotFor? layout.slots frame.owner name = some slot →
        base ≤ slot ∧ slot + 32 ≤ reserved)
    (hbaseCutoff : base ≤ cutoff) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.expr (.builtin policyOp policyArgs))
      (.expr (.builtin executedOp executedArgs))
      (.eres (.vals values sourceFinalState)) sourceFuns targetState
      exitCopies cutoff := by
  obtain ⟨targetArgsResult, htargetArgs, hargsResult, haboveArgs⟩ := hargs
  cases targetArgsResult with
  | sres targetFinal targetFinalState targetOutcome =>
      simp [ResultControlRel] at hargsResult
  | eres targetArgsResult' =>
      cases targetArgsResult' with
      | halt targetArgsState => simp [ResultControlRel] at hargsResult
      | vals targetArgvals targetArgsState =>
          rcases hargsResult with
            ⟨hargvals, hcontrol, horigin, hexitBound, hexitSignature⟩
          subst targetArgvals
          obtain ⟨rightResult, hright, hresult, hloaded, haboveBuiltin⟩ :=
            guardedBuiltin_sim hexternals hcontrol.liveRel.frameRel.scratch
              hbuiltin hcontrol.liveRel.frameRel.loaded hbounds hbaseCutoff
          cases rightResult with
          | halt rightState => simp [ResultRel] at hresult
          | ok rightValues rightState =>
              rcases hresult with ⟨hvalues, hscratch⟩
              refine ⟨.eres (.vals rightValues rightState), ?_, ?_,
                haboveArgs.trans haboveBuiltin⟩
              · simpa [rewriteCode, rewriteExpr] using
                  (Step.builtinOk htargetArgs hright)
              · exact ⟨hvalues.symm,
                  { liveRel := {
                      frameRel := {
                        env := hcontrol.liveRel.frameRel.env
                        loaded := hloaded
                        scratch := hscratch }
                      bound := hcontrol.liveRel.bound
                      certified := hcontrol.liveRel.certified }
                    unique := hcontrol.unique },
                  horigin, hexitBound, hexitSignature⟩

theorem closeBuiltinHaltBranch
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {policyOp executedOp : Op}
    {policyArgs executedArgs : List (Expr Op)} {argvals : List U256}
    {source target : WordEnv}
    {sourceArgState sourceFinalState targetState : EvmState}
    {sourceFuns : FunEnv G} {exitCopies : Block Op} {cutoff : Nat}
    (hargs : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.args policyArgs) (.args executedArgs)
      (.eres (.vals argvals sourceArgState)) sourceFuns targetState
      exitCopies cutoff)
    (hbuiltin : (guardedEvm calls creates base reserved).Builtin
      executedOp argvals sourceArgState
      (.halt sourceFinalState))
    (hexternals : GuardedExternals calls creates base reserved)
    (hbounds : ∀ name slot,
      slotFor? layout.slots frame.owner name = some slot →
        base ≤ slot ∧ slot + 32 ≤ reserved)
    (hbaseCutoff : base ≤ cutoff) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.expr (.builtin policyOp policyArgs))
      (.expr (.builtin executedOp executedArgs))
      (.eres (.halt sourceFinalState)) sourceFuns targetState exitCopies cutoff := by
  obtain ⟨targetArgsResult, htargetArgs, hargsResult, haboveArgs⟩ := hargs
  cases targetArgsResult with
  | sres targetFinal targetFinalState targetOutcome =>
      simp [ResultControlRel] at hargsResult
  | eres targetArgsResult' =>
      cases targetArgsResult' with
      | halt targetArgsState => simp [ResultControlRel] at hargsResult
      | vals targetArgvals targetArgsState =>
          rcases hargsResult with
            ⟨hargvals, hcontrol, horigin, hexitBound, hexitSignature⟩
          subst targetArgvals
          obtain ⟨rightResult, hright, hresult, hloaded, haboveBuiltin⟩ :=
            guardedBuiltin_sim hexternals hcontrol.liveRel.frameRel.scratch
              hbuiltin hcontrol.liveRel.frameRel.loaded hbounds hbaseCutoff
          cases rightResult with
          | ok rightValues rightState => simp [ResultRel] at hresult
          | halt rightState =>
              refine ⟨.eres (.halt rightState), ?_, ?_,
                haboveArgs.trans haboveBuiltin⟩
              · simpa [rewriteCode, rewriteExpr] using
                  (Step.builtinHalt htargetArgs hright)
              · exact ⟨{
                    liveRel := {
                      frameRel := {
                        env := hcontrol.liveRel.frameRel.env
                        loaded := hloaded
                        scratch := hresult }
                      bound := hcontrol.liveRel.bound
                      certified := hcontrol.liveRel.certified }
                    unique := hcontrol.unique },
                  horigin, hexitBound, hexitSignature⟩

theorem closeBuiltinArgsHaltBranch
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {policyOp executedOp : Op}
    {policyArgs executedArgs : List (Expr Op)}
    {source target : WordEnv} {sourceFinalState targetState : EvmState}
    {sourceFuns : FunEnv G} {exitCopies : Block Op} {cutoff : Nat}
    (hargs : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.args policyArgs) (.args executedArgs)
      (.eres (.halt sourceFinalState)) sourceFuns targetState exitCopies cutoff) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.expr (.builtin policyOp policyArgs))
      (.expr (.builtin executedOp executedArgs))
      (.eres (.halt sourceFinalState)) sourceFuns targetState exitCopies cutoff := by
  obtain ⟨targetResult, htarget, hresult, habove⟩ := hargs
  cases targetResult with
  | sres targetFinal targetFinalState targetOutcome =>
      simp [ResultControlRel] at hresult
  | eres targetArgsResult =>
      cases targetArgsResult with
      | vals targetValues targetFinalState => simp [ResultControlRel] at hresult
      | halt targetFinalState =>
          rcases hresult with
            ⟨hcontrol, horigin, hexitBound, hexitSignature⟩
          refine ⟨.eres (.halt targetFinalState), ?_, ?_, habove⟩
          · simpa [rewriteCode, rewriteExpr] using
              (Step.builtinArgsHalt htarget)
          · exact ⟨hcontrol, horigin, hexitBound, hexitSignature⟩

/-! ## Right-to-left argument-list composition -/

theorem closeArgsRestHaltBranch
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {policyHead executedHead : Expr Op}
    {policyRest executedRest : List (Expr Op)}
    {source target : WordEnv} {sourceFinalState targetState : EvmState}
    {sourceFuns : FunEnv G} {exitCopies : Block Op} {cutoff : Nat}
    (hrest : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.args policyRest) (.args executedRest)
      (.eres (.halt sourceFinalState)) sourceFuns targetState exitCopies cutoff) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.args (policyHead :: policyRest))
      (.args (executedHead :: executedRest))
      (.eres (.halt sourceFinalState)) sourceFuns targetState exitCopies cutoff := by
  obtain ⟨targetResult, htarget, hresult, habove⟩ := hrest
  cases targetResult with
  | sres targetFinal targetFinalState targetOutcome =>
      simp [ResultControlRel] at hresult
  | eres targetRestResult =>
      cases targetRestResult with
      | vals targetValues targetFinalState => simp [ResultControlRel] at hresult
      | halt targetFinalState =>
          rcases hresult with
            ⟨hcontrol, horigin, hexitBound, hexitSignature⟩
          refine ⟨.eres (.halt targetFinalState), ?_, ?_, habove⟩
          · simpa [rewriteCode, rewriteArgs] using
              (Step.argsRestHalt htarget)
          · exact ⟨hcontrol, horigin, hexitBound, hexitSignature⟩

theorem closeArgsConsBranch
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {policyHead executedHead : Expr Op}
    {policyRest executedRest : List (Expr Op)} {restValues : List U256}
    {value : U256} {source target : WordEnv}
    {sourceRestState sourceFinalState targetState : EvmState}
    {sourceFuns : FunEnv G} {exitCopies : Block Op} {cutoff : Nat}
    (hrest : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.args policyRest) (.args executedRest)
      (.eres (.vals restValues sourceRestState)) sourceFuns targetState
      exitCopies cutoff)
    (hclose : ∀ {targetRestState},
      EvalArgs D (spillFuns layout.slots sourceFuns) target targetState
          (rewriteArgs layout.slots frame.owner executedRest)
          (.vals restValues targetRestState) →
        ControlLiveRel (base := base) (reserved := reserved)
          selected layout frame signature cuts live
          source sourceRestState target targetRestState →
        ∃ targetFinalState,
          EvalExpr D (spillFuns layout.slots sourceFuns) target targetRestState
              (rewriteExpr layout.slots frame.owner executedHead)
              (.vals [value] targetFinalState) ∧
            ControlLiveRel (base := base) (reserved := reserved)
              selected layout frame signature cuts live
              source sourceFinalState target targetFinalState ∧
            AboveUnchanged cutoff reserved targetRestState targetFinalState) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.args (policyHead :: policyRest))
      (.args (executedHead :: executedRest))
      (.eres (.vals (value :: restValues) sourceFinalState)) sourceFuns targetState
      exitCopies cutoff := by
  obtain ⟨targetResult, htargetRest, hresult, haboveRest⟩ := hrest
  cases targetResult with
  | sres targetFinal targetFinalState targetOutcome =>
      simp [ResultControlRel] at hresult
  | eres targetRestResult =>
      cases targetRestResult with
      | halt targetRestState => simp [ResultControlRel] at hresult
      | vals targetRestValues targetRestState =>
          rcases hresult with
            ⟨hvalues, hcontrol, horigin, hexitBound, hexitSignature⟩
          subst targetRestValues
          obtain ⟨targetFinalState, htargetHead, hcontrol', haboveHead⟩ :=
            hclose htargetRest hcontrol
          refine ⟨.eres (.vals (value :: restValues) targetFinalState), ?_,
            ?_, haboveRest.trans haboveHead⟩
          · simpa [rewriteCode, rewriteArgs] using
              (Step.argsCons htargetRest htargetHead)
          · exact ⟨rfl, hcontrol', horigin, hexitBound, hexitSignature⟩

theorem closeArgsHeadHaltBranch
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {policyHead executedHead : Expr Op}
    {policyRest executedRest : List (Expr Op)} {restValues : List U256}
    {source target : WordEnv}
    {sourceRestState sourceFinalState targetState : EvmState}
    {sourceFuns : FunEnv G} {exitCopies : Block Op} {cutoff : Nat}
    (hrest : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.args policyRest) (.args executedRest)
      (.eres (.vals restValues sourceRestState)) sourceFuns targetState
      exitCopies cutoff)
    (hclose : ∀ {targetRestState},
      EvalArgs D (spillFuns layout.slots sourceFuns) target targetState
          (rewriteArgs layout.slots frame.owner executedRest)
          (.vals restValues targetRestState) →
        ControlLiveRel (base := base) (reserved := reserved)
          selected layout frame signature cuts live
          source sourceRestState target targetRestState →
        ∃ targetFinalState,
          EvalExpr D (spillFuns layout.slots sourceFuns) target targetRestState
              (rewriteExpr layout.slots frame.owner executedHead)
              (.halt targetFinalState) ∧
            ControlLiveRel (base := base) (reserved := reserved)
              selected layout frame signature cuts live
              source sourceFinalState target targetFinalState ∧
            AboveUnchanged cutoff reserved targetRestState targetFinalState) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.args (policyHead :: policyRest))
      (.args (executedHead :: executedRest))
      (.eres (.halt sourceFinalState)) sourceFuns targetState exitCopies cutoff := by
  obtain ⟨targetResult, htargetRest, hresult, haboveRest⟩ := hrest
  cases targetResult with
  | sres targetFinal targetFinalState targetOutcome =>
      simp [ResultControlRel] at hresult
  | eres targetRestResult =>
      cases targetRestResult with
      | halt targetRestState => simp [ResultControlRel] at hresult
      | vals targetRestValues targetRestState =>
          rcases hresult with
            ⟨hvalues, hcontrol, horigin, hexitBound, hexitSignature⟩
          subst targetRestValues
          obtain ⟨targetFinalState, htargetHead, hcontrol', haboveHead⟩ :=
            hclose htargetRest hcontrol
          refine ⟨.eres (.halt targetFinalState), ?_, ?_,
            haboveRest.trans haboveHead⟩
          · simpa [rewriteCode, rewriteArgs] using
              (Step.argsHeadHalt htargetRest htargetHead)
          · exact ⟨hcontrol', horigin, hexitBound, hexitSignature⟩

theorem simulateFunDefLeaf
    {mode : OriginMode} {policyRoot : Block Op} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout}
    {policyFrame executedFrame : Frame} {cuts : List CutMark}
    {live : SpillSet} {exitNames : List Ident}
    {policyName executedName : Ident}
    {policyParams policyReturns : List Ident} {policyBody : Block Op}
    {executedParams executedReturns : List Ident} {executedBody : Block Op}
    {source target : WordEnv} {sourceState targetState : EvmState}
    {sourceFuns : FunEnv G} {exitCopies : Block Op} {cutoff : Nat}
    (hctx : ControlStepContext mode policyRoot selected policyFrame executedFrame
      live (.stmt (.funDef policyName policyParams policyReturns policyBody))
      (.stmt (.funDef executedName executedParams executedReturns executedBody))
      exitNames source)
    (hrel : ControlLiveRel (base := base) (reserved := reserved)
      selected layout policyFrame (policyFrame.params ++ policyFrame.returns)
      cuts live source sourceState target targetState) :
    StepSimResult (base := base) (reserved := reserved)
      (MemorySpill.declaredStmts policyRoot) selected layout policyFrame
      (policyFrame.params ++ policyFrame.returns) cuts live exitNames source target
      (.stmt (.funDef policyName policyParams policyReturns policyBody))
      (.stmt (.funDef executedName executedParams executedReturns executedBody))
      (.sres source sourceState .normal) sourceFuns targetState exitCopies cutoff := by
  refine ⟨.sres target targetState .normal, ?_, ?_,
    AboveUnchanged.refl cutoff reserved targetState⟩
  · simpa [rewriteCode] using
      (execRewriteFunDef (slots := layout.slots) (owner := policyFrame.owner)
        (exitCopies := exitCopies) (sourceFuns := sourceFuns)
        (name := executedName) (params := executedParams)
        (returns := executedReturns) (body := executedBody)
        (vars := target) (state := targetState))
  · refine ⟨live, rfl, hrel, hctx.motive.envDeclared, hctx.exitsBound,
      hctx.exitsInSignature, ?_, ?_, ?_⟩
    · intro hleave
      contradiction
    · intro body heq
      cases heq
    · intro _
      simp [liveAfterCode, liveStmt]

theorem simulateBreakLeaf
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {source target : WordEnv}
    {sourceState targetState : EvmState} {sourceFuns : FunEnv G}
    {exitCopies : Block Op} {cutoff : Nat}
    (hrel : ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (horigin : EnvDeclaredOrigin globalDeclared source)
    (hexitBound : NamesBound exitNames source)
    (hexitSignature : ∀ name ∈ exitNames, name ∈ signature) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.stmt .break) (.stmt .break)
      (.sres source sourceState .break) sourceFuns targetState exitCopies cutoff := by
  obtain ⟨targetResult, hstep, hresult, habove⟩ :=
    simulateBreak (exitCopies := exitCopies) hrel horigin hexitBound
      hexitSignature cutoff
  exact ⟨targetResult, hstep, hresult, habove⟩

theorem simulateContinueLeaf
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {source target : WordEnv}
    {sourceState targetState : EvmState} {sourceFuns : FunEnv G}
    {exitCopies : Block Op} {cutoff : Nat}
    (hrel : ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (horigin : EnvDeclaredOrigin globalDeclared source)
    (hexitBound : NamesBound exitNames source)
    (hexitSignature : ∀ name ∈ exitNames, name ∈ signature) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.stmt .continue) (.stmt .continue)
      (.sres source sourceState .continue) sourceFuns targetState exitCopies cutoff := by
  obtain ⟨targetResult, hstep, hresult, habove⟩ :=
    simulateContinue (exitCopies := exitCopies) hrel horigin hexitBound
      hexitSignature cutoff
  exact ⟨targetResult, hstep, hresult, habove⟩

theorem simulateSeqNilLeaf
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {source target : WordEnv}
    {sourceState targetState : EvmState} {sourceFuns : FunEnv G}
    {exitCopies : Block Op} {cutoff : Nat}
    (hrel : ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (horigin : EnvDeclaredOrigin globalDeclared source)
    (hexitBound : NamesBound exitNames source)
    (hexitSignature : ∀ name ∈ exitNames, name ∈ signature) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.stmts []) (.stmts [])
      (.sres source sourceState .normal) sourceFuns targetState exitCopies cutoff := by
  refine ⟨.sres target targetState .normal, ?_, ?_,
    AboveUnchanged.refl cutoff reserved targetState⟩
  · simpa [rewriteCode, rewriteStmts] using
      (Step.seqNil : ExecStmts D (spillFuns layout.slots sourceFuns)
        target targetState [] target targetState .normal)
  · refine ⟨live, rfl, hrel, horigin, hexitBound, hexitSignature,
      ?_, ?_, ?_⟩
    · intro hleave
      contradiction
    · intro body heq
      cases heq
    · intro _
      simp [liveAfterCode, liveStmts]

/-! ## Statement shells fed by an expression induction hypothesis -/

theorem closeExprStmtNormal
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {policyExpr executedExpr : Expr Op}
    {source target : WordEnv} {sourceFinalState targetState : EvmState}
    {sourceFuns : FunEnv G} {exitCopies : Block Op} {cutoff : Nat}
    (hexpr : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.expr policyExpr) (.expr executedExpr)
      (.eres (.vals [] sourceFinalState)) sourceFuns targetState exitCopies cutoff) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.stmt (.exprStmt policyExpr)) (.stmt (.exprStmt executedExpr))
      (.sres source sourceFinalState .normal) sourceFuns targetState
      exitCopies cutoff := by
  obtain ⟨targetResult, htarget, hresult, habove⟩ := hexpr
  cases targetResult with
  | sres targetFinal targetFinalState targetOutcome =>
      simp [ResultControlRel] at hresult
  | eres targetExprResult =>
      cases targetExprResult with
      | halt targetFinalState => simp [ResultControlRel] at hresult
      | vals targetValues targetFinalState =>
          rcases hresult with
            ⟨hvalues, hcontrol, horigin, hexitBound, hexitSignature⟩
          subst targetValues
          refine ⟨.sres target targetFinalState .normal, ?_, ?_, habove⟩
          · simpa [rewriteCode] using
              (execRewriteExprStmt_normal
                (slots := layout.slots) (owner := frame.owner)
                (exitCopies := exitCopies) (sourceFuns := sourceFuns)
                (expression := executedExpr) htarget)
          · refine ⟨live, rfl, hcontrol, horigin, hexitBound,
              hexitSignature, ?_, ?_, ?_⟩
            · intro hleave
              contradiction
            · intro body heq
              cases heq
            · intro _
              simp [liveAfterCode, liveStmt]

theorem closeExprStmtHalt
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {policyExpr executedExpr : Expr Op}
    {source target : WordEnv} {sourceFinalState targetState : EvmState}
    {sourceFuns : FunEnv G} {exitCopies : Block Op} {cutoff : Nat}
    (hexpr : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.expr policyExpr) (.expr executedExpr)
      (.eres (.halt sourceFinalState)) sourceFuns targetState exitCopies cutoff) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.stmt (.exprStmt policyExpr)) (.stmt (.exprStmt executedExpr))
      (.sres source sourceFinalState .halt) sourceFuns targetState
      exitCopies cutoff := by
  obtain ⟨targetResult, htarget, hresult, habove⟩ := hexpr
  cases targetResult with
  | sres targetFinal targetFinalState targetOutcome =>
      simp [ResultControlRel] at hresult
  | eres targetExprResult =>
      cases targetExprResult with
      | vals targetValues targetFinalState => simp [ResultControlRel] at hresult
      | halt targetFinalState =>
          rcases hresult with
            ⟨hcontrol, horigin, hexitBound, hexitSignature⟩
          refine ⟨.sres target targetFinalState .halt, ?_, ?_, habove⟩
          · simpa [rewriteCode] using
              (execRewriteExprStmt_halt
                (slots := layout.slots) (owner := frame.owner)
                (exitCopies := exitCopies) (sourceFuns := sourceFuns)
                (expression := executedExpr) htarget)
          · refine ⟨live, rfl, hcontrol, horigin, hexitBound,
              hexitSignature, ?_, ?_, ?_⟩
            · intro hleave
              contradiction
            · intro body heq
              cases heq
            · intro hnormal
              contradiction

theorem closeIfFalse
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {policyCondition executedCondition : Expr Op}
    {policyBody executedBody : Block Op} {value : U256}
    {source target : WordEnv} {sourceFinalState targetState : EvmState}
    {sourceFuns : FunEnv G} {exitCopies : Block Op} {cutoff : Nat}
    (hexpr : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.expr policyCondition) (.expr executedCondition)
      (.eres (.vals [value] sourceFinalState)) sourceFuns targetState
      exitCopies cutoff)
    (hzero : value = Dialect.zero G) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.stmt (.cond policyCondition policyBody))
      (.stmt (.cond executedCondition executedBody))
      (.sres source sourceFinalState .normal) sourceFuns targetState
      exitCopies cutoff := by
  obtain ⟨targetResult, htarget, hresult, habove⟩ := hexpr
  cases targetResult with
  | sres targetFinal targetFinalState targetOutcome =>
      simp [ResultControlRel] at hresult
  | eres targetExprResult =>
      cases targetExprResult with
      | halt targetFinalState => simp [ResultControlRel] at hresult
      | vals targetValues targetFinalState =>
          rcases hresult with
            ⟨hvalues, hcontrol, horigin, hexitBound, hexitSignature⟩
          have hzero' : value = 0 := by
            change value = (0 : U256) at hzero
            exact hzero
          subst value
          subst targetValues
          refine ⟨.sres target targetFinalState .normal, ?_, ?_, habove⟩
          · simpa [rewriteCode] using
              (execRewriteIf_false
                (slots := layout.slots) (owner := frame.owner)
                (exitCopies := exitCopies) (sourceFuns := sourceFuns)
                (condition := executedCondition) (body := executedBody) htarget)
          · refine ⟨live, rfl, hcontrol, horigin, hexitBound,
              hexitSignature, ?_, ?_, ?_⟩
            · intro hleave
              contradiction
            · intro body heq
              cases heq
            · intro _
              simp [liveAfterCode, liveStmt]

theorem closeIfHalt
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {policyCondition executedCondition : Expr Op}
    {policyBody executedBody : Block Op}
    {source target : WordEnv} {sourceFinalState targetState : EvmState}
    {sourceFuns : FunEnv G} {exitCopies : Block Op} {cutoff : Nat}
    (hexpr : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.expr policyCondition) (.expr executedCondition)
      (.eres (.halt sourceFinalState)) sourceFuns targetState exitCopies cutoff) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.stmt (.cond policyCondition policyBody))
      (.stmt (.cond executedCondition executedBody))
      (.sres source sourceFinalState .halt) sourceFuns targetState
      exitCopies cutoff := by
  obtain ⟨targetResult, htarget, hresult, habove⟩ := hexpr
  cases targetResult with
  | sres targetFinal targetFinalState targetOutcome =>
      simp [ResultControlRel] at hresult
  | eres targetExprResult =>
      cases targetExprResult with
      | vals targetValues targetFinalState => simp [ResultControlRel] at hresult
      | halt targetFinalState =>
          rcases hresult with
            ⟨hcontrol, horigin, hexitBound, hexitSignature⟩
          refine ⟨.sres target targetFinalState .halt, ?_, ?_, habove⟩
          · simpa [rewriteCode] using
              (execRewriteIf_halt
                (slots := layout.slots) (owner := frame.owner)
                (exitCopies := exitCopies) (sourceFuns := sourceFuns)
                (condition := executedCondition) (body := executedBody) htarget)
          · refine ⟨live, rfl, hcontrol, horigin, hexitBound,
              hexitSignature, ?_, ?_, ?_⟩
            · intro hleave
              contradiction
            · intro body heq
              cases heq
            · intro hnormal
              contradiction

theorem closeIfTrue
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {policyCondition executedCondition : Expr Op}
    {policyBody executedBody : Block Op} {value : U256}
    {source sourceFinal target : WordEnv}
    {sourceConditionState sourceFinalState targetState : EvmState}
    {outcome : Outcome} {sourceFuns : FunEnv G}
    {exitCopies : Block Op} {cutoff : Nat}
    (hcondition : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.expr policyCondition) (.expr executedCondition)
      (.eres (.vals [value] sourceConditionState)) sourceFuns targetState
      exitCopies cutoff)
    (hnonzero : value ≠ Dialect.zero G)
    (hbodyClose : ∀ {targetConditionState},
      EvalExpr D (spillFuns layout.slots sourceFuns) target targetState
          (rewriteExpr layout.slots frame.owner executedCondition)
          (.vals [value] targetConditionState) →
        ControlLiveRel (base := base) (reserved := reserved)
          selected layout frame signature cuts live
          source sourceConditionState target targetConditionState →
        StepSimResult (base := base) (reserved := reserved)
          globalDeclared selected layout frame signature cuts live exitNames
          source target (.stmt (.block policyBody)) (.stmt (.block executedBody))
          (.sres sourceFinal sourceFinalState outcome) sourceFuns
          targetConditionState exitCopies cutoff) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.stmt (.cond policyCondition policyBody))
      (.stmt (.cond executedCondition executedBody))
      (.sres sourceFinal sourceFinalState outcome) sourceFuns targetState
      exitCopies cutoff := by
  obtain ⟨targetConditionResult, htargetCondition, hconditionResult,
    haboveCondition⟩ := hcondition
  cases targetConditionResult with
  | sres targetFinal' targetFinalState targetOutcome =>
      simp [ResultControlRel] at hconditionResult
  | eres targetConditionResult' =>
      cases targetConditionResult' with
      | halt targetConditionState => simp [ResultControlRel] at hconditionResult
      | vals targetValues targetConditionState =>
          rcases hconditionResult with
            ⟨hvalues, hcontrol, horigin, hexitBound, hexitSignature⟩
          subst targetValues
          obtain ⟨targetBodyResult, htargetBody, hbodyResult, haboveBody⟩ :=
            hbodyClose htargetCondition hcontrol
          cases targetBodyResult with
          | eres targetExpressionResult => simp [ResultControlRel] at hbodyResult
          | sres targetBody targetFinalState targetOutcome =>
              rcases hbodyResult with
                ⟨finalLive, houtcome, hfinalControl, hfinalOrigin,
                  hfinalBound, hfinalSignature, hleave, hblock, hnormal⟩
              subst targetOutcome
              have hzero : Dialect.zero D = (0 : U256) := by
                change litValue (.number 0) = (0 : U256)
                decide
              have hnonzero' : value ≠ Dialect.zero D := by
                rw [hzero]
                change value ≠ (0 : U256) at hnonzero
                exact hnonzero
              refine ⟨.sres targetBody targetFinalState outcome, ?_, ?_,
                haboveCondition.trans haboveBody⟩
              · have htargetBody' : ExecStmts D
                    (spillFuns layout.slots sourceFuns) target targetConditionState
                    [.block (rewriteStmts layout.slots frame.owner exitCopies
                      executedBody)] targetBody targetFinalState outcome := by
                    simpa [rewriteCode, rewriteStmt] using htargetBody
                simpa [rewriteCode] using
                  (execRewriteIf_true htargetCondition hnonzero'
                    (execStmt_of_singleton htargetBody'))
              · refine ⟨finalLive, rfl, hfinalControl, hfinalOrigin,
                  hfinalBound, hfinalSignature, hleave, ?_, ?_⟩
                · intro body heq
                  cases heq
                intro hout
                have := hnormal hout
                simpa [liveAfterCode, liveStmt] using this

theorem closeSwitchHalt
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {policyCondition executedCondition : Expr Op}
    {policyCases executedCases : List (Literal × Block Op)}
    {policyDefault executedDefault : Option (Block Op)}
    {source target : WordEnv} {sourceFinalState targetState : EvmState}
    {sourceFuns : FunEnv G} {exitCopies : Block Op} {cutoff : Nat}
    (hexpr : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.expr policyCondition) (.expr executedCondition)
      (.eres (.halt sourceFinalState)) sourceFuns targetState exitCopies cutoff) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.stmt (.switch policyCondition policyCases policyDefault))
      (.stmt (.switch executedCondition executedCases executedDefault))
      (.sres source sourceFinalState .halt) sourceFuns targetState
      exitCopies cutoff := by
  obtain ⟨targetResult, htarget, hresult, habove⟩ := hexpr
  cases targetResult with
  | sres targetFinal targetFinalState targetOutcome =>
      simp [ResultControlRel] at hresult
  | eres targetExprResult =>
      cases targetExprResult with
      | vals targetValues targetFinalState => simp [ResultControlRel] at hresult
      | halt targetFinalState =>
          rcases hresult with
            ⟨hcontrol, horigin, hexitBound, hexitSignature⟩
          refine ⟨.sres target targetFinalState .halt, ?_, ?_, habove⟩
          · have hstep := Step.seqStop (rest := [])
                (Step.switchHalt htarget : ExecStmt D
                  (spillFuns layout.slots sourceFuns) target targetState
                  (.switch (rewriteExpr layout.slots frame.owner executedCondition)
                    (rewriteCases layout.slots frame.owner exitCopies executedCases)
                    (executedDefault.map
                      (rewriteStmts layout.slots frame.owner exitCopies)))
                  target targetFinalState .halt)
                (by decide)
            cases executedDefault <;>
              simpa [rewriteCode, rewriteStmt] using hstep
          · refine ⟨live, rfl, hcontrol, horigin, hexitBound,
              hexitSignature, ?_, ?_, ?_⟩
            · intro hleave
              contradiction
            · intro body heq
              cases heq
            · intro hnormal
              contradiction

theorem closeSwitchExec
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {policyCondition executedCondition : Expr Op}
    {policyCases executedCases : List (Literal × Block Op)}
    {policyDefault executedDefault : Option (Block Op)} {value : U256}
    {source sourceFinal target : WordEnv}
    {sourceConditionState sourceFinalState targetState : EvmState}
    {outcome : Outcome} {sourceFuns : FunEnv G}
    {exitCopies : Block Op} {cutoff : Nat}
    (hcondition : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.expr policyCondition) (.expr executedCondition)
      (.eres (.vals [value] sourceConditionState)) sourceFuns targetState
      exitCopies cutoff)
    (hbodyClose : ∀ {targetConditionState},
      EvalExpr D (spillFuns layout.slots sourceFuns) target targetState
          (rewriteExpr layout.slots frame.owner executedCondition)
          (.vals [value] targetConditionState) →
        ControlLiveRel (base := base) (reserved := reserved)
          selected layout frame signature cuts live
          source sourceConditionState target targetConditionState →
        StepSimResult (base := base) (reserved := reserved)
          globalDeclared selected layout frame signature cuts live exitNames
          source target
          (.stmt (.block (selectSwitch G value policyCases policyDefault)))
          (.stmt (.block (selectSwitch G value executedCases executedDefault)))
          (.sres sourceFinal sourceFinalState outcome) sourceFuns
          targetConditionState exitCopies cutoff) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.stmt (.switch policyCondition policyCases policyDefault))
      (.stmt (.switch executedCondition executedCases executedDefault))
      (.sres sourceFinal sourceFinalState outcome) sourceFuns targetState
      exitCopies cutoff := by
  obtain ⟨targetConditionResult, htargetCondition, hconditionResult,
    haboveCondition⟩ := hcondition
  cases targetConditionResult with
  | sres targetFinal' targetFinalState targetOutcome =>
      simp [ResultControlRel] at hconditionResult
  | eres targetConditionResult' =>
      cases targetConditionResult' with
      | halt targetConditionState => simp [ResultControlRel] at hconditionResult
      | vals targetValues targetConditionState =>
          rcases hconditionResult with
            ⟨hvalues, hcontrol, horigin, hexitBound, hexitSignature⟩
          subst targetValues
          obtain ⟨targetBodyResult, htargetBody, hbodyResult, haboveBody⟩ :=
            hbodyClose htargetCondition hcontrol
          cases targetBodyResult with
          | eres targetExpressionResult => simp [ResultControlRel] at hbodyResult
          | sres targetBody targetFinalState targetOutcome =>
              rcases hbodyResult with
                ⟨finalLive, houtcome, hfinalControl, hfinalOrigin,
                  hfinalBound, hfinalSignature, hleave, hblock, hnormal⟩
              subst targetOutcome
              have htargetBody' : ExecStmts D
                  (spillFuns layout.slots sourceFuns) target targetConditionState
                  [.block (rewriteStmts layout.slots frame.owner exitCopies
                    (selectSwitch G value executedCases executedDefault))]
                  targetBody targetFinalState outcome := by
                simpa [rewriteCode, rewriteStmt] using htargetBody
              have hselected : ExecStmt D (spillFuns layout.slots sourceFuns)
                  target targetConditionState
                  (.block (selectSwitch D value
                    (rewriteCases layout.slots frame.owner exitCopies executedCases)
                    (executedDefault.map
                      (rewriteStmts layout.slots frame.owner exitCopies))))
                  targetBody targetFinalState outcome := by
                rw [rewrite_selectSwitch]
                exact execStmt_of_singleton htargetBody'
              refine ⟨.sres targetBody targetFinalState outcome, ?_, ?_,
                haboveCondition.trans haboveBody⟩
              · have hstep := execStmts_singleton
                    (Step.switchExec htargetCondition hselected)
                cases executedDefault <;>
                  simpa [rewriteCode, rewriteStmt] using hstep
              · refine ⟨finalLive, rfl, hfinalControl, hfinalOrigin,
                  hfinalBound, hfinalSignature, hleave, ?_, ?_⟩
                · intro body heq
                  cases heq
                intro hout
                have := hnormal hout
                calc
                  finalLive = live := by
                    simpa [liveAfterCode, liveStmt] using this
                  _ = liveAfterCode selected frame.owner live
                      (.stmt (.switch policyCondition policyCases policyDefault)) := by
                    simp [liveAfterCode, liveStmt.eq_def]

theorem closeLoopDone
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {policyCondition executedCondition : Expr Op}
    {policyPost policyBody executedPost executedBody : Block Op} {value : U256}
    {source target : WordEnv} {sourceFinalState targetState : EvmState}
    {sourceFuns : FunEnv G} {exitCopies : Block Op} {cutoff : Nat}
    (hexpr : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.expr policyCondition) (.expr executedCondition)
      (.eres (.vals [value] sourceFinalState)) sourceFuns targetState
      exitCopies cutoff)
    (hzero : value = Dialect.zero G) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.loop policyCondition policyPost policyBody)
      (.loop executedCondition executedPost executedBody)
      (.sres source sourceFinalState .normal) sourceFuns targetState
      exitCopies cutoff := by
  obtain ⟨targetResult, htarget, hresult, habove⟩ := hexpr
  cases targetResult with
  | sres targetFinal targetFinalState targetOutcome =>
      simp [ResultControlRel] at hresult
  | eres targetExprResult =>
      cases targetExprResult with
      | halt targetFinalState => simp [ResultControlRel] at hresult
      | vals targetValues targetFinalState =>
          rcases hresult with
            ⟨hvalues, hcontrol, horigin, hexitBound, hexitSignature⟩
          have hzero' : value = (0 : U256) := by
            change value = (0 : U256) at hzero
            exact hzero
          subst value
          subst targetValues
          refine ⟨.sres target targetFinalState .normal, ?_, ?_, habove⟩
          · simpa [rewriteCode] using
              (Step.loopDone htarget rfl : ExecLoop D
                (spillFuns layout.slots sourceFuns) target targetState
                (rewriteExpr layout.slots frame.owner executedCondition)
                (rewriteStmts layout.slots frame.owner exitCopies executedPost)
                (rewriteStmts layout.slots frame.owner exitCopies executedBody)
                target targetFinalState .normal)
          · refine ⟨live, rfl, hcontrol, horigin, hexitBound,
              hexitSignature, ?_, ?_, ?_⟩
            · intro hleave
              contradiction
            · intro body heq
              cases heq
            · intro _
              rfl

theorem closeLoopCondHalt
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {policyCondition executedCondition : Expr Op}
    {policyPost policyBody executedPost executedBody : Block Op}
    {source target : WordEnv} {sourceFinalState targetState : EvmState}
    {sourceFuns : FunEnv G} {exitCopies : Block Op} {cutoff : Nat}
    (hexpr : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.expr policyCondition) (.expr executedCondition)
      (.eres (.halt sourceFinalState)) sourceFuns targetState exitCopies cutoff) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.loop policyCondition policyPost policyBody)
      (.loop executedCondition executedPost executedBody)
      (.sres source sourceFinalState .halt) sourceFuns targetState
      exitCopies cutoff := by
  obtain ⟨targetResult, htarget, hresult, habove⟩ := hexpr
  cases targetResult with
  | sres targetFinal targetFinalState targetOutcome =>
      simp [ResultControlRel] at hresult
  | eres targetExprResult =>
      cases targetExprResult with
      | vals targetValues targetFinalState => simp [ResultControlRel] at hresult
      | halt targetFinalState =>
          rcases hresult with
            ⟨hcontrol, horigin, hexitBound, hexitSignature⟩
          refine ⟨.sres target targetFinalState .halt, ?_, ?_, habove⟩
          · simpa [rewriteCode] using
              (Step.loopCondHalt htarget : ExecLoop D
                (spillFuns layout.slots sourceFuns) target targetState
                (rewriteExpr layout.slots frame.owner executedCondition)
                (rewriteStmts layout.slots frame.owner exitCopies executedPost)
                (rewriteStmts layout.slots frame.owner exitCopies executedBody)
                target targetFinalState .halt)
          · refine ⟨live, rfl, hcontrol, horigin, hexitBound,
              hexitSignature, ?_, ?_, ?_⟩
            · intro hleave
              contradiction
            · intro body heq
              cases heq
            · intro hnormal
              contradiction

/-- Shared shell for loop-body outcomes that propagate unchanged (`leave` and
`halt`).  Catching `break`/`continue` needs the stronger lexical-block live
fact retained by the capstone's block branch and is intentionally separate. -/
theorem closeLoopTerminalSame
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {policyCondition executedCondition : Expr Op}
    {policyPost policyBody executedPost executedBody : Block Op} {value : U256}
    {source sourceFinal target : WordEnv}
    {sourceConditionState sourceFinalState targetState : EvmState}
    {outcome : Outcome} {sourceFuns : FunEnv G}
    {exitCopies : Block Op} {cutoff : Nat}
    (hcondition : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.expr policyCondition) (.expr executedCondition)
      (.eres (.vals [value] sourceConditionState)) sourceFuns targetState
      exitCopies cutoff)
    (_hnonzero : value ≠ Dialect.zero G) (hnonnormal : outcome ≠ .normal)
    (hbodyClose : ∀ {targetConditionState},
      EvalExpr D (spillFuns layout.slots sourceFuns) target targetState
          (rewriteExpr layout.slots frame.owner executedCondition)
          (.vals [value] targetConditionState) →
        ControlLiveRel (base := base) (reserved := reserved)
          selected layout frame signature cuts live
          source sourceConditionState target targetConditionState →
        StepSimResult (base := base) (reserved := reserved)
          globalDeclared selected layout frame signature cuts live exitNames
          source target (.stmt (.block policyBody)) (.stmt (.block executedBody))
          (.sres sourceFinal sourceFinalState outcome) sourceFuns
          targetConditionState exitCopies cutoff)
    (hbuild : ∀ {targetConditionState targetFinalState targetFinal},
      EvalExpr D (spillFuns layout.slots sourceFuns) target targetState
          (rewriteExpr layout.slots frame.owner executedCondition)
          (.vals [value] targetConditionState) →
        ExecStmt D (spillFuns layout.slots sourceFuns) target targetConditionState
          (.block (rewriteStmts layout.slots frame.owner exitCopies executedBody))
          targetFinal targetFinalState outcome →
        ExecLoop D (spillFuns layout.slots sourceFuns) target targetState
          (rewriteExpr layout.slots frame.owner executedCondition)
          (rewriteStmts layout.slots frame.owner exitCopies executedPost)
          (rewriteStmts layout.slots frame.owner exitCopies executedBody)
          targetFinal targetFinalState outcome) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.loop policyCondition policyPost policyBody)
      (.loop executedCondition executedPost executedBody)
      (.sres sourceFinal sourceFinalState outcome) sourceFuns targetState
      exitCopies cutoff := by
  obtain ⟨targetConditionResult, htargetCondition, hconditionResult,
    haboveCondition⟩ := hcondition
  cases targetConditionResult with
  | sres targetFinal' targetFinalState targetOutcome =>
      simp [ResultControlRel] at hconditionResult
  | eres targetConditionResult' =>
      cases targetConditionResult' with
      | halt targetConditionState => simp [ResultControlRel] at hconditionResult
      | vals targetValues targetConditionState =>
          rcases hconditionResult with
            ⟨hvalues, hcontrol, horigin, hexitBound, hexitSignature⟩
          subst targetValues
          obtain ⟨targetBodyResult, htargetBody, hbodyResult, haboveBody⟩ :=
            hbodyClose htargetCondition hcontrol
          cases targetBodyResult with
          | eres targetExpressionResult => simp [ResultControlRel] at hbodyResult
          | sres targetBody targetFinalState targetOutcome =>
              rcases hbodyResult with
                ⟨finalLive, houtcome, hfinalControl, hfinalOrigin,
                  hfinalBound, hfinalSignature, hleave, hblock, hnormal⟩
              subst targetOutcome
              have htargetBody' : ExecStmts D
                  (spillFuns layout.slots sourceFuns) target targetConditionState
                  [.block (rewriteStmts layout.slots frame.owner exitCopies
                    executedBody)] targetBody targetFinalState outcome := by
                simpa [rewriteCode, rewriteStmt] using htargetBody
              refine ⟨.sres targetBody targetFinalState outcome, ?_, ?_,
                haboveCondition.trans haboveBody⟩
              · exact hbuild htargetCondition
                  (execStmt_of_singleton htargetBody')
              · refine ⟨finalLive, rfl, hfinalControl, hfinalOrigin,
                  hfinalBound, hfinalSignature, hleave, ?_, ?_⟩
                · intro body heq
                  cases heq
                intro hnormal'
                exact False.elim (hnonnormal hnormal')

theorem closeLoopBreak
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {policyCondition executedCondition : Expr Op}
    {policyPost policyBody executedPost executedBody : Block Op} {value : U256}
    {source sourceFinal target : WordEnv}
    {sourceConditionState sourceFinalState targetState : EvmState}
    {sourceFuns : FunEnv G} {exitCopies : Block Op} {cutoff : Nat}
    (hcondition : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.expr policyCondition) (.expr executedCondition)
      (.eres (.vals [value] sourceConditionState)) sourceFuns targetState
      exitCopies cutoff)
    (hnonzero : value ≠ Dialect.zero G)
    (hbodyClose : ∀ {targetConditionState},
      EvalExpr D (spillFuns layout.slots sourceFuns) target targetState
          (rewriteExpr layout.slots frame.owner executedCondition)
          (.vals [value] targetConditionState) →
        ControlLiveRel (base := base) (reserved := reserved)
          selected layout frame signature cuts live
          source sourceConditionState target targetConditionState →
        StepSimResult (base := base) (reserved := reserved)
          globalDeclared selected layout frame signature cuts live exitNames
          source target (.stmt (.block policyBody)) (.stmt (.block executedBody))
          (.sres sourceFinal sourceFinalState .break) sourceFuns
          targetConditionState exitCopies cutoff) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.loop policyCondition policyPost policyBody)
      (.loop executedCondition executedPost executedBody)
      (.sres sourceFinal sourceFinalState .normal) sourceFuns targetState
      exitCopies cutoff := by
  obtain ⟨targetConditionResult, htargetCondition, hconditionResult,
    haboveCondition⟩ := hcondition
  cases targetConditionResult with
  | sres targetFinal' targetFinalState targetOutcome =>
      simp [ResultControlRel] at hconditionResult
  | eres targetConditionResult' =>
      cases targetConditionResult' with
      | halt targetConditionState => simp [ResultControlRel] at hconditionResult
      | vals targetValues targetConditionState =>
          rcases hconditionResult with
            ⟨hvalues, hcontrol, horigin, hexitBound, hexitSignature⟩
          subst targetValues
          obtain ⟨targetBodyResult, htargetBody, hbodyResult, haboveBody⟩ :=
            hbodyClose htargetCondition hcontrol
          cases targetBodyResult with
          | eres targetExpressionResult => simp [ResultControlRel] at hbodyResult
          | sres targetBody targetFinalState targetOutcome =>
              rcases hbodyResult with
                ⟨finalLive, houtcome, hfinalControl, hfinalOrigin,
                  hfinalBound, hfinalSignature, hleave, hblock, hnormal⟩
              subst targetOutcome
              have hfinalLive : finalLive = live :=
                hblock policyBody rfl
              subst finalLive
              have htargetBody' : ExecStmts D
                  (spillFuns layout.slots sourceFuns) target targetConditionState
                  [.block (rewriteStmts layout.slots frame.owner exitCopies
                    executedBody)] targetBody targetFinalState .break := by
                simpa [rewriteCode, rewriteStmt] using htargetBody
              have hzero : Dialect.zero D = (0 : U256) := by
                change litValue (.number 0) = (0 : U256)
                decide
              have hnonzero' : value ≠ Dialect.zero D := by
                rw [hzero]
                change value ≠ (0 : U256) at hnonzero
                exact hnonzero
              refine ⟨.sres targetBody targetFinalState .normal, ?_, ?_,
                haboveCondition.trans haboveBody⟩
              · simpa [rewriteCode] using
                  (Step.loopBreak htargetCondition hnonzero'
                    (execStmt_of_singleton htargetBody'))
              · refine ⟨live, rfl, hfinalControl, hfinalOrigin,
                  hfinalBound, hfinalSignature, ?_, ?_, ?_⟩
                · intro hleave'
                  contradiction
                · intro body heq
                  cases heq
                · intro _
                  rfl

theorem closeLoopPostHalt
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {policyCondition executedCondition : Expr Op}
    {policyPost policyBody executedPost executedBody : Block Op} {value : U256}
    {source sourceBody sourcePost target : WordEnv}
    {sourceConditionState sourceBodyState sourcePostState targetState : EvmState}
    {bodyOutcome : Outcome} {sourceFuns : FunEnv G}
    {exitCopies : Block Op} {cutoff : Nat}
    (hcondition : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.expr policyCondition) (.expr executedCondition)
      (.eres (.vals [value] sourceConditionState)) sourceFuns targetState
      exitCopies cutoff)
    (hnonzero : value ≠ Dialect.zero G)
    (hbodyOutcome : bodyOutcome = .normal ∨ bodyOutcome = .continue)
    (hbodyClose : ∀ {targetConditionState},
      EvalExpr D (spillFuns layout.slots sourceFuns) target targetState
          (rewriteExpr layout.slots frame.owner executedCondition)
          (.vals [value] targetConditionState) →
        ControlLiveRel (base := base) (reserved := reserved)
          selected layout frame signature cuts live
          source sourceConditionState target targetConditionState →
        StepSimResult (base := base) (reserved := reserved)
          globalDeclared selected layout frame signature cuts live exitNames
          source target (.stmt (.block policyBody)) (.stmt (.block executedBody))
          (.sres sourceBody sourceBodyState bodyOutcome) sourceFuns
          targetConditionState exitCopies cutoff)
    (hpostClose : ∀ {targetBody targetBodyState},
      ControlLiveRel (base := base) (reserved := reserved)
          selected layout frame signature cuts live
          sourceBody sourceBodyState targetBody targetBodyState →
        EnvDeclaredOrigin globalDeclared sourceBody →
        NamesBound exitNames sourceBody →
        StepSimResult (base := base) (reserved := reserved)
          globalDeclared selected layout frame signature cuts live exitNames
          sourceBody targetBody (.stmt (.block policyPost))
          (.stmt (.block executedPost))
          (.sres sourcePost sourcePostState .halt) sourceFuns
          targetBodyState exitCopies cutoff) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.loop policyCondition policyPost policyBody)
      (.loop executedCondition executedPost executedBody)
      (.sres sourcePost sourcePostState .halt) sourceFuns targetState
      exitCopies cutoff := by
  obtain ⟨targetConditionResult, htargetCondition, hconditionResult,
    haboveCondition⟩ := hcondition
  cases targetConditionResult with
  | sres targetFinal' targetFinalState targetOutcome =>
      simp [ResultControlRel] at hconditionResult
  | eres targetConditionResult' =>
      cases targetConditionResult' with
      | halt targetConditionState => simp [ResultControlRel] at hconditionResult
      | vals targetValues targetConditionState =>
          rcases hconditionResult with
            ⟨hvalues, hcontrol, horigin, hexitBound, hexitSignature⟩
          subst targetValues
          obtain ⟨targetBodyResult, htargetBody, hbodyResult, haboveBody⟩ :=
            hbodyClose htargetCondition hcontrol
          cases targetBodyResult with
          | eres targetExpressionResult => simp [ResultControlRel] at hbodyResult
          | sres targetBody targetBodyState targetBodyOutcome =>
              rcases hbodyResult with
                ⟨bodyLive, houtcome, hbodyControl, hbodyOrigin,
                  hbodyBound, hbodySignature, hbodyLeave, hbodyBlock,
                  hbodyNormal⟩
              subst targetBodyOutcome
              have hbodyLiveEq : bodyLive = live := hbodyBlock policyBody rfl
              subst bodyLive
              obtain ⟨targetPostResult, htargetPost, hpostResult, habovePost⟩ :=
                hpostClose hbodyControl hbodyOrigin hbodyBound
              cases targetPostResult with
              | eres targetExpressionResult =>
                  simp [ResultControlRel] at hpostResult
              | sres targetPost targetPostState targetPostOutcome =>
                  rcases hpostResult with
                    ⟨postLive, hpostOutcome, hpostControl, hpostOrigin,
                      hpostBound, hpostSignature, hpostLeave, hpostBlock,
                      hpostNormal⟩
                  subst targetPostOutcome
                  have htargetBody' : ExecStmts D
                      (spillFuns layout.slots sourceFuns) target
                      targetConditionState
                      [.block (rewriteStmts layout.slots frame.owner exitCopies
                        executedBody)] targetBody targetBodyState bodyOutcome := by
                    simpa [rewriteCode, rewriteStmt] using htargetBody
                  have htargetPost' : ExecStmts D
                      (spillFuns layout.slots sourceFuns) targetBody
                      targetBodyState
                      [.block (rewriteStmts layout.slots frame.owner exitCopies
                        executedPost)] targetPost targetPostState .halt := by
                    simpa [rewriteCode, rewriteStmt] using htargetPost
                  have hzero : Dialect.zero D = (0 : U256) := by
                    change litValue (.number 0) = (0 : U256)
                    decide
                  have hnonzero' : value ≠ Dialect.zero D := by
                    rw [hzero]
                    change value ≠ (0 : U256) at hnonzero
                    exact hnonzero
                  refine ⟨.sres targetPost targetPostState .halt, ?_, ?_,
                    haboveCondition.trans (haboveBody.trans habovePost)⟩
                  · simpa [rewriteCode] using
                      (Step.loopPostHalt htargetCondition hnonzero'
                        (execStmt_of_singleton htargetBody') hbodyOutcome
                        (execStmt_of_singleton htargetPost'))
                  · refine ⟨postLive, rfl, hpostControl, hpostOrigin,
                      hpostBound, hpostSignature, hpostLeave, ?_, ?_⟩
                    · intro body heq
                      cases heq
                    · intro hnormal
                      contradiction

theorem closeLoopStep
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {policyCondition executedCondition : Expr Op}
    {policyPost policyBody executedPost executedBody : Block Op} {value : U256}
    {source sourceBody sourcePost sourceFinal target : WordEnv}
    {sourceConditionState sourceBodyState sourcePostState sourceFinalState
      targetState : EvmState}
    {bodyOutcome outcome : Outcome} {sourceFuns : FunEnv G}
    {exitCopies : Block Op} {cutoff : Nat}
    (hcondition : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.expr policyCondition) (.expr executedCondition)
      (.eres (.vals [value] sourceConditionState)) sourceFuns targetState
      exitCopies cutoff)
    (hnonzero : value ≠ Dialect.zero G)
    (hbodyOutcome : bodyOutcome = .normal ∨ bodyOutcome = .continue)
    (hbodyClose : ∀ {targetConditionState},
      EvalExpr D (spillFuns layout.slots sourceFuns) target targetState
          (rewriteExpr layout.slots frame.owner executedCondition)
          (.vals [value] targetConditionState) →
        ControlLiveRel (base := base) (reserved := reserved)
          selected layout frame signature cuts live
          source sourceConditionState target targetConditionState →
        StepSimResult (base := base) (reserved := reserved)
          globalDeclared selected layout frame signature cuts live exitNames
          source target (.stmt (.block policyBody)) (.stmt (.block executedBody))
          (.sres sourceBody sourceBodyState bodyOutcome) sourceFuns
          targetConditionState exitCopies cutoff)
    (hpostClose : ∀ {targetBody targetBodyState},
      ControlLiveRel (base := base) (reserved := reserved)
          selected layout frame signature cuts live
          sourceBody sourceBodyState targetBody targetBodyState →
        EnvDeclaredOrigin globalDeclared sourceBody →
        NamesBound exitNames sourceBody →
        StepSimResult (base := base) (reserved := reserved)
          globalDeclared selected layout frame signature cuts live exitNames
          sourceBody targetBody (.stmt (.block policyPost))
          (.stmt (.block executedPost))
          (.sres sourcePost sourcePostState .normal) sourceFuns
          targetBodyState exitCopies cutoff)
    (hloopClose : ∀ {targetPost targetPostState},
      ControlLiveRel (base := base) (reserved := reserved)
          selected layout frame signature cuts live
          sourcePost sourcePostState targetPost targetPostState →
        EnvDeclaredOrigin globalDeclared sourcePost →
        NamesBound exitNames sourcePost →
        StepSimResult (base := base) (reserved := reserved)
          globalDeclared selected layout frame signature cuts live exitNames
          sourcePost targetPost (.loop policyCondition policyPost policyBody)
          (.loop executedCondition executedPost executedBody)
          (.sres sourceFinal sourceFinalState outcome) sourceFuns
          targetPostState exitCopies cutoff) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.loop policyCondition policyPost policyBody)
      (.loop executedCondition executedPost executedBody)
      (.sres sourceFinal sourceFinalState outcome) sourceFuns targetState
      exitCopies cutoff := by
  obtain ⟨targetConditionResult, htargetCondition, hconditionResult,
    haboveCondition⟩ := hcondition
  cases targetConditionResult with
  | sres targetFinal' targetFinalState targetOutcome =>
      simp [ResultControlRel] at hconditionResult
  | eres targetConditionResult' =>
      cases targetConditionResult' with
      | halt targetConditionState => simp [ResultControlRel] at hconditionResult
      | vals targetValues targetConditionState =>
          rcases hconditionResult with
            ⟨hvalues, hcontrol, horigin, hexitBound, hexitSignature⟩
          subst targetValues
          obtain ⟨targetBodyResult, htargetBody, hbodyResult, haboveBody⟩ :=
            hbodyClose htargetCondition hcontrol
          cases targetBodyResult with
          | eres targetExpressionResult => simp [ResultControlRel] at hbodyResult
          | sres targetBody targetBodyState targetBodyOutcome =>
              rcases hbodyResult with
                ⟨bodyLive, houtcome, hbodyControl, hbodyOrigin,
                  hbodyBound, hbodySignature, hbodyLeave, hbodyBlock,
                  hbodyNormal⟩
              subst targetBodyOutcome
              have hbodyLiveEq : bodyLive = live := hbodyBlock policyBody rfl
              subst bodyLive
              obtain ⟨targetPostResult, htargetPost, hpostResult, habovePost⟩ :=
                hpostClose hbodyControl hbodyOrigin hbodyBound
              cases targetPostResult with
              | eres targetExpressionResult =>
                  simp [ResultControlRel] at hpostResult
              | sres targetPost targetPostState targetPostOutcome =>
                  rcases hpostResult with
                    ⟨postLive, hpostOutcome, hpostControl, hpostOrigin,
                      hpostBound, hpostSignature, hpostLeave, hpostBlock,
                      hpostNormal⟩
                  subst targetPostOutcome
                  have hpostLiveEq : postLive = live :=
                    hpostBlock policyPost rfl
                  subst postLive
                  obtain ⟨targetLoopResult, htargetLoop, hloopResult,
                    haboveLoop⟩ :=
                    hloopClose hpostControl hpostOrigin hpostBound
                  have htargetBody' : ExecStmts D
                      (spillFuns layout.slots sourceFuns) target
                      targetConditionState
                      [.block (rewriteStmts layout.slots frame.owner exitCopies
                        executedBody)] targetBody targetBodyState bodyOutcome := by
                    simpa [rewriteCode, rewriteStmt] using htargetBody
                  have htargetPost' : ExecStmts D
                      (spillFuns layout.slots sourceFuns) targetBody
                      targetBodyState
                      [.block (rewriteStmts layout.slots frame.owner exitCopies
                        executedPost)] targetPost targetPostState .normal := by
                    simpa [rewriteCode, rewriteStmt] using htargetPost
                  have hzero : Dialect.zero D = (0 : U256) := by
                    change litValue (.number 0) = (0 : U256)
                    decide
                  have hnonzero' : value ≠ Dialect.zero D := by
                    rw [hzero]
                    change value ≠ (0 : U256) at hnonzero
                    exact hnonzero
                  cases targetLoopResult with
                  | eres targetExpressionResult =>
                      simp [ResultControlRel] at hloopResult
                  | sres targetFinal targetFinalState targetOutcome =>
                      have htargetLoop' : ExecLoop D
                          (spillFuns layout.slots sourceFuns) targetPost
                          targetPostState
                          (rewriteExpr layout.slots frame.owner executedCondition)
                          (rewriteStmts layout.slots frame.owner exitCopies
                            executedPost)
                          (rewriteStmts layout.slots frame.owner exitCopies
                            executedBody)
                          targetFinal targetFinalState targetOutcome := by
                        simpa [rewriteCode] using htargetLoop
                      refine ⟨.sres targetFinal targetFinalState targetOutcome,
                        ?_, hloopResult,
                        haboveCondition.trans
                          (haboveBody.trans (habovePost.trans haboveLoop))⟩
                      simpa [rewriteCode] using
                        (Step.loopStep htargetCondition hnonzero'
                          (execStmt_of_singleton htargetBody') hbodyOutcome
                          (execStmt_of_singleton htargetPost') htargetLoop')

/-! ## Outer `for` statement closure -/

theorem closeForLoopWith
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {policyInit executedInit : Block Op}
    {policyCondition executedCondition : Expr Op}
    {policyPost policyBody executedPost executedBody : Block Op}
    {source sourceInit sourceFinal target : WordEnv}
    {sourceState sourceInitState sourceFinalState targetState : EvmState}
    {outcome : Outcome} {sourceFuns : FunEnv G}
    {exitCopies : Block Op} {cutoff : Nat}
    (houter : ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (hexitBoundOuter : NamesBound exitNames source)
    (hexitSignature : ∀ name ∈ exitNames, name ∈ signature)
    (hinit : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature
      (scopeMark source target :: cuts) live exitNames source target
      (.stmts policyInit) (.stmts executedInit)
      (.sres sourceInit sourceInitState .normal)
      (hoist G executedInit :: sourceFuns) targetState exitCopies cutoff)
    (hloopClose : ∀ {targetInit targetInitState initLive},
      ControlLiveRel (base := base) (reserved := reserved)
          selected layout frame signature (scopeMark source target :: cuts)
          initLive sourceInit sourceInitState targetInit targetInitState →
        initLive = liveAfterCode selected frame.owner live (.stmts policyInit) →
        EnvDeclaredOrigin globalDeclared sourceInit →
        NamesBound exitNames sourceInit →
        StepSimResult (base := base) (reserved := reserved)
          globalDeclared selected layout frame signature
          (scopeMark source target :: cuts) initLive exitNames
          sourceInit targetInit
          (.loop policyCondition policyPost policyBody)
          (.loop executedCondition executedPost executedBody)
          (.sres sourceFinal sourceFinalState outcome)
          (hoist G executedInit :: sourceFuns) targetInitState
          exitCopies cutoff)
    (hkeys : (@YulSemantics.restore G source sourceFinal).map Prod.fst =
      source.map Prod.fst) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target
      (.stmt (.forLoop policyInit policyCondition policyPost policyBody))
      (.stmt (.forLoop executedInit executedCondition executedPost executedBody))
      (.sres (@YulSemantics.restore G source sourceFinal) sourceFinalState outcome)
      sourceFuns targetState exitCopies cutoff := by
  obtain ⟨targetInitResult, htargetInit, hinitResult, haboveInit⟩ := hinit
  cases targetInitResult with
  | eres targetExpressionResult => simp [ResultControlRel] at hinitResult
  | sres targetInit targetInitState targetInitOutcome =>
      rcases hinitResult with
        ⟨initLive, hinitOutcome, hinitControl, hinitOrigin,
          hinitBound, hinitSignature, hinitLeave, hinitBlock, hinitNormal⟩
      subst targetInitOutcome
      have hinitLive :
          initLive = liveAfterCode selected frame.owner live
            (.stmts policyInit) := hinitNormal rfl
      obtain ⟨targetLoopResult, htargetLoop, hloopResult, haboveLoop⟩ :=
        hloopClose hinitControl hinitLive hinitOrigin hinitBound
      cases targetLoopResult with
      | eres targetExpressionResult => simp [ResultControlRel] at hloopResult
      | sres targetFinal targetFinalState targetOutcome =>
          rcases hloopResult with
            ⟨finalLive, hloopOutcome, hfinalControl, hfinalOrigin,
              hfinalBound, hfinalSignature, hleave, hblock, hnormal⟩
          subst targetOutcome
          have htargetInit' : ExecStmts D
              (hoist D
                  (rewriteStmts layout.slots frame.owner exitCopies executedInit) ::
                spillFuns layout.slots sourceFuns)
              target targetState
              (rewriteStmts layout.slots frame.owner exitCopies executedInit)
              targetInit targetInitState .normal := by
            rw [← spillScope_hoist]
            simpa [spillFuns, rewriteCode] using htargetInit
          have htargetLoop' : ExecLoop D
              (hoist D
                  (rewriteStmts layout.slots frame.owner exitCopies executedInit) ::
                spillFuns layout.slots sourceFuns)
              targetInit targetInitState
              (rewriteExpr layout.slots frame.owner executedCondition)
              (rewriteStmts layout.slots frame.owner exitCopies executedPost)
              (rewriteStmts layout.slots frame.owner exitCopies executedBody)
              targetFinal targetFinalState outcome := by
            rw [← spillScope_hoist]
            simpa [spillFuns, rewriteCode] using htargetLoop
          have htargetFor : ExecStmt D (spillFuns layout.slots sourceFuns)
              target targetState
              (.forLoop
                (rewriteStmts layout.slots frame.owner exitCopies executedInit)
                (rewriteExpr layout.slots frame.owner executedCondition)
                (rewriteStmts layout.slots frame.owner exitCopies executedPost)
                (rewriteStmts layout.slots frame.owner exitCopies executedBody))
              (@YulSemantics.restore D target targetFinal)
              targetFinalState outcome :=
            Step.forLoop htargetInit' htargetLoop'
          have hpop : ControlLiveRel (base := base) (reserved := reserved)
              selected layout frame signature cuts live
              (@YulSemantics.restore G source sourceFinal) sourceFinalState
              (@YulSemantics.restore D target targetFinal) targetFinalState :=
            houter.popScope hfinalControl hkeys
          have horiginFinal : EnvDeclaredOrigin globalDeclared
              (@YulSemantics.restore G source sourceFinal) :=
            hfinalOrigin.restore
          have hexitBoundFinal : NamesBound exitNames
              (@YulSemantics.restore G source sourceFinal) :=
            NamesBound.restore hexitBoundOuter hkeys
          refine ⟨.sres (@YulSemantics.restore D target targetFinal)
            targetFinalState outcome, ?_, ?_, haboveInit.trans haboveLoop⟩
          · simpa [rewriteCode, rewriteStmt] using
              (execStmts_singleton htargetFor)
          · refine ⟨live, rfl, hpop, horiginFinal, hexitBoundFinal,
              hexitSignature, ?_, ?_, ?_⟩
            · intro hleaveOutcome
              exact returnsSynced_restore_of_scopedFrameRel
                hfinalControl.liveRel.frameRel (hleave hleaveOutcome)
                hexitBoundOuter hkeys hexitSignature hfinalControl.unique
            · intro body heq
              cases heq
            · intro _
              simp [liveAfterCode, liveStmt]

theorem closeForInitHaltWith
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {policyInit executedInit : Block Op}
    {policyCondition executedCondition : Expr Op}
    {policyPost policyBody executedPost executedBody : Block Op}
    {source sourceInit target : WordEnv}
    {sourceState sourceInitState targetState : EvmState}
    {sourceFuns : FunEnv G} {exitCopies : Block Op} {cutoff : Nat}
    (houter : ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (hexitBoundOuter : NamesBound exitNames source)
    (hexitSignature : ∀ name ∈ exitNames, name ∈ signature)
    (hinit : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature
      (scopeMark source target :: cuts) live exitNames source target
      (.stmts policyInit) (.stmts executedInit)
      (.sres sourceInit sourceInitState .halt)
      (hoist G executedInit :: sourceFuns) targetState exitCopies cutoff)
    (hkeys : (@YulSemantics.restore G source sourceInit).map Prod.fst =
      source.map Prod.fst) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target
      (.stmt (.forLoop policyInit policyCondition policyPost policyBody))
      (.stmt (.forLoop executedInit executedCondition executedPost executedBody))
      (.sres (@YulSemantics.restore G source sourceInit) sourceInitState .halt)
      sourceFuns targetState exitCopies cutoff := by
  obtain ⟨targetInitResult, htargetInit, hinitResult, habove⟩ := hinit
  cases targetInitResult with
  | eres targetExpressionResult => simp [ResultControlRel] at hinitResult
  | sres targetInit targetInitState targetInitOutcome =>
      rcases hinitResult with
        ⟨initLive, hinitOutcome, hinitControl, hinitOrigin,
          hinitBound, hinitSignature, hinitLeave, hinitBlock, hinitNormal⟩
      subst targetInitOutcome
      have htargetInit' : ExecStmts D
          (hoist D
              (rewriteStmts layout.slots frame.owner exitCopies executedInit) ::
            spillFuns layout.slots sourceFuns)
          target targetState
          (rewriteStmts layout.slots frame.owner exitCopies executedInit)
          targetInit targetInitState .halt := by
        rw [← spillScope_hoist]
        simpa [spillFuns, rewriteCode] using htargetInit
      have htargetFor : ExecStmt D (spillFuns layout.slots sourceFuns)
          target targetState
          (.forLoop
            (rewriteStmts layout.slots frame.owner exitCopies executedInit)
            (rewriteExpr layout.slots frame.owner executedCondition)
            (rewriteStmts layout.slots frame.owner exitCopies executedPost)
            (rewriteStmts layout.slots frame.owner exitCopies executedBody))
          (@YulSemantics.restore D target targetInit) targetInitState .halt :=
        Step.forInitHalt htargetInit'
      have hpop : ControlLiveRel (base := base) (reserved := reserved)
          selected layout frame signature cuts live
          (@YulSemantics.restore G source sourceInit) sourceInitState
          (@YulSemantics.restore D target targetInit) targetInitState :=
        houter.popScope hinitControl hkeys
      refine ⟨.sres (@YulSemantics.restore D target targetInit)
        targetInitState .halt, ?_, ?_, habove⟩
      · simpa [rewriteCode, rewriteStmt] using
          (execStmts_singleton htargetFor)
      · refine ⟨live, rfl, hpop, hinitOrigin.restore,
          NamesBound.restore hexitBoundOuter hkeys, hexitSignature, ?_, ?_, ?_⟩
        · intro hleaveOutcome
          contradiction
        · intro body heq
          cases heq
        · intro hnormalOutcome
          contradiction

end YulEvmCompiler.Optimizer.MemorySpillStepSound
