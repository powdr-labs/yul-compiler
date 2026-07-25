import YulEvmCompiler.Optimizer.Implementation.MemorySpillStepSound
import YulEvmCompiler.Optimizer.Implementation.MemorySpillBindingSound
set_option warningAsError true
/-!
# Statement closure packages for memory spilling

These lemmas isolate the result-package plumbing around statement constructors.
Constructor-specific target execution and binding transport remain explicit
premises, so the structural `Step` induction can discharge them with the
selected/all-unselected lemmas from `MemorySpillBindingSound`.
-/

namespace YulEvmCompiler.Optimizer.MemorySpillStmtStepSound

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer
open MemorySpillSelect
open MemorySpillRewriteSound
open MemorySpillFrameSound
open MemorySpillControlSound
open MemorySpillBindingSound
open MemorySpillExitSound
open MemorySpillStepSound

variable {base reserved : Nat}
variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "G" => guardedEvm calls creates base reserved
local notation "D" => evmWithExternal calls creates

/-- Close any normal statement once its constructor-specific target execution
and final control relation have been established. -/
theorem closeStmtNormalWith
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live finalLive : SpillSet}
    {exitNames : List Ident} {source target sourceFinal targetFinal : WordEnv}
    {targetState sourceFinalState targetFinalState : EvmState}
    {sourceFuns : FunEnv G} {policyStmt executedStmt : Stmt Op}
    {exitCopies : Block Op} {cutoff : Nat}
    (htarget : Step D (spillFuns layout.slots sourceFuns) target targetState
      (rewriteCode layout.slots frame.owner exitCopies (.stmt executedStmt))
      (.sres targetFinal targetFinalState .normal))
    (hcontrol : ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts finalLive
      sourceFinal sourceFinalState targetFinal targetFinalState)
    (horigin : EnvDeclaredOrigin globalDeclared sourceFinal)
    (hexitBound : NamesBound exitNames sourceFinal)
    (hexitSignature : ∀ name ∈ exitNames, name ∈ signature)
    (hfinalLive : finalLive =
      liveAfterCode selected frame.owner live (.stmt policyStmt))
    (habove : AboveUnchanged cutoff reserved targetState targetFinalState) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.stmt policyStmt) (.stmt executedStmt)
      (.sres sourceFinal sourceFinalState .normal) sourceFuns targetState
      exitCopies cutoff := by
  refine ⟨.sres targetFinal targetFinalState .normal, htarget, ?_, habove⟩
  exact ⟨finalLive, rfl, hcontrol, horigin, hexitBound, hexitSignature,
    by intro h; contradiction,
    by
      intro body hbody
      cases hbody
      simpa [liveAfterCode, liveStmt] using hfinalLive,
    fun _ => hfinalLive⟩

/-- Close any halting statement.  A halt leaves the dynamic exit invariants at
the environment in which its expression was evaluated. -/
theorem closeStmtHaltWith
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {source target : WordEnv}
    {targetState sourceFinalState targetFinalState : EvmState}
    {sourceFuns : FunEnv G} {policyStmt executedStmt : Stmt Op}
    {exitCopies : Block Op} {cutoff : Nat}
    (htarget : Step D (spillFuns layout.slots sourceFuns) target targetState
      (rewriteCode layout.slots frame.owner exitCopies (.stmt executedStmt))
      (.sres target targetFinalState .halt))
    (hcontrol : ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceFinalState target targetFinalState)
    (horigin : EnvDeclaredOrigin globalDeclared source)
    (hexitBound : NamesBound exitNames source)
    (hexitSignature : ∀ name ∈ exitNames, name ∈ signature)
    (habove : AboveUnchanged cutoff reserved targetState targetFinalState) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.stmt policyStmt) (.stmt executedStmt)
      (.sres source sourceFinalState .halt) sourceFuns targetState
      exitCopies cutoff := by
  refine ⟨.sres target targetFinalState .halt, htarget, ?_, habove⟩
  exact ⟨live, rfl, hcontrol, horigin, hexitBound, hexitSignature,
    by intro h; contradiction, by simp, by intro h; contradiction⟩

/-- Adapt a halting expression induction hypothesis to a let declaration.
The execution builder selects `execMultiLetHalt` or
`execSelectedTempBlockHalt` according to the binding dichotomy. -/
theorem closeLetHaltWith
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames names : List Ident} {source target : WordEnv}
    {sourceFinalState targetState : EvmState} {sourceFuns : FunEnv G}
    {policyExpr executedExpr : Expr Op} {exitCopies : Block Op} {cutoff : Nat}
    (hexpr : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.expr policyExpr) (.expr executedExpr)
      (.eres (.halt sourceFinalState)) sourceFuns targetState exitCopies cutoff)
    (hbuild : ∀ targetFinalState,
      EvalExpr D (spillFuns layout.slots sourceFuns) target targetState
        (rewriteExpr layout.slots frame.owner executedExpr) (.halt targetFinalState) →
      Step D (spillFuns layout.slots sourceFuns) target targetState
        (rewriteCode layout.slots frame.owner exitCopies
          (.stmt (.letDecl names (some executedExpr))))
        (.sres target targetFinalState .halt)) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.stmt (.letDecl names (some policyExpr)))
      (.stmt (.letDecl names (some executedExpr)))
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
          exact closeStmtHaltWith (hbuild targetFinalState htarget) hcontrol
            horigin hexitBound hexitSignature habove

/-- Assignment analogue of `closeLetHaltWith`. -/
theorem closeAssignHaltWith
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames names : List Ident} {source target : WordEnv}
    {sourceFinalState targetState : EvmState} {sourceFuns : FunEnv G}
    {policyExpr executedExpr : Expr Op} {exitCopies : Block Op} {cutoff : Nat}
    (hexpr : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.expr policyExpr) (.expr executedExpr)
      (.eres (.halt sourceFinalState)) sourceFuns targetState exitCopies cutoff)
    (hbuild : ∀ targetFinalState,
      EvalExpr D (spillFuns layout.slots sourceFuns) target targetState
        (rewriteExpr layout.slots frame.owner executedExpr) (.halt targetFinalState) →
      Step D (spillFuns layout.slots sourceFuns) target targetState
        (rewriteCode layout.slots frame.owner exitCopies
          (.stmt (.assign names executedExpr)))
        (.sres target targetFinalState .halt)) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.stmt (.assign names policyExpr))
      (.stmt (.assign names executedExpr))
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
          exact closeStmtHaltWith (hbuild targetFinalState htarget) hcontrol
            horigin hexitBound hexitSignature habove

/-! ## Binding-result adapters -/

/-- The zero-initialized declaration case has no expression child; this
specialization records its exact source and rewritten statement shapes. -/
theorem closeLetZeroWith
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live finalLive : SpillSet}
    {exitNames names : List Ident} {source target targetFinal : WordEnv}
    {sourceState targetState targetFinalState : EvmState}
    {sourceFuns : FunEnv G} {executedStmt : Stmt Op}
    {exitCopies : Block Op} {cutoff : Nat}
    (htarget : Step D (spillFuns layout.slots sourceFuns) target targetState
      (rewriteCode layout.slots frame.owner exitCopies (.stmt executedStmt))
      (.sres targetFinal targetFinalState .normal))
    (hcontrol : ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts finalLive
      (bindZeros G names ++ source) sourceState targetFinal targetFinalState)
    (horigin : EnvDeclaredOrigin globalDeclared (bindZeros G names ++ source))
    (hexitBound : NamesBound exitNames (bindZeros G names ++ source))
    (hexitSignature : ∀ name ∈ exitNames, name ∈ signature)
    (hfinalLive : finalLive = liveAfterCode selected frame.owner live
      (.stmt (.letDecl names none)))
    (habove : AboveUnchanged cutoff reserved targetState targetFinalState) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.stmt (.letDecl names none)) (.stmt executedStmt)
      (.sres (bindZeros G names ++ source) sourceState .normal)
      sourceFuns targetState exitCopies cutoff :=
  closeStmtNormalWith htarget hcontrol horigin hexitBound hexitSignature
    hfinalLive habove

/-- Unpack a value-producing expression simulation for a let declaration.
The continuation is where the selected/all-unselected binding dichotomy is
discharged with `execSelectedMultiLetVal` or `execUnselectedMultiLetVal`. -/
theorem closeLetValWith
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames names : List Ident} {values : List U256}
    {source target : WordEnv} {sourceFinalState targetState : EvmState}
    {sourceFuns : FunEnv G} {policyExpr executedExpr : Expr Op}
    {executedStmt : Stmt Op} {exitCopies : Block Op} {cutoff : Nat}
    (hexpr : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.expr policyExpr) (.expr executedExpr)
      (.eres (.vals values sourceFinalState)) sourceFuns targetState
      exitCopies cutoff)
    (hfinish : ∀ {targetValues : List U256} {targetFinalState : EvmState},
      targetValues = values →
      EvalExpr D (spillFuns layout.slots sourceFuns) target targetState
        (rewriteExpr layout.slots frame.owner executedExpr)
        (.vals targetValues targetFinalState) →
      ControlLiveRel (base := base) (reserved := reserved)
        selected layout frame signature cuts live
        source sourceFinalState target targetFinalState →
      EnvDeclaredOrigin globalDeclared source → NamesBound exitNames source →
      (∀ name ∈ exitNames, name ∈ signature) →
      AboveUnchanged cutoff reserved targetState targetFinalState →
      StepSimResult (base := base) (reserved := reserved)
        globalDeclared selected layout frame signature cuts live exitNames
        source target (.stmt (.letDecl names (some policyExpr)))
        (.stmt executedStmt)
        (.sres (names.zip values ++ source) sourceFinalState .normal)
        sourceFuns targetState exitCopies cutoff) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.stmt (.letDecl names (some policyExpr)))
      (.stmt executedStmt)
      (.sres (names.zip values ++ source) sourceFinalState .normal)
      sourceFuns targetState exitCopies cutoff := by
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
          exact hfinish hvalues htarget hcontrol horigin hexitBound
            hexitSignature habove

/-- Value-producing assignment analogue of `closeLetValWith`. -/
theorem closeAssignValWith
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames names : List Ident} {values : List U256}
    {source target : WordEnv} {sourceFinalState targetState : EvmState}
    {sourceFuns : FunEnv G} {policyExpr executedExpr : Expr Op}
    {executedStmt : Stmt Op} {exitCopies : Block Op} {cutoff : Nat}
    (hexpr : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.expr policyExpr) (.expr executedExpr)
      (.eres (.vals values sourceFinalState)) sourceFuns targetState
      exitCopies cutoff)
    (hfinish : ∀ {targetValues : List U256} {targetFinalState : EvmState},
      targetValues = values →
      EvalExpr D (spillFuns layout.slots sourceFuns) target targetState
        (rewriteExpr layout.slots frame.owner executedExpr)
        (.vals targetValues targetFinalState) →
      ControlLiveRel (base := base) (reserved := reserved)
        selected layout frame signature cuts live
        source sourceFinalState target targetFinalState →
      EnvDeclaredOrigin globalDeclared source → NamesBound exitNames source →
      (∀ name ∈ exitNames, name ∈ signature) →
      AboveUnchanged cutoff reserved targetState targetFinalState →
      StepSimResult (base := base) (reserved := reserved)
        globalDeclared selected layout frame signature cuts live exitNames
        source target (.stmt (.assign names policyExpr)) (.stmt executedStmt)
        (.sres (@VEnv.setMany G source names values) sourceFinalState .normal)
        sourceFuns targetState exitCopies cutoff) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.stmt (.assign names policyExpr)) (.stmt executedStmt)
      (.sres (@VEnv.setMany G source names values) sourceFinalState .normal)
      sourceFuns targetState exitCopies cutoff := by
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
          exact hfinish hvalues htarget hcontrol horigin hexitBound
            hexitSignature habove

/-! ## Statement-sequence closure -/

/-- Continue after a normally completing rewritten statement.  The callback
is exactly the generalized tail induction hypothesis, instantiated at the
existential target environment and state produced by the head simulation. -/
theorem closeSeqConsWith
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {source target sourceMiddle sourceFinal : WordEnv}
    {targetState sourceMiddleState sourceFinalState : EvmState}
    {sourceFuns : FunEnv G} {policyStmt executedStmt : Stmt Op}
    {policyRest executedRest : Block Op} {outcome : Outcome}
    {exitCopies : Block Op} {cutoff : Nat}
    (hhead : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.stmt policyStmt) (.stmt executedStmt)
      (.sres sourceMiddle sourceMiddleState .normal) sourceFuns targetState
      exitCopies cutoff)
    (htail : ∀ {targetMiddle : WordEnv} {targetMiddleState : EvmState},
      ResultControlRel (base := base) (reserved := reserved)
        (calls := calls) (creates := creates)
        globalDeclared selected layout frame signature cuts live exitNames
        source target (.stmt policyStmt)
        (.sres sourceMiddle sourceMiddleState .normal)
        (.sres targetMiddle targetMiddleState .normal) →
      ResAboveUnchanged (calls := calls) (creates := creates)
        cutoff reserved targetState
        (.sres targetMiddle targetMiddleState .normal) →
      StepSimResult (base := base) (reserved := reserved)
        globalDeclared selected layout frame signature cuts
        (liveStmt selected frame.owner live policyStmt).2 exitNames
        sourceMiddle targetMiddle (.stmts policyRest) (.stmts executedRest)
        (.sres sourceFinal sourceFinalState outcome) sourceFuns targetMiddleState
        exitCopies cutoff) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.stmts (policyStmt :: policyRest))
      (.stmts (executedStmt :: executedRest))
      (.sres sourceFinal sourceFinalState outcome) sourceFuns targetState
      exitCopies cutoff := by
  obtain ⟨targetHeadResult, htargetHead, hheadResult, haboveHead⟩ := hhead
  cases targetHeadResult with
  | eres targetExprResult => simp [ResultControlRel] at hheadResult
  | sres targetMiddle targetMiddleState targetOutcome =>
      rcases hheadResult with
        ⟨headLive, houtcome, hheadControl, horigin, hexitBound,
          hexitSignature, hleave, hblock, hnormal⟩
      subst targetOutcome
      have hheadResult' : ResultControlRel (base := base) (reserved := reserved)
          globalDeclared selected layout frame signature cuts live exitNames
          source target (.stmt policyStmt)
          (.sres sourceMiddle sourceMiddleState .normal)
          (.sres targetMiddle targetMiddleState .normal) :=
        ⟨headLive, rfl, hheadControl, horigin, hexitBound, hexitSignature,
          hleave, hblock, hnormal⟩
      obtain ⟨targetTailResult, htargetTail, htailResult, haboveTail⟩ :=
        htail hheadResult' haboveHead
      cases targetTailResult with
      | eres targetExprResult => simp [ResultControlRel] at htailResult
      | sres targetFinal targetFinalState targetFinalOutcome =>
          have hheadExec : ExecStmts D (spillFuns layout.slots sourceFuns)
              target targetState
              (rewriteStmt layout.slots frame.owner exitCopies executedStmt)
              targetMiddle targetMiddleState .normal := by
            simpa [rewriteCode] using htargetHead
          have htailExec : ExecStmts D (spillFuns layout.slots sourceFuns)
              targetMiddle targetMiddleState
              (rewriteStmts layout.slots frame.owner exitCopies executedRest)
              targetFinal targetFinalState targetFinalOutcome := by
            simpa [rewriteCode] using htargetTail
          have htarget := closeRewriteStmts_cons_normal hheadExec htailExec
          refine ⟨.sres targetFinal targetFinalState targetFinalOutcome, ?_,
            ?_, ?_⟩
          · simpa [rewriteCode] using htarget
          · simpa [ResultControlRel, liveAfterCode, liveStmts] using htailResult
          · exact haboveHead.trans haboveTail

/-- Close a statement sequence when its first statement exits early. -/
theorem closeSeqStop
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {source target sourceFinal : WordEnv}
    {sourceFinalState targetState : EvmState} {sourceFuns : FunEnv G}
    {policyStmt executedStmt : Stmt Op} {policyRest executedRest : Block Op}
    {outcome : Outcome} (hearly : outcome ≠ .normal)
    {exitCopies : Block Op} {cutoff : Nat}
    (hhead : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.stmt policyStmt) (.stmt executedStmt)
      (.sres sourceFinal sourceFinalState outcome) sourceFuns targetState
      exitCopies cutoff) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.stmts (policyStmt :: policyRest))
      (.stmts (executedStmt :: executedRest))
      (.sres sourceFinal sourceFinalState outcome) sourceFuns targetState
      exitCopies cutoff := by
  obtain ⟨targetHeadResult, htargetHead, hheadResult, habove⟩ := hhead
  cases targetHeadResult with
  | eres targetExprResult => simp [ResultControlRel] at hheadResult
  | sres targetFinal targetFinalState targetOutcome =>
      rcases hheadResult with
        ⟨finalLive, houtcome, hcontrol, horigin, hexitBound,
          hexitSignature, hleave, _hblock, hnormal⟩
      subst targetOutcome
      have hheadExec : ExecStmts D (spillFuns layout.slots sourceFuns)
          target targetState
          (rewriteStmt layout.slots frame.owner exitCopies executedStmt)
          targetFinal targetFinalState outcome := by
        simpa [rewriteCode] using htargetHead
      have htarget := closeRewriteStmts_cons_early
        (rest := executedRest) hheadExec hearly
      refine ⟨.sres targetFinal targetFinalState outcome, ?_, ?_, habove⟩
      · simpa [rewriteCode] using htarget
      · refine ⟨finalLive, rfl, hcontrol, horigin, hexitBound,
          hexitSignature, hleave, by simp, ?_⟩
        intro hnormalOutcome
        exact (hearly hnormalOutcome).elim

/-! ## Lexical block closure -/

/-- Restore both environments after a block and pop the matching spill-scope
cut.  The key equality is the ordinary Yul block-domain invariant. -/
theorem closeBlockWith
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident} {source target innerSource : WordEnv}
    {sourceState targetState innerSourceState : EvmState}
    {sourceFuns : FunEnv G} {policyBody executedBody : Block Op}
    {outcome : Outcome} {exitCopies : Block Op} {cutoff : Nat}
    (houter : ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (hexitBoundOuter : NamesBound exitNames source)
    (hexitSignature : ∀ name ∈ exitNames, name ∈ signature)
    (hbody : StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature
      (scopeMark source target :: cuts) live exitNames source target
      (.stmts policyBody) (.stmts executedBody)
      (.sres innerSource innerSourceState outcome)
      (hoist G executedBody :: sourceFuns) targetState exitCopies cutoff)
    (hkeys : (@YulSemantics.restore G source innerSource).map Prod.fst =
      source.map Prod.fst) :
    StepSimResult (base := base) (reserved := reserved)
      globalDeclared selected layout frame signature cuts live exitNames
      source target (.stmt (.block policyBody)) (.stmt (.block executedBody))
      (.sres (@YulSemantics.restore G source innerSource) innerSourceState outcome)
      sourceFuns targetState exitCopies cutoff := by
  obtain ⟨targetBodyResult, htargetBody, hbodyResult, habove⟩ := hbody
  cases targetBodyResult with
  | eres targetExprResult => simp [ResultControlRel] at hbodyResult
  | sres innerTarget innerTargetState targetOutcome =>
      rcases hbodyResult with
        ⟨innerLive, houtcome, hinner, horiginInner, hexitBoundInner,
          _hexitSignatureInner, hleave, _hblock, _hnormal⟩
      subst targetOutcome
      have hbodyExec : ExecStmts D
          (spillFuns layout.slots (hoist G executedBody :: sourceFuns))
          target targetState
          (rewriteStmts layout.slots frame.owner exitCopies executedBody)
          innerTarget innerTargetState outcome := by
        simpa [rewriteCode] using htargetBody
      have htarget := execRewriteBlock hbodyExec
      have hpop : ControlLiveRel (base := base) (reserved := reserved)
          selected layout frame signature cuts live
          (@YulSemantics.restore G source innerSource) innerSourceState
          (@YulSemantics.restore D target innerTarget) innerTargetState :=
        houter.popScope hinner hkeys
      have horiginFinal : EnvDeclaredOrigin globalDeclared
          (@YulSemantics.restore G source innerSource) :=
        horiginInner.restore
      have hexitBoundFinal : NamesBound exitNames
          (@YulSemantics.restore G source innerSource) :=
        NamesBound.restore hexitBoundOuter hkeys
      refine ⟨.sres (@YulSemantics.restore D target innerTarget)
        innerTargetState outcome, ?_, ?_, habove⟩
      · simpa [rewriteCode] using htarget
      · refine ⟨live, rfl, hpop, horiginFinal, hexitBoundFinal,
          hexitSignature, ?_, ?_, ?_⟩
        · intro hleaveOutcome
          have hsyncedInner := hleave hleaveOutcome
          exact returnsSynced_restore_of_scopedFrameRel
            hinner.liveRel.frameRel hsyncedInner hexitBoundOuter hkeys
            hexitSignature hinner.unique
        · intro body _
          rfl
        · intro _
          simp [liveAfterCode, liveStmt]

/-! ## Capstone structural induction -/

/-- `execCode` preserves the outer statement code constructor in both origin
modes.  The statement payload itself may still differ after object-layout
resolution. -/
theorem execCode_stmt_inv
    {mode : MemorySpillOriginSound.OriginMode} {policyCode : Code Op}
    {executedStmt : Stmt Op}
    (heq : (.stmt executedStmt : Code Op) = execCode mode policyCode) :
    ∃ policyStmt, policyCode = .stmt policyStmt ∧
      (.stmt executedStmt : Code Op) = execCode mode (.stmt policyStmt) := by
  cases mode with
  | identity =>
      simp [execCode] at heq
      subst policyCode
      exact ⟨executedStmt, rfl, rfl⟩
  | «object» objectLayout =>
      cases policyCode with
      | expr policyExpr => simp [execCode] at heq
      | args policyArgs => simp [execCode] at heq
      | stmt policyStmt => exact ⟨policyStmt, rfl, heq⟩
      | stmts policyStmts => simp [execCode] at heq
      | loop policyCondition policyPost policyBody => simp [execCode] at heq

theorem execCode_expr_inv
    {mode : MemorySpillOriginSound.OriginMode} {policyCode : Code Op}
    {executedExpr : Expr Op}
    (heq : (.expr executedExpr : Code Op) = execCode mode policyCode) :
    ∃ policyExpr, policyCode = .expr policyExpr ∧
      (.expr executedExpr : Code Op) = execCode mode (.expr policyExpr) := by
  cases mode with
  | identity =>
      simp [execCode] at heq
      subst policyCode
      exact ⟨executedExpr, rfl, rfl⟩
  | «object» objectLayout =>
      cases policyCode with
      | expr policyExpr => exact ⟨policyExpr, rfl, heq⟩
      | args policyArgs => simp [execCode] at heq
      | stmt policyStmt => simp [execCode] at heq
      | stmts policyStmts => simp [execCode] at heq
      | loop policyCondition policyPost policyBody => simp [execCode] at heq

theorem execCode_stmts_inv
    {mode : MemorySpillOriginSound.OriginMode} {policyCode : Code Op}
    {executedStmts : Block Op}
    (heq : (.stmts executedStmts : Code Op) = execCode mode policyCode) :
    ∃ policyStmts, policyCode = .stmts policyStmts ∧
      (.stmts executedStmts : Code Op) = execCode mode (.stmts policyStmts) := by
  cases mode with
  | identity =>
      simp [execCode] at heq
      subst policyCode
      exact ⟨executedStmts, rfl, rfl⟩
  | «object» objectLayout =>
      cases policyCode with
      | expr policyExpr => simp [execCode] at heq
      | args policyArgs => simp [execCode] at heq
      | stmt policyStmt => simp [execCode] at heq
      | stmts policyStmts => exact ⟨policyStmts, rfl, heq⟩
      | loop policyCondition policyPost policyBody => simp [execCode] at heq

theorem execCode_args_inv
    {mode : MemorySpillOriginSound.OriginMode} {policyCode : Code Op}
    {executedArgs : List (Expr Op)}
    (heq : (.args executedArgs : Code Op) = execCode mode policyCode) :
    ∃ policyArgs, policyCode = .args policyArgs ∧
      (.args executedArgs : Code Op) = execCode mode (.args policyArgs) := by
  cases mode with
  | identity =>
      simp [execCode] at heq
      subst policyCode
      exact ⟨executedArgs, rfl, rfl⟩
  | «object» objectLayout =>
      cases policyCode with
      | expr policyExpr => simp [execCode] at heq
      | args policyArgs => exact ⟨policyArgs, rfl, heq⟩
      | stmt policyStmt => simp [execCode] at heq
      | stmts policyStmts => simp [execCode] at heq
      | loop policyCondition policyPost policyBody => simp [execCode] at heq

theorem execCode_loop_inv
    {mode : MemorySpillOriginSound.OriginMode} {policyCode : Code Op}
    {executedCondition : Expr Op} {executedPost executedBody : Block Op}
    (heq : (.loop executedCondition executedPost executedBody : Code Op) =
      execCode mode policyCode) :
    ∃ policyCondition policyPost policyBody,
      policyCode = .loop policyCondition policyPost policyBody ∧
      (.loop executedCondition executedPost executedBody : Code Op) =
        execCode mode (.loop policyCondition policyPost policyBody) := by
  cases mode with
  | identity =>
      simp [execCode] at heq
      subst policyCode
      exact ⟨executedCondition, executedPost, executedBody, rfl, rfl⟩
  | «object» objectLayout =>
      cases policyCode with
      | expr policyExpr => simp [execCode] at heq
      | args policyArgs => simp [execCode] at heq
      | stmt policyStmt => simp [execCode] at heq
      | stmts policyStmts => simp [execCode] at heq
      | loop policyCondition policyPost policyBody =>
          exact ⟨policyCondition, policyPost, policyBody, rfl, heq⟩

theorem resolveForLayoutExpr_eq_builtin_inv_local (objectLayout : EVM.Layout)
    {expression : Expr Op} {op : Op} {args : List (Expr Op)}
    (heq : resolveForLayoutExpr objectLayout expression = .builtin op args) :
    ∃ policyArgs, expression = .builtin op policyArgs ∧
      args = resolveForLayoutExprs objectLayout policyArgs := by
  cases expression with
  | lit literal => simp [resolveForLayoutExpr] at heq
  | var name => simp [resolveForLayoutExpr] at heq
  | call name callArgs => simp [resolveForLayoutExpr] at heq
  | builtin policyOp policyArgs =>
      simp only [resolveForLayoutExpr] at heq
      split at heq
      · cases heq
      · cases heq
      · injection heq with hop hargs
        subst hop
        exact ⟨policyArgs, rfl, hargs.symm⟩

theorem resolveForLayoutExpr_eq_call_inv_local (objectLayout : EVM.Layout)
    {expression : Expr Op} {name : Ident} {args : List (Expr Op)}
    (heq : resolveForLayoutExpr objectLayout expression = .call name args) :
    ∃ policyArgs, expression = .call name policyArgs ∧
      args = resolveForLayoutExprs objectLayout policyArgs := by
  cases expression with
  | lit literal => simp [resolveForLayoutExpr] at heq
  | var policyVar => simp [resolveForLayoutExpr] at heq
  | builtin op policyArgs =>
      simp only [resolveForLayoutExpr] at heq
      split at heq <;> cases heq
  | call policyName policyArgs =>
      simp [resolveForLayoutExpr] at heq
      rcases heq with ⟨rfl, hargs⟩
      exact ⟨policyArgs, rfl, hargs.symm⟩

theorem execCode_builtin_inv
    {mode : MemorySpillOriginSound.OriginMode} {policyCode : Code Op}
    {executedOp : Op} {executedArgs : List (Expr Op)}
    (heq : (.expr (.builtin executedOp executedArgs) : Code Op) =
      execCode mode policyCode) :
    ∃ policyArgs, policyCode = .expr (.builtin executedOp policyArgs) ∧
      (.args executedArgs : Code Op) = execCode mode (.args policyArgs) := by
  cases mode with
  | identity =>
      simp [execCode] at heq
      subst policyCode
      exact ⟨executedArgs, rfl, rfl⟩
  | «object» objectLayout =>
      cases policyCode with
      | expr policyExpr =>
          have heq' : resolveForLayoutExpr objectLayout policyExpr =
              .builtin executedOp executedArgs := by
            simpa [execCode] using heq.symm
          obtain ⟨policyArgs, hpolicy, hargs⟩ :=
            resolveForLayoutExpr_eq_builtin_inv_local objectLayout heq'
          subst policyExpr
          exact ⟨policyArgs, rfl, by simpa [execCode] using congrArg Code.args hargs⟩
      | args policyArgs => simp [execCode] at heq
      | stmt policyStmt => simp [execCode] at heq
      | stmts policyStmts => simp [execCode] at heq
      | loop policyCondition policyPost policyBody => simp [execCode] at heq

theorem execCode_call_inv
    {mode : MemorySpillOriginSound.OriginMode} {policyCode : Code Op}
    {executedName : Ident} {executedArgs : List (Expr Op)}
    (heq : (.expr (.call executedName executedArgs) : Code Op) =
      execCode mode policyCode) :
    ∃ policyArgs, policyCode = .expr (.call executedName policyArgs) ∧
      (.args executedArgs : Code Op) = execCode mode (.args policyArgs) := by
  cases mode with
  | identity =>
      simp [execCode] at heq
      subst policyCode
      exact ⟨executedArgs, rfl, rfl⟩
  | «object» objectLayout =>
      cases policyCode with
      | expr policyExpr =>
          have heq' : resolveForLayoutExpr objectLayout policyExpr =
              .call executedName executedArgs := by
            simpa [execCode] using heq.symm
          obtain ⟨policyArgs, hpolicy, hargs⟩ :=
            resolveForLayoutExpr_eq_call_inv_local objectLayout heq'
          subst policyExpr
          exact ⟨policyArgs, rfl, by simpa [execCode] using congrArg Code.args hargs⟩
      | args policyArgs => simp [execCode] at heq
      | stmt policyStmt => simp [execCode] at heq
      | stmts policyStmts => simp [execCode] at heq
      | loop policyCondition policyPost policyBody => simp [execCode] at heq

theorem execCode_let_some_inv
    {mode : MemorySpillOriginSound.OriginMode} {policyCode : Code Op}
    {executedNames : List Ident} {executedExpr : Expr Op}
    (heq : (.stmt (.letDecl executedNames (some executedExpr)) : Code Op) =
      execCode mode policyCode) :
    ∃ policyExpr,
      policyCode = .stmt (.letDecl executedNames (some policyExpr)) ∧
      (.expr executedExpr : Code Op) = execCode mode (.expr policyExpr) := by
  cases mode with
  | identity =>
      simp [execCode] at heq
      subst policyCode
      exact ⟨executedExpr, rfl, rfl⟩
  | «object» layout =>
      cases policyCode with
      | expr expression => simp [execCode] at heq
      | args args => simp [execCode] at heq
      | stmts statements => simp [execCode] at heq
      | loop condition post body => simp [execCode] at heq
      | stmt statement =>
          cases statement with
          | letDecl names value =>
              cases value with
              | none => simp [execCode] at heq
              | some policyExpr =>
                  simp [execCode] at heq
                  rcases heq with ⟨rfl, hexpr⟩
                  exact ⟨policyExpr, rfl, congrArg Code.expr hexpr⟩
          | block body => simp [execCode] at heq
          | funDef name params returns body => simp [execCode] at heq
          | assign names value => simp [execCode] at heq
          | cond condition body => simp [execCode] at heq
          | «switch» condition cases fallback => simp [execCode] at heq
          | forLoop init condition post body => simp [execCode] at heq
          | exprStmt expression => simp [execCode] at heq
          | «break» => simp [execCode] at heq
          | «continue» => simp [execCode] at heq
          | «leave» => simp [execCode] at heq

theorem execCode_let_none_inv
    {mode : MemorySpillOriginSound.OriginMode} {policyCode : Code Op}
    {executedNames : List Ident}
    (heq : (.stmt (.letDecl executedNames none) : Code Op) =
      execCode mode policyCode) :
    policyCode = .stmt (.letDecl executedNames none) := by
  cases mode with
  | identity =>
      simpa [execCode] using heq.symm
  | «object» layout =>
      cases policyCode with
      | expr expression => simp [execCode] at heq
      | args args => simp [execCode] at heq
      | stmts statements => simp [execCode] at heq
      | loop condition post body => simp [execCode] at heq
      | stmt statement =>
          cases statement with
          | letDecl names value =>
              cases value with
              | none =>
                  simp [execCode] at heq
                  exact congrArg (fun names =>
                    (.stmt (.letDecl names none) : Code Op)) heq.symm
              | some policyExpr => simp [execCode] at heq
          | block body => simp [execCode] at heq
          | funDef name params returns body => simp [execCode] at heq
          | assign names value => simp [execCode] at heq
          | cond condition body => simp [execCode] at heq
          | «switch» condition cases fallback => simp [execCode] at heq
          | forLoop init condition post body => simp [execCode] at heq
          | exprStmt expression => simp [execCode] at heq
          | «break» => simp [execCode] at heq
          | «continue» => simp [execCode] at heq
          | «leave» => simp [execCode] at heq

theorem execCode_assign_inv
    {mode : MemorySpillOriginSound.OriginMode} {policyCode : Code Op}
    {executedNames : List Ident} {executedExpr : Expr Op}
    (heq : (.stmt (.assign executedNames executedExpr) : Code Op) =
      execCode mode policyCode) :
    ∃ policyExpr,
      policyCode = .stmt (.assign executedNames policyExpr) ∧
      (.expr executedExpr : Code Op) = execCode mode (.expr policyExpr) := by
  cases mode with
  | identity =>
      simp [execCode] at heq
      subst policyCode
      exact ⟨executedExpr, rfl, rfl⟩
  | «object» layout =>
      cases policyCode with
      | expr expression => simp [execCode] at heq
      | args args => simp [execCode] at heq
      | stmts statements => simp [execCode] at heq
      | loop condition post body => simp [execCode] at heq
      | stmt statement =>
          cases statement with
          | assign names policyExpr =>
              simp [execCode] at heq
              rcases heq with ⟨rfl, hexpr⟩
              exact ⟨policyExpr, rfl, congrArg Code.expr hexpr⟩
          | block body => simp [execCode] at heq
          | funDef name params returns body => simp [execCode] at heq
          | letDecl names value => simp [execCode] at heq
          | cond condition body => simp [execCode] at heq
          | «switch» condition cases fallback => simp [execCode] at heq
          | forLoop init condition post body => simp [execCode] at heq
          | exprStmt expression => simp [execCode] at heq
          | «break» => simp [execCode] at heq
          | «continue» => simp [execCode] at heq
          | «leave» => simp [execCode] at heq

theorem execCode_args_cons_inv
    {mode : MemorySpillOriginSound.OriginMode} {policyCode : Code Op}
    {executedHead : Expr Op} {executedRest : List (Expr Op)}
    (heq : (.args (executedHead :: executedRest) : Code Op) =
      execCode mode policyCode) :
    ∃ policyHead policyRest,
      policyCode = .args (policyHead :: policyRest) ∧
      (.expr executedHead : Code Op) = execCode mode (.expr policyHead) ∧
      (.args executedRest : Code Op) = execCode mode (.args policyRest) := by
  cases mode with
  | identity =>
      simp [execCode] at heq
      subst policyCode
      exact ⟨executedHead, executedRest, rfl, rfl, rfl⟩
  | «object» objectLayout =>
      cases policyCode with
      | expr policyExpr => simp [execCode] at heq
      | args policyArgs =>
          cases policyArgs with
          | nil => simp [execCode, resolveForLayoutExprs] at heq
          | cons policyHead policyRest =>
              simp [execCode, resolveForLayoutExprs] at heq
              exact ⟨policyHead, policyRest, rfl, congrArg Code.expr heq.1,
                congrArg Code.args heq.2⟩
      | stmt policyStmt => simp [execCode] at heq
      | stmts policyStmts => simp [execCode] at heq
      | loop policyCondition policyPost policyBody => simp [execCode] at heq

theorem execCode_stmts_cons_inv
    {mode : MemorySpillOriginSound.OriginMode} {policyCode : Code Op}
    {executedHead : Stmt Op} {executedRest : Block Op}
    (heq : (.stmts (executedHead :: executedRest) : Code Op) =
      execCode mode policyCode) :
    ∃ policyHead policyRest,
      policyCode = .stmts (policyHead :: policyRest) ∧
      (.stmt executedHead : Code Op) = execCode mode (.stmt policyHead) ∧
      (.stmts executedRest : Code Op) = execCode mode (.stmts policyRest) := by
  cases mode with
  | identity =>
      simp [execCode] at heq
      subst policyCode
      exact ⟨executedHead, executedRest, rfl, rfl, rfl⟩
  | «object» objectLayout =>
      cases policyCode with
      | expr policyExpr => simp [execCode] at heq
      | args policyArgs => simp [execCode] at heq
      | stmt policyStmt => simp [execCode] at heq
      | stmts policyStmts =>
          cases policyStmts with
          | nil => simp [execCode] at heq
          | cons policyHead policyRest =>
              simp [execCode] at heq
              exact ⟨policyHead, policyRest, rfl, congrArg Code.stmt heq.1,
                congrArg Code.stmts heq.2⟩
      | loop policyCondition policyPost policyBody => simp [execCode] at heq

/-- Concrete structural simulation.  The constructor list is deliberately
spelled out: each placeholder is replaced branch-by-branch with the reusable
closures above and in `MemorySpillStepSound`. -/
theorem step_sim {raw : Block Op} {result : Result} {guards : List Nat}
    (hfacts : SpillFacts raw result guards)
    (hexternals : GuardedExternals calls creates result.base result.reserved)
    (mode : MemorySpillOriginSound.OriginMode)
    {sourceFuns : FunEnv
      (guardedEvm calls creates result.base result.reserved)}
    {source sourceState executedCode sourceResult}
    (hsource : Step (guardedEvm calls creates result.base result.reserved)
      sourceFuns source sourceState executedCode sourceResult) :
    StepSimMotive hfacts hexternals mode hsource := by
  induction hsource with
  | lit =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel _hcovered _hexitCopies
        hcutoff
      obtain ⟨policyExpr, rfl, _heq⟩ :=
        execCode_expr_inv hctx.motive.origin.executedCode_eq
      exact simulateCallFreeExprBranch hfacts hexternals hctx Step.lit (.lit _)
        hrel hcutoff
  | var hget =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel _hcovered _hexitCopies
        hcutoff
      obtain ⟨policyExpr, rfl, _heq⟩ :=
        execCode_expr_inv hctx.motive.origin.executedCode_eq
      exact simulateCallFreeExprBranch hfacts hexternals hctx (Step.var hget)
        (.var _) hrel hcutoff
  | builtinOk hargs hbuiltin ihArgs =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered hexitCopies
        hcutoff
      subst exitCopies
      obtain ⟨policyArgs, rfl, hargsEq⟩ :=
        execCode_builtin_inv hctx.motive.origin.executedCode_eq
      have hargsCtx := hctx.argsChild
        hctx.motive.origin.callOrigin.builtinArgs hctx.motive.envDeclared
        hctx.exitsBound
      rw [← hargsEq] at hargsCtx
      have hsim := ihArgs hargsCtx hrel hcovered rfl hcutoff
      exact closeBuiltinOkBranch hsim hbuiltin hexternals
        (fun _ _ hslot => SpillFacts.slotBounds hfacts hslot)
        (le_trans (frameCutoff_base_le result.base result.layout _) hcutoff)
  | builtinHalt hargs hbuiltin ihArgs =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered hexitCopies
        hcutoff
      subst exitCopies
      obtain ⟨policyArgs, rfl, hargsEq⟩ :=
        execCode_builtin_inv hctx.motive.origin.executedCode_eq
      have hargsCtx := hctx.argsChild
        hctx.motive.origin.callOrigin.builtinArgs hctx.motive.envDeclared
        hctx.exitsBound
      rw [← hargsEq] at hargsCtx
      have hsim := ihArgs hargsCtx hrel hcovered rfl hcutoff
      exact closeBuiltinHaltBranch hsim hbuiltin hexternals
        (fun _ _ hslot => SpillFacts.slotBounds hfacts hslot)
        (le_trans (frameCutoff_base_le result.base result.layout _) hcutoff)
  | builtinArgsHalt hargs ihArgs =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered _hexitCopies
        hcutoff
      obtain ⟨policyArgs, rfl, hargsEq⟩ :=
        execCode_builtin_inv hctx.motive.origin.executedCode_eq
      have hargsCtx := hctx.argsChild
        hctx.motive.origin.callOrigin.builtinArgs hctx.motive.envDeclared
        hctx.exitsBound
      rw [← hargsEq] at hargsCtx
      have hsim := ihArgs hargsCtx hrel hcovered rfl hcutoff
      exact closeBuiltinArgsHaltBranch hsim
  | callOk hargs hlookup hlength hbody houtcome ihArgs =>
      rename_i sourceFuns source sourceState fn args argvals sourceArgState
        decl closure sourceFinal sourceFinalState outcome ihBody
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered _hexitCopies
        hcutoff
      obtain ⟨policyArgs, rfl, hargsEq⟩ :=
        execCode_call_inv hctx.motive.origin.executedCode_eq
      have hargsCtx := hctx.argsChild
        hctx.motive.origin.callOrigin.callArgs hctx.motive.envDeclared
        hctx.exitsBound
      rw [← hargsEq] at hargsCtx
      have hargsSim := ihArgs hargsCtx hrel hcovered rfl hcutoff
      have hcalleeFrame := MemorySpillCallSound.covered_calleeFrame_mem
        hcovered hlookup
      obtain ⟨policyCallee0, hcalleeMem0, hframeEq0⟩ :=
        List.mem_map.mp hcalleeFrame
      have hnodup0 := frameSignaturesWF_frame hfacts.signatures_wf hcalleeMem0
      have hparamsEq : policyCallee0.params = decl.params := by
        have := congrArg Frame.params hframeEq0
        simpa [MemorySpillCallSound.calleeFrame] using this
      have hreturnsEq : policyCallee0.returns = decl.rets := by
        have := congrArg Frame.returns hframeEq0
        simpa [MemorySpillCallSound.calleeFrame] using this
      have hnodup : (decl.params ++ decl.rets).Nodup := by
        simpa [hparamsEq, hreturnsEq] using hnodup0
      obtain ⟨policyCallee, hcalleeMem, hframeEq, hclosureCovered,
          hbodyCtx⟩ := ControlStepContext.calleeBlock
            (selected := result.selection) hctx.selectedBindingsWF hcovered
            hlookup hlength hnodup
      have howner : policyCallee.owner = some fn := by
        have := congrArg Frame.owner hframeEq
        simpa [MemorySpillCallSound.calleeFrame] using this
      have hparams : policyCallee.params = decl.params := by
        have := congrArg Frame.params hframeEq
        simpa [MemorySpillCallSound.calleeFrame] using this
      have hreturns : policyCallee.returns = decl.rets := by
        have := congrArg Frame.returns hframeEq
        simpa [MemorySpillCallSound.calleeFrame] using this
      let callCutoff := frameCutoff result.base result.layout
        (frameInfo result.selection
          ((frames (resolveMemoryGuardStmts result.base result.reserved raw)).filterMap
            (·.owner)) policyCallee)
      have hcallOuter : callCutoff ≤ cutoff := by
        apply le_trans (MemorySpillCallSound.calleeCutoff_le_callerCutoff
          hfacts.layout_built hfacts.layout_check
          hctx.motive.origin.policyFrame_mem hcalleeMem howner
          hctx.motive.origin.callOrigin.call)
        exact hcutoff
      have hslotCutoff : ∀ localName slot,
          slotFor? result.layout.slots policyFrame.owner localName = some slot →
            callCutoff ≤ slot := by
        intro localName slot hslot
        exact MemorySpillCallSound.calleeCutoff_le_callerSlot
          hfacts.layout_built hfacts.layout_check
          hctx.motive.origin.policyFrame_mem hcalleeMem howner
          hctx.motive.origin.callOrigin.call hslot
      apply closeCallOkBranch hargsSim
      · intro targetArgState htargetArgs hscratch
        obtain ⟨hentry, hentryLive, hentryAbove⟩ :=
          MemorySpillExprCallSound.enterPolicyCallee hfacts.layout_built
          hfacts.layout_check hcalleeMem howner hparams hreturns hlength hnodup
          hscratch hfacts.reserved_lt callCutoff
          (fun localName slot hslot => by
            apply MemorySpillCallSound.calleeSlotEnd_le_cutoff
              hfacts.layout_built hfacts.layout_check hcalleeMem
            exact hslot)
        have hentryRel' : ControlLiveRel
            (base := result.base) (reserved := result.reserved)
            result.selection result.layout policyCallee
            (decl.params ++ decl.rets) []
            (frameInitialLive result.selection policyCallee)
            (MemorySpillCallSound.callEnv decl.params decl.rets argvals)
            sourceArgState
            (MemorySpillCallSound.callEnv decl.params decl.rets argvals)
            (afterInitReturns result.layout.slots (some fn) decl.rets
              (afterInitParams result.layout.slots (some fn)
                (MemorySpillCallSound.callEnv decl.params decl.rets argvals)
                decl.params targetArgState)) := by
          exact {
            liveRel := by simpa [howner, hparams, hreturns] using hentryLive
            unique := callEnv_selectedUnique hlength hnodup }
        have hentryRelForBody : ControlLiveRel
            (base := result.base) (reserved := result.reserved)
            result.selection result.layout policyCallee
            (policyCallee.params ++ policyCallee.returns) []
            (frameInitialLive result.selection policyCallee)
            (MemorySpillCallSound.callEnv decl.params decl.rets argvals)
            sourceArgState
            (MemorySpillCallSound.callEnv decl.params decl.rets argvals)
            (afterInitReturns result.layout.slots (some fn) decl.rets
              (afterInitParams result.layout.slots (some fn)
                (MemorySpillCallSound.callEnv decl.params decl.rets argvals)
                decl.params targetArgState)) := by
          simpa [hparams, hreturns, MemorySpillCallSound.callEnv] using hentryRel'
        have hbodySim := ihBody hbodyCtx hentryRelForBody hclosureCovered rfl
          (le_refl callCutoff)
        have hbodySim' : StepSimResult
            (base := result.base) (reserved := result.reserved)
            (MemorySpill.declaredStmts
              (resolveMemoryGuardStmts result.base result.reserved raw))
            result.selection result.layout policyCallee
            (decl.params ++ decl.rets) []
            (frameInitialLive result.selection policyCallee) decl.rets
            (MemorySpillCallSound.callEnv decl.params decl.rets argvals)
            (MemorySpillCallSound.callEnv decl.params decl.rets argvals)
            (.stmt (.block policyCallee.body)) (.stmt (.block decl.body))
            (.sres sourceFinal sourceFinalState outcome) closure
            (afterInitReturns result.layout.slots (some fn) decl.rets
              (afterInitParams result.layout.slots (some fn)
                (MemorySpillCallSound.callEnv decl.params decl.rets argvals)
                decl.params targetArgState))
            (copyBackReturns result.layout.slots policyCallee.owner decl.rets)
            callCutoff := by
          simpa [hparams, hreturns, MemorySpillCallSound.callEnv, bindZeros,
            guardedEvm, Dialect.zero, litValue] using hbodySim
        obtain ⟨hbodyResult⟩ := calleeBodyResult_of_stepSim
          (base := result.base) (reserved := result.reserved)
          (selected := result.selection) (layout := result.layout)
          (name := fn) (decl := decl) (closure := closure)
          (argvals := argvals) (sourceFinal := sourceFinal)
          (sourceFinalState := sourceFinalState) (outcome := outcome)
          (cutoff := callCutoff) hbodySim' howner
        have hbodyResult' : MemorySpillExprCallSound.CalleeBodyResult
            (base := result.base) (reserved := result.reserved)
            result.selection result.layout policyCallee fn decl closure argvals
            sourceFinal sourceFinalState outcome
            (afterInitReturns result.layout.slots policyCallee.owner
              policyCallee.returns
              (afterInitParams result.layout.slots policyCallee.owner
                (MemorySpillCallSound.callEnv decl.params decl.rets argvals)
                policyCallee.params targetArgState)) callCutoff := by
          simpa [howner, hparams, hreturns] using hbodyResult
        rcases houtcome with rfl | rfl
        · exact closeNormalCalleeBody hlookup hlength hbody htargetArgs
            hentry hentryAbove hbodyResult' howner
            (List.nodup_append.mp hnodup).2.1
            (fun localName slot hslot =>
              (SpillFacts.slotBounds hfacts hslot).2)
            hfacts.reserved_lt
        · exact closeLeaveCalleeBody hlookup hlength hbody htargetArgs
            hentry hentryAbove hbodyResult' howner
      · exact hslotCutoff
      · intro localName slot hslot
        exact (SpillFacts.slotBounds hfacts hslot).2
      · exact hcallOuter
  | callHalt hargs hlookup hlength hbody ihArgs =>
      rename_i sourceFuns source sourceState fn args argvals sourceArgState
        decl closure sourceFinal sourceFinalState ihBody
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered _hexitCopies
        hcutoff
      obtain ⟨policyArgs, rfl, hargsEq⟩ :=
        execCode_call_inv hctx.motive.origin.executedCode_eq
      have hargsCtx := hctx.argsChild
        hctx.motive.origin.callOrigin.callArgs hctx.motive.envDeclared
        hctx.exitsBound
      rw [← hargsEq] at hargsCtx
      have hargsSim := ihArgs hargsCtx hrel hcovered rfl hcutoff
      have hcalleeFrame := MemorySpillCallSound.covered_calleeFrame_mem
        hcovered hlookup
      obtain ⟨policyCallee0, hcalleeMem0, hframeEq0⟩ :=
        List.mem_map.mp hcalleeFrame
      have hnodup0 := frameSignaturesWF_frame hfacts.signatures_wf hcalleeMem0
      have hparamsEq : policyCallee0.params = decl.params := by
        have := congrArg Frame.params hframeEq0
        simpa [MemorySpillCallSound.calleeFrame] using this
      have hreturnsEq : policyCallee0.returns = decl.rets := by
        have := congrArg Frame.returns hframeEq0
        simpa [MemorySpillCallSound.calleeFrame] using this
      have hnodup : (decl.params ++ decl.rets).Nodup := by
        simpa [hparamsEq, hreturnsEq] using hnodup0
      obtain ⟨policyCallee, hcalleeMem, hframeEq, hclosureCovered,
          hbodyCtx⟩ := ControlStepContext.calleeBlock
            (selected := result.selection) hctx.selectedBindingsWF hcovered
            hlookup hlength hnodup
      have howner : policyCallee.owner = some fn := by
        have := congrArg Frame.owner hframeEq
        simpa [MemorySpillCallSound.calleeFrame] using this
      have hparams : policyCallee.params = decl.params := by
        have := congrArg Frame.params hframeEq
        simpa [MemorySpillCallSound.calleeFrame] using this
      have hreturns : policyCallee.returns = decl.rets := by
        have := congrArg Frame.returns hframeEq
        simpa [MemorySpillCallSound.calleeFrame] using this
      let callCutoff := frameCutoff result.base result.layout
        (frameInfo result.selection
          ((frames (resolveMemoryGuardStmts result.base result.reserved raw)).filterMap
            (·.owner)) policyCallee)
      have hcallOuter : callCutoff ≤ cutoff := by
        apply le_trans (MemorySpillCallSound.calleeCutoff_le_callerCutoff
          hfacts.layout_built hfacts.layout_check
          hctx.motive.origin.policyFrame_mem hcalleeMem howner
          hctx.motive.origin.callOrigin.call)
        exact hcutoff
      have hslotCutoff : ∀ localName slot,
          slotFor? result.layout.slots policyFrame.owner localName = some slot →
            callCutoff ≤ slot := by
        intro localName slot hslot
        exact MemorySpillCallSound.calleeCutoff_le_callerSlot
          hfacts.layout_built hfacts.layout_check
          hctx.motive.origin.policyFrame_mem hcalleeMem howner
          hctx.motive.origin.callOrigin.call hslot
      apply closeCallHaltBranch hargsSim
      · intro targetArgState htargetArgs hscratch
        obtain ⟨hentry, hentryLive, hentryAbove⟩ :=
          MemorySpillExprCallSound.enterPolicyCallee hfacts.layout_built
          hfacts.layout_check hcalleeMem howner hparams hreturns hlength hnodup
          hscratch hfacts.reserved_lt callCutoff
          (fun localName slot hslot => by
            apply MemorySpillCallSound.calleeSlotEnd_le_cutoff
              hfacts.layout_built hfacts.layout_check hcalleeMem
            exact hslot)
        have hentryRel' : ControlLiveRel
            (base := result.base) (reserved := result.reserved)
            result.selection result.layout policyCallee
            (decl.params ++ decl.rets) []
            (frameInitialLive result.selection policyCallee)
            (MemorySpillCallSound.callEnv decl.params decl.rets argvals)
            sourceArgState
            (MemorySpillCallSound.callEnv decl.params decl.rets argvals)
            (afterInitReturns result.layout.slots (some fn) decl.rets
              (afterInitParams result.layout.slots (some fn)
                (MemorySpillCallSound.callEnv decl.params decl.rets argvals)
                decl.params targetArgState)) := by
          exact {
            liveRel := by simpa [howner, hparams, hreturns] using hentryLive
            unique := callEnv_selectedUnique hlength hnodup }
        have hentryRelForBody : ControlLiveRel
            (base := result.base) (reserved := result.reserved)
            result.selection result.layout policyCallee
            (policyCallee.params ++ policyCallee.returns) []
            (frameInitialLive result.selection policyCallee)
            (MemorySpillCallSound.callEnv decl.params decl.rets argvals)
            sourceArgState
            (MemorySpillCallSound.callEnv decl.params decl.rets argvals)
            (afterInitReturns result.layout.slots (some fn) decl.rets
              (afterInitParams result.layout.slots (some fn)
                (MemorySpillCallSound.callEnv decl.params decl.rets argvals)
                decl.params targetArgState)) := by
          simpa [hparams, hreturns, MemorySpillCallSound.callEnv] using hentryRel'
        have hbodySim := ihBody hbodyCtx hentryRelForBody hclosureCovered rfl
          (le_refl callCutoff)
        have hbodySim' : StepSimResult
            (base := result.base) (reserved := result.reserved)
            (MemorySpill.declaredStmts
              (resolveMemoryGuardStmts result.base result.reserved raw))
            result.selection result.layout policyCallee
            (decl.params ++ decl.rets) []
            (frameInitialLive result.selection policyCallee) decl.rets
            (MemorySpillCallSound.callEnv decl.params decl.rets argvals)
            (MemorySpillCallSound.callEnv decl.params decl.rets argvals)
            (.stmt (.block policyCallee.body)) (.stmt (.block decl.body))
            (.sres sourceFinal sourceFinalState .halt) closure
            (afterInitReturns result.layout.slots (some fn) decl.rets
              (afterInitParams result.layout.slots (some fn)
                (MemorySpillCallSound.callEnv decl.params decl.rets argvals)
                decl.params targetArgState))
            (copyBackReturns result.layout.slots policyCallee.owner decl.rets)
            callCutoff := by
          simpa [hparams, hreturns, MemorySpillCallSound.callEnv, bindZeros,
            guardedEvm, Dialect.zero, litValue] using hbodySim
        obtain ⟨hbodyResult⟩ := calleeBodyResult_of_stepSim
          (base := result.base) (reserved := result.reserved)
          (selected := result.selection) (layout := result.layout)
          (name := fn) (decl := decl) (closure := closure)
          (argvals := argvals) (sourceFinal := sourceFinal)
          (sourceFinalState := sourceFinalState) (outcome := .halt)
          (cutoff := callCutoff) hbodySim' howner
        have hbodyResult' : MemorySpillExprCallSound.CalleeBodyResult
            (base := result.base) (reserved := result.reserved)
            result.selection result.layout policyCallee fn decl closure argvals
            sourceFinal sourceFinalState .halt
            (afterInitReturns result.layout.slots policyCallee.owner
              policyCallee.returns
              (afterInitParams result.layout.slots policyCallee.owner
                (MemorySpillCallSound.callEnv decl.params decl.rets argvals)
                policyCallee.params targetArgState)) callCutoff := by
          simpa [howner, hparams, hreturns] using hbodyResult
        exact closeHaltingCalleeBody hlookup hlength hbody htargetArgs
          hentry hentryAbove hbodyResult' howner
      · exact hslotCutoff
      · intro localName slot hslot
        exact (SpillFacts.slotBounds hfacts hslot).2
      · exact hcallOuter
  | callArgsHalt hargs ihArgs =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered _hexitCopies
        hcutoff
      obtain ⟨policyArgs, rfl, hargsEq⟩ :=
        execCode_call_inv hctx.motive.origin.executedCode_eq
      have hargsCtx := hctx.argsChild
        hctx.motive.origin.callOrigin.callArgs hctx.motive.envDeclared
        hctx.exitsBound
      rw [← hargsEq] at hargsCtx
      have hsim := ihArgs hargsCtx hrel hcovered rfl hcutoff
      exact closeCallArgsHaltBranch hsim
  | argsNil =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel _hcovered _hexitCopies
        hcutoff
      obtain ⟨policyArgs, rfl, heq⟩ :=
        execCode_args_inv hctx.motive.origin.executedCode_eq
      cases mode <;> cases policyArgs <;> simp [execCode] at heq
      all_goals
        exact simulateCallFreeArgsBranch hfacts hexternals hctx Step.argsNil
          .nil hrel hcutoff
  | argsCons hrest hhead ihRest ihHead =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered _hexitCopies
        hcutoff
      obtain ⟨policyHead, policyRest, rfl, hheadEq, hrestEq⟩ :=
        execCode_args_cons_inv hctx.motive.origin.executedCode_eq
      have hrestCtx := hctx.argsChild
        hctx.motive.origin.callOrigin.argsTail hctx.motive.envDeclared
        hctx.exitsBound
      rw [← hrestEq] at hrestCtx
      have hrestSim := ihRest hrestCtx hrel hcovered rfl hcutoff
      apply closeArgsConsBranch hrestSim
      intro targetRestState htargetRest hcontrol
      have hheadCtx := hctx.exprChild
        hctx.motive.origin.callOrigin.argsHead hctx.motive.envDeclared
        hctx.exitsBound
      rw [← hheadEq] at hheadCtx
      have hheadSim := ihHead hheadCtx hcontrol hcovered rfl hcutoff
      obtain ⟨targetHeadResult, htargetHead, hheadResult, haboveHead⟩ := hheadSim
      cases targetHeadResult with
      | sres targetFinal targetFinalState targetOutcome =>
          simp [ResultControlRel] at hheadResult
      | eres targetExprResult =>
          cases targetExprResult with
          | halt targetFinalState => simp [ResultControlRel] at hheadResult
          | vals targetValues targetFinalState =>
              rcases hheadResult with
                ⟨hvalues, hcontrol', _horigin, _hexitBound, _hexitSignature⟩
              subst targetValues
              exact ⟨targetFinalState, htargetHead, hcontrol', haboveHead⟩
  | argsRestHalt hrest ihRest =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered _hexitCopies
        hcutoff
      obtain ⟨policyArgs, rfl, heq⟩ :=
        execCode_args_inv hctx.motive.origin.executedCode_eq
      cases mode <;> cases policyArgs <;>
        simp [execCode, resolveForLayoutExprs] at heq
      all_goals
        rcases heq with ⟨rfl, rfl⟩
        have hrestCtx := hctx.argsChild
          hctx.motive.origin.callOrigin.argsTail hctx.motive.envDeclared
          hctx.exitsBound
        have hsim := ihRest hrestCtx hrel hcovered rfl hcutoff
        exact closeArgsRestHaltBranch hsim
  | argsHeadHalt hrest hhead ihRest ihHead =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered _hexitCopies
        hcutoff
      obtain ⟨policyHead, policyRest, rfl, hheadEq, hrestEq⟩ :=
        execCode_args_cons_inv hctx.motive.origin.executedCode_eq
      have hrestCtx := hctx.argsChild
        hctx.motive.origin.callOrigin.argsTail hctx.motive.envDeclared
        hctx.exitsBound
      rw [← hrestEq] at hrestCtx
      have hrestSim := ihRest hrestCtx hrel hcovered rfl hcutoff
      apply closeArgsHeadHaltBranch hrestSim
      intro targetRestState htargetRest hcontrol
      have hheadCtx := hctx.exprChild
        hctx.motive.origin.callOrigin.argsHead hctx.motive.envDeclared
        hctx.exitsBound
      rw [← hheadEq] at hheadCtx
      have hheadSim := ihHead hheadCtx hcontrol hcovered rfl hcutoff
      obtain ⟨targetHeadResult, htargetHead, hheadResult, haboveHead⟩ := hheadSim
      cases targetHeadResult with
      | sres targetFinal targetFinalState targetOutcome =>
          simp [ResultControlRel] at hheadResult
      | eres targetExprResult =>
          cases targetExprResult with
          | vals targetValues targetFinalState => simp [ResultControlRel] at hheadResult
          | halt targetFinalState =>
              rcases hheadResult with
                ⟨hcontrol', _horigin, _hexitBound, _hexitSignature⟩
              exact ⟨targetFinalState, htargetHead, hcontrol', haboveHead⟩
  | funDef =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel _hcovered _hexitCopies
        _hcutoff
      obtain ⟨policyStmt, rfl, heq⟩ :=
        execCode_stmt_inv hctx.motive.origin.executedCode_eq
      cases mode <;> cases policyStmt <;>
        simp [execCode] at heq
      all_goals
        rcases heq with ⟨rfl, rfl, rfl, rfl⟩
        exact simulateFunDefLeaf hctx hrel
  | block hbody ihBody =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered _hexitCopies
        hcutoff
      obtain ⟨policyStmt, rfl, heq⟩ :=
        execCode_stmt_inv hctx.motive.origin.executedCode_eq
      cases mode <;> cases policyStmt <;> simp [execCode] at heq
      all_goals
        subst_vars
        have hbodyCtx := hctx.blockBody
        have hbodyRel := hrel.pushScope
        have hbodyCovered := MemorySpillControlSound.FunsCovered.pushHoist
          hcovered hctx.motive.origin.executedFrameOrigin.block
        have hbodySim := ihBody hbodyCtx hbodyRel hbodyCovered rfl hcutoff
        exact closeBlockWith hrel hctx.exitsBound hctx.exitsInSignature
          hbodySim (restore_keys (venvKeys_suffix hbody rfl)
            (venvLen_mono hbody rfl))
  | @letZero funs V st names =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel _hcovered hexitCopies
        hcutoff
      subst exitCopies
      have hpolicy := execCode_let_none_inv
        hctx.motive.origin.executedCode_eq
      subst policyCode
      let nextLive := liveAfterCode result.selection policyFrame.owner live
        (.stmt (.letDecl names none))
      have hzero :
          (guardedEvm calls creates result.base result.reserved).zero =
            (0 : U256) := by
        change litValue (.number 0) = (0 : U256)
        decide
      have hzeroD : Dialect.zero D = (0 : U256) := by
        change litValue (.number 0) = (0 : U256)
        decide
      have hzeroKeys :
          (bindZeros (guardedEvm calls creates result.base result.reserved)
            names).map Prod.fst = names := by
        unfold bindZeros
        rw [List.map_map]
        change names.map id = names
        exact List.map_id names
      have hzeroZip :
          names.zip (List.replicate names.length (0 : U256)) =
            bindZeros (guardedEvm calls creates result.base result.reserved)
              names := by
        have hz : ∀ xs : List Ident,
            xs.zip (List.replicate xs.length (0 : U256)) =
              bindZeros (guardedEvm calls creates result.base result.reserved)
                xs := by
          intro xs
          induction xs with
          | nil => rfl
          | cons name rest ih =>
              have hc := congrArg (List.cons (name, (0 : U256))) ih
              simpa [bindZeros, List.replicate_succ, hzero] using hc
        exact hz names
      have holdLive : ∀ key ∈ live, key ∈ nextLive := by
        intro key hkey
        exact liveStmt_entry_subset_out result.selection policyFrame.owner live
          (.letDecl names none) key hkey
      have hcertified : LiveCertified result.selection policyFrame nextLive := by
        simpa [nextLive, LetAfterCertified] using hctx.letAfterCertified
      have horiginLet : EnvDeclaredOrigin
          (MemorySpill.declaredStmts
            (resolveMemoryGuardStmts result.base result.reserved raw))
          (bindZeros (guardedEvm calls creates result.base result.reserved)
            names ++ V) :=
        hctx.motive.envDeclared.prependList (by
          intro name hname
          rw [hzeroKeys] at hname
          apply hctx.motive.origin.bindingOrigin.declared name
          simpa only [codeDeclared, MemorySpill.declaredStmt] using hname)
      have hboundLet : NamesBound exitNames
          (bindZeros (guardedEvm calls creates result.base result.reserved)
            names ++ V) := by
        intro name hname
        obtain ⟨value, hget⟩ := hctx.exitsBound name hname
        apply MemorySpillControlSound.envGet_exists_of_name_mem
        rw [List.map_append]
        exact List.mem_append_right _ (envGet_name_mem hget)
      have hslotEnd : ∀ name slot,
          slotFor? result.layout.slots policyFrame.owner name = some slot →
            slot + 32 ≤ cutoff := by
        intro name slot hslot
        exact le_trans (buildLayout_slotFor_end_le_frameCutoff
          hfacts.layout_built hfacts.layout_check
          hctx.motive.origin.policyFrame_mem hslot) hcutoff
      cases names with
      | nil =>
          obtain ⟨hexec, hfinal, haboveFinal⟩ := execSelectedMultiLetZero
            hfacts.layout_built hfacts.layout_check hfacts.reserved_lt
            hctx.motive.origin.policyFrame_mem hrel.liveRel
            (names := []) (targets := []) rfl (by simp) (by simp) (by simp)
            holdLive
            (by simp) hcertified (by simp)
          exact closeLetZeroWith
            (calls := calls) (creates := creates)
            (base := result.base) (reserved := result.reserved)
            (names := []) (source := V) (target := target)
            (finalLive := nextLive)
            (by simpa [rewriteCode, rewriteStmt, targetSlots?] using hexec)
            ⟨hfinal, by simpa [bindZeros] using hrel.unique⟩
            horiginLet hboundLet
            hctx.exitsInSignature (by rfl) haboveFinal
      | cons name rest =>
          cases rest with
          | nil =>
              cases hslot : slotFor? result.layout.slots policyFrame.owner name with
              | some slot =>
                  have hselected := layoutCheck_slot_selected
                    hfacts.layout_check hslot
                  have hready := hctx.selectedLetReady (by simp) hselected
                  have hfresh : name ∉ V.map Prod.fst := by
                    intro hname
                    exact hready.1 (hrel.liveRel.bound name hname slot hslot)
                  have hnamesLive :
                      ({ owner := policyFrame.owner, name } : SpillKey) ∈
                        nextLive := by
                    have hselectedKey :
                        ({ owner := policyFrame.owner, name } : SpillKey) ∈
                          selectedKeys result.selection policyFrame.owner
                            [name] := by
                      simp [selectedKeys, hselected]
                    simpa [nextLive, liveAfterCode, liveStmt] using
                      List.mem_append_left live hselectedKey
                  obtain ⟨hexec, hfinal, haboveFinal⟩ :=
                    execSelectedMultiLetZero hfacts.layout_built
                      hfacts.layout_check hfacts.reserved_lt
                      hctx.motive.origin.policyFrame_mem hrel.liveRel
                      (names := [name])
                      (targets := [slot]) (by simp [targetSlots?, hslot])
                      (by simp)
                      (by
                        intro item hitem
                        simp only [List.mem_singleton] at hitem
                        subst item
                        exact hfresh)
                      (by
                        intro item hitem
                        simp only [List.mem_singleton] at hitem
                        subst item
                        exact hready.2)
                      holdLive (by simpa using hnamesLive) hcertified
                      (by intro item hitem itemSlot hitemSlot
                          simpa using hslotEnd item itemSlot hitemSlot)
                  have hunique := hrel.unique.prependSelectedFresh
                    (value := (guardedEvm calls creates result.base
                      result.reserved).zero) hfresh
                  exact closeLetZeroWith
                    (calls := calls) (creates := creates)
                    (base := result.base) (reserved := result.reserved)
                    (names := [name]) (source := V) (target := target)
                    (finalLive := nextLive)
                    (by simpa [rewriteCode, rewriteStmt, hslot] using hexec)
                    ⟨hfinal, by simpa [bindZeros] using hunique⟩
                    horiginLet hboundLet hctx.exitsInSignature (by rfl)
                    haboveFinal
              | none =>
                  have hlitZeroD : Dialect.litValue D (.number 0) =
                      (0 : U256) := by
                    change litValue (.number 0) = (0 : U256)
                    decide
                  have heval : EvalExpr D (spillFuns result.layout.slots funs)
                      target targetState (MemorySpill.word 0)
                      (.vals [0] targetState) := by
                    have hlit := (Step.lit : EvalExpr D
                      (spillFuns result.layout.slots funs) target targetState
                      (.lit (.number 0))
                      (.vals [Dialect.litValue D (.number 0)] targetState))
                    rw [hlitZeroD] at hlit
                    exact hlit
                  obtain ⟨hexec, hfinal, haboveFinal⟩ := execUnselectedLet
                    hslot hcertified holdLive hrel.liveRel heval
                    (AboveUnchanged.refl cutoff result.reserved targetState)
                  have hunique := hrel.unique.prependNoSlot
                    (value := (guardedEvm calls creates result.base
                      result.reserved).zero) hslot
                  exact closeLetZeroWith
                    (calls := calls) (creates := creates)
                    (base := result.base) (reserved := result.reserved)
                    (finalLive := nextLive)
                    (by simpa [rewriteCode, rewriteStmt, hslot] using hexec)
                    ⟨by
                      have hbindSingleton :
                          bindZeros (guardedEvm calls creates result.base
                            result.reserved) [name] ++ V =
                            (name, (0 : U256)) :: V := by
                        simp only [bindZeros, List.map_cons, List.map_nil]
                        rw [hzero]
                        rfl
                      rw [hbindSingleton]
                      exact hfinal,
                      by simpa [bindZeros] using hunique⟩
                    horiginLet hboundLet hctx.exitsInSignature (by rfl)
                    haboveFinal
          | cons second tail =>
              have hgroup := hctx.motive.origin.bindingOrigin.letGroup
                (by simp)
              rcases coupledGroup_dichotomy hfacts hgroup with
                ⟨hnodup, hall | hall⟩
              · obtain ⟨targets, htargets, _htargetsLength⟩ :=
                  selectedTuple_targets hfacts hall
                have hfresh : ∀ item ∈ name :: second :: tail,
                    item ∉ V.map Prod.fst := by
                  intro item hitem hsource
                  obtain ⟨slot, hslot⟩ :=
                    layoutCheck_selected_slot hfacts.layout_check
                      (hall item hitem)
                  exact (hctx.selectedLetReady hitem (hall item hitem)).1
                    (hrel.liveRel.bound item hsource slot hslot)
                have hnotSignature : ∀ item ∈ name :: second :: tail,
                    item ∉ policyFrame.params ++ policyFrame.returns := by
                  intro item hitem
                  exact (hctx.selectedLetReady hitem (hall item hitem)).2
                have hnamesLive : ∀ item ∈ name :: second :: tail,
                    ({ owner := policyFrame.owner, name := item } : SpillKey) ∈
                      nextLive := by
                  intro item hitem
                  have hselectedKey :
                      ({ owner := policyFrame.owner, name := item } : SpillKey) ∈
                        selectedKeys result.selection policyFrame.owner
                          (name :: second :: tail) := by
                    simp only [selectedKeys, List.mem_filterMap]
                    exact ⟨item, hitem, by simp [hall item hitem]⟩
                  simpa [nextLive, liveAfterCode, liveStmt] using
                    List.mem_append_left live hselectedKey
                obtain ⟨hexec, hfinal, haboveFinal⟩ :=
                  execSelectedMultiLetZero hfacts.layout_built
                    hfacts.layout_check hfacts.reserved_lt
                    hctx.motive.origin.policyFrame_mem hrel.liveRel htargets
                    hnodup hfresh hnotSignature holdLive hnamesLive hcertified
                    (by intro item hitem slot hslot
                        exact hslotEnd item slot hslot)
                have hunique : SelectedUnique result.layout.slots
                    policyFrame.owner
                    (bindZeros
                      (guardedEvm calls creates result.base result.reserved)
                      (name :: second :: tail) ++ V) := by
                  apply hrel.unique.prependFreshList
                  · rw [hzeroKeys]
                    exact hnodup
                  · intro item hitem
                    rw [hzeroKeys] at hitem
                    exact hfresh item hitem
                exact closeLetZeroWith
                  (calls := calls) (creates := creates)
                  (base := result.base) (reserved := result.reserved)
                  (names := name :: second :: tail)
                  (source := V) (target := target)
                  (finalLive := nextLive)
                  (by simpa [rewriteCode, rewriteStmt, htargets] using hexec)
                  ⟨by rw [hzeroZip.symm]; exact hfinal, hunique⟩
                  horiginLet hboundLet
                  hctx.exitsInSignature (by rfl) haboveFinal
              · have hnoTargets := unselectedTuple_noTargets hfacts hall
                have hnoSlots : ∀ item ∈ name :: second :: tail,
                    slotFor? result.layout.slots policyFrame.owner item = none := by
                  intro item hitem
                  cases hslot : slotFor? result.layout.slots
                      policyFrame.owner item with
                  | none => rfl
                  | some slot =>
                      exact False.elim (hall item hitem
                        (layoutCheck_slot_selected hfacts.layout_check hslot))
                obtain ⟨hexec, hfinal, haboveFinal⟩ :=
                  execUnselectedMultiLetZero hrel.liveRel hnoSlots holdLive
                    hcertified
                have hunique : SelectedUnique result.layout.slots
                    policyFrame.owner
                    (bindZeros
                      (guardedEvm calls creates result.base result.reserved)
                      (name :: second :: tail) ++ V) := by
                  apply hrel.unique.prependNoSlots
                  intro item hitem
                  rw [hzeroKeys] at hitem
                  exact hnoSlots item hitem
                exact closeLetZeroWith
                  (calls := calls) (creates := creates)
                  (base := result.base) (reserved := result.reserved)
                  (names := name :: second :: tail)
                  (source := V) (target := target)
                  (finalLive := nextLive)
                  (by simpa [rewriteCode, rewriteStmt, hnoTargets] using hexec)
                  ⟨hfinal, hunique⟩ horiginLet hboundLet
                  hctx.exitsInSignature (by rfl) (haboveFinal cutoff)
  | @letVal funs V st names expression values finalState hexpr hlength ihExpr =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered hexitCopies
        hcutoff
      subst exitCopies
      obtain ⟨policyExpr, rfl, hexprEq⟩ :=
        execCode_let_some_inv hctx.motive.origin.executedCode_eq
      have hchildCtx := hctx.exprChild
        hctx.motive.origin.callOrigin.letExpr hctx.motive.envDeclared
        hctx.exitsBound
      rw [← hexprEq] at hchildCtx
      have hsim := ihExpr hchildCtx hrel hcovered rfl hcutoff
      apply closeLetValWith (names := names) hsim
      intro targetValues targetFinalState hvalues htarget hcontrol horigin
        hexitBound hexitSignature habove
      subst targetValues
      let nextLive := liveAfterCode result.selection policyFrame.owner live
        (.stmt (.letDecl names (some policyExpr)))
      have holdLive : ∀ key ∈ live, key ∈ nextLive := by
        intro key hkey
        exact liveStmt_entry_subset_out result.selection policyFrame.owner live
          (.letDecl names (some policyExpr)) key hkey
      have hcertified : LiveCertified result.selection policyFrame nextLive := by
        simpa [nextLive, LetAfterCertified] using hctx.letAfterCertified
      have horiginLet : EnvDeclaredOrigin
          (MemorySpill.declaredStmts
            (resolveMemoryGuardStmts result.base result.reserved raw))
          (names.zip values ++ V) :=
        horigin.prependList (by
          intro name hname
          rw [List.map_fst_zip (Nat.le_of_eq hlength.symm)] at hname
          apply hctx.motive.origin.bindingOrigin.declared name
          simpa [codeDeclared, MemorySpill.declaredStmt] using hname)
      have hboundLet : NamesBound exitNames (names.zip values ++ V) := by
        intro name hname
        obtain ⟨value, hget⟩ := hexitBound name hname
        apply MemorySpillControlSound.envGet_exists_of_name_mem
        rw [List.map_append]
        exact List.mem_append_right _ (envGet_name_mem hget)
      have hslotEnd : ∀ name slot,
          slotFor? result.layout.slots policyFrame.owner name = some slot →
            slot + 32 ≤ cutoff := by
        intro name slot hslot
        exact le_trans (buildLayout_slotFor_end_le_frameCutoff
          hfacts.layout_built hfacts.layout_check
          hctx.motive.origin.policyFrame_mem hslot) hcutoff
      cases names with
      | nil =>
          have htarget' := YulEvmCompiler.Optimizer.Step.emptyScope_congr
            htarget (Optimizer.EmptyScopeRel.add _)
          obtain ⟨hexec, hfinal, haboveFinal⟩ := execSelectedMultiLetVal
            hfacts.layout_built hfacts.layout_check hfacts.reserved_lt
            hctx.motive.origin.policyFrame_mem hcontrol.liveRel htarget'
            (targets := []) rfl hlength (by simp) (by simp) (by simp)
            holdLive (by simp) hcertified habove (by simp)
          exact closeStmtNormalWith
            (calls := calls) (creates := creates)
            (base := result.base) (reserved := result.reserved)
            (finalLive := nextLive)
            (policyStmt := .letDecl [] (some policyExpr))
            (by simpa [rewriteCode, rewriteStmt, targetSlots?] using hexec)
            ⟨hfinal, by simpa using hcontrol.unique⟩ horiginLet hboundLet
            hexitSignature (by rfl) haboveFinal
      | cons name rest =>
          cases rest with
          | nil =>
              cases values with
              | nil => simp at hlength
              | cons value valueRest =>
                  cases valueRest with
                  | cons value2 values => simp at hlength
                  | nil =>
                      cases hslot : slotFor? result.layout.slots
                          policyFrame.owner name with
                      | some slot =>
                          have hselected := layoutCheck_slot_selected
                            hfacts.layout_check hslot
                          have hready := hctx.selectedLetReady (by simp) hselected
                          have hfresh : name ∉ V.map Prod.fst := by
                            intro hname
                            exact hready.1
                              (hcontrol.liveRel.bound name hname slot hslot)
                          have hnextCertified : LiveCertified result.selection
                              policyFrame
                              ({ owner := policyFrame.owner, name } :: live) := by
                            simpa [nextLive, liveAfterCode, liveStmt, selectedKeys,
                              hselected] using hcertified
                          obtain ⟨hexec, hfinal, haboveFinal⟩ := execSelectedLet
                            hfacts.layout_built hfacts.layout_check
                            hfacts.reserved_lt
                            hctx.motive.origin.policyFrame_mem hslot hready.2
                            hnextCertified hcontrol.liveRel htarget habove
                            (hslotEnd name slot hslot)
                          have hunique :=
                            hcontrol.unique.prependSelectedFresh
                              (value := value) hfresh
                          exact closeStmtNormalWith
                            (calls := calls) (creates := creates)
                            (base := result.base) (reserved := result.reserved)
                            (finalLive := nextLive)
                            (policyStmt := .letDecl [name] (some policyExpr))
                            (by simpa [rewriteCode, rewriteStmt, hslot] using hexec)
                            ⟨by simpa [nextLive, liveAfterCode, liveStmt,
                                selectedKeys, hselected] using hfinal,
                              by simpa using hunique⟩
                            horiginLet hboundLet hexitSignature (by rfl)
                            haboveFinal
                      | none =>
                          obtain ⟨hexec, hfinal, haboveFinal⟩ :=
                            execUnselectedLet hslot hcertified holdLive
                              hcontrol.liveRel htarget habove
                          have hunique := hcontrol.unique.prependNoSlot
                            (value := value) hslot
                          exact closeStmtNormalWith
                            (calls := calls) (creates := creates)
                            (base := result.base) (reserved := result.reserved)
                            (finalLive := nextLive)
                            (policyStmt := .letDecl [name] (some policyExpr))
                            (by simpa [rewriteCode, rewriteStmt, hslot] using hexec)
                            ⟨hfinal, by simpa using hunique⟩
                            horiginLet hboundLet hexitSignature (by rfl)
                            haboveFinal
          | cons second tail =>
              have hgroup := hctx.motive.origin.bindingOrigin.letGroup
                (by simp)
              rcases coupledGroup_dichotomy hfacts hgroup with
                ⟨hnodup, hall | hall⟩
              · obtain ⟨targets, htargets, _htargetsLength⟩ :=
                  selectedTuple_targets hfacts hall
                have hfresh : ∀ item ∈ name :: second :: tail,
                    item ∉ V.map Prod.fst := by
                  intro item hitem hsource
                  obtain ⟨slot, hslot⟩ :=
                    layoutCheck_selected_slot hfacts.layout_check
                      (hall item hitem)
                  exact (hctx.selectedLetReady hitem (hall item hitem)).1
                    (hcontrol.liveRel.bound item hsource slot hslot)
                have hnotSignature : ∀ item ∈ name :: second :: tail,
                    item ∉ policyFrame.params ++ policyFrame.returns := by
                  intro item hitem
                  exact (hctx.selectedLetReady hitem (hall item hitem)).2
                have hnamesLive : ∀ item ∈ name :: second :: tail,
                    ({ owner := policyFrame.owner, name := item } : SpillKey) ∈
                      nextLive := by
                  intro item hitem
                  have hcontains : result.selection.contains
                      ({ owner := policyFrame.owner, name := item } : SpillKey) =
                        true := by
                    simpa using hall item hitem
                  simp only [nextLive, liveAfterCode, liveStmt]
                  change ({ owner := policyFrame.owner, name := item } : SpillKey) ∈
                    selectedKeys result.selection policyFrame.owner
                      (name :: second :: tail) ++ live
                  apply List.mem_append_left
                  unfold selectedKeys
                  rw [List.mem_filterMap]
                  refine ⟨item, hitem, ?_⟩
                  change (if result.selection.contains
                      ({ owner := policyFrame.owner, name := item } : SpillKey)
                    then some ({ owner := policyFrame.owner, name := item } : SpillKey)
                    else none) =
                      some ({ owner := policyFrame.owner, name := item } : SpillKey)
                  rw [hcontains]
                  rfl
                have htarget' :=
                  YulEvmCompiler.Optimizer.Step.emptyScope_congr htarget
                    (Optimizer.EmptyScopeRel.add _)
                obtain ⟨hexec, hfinal, haboveFinal⟩ :=
                  execSelectedMultiLetVal hfacts.layout_built
                    hfacts.layout_check hfacts.reserved_lt
                    hctx.motive.origin.policyFrame_mem hcontrol.liveRel htarget'
                    htargets hlength hnodup hfresh hnotSignature holdLive
                    hnamesLive hcertified habove
                    (by intro item hitem slot hslot
                        exact hslotEnd item slot hslot)
                have hunique : SelectedUnique result.layout.slots
                    policyFrame.owner
                    ((name :: second :: tail).zip values ++ V) := by
                  apply hcontrol.unique.prependFreshList
                  · simpa [List.map_fst_zip (Nat.le_of_eq hlength.symm)] using
                      hnodup
                  · intro item hitem
                    rw [List.map_fst_zip (Nat.le_of_eq hlength.symm)] at hitem
                    exact hfresh item hitem
                exact closeStmtNormalWith
                  (calls := calls) (creates := creates)
                  (base := result.base) (reserved := result.reserved)
                  (finalLive := nextLive)
                  (policyStmt := .letDecl (name :: second :: tail)
                    (some policyExpr))
                  (by simpa [rewriteCode, rewriteStmt, htargets] using hexec)
                  ⟨hfinal, hunique⟩ horiginLet hboundLet hexitSignature
                  (by rfl) haboveFinal
              · have hnoTargets := unselectedTuple_noTargets hfacts hall
                have hnoSlots : ∀ item ∈ name :: second :: tail,
                    slotFor? result.layout.slots policyFrame.owner item = none := by
                  intro item hitem
                  cases hslot : slotFor? result.layout.slots
                      policyFrame.owner item with
                  | none => rfl
                  | some slot =>
                      exact False.elim (hall item hitem
                        (layoutCheck_slot_selected hfacts.layout_check hslot))
                obtain ⟨hexec, hfinal, haboveFinal⟩ :=
                  execUnselectedMultiLetVal hcontrol.liveRel htarget hlength
                    hnoSlots holdLive hcertified habove
                have hunique : SelectedUnique result.layout.slots
                    policyFrame.owner
                    ((name :: second :: tail).zip values ++ V) := by
                  apply hcontrol.unique.prependNoSlots
                  intro item hitem
                  rw [List.map_fst_zip (Nat.le_of_eq hlength.symm)] at hitem
                  exact hnoSlots item hitem
                exact closeStmtNormalWith
                  (calls := calls) (creates := creates)
                  (base := result.base) (reserved := result.reserved)
                  (finalLive := nextLive)
                  (policyStmt := .letDecl (name :: second :: tail)
                    (some policyExpr))
                  (by simpa [rewriteCode, rewriteStmt, hnoTargets] using hexec)
                  ⟨hfinal, hunique⟩ horiginLet hboundLet hexitSignature
                  (by rfl) haboveFinal
  | @letHalt funs V st names expression finalState hexpr ihExpr =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered hexitCopies
        hcutoff
      obtain ⟨policyExpr, rfl, hexprEq⟩ :=
        execCode_let_some_inv hctx.motive.origin.executedCode_eq
      have hchildCtx := hctx.exprChild
        hctx.motive.origin.callOrigin.letExpr hctx.motive.envDeclared
        hctx.exitsBound
      rw [← hexprEq] at hchildCtx
      have hsim := ihExpr hchildCtx hrel hcovered rfl hcutoff
      subst exitCopies
      apply closeLetHaltWith (names := names) hsim
      intro targetFinalState htarget
      cases names with
        | nil =>
            have htarget' := YulEvmCompiler.Optimizer.Step.emptyScope_congr
              htarget (Optimizer.EmptyScopeRel.add _)
            simpa [rewriteCode, rewriteStmt, targetSlots?] using
              execSelectedTempBlockHalt (targets := []) (temps := []) htarget'
        | cons name rest =>
            cases rest with
            | nil =>
                cases hslot : slotFor? result.layout.slots policyFrame.owner name with
                | some slot =>
                    simpa [rewriteCode, rewriteStmt, hslot] using
                      Step.seqStop (execStoreSlot_halt htarget) (by decide)
                | none =>
                    simpa [rewriteCode, rewriteStmt, hslot] using
                      execMultiLetHalt htarget
            | cons second tail =>
                cases htargets : targetSlots? result.layout.slots
                    policyFrame.owner (name :: second :: tail) with
                | some targets =>
                    have htarget' :=
                      YulEvmCompiler.Optimizer.Step.emptyScope_congr htarget
                        (Optimizer.EmptyScopeRel.add _)
                    simpa [rewriteCode, rewriteStmt, htargets] using
                      execSelectedTempBlockHalt (targets := targets)
                        (temps := (name :: second :: tail).map
                          (tempName policyFrame.owner)) htarget'
                | none =>
                    simpa [rewriteCode, rewriteStmt, htargets] using
                      execMultiLetHalt htarget
  | @assignVal funs V st names expression values finalState hexpr hlength ihExpr =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered hexitCopies
        hcutoff
      subst exitCopies
      obtain ⟨policyExpr, rfl, hexprEq⟩ :=
        execCode_assign_inv hctx.motive.origin.executedCode_eq
      have hchildCtx := hctx.exprChild
        hctx.motive.origin.callOrigin.assignExpr hctx.motive.envDeclared
        hctx.exitsBound
      rw [← hexprEq] at hchildCtx
      have hsim := ihExpr hchildCtx hrel hcovered rfl hcutoff
      apply closeAssignValWith (names := names) hsim
      intro targetValues targetFinalState hvalues htarget hcontrol horigin
        hexitBound hexitSignature habove
      subst targetValues
      have hkeys := @VEnv.setMany_keys
        (guardedEvm calls creates result.base result.reserved) inferInstance
        V names values
      have horiginAssign : EnvDeclaredOrigin
          (MemorySpill.declaredStmts
            (resolveMemoryGuardStmts result.base result.reserved raw))
          (VEnv.setMany V names values) := by
        intro name hname
        rw [hkeys] at hname
        exact horigin name hname
      have hboundAssign : NamesBound exitNames
          (VEnv.setMany V names values) :=
        NamesBound.of_keys_eq hexitBound hkeys
      have huniqueAssign : SelectedUnique result.layout.slots
          policyFrame.owner (VEnv.setMany V names values) := by
        intro name slot hslot
        rw [hkeys]
        exact hcontrol.unique name slot hslot
      have hslotEnd : ∀ name slot,
          slotFor? result.layout.slots policyFrame.owner name = some slot →
            slot + 32 ≤ cutoff := by
        intro name slot hslot
        exact le_trans (buildLayout_slotFor_end_le_frameCutoff
          hfacts.layout_built hfacts.layout_check
          hctx.motive.origin.policyFrame_mem hslot) hcutoff
      cases names with
      | nil =>
          have htarget' := YulEvmCompiler.Optimizer.Step.emptyScope_congr
            htarget (Optimizer.EmptyScopeRel.add _)
          obtain ⟨hexec, hfinal, haboveFinal⟩ := execSelectedMultiAssign
            hfacts.layout_built hfacts.layout_check hfacts.reserved_lt
            hctx.motive.origin.policyFrame_mem hcontrol.liveRel htarget'
            (targets := []) rfl hlength (by simp) (by simp) habove
            (by simp)
          exact closeStmtNormalWith
            (by simpa [rewriteCode, rewriteStmt, targetSlots?] using hexec)
            ⟨hfinal, huniqueAssign⟩ horiginAssign hboundAssign
            hexitSignature (by simp [liveAfterCode, liveStmt]) haboveFinal
      | cons name rest =>
          cases rest with
          | nil =>
              cases values with
              | nil => simp at hlength
              | cons value valueRest =>
                  cases valueRest with
                  | cons value2 values => simp at hlength
                  | nil =>
                      cases hslot : slotFor? result.layout.slots
                          policyFrame.owner name with
                      | some slot =>
                          have hselected := layoutCheck_slot_selected
                            hfacts.layout_check hslot
                          have hlive := hctx.selectedAssignReady (by simp)
                            hselected
                          obtain ⟨hexec, hfinal, haboveFinal⟩ :=
                            execSelectedAssign hfacts.layout_built
                              hfacts.layout_check hfacts.reserved_lt
                              hctx.motive.origin.policyFrame_mem hslot hlive
                              hcontrol.liveRel htarget habove
                              (hslotEnd name slot hslot)
                          rw [envSet_eq (calls := calls) (creates := creates)
                            (base := result.base) (reserved := result.reserved)
                            V name value] at hfinal
                          exact closeStmtNormalWith
                            (calls := calls) (creates := creates)
                            (base := result.base) (reserved := result.reserved)
                            (sourceFinal := @VEnv.setMany
                              (guardedEvm calls creates result.base result.reserved)
                              V [name] [value])
                            (finalLive := live)
                            (policyStmt := .assign [name] policyExpr)
                            (by simpa [rewriteCode, rewriteStmt, hslot] using hexec)
                            ⟨by simpa [VEnv.setMany] using hfinal,
                              huniqueAssign⟩ horiginAssign hboundAssign
                            hexitSignature (by simp [liveAfterCode, liveStmt])
                            haboveFinal
                      | none =>
                          obtain ⟨hexec, hfinal, haboveFinal⟩ :=
                            execUnselectedAssign hslot hcontrol.liveRel htarget
                              habove
                          rw [envSet_eq (calls := calls) (creates := creates)
                            (base := result.base) (reserved := result.reserved)
                            V name value] at hfinal
                          exact closeStmtNormalWith
                            (calls := calls) (creates := creates)
                            (base := result.base) (reserved := result.reserved)
                            (sourceFinal := @VEnv.setMany
                              (guardedEvm calls creates result.base result.reserved)
                              V [name] [value])
                            (finalLive := live)
                            (policyStmt := .assign [name] policyExpr)
                            (by simpa [rewriteCode, rewriteStmt, hslot] using hexec)
                            ⟨by simpa [VEnv.setMany] using hfinal,
                              huniqueAssign⟩ horiginAssign hboundAssign
                            hexitSignature (by simp [liveAfterCode, liveStmt])
                            haboveFinal
          | cons second tail =>
              have hgroup := hctx.motive.origin.bindingOrigin.assignGroup
                (by simp)
              rcases coupledGroup_dichotomy hfacts hgroup with
                ⟨hnodup, hall | hall⟩
              · obtain ⟨targets, htargets, htargetsLength⟩ :=
                  selectedTuple_targets hfacts hall
                have hlive : ∀ item ∈ name :: second :: tail,
                    ({ owner := policyFrame.owner, name := item } : SpillKey) ∈
                      live := by
                  intro item hitem
                  exact hctx.selectedAssignReady hitem (hall item hitem)
                have htarget' := YulEvmCompiler.Optimizer.Step.emptyScope_congr
                  htarget (Optimizer.EmptyScopeRel.add _)
                obtain ⟨hexec, hfinal, haboveFinal⟩ := execSelectedMultiAssign
                  hfacts.layout_built hfacts.layout_check hfacts.reserved_lt
                  hctx.motive.origin.policyFrame_mem hcontrol.liveRel htarget'
                  htargets hlength hnodup hlive habove
                  (by intro item hitem slot hslot
                      exact hslotEnd item slot hslot)
                exact closeStmtNormalWith
                  (by simpa [rewriteCode, rewriteStmt, htargets] using hexec)
                  ⟨hfinal, huniqueAssign⟩ horiginAssign hboundAssign
                  hexitSignature (by simp [liveAfterCode, liveStmt])
                  haboveFinal
              · have hnoTargets := unselectedTuple_noTargets hfacts hall
                have hnoSlots : ∀ item ∈ name :: second :: tail,
                    slotFor? result.layout.slots policyFrame.owner item = none := by
                  intro item hitem
                  cases hslot : slotFor? result.layout.slots
                      policyFrame.owner item with
                  | none => rfl
                  | some slot =>
                      exact False.elim (hall item hitem
                        (layoutCheck_slot_selected hfacts.layout_check hslot))
                obtain ⟨hexec, hfinal, haboveFinal⟩ := execUnselectedMultiAssign
                  hcontrol.liveRel htarget hlength hnoSlots habove
                exact closeStmtNormalWith
                  (by simpa [rewriteCode, rewriteStmt, hnoTargets] using hexec)
                  ⟨hfinal, huniqueAssign⟩ horiginAssign hboundAssign
                  hexitSignature (by simp [liveAfterCode, liveStmt])
                  haboveFinal
  | @assignHalt funs V st names expression finalState hexpr ihExpr =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered hexitCopies
        hcutoff
      obtain ⟨policyExpr, rfl, hexprEq⟩ :=
        execCode_assign_inv hctx.motive.origin.executedCode_eq
      have hchildCtx := hctx.exprChild
        hctx.motive.origin.callOrigin.assignExpr hctx.motive.envDeclared
        hctx.exitsBound
      rw [← hexprEq] at hchildCtx
      have hsim := ihExpr hchildCtx hrel hcovered rfl hcutoff
      subst exitCopies
      apply closeAssignHaltWith (names := names) hsim
      intro targetFinalState htarget
      cases names with
        | nil =>
            have htarget' := YulEvmCompiler.Optimizer.Step.emptyScope_congr
              htarget (Optimizer.EmptyScopeRel.add _)
            simpa [rewriteCode, rewriteStmt, targetSlots?] using
              execSelectedTempBlockHalt (targets := []) (temps := []) htarget'
        | cons name rest =>
            cases rest with
            | nil =>
                cases hslot : slotFor? result.layout.slots policyFrame.owner name with
                | some slot =>
                    simpa [rewriteCode, rewriteStmt, hslot] using
                      Step.seqStop (execStoreSlot_halt htarget) (by decide)
                | none =>
                    simpa [rewriteCode, rewriteStmt, hslot] using
                      execMultiAssignHalt htarget
            | cons second tail =>
                cases htargets : targetSlots? result.layout.slots
                    policyFrame.owner (name :: second :: tail) with
                | some targets =>
                    have htarget' :=
                      YulEvmCompiler.Optimizer.Step.emptyScope_congr htarget
                        (Optimizer.EmptyScopeRel.add _)
                    simpa [rewriteCode, rewriteStmt, htargets] using
                      execSelectedTempBlockHalt (targets := targets)
                        (temps := (name :: second :: tail).map
                          (tempName policyFrame.owner)) htarget'
                | none =>
                    simpa [rewriteCode, rewriteStmt, htargets] using
                      execMultiAssignHalt htarget
  | exprStmt hexpr ihExpr =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered hexitCopies
        hcutoff
      obtain ⟨policyStmt, rfl, heq⟩ :=
        execCode_stmt_inv hctx.motive.origin.executedCode_eq
      cases mode <;> cases policyStmt <;> simp [execCode] at heq
      all_goals
        subst_vars
        have hchildCtx := hctx.exprChild
          hctx.motive.origin.callOrigin.exprStmt hctx.motive.envDeclared
          hctx.exitsBound
        have hsim := ihExpr hchildCtx hrel hcovered rfl hcutoff
        exact closeExprStmtNormal hsim
  | exprStmtHalt hexpr ihExpr =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered hexitCopies
        hcutoff
      obtain ⟨policyStmt, rfl, heq⟩ :=
        execCode_stmt_inv hctx.motive.origin.executedCode_eq
      cases mode <;> cases policyStmt <;> simp [execCode] at heq
      all_goals
        subst_vars
        have hchildCtx := hctx.exprChild
          hctx.motive.origin.callOrigin.exprStmt hctx.motive.envDeclared
          hctx.exitsBound
        have hsim := ihExpr hchildCtx hrel hcovered rfl hcutoff
        exact closeExprStmtHalt hsim
  | ifTrue hcond hnonzero hbody ihCond ihBody =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered hexitCopies
        hcutoff
      subst exitCopies
      obtain ⟨policyStmt, rfl, heq⟩ :=
        execCode_stmt_inv hctx.motive.origin.executedCode_eq
      cases mode <;> cases policyStmt <;> simp [execCode] at heq
      all_goals
        rcases heq with ⟨rfl, rfl⟩
        have hcondSim := ihCond hctx.condExpr hrel hcovered rfl hcutoff
        apply closeIfTrue hcondSim hnonzero
        intro targetConditionState htargetCondition hconditionControl
        exact ihBody hctx.condBody.asBlockStmt hconditionControl hcovered rfl
          hcutoff
  | ifFalse hcond hzero ihCond =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered _hexitCopies
        hcutoff
      obtain ⟨policyStmt, rfl, heq⟩ :=
        execCode_stmt_inv hctx.motive.origin.executedCode_eq
      cases mode <;> cases policyStmt <;> simp [execCode] at heq
      all_goals
        rcases heq with ⟨rfl, rfl⟩
        have hsim := ihCond hctx.condExpr hrel hcovered rfl hcutoff
        exact closeIfFalse hsim hzero
  | ifHalt hcond ihCond =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered _hexitCopies
        hcutoff
      obtain ⟨policyStmt, rfl, heq⟩ :=
        execCode_stmt_inv hctx.motive.origin.executedCode_eq
      cases mode <;> cases policyStmt <;> simp [execCode] at heq
      all_goals
        rcases heq with ⟨rfl, rfl⟩
        have hsim := ihCond hctx.condExpr hrel hcovered rfl hcutoff
        exact closeIfHalt hsim
  | @switchExec funs V st condition cases fallback value conditionState finalEnv
      finalState outcome hcond hbody ihCond ihBody =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered hexitCopies
        hcutoff
      subst exitCopies
      obtain ⟨policyStmt, rfl, heq⟩ :=
        execCode_stmt_inv hctx.motive.origin.executedCode_eq
      cases mode <;> cases policyStmt <;> simp [execCode] at heq
      all_goals
        rcases heq with ⟨rfl, rfl, rfl⟩
        have hcondCtx := hctx.exprChild
          hctx.motive.origin.callOrigin.switchExpr hctx.motive.envDeclared
          hctx.exitsBound
        have hcondSim := ihCond hcondCtx hrel hcovered rfl hcutoff
        apply closeSwitchExec hcondSim
        intro targetConditionState htargetCondition hconditionControl
        rcases hctx.switchSelectedBlock value with hempty | hselected
        · rcases hempty with ⟨hpolicyEmpty, hexecutedEmpty⟩
          rw [hexecutedEmpty] at hbody
          cases hbody with
          | block hseq =>
              cases hseq with
              | seqNil =>
                  have hseqSim := simulateSeqNilLeaf
                    (calls := calls) (creates := creates)
                    (cuts := scopeMark _ _ :: cuts)
                    (sourceFuns := hoist _ [] :: funs)
                    (exitCopies := copyBackReturns result.layout.slots
                      policyFrame.owner exitNames)
                    (cutoff := cutoff)
                    hconditionControl.pushScope hctx.motive.envDeclared
                    hctx.exitsBound hctx.exitsInSignature
                  simpa [hpolicyEmpty, hexecutedEmpty] using
                    closeBlockWith hconditionControl hctx.exitsBound
                      hctx.exitsInSignature hseqSim
                      (restore_keys (by rfl) (le_refl _))
        · exact ihBody hselected hconditionControl hcovered rfl hcutoff
  | switchHalt hcond ihCond =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered _hexitCopies
        hcutoff
      obtain ⟨policyStmt, rfl, heq⟩ :=
        execCode_stmt_inv hctx.motive.origin.executedCode_eq
      cases mode <;> cases policyStmt <;> simp [execCode] at heq
      all_goals
        rcases heq with ⟨rfl, rfl, rfl⟩
        have hcondCtx := hctx.exprChild
          hctx.motive.origin.callOrigin.switchExpr hctx.motive.envDeclared
          hctx.exitsBound
        have hsim := ihCond hcondCtx hrel hcovered rfl hcutoff
        exact closeSwitchHalt hsim
  | forLoop hinit hloop ihInit ihLoop =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered hexitCopies
        hcutoff
      subst exitCopies
      obtain ⟨policyStmt, rfl, heq⟩ :=
        execCode_stmt_inv hctx.motive.origin.executedCode_eq
      cases mode <;> cases policyStmt <;> simp [execCode] at heq
      all_goals
        rcases heq with ⟨rfl, rfl, rfl, rfl⟩
        have hinitCtx := hctx.forInit
        have hinitCovered := MemorySpillControlSound.FunsCovered.pushHoist
          hcovered hinitCtx.motive.origin.executedFrameOrigin
        have hinitSim := ihInit hinitCtx hrel.pushScope hinitCovered rfl hcutoff
        apply closeForLoopWith hrel hctx.exitsBound hctx.exitsInSignature
          hinitSim
        · intro targetInit targetInitState initLive hinitControl hinitLive
            hinitOrigin hinitBound
          subst initLive
          have hloopCtx := hctx.forLoop hinitOrigin hinitBound
          exact ihLoop hloopCtx hinitControl hinitCovered rfl hcutoff
        · exact restore_keys
            ((venvKeys_suffix hinit rfl).trans (venvKeys_suffix hloop rfl))
            ((venvLen_mono hinit rfl).trans (venvLen_mono hloop rfl))
  | forInitHalt hinit ihInit =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered hexitCopies
        hcutoff
      subst exitCopies
      obtain ⟨policyStmt, rfl, heq⟩ :=
        execCode_stmt_inv hctx.motive.origin.executedCode_eq
      cases mode <;> cases policyStmt <;> simp [execCode] at heq
      all_goals
        rcases heq with ⟨rfl, rfl, rfl, rfl⟩
        have hinitCtx := hctx.forInit
        have hinitCovered := MemorySpillControlSound.FunsCovered.pushHoist
          hcovered hinitCtx.motive.origin.executedFrameOrigin
        have hinitSim := ihInit hinitCtx hrel.pushScope hinitCovered rfl hcutoff
        exact closeForInitHaltWith hrel hctx.exitsBound hctx.exitsInSignature
          hinitSim (restore_keys (venvKeys_suffix hinit rfl)
            (venvLen_mono hinit rfl))
  | «break» =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel _hcovered _hexitCopies
        _hcutoff
      obtain ⟨policyStmt, rfl, heq⟩ :=
        execCode_stmt_inv hctx.motive.origin.executedCode_eq
      cases mode <;> cases policyStmt <;> simp [execCode] at heq
      all_goals
        exact simulateBreakLeaf hrel hctx.motive.envDeclared hctx.exitsBound
          hctx.exitsInSignature
  | «continue» =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel _hcovered _hexitCopies
        _hcutoff
      obtain ⟨policyStmt, rfl, heq⟩ :=
        execCode_stmt_inv hctx.motive.origin.executedCode_eq
      cases mode <;> cases policyStmt <;> simp [execCode] at heq
      all_goals
        exact simulateContinueLeaf hrel hctx.motive.envDeclared hctx.exitsBound
          hctx.exitsInSignature
  | «leave» =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel _hcovered hexitCopies
        _hcutoff
      obtain ⟨policyStmt, rfl, heq⟩ :=
        execCode_stmt_inv hctx.motive.origin.executedCode_eq
      cases mode <;> cases policyStmt <;> simp [execCode] at heq
      all_goals
        exact simulateLeaveLeaf hctx hrel
          (fun _ _ hslot => (SpillFacts.slotBounds hfacts hslot).2)
          hfacts.reserved_lt hexitCopies
  | seqNil =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel _hcovered _hexitCopies
        _hcutoff
      obtain ⟨policyStmts, rfl, heq⟩ :=
        execCode_stmts_inv hctx.motive.origin.executedCode_eq
      cases mode <;> cases policyStmts <;> simp [execCode] at heq
      all_goals
        exact simulateSeqNilLeaf hrel hctx.motive.envDeclared hctx.exitsBound
          hctx.exitsInSignature
  | seqCons hhead htail ihHead ihTail =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered hexitCopies
        hcutoff
      subst exitCopies
      obtain ⟨policyHead, policyRest, rfl, hheadEq, htailEq⟩ :=
        execCode_stmts_cons_inv hctx.motive.origin.executedCode_eq
      have hheadCtx := hctx.stmtsHead
      rw [← hheadEq] at hheadCtx
      have hheadSim := ihHead hheadCtx hrel hcovered rfl hcutoff
      apply closeSeqConsWith hheadSim
      intro targetMiddle targetMiddleState hheadResult haboveHead
      rcases hheadResult with
        ⟨headLive, _houtcome, hheadControl, horigin, hexitBound,
          _hexitSignature, _hleave, _hblock, hnormal⟩
      have hlive := hnormal rfl
      simp only [liveAfterCode] at hlive
      subst headLive
      have htailCtx := hctx.stmtsTail horigin hexitBound
      rw [← htailEq] at htailCtx
      exact ihTail htailCtx hheadControl hcovered rfl hcutoff
  | seqStop hhead hearly ihHead =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered hexitCopies
        hcutoff
      subst exitCopies
      obtain ⟨policyHead, policyRest, rfl, hheadEq, htailEq⟩ :=
        execCode_stmts_cons_inv hctx.motive.origin.executedCode_eq
      have hheadCtx := hctx.stmtsHead
      rw [← hheadEq] at hheadCtx
      have hheadSim := ihHead hheadCtx hrel hcovered rfl hcutoff
      exact closeSeqStop hearly hheadSim
  | loopDone hcond hzero ihCond =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered _hexitCopies
        hcutoff
      obtain ⟨policyCondition, policyPost, policyBody, rfl, heq⟩ :=
        execCode_loop_inv hctx.motive.origin.executedCode_eq
      cases mode <;> simp [execCode] at heq
      all_goals
        rcases heq with ⟨rfl, rfl, rfl⟩
        have hcondCtx := hctx.exprChild
          hctx.motive.origin.callOrigin.loopCond hctx.motive.envDeclared
          hctx.exitsBound
        have hsim := ihCond hcondCtx hrel hcovered rfl hcutoff
        exact closeLoopDone hsim hzero
  | loopCondHalt hcond ihCond =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered _hexitCopies
        hcutoff
      obtain ⟨policyCondition, policyPost, policyBody, rfl, heq⟩ :=
        execCode_loop_inv hctx.motive.origin.executedCode_eq
      cases mode <;> simp [execCode] at heq
      all_goals
        rcases heq with ⟨rfl, rfl, rfl⟩
        have hcondCtx := hctx.exprChild
          hctx.motive.origin.callOrigin.loopCond hctx.motive.envDeclared
          hctx.exitsBound
        have hsim := ihCond hcondCtx hrel hcovered rfl hcutoff
        exact closeLoopCondHalt hsim
  | loopStep hcond hnonzero hbody hbodyOutcome hpost hloop ihCond ihBody
      ihPost ihLoop =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered hexitCopies
        hcutoff
      subst exitCopies
      obtain ⟨policyCondition, policyPost, policyBody, rfl, heq⟩ :=
        execCode_loop_inv hctx.motive.origin.executedCode_eq
      cases mode <;> simp [execCode] at heq
      all_goals
        rcases heq with ⟨rfl, rfl, rfl⟩
        have hcondCtx := hctx.exprChild
          hctx.motive.origin.callOrigin.loopCond hctx.motive.envDeclared
          hctx.exitsBound
        have hcondSim := ihCond hcondCtx hrel hcovered rfl hcutoff
        apply closeLoopStep hcondSim hnonzero hbodyOutcome
        · intro targetConditionState htargetCondition hconditionControl
          have hbodyStmtsCtx := hctx.loopBody
            hctx.motive.envDeclared hctx.exitsBound
          exact ihBody hbodyStmtsCtx.asBlockStmt hconditionControl hcovered
            rfl hcutoff
        · intro targetBody targetBodyState hbodyControl hbodyOrigin hbodyBound
          have hpostStmtsCtx := hctx.loopPost hbodyOrigin hbodyBound
          exact ihPost hpostStmtsCtx.asBlockStmt hbodyControl hcovered rfl
            hcutoff
        · intro targetPost targetPostState hpostControl hpostOrigin hpostBound
          have hloopCtx := hctx.loopAgain hpostOrigin hpostBound
          exact ihLoop hloopCtx hpostControl hcovered rfl hcutoff
  | loopPostHalt hcond hnonzero hbody hbodyOutcome hpost ihCond ihBody ihPost =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered hexitCopies
        hcutoff
      subst exitCopies
      obtain ⟨policyCondition, policyPost, policyBody, rfl, heq⟩ :=
        execCode_loop_inv hctx.motive.origin.executedCode_eq
      cases mode <;> simp [execCode] at heq
      all_goals
        rcases heq with ⟨rfl, rfl, rfl⟩
        have hcondCtx := hctx.exprChild
          hctx.motive.origin.callOrigin.loopCond hctx.motive.envDeclared
          hctx.exitsBound
        have hcondSim := ihCond hcondCtx hrel hcovered rfl hcutoff
        apply closeLoopPostHalt hcondSim hnonzero hbodyOutcome
        · intro targetConditionState htargetCondition hconditionControl
          have hbodyStmtsCtx := hctx.loopBody
            hctx.motive.envDeclared hctx.exitsBound
          exact ihBody hbodyStmtsCtx.asBlockStmt hconditionControl hcovered
            rfl hcutoff
        · intro targetBody targetBodyState hbodyControl hbodyOrigin hbodyBound
          have hpostStmtsCtx := hctx.loopPost hbodyOrigin hbodyBound
          exact ihPost hpostStmtsCtx.asBlockStmt hbodyControl hcovered rfl
            hcutoff
  | loopBreak hcond hnonzero hbody ihCond ihBody =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered hexitCopies
        hcutoff
      subst exitCopies
      obtain ⟨policyCondition, policyPost, policyBody, rfl, heq⟩ :=
        execCode_loop_inv hctx.motive.origin.executedCode_eq
      cases mode <;> simp [execCode] at heq
      all_goals
        rcases heq with ⟨rfl, rfl, rfl⟩
        have hcondCtx := hctx.exprChild
          hctx.motive.origin.callOrigin.loopCond hctx.motive.envDeclared
          hctx.exitsBound
        have hcondSim := ihCond hcondCtx hrel hcovered rfl hcutoff
        apply closeLoopBreak hcondSim hnonzero
        intro targetConditionState htargetCondition hconditionControl
        have hbodyStmtsCtx := hctx.loopBody
          hctx.motive.envDeclared hctx.exitsBound
        have hbodyCtx := hbodyStmtsCtx.asBlockStmt
        exact ihBody hbodyCtx hconditionControl hcovered rfl hcutoff
  | loopLeave hcond hnonzero hbody ihCond ihBody =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered hexitCopies
        hcutoff
      subst exitCopies
      obtain ⟨policyCondition, policyPost, policyBody, rfl, heq⟩ :=
        execCode_loop_inv hctx.motive.origin.executedCode_eq
      cases mode <;> simp [execCode] at heq
      all_goals
        rcases heq with ⟨rfl, rfl, rfl⟩
        have hcondCtx := hctx.exprChild
          hctx.motive.origin.callOrigin.loopCond hctx.motive.envDeclared
          hctx.exitsBound
        have hcondSim := ihCond hcondCtx hrel hcovered rfl hcutoff
        apply closeLoopTerminalSame hcondSim hnonzero (by decide)
        · intro targetConditionState htargetCondition hconditionControl
          have hbodyStmtsCtx := hctx.loopBody
            hctx.motive.envDeclared hctx.exitsBound
          exact ihBody hbodyStmtsCtx.asBlockStmt hconditionControl hcovered
            rfl hcutoff
        · intro targetConditionState targetFinalState targetFinal htargetCondition
            htargetBody
          exact Step.loopLeave htargetCondition (by
            change _ ≠ (0 : U256)
            change _ ≠ (0 : U256) at hnonzero
            exact hnonzero)
            htargetBody
  | loopBodyHalt hcond hnonzero hbody ihCond ihBody =>
      dsimp [StepSimMotive]
      intro policyFrame executedFrame live policyCode exitNames target
        targetState cuts exitCopies cutoff hctx hrel hcovered hexitCopies
        hcutoff
      subst exitCopies
      obtain ⟨policyCondition, policyPost, policyBody, rfl, heq⟩ :=
        execCode_loop_inv hctx.motive.origin.executedCode_eq
      cases mode <;> simp [execCode] at heq
      all_goals
        rcases heq with ⟨rfl, rfl, rfl⟩
        have hcondCtx := hctx.exprChild
          hctx.motive.origin.callOrigin.loopCond hctx.motive.envDeclared
          hctx.exitsBound
        have hcondSim := ihCond hcondCtx hrel hcovered rfl hcutoff
        apply closeLoopTerminalSame hcondSim hnonzero (by decide)
        · intro targetConditionState htargetCondition hconditionControl
          have hbodyStmtsCtx := hctx.loopBody
            hctx.motive.envDeclared hctx.exitsBound
          exact ihBody hbodyStmtsCtx.asBlockStmt hconditionControl hcovered
            rfl hcutoff
        · intro targetConditionState targetFinalState targetFinal htargetCondition
            htargetBody
          exact Step.loopBodyHalt htargetCondition (by
            change _ ≠ (0 : U256)
            change _ ≠ (0 : U256) at hnonzero
            exact hnonzero)
            htargetBody

end YulEvmCompiler.Optimizer.MemorySpillStmtStepSound
