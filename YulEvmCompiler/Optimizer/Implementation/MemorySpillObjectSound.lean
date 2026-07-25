import YulEvmCompiler.Optimizer.Implementation.MemorySpillLayoutSound
import YulEvmCompiler.Optimizer.Implementation.MemorySpillResolveSound
import YulEvmCompiler.Optimizer.Implementation.Pipeline
set_option warningAsError true
/-!
# Object-tree structure for memory spilling

The hybrid object spiller pairs raw object code with the already verified
optimizer-pipeline object.  This module records the exact recursive alignment
between that pair, the emitted object, and the per-node spill plan.  The
semantic theorem at the end is parameterized by the block-level spill theorem;
it does not grant semantic authority to an arbitrary fallback object.
-/

namespace YulEvmCompiler.Optimizer.MemorySpillObjectSound

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open MemorySpill
open MemorySpillSelect

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates
local notation "G" => guardedEvm calls creates
abbrev WordEnv := List (Ident × U256)

def plannedCode (fallback : Block Op) : Option Result → Block Op
  | some result => result.block
  | none => fallback

mutual
  /-- Exact node correspondence produced by `spillObjectWithFallback`.

  Sharing the name in all three indices pins name preservation.  The emitted
  data is definitionally the raw data; fallback data is intentionally ignored.
  The plan's optional result selects exactly one of the spill block and the
  paired fallback block. -/
  inductive ObjectPlanRel : Object Op → Object Op → Object Op →
      MemorySpillSelect.ObjectPlan → Prop
    | mk {name : String} {rawCode fallbackCode : Block Op}
        {rawSubs fallbackSubs outputSubs : List (Object Op)}
        {rawData fallbackData : List (String × Data)}
        {outputCode : Block Op}
        {codeResult : Option Result}
        {childPlans : List MemorySpillSelect.ObjectPlan}
        (hspill : spillBlock? rawCode = codeResult)
        (hcode : outputCode = plannedCode fallbackCode codeResult)
        (children : ObjectPlansRel rawSubs fallbackSubs outputSubs childPlans) :
        ObjectPlanRel
          (.mk name rawCode rawSubs rawData)
          (.mk name fallbackCode fallbackSubs fallbackData)
          (.mk name outputCode outputSubs rawData)
          (MemorySpillSelect.ObjectPlan.mk codeResult childPlans)

  /-- List-level alignment for child object trees. -/
  inductive ObjectPlansRel : List (Object Op) → List (Object Op) →
      List (Object Op) → List MemorySpillSelect.ObjectPlan → Prop
    | nil : ObjectPlansRel [] [] [] []
    | cons {raw fallback output : Object Op}
        {raws fallbacks outputs : List (Object Op)}
        {plan : MemorySpillSelect.ObjectPlan}
        {plans : List MemorySpillSelect.ObjectPlan}
        (head : ObjectPlanRel raw fallback output plan)
        (tail : ObjectPlansRel raws fallbacks outputs plans) :
        ObjectPlansRel (raw :: raws) (fallback :: fallbacks)
          (output :: outputs) (plan :: plans)
end

mutual
  theorem spillObjectWithFallback_planRel {raw fallback : Object Op}
      {result : ObjectResult}
      (hspill : spillObjectWithFallback raw fallback = some result) :
      ObjectPlanRel raw fallback result.object result.plan := by
    cases raw with
    | mk rawName rawCode rawSubs rawData =>
      cases fallback with
      | mk fallbackName fallbackCode fallbackSubs fallbackData =>
        rw [spillObjectWithFallback] at hspill
        simp only [bne_iff_ne] at hspill
        split at hspill
        · contradiction
        · rename_i hnames
          have hnameEq : rawName = fallbackName := by
            simpa using hnames
          subst fallbackName
          obtain ⟨children, hchildrenCall, hrest⟩ :=
            Option.bind_eq_some_iff.mp hspill
          obtain ⟨outputSubs, childPlans, childCount⟩ := children
          simp only [Option.some.injEq] at hrest
          subst result
          change ObjectPlanRel
            (.mk rawName rawCode rawSubs rawData)
            (.mk rawName fallbackCode fallbackSubs fallbackData)
            (.mk rawName (plannedCode fallbackCode (spillBlock? rawCode))
              outputSubs rawData)
            (MemorySpillSelect.ObjectPlan.mk (spillBlock? rawCode) childPlans)
          exact ObjectPlanRel.mk (name := rawName) (rawCode := rawCode)
            (fallbackCode := fallbackCode) (rawData := rawData)
            (fallbackData := fallbackData)
            (outputCode := plannedCode fallbackCode (spillBlock? rawCode))
            (codeResult := spillBlock? rawCode)
            (childPlans := childPlans) rfl rfl
            (spillObjectsWithFallback_planRel hchildrenCall)
  termination_by sizeOf raw

  theorem spillObjectsWithFallback_planRel
      {raws fallbacks outputs : List (Object Op)}
      {plans : List MemorySpillSelect.ObjectPlan}
      {count : Nat}
      (hspill : spillObjectsWithFallback raws fallbacks =
        some (outputs, plans, count)) :
      ObjectPlansRel raws fallbacks outputs plans := by
    cases raws with
    | nil =>
      cases fallbacks with
      | nil =>
        rw [spillObjectsWithFallback.eq_def] at hspill
        obtain ⟨rfl, rfl, rfl⟩ := hspill
        exact .nil
      | cons fallback fallbacks =>
        rw [spillObjectsWithFallback.eq_def] at hspill
        contradiction
    | cons raw raws =>
      cases fallbacks with
      | nil =>
        rw [spillObjectsWithFallback.eq_def] at hspill
        contradiction
      | cons fallback fallbacks =>
        rw [spillObjectsWithFallback.eq_def] at hspill
        obtain ⟨headResult, hhead, htailBind⟩ :=
          Option.bind_eq_some_iff.mp hspill
        obtain ⟨tailResult, htail, hresult⟩ :=
          Option.bind_eq_some_iff.mp htailBind
        obtain ⟨tailOutputs, tailPlans, tailCount⟩ := tailResult
        simp only [Option.some.injEq] at hresult
        obtain ⟨rfl, rfl, rfl⟩ := hresult
        exact .cons (spillObjectWithFallback_planRel hhead)
          (spillObjectsWithFallback_planRel htail)
  termination_by sizeOf raws
end

mutual
  /-- Equality of the non-code object skeleton. -/
  inductive SameObjectShape : Object Op → Object Op → Prop
    | mk {name : String} {leftCode rightCode : Block Op}
        {leftSubs rightSubs : List (Object Op)}
        {segments : List (String × Data)}
        (children : SameObjectShapes leftSubs rightSubs) :
        SameObjectShape (.mk name leftCode leftSubs segments)
          (.mk name rightCode rightSubs segments)

  inductive SameObjectShapes : List (Object Op) → List (Object Op) → Prop
    | nil : SameObjectShapes [] []
    | cons {left right : Object Op} {lefts rights : List (Object Op)}
        (head : SameObjectShape left right)
        (tail : SameObjectShapes lefts rights) :
        SameObjectShapes (left :: lefts) (right :: rights)
end

mutual
  theorem ObjectPlanRel.output_shape {raw fallback output : Object Op}
      {plan : MemorySpillSelect.ObjectPlan}
      (hrel : ObjectPlanRel raw fallback output plan) :
      SameObjectShape raw output := by
    cases hrel with
    | mk hspill hcode children =>
      exact .mk (ObjectPlansRel.output_shapes children)

  theorem ObjectPlansRel.output_shapes
      {raws fallbacks outputs : List (Object Op)}
      {plans : List MemorySpillSelect.ObjectPlan}
      (hrel : ObjectPlansRel raws fallbacks outputs plans) :
      SameObjectShapes raws outputs := by
    cases hrel with
    | nil => exact .nil
    | cons head tail =>
      exact .cons (ObjectPlanRel.output_shape head)
        (ObjectPlansRel.output_shapes tail)
end

theorem spillObjectWithFallback_shape {raw fallback : Object Op}
    {result : ObjectResult}
    (hspill : spillObjectWithFallback raw fallback = some result) :
    SameObjectShape raw result.object :=
  (spillObjectWithFallback_planRel hspill).output_shape

theorem ObjectPlanRel.spill_eq {raw fallback output : Object Op}
    {codeResult : Option Result}
    {children : List MemorySpillSelect.ObjectPlan}
    (hrel : ObjectPlanRel raw fallback output
      (MemorySpillSelect.ObjectPlan.mk codeResult children)) :
    spillBlock? raw.codeBlock = codeResult := by
  cases hrel
  assumption

theorem ObjectPlanRel.output_code_eq {raw fallback output : Object Op}
    {codeResult : Option Result}
    {children : List MemorySpillSelect.ObjectPlan}
    (hrel : ObjectPlanRel raw fallback output
      (MemorySpillSelect.ObjectPlan.mk codeResult children)) :
    output.codeBlock = plannedCode fallback.codeBlock codeResult := by
  cases hrel
  assumption

theorem ObjectPlanRel.spilled_code_eq {raw fallback output : Object Op}
    {result : Result} {children : List MemorySpillSelect.ObjectPlan}
    (hrel : ObjectPlanRel raw fallback output
      (MemorySpillSelect.ObjectPlan.mk (some result) children)) :
    output.codeBlock = result.block := by
  simpa [plannedCode] using hrel.output_code_eq

theorem ObjectPlanRel.fallback_code_eq {raw fallback output : Object Op}
    {children : List MemorySpillSelect.ObjectPlan}
    (hrel : ObjectPlanRel raw fallback output
      (MemorySpillSelect.ObjectPlan.mk none children)) :
    output.codeBlock = fallback.codeBlock := by
  simpa [plannedCode] using hrel.output_code_eq

theorem ObjectPlanRel.spill_facts {raw fallback output : Object Op}
    {result : Result} {children : List MemorySpillSelect.ObjectPlan}
    (hrel : ObjectPlanRel raw fallback output
      (MemorySpillSelect.ObjectPlan.mk (some result) children)) :
    ∃ guards, SpillFacts raw.codeBlock result guards :=
  spillBlock_facts hrel.spill_eq

/-- At a successful spill node, layout-reference resolution may be moved
through the emitted rewrite.  This is the exact bridge needed before applying
the block simulation to object code. -/
theorem ObjectPlanRel.resolve_spilled_code {raw fallback output : Object Op}
    {result : Result} {children : List MemorySpillSelect.ObjectPlan}
    (hrel : ObjectPlanRel raw fallback output
      (MemorySpillSelect.ObjectPlan.mk (some result) children))
    (L : EVM.Layout) :
    resolveForLayoutStmts L output.codeBlock =
      rewriteStmts result.layout.slots none []
        (resolveForLayoutStmts L
          (resolveMemoryGuardStmts result.base result.reserved raw.codeBlock)) := by
  obtain ⟨guards, hfacts⟩ := hrel.spill_facts
  rw [hrel.spilled_code_eq, hfacts.block_eq]
  simpa [resolveMemoryGuardStmts, resolveForLayoutStmts] using
    resolveForLayout_rewriteMemoryGuardStmts L result.layout.slots none
      result.base result.reserved [] raw.codeBlock

/-! ## Plan-indexed top-code semantic composition -/

/-- The interface expected from the block-level spilling theorem after object
layout references have been resolved.  The target run has the same outcome,
but its final environment and state are existential; only the optimizer-owned
scratch interval may differ from the guarded source state. -/
def SpillNodeRunSound (L : EVM.Layout) : Prop :=
  ∀ {raw : Block Op} {result : Result} {guards : List Nat}
    {sourceEnv : WordEnv} {sourceFinal : EvmState} {out : Outcome},
    SpillFacts raw result guards →
    GuardedExternals calls creates result.base result.reserved →
    Run (G result.base result.reserved)
      (resolveForLayoutStmts L
        (resolveMemoryGuardStmts result.base result.reserved raw))
      L.initState sourceEnv sourceFinal out →
    ∃ targetEnv targetFinal,
      Run D (resolveForLayoutStmts L result.block)
        L.initState targetEnv targetFinal out ∧
      ScratchRel result.base result.reserved sourceFinal targetFinal

/-- Explicit semantic callback for a fallback node.  This is a premise, not an
equivalence claim for arbitrary fallback objects; the production capstone must
instantiate it with its verified parser-erasure/optimizer pipeline. -/
def FallbackNodeRunSound (L : EVM.Layout)
    (sourceCode fallbackCode : Block Op) : Prop :=
  ∀ {sourceEnv : WordEnv} {sourceFinal : EvmState} {out : Outcome},
    Run D (resolveForLayoutStmts L sourceCode)
      L.initState sourceEnv sourceFinal out →
    Run D (resolveForLayoutStmts L fallbackCode)
      L.initState sourceEnv sourceFinal out

/-- Source execution appropriate to the current plan node.  Successful spill
nodes use the guarded dialect and the compiler-selected guard result;
fallback nodes use the ordinary resolved object semantics. -/
inductive PlannedTopRun (L : EVM.Layout) (raw : Object Op) :
    MemorySpillSelect.ObjectPlan → WordEnv → EvmState → Outcome → Prop
  | spilled {result : Result} {children : List MemorySpillSelect.ObjectPlan}
      {sourceEnv : WordEnv} {sourceFinal : EvmState} {out : Outcome}
      (externals : GuardedExternals calls creates result.base result.reserved)
      (run : Run (G result.base result.reserved)
        (resolveForLayoutStmts L
          (resolveMemoryGuardStmts result.base result.reserved raw.codeBlock))
        L.initState sourceEnv sourceFinal out) :
      PlannedTopRun L raw (MemorySpillSelect.ObjectPlan.mk (some result) children)
        sourceEnv sourceFinal out
  | fallback {children : List MemorySpillSelect.ObjectPlan}
      {sourceEnv : WordEnv} {sourceFinal : EvmState} {out : Outcome}
      (run : Run D
        (resolveForLayoutStmts L (eraseMemoryGuardStmts raw.codeBlock))
        L.initState sourceEnv sourceFinal out) :
      PlannedTopRun L raw (MemorySpillSelect.ObjectPlan.mk none children)
        sourceEnv sourceFinal out

/-- Postcondition selected by the same plan node.  The fallback branch is
exact because it is ordinary block equivalence; a spill branch retains the
precise scratch relation promised by the block theorem. -/
def PlannedFinalRel (plan : MemorySpillSelect.ObjectPlan)
    (sourceEnv : WordEnv) (sourceFinal : EvmState)
    (targetEnv : WordEnv) (targetFinal : EvmState) : Prop :=
  match plan with
  | .mk (some result) _ =>
      ScratchRel result.base result.reserved sourceFinal targetFinal
  | .mk none _ => targetEnv = sourceEnv ∧ targetFinal = sourceFinal

/-- Compose the forthcoming block theorem or the verified fallback theorem at
the top code of an already aligned plan node.  Recursive object alignment was
proved once by `spillObjectWithFallback_planRel`; no object recursion remains
for the final compiler capstone. -/
theorem ObjectPlanRel.compose_top_run {raw fallback output : Object Op}
    {plan : MemorySpillSelect.ObjectPlan} {L : EVM.Layout}
    (hrel : ObjectPlanRel raw fallback output plan)
    (hfallback : FallbackNodeRunSound
      (calls := calls) (creates := creates) L
        (eraseMemoryGuardStmts raw.codeBlock) fallback.codeBlock)
    (hspillSound : SpillNodeRunSound
      (calls := calls) (creates := creates) L)
    {sourceEnv : WordEnv} {sourceFinal : EvmState} {out : Outcome}
    (hsource : PlannedTopRun (calls := calls) (creates := creates)
      L raw plan sourceEnv sourceFinal out) :
    ∃ targetEnv targetFinal,
      Run D (resolveForLayoutStmts L output.codeBlock)
        L.initState targetEnv targetFinal out ∧
      PlannedFinalRel plan sourceEnv sourceFinal targetEnv targetFinal := by
  cases hsource with
  | @spilled result children sourceEnv sourceFinal out hexternals hrun =>
      obtain ⟨guards, hfacts⟩ := hrel.spill_facts
      obtain ⟨targetEnv, targetFinal, htarget, hscratch⟩ :=
        hspillSound hfacts hexternals hrun
      refine ⟨targetEnv, targetFinal, ?_, ?_⟩
      · rwa [hrel.spilled_code_eq]
      · exact hscratch
  | @fallback children sourceEnv sourceFinal out hrun =>
      have htargetFallback := hfallback hrun
      refine ⟨sourceEnv, sourceFinal, ?_, rfl, rfl⟩
      rwa [hrel.fallback_code_eq]

/-! A fallback callback at every paired node.  This is the generic recursive
premise later instantiated by the exact parser-erasure/optimizer object. -/
mutual
  inductive FallbackTreeRunSound (L : EVM.Layout) :
      Object Op → Object Op → Prop
    | mk {rawName fallbackName : String} {rawCode fallbackCode : Block Op}
        {rawSubs fallbackSubs : List (Object Op)}
        {rawData fallbackData : List (String × Data)}
        (top : FallbackNodeRunSound (calls := calls) (creates := creates)
          L (eraseMemoryGuardStmts rawCode) fallbackCode)
        (children : FallbackTreesRunSound L rawSubs fallbackSubs) :
        FallbackTreeRunSound L (.mk rawName rawCode rawSubs rawData)
          (.mk fallbackName fallbackCode fallbackSubs fallbackData)

  inductive FallbackTreesRunSound (L : EVM.Layout) :
      List (Object Op) → List (Object Op) → Prop
    | nil : FallbackTreesRunSound L [] []
    | cons {raw fallback : Object Op}
        {raws fallbacks : List (Object Op)}
        (head : FallbackTreeRunSound L raw fallback)
        (tail : FallbackTreesRunSound L raws fallbacks) :
        FallbackTreesRunSound L (raw :: raws) (fallback :: fallbacks)
end

mutual
  theorem erasedPipelineFallback_runSound (L : EVM.Layout) (raw : Object Op) :
      FallbackTreeRunSound (calls := calls) (creates := creates) L raw
        (optimizerPipelineObject (calls := calls) (creates := creates)
          (eraseMemoryGuardObject raw)) := by
    cases raw with
    | mk name code children segments =>
      simp only [eraseMemoryGuardObject, optimizerPipelineObject,
        optimizerPipelineObjectRounds]
      apply FallbackTreeRunSound.mk
      · intro sourceEnv sourceFinal out hrun
        exact (resolveObjectPipelineBlock_equiv
          (calls := calls) (creates := creates) L
          (eraseMemoryGuardStmts code)).run_iff.mp hrun
      · exact erasedPipelineFallbacks_runSound L children
  termination_by sizeOf raw

  theorem erasedPipelineFallbacks_runSound (L : EVM.Layout)
      (raws : List (Object Op)) :
      FallbackTreesRunSound (calls := calls) (creates := creates) L raws
        (optimizerPipelineObjectsRounds (calls := calls) (creates := creates)
          pipelineRounds (eraseMemoryGuardObjects raws)) := by
    cases raws with
    | nil => exact .nil
    | cons raw raws =>
      simp only [eraseMemoryGuardObjects, optimizerPipelineObjectsRounds]
      exact .cons (erasedPipelineFallback_runSound L raw)
        (erasedPipelineFallbacks_runSound L raws)
  termination_by sizeOf raws
end

def PlannedNodeRunSound (L : EVM.Layout) (raw output : Object Op)
    (plan : MemorySpillSelect.ObjectPlan) : Prop :=
  ∀ {sourceEnv : WordEnv} {sourceFinal : EvmState} {out : Outcome},
    PlannedTopRun (calls := calls) (creates := creates)
      L raw plan sourceEnv sourceFinal out →
    ∃ targetEnv targetFinal,
      Run D (resolveForLayoutStmts L output.codeBlock)
        L.initState targetEnv targetFinal out ∧
      PlannedFinalRel plan sourceEnv sourceFinal targetEnv targetFinal

/-! The composed run transformer at every output-plan node. -/
mutual
  inductive PlannedObjectRunSound (L : EVM.Layout) :
      Object Op → Object Op → MemorySpillSelect.ObjectPlan → Prop
    | mk {rawName outputName : String} {rawCode outputCode : Block Op}
        {rawSubs outputSubs : List (Object Op)}
        {rawData outputData : List (String × Data)}
        {codeResult : Option Result}
        {childPlans : List MemorySpillSelect.ObjectPlan}
        (top : PlannedNodeRunSound (calls := calls) (creates := creates) L
          (.mk rawName rawCode rawSubs rawData)
          (.mk outputName outputCode outputSubs outputData)
          (.mk codeResult childPlans))
        (children : PlannedObjectsRunSound L rawSubs outputSubs childPlans) :
        PlannedObjectRunSound L
          (.mk rawName rawCode rawSubs rawData)
          (.mk outputName outputCode outputSubs outputData)
          (.mk codeResult childPlans)

  inductive PlannedObjectsRunSound (L : EVM.Layout) :
      List (Object Op) → List (Object Op) →
        List MemorySpillSelect.ObjectPlan → Prop
    | nil : PlannedObjectsRunSound L [] [] []
    | cons {raw output : Object Op} {raws outputs : List (Object Op)}
        {plan : MemorySpillSelect.ObjectPlan}
        {plans : List MemorySpillSelect.ObjectPlan}
        (head : PlannedObjectRunSound L raw output plan)
        (tail : PlannedObjectsRunSound L raws outputs plans) :
        PlannedObjectsRunSound L (raw :: raws) (output :: outputs)
          (plan :: plans)
end

mutual
  theorem ObjectPlanRel.compose_all_runs {raw fallback output : Object Op}
      {plan : MemorySpillSelect.ObjectPlan} {L : EVM.Layout}
      (hrel : ObjectPlanRel raw fallback output plan)
      (hfallback : FallbackTreeRunSound
        (calls := calls) (creates := creates) L raw fallback)
      (hspillSound : SpillNodeRunSound
        (calls := calls) (creates := creates) L) :
      PlannedObjectRunSound (calls := calls) (creates := creates)
        L raw output plan := by
    cases hrel with
    | @mk name rawCode fallbackCode rawSubs fallbackSubs outputSubs rawData
        fallbackData outputCode codeResult childPlans hspill hcode children =>
      cases hfallback with
      | @mk _ _ _ _ _ _ _ _ top fallbackChildren =>
        apply PlannedObjectRunSound.mk
        · intro sourceEnv sourceFinal out hsource
          exact (ObjectPlanRel.mk (fallbackData := fallbackData)
            hspill hcode children).compose_top_run
            top hspillSound hsource
        · exact ObjectPlansRel.compose_all_runs children fallbackChildren
            hspillSound
  termination_by sizeOf raw

  theorem ObjectPlansRel.compose_all_runs
      {raws fallbacks outputs : List (Object Op)}
      {plans : List MemorySpillSelect.ObjectPlan} {L : EVM.Layout}
      (hrel : ObjectPlansRel raws fallbacks outputs plans)
      (hfallback : FallbackTreesRunSound
        (calls := calls) (creates := creates) L raws fallbacks)
      (hspillSound : SpillNodeRunSound
        (calls := calls) (creates := creates) L) :
      PlannedObjectsRunSound (calls := calls) (creates := creates)
        L raws outputs plans := by
    cases hrel with
    | nil =>
      cases hfallback
      exact .nil
    | cons head tail =>
      cases hfallback with
      | cons fallbackHead fallbackTail =>
        exact .cons (ObjectPlanRel.compose_all_runs head fallbackHead hspillSound)
          (ObjectPlansRel.compose_all_runs tail fallbackTail hspillSound)
  termination_by sizeOf raws
end

theorem PlannedObjectRunSound.top_run {L : EVM.Layout}
    {raw output : Object Op} {plan : MemorySpillSelect.ObjectPlan}
    (hsound : PlannedObjectRunSound (calls := calls) (creates := creates)
      L raw output plan) :
    PlannedNodeRunSound (calls := calls) (creates := creates)
      L raw output plan := by
  cases hsound
  assumption

/-- All-node semantic certificate for the exact production pairing: raw
guard-bearing syntax is paired with the optimizer pipeline of the parser's
exact memoryguard erasure. -/
theorem spillObjectWithErasedPipelineFallback_all_runs
    {raw output : Object Op} {plan : MemorySpillSelect.ObjectPlan}
    {selected : Nat} {L : EVM.Layout}
    (hbuild : spillObjectWithFallback raw
      (optimizerPipelineObject (calls := calls) (creates := creates)
        (eraseMemoryGuardObject raw)) =
        some { «object» := output, plan := plan, selected := selected })
    (hspillSound : SpillNodeRunSound
      (calls := calls) (creates := creates) L) :
    PlannedObjectRunSound (calls := calls) (creates := creates)
      L raw output plan := by
  have hrel := spillObjectWithFallback_planRel hbuild
  exact hrel.compose_all_runs (erasedPipelineFallback_runSound L raw)
    hspillSound

/-- Top-code projection of the all-node production certificate, ready for the
object compiler capstone. -/
theorem spillObjectWithErasedPipelineFallback_top_run
    {raw output : Object Op} {plan : MemorySpillSelect.ObjectPlan}
    {selected : Nat} {L : EVM.Layout}
    (hbuild : spillObjectWithFallback raw
      (optimizerPipelineObject (calls := calls) (creates := creates)
        (eraseMemoryGuardObject raw)) =
        some { «object» := output, plan := plan, selected := selected })
    (hspillSound : SpillNodeRunSound
      (calls := calls) (creates := creates) L) :
    PlannedNodeRunSound (calls := calls) (creates := creates)
      L raw output plan :=
  (spillObjectWithErasedPipelineFallback_all_runs hbuild hspillSound).top_run

end YulEvmCompiler.Optimizer.MemorySpillObjectSound
