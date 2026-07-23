import YulEvmCompiler.ObjectResolve
import YulEvmCompiler.Optimizer.Implementation.MemorySpillLayoutSound
import YulEvmCompiler.Optimizer.Spec.MemoryGuard
set_option warningAsError true
/-!
# Syntax origins for memory-spill simulation

The spill allocator records frames and direct calls from the block on which its
policy ran.  Object compilation may subsequently execute the same syntax after
`resolveForLayoutStmts` has replaced object-layout references.  This module
pins down the structural facts shared by those two modes:

* identity execution uses the policy block verbatim;
* object execution maps every frame body through `resolveForLayoutStmts`;
* frame owners, signatures, declared names, and direct call names are unchanged;
* a dynamic `lookupFun` hit can be related to an exact covered frame; and
* every direct call retained by `frameCallsStmts` is present in the exact
  `FrameInfo.callees` entry when its name is defined in the object-wide frame
  set.

These lemmas deliberately contain no semantic simulation.  They are the
proof-ready bridge from the policy AST to the AST appearing in a `Step`
derivation.
-/

namespace YulEvmCompiler.Optimizer.MemorySpillOriginSound

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open MemorySpillSelect

/-! ## Policy block versus executed block -/

/-- The two AST origins that the spill proof must support. -/
inductive OriginMode where
  /-- Direct block compilation: the policy and executed syntax coincide. -/
  | identity
  /-- Object compilation: object references have been resolved for `layout`. -/
  | object (layout : YulSemantics.EVM.Layout)

/-- The block actually interpreted in a given origin mode. -/
def OriginMode.execBlock : OriginMode → Block Op → Block Op
  | .identity, body => body
  | .object layout, body => resolveForLayoutStmts layout body

/-- The exact executed counterpart of a policy frame. -/
def OriginMode.execFrame : OriginMode → Frame → Frame
  | .identity, frame => frame
  | .object layout, frame =>
      { frame with body := resolveForLayoutStmts layout frame.body }

@[simp] theorem OriginMode.execBlock_identity (body : Block Op) :
    OriginMode.identity.execBlock body = body := rfl

@[simp] theorem OriginMode.execBlock_object (layout : YulSemantics.EVM.Layout)
    (body : Block Op) :
    (OriginMode.object layout).execBlock body =
      resolveForLayoutStmts layout body := rfl

@[simp] theorem OriginMode.execFrame_owner (mode : OriginMode) (frame : Frame) :
    (mode.execFrame frame).owner = frame.owner := by
  cases mode <;> rfl

@[simp] theorem OriginMode.execFrame_params (mode : OriginMode) (frame : Frame) :
    (mode.execFrame frame).params = frame.params := by
  cases mode <;> rfl

@[simp] theorem OriginMode.execFrame_returns (mode : OriginMode) (frame : Frame) :
    (mode.execFrame frame).returns = frame.returns := by
  cases mode <;> rfl

/-! ## Object resolution preserves call syntax -/

mutual
  theorem callsExpr_resolveForLayout (layout : YulSemantics.EVM.Layout) :
      ∀ expression : Expr Op,
        callsExpr (resolveForLayoutExpr layout expression) = callsExpr expression := by
    intro expression
    cases expression with
    | lit literal => rfl
    | var name => rfl
    | builtin op args =>
        cases op <;> simp only [resolveForLayoutExpr, callsExpr] <;>
          try exact callsArgs_resolveForLayout layout args
        all_goals
          cases args with
          | nil => rfl
          | cons expression rest =>
              cases expression with
              | lit literal =>
                  cases literal <;> try exact callsArgs_resolveForLayout layout _
                  case string name =>
                    cases rest <;> try rfl
                    exact callsArgs_resolveForLayout layout _
              | var name => exact callsArgs_resolveForLayout layout _
              | builtin op nested => exact callsArgs_resolveForLayout layout _
              | call fn nested => exact callsArgs_resolveForLayout layout _
    | call fn args =>
        simp only [resolveForLayoutExpr, callsExpr]
        rw [callsArgs_resolveForLayout]
  termination_by expression => 2 * sizeOf expression + 1

  theorem callsArgs_resolveForLayout (layout : YulSemantics.EVM.Layout) :
      ∀ expressions : List (Expr Op),
        callsArgs (resolveForLayoutExprs layout expressions) = callsArgs expressions
    | [] => rfl
    | expression :: rest => by
        simp only [resolveForLayoutExprs, callsArgs]
        rw [callsExpr_resolveForLayout, callsArgs_resolveForLayout]
  termination_by expressions => 2 * sizeOf expressions
  decreasing_by all_goals simp_all <;> omega
end

mutual
  theorem frameCallsStmt_resolveForLayout (layout : YulSemantics.EVM.Layout) :
      ∀ statement : Stmt Op,
        frameCallsStmt (resolveForLayoutStmt layout statement) =
          frameCallsStmt statement := by
    intro statement
    cases statement with
    | block body =>
        rw [resolveForLayoutStmt_block]
        simp only [frameCallsStmt]
        exact frameCallsStmts_resolveForLayout layout body
    | funDef name params returns body =>
        simp [resolveForLayoutStmt.eq_def, frameCallsStmt]
    | letDecl names value =>
        cases value <;>
          simp [resolveForLayoutStmt.eq_def, frameCallsStmt,
            callsExpr_resolveForLayout]
    | assign names value =>
        simp [resolveForLayoutStmt.eq_def, frameCallsStmt,
          callsExpr_resolveForLayout]
    | cond condition body =>
        rw [resolveForLayoutStmt_cond]
        simp only [frameCallsStmt]
        rw [callsExpr_resolveForLayout,
          frameCallsStmts_resolveForLayout layout body]
    | «switch» condition cases fallback =>
        cases fallback with
        | none =>
            rw [resolveForLayoutStmt_switch, Option.map_none,
              frameCallsStmt.eq_8, frameCallsStmt.eq_8,
              callsExpr_resolveForLayout,
              frameCallsCases_resolveForLayout layout cases]
        | some fallback =>
            rw [resolveForLayoutStmt_switch, Option.map_some,
              frameCallsStmt.eq_7, frameCallsStmt.eq_7,
              callsExpr_resolveForLayout,
              frameCallsCases_resolveForLayout layout cases,
              frameCallsStmts_resolveForLayout layout fallback]
    | forLoop init condition post body =>
        rw [resolveForLayoutStmt_forLoop]
        simp only [frameCallsStmt]
        rw [frameCallsStmts_resolveForLayout layout init,
          callsExpr_resolveForLayout,
          frameCallsStmts_resolveForLayout layout post,
          frameCallsStmts_resolveForLayout layout body]
    | exprStmt expression =>
        simp [resolveForLayoutStmt.eq_def, frameCallsStmt,
          callsExpr_resolveForLayout]
    | «break» => simp [resolveForLayoutStmt.eq_def, frameCallsStmt]
    | «continue» => simp [resolveForLayoutStmt.eq_def, frameCallsStmt]
    | «leave» => simp [resolveForLayoutStmt.eq_def, frameCallsStmt]
  termination_by statement => 2 * sizeOf statement

  theorem frameCallsStmts_resolveForLayout (layout : YulSemantics.EVM.Layout) :
      ∀ body : Block Op,
        frameCallsStmts (resolveForLayoutStmts layout body) =
          frameCallsStmts body
    | [] => by simp [frameCallsStmts]
    | statement :: rest => by
        simp only [resolveForLayoutStmts, frameCallsStmts]
        rw [frameCallsStmt_resolveForLayout, frameCallsStmts_resolveForLayout]
  termination_by body => 2 * sizeOf body + 1

  theorem frameCallsCases_resolveForLayout (layout : YulSemantics.EVM.Layout) :
      ∀ cases : List (Literal × Block Op),
        frameCallsCases (resolveForLayoutCases layout cases) =
          frameCallsCases cases
    | [] => by rw [resolveForLayoutCases]
    | (literal, body) :: rest => by
        simp only [resolveForLayoutCases, frameCallsCases]
        rw [frameCallsStmts_resolveForLayout, frameCallsCases_resolveForLayout]
  termination_by cases => 2 * sizeOf cases + 1
  decreasing_by all_goals simp_all <;> omega
end

@[simp] theorem OriginMode.execFrame_calls (mode : OriginMode) (frame : Frame) :
    frameCallsStmts (mode.execFrame frame).body = frameCallsStmts frame.body := by
  cases mode with
  | identity => rfl
  | «object» layout => exact frameCallsStmts_resolveForLayout layout frame.body

/-! ## Object resolution preserves the exact frame tree -/

mutual
  theorem nestedFramesStmt_resolveForLayout (layout : YulSemantics.EVM.Layout) :
      ∀ statement : Stmt Op,
        nestedFramesStmt (resolveForLayoutStmt layout statement) =
          (nestedFramesStmt statement).map
            (OriginMode.object layout).execFrame := by
    intro statement
    cases statement with
    | block body =>
        rw [resolveForLayoutStmt_block]
        simp only [nestedFramesStmt]
        exact nestedFramesStmts_resolveForLayout layout body
    | funDef name params returns body =>
        rw [resolveForLayoutStmt_funDef]
        simp only [nestedFramesStmt, List.map_cons]
        rw [nestedFramesStmts_resolveForLayout layout body]
        rfl
    | letDecl names value => simp [resolveForLayoutStmt.eq_def, nestedFramesStmt]
    | assign names value => simp [resolveForLayoutStmt.eq_def, nestedFramesStmt]
    | cond condition body =>
        rw [resolveForLayoutStmt_cond]
        simp only [nestedFramesStmt]
        rw [nestedFramesStmts_resolveForLayout layout body]
    | «switch» condition cases fallback =>
        cases fallback with
        | none =>
            rw [resolveForLayoutStmt_switch, Option.map_none,
              nestedFramesStmt.eq_5, nestedFramesStmt.eq_5,
              nestedFramesCases_resolveForLayout layout cases,
              List.map_append]
            simp
        | some fallback =>
            rw [resolveForLayoutStmt_switch, Option.map_some,
              nestedFramesStmt.eq_4, nestedFramesStmt.eq_4,
              nestedFramesCases_resolveForLayout layout cases,
              nestedFramesStmts_resolveForLayout layout fallback,
              List.map_append]
    | forLoop init condition post body =>
        rw [resolveForLayoutStmt_forLoop]
        simp only [nestedFramesStmt, List.map_append]
        rw [nestedFramesStmts_resolveForLayout layout init,
          nestedFramesStmts_resolveForLayout layout post,
          nestedFramesStmts_resolveForLayout layout body]
    | exprStmt expression => simp [resolveForLayoutStmt.eq_def, nestedFramesStmt]
    | «break» => simp [resolveForLayoutStmt.eq_def, nestedFramesStmt]
    | «continue» => simp [resolveForLayoutStmt.eq_def, nestedFramesStmt]
    | «leave» => simp [resolveForLayoutStmt.eq_def, nestedFramesStmt]
  termination_by statement => 2 * sizeOf statement

  theorem nestedFramesStmts_resolveForLayout (layout : YulSemantics.EVM.Layout) :
      ∀ body : Block Op,
        nestedFramesStmts (resolveForLayoutStmts layout body) =
          (nestedFramesStmts body).map
            (OriginMode.object layout).execFrame
    | [] => by simp [nestedFramesStmts]
    | statement :: rest => by
        simp only [resolveForLayoutStmts, nestedFramesStmts]
        rw [nestedFramesStmt_resolveForLayout,
          nestedFramesStmts_resolveForLayout, List.map_append]
  termination_by body => 2 * sizeOf body + 1

  theorem nestedFramesCases_resolveForLayout (layout : YulSemantics.EVM.Layout) :
      ∀ cases : List (Literal × Block Op),
        nestedFramesCases (resolveForLayoutCases layout cases) =
          (nestedFramesCases cases).map
            (OriginMode.object layout).execFrame
    | [] => by rw [resolveForLayoutCases]; simp [nestedFramesCases]
    | (literal, body) :: rest => by
        simp only [resolveForLayoutCases, nestedFramesCases]
        rw [nestedFramesStmts_resolveForLayout,
          nestedFramesCases_resolveForLayout, List.map_append]
  termination_by cases => 2 * sizeOf cases + 1
  decreasing_by all_goals simp_all <;> omega
end

theorem frames_execBlock (mode : OriginMode) (body : Block Op) :
    frames (mode.execBlock body) = (frames body).map mode.execFrame := by
  cases mode with
  | identity =>
      change frames body = (frames body).map (fun frame => frame)
      simp
  | «object» layout =>
      simp only [OriginMode.execBlock, frames, List.map_cons]
      rw [nestedFramesStmts_resolveForLayout]
      rfl

theorem execFrame_mem_frames {mode : OriginMode} {body : Block Op} {frame : Frame}
    (hframe : frame ∈ frames body) :
    mode.execFrame frame ∈ frames (mode.execBlock body) := by
  rw [frames_execBlock]
  exact List.mem_map.mpr ⟨frame, hframe, rfl⟩

theorem frame_mem_of_execFrame_mem {mode : OriginMode} {body : Block Op}
    {executed : Frame} (hframe : executed ∈ frames (mode.execBlock body)) :
    ∃ policy ∈ frames body, executed = mode.execFrame policy := by
  rw [frames_execBlock] at hframe
  obtain ⟨policy, hpolicy, rfl⟩ := List.mem_map.mp hframe
  exact ⟨policy, hpolicy, rfl⟩

/-! ## Declared-name and policy-check invariance -/

mutual
  theorem frameNamesStmt_resolveForLayout (layout : YulSemantics.EVM.Layout) :
      ∀ statement : Stmt Op,
        frameNamesStmt (resolveForLayoutStmt layout statement) =
          frameNamesStmt statement := by
    intro statement
    cases statement with
    | block body =>
        rw [resolveForLayoutStmt_block]
        simp only [frameNamesStmt]
        exact frameNamesStmts_resolveForLayout layout body
    | funDef name params returns body =>
        simp [resolveForLayoutStmt.eq_def, frameNamesStmt]
    | letDecl names value => simp [resolveForLayoutStmt.eq_def, frameNamesStmt]
    | assign names value => simp [resolveForLayoutStmt.eq_def, frameNamesStmt]
    | cond condition body =>
        rw [resolveForLayoutStmt_cond]
        simp only [frameNamesStmt]
        rw [frameNamesStmts_resolveForLayout layout body]
    | «switch» condition cases fallback =>
        cases fallback with
        | none =>
            rw [resolveForLayoutStmt_switch, Option.map_none,
              frameNamesStmt.eq_6, frameNamesStmt.eq_6,
              frameNamesCases_resolveForLayout layout cases]
        | some fallback =>
            rw [resolveForLayoutStmt_switch, Option.map_some,
              frameNamesStmt.eq_5, frameNamesStmt.eq_5,
              frameNamesCases_resolveForLayout layout cases,
              frameNamesStmts_resolveForLayout layout fallback]
    | forLoop init condition post body =>
        rw [resolveForLayoutStmt_forLoop]
        simp only [frameNamesStmt]
        rw [frameNamesStmts_resolveForLayout layout init,
          frameNamesStmts_resolveForLayout layout post,
          frameNamesStmts_resolveForLayout layout body]
    | exprStmt expression => simp [resolveForLayoutStmt.eq_def, frameNamesStmt]
    | «break» => simp [resolveForLayoutStmt.eq_def, frameNamesStmt]
    | «continue» => simp [resolveForLayoutStmt.eq_def, frameNamesStmt]
    | «leave» => simp [resolveForLayoutStmt.eq_def, frameNamesStmt]
  termination_by statement => 2 * sizeOf statement

  theorem frameNamesStmts_resolveForLayout (layout : YulSemantics.EVM.Layout) :
      ∀ body : Block Op,
        frameNamesStmts (resolveForLayoutStmts layout body) = frameNamesStmts body
    | [] => by simp [frameNamesStmts]
    | statement :: rest => by
        simp only [resolveForLayoutStmts, frameNamesStmts]
        rw [frameNamesStmt_resolveForLayout, frameNamesStmts_resolveForLayout]
  termination_by body => 2 * sizeOf body + 1

  theorem frameNamesCases_resolveForLayout (layout : YulSemantics.EVM.Layout) :
      ∀ cases : List (Literal × Block Op),
        frameNamesCases (resolveForLayoutCases layout cases) = frameNamesCases cases
    | [] => by rw [resolveForLayoutCases]
    | (literal, body) :: rest => by
        simp only [resolveForLayoutCases, frameNamesCases]
        rw [frameNamesStmts_resolveForLayout, frameNamesCases_resolveForLayout]
  termination_by cases => 2 * sizeOf cases + 1
  decreasing_by all_goals simp_all <;> omega
end

@[simp] theorem OriginMode.execFrame_names (mode : OriginMode) (frame : Frame) :
    frameNames (mode.execFrame frame) = frameNames frame := by
  cases mode with
  | identity => rfl
  | «object» layout =>
      simp only [OriginMode.execFrame, frameNames]
      rw [frameNamesStmts_resolveForLayout]

theorem framesWF_execBlock (mode : OriginMode) (body : Block Op) :
    framesWF (frames (mode.execBlock body)) = framesWF (frames body) := by
  rw [frames_execBlock]
  unfold framesWF
  have howners :
      ((frames body).map mode.execFrame).map (fun frame => frame.owner) =
        (frames body).map (fun frame => frame.owner) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro frame hframe
    exact OriginMode.execFrame_owner mode frame
  rw [howners]

private theorem find_execFrame_owner (mode : OriginMode) (owner : Owner) :
    ∀ fs : List Frame,
      (fs.map mode.execFrame).find? (fun frame => frame.owner = owner) =
        (fs.find? fun frame => frame.owner = owner).map mode.execFrame := by
  intro fs
  induction fs with
  | nil => rfl
  | cons frame rest ih =>
      simp only [List.map_cons, List.find?_cons, OriginMode.execFrame_owner]
      by_cases howner : frame.owner = owner
      · simp [howner]
      · simp [howner, ih]

theorem selectedWF_execBlock (mode : OriginMode) (body : Block Op)
    (selected : SpillSet) :
    selectedWF (frames (mode.execBlock body)) selected =
      selectedWF (frames body) selected := by
  simp only [selectedWF, frames_execBlock]
  congr 1
  funext key
  rw [find_execFrame_owner]
  cases hfind : (frames body).find? fun frame => frame.owner = key.owner with
  | none => rfl
  | some frame => simp [OriginMode.execFrame_names]

/-! ## Dynamic function-environment coverage -/

/-- Exact frame shape corresponding to a function declaration.  `encodeBody`
allows the same lookup invariant to describe guarded syntax, identity ordinary
syntax, or layout-resolved ordinary syntax. -/
def DeclCovered (D : Dialect) (encodeBody : Block D.Op → Block Op)
    (allFrames : List Frame) (name : Ident) (decl : FDecl D) : Prop :=
  ∃ frame ∈ allFrames,
    frame.owner = some name ∧
      frame.params = decl.params ∧
      frame.returns = decl.rets ∧
      frame.body = encodeBody decl.body

def ScopeCovered (D : Dialect) (encodeBody : Block D.Op → Block Op)
    (allFrames : List Frame) (scope : FScope D) : Prop :=
  ∀ name decl, (name, decl) ∈ scope →
    DeclCovered D encodeBody allFrames name decl

/-- Every declaration reachable through the dynamic scope stack has an exact
frame in `allFrames`. -/
def FunsCovered (D : Dialect) (encodeBody : Block D.Op → Block Op)
    (allFrames : List Frame) (funs : FunEnv D) : Prop :=
  ∀ scope ∈ funs, ScopeCovered D encodeBody allFrames scope

theorem FunsCovered.nil (D : Dialect) (encodeBody : Block D.Op → Block Op)
    (allFrames : List Frame) :
    FunsCovered D encodeBody allFrames [] := by
  intro scope hscope
  simp at hscope

theorem FunsCovered.cons {D : Dialect} {encodeBody : Block D.Op → Block Op}
    {allFrames : List Frame} {scope : FScope D} {funs : FunEnv D}
    (hscope : ScopeCovered D encodeBody allFrames scope)
    (hfuns : FunsCovered D encodeBody allFrames funs) :
    FunsCovered D encodeBody allFrames (scope :: funs) := by
  intro candidate hmem
  rcases List.mem_cons.mp hmem with heq | htail
  · exact heq ▸ hscope
  · exact hfuns candidate htail

theorem FunsCovered.tail {D : Dialect} {encodeBody : Block D.Op → Block Op}
    {allFrames : List Frame} {scope : FScope D} {funs : FunEnv D}
    (hcovered : FunsCovered D encodeBody allFrames (scope :: funs)) :
    FunsCovered D encodeBody allFrames funs := by
  intro candidate hmem
  exact hcovered candidate (by simp [hmem])

/-- A successful dynamic lookup identifies a declaration whose signature and
body agree with an exact frame from the policy certificate. -/
theorem FunsCovered.lookup {D : Dialect} {encodeBody : Block D.Op → Block Op}
    {allFrames : List Frame} {funs : FunEnv D} {name : Ident}
    {decl : FDecl D} {closure : FunEnv D}
    (hcovered : FunsCovered D encodeBody allFrames funs)
    (hlookup : lookupFun funs name = some (decl, closure)) :
    DeclCovered D encodeBody allFrames name decl ∧
      FunsCovered D encodeBody allFrames closure := by
  induction funs with
  | nil => simp [lookupFun] at hlookup
  | cons scope rest ih =>
      simp only [lookupFun] at hlookup
      cases hfind : scope.find? (fun item => item.1 = name) with
      | none =>
          rw [hfind] at hlookup
          exact ih hcovered.tail hlookup
      | some item =>
          rw [hfind] at hlookup
          obtain ⟨foundName, foundDecl⟩ := item
          simp only [Option.some.injEq, Prod.mk.injEq] at hlookup
          rcases hlookup with ⟨hdecl, hclosure⟩
          subst decl
          subst closure
          have hname : foundName = name := by
            simpa using List.find?_some hfind
          subst foundName
          have hmem : (name, foundDecl) ∈ scope := List.mem_of_find?_eq_some hfind
          exact ⟨hcovered scope (by simp) name foundDecl hmem, hcovered⟩

/-- A declaration hoisted directly by a block has the exact function frame
collected from that block.  This is the syntax-level constructor used when a
`Step.block` or loop initializer pushes a new dynamic function scope. -/
private theorem hoist_decl_mem_nestedFrames {body : Block Op} {name : Ident}
    {decl : FDecl evm} (hmem : (name, decl) ∈ hoist evm body) :
    ∃ frame ∈ nestedFramesStmts body,
      frame.owner = some name ∧
        frame.params = decl.params ∧
        frame.returns = decl.rets ∧
        frame.body = decl.body := by
  induction body with
  | nil => simp [hoist] at hmem
  | cons statement rest ih =>
      cases statement with
      | funDef foundName params returns funBody =>
          simp only [hoist, List.filterMap_cons, List.mem_cons] at hmem
          rcases hmem with heq | hrest
          · simp only [Prod.mk.injEq] at heq
            rcases heq with ⟨hname, hdecl⟩
            subst foundName
            subst decl
            refine ⟨
              { owner := some name, params, returns, body := funBody }, ?_, rfl,
              rfl, rfl, rfl⟩
            simp [nestedFramesStmts, nestedFramesStmt]
          · obtain ⟨frame, hframe, howner, hparams, hreturns, hbody⟩ := ih hrest
            refine ⟨frame, ?_, howner, hparams, hreturns, hbody⟩
            simp only [nestedFramesStmts]
            exact List.mem_append_right _ hframe
      | block nested =>
          simp only [hoist, List.filterMap_cons] at hmem
          obtain ⟨frame, hframe, howner, hparams, hreturns, hbody⟩ := ih hmem
          exact ⟨frame, by
            simp only [nestedFramesStmts, nestedFramesStmt]
            exact List.mem_append_right _ hframe,
            howner, hparams, hreturns, hbody⟩
      | letDecl names value =>
          simp only [hoist, List.filterMap_cons] at hmem
          simpa [nestedFramesStmts, nestedFramesStmt] using ih hmem
      | assign names value =>
          simp only [hoist, List.filterMap_cons] at hmem
          simpa [nestedFramesStmts, nestedFramesStmt] using ih hmem
      | cond condition nested =>
          simp only [hoist, List.filterMap_cons] at hmem
          obtain ⟨frame, hframe, howner, hparams, hreturns, hbody⟩ := ih hmem
          exact ⟨frame, by
            simp only [nestedFramesStmts, nestedFramesStmt]
            exact List.mem_append_right _ hframe,
            howner, hparams, hreturns, hbody⟩
      | «switch» condition cases fallback =>
          simp only [hoist, List.filterMap_cons] at hmem
          obtain ⟨frame, hframe, howner, hparams, hreturns, hbody⟩ := ih hmem
          exact ⟨frame, by
            simp only [nestedFramesStmts]
            exact List.mem_append_right _ hframe,
            howner, hparams, hreturns, hbody⟩
      | forLoop init condition post loopBody =>
          simp only [hoist, List.filterMap_cons] at hmem
          obtain ⟨frame, hframe, howner, hparams, hreturns, hbody⟩ := ih hmem
          exact ⟨frame, by
            simp only [nestedFramesStmts, nestedFramesStmt]
            exact List.mem_append_right _ hframe,
            howner, hparams, hreturns, hbody⟩
      | exprStmt expression =>
          simp only [hoist, List.filterMap_cons] at hmem
          simpa [nestedFramesStmts, nestedFramesStmt] using ih hmem
      | «break» =>
          simp only [hoist, List.filterMap_cons] at hmem
          simpa [nestedFramesStmts, nestedFramesStmt] using ih hmem
      | «continue» =>
          simp only [hoist, List.filterMap_cons] at hmem
          simpa [nestedFramesStmts, nestedFramesStmt] using ih hmem
      | «leave» =>
          simp only [hoist, List.filterMap_cons] at hmem
          simpa [nestedFramesStmts, nestedFramesStmt] using ih hmem

theorem scopeCovered_hoist_frames (body : Block Op) :
    ScopeCovered evm (fun executed => executed) (frames body) (hoist evm body) := by
  intro name decl hmem
  obtain ⟨frame, hframe, howner, hparams, hreturns, hbody⟩ :=
    hoist_decl_mem_nestedFrames hmem
  exact ⟨frame, by simp [frames, hframe], howner, hparams, hreturns, hbody⟩

theorem rootFunsCovered (body : Block Op) :
    FunsCovered evm (fun executed => executed) (frames body) [hoist evm body] :=
  FunsCovered.cons (scopeCovered_hoist_frames body)
    (FunsCovered.nil evm (fun executed => executed) (frames body))

/-- Root dynamic lookup, specialized to the exact frame list collected by the
spill policy. -/
theorem lookup_root_frame {body : Block Op} {name : Ident} {decl : FDecl evm}
    {closure : FunEnv evm}
    (hlookup : lookupFun [hoist evm body] name = some (decl, closure)) :
    DeclCovered evm (fun executed => executed) (frames body) name decl :=
  (rootFunsCovered body).lookup hlookup |>.1

/-! ### Guarded-source and executed-mode constructors -/

private def guardedDeclToEvm {calls : ExternalCalls} {creates : ExternalCreates}
    {base reserved : Nat}
    (decl : FDecl (guardedEvm calls creates base reserved)) : FDecl evm :=
  { params := decl.params, rets := decl.rets, body := decl.body }

private theorem guardedHoist_toEvm (calls : ExternalCalls)
    (creates : ExternalCreates) (base reserved : Nat) : ∀ body : Block Op,
    (hoist (guardedEvm calls creates base reserved) body).map
      (fun item => (item.1, guardedDeclToEvm item.2)) = hoist evm body
  | [] => rfl
  | statement :: rest => by
      cases statement <;>
        simp only [hoist, List.filterMap_cons, List.map_cons,
          guardedDeclToEvm]
      case funDef =>
        congr 1
        change (hoist (guardedEvm calls creates base reserved) rest).map
          (fun item => (item.1, guardedDeclToEvm item.2)) = hoist evm rest
        exact guardedHoist_toEvm calls creates base reserved rest
      all_goals
        change (hoist (guardedEvm calls creates base reserved) rest).map
          (fun item => (item.1, guardedDeclToEvm item.2)) = hoist evm rest
        exact guardedHoist_toEvm calls creates base reserved rest

theorem guardedScopeCovered (calls : ExternalCalls) (creates : ExternalCreates)
    (base reserved : Nat) (body : Block Op) :
    ScopeCovered (guardedEvm calls creates base reserved)
      (fun executed => executed) (frames body)
      (hoist (guardedEvm calls creates base reserved) body) := by
  intro name decl hmem
  let ordinary := guardedDeclToEvm decl
  have hmapped : (name, ordinary) ∈
      (hoist (guardedEvm calls creates base reserved) body).map
        (fun item => (item.1, guardedDeclToEvm item.2)) :=
    List.mem_map.mpr ⟨(name, decl), hmem, rfl⟩
  have hordinary : (name, ordinary) ∈ hoist evm body := by
    rw [guardedHoist_toEvm calls creates base reserved body] at hmapped
    exact hmapped
  obtain ⟨frame, hframe, howner, hparams, hreturns, hbody⟩ :=
    scopeCovered_hoist_frames body name ordinary hordinary
  exact ⟨frame, hframe, howner, hparams, hreturns, hbody⟩

theorem guardedRootFunsCovered (calls : ExternalCalls) (creates : ExternalCreates)
    (base reserved : Nat) (body : Block Op) :
    FunsCovered (guardedEvm calls creates base reserved)
      (fun executed => executed) (frames body)
      [hoist (guardedEvm calls creates base reserved) body] :=
  FunsCovered.cons (guardedScopeCovered calls creates base reserved body)
    (FunsCovered.nil (guardedEvm calls creates base reserved)
      (fun executed => executed) (frames body))

theorem guardedLookup_root_frame (calls : ExternalCalls)
    (creates : ExternalCreates) (base reserved : Nat) {body : Block Op}
    {name : Ident} {decl : FDecl (guardedEvm calls creates base reserved)}
    {closure : FunEnv (guardedEvm calls creates base reserved)}
    (hlookup : lookupFun [hoist (guardedEvm calls creates base reserved) body]
      name = some (decl, closure)) :
    DeclCovered (guardedEvm calls creates base reserved)
      (fun executed => executed) (frames body) name decl :=
  (guardedRootFunsCovered calls creates base reserved body).lookup hlookup |>.1

private def externalDeclToEvm {calls : ExternalCalls} {creates : ExternalCreates}
    (decl : FDecl (evmWithExternal calls creates)) : FDecl evm :=
  { params := decl.params, rets := decl.rets, body := decl.body }

private theorem externalHoist_toEvm (calls : ExternalCalls)
    (creates : ExternalCreates) : ∀ body : Block Op,
    (hoist (evmWithExternal calls creates) body).map
      (fun item => (item.1, externalDeclToEvm item.2)) = hoist evm body
  | [] => rfl
  | statement :: rest => by
      cases statement <;>
        simp only [hoist, List.filterMap_cons, List.map_cons,
          externalDeclToEvm]
      case funDef =>
        congr 1
        change (hoist (evmWithExternal calls creates) rest).map
          (fun item => (item.1, externalDeclToEvm item.2)) = hoist evm rest
        exact externalHoist_toEvm calls creates rest
      all_goals
        change (hoist (evmWithExternal calls creates) rest).map
          (fun item => (item.1, externalDeclToEvm item.2)) = hoist evm rest
        exact externalHoist_toEvm calls creates rest

theorem externalScopeCovered (calls : ExternalCalls) (creates : ExternalCreates)
    (body : Block Op) :
    ScopeCovered (evmWithExternal calls creates) (fun executed => executed)
      (frames body) (hoist (evmWithExternal calls creates) body) := by
  intro name decl hmem
  let ordinary := externalDeclToEvm decl
  have hmapped : (name, ordinary) ∈
      (hoist (evmWithExternal calls creates) body).map
        (fun item => (item.1, externalDeclToEvm item.2)) :=
    List.mem_map.mpr ⟨(name, decl), hmem, rfl⟩
  have hordinary : (name, ordinary) ∈ hoist evm body := by
    rw [externalHoist_toEvm calls creates body] at hmapped
    exact hmapped
  obtain ⟨frame, hframe, howner, hparams, hreturns, hbody⟩ :=
    scopeCovered_hoist_frames body name ordinary hordinary
  exact ⟨frame, hframe, howner, hparams, hreturns, hbody⟩

theorem externalRootFunsCovered (calls : ExternalCalls)
    (creates : ExternalCreates) (body : Block Op) :
    FunsCovered (evmWithExternal calls creates) (fun executed => executed)
      (frames body) [hoist (evmWithExternal calls creates) body] :=
  FunsCovered.cons (externalScopeCovered calls creates body)
    (FunsCovered.nil (evmWithExternal calls creates)
      (fun executed => executed) (frames body))

/-- Target-dialect coverage indexed by the original policy frames.  This is
the constructor consumed by the rewrite simulation in both direct and
object-layout-resolved modes. -/
theorem externalExecutedScopeCovered (calls : ExternalCalls)
    (creates : ExternalCreates) (mode : OriginMode) (body : Block Op) :
    ScopeCovered (evmWithExternal calls creates) (fun executed => executed)
      ((frames body).map mode.execFrame)
      (hoist (evmWithExternal calls creates) (mode.execBlock body)) := by
  rw [← frames_execBlock]
  exact externalScopeCovered calls creates (mode.execBlock body)

theorem externalExecutedRootFunsCovered (calls : ExternalCalls)
    (creates : ExternalCreates) (mode : OriginMode) (body : Block Op) :
    FunsCovered (evmWithExternal calls creates) (fun executed => executed)
      ((frames body).map mode.execFrame)
      [hoist (evmWithExternal calls creates) (mode.execBlock body)] :=
  FunsCovered.cons (externalExecutedScopeCovered calls creates mode body)
    (FunsCovered.nil (evmWithExternal calls creates)
      (fun executed => executed) ((frames body).map mode.execFrame))

theorem externalExecutedLookup_root_frame (calls : ExternalCalls)
    (creates : ExternalCreates) (mode : OriginMode) {body : Block Op}
    {name : Ident} {decl : FDecl (evmWithExternal calls creates)}
    {closure : FunEnv (evmWithExternal calls creates)}
    (hlookup : lookupFun
      [hoist (evmWithExternal calls creates) (mode.execBlock body)] name =
        some (decl, closure)) :
    DeclCovered (evmWithExternal calls creates) (fun executed => executed)
      ((frames body).map mode.execFrame) name decl :=
  (externalExecutedRootFunsCovered calls creates mode body).lookup hlookup |>.1

/-- The exact frame list seen after object-layout resolution, stated as a map
of the policy frame list so callers can retain the original allocation
certificate. -/
theorem executedScopeCovered (mode : OriginMode) (body : Block Op) :
    ScopeCovered evm (fun executed => executed)
      ((frames body).map mode.execFrame)
      (hoist evm (mode.execBlock body)) := by
  rw [← frames_execBlock]
  exact scopeCovered_hoist_frames (mode.execBlock body)

theorem executedRootFunsCovered (mode : OriginMode) (body : Block Op) :
    FunsCovered evm (fun executed => executed)
      ((frames body).map mode.execFrame)
      [hoist evm (mode.execBlock body)] :=
  FunsCovered.cons (executedScopeCovered mode body)
    (FunsCovered.nil evm (fun executed => executed)
      ((frames body).map mode.execFrame))

theorem executedLookup_root_frame (mode : OriginMode) {body : Block Op}
    {name : Ident} {decl : FDecl evm} {closure : FunEnv evm}
    (hlookup : lookupFun [hoist evm (mode.execBlock body)] name =
      some (decl, closure)) :
    DeclCovered evm (fun executed => executed)
      ((frames body).map mode.execFrame) name decl :=
  (executedRootFunsCovered mode body).lookup hlookup |>.1

/-! ## Exact call-edge coverage -/

/-- The direct calls of `frame` agree with the exact allocator call-edge list
in `info`; unresolved external/pseudo-operation names are intentionally outside
the premise `name ∈ defined`. -/
structure CallsCovered (defined : List Ident) (frame : Frame)
    (info : FrameInfo) : Prop where
  owner_eq : info.owner = frame.owner
  direct : ∀ name, name ∈ frameCallsStmts frame.body → name ∈ defined →
    some name ∈ info.callees

theorem frameInfo_callsCovered (selected : SpillSet) (defined : List Ident)
    (frame : Frame) :
    CallsCovered defined frame (frameInfo selected defined frame) := by
  constructor
  · rfl
  · intro name hcall hdefined
    unfold frameInfo
    simp only [List.mem_map, Option.some.injEq]
    refine ⟨name, ?_, rfl⟩
    exact List.mem_eraseDups.mpr (List.mem_filter.mpr ⟨hcall, by simpa using hdefined⟩)

theorem frameInfo_execFrame_callsCovered (selected : SpillSet)
    (defined : List Ident) (mode : OriginMode) (frame : Frame) :
    CallsCovered defined (mode.execFrame frame) (frameInfo selected defined frame) := by
  constructor
  · exact (frameInfo_callsCovered selected defined frame).owner_eq.trans
      (OriginMode.execFrame_owner mode frame).symm
  · intro name hcall hdefined
    apply (frameInfo_callsCovered selected defined frame).direct name _ hdefined
    simpa using hcall

/-- A call in a certified policy frame resolves to a cached allocator callee
whenever the called name denotes one of the collected function frames. -/
theorem call_mem_callees_of_frame_mem {body : Block Op} {selected : SpillSet}
    {frame : Frame} (_hframe : frame ∈ frames body) {name : Ident}
    (hcall : name ∈ frameCallsStmts frame.body)
    (hdefined : name ∈ (frames body).filterMap (·.owner)) :
    some name ∈
      (frameInfo selected ((frames body).filterMap (·.owner)) frame).callees := by
  exact (frameInfo_callsCovered selected
    ((frames body).filterMap (·.owner)) frame).direct name hcall hdefined

/-- Layout-level form of call coverage: both the caller info and its exact
callee owner are present in a successfully built allocator layout. -/
theorem buildLayout_call_covered {base : Nat} {body : Block Op}
    {selected : SpillSet} {layout : MemorySpillSelect.Layout}
    (hbuild : buildLayout base selected body = some layout)
    {frame : Frame} (hframe : frame ∈ frames body) {name : Ident}
    (hcall : name ∈ frameCallsStmts frame.body)
    (hdefined : name ∈ (frames body).filterMap (·.owner)) :
    ∃ info ∈ layout.infos,
      info = frameInfo selected ((frames body).filterMap (·.owner)) frame ∧
        some name ∈ info.callees := by
  let info := frameInfo selected ((frames body).filterMap (·.owner)) frame
  refine ⟨info, buildLayout_frameInfo_mem hbuild hframe, rfl, ?_⟩
  exact call_mem_callees_of_frame_mem hframe hcall hdefined

end YulEvmCompiler.Optimizer.MemorySpillOriginSound
