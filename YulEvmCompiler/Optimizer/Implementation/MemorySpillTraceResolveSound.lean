import YulEvmCompiler.Optimizer.Implementation.MemorySpillRewriteSound
set_option warningAsError true
/-!
# Layout-resolution invariance for spill traces

Object-layout resolution changes only expressions.  The spill allocator's
declared-name, tuple-coupling, and lexical-live certificates are therefore
identical before and after resolution.  This module packages that structural
fact for the dual policy/executed-frame simulation used by object spilling.
-/

namespace YulEvmCompiler.Optimizer.MemorySpillTraceResolveSound

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open MemorySpill
open MemorySpillSelect
open MemorySpillOriginSound
open MemorySpillRewriteSound

/-! ## Declared names -/

mutual
  theorem declaredStmt_resolveForLayout (layout : EVM.Layout) :
      ∀ statement : Stmt Op,
        declaredStmt (resolveForLayoutStmt layout statement) =
          declaredStmt statement := by
    intro statement
    cases statement with
    | block body =>
        simp only [resolveForLayoutStmt_block, declaredStmt]
        exact declaredStmts_resolveForLayout layout body
    | funDef name params returns body =>
        simp only [resolveForLayoutStmt_funDef, declaredStmt]
        rw [declaredStmts_resolveForLayout]
    | letDecl names value =>
        simp [resolveForLayoutStmt_letDecl, declaredStmt]
    | assign names value =>
        simp [resolveForLayoutStmt_assign, declaredStmt]
    | cond condition body =>
        simp only [resolveForLayoutStmt_cond, declaredStmt]
        rw [declaredStmts_resolveForLayout]
    | «switch» condition cases fallback =>
        cases fallback with
        | none =>
            simp only [resolveForLayoutStmt_switch, Option.map_none, declaredStmt]
            rw [declaredCases_resolveForLayout]
        | some fallback =>
            simp only [resolveForLayoutStmt_switch, Option.map_some, declaredStmt]
            rw [declaredCases_resolveForLayout,
              declaredStmts_resolveForLayout layout fallback]
    | forLoop init condition post body =>
        simp only [resolveForLayoutStmt_forLoop, declaredStmt]
        rw [declaredStmts_resolveForLayout layout init,
          declaredStmts_resolveForLayout layout post,
          declaredStmts_resolveForLayout layout body]
    | exprStmt expression => simp [resolveForLayoutStmt_exprStmt, declaredStmt]
    | «break» => simp [resolveForLayoutStmt_break, declaredStmt]
    | «continue» => simp [resolveForLayoutStmt_continue, declaredStmt]
    | «leave» => simp [resolveForLayoutStmt_leave, declaredStmt]
  termination_by statement => 2 * sizeOf statement

  theorem declaredStmts_resolveForLayout (layout : EVM.Layout) :
      ∀ body : Block Op,
        declaredStmts (resolveForLayoutStmts layout body) = declaredStmts body
    | [] => by simp [declaredStmts]
    | statement :: rest => by
        simp only [resolveForLayoutStmts, declaredStmts]
        rw [declaredStmt_resolveForLayout,
          declaredStmts_resolveForLayout]
  termination_by body => 2 * sizeOf body + 1

  theorem declaredCases_resolveForLayout (layout : EVM.Layout) :
      ∀ cases : List (Literal × Block Op),
        declaredCases (resolveForLayoutCases layout cases) = declaredCases cases
    | [] => by simp [resolveForLayoutCases, declaredCases]
    | (literal, body) :: rest => by
        simp only [resolveForLayoutCases, declaredCases]
        rw [declaredStmts_resolveForLayout,
          declaredCases_resolveForLayout]
  termination_by cases => 2 * sizeOf cases + 1
  decreasing_by all_goals simp_all <;> omega
end

/-! ## Coupled tuple groups -/

mutual
  theorem coupledStmt_resolveForLayout (layout : EVM.Layout) (owner : Owner) :
      ∀ statement : Stmt Op,
        coupledStmt owner (resolveForLayoutStmt layout statement) =
          coupledStmt owner statement := by
    intro statement
    cases statement with
    | block body =>
        simp only [resolveForLayoutStmt_block, coupledStmt]
        exact coupledStmts_resolveForLayout layout owner body
    | funDef name params returns body =>
        simp only [resolveForLayoutStmt_funDef, coupledStmt]
        exact coupledStmts_resolveForLayout layout (some name) body
    | letDecl names value =>
        simp [resolveForLayoutStmt_letDecl, coupledStmt]
    | assign names value =>
        simp [resolveForLayoutStmt_assign, coupledStmt]
    | cond condition body =>
        simp only [resolveForLayoutStmt_cond, coupledStmt]
        exact coupledStmts_resolveForLayout layout owner body
    | «switch» condition cases fallback =>
        cases fallback with
        | none =>
            simp only [resolveForLayoutStmt_switch, Option.map_none, coupledStmt]
            rw [coupledCases_resolveForLayout]
        | some fallback =>
            simp only [resolveForLayoutStmt_switch, Option.map_some, coupledStmt]
            rw [coupledCases_resolveForLayout,
              coupledStmts_resolveForLayout layout owner fallback]
    | forLoop init condition post body =>
        simp only [resolveForLayoutStmt_forLoop, coupledStmt]
        rw [coupledStmts_resolveForLayout layout owner init,
          coupledStmts_resolveForLayout layout owner post,
          coupledStmts_resolveForLayout layout owner body]
    | exprStmt expression => simp [resolveForLayoutStmt_exprStmt, coupledStmt]
    | «break» => simp [resolveForLayoutStmt_break, coupledStmt]
    | «continue» => simp [resolveForLayoutStmt_continue, coupledStmt]
    | «leave» => simp [resolveForLayoutStmt_leave, coupledStmt]
  termination_by statement => 2 * sizeOf statement

  theorem coupledStmts_resolveForLayout (layout : EVM.Layout) (owner : Owner) :
      ∀ body : Block Op,
        coupledStmts owner (resolveForLayoutStmts layout body) =
          coupledStmts owner body
    | [] => by simp [coupledStmts]
    | statement :: rest => by
        simp only [resolveForLayoutStmts, coupledStmts]
        rw [coupledStmt_resolveForLayout,
          coupledStmts_resolveForLayout]
  termination_by body => 2 * sizeOf body + 1

  theorem coupledCases_resolveForLayout (layout : EVM.Layout) (owner : Owner) :
      ∀ cases : List (Literal × Block Op),
        coupledCases owner (resolveForLayoutCases layout cases) =
          coupledCases owner cases
    | [] => by simp [resolveForLayoutCases, coupledCases]
    | (literal, body) :: rest => by
        simp only [resolveForLayoutCases, coupledCases]
        rw [coupledStmts_resolveForLayout,
          coupledCases_resolveForLayout]
  termination_by cases => 2 * sizeOf cases + 1
  decreasing_by all_goals simp_all <;> omega
end

/-! ## Lexical-live traces -/

mutual
  theorem liveStmt_resolveForLayout (layout : EVM.Layout)
      (selected : SpillSet) (owner : Owner) (live : SpillSet) :
      ∀ statement : Stmt Op,
        liveStmt selected owner live (resolveForLayoutStmt layout statement) =
          liveStmt selected owner live statement := by
    intro statement
    cases statement with
    | block body =>
        simp only [resolveForLayoutStmt_block, liveStmt, liveScope]
        rw [liveStmts_resolveForLayout]
    | funDef name params returns body =>
        simp [resolveForLayoutStmt_funDef, liveStmt]
    | letDecl names value =>
        simp [resolveForLayoutStmt_letDecl, liveStmt]
    | assign names value =>
        simp [resolveForLayoutStmt_assign, liveStmt]
    | cond condition body =>
        simp only [resolveForLayoutStmt_cond, liveStmt, liveScope]
        rw [liveStmts_resolveForLayout]
    | «switch» condition cases fallback =>
        cases fallback with
        | none =>
            simp only [resolveForLayoutStmt_switch, Option.map_none, liveStmt]
            rw [liveCases_resolveForLayout]
        | some fallback =>
            simp only [resolveForLayoutStmt_switch, Option.map_some, liveStmt,
              liveScope]
            rw [liveCases_resolveForLayout,
              liveStmts_resolveForLayout layout selected owner live fallback]
    | forLoop init condition post body =>
        simp only [resolveForLayoutStmt_forLoop, liveStmt, liveScope]
        rw [liveStmts_resolveForLayout layout selected owner live init]
        rw [liveStmts_resolveForLayout layout selected owner
          (liveStmts selected owner live init).2 body]
        rw [liveStmts_resolveForLayout layout selected owner
          (liveStmts selected owner live init).2 post]
    | exprStmt expression => simp [resolveForLayoutStmt_exprStmt, liveStmt]
    | «break» => simp [resolveForLayoutStmt_break, liveStmt]
    | «continue» => simp [resolveForLayoutStmt_continue, liveStmt]
    | «leave» => simp [resolveForLayoutStmt_leave, liveStmt]
  termination_by statement => 2 * sizeOf statement

  theorem liveStmts_resolveForLayout (layout : EVM.Layout)
      (selected : SpillSet) (owner : Owner) (live : SpillSet) :
      ∀ body : Block Op,
        liveStmts selected owner live (resolveForLayoutStmts layout body) =
          liveStmts selected owner live body
    | [] => by simp [liveStmts]
    | statement :: rest => by
        simp only [resolveForLayoutStmts, liveStmts]
        rw [liveStmt_resolveForLayout]
        rw [liveStmts_resolveForLayout]
  termination_by body => 2 * sizeOf body + 1

  theorem liveCases_resolveForLayout (layout : EVM.Layout)
      (selected : SpillSet) (owner : Owner) (live : SpillSet) :
      ∀ cases : List (Literal × Block Op),
        liveCases selected owner live (resolveForLayoutCases layout cases) =
          liveCases selected owner live cases
    | [] => by simp [resolveForLayoutCases, liveCases]
    | (literal, body) :: rest => by
        simp only [resolveForLayoutCases, liveCases, liveScope]
        rw [liveStmts_resolveForLayout,
          liveCases_resolveForLayout]
  termination_by cases => 2 * sizeOf cases + 1
  decreasing_by all_goals simp_all <;> omega
end

theorem liveScope_resolveForLayout (layout : EVM.Layout)
    (selected : SpillSet) (owner : Owner) (live : SpillSet) (body : Block Op) :
    liveScope selected owner live (resolveForLayoutStmts layout body) =
      liveScope selected owner live body := by
  simp [liveScope, liveStmts_resolveForLayout]

theorem frameNames_resolveForLayout (layout : EVM.Layout) (frame : Frame) :
    frameNames ((OriginMode.object layout).execFrame frame) = frameNames frame :=
  OriginMode.execFrame_names (.object layout) frame

@[simp] theorem frameInitialLive_execFrame (mode : OriginMode)
    (selected : SpillSet) (frame : Frame) :
    frameInitialLive selected (mode.execFrame frame) =
      frameInitialLive selected frame := by
  cases mode <;> rfl

@[simp] theorem frameLives_execFrame (mode : OriginMode)
    (selected : SpillSet) (frame : Frame) :
    frameLives selected (mode.execFrame frame) = frameLives selected frame := by
  cases mode with
  | identity => rfl
  | «object» layout =>
      simp only [OriginMode.execFrame, frameLives]
      rw [liveStmts_resolveForLayout]

/-! ## Origin-mode transport -/

theorem declaredStmts_execBlock (mode : OriginMode) (body : Block Op) :
    declaredStmts (mode.execBlock body) = declaredStmts body := by
  cases mode with
  | identity => rfl
  | «object» layout => exact declaredStmts_resolveForLayout layout body

theorem coupledStmts_execBlock (mode : OriginMode) (owner : Owner)
    (body : Block Op) :
    coupledStmts owner (mode.execBlock body) = coupledStmts owner body := by
  cases mode with
  | identity => rfl
  | «object» layout => exact coupledStmts_resolveForLayout layout owner body

theorem liveStmts_execBlock (mode : OriginMode) (selected : SpillSet)
    (owner : Owner) (live : SpillSet) (body : Block Op) :
    liveStmts selected owner live (mode.execBlock body) =
      liveStmts selected owner live body := by
  cases mode with
  | identity => rfl
  | «object» layout =>
      exact liveStmts_resolveForLayout layout selected owner live body

theorem declaredStmts_execFrame (mode : OriginMode) (frame : Frame) :
    declaredStmts (mode.execFrame frame).body = declaredStmts frame.body := by
  cases mode with
  | identity => rfl
  | «object» layout => exact declaredStmts_resolveForLayout layout frame.body

theorem coupledStmts_execFrame (mode : OriginMode) (owner : Owner)
    (frame : Frame) :
    coupledStmts owner (mode.execFrame frame).body =
      coupledStmts owner frame.body := by
  cases mode with
  | identity => rfl
  | «object» layout => exact coupledStmts_resolveForLayout layout owner frame.body

theorem liveCertified_execFrame_iff (mode : OriginMode) (selected : SpillSet)
    (frame : Frame) (live : SpillSet) :
    LiveCertified selected (mode.execFrame frame) live ↔
      LiveCertified selected frame live := by
  constructor
  · rintro ⟨maxLive, hmax, hsubset⟩
    exact ⟨maxLive, by simpa using hmax, hsubset⟩
  · rintro ⟨maxLive, hmax, hsubset⟩
    exact ⟨maxLive, by simpa using hmax, hsubset⟩

theorem traceCovered_exec_iff (mode : OriginMode) (selected : SpillSet)
    (frame : Frame) (live : SpillSet) (body : Block Op) :
    TraceCovered selected (mode.execFrame frame) live (mode.execBlock body) ↔
      TraceCovered selected frame live body := by
  simp only [TraceCovered, OriginMode.execFrame_owner,
    frameLives_execFrame, liveStmts_execBlock]

theorem traceCovered_execBlock_iff (mode : OriginMode) (selected : SpillSet)
    (frame : Frame) (live : SpillSet) (body : Block Op) :
    TraceCovered selected frame live (mode.execBlock body) ↔
      TraceCovered selected frame live body := by
  simp only [TraceCovered, liveStmts_execBlock]

/-! ## Membership transport for local binding cases -/

theorem declared_mem_resolveForLayout_iff (layout : EVM.Layout)
    (name : Ident) (body : Block Op) :
    name ∈ declaredStmts (resolveForLayoutStmts layout body) ↔
      name ∈ declaredStmts body := by
  rw [declaredStmts_resolveForLayout]

theorem declaredStmt_mem_resolveForLayout_iff (layout : EVM.Layout)
    (name : Ident) (statement : Stmt Op) :
    name ∈ declaredStmt (resolveForLayoutStmt layout statement) ↔
      name ∈ declaredStmt statement := by
  rw [declaredStmt_resolveForLayout]

theorem coupled_mem_resolveForLayout_iff (layout : EVM.Layout)
    (owner : Owner) (group : List SpillKey) (body : Block Op) :
    group ∈ coupledStmts owner (resolveForLayoutStmts layout body) ↔
      group ∈ coupledStmts owner body := by
  rw [coupledStmts_resolveForLayout]

theorem coupledStmt_mem_resolveForLayout_iff (layout : EVM.Layout)
    (owner : Owner) (group : List SpillKey) (statement : Stmt Op) :
    group ∈ coupledStmt owner (resolveForLayoutStmt layout statement) ↔
      group ∈ coupledStmt owner statement := by
  rw [coupledStmt_resolveForLayout]

theorem declared_mem_execBlock_iff (mode : OriginMode)
    (name : Ident) (body : Block Op) :
    name ∈ declaredStmts (mode.execBlock body) ↔
      name ∈ declaredStmts body := by
  rw [declaredStmts_execBlock]

theorem coupled_mem_execBlock_iff (mode : OriginMode) (owner : Owner)
    (group : List SpillKey) (body : Block Op) :
    group ∈ coupledStmts owner (mode.execBlock body) ↔
      group ∈ coupledStmts owner body := by
  rw [coupledStmts_execBlock]

theorem declared_mem_execFrame_iff (mode : OriginMode)
    (name : Ident) (frame : Frame) :
    name ∈ declaredStmts (mode.execFrame frame).body ↔
      name ∈ declaredStmts frame.body := by
  rw [declaredStmts_execFrame]

theorem coupled_mem_execFrame_iff (mode : OriginMode) (owner : Owner)
    (group : List SpillKey) (frame : Frame) :
    group ∈ coupledStmts owner (mode.execFrame frame).body ↔
      group ∈ coupledStmts owner frame.body := by
  rw [coupledStmts_execFrame]

end YulEvmCompiler.Optimizer.MemorySpillTraceResolveSound
