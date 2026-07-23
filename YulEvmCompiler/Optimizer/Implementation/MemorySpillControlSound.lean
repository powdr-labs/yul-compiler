import YulEvmCompiler.Optimizer.Implementation.MemorySpillCallSound
import YulEvmCompiler.Optimizer.Implementation.MemorySpillBindingSound
import YulEvmCompiler.Optimizer.Implementation.MemorySpillTraceResolveSound
import YulEvmCompiler.Optimizer.Implementation.MemorySpillExitSound
set_option warningAsError true
/-!
# Control-flow interfaces for memory spilling

The statement induction needs two invariants not expressible by
`LiveFrameRel` alone:

* the currently executed syntax is a descendant of the owning frame, so a
  dynamic user call is an allocator call edge; and
* callee writes below the caller's frame cutoff preserve the caller's loaded
  spill cells.

This module makes both invariants explicit and proves their reusable closure
lemmas.  They are the control-flow shell consumed by the full syntax
induction.
-/

namespace YulEvmCompiler.Optimizer.MemorySpillControlSound

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer
open MemorySpillSelect
open MemorySpillStateSound
open MemorySpillRewriteSound
open MemorySpillFrameSound
open MemorySpillOriginSound
open MemorySpillCallSound
open MemorySpillBindingSound
open MemorySpillTraceResolveSound
open MemorySpillExitSound

variable {base reserved : Nat}
variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "G" => guardedEvm calls creates base reserved
local notation "D" => evmWithExternal calls creates

/-- Executed code corresponding to policy code in direct and object modes. -/
def execCode : OriginMode → Code Op → Code Op
  | .identity, code => code
  | .object layout, code => resolveForLayoutCode layout code

/-! ## Binding/declaration descendant origin

Tuple closure and generated-name freshness are global policy facts.  The
simulation must therefore remember that the current syntax is a structural
descendant of the policy root, rather than asking each binding case for an
unrelated membership hypothesis. -/

def codeGroups (owner : Owner) : Code Op → List (List SpillKey)
  | .expr _ | .args _ => []
  | .stmt statement => coupledStmt owner statement
  | .stmts statements => coupledStmts owner statements
  | .loop _ post body => coupledStmts owner post ++ coupledStmts owner body

def codeDeclared : Code Op → List Ident
  | .expr _ | .args _ => []
  | .stmt statement => MemorySpill.declaredStmt statement
  | .stmts statements => MemorySpill.declaredStmts statements
  | .loop _ post body =>
      MemorySpill.declaredStmts post ++ MemorySpill.declaredStmts body

structure BindingOrigin (globalGroups : List (List SpillKey))
    (globalDeclared : List Ident) (owner : Owner) (code : Code Op) : Prop where
  groups : ∀ group, group ∈ codeGroups owner code → group ∈ globalGroups
  declared : ∀ name, name ∈ codeDeclared code → name ∈ globalDeclared

structure FrameBindingOrigin (globalGroups : List (List SpillKey))
    (globalDeclared : List Ident) (frame : Frame) : Prop where
  groups : ∀ group, group ∈ coupledStmts frame.owner frame.body →
    group ∈ globalGroups
  declared : ∀ name,
    name ∈ frame.params ++ frame.returns ++
      MemorySpill.declaredStmts frame.body →
    name ∈ globalDeclared

theorem FrameBindingOrigin.mono {groups smallGroups : List (List SpillKey)}
    {declared smallDeclared : List Ident} {frame : Frame}
    (horigin : FrameBindingOrigin smallGroups smallDeclared frame)
    (hgroups : ∀ group, group ∈ smallGroups → group ∈ groups)
    (hdeclared : ∀ name, name ∈ smallDeclared → name ∈ declared) :
    FrameBindingOrigin groups declared frame := by
  exact {
    groups := fun group hgroup => hgroups group (horigin.groups group hgroup)
    declared := fun name hname => hdeclared name (horigin.declared name hname) }

mutual
  theorem nestedFrameBindingStmt (owner : Owner) : ∀ statement frame,
      frame ∈ nestedFramesStmt statement →
      FrameBindingOrigin (coupledStmt owner statement)
        (MemorySpill.declaredStmt statement) frame := by
    intro statement frame hframe
    cases statement with
    | block body =>
        simpa [nestedFramesStmt, coupledStmt, MemorySpill.declaredStmt] using
          nestedFrameBindingStmts owner body frame (by
            simpa [nestedFramesStmt] using hframe)
    | funDef name params returns body =>
        simp only [nestedFramesStmt, List.mem_cons] at hframe
        rcases hframe with rfl | hnested
        · exact {
            groups := fun _ h => by simpa [coupledStmt] using h
            declared := fun _ h => by
              simpa [MemorySpill.declaredStmt] using h }
        · exact (nestedFrameBindingStmts (some name) body frame hnested).mono
            (fun _ h => by simpa [coupledStmt] using h) (fun declared h => by
              simp only [MemorySpill.declaredStmt, List.mem_append]
              exact Or.inr h)
    | letDecl names value => simp [nestedFramesStmt] at hframe
    | assign names value => simp [nestedFramesStmt] at hframe
    | cond condition body =>
        simpa [nestedFramesStmt, coupledStmt, MemorySpill.declaredStmt] using
          nestedFrameBindingStmts owner body frame (by
            simpa [nestedFramesStmt] using hframe)
    | «switch» condition cases fallback =>
        cases fallback with
        | none =>
            have hcases : frame ∈ nestedFramesCases cases := by
              simpa [nestedFramesStmt] using hframe
            exact (nestedFrameBindingCases owner cases frame hcases).mono
              (fun group h => by simpa [coupledStmt] using h)
              (fun name h => by
                simpa [MemorySpill.declaredStmt] using h)
        | some fallback =>
            have hsplit : frame ∈ nestedFramesCases cases ∨
                frame ∈ nestedFramesStmts fallback := by
              simpa [nestedFramesStmt] using hframe
            rcases hsplit with hcases | hfallback
            · exact (nestedFrameBindingCases owner cases frame hcases).mono
                (fun group h => by
                  simp only [coupledStmt, List.mem_append]
                  exact Or.inl h)
                (fun name h => by
                  simp only [MemorySpill.declaredStmt, List.mem_append]
                  exact Or.inl h)
            · exact (nestedFrameBindingStmts owner fallback frame hfallback).mono
                (fun group h => by
                  simp only [coupledStmt, List.mem_append]
                  exact Or.inr h)
                (fun name h => by
                  simp only [MemorySpill.declaredStmt, List.mem_append]
                  exact Or.inr h)
    | forLoop init condition post body =>
        simp only [nestedFramesStmt, List.mem_append] at hframe
        rcases hframe with hinitPost | hbody
        · rcases hinitPost with hinit | hpost
          · exact (nestedFrameBindingStmts owner init frame hinit).mono
              (fun group h => by
                simp only [coupledStmt, List.mem_append]
                exact Or.inl (Or.inl h))
              (fun name h => by
                simp only [MemorySpill.declaredStmt, List.mem_append]
                exact Or.inl (Or.inl h))
          · exact (nestedFrameBindingStmts owner post frame hpost).mono
              (fun group h => by
                simp only [coupledStmt, List.mem_append]
                exact Or.inl (Or.inr h))
              (fun name h => by
                simp only [MemorySpill.declaredStmt, List.mem_append]
                exact Or.inl (Or.inr h))
        · exact (nestedFrameBindingStmts owner body frame hbody).mono
            (fun group h => by
              simp only [coupledStmt, List.mem_append]
              exact Or.inr h)
            (fun name h => by
              simp only [MemorySpill.declaredStmt, List.mem_append]
              exact Or.inr h)
    | exprStmt expression => simp [nestedFramesStmt] at hframe
    | «break» => simp [nestedFramesStmt] at hframe
    | «continue» => simp [nestedFramesStmt] at hframe
    | «leave» => simp [nestedFramesStmt] at hframe
  termination_by statement => 2 * sizeOf statement

  theorem nestedFrameBindingStmts (owner : Owner) : ∀ body frame,
      frame ∈ nestedFramesStmts body →
      FrameBindingOrigin (coupledStmts owner body)
        (MemorySpill.declaredStmts body) frame
    | [], frame, hframe => by simp [nestedFramesStmts] at hframe
    | statement :: rest, frame, hframe => by
        simp only [nestedFramesStmts, List.mem_append] at hframe
        rcases hframe with hhead | htail
        · exact (nestedFrameBindingStmt owner statement frame hhead).mono
            (fun group h => by
              simp only [coupledStmts, List.mem_append]
              exact Or.inl h)
            (fun name h => by
              simp only [MemorySpill.declaredStmts, List.mem_append]
              exact Or.inl h)
        · exact (nestedFrameBindingStmts owner rest frame htail).mono
            (fun group h => by
              simp only [coupledStmts, List.mem_append]
              exact Or.inr h)
            (fun name h => by
              simp only [MemorySpill.declaredStmts, List.mem_append]
              exact Or.inr h)
  termination_by body => 2 * sizeOf body + 1

  theorem nestedFrameBindingCases (owner : Owner) : ∀ cases frame,
      frame ∈ nestedFramesCases cases →
      FrameBindingOrigin (coupledCases owner cases)
        (MemorySpill.declaredCases cases) frame
    | [], frame, hframe => by simp [nestedFramesCases] at hframe
    | (literal, body) :: rest, frame, hframe => by
        simp only [nestedFramesCases, List.mem_append] at hframe
        rcases hframe with hbody | hrest
        · exact (nestedFrameBindingStmts owner body frame hbody).mono
            (fun group h => by
              simp only [coupledCases, List.mem_append]
              exact Or.inl h)
            (fun name h => by
              simp only [MemorySpill.declaredCases, List.mem_append]
              exact Or.inl h)
        · exact (nestedFrameBindingCases owner rest frame hrest).mono
            (fun group h => by
              simp only [coupledCases, List.mem_append]
              exact Or.inr h)
            (fun name h => by
              simp only [MemorySpill.declaredCases, List.mem_append]
              exact Or.inr h)
  termination_by cases => 2 * sizeOf cases + 1
  decreasing_by all_goals simp_wf <;> omega
end

theorem frameBindingOrigin_of_mem {body : Block Op} {frame : Frame}
    (hframe : frame ∈ frames body) :
    FrameBindingOrigin (coupledStmts none body)
      (MemorySpill.declaredStmts body) frame := by
  simp only [frames, List.mem_cons] at hframe
  rcases hframe with rfl | hnested
  · exact {
      groups := fun _ h => h
      declared := fun name h => by simpa using h }
  · exact nestedFrameBindingStmts none body frame hnested

/-! `frames` is transitively closed: the nested frames of a frame already
collected from the policy tree are themselves in the same global list. -/
mutual
  theorem nestedFramesStmt_descendants : ∀ statement frame,
      frame ∈ nestedFramesStmt statement →
      ∀ child, child ∈ nestedFramesStmts frame.body →
        child ∈ nestedFramesStmt statement := by
    intro statement frame hframe child hchild
    cases statement with
    | block body =>
        simpa [nestedFramesStmt] using
          nestedFramesStmts_descendants body frame
            (by simpa [nestedFramesStmt] using hframe) child hchild
    | funDef name params returns body =>
        simp only [nestedFramesStmt, List.mem_cons] at hframe ⊢
        rcases hframe with rfl | hnested
        · exact Or.inr hchild
        · exact Or.inr
            (nestedFramesStmts_descendants body frame hnested child hchild)
    | letDecl names value => simp [nestedFramesStmt] at hframe
    | assign names value => simp [nestedFramesStmt] at hframe
    | cond condition body =>
        simpa [nestedFramesStmt] using
          nestedFramesStmts_descendants body frame
            (by simpa [nestedFramesStmt] using hframe) child hchild
    | «switch» condition cases fallback =>
        cases fallback with
        | none =>
            have hcases : frame ∈ nestedFramesCases cases := by
              simpa [nestedFramesStmt] using hframe
            simpa [nestedFramesStmt] using
              nestedFramesCases_descendants cases frame hcases child hchild
        | some fallback =>
            have hsplit : frame ∈ nestedFramesCases cases ∨
                frame ∈ nestedFramesStmts fallback := by
              simpa [nestedFramesStmt] using hframe
            rcases hsplit with hcases | hfallback
            · simp only [nestedFramesStmt, List.mem_append]
              exact Or.inl
                (nestedFramesCases_descendants cases frame hcases child hchild)
            · simp only [nestedFramesStmt, List.mem_append]
              exact Or.inr
                (nestedFramesStmts_descendants fallback frame hfallback child hchild)
    | forLoop init condition post body =>
        simp only [nestedFramesStmt, List.mem_append] at hframe ⊢
        rcases hframe with hinitPost | hbody
        · rcases hinitPost with hinit | hpost
          · exact Or.inl (Or.inl
              (nestedFramesStmts_descendants init frame hinit child hchild))
          · exact Or.inl (Or.inr
              (nestedFramesStmts_descendants post frame hpost child hchild))
        · exact Or.inr
            (nestedFramesStmts_descendants body frame hbody child hchild)
    | exprStmt expression => simp [nestedFramesStmt] at hframe
    | «break» => simp [nestedFramesStmt] at hframe
    | «continue» => simp [nestedFramesStmt] at hframe
    | «leave» => simp [nestedFramesStmt] at hframe
  termination_by statement => 2 * sizeOf statement

  theorem nestedFramesStmts_descendants : ∀ body frame,
      frame ∈ nestedFramesStmts body →
      ∀ child, child ∈ nestedFramesStmts frame.body →
        child ∈ nestedFramesStmts body
    | [], frame, hframe => by simp [nestedFramesStmts] at hframe
    | statement :: rest, frame, hframe => by
        intro child hchild
        simp only [nestedFramesStmts, List.mem_append] at hframe ⊢
        rcases hframe with hhead | htail
        · exact Or.inl
            (nestedFramesStmt_descendants statement frame hhead child hchild)
        · exact Or.inr
            (nestedFramesStmts_descendants rest frame htail child hchild)
  termination_by body => 2 * sizeOf body + 1

  theorem nestedFramesCases_descendants : ∀ cases frame,
      frame ∈ nestedFramesCases cases →
      ∀ child, child ∈ nestedFramesStmts frame.body →
        child ∈ nestedFramesCases cases
    | [], frame, hframe => by simp [nestedFramesCases] at hframe
    | (literal, body) :: rest, frame, hframe => by
        intro child hchild
        simp only [nestedFramesCases, List.mem_append] at hframe ⊢
        rcases hframe with hbody | hrest
        · exact Or.inl
            (nestedFramesStmts_descendants body frame hbody child hchild)
        · exact Or.inr
            (nestedFramesCases_descendants rest frame hrest child hchild)
  termination_by cases => 2 * sizeOf cases + 1
  decreasing_by all_goals simp_wf <;> omega
end

theorem FrameBindingOrigin.body {globalGroups : List (List SpillKey)}
    {globalDeclared : List Ident} {frame : Frame}
    (horigin : FrameBindingOrigin globalGroups globalDeclared frame) :
    BindingOrigin globalGroups globalDeclared frame.owner (.stmts frame.body) := by
  exact {
    groups := horigin.groups
    declared := fun name hname => horigin.declared name (by
      simp only [List.mem_append]
      exact Or.inr hname) }

theorem BindingOrigin.expr (globalGroups : List (List SpillKey))
    (globalDeclared : List Ident) (owner : Owner) (expression : Expr Op) :
    BindingOrigin globalGroups globalDeclared owner (.expr expression) := by
  constructor <;> simp [codeGroups, codeDeclared]

theorem BindingOrigin.args (globalGroups : List (List SpillKey))
    (globalDeclared : List Ident) (owner : Owner) (args : List (Expr Op)) :
    BindingOrigin globalGroups globalDeclared owner (.args args) := by
  constructor <;> simp [codeGroups, codeDeclared]

theorem BindingOrigin.root (body : Block Op) :
    BindingOrigin (coupledStmts none body) (MemorySpill.declaredStmts body)
      none (.stmts body) := by
  exact ⟨fun _ h => h, fun _ h => h⟩

theorem BindingOrigin.stmtsHead {globalGroups : List (List SpillKey)}
    {globalDeclared : List Ident} {owner : Owner} {statement : Stmt Op}
    {rest : Block Op}
    (horigin : BindingOrigin globalGroups globalDeclared owner
      (.stmts (statement :: rest))) :
    BindingOrigin globalGroups globalDeclared owner (.stmt statement) := by
  constructor
  · intro group hgroup
    apply horigin.groups group
    simp only [codeGroups, coupledStmts, List.mem_append]
    exact Or.inl hgroup
  · intro name hname
    apply horigin.declared name
    simp only [codeDeclared, MemorySpill.declaredStmts, List.mem_append]
    exact Or.inl hname

theorem BindingOrigin.stmtsTail {globalGroups : List (List SpillKey)}
    {globalDeclared : List Ident} {owner : Owner} {statement : Stmt Op}
    {rest : Block Op}
    (horigin : BindingOrigin globalGroups globalDeclared owner
      (.stmts (statement :: rest))) :
    BindingOrigin globalGroups globalDeclared owner (.stmts rest) := by
  constructor
  · intro group hgroup
    apply horigin.groups group
    simp only [codeGroups, coupledStmts, List.mem_append]
    exact Or.inr hgroup
  · intro name hname
    apply horigin.declared name
    simp only [codeDeclared, MemorySpill.declaredStmts, List.mem_append]
    exact Or.inr hname

theorem BindingOrigin.block {globalGroups : List (List SpillKey)}
    {globalDeclared : List Ident} {owner : Owner} {body : Block Op}
    (horigin : BindingOrigin globalGroups globalDeclared owner
      (.stmt (.block body))) :
    BindingOrigin globalGroups globalDeclared owner (.stmts body) := by
  constructor
  · intro group hgroup
    apply horigin.groups group
    simpa [codeGroups, coupledStmt] using hgroup
  · intro name hname
    apply horigin.declared name
    simpa [codeDeclared, MemorySpill.declaredStmt] using hname

theorem BindingOrigin.condBody {globalGroups : List (List SpillKey)}
    {globalDeclared : List Ident} {owner : Owner} {condition : Expr Op}
    {body : Block Op}
    (horigin : BindingOrigin globalGroups globalDeclared owner
      (.stmt (.cond condition body))) :
    BindingOrigin globalGroups globalDeclared owner (.stmts body) := by
  constructor
  · intro group hgroup
    apply horigin.groups group
    simpa [codeGroups, coupledStmt] using hgroup
  · intro name hname
    apply horigin.declared name
    simpa [codeDeclared, MemorySpill.declaredStmt] using hname

theorem coupledStmts_mem_coupledCases_of_mem {owner : Owner}
    {literal : Literal} {body : Block Op}
    {cases : List (Literal × Block Op)}
    (hcase : (literal, body) ∈ cases) :
    ∀ group, group ∈ coupledStmts owner body →
      group ∈ coupledCases owner cases := by
  induction cases with
  | nil => simp at hcase
  | cons head rest ih =>
      obtain ⟨headLiteral, headBody⟩ := head
      simp only [List.mem_cons] at hcase
      simp only [coupledCases, List.mem_append]
      rcases hcase with heq | hrest
      · cases heq
        exact fun _ h => Or.inl h
      · exact fun group hgroup => Or.inr (ih hrest group hgroup)

theorem declaredStmts_mem_declaredCases_of_mem {literal : Literal}
    {body : Block Op} {cases : List (Literal × Block Op)}
    (hcase : (literal, body) ∈ cases) :
    ∀ name, name ∈ MemorySpill.declaredStmts body →
      name ∈ MemorySpill.declaredCases cases := by
  induction cases with
  | nil => simp at hcase
  | cons head rest ih =>
      obtain ⟨headLiteral, headBody⟩ := head
      simp only [List.mem_cons] at hcase
      simp only [MemorySpill.declaredCases, List.mem_append]
      rcases hcase with heq | hrest
      · cases heq
        exact fun _ h => Or.inl h
      · exact fun name hname => Or.inr (ih hrest name hname)

theorem BindingOrigin.switchCase {globalGroups : List (List SpillKey)}
    {globalDeclared : List Ident} {owner : Owner} {condition : Expr Op}
    {cases : List (Literal × Block Op)} {fallback : Option (Block Op)}
    {literal : Literal} {body : Block Op}
    (horigin : BindingOrigin globalGroups globalDeclared owner
      (.stmt (.switch condition cases fallback)))
    (hcase : (literal, body) ∈ cases) :
    BindingOrigin globalGroups globalDeclared owner (.stmts body) := by
  cases fallback with
  | none =>
      constructor
      · intro group hgroup
        apply horigin.groups group
        simpa [codeGroups, coupledStmt] using
          coupledStmts_mem_coupledCases_of_mem hcase group hgroup
      · intro name hname
        apply horigin.declared name
        simpa [codeDeclared, MemorySpill.declaredStmt] using
          declaredStmts_mem_declaredCases_of_mem hcase name hname
  | some fallbackBody =>
      constructor
      · intro group hgroup
        apply horigin.groups group
        simpa [codeGroups, coupledStmt] using List.mem_append_left
          (coupledStmts owner fallbackBody)
          (coupledStmts_mem_coupledCases_of_mem hcase group hgroup)
      · intro name hname
        apply horigin.declared name
        simpa [codeDeclared, MemorySpill.declaredStmt] using List.mem_append_left
          (MemorySpill.declaredStmts fallbackBody)
          (declaredStmts_mem_declaredCases_of_mem hcase name hname)

theorem BindingOrigin.switchDefault {globalGroups : List (List SpillKey)}
    {globalDeclared : List Ident} {owner : Owner} {condition : Expr Op}
    {cases : List (Literal × Block Op)} {body : Block Op}
    (horigin : BindingOrigin globalGroups globalDeclared owner
      (.stmt (.switch condition cases (some body)))) :
    BindingOrigin globalGroups globalDeclared owner (.stmts body) := by
  constructor
  · intro group hgroup
    apply horigin.groups group
    simp only [codeGroups, coupledStmt, List.mem_append]
    exact Or.inr hgroup
  · intro name hname
    apply horigin.declared name
    simp only [codeDeclared, MemorySpill.declaredStmt, List.mem_append]
    exact Or.inr hname

theorem liveScope_mem_liveCases_of_mem {selected : SpillSet} {owner : Owner}
    {live : SpillSet} {literal : Literal} {body : Block Op}
    {cases : List (Literal × Block Op)}
    (hcase : (literal, body) ∈ cases) :
    ∀ liveSet, liveSet ∈ liveScope selected owner live body →
      liveSet ∈ liveCases selected owner live cases := by
  induction cases with
  | nil => simp at hcase
  | cons head rest ih =>
      obtain ⟨headLiteral, headBody⟩ := head
      simp only [List.mem_cons] at hcase
      simp only [liveCases, List.mem_append]
      rcases hcase with heq | hrest
      · cases heq
        exact fun _ h => Or.inl h
      · exact fun liveSet h => Or.inr (ih hrest liveSet h)

theorem traceCovered_switchCase {selected : SpillSet} {frame : Frame}
    {live : SpillSet} {condition : Expr Op}
    {cases : List (Literal × Block Op)} {fallback : Option (Block Op)}
    {literal : Literal} {body : Block Op}
    (hsets : ∀ liveSet ∈
      (liveStmt selected frame.owner live
        (.switch condition cases fallback)).1,
      liveSet ∈ (frameLives selected frame).sets)
    (hcase : (literal, body) ∈ cases) :
    TraceCovered selected frame live body := by
  intro liveSet hmem
  apply hsets liveSet
  have hcases := liveScope_mem_liveCases_of_mem hcase liveSet (by
    simpa [liveScope] using hmem)
  cases fallback with
  | none => simpa [liveStmt] using hcases
  | some fallback =>
      simp only [liveStmt, List.mem_append]
      exact Or.inl hcases

theorem traceCovered_switchDefault {selected : SpillSet} {frame : Frame}
    {live : SpillSet} {condition : Expr Op}
    {cases : List (Literal × Block Op)} {body : Block Op}
    (hsets : ∀ liveSet ∈
      (liveStmt selected frame.owner live
        (.switch condition cases (some body))).1,
      liveSet ∈ (frameLives selected frame).sets) :
    TraceCovered selected frame live body := by
  intro liveSet hmem
  apply hsets liveSet
  simp only [liveStmt, List.mem_append]
  exact Or.inr (by simpa [liveScope] using hmem)

theorem BindingOrigin.funBody {globalGroups : List (List SpillKey)}
    {globalDeclared : List Ident} {outerOwner : Owner} {name : Ident}
    {params returns : List Ident} {body : Block Op}
    (horigin : BindingOrigin globalGroups globalDeclared outerOwner
      (.stmt (.funDef name params returns body))) :
    BindingOrigin globalGroups globalDeclared (some name) (.stmts body) := by
  constructor
  · intro group hgroup
    apply horigin.groups group
    simpa [codeGroups, coupledStmt] using hgroup
  · intro declared hdeclared
    apply horigin.declared declared
    change declared ∈ MemorySpill.declaredStmts body at hdeclared
    simp only [codeDeclared, MemorySpill.declaredStmt, List.mem_append]
    exact Or.inr hdeclared

theorem BindingOrigin.forInit {globalGroups : List (List SpillKey)}
    {globalDeclared : List Ident} {owner : Owner} {init post body : Block Op}
    {condition : Expr Op}
    (horigin : BindingOrigin globalGroups globalDeclared owner
      (.stmt (.forLoop init condition post body))) :
    BindingOrigin globalGroups globalDeclared owner (.stmts init) := by
  constructor
  · intro group hgroup
    change group ∈ coupledStmts owner init at hgroup
    apply horigin.groups group
    simp only [codeGroups, coupledStmt, List.mem_append]
    exact Or.inl (Or.inl hgroup)
  · intro name hname
    change name ∈ MemorySpill.declaredStmts init at hname
    apply horigin.declared name
    simp only [codeDeclared, MemorySpill.declaredStmt, List.mem_append]
    exact Or.inl (Or.inl hname)

theorem BindingOrigin.forPost {globalGroups : List (List SpillKey)}
    {globalDeclared : List Ident} {owner : Owner} {init post body : Block Op}
    {condition : Expr Op}
    (horigin : BindingOrigin globalGroups globalDeclared owner
      (.stmt (.forLoop init condition post body))) :
    BindingOrigin globalGroups globalDeclared owner (.stmts post) := by
  constructor
  · intro group hgroup
    change group ∈ coupledStmts owner post at hgroup
    apply horigin.groups group
    simp only [codeGroups, coupledStmt, List.mem_append]
    exact Or.inl (Or.inr hgroup)
  · intro name hname
    change name ∈ MemorySpill.declaredStmts post at hname
    apply horigin.declared name
    simp only [codeDeclared, MemorySpill.declaredStmt, List.mem_append]
    exact Or.inl (Or.inr hname)

theorem BindingOrigin.forBody {globalGroups : List (List SpillKey)}
    {globalDeclared : List Ident} {owner : Owner} {init post body : Block Op}
    {condition : Expr Op}
    (horigin : BindingOrigin globalGroups globalDeclared owner
      (.stmt (.forLoop init condition post body))) :
    BindingOrigin globalGroups globalDeclared owner (.stmts body) := by
  constructor
  · intro group hgroup
    change group ∈ coupledStmts owner body at hgroup
    apply horigin.groups group
    simp only [codeGroups, coupledStmt, List.mem_append]
    exact Or.inr hgroup
  · intro name hname
    change name ∈ MemorySpill.declaredStmts body at hname
    apply horigin.declared name
    simp only [codeDeclared, MemorySpill.declaredStmt, List.mem_append]
    exact Or.inr hname

theorem BindingOrigin.loopPost {globalGroups : List (List SpillKey)}
    {globalDeclared : List Ident} {owner : Owner} {post body : Block Op}
    {condition : Expr Op}
    (horigin : BindingOrigin globalGroups globalDeclared owner
      (.loop condition post body)) :
    BindingOrigin globalGroups globalDeclared owner (.stmts post) := by
  constructor
  · intro group hgroup
    exact horigin.groups group (List.mem_append_left _ hgroup)
  · intro name hname
    exact horigin.declared name (List.mem_append_left _ hname)

theorem BindingOrigin.loopBody {globalGroups : List (List SpillKey)}
    {globalDeclared : List Ident} {owner : Owner} {post body : Block Op}
    {condition : Expr Op}
    (horigin : BindingOrigin globalGroups globalDeclared owner
      (.loop condition post body)) :
    BindingOrigin globalGroups globalDeclared owner (.stmts body) := by
  constructor
  · intro group hgroup
    exact horigin.groups group (List.mem_append_right _ hgroup)
  · intro name hname
    exact horigin.declared name (List.mem_append_right _ hname)

/-- Every dynamic source binding originates at a declaration in the global
policy tree.  This is the runtime half of generated-temporary freshness. -/
def EnvDeclaredOrigin (globalDeclared : List Ident) (source : WordEnv) : Prop :=
  ∀ name, name ∈ source.map Prod.fst → name ∈ globalDeclared

theorem EnvDeclaredOrigin.empty (globalDeclared : List Ident) :
    EnvDeclaredOrigin globalDeclared [] := by simp [EnvDeclaredOrigin]

theorem EnvDeclaredOrigin.set {globalDeclared : List Ident} {source : WordEnv}
    (horigin : EnvDeclaredOrigin globalDeclared source) (name : Ident)
    (value : U256) :
    EnvDeclaredOrigin globalDeclared (envSet source name value) := by
  intro declared hdeclared
  rw [envSet_keys] at hdeclared
  exact horigin declared hdeclared

theorem EnvDeclaredOrigin.prepend {globalDeclared : List Ident}
    {source : WordEnv} (horigin : EnvDeclaredOrigin globalDeclared source)
    {name : Ident} {value : U256} (hname : name ∈ globalDeclared) :
    EnvDeclaredOrigin globalDeclared ((name, value) :: source) := by
  intro declared hdeclared
  simp only [List.map_cons, List.mem_cons] at hdeclared
  rcases hdeclared with rfl | hrest
  · exact hname
  · exact horigin declared hrest

theorem EnvDeclaredOrigin.prependList {globalDeclared : List Ident}
    {source front : WordEnv}
    (horigin : EnvDeclaredOrigin globalDeclared source)
    (hfront : ∀ name, name ∈ front.map Prod.fst → name ∈ globalDeclared) :
    EnvDeclaredOrigin globalDeclared (front ++ source) := by
  intro name hname
  simp only [List.map_append, List.mem_append] at hname
  exact hname.elim (hfront name) (horigin name)

theorem EnvDeclaredOrigin.restore {globalDeclared : List Ident}
    {outer source : WordEnv}
    (horigin : EnvDeclaredOrigin globalDeclared source) :
    EnvDeclaredOrigin globalDeclared (@YulSemantics.restore G outer source) := by
  intro name hname
  unfold YulSemantics.restore at hname
  rw [List.map_drop] at hname
  exact horigin name (List.mem_of_mem_drop hname)

theorem EnvDeclaredOrigin.avoids {globalDeclared : List Ident}
    {source : WordEnv} (horigin : EnvDeclaredOrigin globalDeclared source)
    {names : List Ident} (hfresh : ∀ name ∈ names, name ∉ globalDeclared) :
    ∀ name ∈ names, name ∉ source.map Prod.fst := by
  intro name hname hsource
  exact hfresh name hname (horigin name hsource)

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

theorem NamesBound.step {funs : FunEnv G} {source : WordEnv}
    {sourceState : EvmState} {code : Code Op}
    {final : WordEnv} {finalState : EvmState} {outcome : Outcome}
    {names : List Ident}
    (hstep : Step G funs source sourceState code
      (.sres final finalState outcome))
    (hbound : NamesBound names source) : NamesBound names final := by
  intro name hname
  obtain ⟨value, hget⟩ := hbound name hname
  apply envGet_exists_of_name_mem
  exact dom_mono hstep (envGet_name_mem hget)

theorem BindingOrigin.letGroup {globalGroups : List (List SpillKey)}
    {globalDeclared : List Ident} {owner : Owner} {names : List Ident}
    {value : Option (Expr Op)}
    (horigin : BindingOrigin globalGroups globalDeclared owner
      (.stmt (.letDecl names value))) (hmulti : names.length > 1) :
    names.map (fun name => ({ owner, name } : SpillKey)) ∈ globalGroups := by
  apply horigin.groups
  simp [codeGroups, coupledStmt, hmulti]

theorem BindingOrigin.assignGroup {globalGroups : List (List SpillKey)}
    {globalDeclared : List Ident} {owner : Owner} {names : List Ident}
    {value : Expr Op}
    (horigin : BindingOrigin globalGroups globalDeclared owner
      (.stmt (.assign names value))) (hmulti : names.length > 1) :
    names.map (fun name => ({ owner, name } : SpillKey)) ∈ globalGroups := by
  apply horigin.groups
  simp [codeGroups, coupledStmt, hmulti]

/-- Global temp-prefix freshness becomes the dynamic environment freshness
required by tuple distribution. -/
theorem tempNames_avoidEnv {raw : Block Op} {result : Result}
    {guards : List Nat} (hfacts : SpillFacts raw result guards)
    {owner : Owner} {names : List Ident} {source : WordEnv}
    (horigin : EnvDeclaredOrigin
      (MemorySpill.declaredStmts
        (resolveMemoryGuardStmts result.base result.reserved raw)) source) :
    ∀ temp ∈ names.map (tempName owner), temp ∉ source.map Prod.fst := by
  exact horigin.avoids (tempNames_fresh hfacts)


/-! ## Syntax origin inside the current frame -/

def codeCalls : Code Op → List Ident
  | .expr expression => callsExpr expression
  | .args args => callsArgs args
  | .stmt statement => frameCallsStmt statement
  | .stmts statements => frameCallsStmts statements
  | .loop condition post body =>
      callsExpr condition ++ frameCallsStmts post ++ frameCallsStmts body

/-- Every user-call name in the currently executed code occurs in the exact
owning frame.  `CodeTraceCovered` only tracks live sets, so this separate
origin invariant is required to invoke allocator call-edge separation. -/
def CodeOrigin (frame : Frame) (code : Code Op) : Prop :=
  ∀ name, name ∈ codeCalls code → name ∈ frameCallsStmts frame.body

theorem CodeOrigin.frame (frame : Frame) :
    CodeOrigin frame (.stmts frame.body) := by
  intro name hname
  exact hname

theorem CodeOrigin.call {frame : Frame} {name : Ident}
    {args : List (Expr Op)}
    (horigin : CodeOrigin frame (.expr (.call name args))) :
    name ∈ frameCallsStmts frame.body := by
  apply horigin name
  simp [codeCalls, callsExpr]

theorem CodeOrigin.callArgs {frame : Frame} {name : Ident}
    {args : List (Expr Op)}
    (horigin : CodeOrigin frame (.expr (.call name args))) :
    CodeOrigin frame (.args args) := by
  intro other hother
  apply horigin other
  change other ∈ callsArgs args at hother
  change other ∈ name :: callsArgs args
  exact List.mem_cons_of_mem name hother

theorem CodeOrigin.builtinArgs {frame : Frame} {op : Op}
    {args : List (Expr Op)}
    (horigin : CodeOrigin frame (.expr (.builtin op args))) :
    CodeOrigin frame (.args args) := by
  simpa [CodeOrigin, codeCalls, callsExpr] using horigin

theorem CodeOrigin.argsHead {frame : Frame} {expression : Expr Op}
    {rest : List (Expr Op)} (horigin : CodeOrigin frame (.args (expression :: rest))) :
    CodeOrigin frame (.expr expression) := by
  intro name hname
  apply horigin name
  simp only [codeCalls, callsArgs, List.mem_append]
  exact Or.inl hname

theorem CodeOrigin.argsTail {frame : Frame} {expression : Expr Op}
    {rest : List (Expr Op)} (horigin : CodeOrigin frame (.args (expression :: rest))) :
    CodeOrigin frame (.args rest) := by
  intro name hname
  apply horigin name
  simp only [codeCalls, callsArgs, List.mem_append]
  exact Or.inr hname

theorem CodeOrigin.stmtsHead {frame : Frame} {statement : Stmt Op}
    {rest : Block Op} (horigin : CodeOrigin frame (.stmts (statement :: rest))) :
    CodeOrigin frame (.stmt statement) := by
  intro name hname
  apply horigin name
  simp only [codeCalls, frameCallsStmts, List.mem_append]
  exact Or.inl hname

theorem CodeOrigin.stmtsTail {frame : Frame} {statement : Stmt Op}
    {rest : Block Op} (horigin : CodeOrigin frame (.stmts (statement :: rest))) :
    CodeOrigin frame (.stmts rest) := by
  intro name hname
  apply horigin name
  simp only [codeCalls, frameCallsStmts, List.mem_append]
  exact Or.inr hname

theorem CodeOrigin.block {frame : Frame} {body : Block Op}
    (horigin : CodeOrigin frame (.stmt (.block body))) :
    CodeOrigin frame (.stmts body) := by
  simpa [CodeOrigin, codeCalls, frameCallsStmt] using horigin

theorem CodeOrigin.condBody {frame : Frame} {condition : Expr Op}
    {body : Block Op} (horigin : CodeOrigin frame (.stmt (.cond condition body))) :
    CodeOrigin frame (.stmts body) := by
  intro name hname
  apply horigin name
  simp only [codeCalls, frameCallsStmt, List.mem_append]
  exact Or.inr hname

theorem CodeOrigin.condExpr {frame : Frame} {condition : Expr Op}
    {body : Block Op}
    (horigin : CodeOrigin frame (.stmt (.cond condition body))) :
    CodeOrigin frame (.expr condition) := by
  intro name hname
  apply horigin name
  simp only [codeCalls, frameCallsStmt, List.mem_append]
  exact Or.inl hname

theorem CodeOrigin.letExpr {frame : Frame} {names : List Ident}
    {expression : Expr Op}
    (horigin : CodeOrigin frame (.stmt (.letDecl names (some expression)))) :
    CodeOrigin frame (.expr expression) := by
  simpa [CodeOrigin, codeCalls, frameCallsStmt] using horigin

theorem CodeOrigin.assignExpr {frame : Frame} {names : List Ident}
    {expression : Expr Op}
    (horigin : CodeOrigin frame (.stmt (.assign names expression))) :
    CodeOrigin frame (.expr expression) := by
  simpa [CodeOrigin, codeCalls, frameCallsStmt] using horigin

theorem CodeOrigin.exprStmt {frame : Frame} {expression : Expr Op}
    (horigin : CodeOrigin frame (.stmt (.exprStmt expression))) :
    CodeOrigin frame (.expr expression) := by
  simpa [CodeOrigin, codeCalls, frameCallsStmt] using horigin

theorem frameCallsStmts_mem_frameCallsCases_of_mem {literal : Literal}
    {body : Block Op} {cases : List (Literal × Block Op)}
    (hcase : (literal, body) ∈ cases) :
    ∀ name, name ∈ frameCallsStmts body → name ∈ frameCallsCases cases := by
  induction cases with
  | nil => simp at hcase
  | cons head rest ih =>
      obtain ⟨headLiteral, headBody⟩ := head
      simp only [List.mem_cons] at hcase
      simp only [frameCallsCases, List.mem_append]
      rcases hcase with heq | hrest
      · cases heq
        exact fun _ h => Or.inl h
      · exact fun name h => Or.inr (ih hrest name h)

theorem CodeOrigin.switchExpr {frame : Frame} {condition : Expr Op}
    {cases : List (Literal × Block Op)} {fallback : Option (Block Op)}
    (horigin : CodeOrigin frame (.stmt (.switch condition cases fallback))) :
    CodeOrigin frame (.expr condition) := by
  intro name hname
  apply horigin name
  cases fallback with
  | none =>
      simp only [codeCalls, frameCallsStmt, List.append_nil, List.mem_append]
      exact Or.inl hname
  | some fallback =>
      simp only [codeCalls, frameCallsStmt, List.mem_append]
      exact Or.inl (Or.inl hname)

theorem CodeOrigin.switchCase {frame : Frame} {condition : Expr Op}
    {cases : List (Literal × Block Op)} {fallback : Option (Block Op)}
    {literal : Literal} {body : Block Op}
    (horigin : CodeOrigin frame (.stmt (.switch condition cases fallback)))
    (hcase : (literal, body) ∈ cases) :
    CodeOrigin frame (.stmts body) := by
  intro name hname
  apply horigin name
  have hcases := frameCallsStmts_mem_frameCallsCases_of_mem hcase name hname
  cases fallback with
  | none =>
      simp only [codeCalls, frameCallsStmt, List.append_nil, List.mem_append]
      exact Or.inr hcases
  | some fallback =>
      simp only [codeCalls, frameCallsStmt, List.mem_append]
      exact Or.inl (Or.inr hcases)

theorem CodeOrigin.switchDefault {frame : Frame} {condition : Expr Op}
    {cases : List (Literal × Block Op)} {body : Block Op}
    (horigin : CodeOrigin frame (.stmt (.switch condition cases (some body)))) :
    CodeOrigin frame (.stmts body) := by
  intro name hname
  apply horigin name
  simp only [codeCalls, frameCallsStmt, List.mem_append]
  exact Or.inr hname

theorem CodeOrigin.forInit {frame : Frame} {init post body : Block Op}
    {condition : Expr Op}
    (horigin : CodeOrigin frame (.stmt (.forLoop init condition post body))) :
    CodeOrigin frame (.stmts init) := by
  intro name hname
  apply horigin name
  simp only [codeCalls, frameCallsStmt, List.mem_append]
  exact Or.inl (Or.inl (Or.inl hname))

theorem CodeOrigin.forCond {frame : Frame} {init post body : Block Op}
    {condition : Expr Op}
    (horigin : CodeOrigin frame (.stmt (.forLoop init condition post body))) :
    CodeOrigin frame (.expr condition) := by
  intro name hname
  apply horigin name
  simp only [codeCalls, frameCallsStmt, List.mem_append]
  exact Or.inl (Or.inl (Or.inr hname))

theorem CodeOrigin.forPost {frame : Frame} {init post body : Block Op}
    {condition : Expr Op}
    (horigin : CodeOrigin frame (.stmt (.forLoop init condition post body))) :
    CodeOrigin frame (.stmts post) := by
  intro name hname
  apply horigin name
  simp only [codeCalls, frameCallsStmt, List.mem_append]
  exact Or.inl (Or.inr hname)

theorem CodeOrigin.forBody {frame : Frame} {init post body : Block Op}
    {condition : Expr Op}
    (horigin : CodeOrigin frame (.stmt (.forLoop init condition post body))) :
    CodeOrigin frame (.stmts body) := by
  intro name hname
  apply horigin name
  simp only [codeCalls, frameCallsStmt, List.mem_append]
  exact Or.inr hname

theorem CodeOrigin.loopCond {frame : Frame} {post body : Block Op}
    {condition : Expr Op}
    (horigin : CodeOrigin frame (.loop condition post body)) :
    CodeOrigin frame (.expr condition) := by
  intro name hname
  exact horigin name (by
    simp only [codeCalls, List.mem_append]
    exact Or.inl (Or.inl hname))

theorem CodeOrigin.loopPost {frame : Frame} {post body : Block Op}
    {condition : Expr Op}
    (horigin : CodeOrigin frame (.loop condition post body)) :
    CodeOrigin frame (.stmts post) := by
  intro name hname
  exact horigin name (by
    simp only [codeCalls, List.mem_append]
    exact Or.inl (Or.inr hname))

theorem CodeOrigin.loopBody {frame : Frame} {post body : Block Op}
    {condition : Expr Op}
    (horigin : CodeOrigin frame (.loop condition post body)) :
    CodeOrigin frame (.stmts body) := by
  intro name hname
  exact horigin name (by
    simp only [codeCalls, List.mem_append]
    exact Or.inr hname)

/-! Function-frame origin is distinct from call-name origin: block execution
pushes a hoisted scope, whose declarations must be covered by the object-wide
policy frame list. -/

def codeNestedFrames : Code Op → List Frame
  | .expr _ | .args _ => []
  | .stmt statement => nestedFramesStmt statement
  | .stmts statements => nestedFramesStmts statements
  | .loop _ post body => nestedFramesStmts post ++ nestedFramesStmts body

def CodeFramesOrigin (allFrames : List Frame) (code : Code Op) : Prop :=
  ∀ frame, frame ∈ codeNestedFrames code → frame ∈ allFrames

theorem CodeFramesOrigin.expr (allFrames : List Frame) (expression : Expr Op) :
    CodeFramesOrigin allFrames (.expr expression) := by
  simp [CodeFramesOrigin, codeNestedFrames]

theorem CodeFramesOrigin.args (allFrames : List Frame)
    (args : List (Expr Op)) : CodeFramesOrigin allFrames (.args args) := by
  simp [CodeFramesOrigin, codeNestedFrames]

theorem CodeFramesOrigin.root (body : Block Op) :
    CodeFramesOrigin (frames body) (.stmts body) := by
  intro frame hframe
  change frame ∈ nestedFramesStmts body at hframe
  exact List.mem_cons_of_mem _ hframe

theorem frameNestedOrigin_of_mem {body : Block Op} {frame : Frame}
    (hframe : frame ∈ frames body) :
    CodeFramesOrigin (frames body) (.stmts frame.body) := by
  intro child hchild
  simp only [codeNestedFrames] at hchild
  simp only [frames, List.mem_cons] at hframe ⊢
  rcases hframe with rfl | hnested
  · exact Or.inr hchild
  · exact Or.inr
      (nestedFramesStmts_descendants body frame hnested child hchild)

theorem CodeFramesOrigin.stmtsHead {allFrames : List Frame}
    {statement : Stmt Op} {rest : Block Op}
    (horigin : CodeFramesOrigin allFrames (.stmts (statement :: rest))) :
    CodeFramesOrigin allFrames (.stmt statement) := by
  intro frame hframe
  apply horigin frame
  simp only [codeNestedFrames, nestedFramesStmts, List.mem_append]
  exact Or.inl hframe

theorem CodeFramesOrigin.stmtsTail {allFrames : List Frame}
    {statement : Stmt Op} {rest : Block Op}
    (horigin : CodeFramesOrigin allFrames (.stmts (statement :: rest))) :
    CodeFramesOrigin allFrames (.stmts rest) := by
  intro frame hframe
  apply horigin frame
  simp only [codeNestedFrames, nestedFramesStmts, List.mem_append]
  exact Or.inr hframe

theorem CodeFramesOrigin.block {allFrames : List Frame} {body : Block Op}
    (horigin : CodeFramesOrigin allFrames (.stmt (.block body))) :
    CodeFramesOrigin allFrames (.stmts body) := by
  simpa [CodeFramesOrigin, codeNestedFrames, nestedFramesStmt] using horigin

theorem CodeFramesOrigin.condBody {allFrames : List Frame}
    {condition : Expr Op} {body : Block Op}
    (horigin : CodeFramesOrigin allFrames (.stmt (.cond condition body))) :
    CodeFramesOrigin allFrames (.stmts body) := by
  simpa [CodeFramesOrigin, codeNestedFrames, nestedFramesStmt] using horigin

theorem nestedFramesStmts_mem_nestedFramesCases_of_mem {literal : Literal}
    {body : Block Op} {cases : List (Literal × Block Op)}
    (hcase : (literal, body) ∈ cases) :
    ∀ frame, frame ∈ nestedFramesStmts body →
      frame ∈ nestedFramesCases cases := by
  induction cases with
  | nil => simp at hcase
  | cons head rest ih =>
      obtain ⟨headLiteral, headBody⟩ := head
      simp only [List.mem_cons] at hcase
      simp only [nestedFramesCases, List.mem_append]
      rcases hcase with heq | hrest
      · cases heq
        exact fun _ h => Or.inl h
      · exact fun frame h => Or.inr (ih hrest frame h)

theorem CodeFramesOrigin.switchCase {allFrames : List Frame}
    {condition : Expr Op} {cases : List (Literal × Block Op)}
    {fallback : Option (Block Op)} {literal : Literal} {body : Block Op}
    (horigin : CodeFramesOrigin allFrames
      (.stmt (.switch condition cases fallback)))
    (hcase : (literal, body) ∈ cases) :
    CodeFramesOrigin allFrames (.stmts body) := by
  intro frame hframe
  apply horigin frame
  have hcases := nestedFramesStmts_mem_nestedFramesCases_of_mem hcase frame hframe
  cases fallback with
  | none => simpa [codeNestedFrames, nestedFramesStmt] using hcases
  | some fallback =>
      simp only [codeNestedFrames, nestedFramesStmt, List.mem_append]
      exact Or.inl hcases

theorem CodeFramesOrigin.switchDefault {allFrames : List Frame}
    {condition : Expr Op} {cases : List (Literal × Block Op)}
    {body : Block Op}
    (horigin : CodeFramesOrigin allFrames
      (.stmt (.switch condition cases (some body)))) :
    CodeFramesOrigin allFrames (.stmts body) := by
  intro frame hframe
  apply horigin frame
  simp only [codeNestedFrames, nestedFramesStmt, List.mem_append]
  exact Or.inr hframe

theorem codeCalls_execCode (mode : OriginMode) (code : Code Op) :
    codeCalls (execCode mode code) = codeCalls code := by
  cases mode with
  | identity => rfl
  | «object» layout =>
      cases code with
      | expr expression =>
          exact callsExpr_resolveForLayout layout expression
      | args args =>
          exact callsArgs_resolveForLayout layout args
      | stmt statement =>
          exact frameCallsStmt_resolveForLayout layout statement
      | stmts statements =>
          exact frameCallsStmts_resolveForLayout layout statements
      | loop condition post body =>
          change codeCalls
            (resolveForLayoutCode layout (.loop condition post body)) = _
          rw [resolveForLayoutCode_loop]
          simp only [codeCalls]
          rw [callsExpr_resolveForLayout,
            frameCallsStmts_resolveForLayout,
            frameCallsStmts_resolveForLayout]

theorem codeNestedFrames_execCode (mode : OriginMode) (code : Code Op) :
    codeNestedFrames (execCode mode code) =
      (codeNestedFrames code).map mode.execFrame := by
  cases mode with
  | identity =>
      change codeNestedFrames code = (codeNestedFrames code).map id
      exact (List.map_id _).symm
  | «object» layout =>
      cases code with
      | expr expression => simp [execCode, codeNestedFrames]
      | args args => simp [execCode, codeNestedFrames]
      | stmt statement =>
          exact nestedFramesStmt_resolveForLayout layout statement
      | stmts statements =>
          exact nestedFramesStmts_resolveForLayout layout statements
      | loop condition post body =>
          change codeNestedFrames
            (resolveForLayoutCode layout (.loop condition post body)) = _
          rw [resolveForLayoutCode_loop]
          simp only [codeNestedFrames, List.map_append]
          rw [nestedFramesStmts_resolveForLayout,
            nestedFramesStmts_resolveForLayout]

theorem CodeOrigin.executed {mode : OriginMode} {frame : Frame}
    {code : Code Op} (horigin : CodeOrigin frame code) :
    CodeOrigin (mode.execFrame frame) (execCode mode code) := by
  intro name hname
  rw [codeCalls_execCode] at hname
  rw [OriginMode.execFrame_calls]
  exact horigin name hname

theorem CodeFramesOrigin.executed {mode : OriginMode}
    {allFrames : List Frame} {code : Code Op}
    (horigin : CodeFramesOrigin allFrames code) :
    CodeFramesOrigin (allFrames.map mode.execFrame) (execCode mode code) := by
  intro frame hframe
  rw [codeNestedFrames_execCode] at hframe
  obtain ⟨policyFrame, hpolicy, heq⟩ := List.mem_map.mp hframe
  rw [← heq]
  exact List.mem_map.mpr ⟨policyFrame, horigin policyFrame hpolicy, rfl⟩

theorem codeTraceCovered_exec_iff (mode : OriginMode) (selected : SpillSet)
    (frame : Frame) (live : SpillSet) (code : Code Op) :
    CodeTraceCovered selected (mode.execFrame frame) live
        (execCode mode code) ↔
      CodeTraceCovered selected frame live code := by
  cases mode with
  | identity => rfl
  | «object» layout =>
      cases code with
      | expr expression => simp [execCode, CodeTraceCovered]
      | args args => simp [execCode, CodeTraceCovered]
      | stmt statement =>
          change CodeTraceCovered selected
            ((OriginMode.object layout).execFrame frame) live
            (resolveForLayoutCode layout (.stmt statement)) ↔ _
          rw [resolveForLayoutCode_stmt]
          simp only [CodeTraceCovered, OriginMode.execFrame_owner,
            frameLives_execFrame]
          rw [liveStmt_resolveForLayout]
      | stmts statements =>
          exact traceCovered_exec_iff (.object layout) selected frame live statements
      | loop condition post body =>
          change CodeTraceCovered selected
            ((OriginMode.object layout).execFrame frame) live
            (resolveForLayoutCode layout (.loop condition post body)) ↔ _
          rw [resolveForLayoutCode_loop]
          simp only [CodeTraceCovered]
          have hpost := traceCovered_exec_iff (OriginMode.object layout)
            selected frame live post
          have hbody := traceCovered_exec_iff (OriginMode.object layout)
            selected frame live body
          simpa only [OriginMode.execBlock] using and_congr hpost hbody

/-- Static component of the main simulation motive.  Allocation certificates
remain on `policyFrame`/`policyCode`; semantic stepping uses their exact
mode-mapped `executedFrame`/`executedCode`. -/
structure PolicyExecOrigin (mode : OriginMode) (policyRoot : Block Op)
    (policyFrame executedFrame : Frame) (policyCode executedCode : Code Op) :
    Prop where
  executedFrame_eq : executedFrame = mode.execFrame policyFrame
  executedCode_eq : executedCode = execCode mode policyCode
  policyFrame_mem : policyFrame ∈ frames policyRoot
  callOrigin : CodeOrigin policyFrame policyCode
  frameOrigin : CodeFramesOrigin (frames policyRoot) policyCode
  bindingOrigin : BindingOrigin (coupledStmts none policyRoot)
    (MemorySpill.declaredStmts policyRoot) policyFrame.owner policyCode

theorem PolicyExecOrigin.root (mode : OriginMode) (body : Block Op) :
    let policyFrame : Frame :=
      { owner := none, params := [], returns := [], body }
    PolicyExecOrigin mode body policyFrame (mode.execFrame policyFrame)
      (.stmts body) (execCode mode (.stmts body)) := by
  dsimp only
  exact {
    executedFrame_eq := rfl
    executedCode_eq := rfl
    policyFrame_mem := by simp [frames]
    callOrigin := CodeOrigin.frame _
    frameOrigin := CodeFramesOrigin.root _
    bindingOrigin := BindingOrigin.root _ }

theorem PolicyExecOrigin.executedCallOrigin {mode : OriginMode}
    {policyRoot : Block Op} {policyFrame executedFrame : Frame}
    {policyCode executedCode : Code Op}
    (horigin : PolicyExecOrigin mode policyRoot policyFrame executedFrame
      policyCode executedCode) :
    CodeOrigin executedFrame executedCode := by
  rw [horigin.executedFrame_eq, horigin.executedCode_eq]
  exact horigin.callOrigin.executed

theorem PolicyExecOrigin.executedFrameOrigin {mode : OriginMode}
    {policyRoot : Block Op} {policyFrame executedFrame : Frame}
    {policyCode executedCode : Code Op}
    (horigin : PolicyExecOrigin mode policyRoot policyFrame executedFrame
      policyCode executedCode) :
    CodeFramesOrigin ((frames policyRoot).map mode.execFrame) executedCode := by
  rw [horigin.executedCode_eq]
  exact horigin.frameOrigin.executed

/-- Generic same-frame descendant constructor.  Branch-specific helpers only
need to establish their three syntax-origin facts; mode transport is uniform. -/
theorem PolicyExecOrigin.child {mode : OriginMode} {policyRoot : Block Op}
    {policyFrame executedFrame : Frame} {parentPolicy parentExecuted child : Code Op}
    (horigin : PolicyExecOrigin mode policyRoot policyFrame executedFrame
      parentPolicy parentExecuted)
    (hcalls : CodeOrigin policyFrame child)
    (hframes : CodeFramesOrigin (frames policyRoot) child)
    (hbindings : BindingOrigin (coupledStmts none policyRoot)
      (MemorySpill.declaredStmts policyRoot) policyFrame.owner child) :
    PolicyExecOrigin mode policyRoot policyFrame executedFrame child
      (execCode mode child) := by
  exact {
    executedFrame_eq := horigin.executedFrame_eq
    executedCode_eq := rfl
    policyFrame_mem := horigin.policyFrame_mem
    callOrigin := hcalls
    frameOrigin := hframes
    bindingOrigin := hbindings }

/-- Full non-semantic context carried by every code induction branch. -/
structure ControlMotiveContext (mode : OriginMode) (policyRoot : Block Op)
    (selected : SpillSet) (policyFrame executedFrame : Frame)
    (live : SpillSet) (policyCode executedCode : Code Op)
    (source : WordEnv) : Prop where
  origin : PolicyExecOrigin mode policyRoot policyFrame executedFrame
    policyCode executedCode
  trace : CodeTraceCovered selected policyFrame live policyCode
  envDeclared : EnvDeclaredOrigin (MemorySpill.declaredStmts policyRoot) source

/-- A direct declaration gets its post-declaration live-set certificate from
the surrounding statement sequence.  Other code shapes need no additional
certificate. -/
def LetAfterCertified (selected : SpillSet) (frame : Frame) (live : SpillSet) :
    Code Op → Prop
  | .stmt (.letDecl names value) =>
      LiveCertified selected frame
        (liveAfterCode selected frame.owner live (.stmt (.letDecl names value)))
  | _ => True

theorem selectedBindingsWF_of_mem {selected : SpillSet} {allFrames : List Frame}
    {frame : Frame} (hwf : selectedBindingsWF selected allFrames = true)
    (hmem : frame ∈ allFrames) :
    selectedBindingsStmtsOK selected frame
      (frameInitialLive selected frame) frame.body = true := by
  have hframe := (List.all_eq_true.mp hwf) frame hmem
  simpa [selectedBindingsWF, frameInitialLive] using hframe

theorem selectedBindingsCasesOK_of_mem {selected : SpillSet} {frame : Frame}
    {live : SpillSet} {cases : List (Literal × Block Op)}
    {literal : Literal} {body : Block Op}
    (hok : selectedBindingsCasesOK selected frame live cases = true)
    (hmem : (literal, body) ∈ cases) :
    selectedBindingsStmtsOK selected frame live body = true := by
  induction cases with
  | nil => simp at hmem
  | cons head rest ih =>
      obtain ⟨headLiteral, headBody⟩ := head
      have hparts :
          selectedBindingsStmtsOK selected frame live headBody = true ∧
            selectedBindingsCasesOK selected frame live rest = true := by
        simpa only [selectedBindingsCasesOK, Bool.and_eq_true] using hok
      rcases List.mem_cons.mp hmem with heq | hrest
      · cases heq
        exact hparts.1
      · exact ih hparts.2 hrest

theorem selectedBindingsSwitchCase_of_ok {selected : SpillSet} {frame : Frame}
    {live : SpillSet} {condition : Expr Op}
    {cases : List (Literal × Block Op)} {fallback : Option (Block Op)}
    {literal : Literal} {body : Block Op}
    (hok : selectedBindingsStmtOK selected frame live
      (.switch condition cases fallback) = true)
    (hmem : (literal, body) ∈ cases) :
    selectedBindingsStmtsOK selected frame live body = true := by
  apply selectedBindingsCasesOK_of_mem (hmem := hmem)
  cases fallback <;>
    simp only [selectedBindingsStmtOK, Bool.and_eq_true] at hok
  · exact hok.1
  · exact hok.1

/-- Dynamic component of the induction motive: function return names remain
bound on every control path, including break/continue paths that a surrounding
loop may catch. -/
structure ControlStepContext (mode : OriginMode) (policyRoot : Block Op)
    (selected : SpillSet) (policyFrame executedFrame : Frame)
    (live : SpillSet) (policyCode executedCode : Code Op)
    (exitNames : List Ident) (source : WordEnv) : Prop where
  motive : ControlMotiveContext mode policyRoot selected policyFrame
    executedFrame live policyCode executedCode source
  selectedBindingsWF : MemorySpillSelect.selectedBindingsWF selected
    (frames policyRoot) = true
  selectedBindingsOK : selectedBindingsCodeOK selected policyFrame live
    policyCode = true
  letAfterCertified : LetAfterCertified selected policyFrame live policyCode
  exitsBound : NamesBound exitNames source
  exitsInSignature : ∀ name ∈ exitNames, name ∈ policyFrame.params ++ policyFrame.returns
  exitsNodup : exitNames.Nodup

theorem ControlStepContext.selectedLetReady {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {names : List Ident} {value : Option (Expr Op)} {executedCode : Code Op}
    {exitNames : List Ident} {source : WordEnv}
    (hctx : ControlStepContext mode policyRoot selected policyFrame executedFrame
      live (.stmt (.letDecl names value)) executedCode exitNames source)
    {name : Ident} (hname : name ∈ names)
    (hselected : ({ owner := policyFrame.owner, name } : SpillKey) ∈ selected) :
    ({ owner := policyFrame.owner, name } : SpillKey) ∉ live ∧
      name ∉ policyFrame.params ++ policyFrame.returns := by
  have hall : names.all (fun name =>
      let key : SpillKey := { owner := policyFrame.owner, name }
      !selected.contains key ||
        (!live.contains key &&
          !(policyFrame.params ++ policyFrame.returns).contains name)) = true := by
    simpa only [selectedBindingsCodeOK, selectedBindingsStmtOK] using
      hctx.selectedBindingsOK
  have hnameOK := (List.all_eq_true.mp hall) name hname
  have hcontains : selected.contains
      ({ owner := policyFrame.owner, name } : SpillKey) = true := by
    simpa using hselected
  simp only [hcontains, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hnameOK
  simpa using hnameOK

theorem ControlStepContext.selectedAssignReady {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {names : List Ident} {value : Expr Op} {executedCode : Code Op}
    {exitNames : List Ident} {source : WordEnv}
    (hctx : ControlStepContext mode policyRoot selected policyFrame executedFrame
      live (.stmt (.assign names value)) executedCode exitNames source)
    {name : Ident} (hname : name ∈ names)
    (hselected : ({ owner := policyFrame.owner, name } : SpillKey) ∈ selected) :
    ({ owner := policyFrame.owner, name } : SpillKey) ∈ live := by
  have hall : names.all (fun name =>
      let key : SpillKey := { owner := policyFrame.owner, name }
      !selected.contains key || live.contains key) = true := by
    simpa only [selectedBindingsCodeOK, selectedBindingsStmtOK] using
      hctx.selectedBindingsOK
  have hnameOK := (List.all_eq_true.mp hall) name hname
  have hcontains : selected.contains
      ({ owner := policyFrame.owner, name } : SpillKey) = true := by
    simpa using hselected
  simp only [hcontains, Bool.not_true, Bool.false_or] at hnameOK
  simpa using hnameOK

/-- Generic same-frame child constructor for the dynamic induction context. -/
theorem ControlStepContext.child {mode : OriginMode} {policyRoot : Block Op}
    {selected : SpillSet} {policyFrame executedFrame : Frame}
    {live childLive : SpillSet} {parentPolicy parentExecuted child : Code Op}
    {exitNames : List Ident} {source childSource : WordEnv}
    (hctx : ControlStepContext mode policyRoot selected policyFrame executedFrame
      live parentPolicy parentExecuted exitNames source)
    (hcalls : CodeOrigin policyFrame child)
    (hframes : CodeFramesOrigin (frames policyRoot) child)
    (hbindings : BindingOrigin (coupledStmts none policyRoot)
      (MemorySpill.declaredStmts policyRoot) policyFrame.owner child)
    (htrace : CodeTraceCovered selected policyFrame childLive child)
    (hselectedBindings : selectedBindingsCodeOK selected policyFrame childLive
      child = true)
    (hletAfter : LetAfterCertified selected policyFrame childLive child)
    (henv : EnvDeclaredOrigin (MemorySpill.declaredStmts policyRoot) childSource)
    (hbound : NamesBound exitNames childSource) :
    ControlStepContext mode policyRoot selected policyFrame executedFrame
      childLive child (execCode mode child) exitNames childSource := by
  exact {
    motive := {
      origin := hctx.motive.origin.child hcalls hframes hbindings
      trace := htrace
      envDeclared := henv }
    selectedBindingsWF := hctx.selectedBindingsWF
    selectedBindingsOK := hselectedBindings
    letAfterCertified := hletAfter
    exitsBound := hbound
    exitsInSignature := hctx.exitsInSignature
    exitsNodup := hctx.exitsNodup }

/-- Recover the exact policy callee behind a dynamic lookup in either direct
or object mode, together with the full dynamic context for its body. -/
theorem ControlStepContext.calleeBody {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {sourceFuns : FunEnv G} {name : Ident} {decl : FDecl G}
    {closure : FunEnv G} {argvals : List U256}
    (hbindingsWF : MemorySpillSelect.selectedBindingsWF selected
      (frames policyRoot) = true)
    (hcovered : FunsCovered G (fun body => body)
      ((frames policyRoot).map mode.execFrame) sourceFuns)
    (hlookup : lookupFun sourceFuns name = some (decl, closure))
    (hlength : argvals.length = decl.params.length)
    (hnodup : (decl.params ++ decl.rets).Nodup) :
    ∃ policyCallee,
      policyCallee ∈ frames policyRoot ∧
      mode.execFrame policyCallee = calleeFrame name decl ∧
      FunsCovered G (fun body => body)
        ((frames policyRoot).map mode.execFrame) closure ∧
      ControlStepContext mode policyRoot selected policyCallee
        (calleeFrame name decl) (frameInitialLive selected policyCallee)
        (.stmts policyCallee.body) (.stmts decl.body) decl.rets
        (callEnv decl.params decl.rets argvals) := by
  obtain ⟨hdecl, hclosure⟩ := hcovered.lookup hlookup
  obtain ⟨executedCallee, hexecutedMem, howner, hparams, hreturns, hbody⟩ :=
    hdecl
  have hexecutedEq : executedCallee = calleeFrame name decl := by
    cases executedCallee
    simp_all [calleeFrame]
  subst executedCallee
  obtain ⟨policyCallee, hpolicyMem, hframeEq⟩ :=
    List.mem_map.mp hexecutedMem
  have hbodyEq : mode.execBlock policyCallee.body = decl.body := by
    have := congrArg Frame.body hframeEq
    cases mode <;> simpa [OriginMode.execFrame, OriginMode.execBlock,
      calleeFrame] using this
  have horigin : PolicyExecOrigin mode policyRoot policyCallee
      (calleeFrame name decl) (.stmts policyCallee.body) (.stmts decl.body) := by
    exact {
      executedFrame_eq := hframeEq.symm
      executedCode_eq := by
        cases mode <;> simpa [execCode, OriginMode.execBlock] using hbodyEq.symm
      policyFrame_mem := hpolicyMem
      callOrigin := CodeOrigin.frame policyCallee
      frameOrigin := frameNestedOrigin_of_mem hpolicyMem
      bindingOrigin := (frameBindingOrigin_of_mem hpolicyMem).body }
  have hentry := callEntryFacts hlength hnodup
  have hentryOrigin : EnvDeclaredOrigin
      (MemorySpill.declaredStmts policyRoot)
      (callEnv decl.params decl.rets argvals) := by
    intro boundName hboundName
    apply (frameBindingOrigin_of_mem hpolicyMem).declared boundName
    have hsignature : boundName ∈ decl.params ++ decl.rets :=
      hentry.names boundName hboundName
    have hparamsEq : policyCallee.params = decl.params := by
      have := congrArg Frame.params hframeEq
      simpa [calleeFrame] using this
    have hreturnsEq : policyCallee.returns = decl.rets := by
      have := congrArg Frame.returns hframeEq
      simpa [calleeFrame] using this
    simp only [List.mem_append]
    exact Or.inl (by simpa [hparamsEq, hreturnsEq] using hsignature)
  have hexitsBound : NamesBound decl.rets
      (callEnv decl.params decl.rets argvals) := by
    intro returnName hreturn
    exact ⟨0, hentry.zero returnName hreturn⟩
  have hexitsSignature : ∀ returnName ∈ decl.rets,
      returnName ∈ policyCallee.params ++ policyCallee.returns := by
    intro returnName hreturn
    have hreturnsEq : policyCallee.returns = decl.rets := by
      have := congrArg Frame.returns hframeEq
      simpa [calleeFrame] using this
    exact List.mem_append_right _ (by simpa [hreturnsEq] using hreturn)
  refine ⟨policyCallee, hpolicyMem, hframeEq, hclosure, ?_⟩
  exact {
    motive := {
      origin := horigin
      trace := traceCovered_frame selected policyCallee
      envDeclared := hentryOrigin }
    selectedBindingsWF := hbindingsWF
    selectedBindingsOK := by
      exact selectedBindingsWF_of_mem hbindingsWF hpolicyMem
    letAfterCertified := trivial
    exitsBound := hexitsBound
    exitsInSignature := hexitsSignature
    exitsNodup := (List.nodup_append.mp hnodup).2.1 }

theorem ControlMotiveContext.executedTrace {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {policyCode executedCode : Code Op} {source : WordEnv}
    (hctx : ControlMotiveContext mode policyRoot selected policyFrame
      executedFrame live policyCode executedCode source) :
    CodeTraceCovered selected executedFrame live executedCode := by
  rw [hctx.origin.executedFrame_eq, hctx.origin.executedCode_eq]
  exact (codeTraceCovered_exec_iff mode selected policyFrame live policyCode).2
    hctx.trace

theorem ControlMotiveContext.rootInitial {raw : Block Op} {result : Result}
    (mode : OriginMode) :
    let policyRoot :=
      resolveMemoryGuardStmts result.base result.reserved raw
    let policyFrame : Frame :=
      { owner := none, params := [], returns := [], body := policyRoot }
    ControlMotiveContext mode policyRoot result.selection policyFrame
      (mode.execFrame policyFrame)
      (frameInitialLive result.selection policyFrame)
      (.stmts policyRoot) (execCode mode (.stmts policyRoot)) [] := by
  dsimp only
  let policyRoot := resolveMemoryGuardStmts result.base result.reserved raw
  let policyFrame : Frame :=
    { owner := none, params := [], returns := [], body := policyRoot }
  exact {
    origin := PolicyExecOrigin.root mode policyRoot
    trace := traceCovered_frame result.selection policyFrame
    envDeclared := EnvDeclaredOrigin.empty _ }

theorem PolicyExecOrigin.stmtsHead {mode : OriginMode} {policyRoot : Block Op}
    {policyFrame executedFrame : Frame} {statement : Stmt Op}
    {rest : Block Op} {executedCode : Code Op}
    (horigin : PolicyExecOrigin mode policyRoot policyFrame executedFrame
      (.stmts (statement :: rest)) executedCode) :
    PolicyExecOrigin mode policyRoot policyFrame executedFrame
      (.stmt statement) (execCode mode (.stmt statement)) := by
  exact {
    executedFrame_eq := horigin.executedFrame_eq
    executedCode_eq := rfl
    policyFrame_mem := horigin.policyFrame_mem
    callOrigin := horigin.callOrigin.stmtsHead
    frameOrigin := horigin.frameOrigin.stmtsHead
    bindingOrigin := horigin.bindingOrigin.stmtsHead }

theorem PolicyExecOrigin.stmtsTail {mode : OriginMode} {policyRoot : Block Op}
    {policyFrame executedFrame : Frame} {statement : Stmt Op}
    {rest : Block Op} {executedCode : Code Op}
    (horigin : PolicyExecOrigin mode policyRoot policyFrame executedFrame
      (.stmts (statement :: rest)) executedCode) :
    PolicyExecOrigin mode policyRoot policyFrame executedFrame
      (.stmts rest) (execCode mode (.stmts rest)) := by
  exact {
    executedFrame_eq := horigin.executedFrame_eq
    executedCode_eq := rfl
    policyFrame_mem := horigin.policyFrame_mem
    callOrigin := horigin.callOrigin.stmtsTail
    frameOrigin := horigin.frameOrigin.stmtsTail
    bindingOrigin := horigin.bindingOrigin.stmtsTail }

theorem ControlMotiveContext.stmtsHead {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {statement : Stmt Op} {rest : Block Op} {executedCode : Code Op}
    {source : WordEnv}
    (hctx : ControlMotiveContext mode policyRoot selected policyFrame
      executedFrame live (.stmts (statement :: rest)) executedCode source) :
    ControlMotiveContext mode policyRoot selected policyFrame executedFrame live
      (.stmt statement) (execCode mode (.stmt statement)) source := by
  exact {
    origin := hctx.origin.stmtsHead
    trace := hctx.trace.head
    envDeclared := hctx.envDeclared }

theorem ControlMotiveContext.stmtsTail {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {statement : Stmt Op} {rest : Block Op} {executedCode : Code Op}
    {source : WordEnv}
    (hctx : ControlMotiveContext mode policyRoot selected policyFrame
      executedFrame live (.stmts (statement :: rest)) executedCode source) :
    ControlMotiveContext mode policyRoot selected policyFrame executedFrame
      (liveStmt selected policyFrame.owner live statement).2
      (.stmts rest) (execCode mode (.stmts rest)) source := by
  exact {
    origin := hctx.origin.stmtsTail
    trace := hctx.trace.tail
    envDeclared := hctx.envDeclared }

theorem PolicyExecOrigin.blockBody {mode : OriginMode} {policyRoot : Block Op}
    {policyFrame executedFrame : Frame} {body : Block Op}
    {executedCode : Code Op}
    (horigin : PolicyExecOrigin mode policyRoot policyFrame executedFrame
      (.stmt (.block body)) executedCode) :
    PolicyExecOrigin mode policyRoot policyFrame executedFrame
      (.stmts body) (execCode mode (.stmts body)) := by
  exact {
    executedFrame_eq := horigin.executedFrame_eq
    executedCode_eq := rfl
    policyFrame_mem := horigin.policyFrame_mem
    callOrigin := horigin.callOrigin.block
    frameOrigin := horigin.frameOrigin.block
    bindingOrigin := horigin.bindingOrigin.block }

theorem ControlMotiveContext.blockBody {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet} {body : Block Op}
    {executedCode : Code Op} {source : WordEnv}
    (hctx : ControlMotiveContext mode policyRoot selected policyFrame
      executedFrame live (.stmt (.block body)) executedCode source) :
    ControlMotiveContext mode policyRoot selected policyFrame executedFrame live
      (.stmts body) (execCode mode (.stmts body)) source := by
  exact {
    origin := hctx.origin.blockBody
    trace := traceCovered_block hctx.trace
    envDeclared := hctx.envDeclared }

theorem PolicyExecOrigin.condExpr {mode : OriginMode} {policyRoot : Block Op}
    {policyFrame executedFrame : Frame} {condition : Expr Op}
    {body : Block Op} {executedCode : Code Op}
    (horigin : PolicyExecOrigin mode policyRoot policyFrame executedFrame
      (.stmt (.cond condition body)) executedCode) :
    PolicyExecOrigin mode policyRoot policyFrame executedFrame
      (.expr condition) (execCode mode (.expr condition)) := by
  exact {
    executedFrame_eq := horigin.executedFrame_eq
    executedCode_eq := rfl
    policyFrame_mem := horigin.policyFrame_mem
    callOrigin := horigin.callOrigin.condExpr
    frameOrigin := CodeFramesOrigin.expr _ _
    bindingOrigin := BindingOrigin.expr _ _ _ _ }

theorem PolicyExecOrigin.exprChild {mode : OriginMode} {policyRoot : Block Op}
    {policyFrame executedFrame : Frame} {parentPolicy parentExecuted : Code Op}
    {expression : Expr Op}
    (horigin : PolicyExecOrigin mode policyRoot policyFrame executedFrame
      parentPolicy parentExecuted)
    (hcalls : CodeOrigin policyFrame (.expr expression)) :
    PolicyExecOrigin mode policyRoot policyFrame executedFrame
      (.expr expression) (execCode mode (.expr expression)) := by
  exact {
    executedFrame_eq := horigin.executedFrame_eq
    executedCode_eq := rfl
    policyFrame_mem := horigin.policyFrame_mem
    callOrigin := hcalls
    frameOrigin := CodeFramesOrigin.expr _ _
    bindingOrigin := BindingOrigin.expr _ _ _ _ }

theorem PolicyExecOrigin.argsChild {mode : OriginMode} {policyRoot : Block Op}
    {policyFrame executedFrame : Frame} {parentPolicy parentExecuted : Code Op}
    {args : List (Expr Op)}
    (horigin : PolicyExecOrigin mode policyRoot policyFrame executedFrame
      parentPolicy parentExecuted)
    (hcalls : CodeOrigin policyFrame (.args args)) :
    PolicyExecOrigin mode policyRoot policyFrame executedFrame
      (.args args) (execCode mode (.args args)) := by
  exact {
    executedFrame_eq := horigin.executedFrame_eq
    executedCode_eq := rfl
    policyFrame_mem := horigin.policyFrame_mem
    callOrigin := hcalls
    frameOrigin := CodeFramesOrigin.args _ _
    bindingOrigin := BindingOrigin.args _ _ _ _ }

theorem ControlMotiveContext.exprChild {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {parentPolicy parentExecuted : Code Op} {expression : Expr Op}
    {source : WordEnv}
    (hctx : ControlMotiveContext mode policyRoot selected policyFrame
      executedFrame live parentPolicy parentExecuted source)
    (hcalls : CodeOrigin policyFrame (.expr expression)) :
    ControlMotiveContext mode policyRoot selected policyFrame executedFrame live
      (.expr expression) (execCode mode (.expr expression)) source := by
  exact {
    origin := hctx.origin.exprChild hcalls
    trace := trivial
    envDeclared := hctx.envDeclared }

theorem ControlMotiveContext.argsChild {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {parentPolicy parentExecuted : Code Op} {args : List (Expr Op)}
    {source : WordEnv}
    (hctx : ControlMotiveContext mode policyRoot selected policyFrame
      executedFrame live parentPolicy parentExecuted source)
    (hcalls : CodeOrigin policyFrame (.args args)) :
    ControlMotiveContext mode policyRoot selected policyFrame executedFrame live
      (.args args) (execCode mode (.args args)) source := by
  exact {
    origin := hctx.origin.argsChild hcalls
    trace := trivial
    envDeclared := hctx.envDeclared }

theorem PolicyExecOrigin.condBody {mode : OriginMode} {policyRoot : Block Op}
    {policyFrame executedFrame : Frame} {condition : Expr Op}
    {body : Block Op} {executedCode : Code Op}
    (horigin : PolicyExecOrigin mode policyRoot policyFrame executedFrame
      (.stmt (.cond condition body)) executedCode) :
    PolicyExecOrigin mode policyRoot policyFrame executedFrame
      (.stmts body) (execCode mode (.stmts body)) := by
  exact {
    executedFrame_eq := horigin.executedFrame_eq
    executedCode_eq := rfl
    policyFrame_mem := horigin.policyFrame_mem
    callOrigin := horigin.callOrigin.condBody
    frameOrigin := horigin.frameOrigin.condBody
    bindingOrigin := horigin.bindingOrigin.condBody }

theorem ControlMotiveContext.condExpr {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {condition : Expr Op} {body : Block Op} {executedCode : Code Op}
    {source : WordEnv}
    (hctx : ControlMotiveContext mode policyRoot selected policyFrame
      executedFrame live (.stmt (.cond condition body)) executedCode source) :
    ControlMotiveContext mode policyRoot selected policyFrame executedFrame live
      (.expr condition) (execCode mode (.expr condition)) source := by
  exact {
    origin := hctx.origin.condExpr
    trace := trivial
    envDeclared := hctx.envDeclared }

theorem ControlMotiveContext.condBody {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {condition : Expr Op} {body : Block Op} {executedCode : Code Op}
    {source : WordEnv}
    (hctx : ControlMotiveContext mode policyRoot selected policyFrame
      executedFrame live (.stmt (.cond condition body)) executedCode source) :
    ControlMotiveContext mode policyRoot selected policyFrame executedFrame live
      (.stmts body) (execCode mode (.stmts body)) source := by
  exact {
    origin := hctx.origin.condBody
    trace := traceCovered_cond hctx.trace
    envDeclared := hctx.envDeclared }

/-! Dynamic-context descendants used directly by the structural `Step`
induction.  Bounds/origin for a post-step environment are explicit arguments;
the static exit-signature inclusion is inherited unchanged. -/

theorem ControlStepContext.rootInitial {raw : Block Op} {result : Result}
    {guards : List Nat} (hfacts : SpillFacts raw result guards)
    (mode : OriginMode) :
    let policyRoot := resolveMemoryGuardStmts result.base result.reserved raw
    let policyFrame : Frame :=
      { owner := none, params := [], returns := [], body := policyRoot }
    ControlStepContext mode policyRoot result.selection policyFrame
      (mode.execFrame policyFrame)
      (frameInitialLive result.selection policyFrame)
      (.stmts policyRoot) (execCode mode (.stmts policyRoot)) [] [] := by
  dsimp only
  exact {
    motive := ControlMotiveContext.rootInitial mode
    selectedBindingsWF := hfacts.selected_bindings_wf
    selectedBindingsOK := by
      simpa only [selectedBindingsCodeOK] using
        selectedBindingsWF_of_mem hfacts.selected_bindings_wf (frame :=
          { owner := none, params := [], returns := [], body :=
              resolveMemoryGuardStmts result.base result.reserved raw }) (by
            simp [frames])
    letAfterCertified := trivial
    exitsBound := by simp [NamesBound]
    exitsInSignature := by simp
    exitsNodup := by simp }

theorem ControlStepContext.stmtsHead {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {statement : Stmt Op} {rest : Block Op} {executedCode : Code Op}
    {exitNames : List Ident} {source : WordEnv}
    (hctx : ControlStepContext mode policyRoot selected policyFrame executedFrame
      live (.stmts (statement :: rest)) executedCode exitNames source) :
    ControlStepContext mode policyRoot selected policyFrame executedFrame live
      (.stmt statement) (execCode mode (.stmt statement)) exitNames source := by
  exact {
    motive := hctx.motive.stmtsHead
    selectedBindingsWF := hctx.selectedBindingsWF
    selectedBindingsOK := by
      have hparts :
          selectedBindingsStmtOK selected policyFrame live statement = true ∧
            selectedBindingsStmtsOK selected policyFrame
              (liveStmt selected policyFrame.owner live statement).2 rest = true := by
        simpa only [selectedBindingsCodeOK, selectedBindingsStmtsOK,
          Bool.and_eq_true] using hctx.selectedBindingsOK
      exact hparts.1
    letAfterCertified := by
      cases statement <;> simp only [LetAfterCertified]
      exact hctx.motive.trace.tail.liveCertified
    exitsBound := hctx.exitsBound
    exitsInSignature := hctx.exitsInSignature
    exitsNodup := hctx.exitsNodup }

theorem ControlStepContext.stmtsTail {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {statement : Stmt Op} {rest : Block Op} {executedCode : Code Op}
    {exitNames : List Ident} {source nextSource : WordEnv}
    (hctx : ControlStepContext mode policyRoot selected policyFrame executedFrame
      live (.stmts (statement :: rest)) executedCode exitNames source)
    (henv : EnvDeclaredOrigin (MemorySpill.declaredStmts policyRoot) nextSource)
    (hbound : NamesBound exitNames nextSource) :
    ControlStepContext mode policyRoot selected policyFrame executedFrame
      (liveStmt selected policyFrame.owner live statement).2
      (.stmts rest) (execCode mode (.stmts rest)) exitNames nextSource := by
  exact {
    motive := {
      origin := hctx.motive.origin.stmtsTail
      trace := hctx.motive.trace.tail
      envDeclared := henv }
    selectedBindingsWF := hctx.selectedBindingsWF
    selectedBindingsOK := by
      have hparts :
          selectedBindingsStmtOK selected policyFrame live statement = true ∧
            selectedBindingsStmtsOK selected policyFrame
              (liveStmt selected policyFrame.owner live statement).2 rest = true := by
        simpa only [selectedBindingsCodeOK, selectedBindingsStmtsOK,
          Bool.and_eq_true] using hctx.selectedBindingsOK
      exact hparts.2
    letAfterCertified := trivial
    exitsBound := hbound
    exitsInSignature := hctx.exitsInSignature
    exitsNodup := hctx.exitsNodup }

theorem ControlStepContext.blockBody {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet} {body : Block Op}
    {executedCode : Code Op} {exitNames : List Ident} {source : WordEnv}
    (hctx : ControlStepContext mode policyRoot selected policyFrame executedFrame
      live (.stmt (.block body)) executedCode exitNames source) :
    ControlStepContext mode policyRoot selected policyFrame executedFrame live
      (.stmts body) (execCode mode (.stmts body)) exitNames source := by
  exact {
    motive := hctx.motive.blockBody
    selectedBindingsWF := hctx.selectedBindingsWF
    selectedBindingsOK := by
      simpa only [selectedBindingsCodeOK, selectedBindingsStmtOK] using
        hctx.selectedBindingsOK
    letAfterCertified := trivial
    exitsBound := hctx.exitsBound
    exitsInSignature := hctx.exitsInSignature
    exitsNodup := hctx.exitsNodup }

theorem ControlStepContext.condExpr {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {condition : Expr Op} {body : Block Op} {executedCode : Code Op}
    {exitNames : List Ident} {source : WordEnv}
    (hctx : ControlStepContext mode policyRoot selected policyFrame executedFrame
      live (.stmt (.cond condition body)) executedCode exitNames source) :
    ControlStepContext mode policyRoot selected policyFrame executedFrame live
      (.expr condition) (execCode mode (.expr condition)) exitNames source := by
  exact {
    motive := hctx.motive.condExpr
    selectedBindingsWF := hctx.selectedBindingsWF
    selectedBindingsOK := rfl
    letAfterCertified := trivial
    exitsBound := hctx.exitsBound
    exitsInSignature := hctx.exitsInSignature
    exitsNodup := hctx.exitsNodup }

theorem ControlStepContext.condBody {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {condition : Expr Op} {body : Block Op} {executedCode : Code Op}
    {exitNames : List Ident} {source : WordEnv}
    (hctx : ControlStepContext mode policyRoot selected policyFrame executedFrame
      live (.stmt (.cond condition body)) executedCode exitNames source) :
    ControlStepContext mode policyRoot selected policyFrame executedFrame live
      (.stmts body) (execCode mode (.stmts body)) exitNames source := by
  exact {
    motive := hctx.motive.condBody
    selectedBindingsWF := hctx.selectedBindingsWF
    selectedBindingsOK := by
      simpa only [selectedBindingsCodeOK, selectedBindingsStmtOK] using
        hctx.selectedBindingsOK
    letAfterCertified := trivial
    exitsBound := hctx.exitsBound
    exitsInSignature := hctx.exitsInSignature
    exitsNodup := hctx.exitsNodup }

theorem resolve_selectSwitch_guarded (layout : YulSemantics.EVM.Layout)
    (value : U256) (cases : List (Literal × Block Op))
    (fallback : Option (Block Op)) :
    resolveForLayoutStmts layout (selectSwitch G value cases fallback) =
      selectSwitch G value (resolveForLayoutCases layout cases)
        (fallback.map (resolveForLayoutStmts layout)) := by
  induction cases with
  | nil => cases fallback <;> simp [selectSwitch, resolveForLayoutCases]
  | cons head rest ih =>
      obtain ⟨literal, body⟩ := head
      by_cases h : decide (value = Dialect.litValue G literal) = true
      · simp [selectSwitch, resolveForLayoutCases, h]
      · simpa [selectSwitch, resolveForLayoutCases, h] using ih

theorem ControlStepContext.switchSelection_eq {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {policyCondition executedCondition : Expr Op}
    {policyCases executedCases : List (Literal × Block Op)}
    {policyFallback executedFallback : Option (Block Op)}
    {exitNames : List Ident} {source : WordEnv}
    (hctx : ControlStepContext mode policyRoot selected policyFrame executedFrame
      live (.stmt (.switch policyCondition policyCases policyFallback))
      (.stmt (.switch executedCondition executedCases executedFallback))
      exitNames source) (value : U256) :
    selectSwitch G value executedCases executedFallback =
      mode.execBlock (selectSwitch G value policyCases policyFallback) := by
  have heq := hctx.motive.origin.executedCode_eq
  cases mode with
  | identity =>
      simp only [execCode] at heq
      injection heq with hstmt
      injection hstmt with _ hcases hfallback
      subst executedCases
      subst executedFallback
      rfl
  | «object» layout =>
      simp only [execCode, resolveForLayoutCode_stmt,
        resolveForLayoutStmt_switch] at heq
      injection heq with hstmt
      injection hstmt with _ hcases hfallback
      subst executedCases
      subst executedFallback
      exact (resolve_selectSwitch_guarded layout value policyCases
        policyFallback).symm

private theorem blockStmtOfStmts {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {policyBody executedBody : Block Op} {exitNames : List Ident}
    {source : WordEnv}
    (hctx : ControlStepContext mode policyRoot selected policyFrame executedFrame
      live (.stmts policyBody) (.stmts executedBody) exitNames source) :
    ControlStepContext mode policyRoot selected policyFrame executedFrame live
      (.stmt (.block policyBody)) (.stmt (.block executedBody))
      exitNames source := by
  exact {
    motive := {
      origin := {
        executedFrame_eq := hctx.motive.origin.executedFrame_eq
        executedCode_eq := by
          have h := hctx.motive.origin.executedCode_eq
          cases mode <;> simpa [execCode, resolveForLayoutCode_stmt,
            resolveForLayoutStmt_block] using h
        policyFrame_mem := hctx.motive.origin.policyFrame_mem
        callOrigin := by
          simpa [CodeOrigin, codeCalls, frameCallsStmt] using
            hctx.motive.origin.callOrigin
        frameOrigin := by
          simpa [CodeFramesOrigin, codeNestedFrames, nestedFramesStmt] using
            hctx.motive.origin.frameOrigin
        bindingOrigin := {
          groups := fun group hgroup =>
            hctx.motive.origin.bindingOrigin.groups group (by
              simpa [codeGroups, coupledStmt] using hgroup)
          declared := fun name hname =>
            hctx.motive.origin.bindingOrigin.declared name (by
              simpa [codeDeclared, MemorySpill.declaredStmt] using hname) } }
      trace := by
        simpa [CodeTraceCovered, TraceCovered, liveStmt, liveScope] using
          hctx.motive.trace
      envDeclared := hctx.motive.envDeclared }
    selectedBindingsWF := hctx.selectedBindingsWF
    selectedBindingsOK := by
      simpa only [selectedBindingsCodeOK, selectedBindingsStmtOK] using
        hctx.selectedBindingsOK
    letAfterCertified := trivial
    exitsBound := hctx.exitsBound
    exitsInSignature := hctx.exitsInSignature
    exitsNodup := hctx.exitsNodup }

theorem ControlStepContext.switchCaseBlock {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {policyCondition executedCondition : Expr Op}
    {policyCases executedCases : List (Literal × Block Op)}
    {policyFallback executedFallback : Option (Block Op)}
    {literal : Literal} {policyBody executedBody : Block Op}
    {exitNames : List Ident} {source : WordEnv}
    (hctx : ControlStepContext mode policyRoot selected policyFrame executedFrame
      live (.stmt (.switch policyCondition policyCases policyFallback))
      (.stmt (.switch executedCondition executedCases executedFallback))
      exitNames source)
    (hcase : (literal, policyBody) ∈ policyCases)
    (hbody : executedBody = mode.execBlock policyBody) :
    ControlStepContext mode policyRoot selected policyFrame executedFrame live
      (.stmt (.block policyBody)) (.stmt (.block executedBody))
      exitNames source := by
  have hstmts : ControlStepContext mode policyRoot selected policyFrame
      executedFrame live (.stmts policyBody) (.stmts executedBody)
      exitNames source := {
    motive := {
      origin := {
        executedFrame_eq := hctx.motive.origin.executedFrame_eq
        executedCode_eq := by
          cases mode <;> simpa [execCode, OriginMode.execBlock] using
            congrArg Code.stmts hbody
        policyFrame_mem := hctx.motive.origin.policyFrame_mem
        callOrigin := hctx.motive.origin.callOrigin.switchCase hcase
        frameOrigin := hctx.motive.origin.frameOrigin.switchCase hcase
        bindingOrigin := hctx.motive.origin.bindingOrigin.switchCase hcase }
      trace := traceCovered_switchCase hctx.motive.trace hcase
      envDeclared := hctx.motive.envDeclared }
    selectedBindingsWF := hctx.selectedBindingsWF
    selectedBindingsOK := by
      apply selectedBindingsSwitchCase_of_ok (hmem := hcase)
      simpa only [selectedBindingsCodeOK] using hctx.selectedBindingsOK
    letAfterCertified := trivial
    exitsBound := hctx.exitsBound
    exitsInSignature := hctx.exitsInSignature
    exitsNodup := hctx.exitsNodup }
  exact blockStmtOfStmts hstmts

theorem ControlStepContext.switchDefaultBlock {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {policyCondition executedCondition : Expr Op}
    {policyCases executedCases : List (Literal × Block Op)}
    {policyBody executedBody : Block Op}
    {executedFallback : Option (Block Op)}
    {exitNames : List Ident} {source : WordEnv}
    (hctx : ControlStepContext mode policyRoot selected policyFrame executedFrame
      live (.stmt (.switch policyCondition policyCases (some policyBody)))
      (.stmt (.switch executedCondition executedCases executedFallback))
      exitNames source)
    (hbody : executedBody = mode.execBlock policyBody) :
    ControlStepContext mode policyRoot selected policyFrame executedFrame live
      (.stmt (.block policyBody)) (.stmt (.block executedBody))
      exitNames source := by
  have hstmts : ControlStepContext mode policyRoot selected policyFrame
      executedFrame live (.stmts policyBody) (.stmts executedBody)
      exitNames source := {
    motive := {
      origin := {
        executedFrame_eq := hctx.motive.origin.executedFrame_eq
        executedCode_eq := by
          cases mode <;> simpa [execCode, OriginMode.execBlock] using
            congrArg Code.stmts hbody
        policyFrame_mem := hctx.motive.origin.policyFrame_mem
        callOrigin := hctx.motive.origin.callOrigin.switchDefault
        frameOrigin := hctx.motive.origin.frameOrigin.switchDefault
        bindingOrigin := hctx.motive.origin.bindingOrigin.switchDefault }
      trace := traceCovered_switchDefault hctx.motive.trace
      envDeclared := hctx.motive.envDeclared }
    selectedBindingsWF := hctx.selectedBindingsWF
    selectedBindingsOK := by
      have hparts := hctx.selectedBindingsOK
      simp only [selectedBindingsCodeOK, selectedBindingsStmtOK,
        Bool.and_eq_true] at hparts
      exact hparts.2
    letAfterCertified := trivial
    exitsBound := hctx.exitsBound
    exitsInSignature := hctx.exitsInSignature
    exitsNodup := hctx.exitsNodup }
  exact blockStmtOfStmts hstmts

theorem selectSwitch_empty_or_origin (value : U256)
    (cases : List (Literal × Block Op)) (fallback : Option (Block Op)) :
    selectSwitch G value cases fallback = [] ∨
      (∃ literal body, (literal, body) ∈ cases ∧
        selectSwitch G value cases fallback = body) ∨
      (∃ body, fallback = some body ∧
        selectSwitch G value cases fallback = body) := by
  unfold selectSwitch
  cases hfind : cases.find?
      (fun item => decide (value = Dialect.litValue G item.1)) with
  | some item =>
      obtain ⟨literal, body⟩ := item
      by_cases hempty : body = []
      · exact Or.inl (by simpa [hfind] using hempty)
      · exact Or.inr (Or.inl ⟨literal, body,
          List.mem_of_find?_eq_some hfind, rfl⟩)
  | none =>
      cases fallback with
      | none => exact Or.inl rfl
      | some body =>
          by_cases hempty : body = []
          · exact Or.inl (by simpa [hfind] using hempty)
          · exact Or.inr (Or.inr ⟨body, rfl, rfl⟩)

/-- Select the policy/runtime switch body.  A no-case/no-default selection is
reported explicitly because the empty block has no statement-trace entry and
is closed directly by the capstone; every nonempty selection returns the exact
block-statement context for its body induction hypothesis. -/
theorem ControlStepContext.switchSelectedBlock {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {policyCondition executedCondition : Expr Op}
    {policyCases executedCases : List (Literal × Block Op)}
    {policyFallback executedFallback : Option (Block Op)}
    {exitNames : List Ident} {source : WordEnv}
    (hctx : ControlStepContext mode policyRoot selected policyFrame executedFrame
      live (.stmt (.switch policyCondition policyCases policyFallback))
      (.stmt (.switch executedCondition executedCases executedFallback))
      exitNames source) (value : U256) :
    let policyBody := selectSwitch G value policyCases policyFallback
    let executedBody := selectSwitch G value executedCases executedFallback
    (policyBody = [] ∧ executedBody = []) ∨
      ControlStepContext mode policyRoot selected policyFrame executedFrame live
        (.stmt (.block policyBody)) (.stmt (.block executedBody))
        exitNames source := by
  dsimp only
  have hexecuted := ControlStepContext.switchSelection_eq
    (base := base) (reserved := reserved) (calls := calls) (creates := creates)
    hctx value
  rcases selectSwitch_empty_or_origin (calls := calls) (creates := creates)
      (base := base) (reserved := reserved) value policyCases policyFallback with
    hempty | hnonempty
  · apply Or.inl
    constructor
    · exact hempty
    · rw [hexecuted, hempty]
      cases mode <;> simp [OriginMode.execBlock]
  · apply Or.inr
    rcases hnonempty with hcase | hdefault
    · obtain ⟨literal, body, hmem, hselected⟩ := hcase
      have hbody : selectSwitch G value executedCases executedFallback =
          mode.execBlock body := by simpa [hselected] using hexecuted
      simpa [hselected] using hctx.switchCaseBlock hmem hbody
    · obtain ⟨body, hfallback, hselected⟩ := hdefault
      subst policyFallback
      have hbody : selectSwitch G value executedCases executedFallback =
          mode.execBlock body := by simpa [hselected] using hexecuted
      simpa [hselected] using hctx.switchDefaultBlock hbody

theorem ControlStepContext.exprChild {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {parentPolicy parentExecuted : Code Op} {expression : Expr Op}
    {exitNames : List Ident} {source childSource : WordEnv}
    (hctx : ControlStepContext mode policyRoot selected policyFrame executedFrame
      live parentPolicy parentExecuted exitNames source)
    (hcalls : CodeOrigin policyFrame (.expr expression))
    (henv : EnvDeclaredOrigin (MemorySpill.declaredStmts policyRoot) childSource)
    (hbound : NamesBound exitNames childSource) :
    ControlStepContext mode policyRoot selected policyFrame executedFrame live
      (.expr expression) (execCode mode (.expr expression)) exitNames childSource := by
  exact hctx.child hcalls (CodeFramesOrigin.expr _ _)
    (BindingOrigin.expr _ _ _ _) trivial rfl trivial henv hbound

theorem ControlStepContext.argsChild {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {parentPolicy parentExecuted : Code Op} {args : List (Expr Op)}
    {exitNames : List Ident} {source childSource : WordEnv}
    (hctx : ControlStepContext mode policyRoot selected policyFrame executedFrame
      live parentPolicy parentExecuted exitNames source)
    (hcalls : CodeOrigin policyFrame (.args args))
    (henv : EnvDeclaredOrigin (MemorySpill.declaredStmts policyRoot) childSource)
    (hbound : NamesBound exitNames childSource) :
    ControlStepContext mode policyRoot selected policyFrame executedFrame live
      (.args args) (execCode mode (.args args)) exitNames childSource := by
  exact hctx.child hcalls (CodeFramesOrigin.args _ _)
    (BindingOrigin.args _ _ _ _) trivial rfl trivial henv hbound

theorem CodeFramesOrigin.loopPost_local {allFrames : List Frame}
    {condition : Expr Op} {post body : Block Op}
    (horigin : CodeFramesOrigin allFrames (.loop condition post body)) :
    CodeFramesOrigin allFrames (.stmts post) := by
  intro frame hframe
  apply horigin frame
  exact List.mem_append_left _ hframe

theorem CodeFramesOrigin.loopBody_local {allFrames : List Frame}
    {condition : Expr Op} {post body : Block Op}
    (horigin : CodeFramesOrigin allFrames (.loop condition post body)) :
    CodeFramesOrigin allFrames (.stmts body) := by
  intro frame hframe
  apply horigin frame
  exact List.mem_append_right _ hframe

theorem CodeFramesOrigin.forInit_local {allFrames : List Frame}
    {init post body : Block Op} {condition : Expr Op}
    (horigin : CodeFramesOrigin allFrames
      (.stmt (.forLoop init condition post body))) :
    CodeFramesOrigin allFrames (.stmts init) := by
  intro frame hframe
  apply horigin frame
  simp only [codeNestedFrames, nestedFramesStmt]
  exact List.mem_append_left _ (List.mem_append_left _ hframe)

theorem CodeOrigin.forLoop_local {frame : Frame} {init post body : Block Op}
    {condition : Expr Op}
    (horigin : CodeOrigin frame (.stmt (.forLoop init condition post body))) :
    CodeOrigin frame (.loop condition post body) := by
  intro name hname
  apply horigin name
  simpa [codeCalls, frameCallsStmt] using Or.inr hname

theorem CodeFramesOrigin.forLoop_local {allFrames : List Frame}
    {init post body : Block Op} {condition : Expr Op}
    (horigin : CodeFramesOrigin allFrames
      (.stmt (.forLoop init condition post body))) :
    CodeFramesOrigin allFrames (.loop condition post body) := by
  intro frame hframe
  apply horigin frame
  simp only [codeNestedFrames, nestedFramesStmt] at hframe ⊢
  simpa [List.append_assoc] using
    List.mem_append_right (nestedFramesStmts init) hframe

theorem BindingOrigin.forLoop_local {globalGroups : List (List SpillKey)}
    {globalDeclared : List Ident} {owner : Owner}
    {init post body : Block Op} {condition : Expr Op}
    (horigin : BindingOrigin globalGroups globalDeclared owner
      (.stmt (.forLoop init condition post body))) :
    BindingOrigin globalGroups globalDeclared owner
      (.loop condition post body) := by
  constructor
  · intro group hgroup
    apply horigin.groups group
    simp only [codeGroups, coupledStmt] at hgroup ⊢
    simpa [List.append_assoc] using
      List.mem_append_right (coupledStmts owner init) hgroup
  · intro name hname
    apply horigin.declared name
    simp only [codeDeclared, MemorySpill.declaredStmt] at hname ⊢
    simpa [List.append_assoc] using
      List.mem_append_right (MemorySpill.declaredStmts init) hname

/-- Checked loop descendants.  These adapters keep the executable binding
gate syntax-directed instead of exposing Boolean bookkeeping at induction
call sites. -/
theorem ControlStepContext.forInit {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {init post body : Block Op} {condition : Expr Op}
    {executedCode : Code Op} {exitNames : List Ident} {source : WordEnv}
    (hctx : ControlStepContext mode policyRoot selected policyFrame executedFrame
      live (.stmt (.forLoop init condition post body)) executedCode
      exitNames source) :
    ControlStepContext mode policyRoot selected policyFrame executedFrame live
      (.stmts init) (execCode mode (.stmts init)) exitNames source := by
  apply hctx.child hctx.motive.origin.callOrigin.forInit
    (CodeFramesOrigin.forInit_local hctx.motive.origin.frameOrigin)
    hctx.motive.origin.bindingOrigin.forInit
    (traceCovered_forInit hctx.motive.trace)
  · have hok := hctx.selectedBindingsOK
    simp only [selectedBindingsCodeOK, selectedBindingsStmtOK,
      Bool.and_eq_true] at hok
    simpa only [selectedBindingsCodeOK] using hok.1.1
  · trivial
  · exact hctx.motive.envDeclared
  · exact hctx.exitsBound

theorem ControlStepContext.forLoop {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {init post body : Block Op} {condition : Expr Op}
    {executedCode : Code Op} {exitNames : List Ident}
    {source childSource : WordEnv}
    (hctx : ControlStepContext mode policyRoot selected policyFrame executedFrame
      live (.stmt (.forLoop init condition post body)) executedCode
      exitNames source)
    (henv : EnvDeclaredOrigin (MemorySpill.declaredStmts policyRoot) childSource)
    (hbound : NamesBound exitNames childSource) :
    ControlStepContext mode policyRoot selected policyFrame executedFrame
      (liveStmts selected policyFrame.owner live init).2
      (.loop condition post body) (execCode mode (.loop condition post body))
      exitNames childSource := by
  apply hctx.child hctx.motive.origin.callOrigin.forLoop_local
    (CodeFramesOrigin.forLoop_local hctx.motive.origin.frameOrigin)
    hctx.motive.origin.bindingOrigin.forLoop_local
  · exact ⟨traceCovered_forPost hctx.motive.trace,
      traceCovered_forBody hctx.motive.trace⟩
  · have hok := hctx.selectedBindingsOK
    simp only [selectedBindingsCodeOK, selectedBindingsStmtOK,
      Bool.and_eq_true] at hok
    simpa only [selectedBindingsCodeOK, Bool.and_eq_true] using
      And.intro hok.1.2 hok.2
  · trivial
  · exact henv
  · exact hbound

theorem ControlStepContext.loopBody {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {condition : Expr Op} {post body : Block Op} {executedCode : Code Op}
    {exitNames : List Ident} {source childSource : WordEnv}
    (hctx : ControlStepContext mode policyRoot selected policyFrame executedFrame
      live (.loop condition post body) executedCode exitNames source)
    (henv : EnvDeclaredOrigin (MemorySpill.declaredStmts policyRoot) childSource)
    (hbound : NamesBound exitNames childSource) :
    ControlStepContext mode policyRoot selected policyFrame executedFrame live
      (.stmts body) (execCode mode (.stmts body)) exitNames childSource := by
  apply hctx.child hctx.motive.origin.callOrigin.loopBody
    (CodeFramesOrigin.loopBody_local hctx.motive.origin.frameOrigin)
    hctx.motive.origin.bindingOrigin.loopBody hctx.motive.trace.2
  · have hok := hctx.selectedBindingsOK
    simp only [selectedBindingsCodeOK, Bool.and_eq_true] at hok
    exact hok.2
  · trivial
  · exact henv
  · exact hbound

theorem ControlStepContext.loopPost {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {condition : Expr Op} {post body : Block Op} {executedCode : Code Op}
    {exitNames : List Ident} {source childSource : WordEnv}
    (hctx : ControlStepContext mode policyRoot selected policyFrame executedFrame
      live (.loop condition post body) executedCode exitNames source)
    (henv : EnvDeclaredOrigin (MemorySpill.declaredStmts policyRoot) childSource)
    (hbound : NamesBound exitNames childSource) :
    ControlStepContext mode policyRoot selected policyFrame executedFrame live
      (.stmts post) (execCode mode (.stmts post)) exitNames childSource := by
  apply hctx.child hctx.motive.origin.callOrigin.loopPost
    (CodeFramesOrigin.loopPost_local hctx.motive.origin.frameOrigin)
    hctx.motive.origin.bindingOrigin.loopPost hctx.motive.trace.1
  · have hok := hctx.selectedBindingsOK
    simp only [selectedBindingsCodeOK, Bool.and_eq_true] at hok
    exact hok.1
  · trivial
  · exact henv
  · exact hbound

theorem ControlStepContext.loopAgain {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {condition : Expr Op} {post body : Block Op} {executedCode : Code Op}
    {exitNames : List Ident} {source childSource : WordEnv}
    (hctx : ControlStepContext mode policyRoot selected policyFrame executedFrame
      live (.loop condition post body) executedCode exitNames source)
    (henv : EnvDeclaredOrigin (MemorySpill.declaredStmts policyRoot) childSource)
    (hbound : NamesBound exitNames childSource) :
    ControlStepContext mode policyRoot selected policyFrame executedFrame live
      (.loop condition post body) (execCode mode (.loop condition post body))
      exitNames childSource := by
  exact hctx.child hctx.motive.origin.callOrigin hctx.motive.origin.frameOrigin
    hctx.motive.origin.bindingOrigin hctx.motive.trace hctx.selectedBindingsOK
    trivial henv hbound

/-- Repackage a statement-sequence context as the block statement that
executes that sequence.  This is the exact code shape used by `Step.block`
premises in calls, conditionals, switches, and loops. -/
theorem ControlStepContext.asBlockStmt {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {policyBody executedBody : Block Op} {exitNames : List Ident}
    {source : WordEnv}
    (hctx : ControlStepContext mode policyRoot selected policyFrame executedFrame
      live (.stmts policyBody) (.stmts executedBody) exitNames source) :
    ControlStepContext mode policyRoot selected policyFrame executedFrame live
      (.stmt (.block policyBody)) (.stmt (.block executedBody))
      exitNames source := by
  exact {
    motive := {
      origin := {
        executedFrame_eq := hctx.motive.origin.executedFrame_eq
        executedCode_eq := by
          have h := hctx.motive.origin.executedCode_eq
          cases mode <;> simpa [execCode, resolveForLayoutCode_stmt,
            resolveForLayoutStmt_block] using h
        policyFrame_mem := hctx.motive.origin.policyFrame_mem
        callOrigin := by
          simpa [CodeOrigin, codeCalls, frameCallsStmt] using
            hctx.motive.origin.callOrigin
        frameOrigin := by
          simpa [CodeFramesOrigin, codeNestedFrames, nestedFramesStmt] using
            hctx.motive.origin.frameOrigin
        bindingOrigin := {
          groups := fun group hgroup =>
            hctx.motive.origin.bindingOrigin.groups group (by
              simpa [codeGroups, coupledStmt] using hgroup)
          declared := fun name hname =>
            hctx.motive.origin.bindingOrigin.declared name (by
              simpa [codeDeclared, MemorySpill.declaredStmt] using hname) } }
      trace := by
        simpa [CodeTraceCovered, TraceCovered, liveStmt, liveScope] using
          hctx.motive.trace
      envDeclared := hctx.motive.envDeclared }
    selectedBindingsWF := hctx.selectedBindingsWF
    selectedBindingsOK := by
      simpa only [selectedBindingsCodeOK, selectedBindingsStmtOK] using
        hctx.selectedBindingsOK
    letAfterCertified := trivial
    exitsBound := hctx.exitsBound
    exitsInSignature := hctx.exitsInSignature
    exitsNodup := hctx.exitsNodup }

/-- Call lookup specialized to the block-statement judgment appearing as the
actual body premise of `Step.callOk` and `Step.callHalt`. -/
theorem ControlStepContext.calleeBlock {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {sourceFuns : FunEnv G} {name : Ident} {decl : FDecl G}
    {closure : FunEnv G} {argvals : List U256}
    (hbindingsWF : MemorySpillSelect.selectedBindingsWF selected
      (frames policyRoot) = true)
    (hcovered : FunsCovered G (fun body => body)
      ((frames policyRoot).map mode.execFrame) sourceFuns)
    (hlookup : lookupFun sourceFuns name = some (decl, closure))
    (hlength : argvals.length = decl.params.length)
    (hnodup : (decl.params ++ decl.rets).Nodup) :
    ∃ policyCallee,
      policyCallee ∈ frames policyRoot ∧
      mode.execFrame policyCallee = calleeFrame name decl ∧
      FunsCovered G (fun body => body)
        ((frames policyRoot).map mode.execFrame) closure ∧
      ControlStepContext mode policyRoot selected policyCallee
        (calleeFrame name decl) (frameInitialLive selected policyCallee)
        (.stmt (.block policyCallee.body)) (.stmt (.block decl.body)) decl.rets
        (callEnv decl.params decl.rets argvals) := by
  obtain ⟨policyCallee, hmem, hframe, hclosure, hctx⟩ :=
    ControlStepContext.calleeBody (selected := selected)
      hbindingsWF hcovered hlookup hlength hnodup
  exact ⟨policyCallee, hmem, hframe, hclosure, hctx.asBlockStmt⟩

/-- Lift the syntax-local guarded hoist certificate into the object-wide
frame list used by allocation.  A directly hoisted function cannot be the
synthetic `none`-owned root of `frames body`, so its witness is necessarily a
nested frame and is transported by `CodeFramesOrigin`. -/
theorem guardedScopeCovered_global {allFrames : List Frame} {body : Block Op}
    (horigin : CodeFramesOrigin allFrames (.stmts body)) :
    ScopeCovered G (fun executed => executed) allFrames (hoist G body) := by
  intro name decl hdecl
  obtain ⟨frame, hframe, howner, hparams, hreturns, hbody⟩ :=
    guardedScopeCovered calls creates base reserved body name decl hdecl
  have hnested : frame ∈ nestedFramesStmts body := by
    simp only [frames, List.mem_cons] at hframe
    rcases hframe with hroot | hnested
    · subst frame
      simp at howner
    · exact hnested
  exact ⟨frame, horigin frame hnested, howner, hparams, hreturns, hbody⟩

theorem FunsCovered.pushHoist {allFrames : List Frame} {body : Block Op}
    {funs : FunEnv G}
    (hfuns : FunsCovered G (fun executed => executed) allFrames funs)
    (horigin : CodeFramesOrigin allFrames (.stmts body)) :
    FunsCovered G (fun executed => executed) allFrames (hoist G body :: funs) :=
  FunsCovered.cons (guardedScopeCovered_global horigin) hfuns

/-! ## Caller spill-cell preservation across a user call -/

/-- Memory equality above a cutoff preserves loaded cells whose complete word
starts at or above that cutoff. -/
theorem SlotsLoaded.preserveAbove {slots : SlotMap} {owner : Owner}
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

/-- Repackage a completed call back into the caller frame.  Callee simulation
supplies the new scratch relation; allocator separation plus
`AboveUnchanged` retains all caller spill cells. -/
theorem LiveFrameRel.afterCall {selected : SpillSet}
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
      loaded := SlotsLoaded.preserveAbove hrel.frameRel.loaded hslotCutoff
        hslotReserved habove
      scratch := hscratch }
    bound := hrel.bound
    certified := hrel.certified }

/-! ## Scope entry -/

def scopeMark (source target : WordEnv) : CutMark :=
  { sourceLen := source.length, targetLen := target.length }

/-- Runtime form of the static selected-name uniqueness check.  Only names
with spill slots matter: unselected shadowing is represented normally on both
sides and needs no special scope argument. -/
def SelectedUnique (slots : SlotMap) (owner : Owner) (source : WordEnv) : Prop :=
  ∀ name slot, slotFor? slots owner name = some slot →
    (source.map Prod.fst).count name ≤ 1

theorem SelectedUnique.empty (slots : SlotMap) (owner : Owner) :
    SelectedUnique slots owner [] := by
  intro name slot hslot
  simp

theorem SelectedUnique.ofNodupKeys {slots : SlotMap} {owner : Owner}
    {source : WordEnv} (hnodup : (source.map Prod.fst).Nodup) :
    SelectedUnique slots owner source := by
  intro name slot hslot
  exact (List.nodup_iff_count_le_one.mp hnodup) name

theorem SelectedUnique.set {slots : SlotMap} {owner : Owner}
    {source : WordEnv} (hunique : SelectedUnique slots owner source)
    (name : Ident) (value : U256) :
    SelectedUnique slots owner (envSet source name value) := by
  intro selectedName slot hslot
  rw [envSet_keys]
  exact hunique selectedName slot hslot

theorem SelectedUnique.restore {slots : SlotMap} {owner : Owner}
    {source outer : WordEnv} (hunique : SelectedUnique slots owner source) :
    SelectedUnique slots owner (@YulSemantics.restore G outer source) := by
  intro name slot hslot
  unfold YulSemantics.restore
  have hle := (List.drop_sublist (source.length - outer.length)
    (source.map Prod.fst)).count_le name
  rw [List.map_drop]
  exact le_trans hle (hunique name slot hslot)

theorem SelectedUnique.prependSelectedFresh {slots : SlotMap} {owner : Owner}
    {source : WordEnv} (hunique : SelectedUnique slots owner source)
    {name : Ident} {value : U256}
    (hfresh : name ∉ source.map Prod.fst) :
    SelectedUnique slots owner ((name, value) :: source) := by
  intro other slot hslot
  simp only [List.map_cons, List.count_cons]
  by_cases heq : name = other
  · subst other
    simp only [beq_self_eq_true, if_true]
    rw [List.count_eq_zero_of_not_mem hfresh]
  · have hbeq : (name == other) = false := by simpa using heq
    simp only [hbeq]
    exact hunique other slot hslot

theorem SelectedUnique.prependNoSlot {slots : SlotMap} {owner : Owner}
    {source : WordEnv} (hunique : SelectedUnique slots owner source)
    {name : Ident} {value : U256}
    (hnoSlot : slotFor? slots owner name = none) :
    SelectedUnique slots owner ((name, value) :: source) := by
  intro other slot hslot
  have hne : name ≠ other := by
    intro heq
    subst other
    rw [hnoSlot] at hslot
    contradiction
  simp only [List.map_cons, List.count_cons]
  have hbeq : (name == other) = false := by simpa using hne
  simp only [hbeq]
  exact hunique other slot hslot

theorem SelectedUnique.prependFreshList {slots : SlotMap} {owner : Owner}
    {source front : WordEnv} (hunique : SelectedUnique slots owner source)
    (hnodup : (front.map Prod.fst).Nodup)
    (hfresh : ∀ name ∈ front.map Prod.fst, name ∉ source.map Prod.fst) :
    SelectedUnique slots owner (front ++ source) := by
  intro name slot hslot
  simp only [List.map_append, List.count_append]
  by_cases hmem : name ∈ front.map Prod.fst
  · have hfront := (List.nodup_iff_count_le_one.mp hnodup) name
    have hfrontPos : 0 < (front.map Prod.fst).count name :=
      List.count_pos_iff.mpr hmem
    rw [List.count_eq_zero_of_not_mem (hfresh name hmem)]
    omega
  · rw [List.count_eq_zero_of_not_mem hmem, Nat.zero_add]
    exact hunique name slot hslot

theorem SelectedUnique.prependNoSlots {slots : SlotMap} {owner : Owner}
    {source front : WordEnv} (hunique : SelectedUnique slots owner source)
    (hall : ∀ name ∈ front.map Prod.fst,
      slotFor? slots owner name = none) :
    SelectedUnique slots owner (front ++ source) := by
  intro name slot hslot
  simp only [List.map_append, List.count_append]
  have hnot : name ∉ front.map Prod.fst := by
    intro hmem
    rw [hall name hmem] at hslot
    contradiction
  rw [List.count_eq_zero_of_not_mem hnot, Nat.zero_add]
  exact hunique name slot hslot

private theorem envGet_drop_of_count_le_one {source : WordEnv} {name : Ident}
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
          have hnameRest : name ∈ rest.map Prod.fst := by
            exact envGet_name_mem (ih (by
              simp only [List.map_cons, List.count_cons] at hcount
              omega) drop hrestGet)
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
          exact ih (by
            simp only [List.map_cons, List.count_cons] at hcount
            split at hcount <;> omega) drop hrestGet

theorem SelectedUnique.restoreVisible {slots : SlotMap} {owner : Owner}
    {outer source : WordEnv} (hunique : SelectedUnique slots owner source)
    {name : Ident} {slot : Nat} {value : U256}
    (hslot : slotFor? slots owner name = some slot)
    (hget : envGet (@YulSemantics.restore G outer source) name = some value) :
    envGet source name = some value := by
  unfold YulSemantics.restore at hget
  exact envGet_drop_of_count_le_one (hunique name slot hslot) _ hget

theorem LiveFrameRel.pushScope {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {source target : WordEnv} {sourceState targetState : EvmState}
    (hrel : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState) :
    LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature (scopeMark source target :: cuts) live
      source sourceState target targetState := by
  exact {
    frameRel := {
      env := hrel.frameRel.env.push
      loaded := hrel.frameRel.loaded
      scratch := hrel.frameRel.scratch }
    bound := hrel.bound
    certified := hrel.certified }

/-- Close a lexical scope once the induction has established that dropping the
scope does not uncover a different selected binding.  The `hvisible` premise
is the exact dynamic fact required for `SlotsLoaded`; it follows from static
uniqueness of selected names, but is not contained in `LiveFrameRel` itself. -/
theorem LiveFrameRel.popScope {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {outerLive innerLive : SpillSet}
    {outerSource outerTarget source target : WordEnv}
    {outerSourceState outerTargetState sourceState targetState : EvmState}
    (houter : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts outerLive
      outerSource outerSourceState outerTarget outerTargetState)
    (hinner : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature
      (scopeMark outerSource outerTarget :: cuts) innerLive
      source sourceState target targetState)
    (hunique : SelectedUnique layout.slots frame.owner source)
    (hkeys : (@YulSemantics.restore G outerSource source).map Prod.fst =
      outerSource.map Prod.fst) :
    LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts outerLive
      (@YulSemantics.restore G outerSource source) sourceState
      (@YulSemantics.restore D outerTarget target) targetState := by
  have henv := EnvRel.pop (calls := calls) (creates := creates)
    (base := base) (reserved := reserved)
    (hsource := rfl) (htarget := rfl) hinner.frameRel.env
  have hloaded : SlotsLoaded layout.slots frame.owner
      (@YulSemantics.restore G outerSource source) targetState := by
    intro name slot value hslot hget
    have hsourceGet := hunique.restoreVisible hslot hget
    exact hinner.frameRel.loaded name slot value hslot hsourceGet
  exact {
    frameRel := {
      env := henv
      loaded := hloaded
      scratch := hinner.frameRel.scratch }
    bound := houter.bound.of_keys_eq hkeys
    certified := houter.certified }

/-! ## Control relation -/

/-- `LiveFrameRel` plus the selected-name uniqueness needed at lexical scope
exit.  Every statement/sequence result in the full induction carries this
pair, including non-normal outcomes. -/
structure ControlLiveRel (selected : SpillSet)
    (layout : MemorySpillSelect.Layout) (frame : Frame)
    (signature : List Ident) (cuts : List CutMark) (live : SpillSet)
    (source : WordEnv) (sourceState : EvmState)
    (target : WordEnv) (targetState : EvmState) : Prop where
  liveRel : LiveFrameRel (base := base) (reserved := reserved)
    selected layout frame signature cuts live
    source sourceState target targetState
  unique : SelectedUnique layout.slots frame.owner source

theorem ControlLiveRel.rootInitial {raw : Block Op} {result : Result}
    {guards : List Nat} (hfacts : SpillFacts raw result guards)
    (sourceState : EvmState) :
    let guarded := resolveMemoryGuardStmts result.base result.reserved raw
    let frame : Frame := { owner := none, params := [], returns := [], body := guarded }
    ControlLiveRel (base := result.base) (reserved := result.reserved)
      result.selection result.layout frame [] []
      (frameInitialLive result.selection frame)
      [] sourceState [] sourceState := by
  dsimp only
  exact {
    liveRel := LiveFrameRel.rootInitial hfacts sourceState
    unique := SelectedUnique.empty result.layout.slots none }

theorem callEnv_selectedUnique {slots : SlotMap} {owner : Owner}
    {params returns : List Ident} {argvals : List U256}
    (hlength : argvals.length = params.length)
    (hnodup : (params ++ returns).Nodup) :
    SelectedUnique slots owner (callEnv params returns argvals) := by
  apply SelectedUnique.ofNodupKeys
  have hkeys : (callEnv params returns argvals).map Prod.fst =
      params ++ returns := by
    unfold callEnv
    rw [List.map_append, List.map_fst_zip (by omega), List.map_map]
    congr 1
    clear hnodup
    induction returns with
    | nil => rfl
    | cons name rest ih =>
        change name :: List.map (Prod.fst ∘ fun item => (item, (0 : U256))) rest =
          name :: rest
        rw [ih]
  rwa [hkeys]

theorem SpillFacts.calleeSignatureNodup {raw : Block Op} {result : Result}
    {guards : List Nat} (hfacts : SpillFacts raw result guards)
    {name : Ident} {decl : FDecl G}
    (hframe : calleeFrame name decl ∈ frames
      (resolveMemoryGuardStmts result.base result.reserved raw)) :
    (decl.params ++ decl.rets).Nodup := by
  exact frameSignaturesWF_frame hfacts.signatures_wf hframe

theorem ControlLiveRel.pushScope {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {source target : WordEnv} {sourceState targetState : EvmState}
    (hrel : ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState) :
    ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature (scopeMark source target :: cuts) live
      source sourceState target targetState := by
  exact {
    liveRel := MemorySpillControlSound.LiveFrameRel.pushScope hrel.liveRel
    unique := hrel.unique }

/-- Block-premise package: syntax context plus the corresponding lexical cut
on the runtime relation. -/
theorem ControlStepContext.enterBlock {mode : OriginMode}
    {policyRoot : Block Op} {selected : SpillSet}
    {policyFrame executedFrame : Frame} {live : SpillSet}
    {policyBody executedBody : Block Op} {exitNames : List Ident}
    {source target : WordEnv} {sourceState targetState : EvmState}
    {layout : MemorySpillSelect.Layout} {signature : List Ident}
    {cuts : List CutMark}
    (hctx : ControlStepContext mode policyRoot selected policyFrame executedFrame
      live (.stmts policyBody) (.stmts executedBody) exitNames source)
    (hrel : ControlLiveRel (base := base) (reserved := reserved)
      selected layout policyFrame signature cuts live
      source sourceState target targetState) :
    ControlStepContext mode policyRoot selected policyFrame executedFrame live
        (.stmt (.block policyBody)) (.stmt (.block executedBody))
        exitNames source ∧
      ControlLiveRel (base := base) (reserved := reserved)
        selected layout policyFrame signature
        (scopeMark source target :: cuts) live
        source sourceState target targetState := by
  exact ⟨hctx.asBlockStmt, hrel.pushScope⟩

theorem ControlLiveRel.popScope {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {outerLive innerLive : SpillSet}
    {outerSource outerTarget source target : WordEnv}
    {outerSourceState outerTargetState sourceState targetState : EvmState}
    (houter : ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts outerLive
      outerSource outerSourceState outerTarget outerTargetState)
    (hinner : ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature
      (scopeMark outerSource outerTarget :: cuts) innerLive
      source sourceState target targetState)
    (hkeys : (@YulSemantics.restore G outerSource source).map Prod.fst =
      outerSource.map Prod.fst) :
    ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts outerLive
      (@YulSemantics.restore G outerSource source) sourceState
      (@YulSemantics.restore D outerTarget target) targetState := by
  exact {
    liveRel := MemorySpillControlSound.LiveFrameRel.popScope
      houter.liveRel hinner.liveRel hinner.unique hkeys
    unique := hinner.unique.restore }

/-- Close a lexical scope while preserving the two dynamic exit invariants.
The outer environment supplies boundness; the inner result supplies the
actual return-value synchronization before restoration. -/
theorem ControlLiveRel.popScopeWithExits {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature exitNames : List Ident} {cuts : List CutMark}
    {outerLive innerLive : SpillSet}
    {outerSource outerTarget source target : WordEnv}
    {outerSourceState outerTargetState sourceState targetState : EvmState}
    (houter : ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts outerLive
      outerSource outerSourceState outerTarget outerTargetState)
    (hinner : ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature
      (scopeMark outerSource outerTarget :: cuts) innerLive
      source sourceState target targetState)
    (hsynced : ReturnsSynced exitNames source target)
    (hbound : NamesBound exitNames outerSource)
    (hkeys : (@YulSemantics.restore G outerSource source).map Prod.fst =
      outerSource.map Prod.fst)
    (hsignature : ∀ name ∈ exitNames, name ∈ signature) :
    ControlLiveRel (base := base) (reserved := reserved)
        selected layout frame signature cuts outerLive
        (@YulSemantics.restore G outerSource source) sourceState
        (@YulSemantics.restore D outerTarget target) targetState ∧
      NamesBound exitNames (@YulSemantics.restore G outerSource source) ∧
      ReturnsSynced exitNames
        (@YulSemantics.restore G outerSource source)
        (@YulSemantics.restore D outerTarget target) := by
  exact ⟨houter.popScope hinner hkeys,
    NamesBound.restore hbound hkeys,
    returnsSynced_restore_of_scopedFrameRel hinner.liveRel.frameRel hsynced
      hbound hkeys hsignature hinner.unique⟩

theorem ControlLiveRel.afterCall {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {source target : WordEnv}
    {sourceState targetState sourceState' targetState' : EvmState}
    {cutoff : Nat}
    (hrel : ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (hscratch : ScratchRel base reserved sourceState' targetState')
    (hslotCutoff : ∀ name slot,
      slotFor? layout.slots frame.owner name = some slot → cutoff ≤ slot)
    (hslotReserved : ∀ name slot,
      slotFor? layout.slots frame.owner name = some slot → slot + 32 ≤ reserved)
    (habove : AboveUnchanged cutoff reserved targetState targetState') :
    ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState' target targetState' := by
  exact {
    liveRel := MemorySpillControlSound.LiveFrameRel.afterCall
      hrel.liveRel hscratch hslotCutoff hslotReserved habove
    unique := hrel.unique }

/-- Result relation used by the full `Step` induction.  Unlike the earlier
expression-only relation, every result also retains selected-name uniqueness
and global declaration origin. -/
def ResultControlRel (globalDeclared : List Ident) (selected : SpillSet)
    (layout : MemorySpillSelect.Layout) (frame : Frame)
    (signature : List Ident) (cuts : List CutMark) (live : SpillSet)
    (exitNames : List Ident) (sourceEnv targetEnv : WordEnv)
    (policyCode : Code Op) : Res G → Res D → Prop
  | .eres (.vals values sourceState),
      .eres (.vals targetValues targetState) =>
      targetValues = values ∧
        ControlLiveRel (base := base) (reserved := reserved)
          selected layout frame signature cuts live
          sourceEnv sourceState targetEnv targetState ∧
        EnvDeclaredOrigin globalDeclared sourceEnv ∧
        NamesBound exitNames sourceEnv ∧
        (∀ name ∈ exitNames, name ∈ signature)
  | .eres (.halt sourceState), .eres (.halt targetState) =>
      ControlLiveRel (base := base) (reserved := reserved)
          selected layout frame signature cuts live
          sourceEnv sourceState targetEnv targetState ∧
        EnvDeclaredOrigin globalDeclared sourceEnv ∧
        NamesBound exitNames sourceEnv ∧
        (∀ name ∈ exitNames, name ∈ signature)
  | .sres source sourceState outcome,
      .sres target targetState targetOutcome =>
      ∃ finalLive,
        targetOutcome = outcome ∧
          ControlLiveRel (base := base) (reserved := reserved)
            selected layout frame signature cuts finalLive
            source sourceState target targetState ∧
          EnvDeclaredOrigin globalDeclared source ∧
          NamesBound exitNames source ∧
          (∀ name ∈ exitNames, name ∈ signature) ∧
          (outcome = .leave → ReturnsSynced exitNames source target) ∧
          (∀ body, policyCode = .stmt (.block body) → finalLive = live) ∧
          (outcome = .normal →
            finalLive = liveAfterCode selected frame.owner live policyCode)
  | _, _ => False

theorem ResultControlRel.ofExprLive
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident}
    {source target : WordEnv} {policyCode : Code Op}
    {sourceResult : EResult G} {targetResult : EResult D}
    (hrel : ResultLiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live source target policyCode
      (.eres sourceResult) (.eres targetResult))
    (hunique : SelectedUnique layout.slots frame.owner source)
    (horigin : EnvDeclaredOrigin globalDeclared source)
    (hexitBound : NamesBound exitNames source)
    (hexitSignature : ∀ name ∈ exitNames, name ∈ signature) :
    ResultControlRel (base := base) (reserved := reserved) globalDeclared
      selected layout frame signature cuts live exitNames source target policyCode
      (.eres sourceResult) (.eres targetResult) := by
  cases sourceResult with
  | vals sourceValues sourceState =>
      cases targetResult with
      | vals targetValues targetState =>
          rcases hrel with ⟨hvalues, hlive⟩
          exact ⟨hvalues, ⟨hlive, hunique⟩, horigin, hexitBound,
            hexitSignature⟩
      | halt targetState => exact hrel
  | halt sourceState =>
      cases targetResult with
      | vals targetValues targetState => exact hrel
      | halt targetState => exact ⟨⟨hrel, hunique⟩, horigin, hexitBound,
          hexitSignature⟩

/-! ## First layer of the `Step` induction -/

/-- Call-free expression branch of the main result package.  User calls use
the separate call callback, but literals, variables, builtins, and recursive
argument lists already produce the exact target step/control/above triple. -/
theorem simulateCallFreeExpr
    {mode : OriginMode} {policyRoot : Block Op} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout}
    {policyFrame executedFrame : Frame} {signature : List Ident}
    {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident}
    {policyExpr executedExpr : Expr Op} {source target : WordEnv}
    {sourceState targetState : EvmState} {sourceFuns : FunEnv G}
    {sourceResult : EResult G}
    (hctx : ControlMotiveContext mode policyRoot selected policyFrame
      executedFrame live (.expr policyExpr) (.expr executedExpr) source)
    (hsource : EvalExpr G sourceFuns source sourceState executedExpr sourceResult)
    (hsyntax : SpillExpr executedExpr)
    (hrel : ControlLiveRel (base := base) (reserved := reserved)
      selected layout policyFrame signature cuts live
      source sourceState target targetState)
    (hexitBound : NamesBound exitNames source)
    (hexitSignature : ∀ name ∈ exitNames, name ∈ signature)
    (hexternals : GuardedExternals calls creates base reserved)
    (hbounds : ∀ name slot,
      slotFor? layout.slots policyFrame.owner name = some slot →
        base ≤ slot ∧ slot + 32 ≤ reserved)
    (hreserved : reserved < 2 ^ 256) (exitCopies : Block Op)
    (cutoff : Nat) (hcutoff : base ≤ cutoff) :
    ∃ targetResult : EResult D,
      EvalExpr D (spillFuns layout.slots sourceFuns) target targetState
        (rewriteExpr layout.slots policyFrame.owner executedExpr) targetResult ∧
      ResultControlRel (base := base) (reserved := reserved)
        (MemorySpill.declaredStmts policyRoot) selected layout policyFrame
        signature cuts live exitNames source target (.expr policyExpr)
        (.eres sourceResult) (.eres targetResult) ∧
      ResAboveUnchanged cutoff reserved targetState (.eres targetResult) := by
  obtain ⟨targetResult, htarget, hresult, habove⟩ :=
    simulateExprStep hsource hsyntax hrel.liveRel hexternals hbounds
      hreserved exitCopies cutoff hcutoff
  exact ⟨targetResult, htarget,
    ResultControlRel.ofExprLive hresult hrel.unique hctx.envDeclared hexitBound
      hexitSignature,
    habove⟩

theorem simulateCallFreeArgs
    {mode : OriginMode} {policyRoot : Block Op} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout}
    {policyFrame executedFrame : Frame} {signature : List Ident}
    {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident}
    {policyArgs executedArgs : List (Expr Op)} {source target : WordEnv}
    {sourceState targetState : EvmState} {sourceFuns : FunEnv G}
    {sourceResult : EResult G}
    (hctx : ControlMotiveContext mode policyRoot selected policyFrame
      executedFrame live (.args policyArgs) (.args executedArgs) source)
    (hsource : EvalArgs G sourceFuns source sourceState executedArgs sourceResult)
    (hsyntax : SpillArgs executedArgs)
    (hrel : ControlLiveRel (base := base) (reserved := reserved)
      selected layout policyFrame signature cuts live
      source sourceState target targetState)
    (hexitBound : NamesBound exitNames source)
    (hexitSignature : ∀ name ∈ exitNames, name ∈ signature)
    (hexternals : GuardedExternals calls creates base reserved)
    (hbounds : ∀ name slot,
      slotFor? layout.slots policyFrame.owner name = some slot →
        base ≤ slot ∧ slot + 32 ≤ reserved)
    (hreserved : reserved < 2 ^ 256) (exitCopies : Block Op)
    (cutoff : Nat) (hcutoff : base ≤ cutoff) :
    ∃ targetResult : EResult D,
      EvalArgs D (spillFuns layout.slots sourceFuns) target targetState
        (rewriteArgs layout.slots policyFrame.owner executedArgs) targetResult ∧
      ResultControlRel (base := base) (reserved := reserved)
        (MemorySpill.declaredStmts policyRoot) selected layout policyFrame
        signature cuts live exitNames source target (.args policyArgs)
        (.eres sourceResult) (.eres targetResult) ∧
      ResAboveUnchanged cutoff reserved targetState (.eres targetResult) := by
  obtain ⟨targetResult, htarget, hresult, habove⟩ :=
    simulateArgsStep hsource hsyntax hrel.liveRel hexternals hbounds
      hreserved exitCopies cutoff hcutoff
  exact ⟨targetResult, htarget,
    ResultControlRel.ofExprLive hresult hrel.unique hctx.envDeclared hexitBound
      hexitSignature,
    habove⟩

theorem simulateSeqNil
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident}
    {source target : WordEnv} {sourceState targetState : EvmState}
    {sourceFuns : FunEnv G}
    (hrel : ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (horigin : EnvDeclaredOrigin globalDeclared source)
    (hexitBound : NamesBound exitNames source)
    (hexitSignature : ∀ name ∈ exitNames, name ∈ signature)
    (cutoff : Nat) :
    ∃ targetResult : Res D,
      Step D (spillFuns layout.slots sourceFuns) target targetState
        (rewriteCode layout.slots frame.owner [] (.stmts [])) targetResult ∧
      ResultControlRel (base := base) (reserved := reserved) globalDeclared
        selected layout frame signature cuts live exitNames source target (.stmts [])
        (.sres source sourceState .normal) targetResult ∧
      ResAboveUnchanged cutoff reserved targetState targetResult := by
  refine ⟨.sres target targetState .normal, ?_, ?_, ?_⟩
  · simpa [rewriteCode, rewriteStmts] using
      (Step.seqNil : ExecStmts D (spillFuns layout.slots sourceFuns)
        target targetState [] target targetState .normal)
  · refine ⟨live, rfl, hrel, horigin, hexitBound, hexitSignature, ?_, ?_, ?_⟩
    · intro hleave
      contradiction
    · intro body hblock
      contradiction
    · intro _
      simp [liveAfterCode, liveStmts]
  · exact AboveUnchanged.refl cutoff reserved targetState

theorem simulateBreak
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident}
    {source target : WordEnv} {sourceState targetState : EvmState}
    {sourceFuns : FunEnv G} {exitCopies : Block Op}
    (hrel : ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (horigin : EnvDeclaredOrigin globalDeclared source)
    (hexitBound : NamesBound exitNames source)
    (hexitSignature : ∀ name ∈ exitNames, name ∈ signature)
    (cutoff : Nat) :
    ∃ targetResult : Res D,
      Step D (spillFuns layout.slots sourceFuns) target targetState
        (rewriteCode layout.slots frame.owner exitCopies (.stmt .break))
        targetResult ∧
      ResultControlRel (base := base) (reserved := reserved) globalDeclared
        selected layout frame signature cuts live exitNames source target (.stmt .break)
        (.sres source sourceState .break) targetResult ∧
      ResAboveUnchanged cutoff reserved targetState targetResult := by
  refine ⟨.sres target targetState .break, ?_, ?_, ?_⟩
  · simpa [rewriteCode, rewriteStmt] using
      (Step.seqStop (rest := [])
        (Step.break : ExecStmt D (spillFuns layout.slots sourceFuns)
          target targetState .break target targetState .break) (by decide))
  · exact ⟨live, rfl, hrel, horigin, hexitBound, hexitSignature,
      by simp, by simp, by simp⟩
  · exact AboveUnchanged.refl cutoff reserved targetState

theorem simulateContinue
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident}
    {source target : WordEnv} {sourceState targetState : EvmState}
    {sourceFuns : FunEnv G} {exitCopies : Block Op}
    (hrel : ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (horigin : EnvDeclaredOrigin globalDeclared source)
    (hexitBound : NamesBound exitNames source)
    (hexitSignature : ∀ name ∈ exitNames, name ∈ signature)
    (cutoff : Nat) :
    ∃ targetResult : Res D,
      Step D (spillFuns layout.slots sourceFuns) target targetState
        (rewriteCode layout.slots frame.owner exitCopies (.stmt .continue))
        targetResult ∧
      ResultControlRel (base := base) (reserved := reserved) globalDeclared
        selected layout frame signature cuts live exitNames source target (.stmt .continue)
        (.sres source sourceState .continue) targetResult ∧
      ResAboveUnchanged cutoff reserved targetState targetResult := by
  refine ⟨.sres target targetState .continue, ?_, ?_, ?_⟩
  · simpa [rewriteCode, rewriteStmt] using
      (Step.seqStop (rest := [])
        (Step.continue : ExecStmt D (spillFuns layout.slots sourceFuns)
          target targetState .continue target targetState .continue) (by decide))
  · exact ⟨live, rfl, hrel, horigin, hexitBound, hexitSignature,
      by simp, by simp, by simp⟩
  · exact AboveUnchanged.refl cutoff reserved targetState

theorem hoist_copyBackReturns_control (slots : SlotMap) (owner : Owner) :
    ∀ returns, hoist D (copyBackReturns slots owner returns) = [] := by
  intro returns
  induction returns with
  | nil => rfl
  | cons name rest ih =>
      cases hslot : slotFor? slots owner name with
      | none => simpa [copyBackReturns, hslot] using ih
      | some slot => simpa [copyBackReturns, hslot, hoist] using ih

theorem hoist_append_control (left right : Block Op) :
    hoist D (left ++ right) = hoist D left ++ hoist D right := by
  induction left with
  | nil => rfl
  | cons statement rest ih =>
      cases statement <;> simp_all [hoist]

theorem execStmts_append_normal_control {funs : FunEnv D}
    {left right : Block Op} {start middle final : WordEnv}
    {startState middleState finalState : EvmState} {outcome : Outcome}
    (hleft : ExecStmts D funs start startState left
      middle middleState .normal)
    (hright : ExecStmts D funs middle middleState right
      final finalState outcome) :
    ExecStmts D funs start startState (left ++ right)
      final finalState outcome := by
  induction left generalizing start startState with
  | nil => cases hleft with | seqNil => exact hright
  | cons statement rest ih =>
      cases hleft with
      | seqCons hstatement hrest => exact Step.seqCons hstatement (ih hrest)
      | seqStop _ hne => exact False.elim (hne rfl)

/-- Execute a rewritten `leave`: refresh retained return cells from spill
memory, then take the source `leave` outcome with synchronized returns. -/
theorem simulateLeaveLeaf
    {mode : OriginMode} {policyRoot : Block Op} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout}
    {policyFrame executedFrame : Frame} {cuts : List CutMark}
    {live : SpillSet} {exitNames : List Ident}
    {source target : WordEnv} {sourceState targetState : EvmState}
    {sourceFuns : FunEnv G} {exitCopies : Block Op} {cutoff : Nat}
    (hctx : ControlStepContext mode policyRoot selected policyFrame executedFrame
      live (.stmt .leave) (.stmt .leave) exitNames source)
    (hrel : ControlLiveRel (base := base) (reserved := reserved)
      selected layout policyFrame (policyFrame.params ++ policyFrame.returns)
      cuts live source sourceState target targetState)
    (hbounds : ∀ name slot,
      slotFor? layout.slots policyFrame.owner name = some slot →
        slot + 32 ≤ reserved)
    (hreserved : reserved < 2 ^ 256)
    (hexitCopies : exitCopies =
      copyBackReturns layout.slots policyFrame.owner exitNames) :
    ∃ targetResult : Res D,
      Step D (spillFuns layout.slots sourceFuns) target targetState
          (rewriteCode layout.slots policyFrame.owner exitCopies (.stmt .leave))
          targetResult ∧
        ResultControlRel (base := base) (reserved := reserved)
          (MemorySpill.declaredStmts policyRoot) selected layout policyFrame
          (policyFrame.params ++ policyFrame.returns) cuts live exitNames
          source target (.stmt .leave)
          (.sres source sourceState .leave) targetResult ∧
        ResAboveUnchanged cutoff reserved targetState targetResult := by
  let copies := copyBackReturns layout.slots policyFrame.owner exitNames
  obtain ⟨targetFinal, targetFinalState, hcopies, hfinalFrame, hsynced,
      _houtside, habove⟩ :=
    execCopyBackReturns (sourceFuns := [] :: sourceFuns)
      hrel.liveRel.frameRel hctx.exitsNodup hctx.exitsInSignature hctx.exitsBound
      hbounds hreserved
  have hfinalControl : ControlLiveRel (base := base) (reserved := reserved)
      selected layout policyFrame (policyFrame.params ++ policyFrame.returns)
      cuts live source sourceState targetFinal targetFinalState := {
    liveRel := {
      frameRel := hfinalFrame
      bound := hrel.liveRel.bound
      certified := hrel.liveRel.certified }
    unique := hrel.unique }
  have htargetLength : targetFinal.length = target.length := by
    rw [hfinalFrame.env.vars.length_eq_filter,
      hrel.liveRel.frameRel.env.vars.length_eq_filter]
  have hrestored : @YulSemantics.restore D target targetFinal = targetFinal := by
    simp [YulSemantics.restore, htargetLength]
  have hleaveInner : ExecStmts D (spillFuns layout.slots ([] :: sourceFuns))
      targetFinal targetFinalState [.leave]
      targetFinal targetFinalState .leave := by
    exact Step.seqStop (rest := []) Step.leave (by decide)
  have hinner : ExecStmts D (spillFuns layout.slots ([] :: sourceFuns))
      target targetState (copies ++ [.leave])
      targetFinal targetFinalState .leave := by
    exact execStmts_append_normal_control
      (by simpa [copies] using hcopies) hleaveInner
  by_cases hempty : copies.isEmpty
  · have hcopiesNil : copies = [] := by simpa using hempty
    change ExecStmts D (spillFuns layout.slots ([] :: sourceFuns))
      target targetState copies targetFinal targetFinalState .normal at hcopies
    rw [hcopiesNil] at hcopies
    cases hcopies
    refine ⟨.sres target targetState .leave, ?_, ?_, ?_⟩
    · simpa [rewriteCode, rewriteStmt, hexitCopies, copies, hcopiesNil] using
        (Step.seqStop (rest := [])
          (Step.leave : ExecStmt D (spillFuns layout.slots sourceFuns)
            target targetState .leave target targetState .leave) (by decide))
    · exact ⟨live, rfl, hfinalControl, hctx.motive.envDeclared,
        hctx.exitsBound, hctx.exitsInSignature, fun _ => hsynced,
        by simp, by simp⟩
    · exact AboveUnchanged.refl cutoff reserved targetState
  · have hhoist : hoist D (copies ++ [.leave]) = [] := by
      rw [hoist_append_control, show copies =
        copyBackReturns layout.slots policyFrame.owner exitNames by rfl,
        hoist_copyBackReturns_control]
      rfl
    have hblock : ExecStmt D (spillFuns layout.slots sourceFuns)
        target targetState (.block (copies ++ [.leave]))
        targetFinal targetFinalState .leave := by
      rw [← hrestored]
      apply Step.block
      rw [hhoist]
      simpa [spillFuns, spillScope] using hinner
    refine ⟨.sres targetFinal targetFinalState .leave, ?_, ?_, ?_⟩
    · have hseq := Step.seqStop (rest := []) hblock (by decide)
      simpa [rewriteCode, rewriteStmt, hexitCopies, copies, hempty] using hseq
    · exact ⟨live, rfl, hfinalControl, hctx.motive.envDeclared,
        hctx.exitsBound, hctx.exitsInSignature, fun _ => hsynced,
        by simp, by simp⟩
    · exact habove cutoff

theorem ControlLiveRel.finishSet {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {source target target' : WordEnv} {sourceState targetState targetState' : EvmState}
    {name : Ident} {value : U256}
    (hrel : ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (hnext : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      (envSet source name value) sourceState target' targetState') :
    ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      (envSet source name value) sourceState target' targetState' := by
  exact { liveRel := hnext, unique := hrel.unique.set name value }

theorem ControlLiveRel.finishSelectedLet {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live nextLive : SpillSet}
    {source target target' : WordEnv} {sourceState targetState targetState' : EvmState}
    {name : Ident} {value : U256}
    (hrel : ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (hnext : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts nextLive
      ((name, value) :: source) sourceState target' targetState')
    (hfresh : name ∉ source.map Prod.fst) :
    ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts nextLive
      ((name, value) :: source) sourceState target' targetState' := by
  exact {
    liveRel := hnext
    unique := hrel.unique.prependSelectedFresh hfresh }

theorem ControlLiveRel.finishUnselectedLet {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live nextLive : SpillSet}
    {source target target' : WordEnv} {sourceState targetState targetState' : EvmState}
    {name : Ident} {value : U256}
    (hrel : ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (hnext : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts nextLive
      ((name, value) :: source) sourceState target' targetState')
    (hnoSlot : slotFor? layout.slots frame.owner name = none) :
    ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts nextLive
      ((name, value) :: source) sourceState target' targetState' := by
  exact {
    liveRel := hnext
    unique := hrel.unique.prependNoSlot hnoSlot }

theorem ControlLiveRel.finishSelectedMultiLet {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live nextLive : SpillSet}
    {source target target' : WordEnv} {sourceState targetState targetState' : EvmState}
    {names : List Ident} {values : List U256}
    (hrel : ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (hnext : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts nextLive
      (names.zip values ++ source) sourceState target' targetState')
    (hlength : values.length = names.length)
    (hnodup : names.Nodup)
    (hfresh : ∀ name ∈ names, name ∉ source.map Prod.fst) :
    ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts nextLive
      (names.zip values ++ source) sourceState target' targetState' := by
  have hkeys : (names.zip values).map Prod.fst = names :=
    List.map_fst_zip (by omega)
  apply ControlLiveRel.mk hnext
  apply hrel.unique.prependFreshList
  · rwa [hkeys]
  · intro name hmem
    rw [hkeys] at hmem
    exact hfresh name hmem

theorem ControlLiveRel.finishUnselectedMultiLet {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live nextLive : SpillSet}
    {source target target' : WordEnv} {sourceState targetState targetState' : EvmState}
    {names : List Ident} {values : List U256}
    (hrel : ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts live
      source sourceState target targetState)
    (hnext : LiveFrameRel (base := base) (reserved := reserved)
      selected layout frame signature cuts nextLive
      (names.zip values ++ source) sourceState target' targetState')
    (hlength : values.length = names.length)
    (hall : ∀ name ∈ names,
      slotFor? layout.slots frame.owner name = none) :
    ControlLiveRel (base := base) (reserved := reserved)
      selected layout frame signature cuts nextLive
      (names.zip values ++ source) sourceState target' targetState' := by
  have hkeys : (names.zip values).map Prod.fst = names :=
    List.map_fst_zip (by omega)
  apply ControlLiveRel.mk hnext
  apply hrel.unique.prependNoSlots
  intro name hmem
  rw [hkeys] at hmem
  exact hall name hmem

/-- Function entry upgraded from `LiveFrameRel` to the control relation. -/
theorem enterCalleeControl {selected : SpillSet} {policyBody : Block Op}
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
    ControlLiveRel (base := base) (reserved := reserved)
      selected layout (calleeFrame name decl) (decl.params ++ decl.rets) []
      (frameInitialLive selected (calleeFrame name decl))
      entry sourceState entry afterEntry ∧
    AboveUnchanged cutoff reserved targetState afterEntry := by
  dsimp only
  obtain ⟨hexec, hlive, habove⟩ := enterCallee hbuild hcheck hframe hlength
    hnodup hscratch hreserved cutoff hcutoff
  exact ⟨hexec, {
    liveRel := hlive
    unique := callEnv_selectedUnique hlength hnodup }, habove⟩

/-! ## Rewritten statement-sequence composition -/

theorem execStmts_append_normal {funs : FunEnv D}
    {left right : Block Op} {start middle final : WordEnv}
    {startState middleState finalState : EvmState} {outcome : Outcome}
    (hleft : ExecStmts D funs start startState left
      middle middleState .normal)
    (hright : ExecStmts D funs middle middleState right
      final finalState outcome) :
    ExecStmts D funs start startState (left ++ right)
      final finalState outcome := by
  induction left generalizing start startState with
  | nil => cases hleft with | seqNil => exact hright
  | cons statement rest ih =>
      cases hleft with
      | seqCons hstatement hrest =>
          exact Step.seqCons hstatement (ih hrest)
      | seqStop _ hne => exact False.elim (hne rfl)

theorem execStmts_append_early {funs : FunEnv D}
    {left right : Block Op} {start final : WordEnv}
    {startState finalState : EvmState} {outcome : Outcome}
    (hleft : ExecStmts D funs start startState left
      final finalState outcome)
    (hearly : outcome ≠ .normal) :
    ExecStmts D funs start startState (left ++ right)
      final finalState outcome := by
  induction left generalizing start startState with
  | nil => cases hleft with | seqNil => exact False.elim (hearly rfl)
  | cons statement rest ih =>
      cases hleft with
      | seqCons hstatement hrest =>
          exact Step.seqCons hstatement (ih hrest)
      | seqStop hstatement hne =>
          exact Step.seqStop (rest := rest ++ right) hstatement hne

/-- The exact code equation used by the sequence induction's normal branch. -/
theorem closeRewriteStmts_cons_normal {slots : SlotMap} {owner : Owner}
    {exitCopies : Block Op} {sourceFuns : FunEnv G}
    {statement : Stmt Op} {rest : Block Op}
    {start middle final : WordEnv}
    {startState middleState finalState : EvmState} {outcome : Outcome}
    (hstatement : ExecStmts D (spillFuns slots sourceFuns) start startState
      (rewriteStmt slots owner exitCopies statement)
      middle middleState .normal)
    (hrest : ExecStmts D (spillFuns slots sourceFuns) middle middleState
      (rewriteStmts slots owner exitCopies rest)
      final finalState outcome) :
    ExecStmts D (spillFuns slots sourceFuns) start startState
      (rewriteStmts slots owner exitCopies (statement :: rest))
      final finalState outcome := by
  simpa [rewriteStmts] using execStmts_append_normal hstatement hrest

/-- A non-normal rewritten head prevents execution of the rewritten tail. -/
theorem closeRewriteStmts_cons_early {slots : SlotMap} {owner : Owner}
    {exitCopies : Block Op} {sourceFuns : FunEnv G}
    {statement : Stmt Op} {rest : Block Op}
    {start final : WordEnv} {startState finalState : EvmState}
    {outcome : Outcome}
    (hstatement : ExecStmts D (spillFuns slots sourceFuns) start startState
      (rewriteStmt slots owner exitCopies statement)
      final finalState outcome)
    (hearly : outcome ≠ .normal) :
    ExecStmts D (spillFuns slots sourceFuns) start startState
      (rewriteStmts slots owner exitCopies (statement :: rest))
      final finalState outcome := by
  simpa [rewriteStmts] using
    (execStmts_append_early (right := rewriteStmts slots owner exitCopies rest)
      hstatement hearly)

theorem closeSeqNormalResult
    {globalDeclared : List Ident} {selected : SpillSet}
    {layout : MemorySpillSelect.Layout} {frame : Frame}
    {signature : List Ident} {cuts : List CutMark} {live : SpillSet}
    {exitNames : List Ident}
    {sourceFuns : FunEnv G} {exitCopies : Block Op}
    {statement : Stmt Op} {rest : Block Op}
    {sourceStart sourceMiddle sourceFinal : WordEnv}
    {targetStart targetMiddle targetFinal : WordEnv}
    {sourceFinalState targetStartState targetMiddleState targetFinalState : EvmState}
    {outcome targetOutcome : Outcome}
    (hhead : ExecStmts D (spillFuns layout.slots sourceFuns)
      targetStart targetStartState
      (rewriteStmt layout.slots frame.owner exitCopies statement)
      targetMiddle targetMiddleState .normal)
    (htail : ExecStmts D (spillFuns layout.slots sourceFuns)
      targetMiddle targetMiddleState
      (rewriteStmts layout.slots frame.owner exitCopies rest)
      targetFinal targetFinalState targetOutcome)
    (hresult : ResultControlRel (base := base) (reserved := reserved)
      (calls := calls) (creates := creates)
      globalDeclared selected layout frame signature cuts
      (liveStmt selected frame.owner live statement).2
      exitNames sourceMiddle targetMiddle (.stmts rest)
      (.sres sourceFinal sourceFinalState outcome)
      (.sres targetFinal targetFinalState targetOutcome)) :
    ExecStmts D (spillFuns layout.slots sourceFuns)
      targetStart targetStartState
      (rewriteStmts layout.slots frame.owner exitCopies (statement :: rest))
      targetFinal targetFinalState targetOutcome ∧
    ResultControlRel (base := base) (reserved := reserved)
      (calls := calls) (creates := creates)
      globalDeclared selected layout frame signature cuts live
      exitNames sourceStart targetStart (.stmts (statement :: rest))
      (.sres sourceFinal sourceFinalState outcome)
      (.sres targetFinal targetFinalState targetOutcome) := by
  constructor
  · exact closeRewriteStmts_cons_normal hhead htail
  · simpa [ResultControlRel, liveAfterCode, liveStmts] using hresult

/-! ## One-statement semantic closures -/

theorem execStmts_singleton {funs : FunEnv D} {statement : Stmt Op}
    {start final : WordEnv} {startState finalState : EvmState}
    {outcome : Outcome}
    (hstatement : ExecStmt D funs start startState statement
      final finalState outcome) :
    ExecStmts D funs start startState [statement]
      final finalState outcome := by
  by_cases hnormal : outcome = .normal
  · subst outcome
    exact Step.seqCons hstatement Step.seqNil
  · exact Step.seqStop hstatement hnormal

theorem execRewriteBlock {slots : SlotMap} {owner : Owner}
    {exitCopies : Block Op} {sourceFuns : FunEnv G} {body : Block Op}
    {start inner : WordEnv} {startState finalState : EvmState}
    {outcome : Outcome}
    (hbody : ExecStmts D
      (spillFuns slots (hoist G body :: sourceFuns)) start startState
      (rewriteStmts slots owner exitCopies body) inner finalState outcome) :
    ExecStmts D (spillFuns slots sourceFuns) start startState
      (rewriteStmt slots owner exitCopies (.block body))
      (@restore D start inner) finalState outcome := by
  have hbody' : ExecStmts D
      (hoist D (rewriteStmts slots owner exitCopies body) ::
        spillFuns slots sourceFuns)
      start startState (rewriteStmts slots owner exitCopies body)
      inner finalState outcome := by
    rw [← spillScope_hoist slots owner exitCopies body]
    simpa [spillFuns] using hbody
  simpa [rewriteStmt] using execStmts_singleton (Step.block hbody')

theorem execRewriteFunDef {slots : SlotMap} {owner : Owner}
    {exitCopies : Block Op} {sourceFuns : FunEnv G}
    {name : Ident} {params returns : List Ident} {body : Block Op}
    {vars : WordEnv} {state : EvmState} :
    ExecStmts D (spillFuns slots sourceFuns) vars state
      (rewriteStmt slots owner exitCopies (.funDef name params returns body))
      vars state .normal := by
  simpa [rewriteStmt, spillDecl] using
    (Step.seqCons
      (Step.funDef : ExecStmt D (spillFuns slots sourceFuns) vars state
        (.funDef name params returns
          (initParams slots (some name) params ++
            initReturns slots (some name) returns ++
            [.block (rewriteStmts slots (some name)
              (copyBackReturns slots (some name) returns) body)] ++
            copyBackReturns slots (some name) returns))
        vars state .normal)
      Step.seqNil)

theorem execRewriteBreak {slots : SlotMap} {owner : Owner}
    {exitCopies : Block Op} {sourceFuns : FunEnv G}
    {vars : WordEnv} {state : EvmState} :
    ExecStmts D (spillFuns slots sourceFuns) vars state
      (rewriteStmt slots owner exitCopies .break) vars state .break := by
  simpa [rewriteStmt] using
    (Step.seqStop (rest := [])
      (Step.break : ExecStmt D (spillFuns slots sourceFuns) vars state
        .break vars state .break) (by decide))

theorem execRewriteContinue {slots : SlotMap} {owner : Owner}
    {exitCopies : Block Op} {sourceFuns : FunEnv G}
    {vars : WordEnv} {state : EvmState} :
    ExecStmts D (spillFuns slots sourceFuns) vars state
      (rewriteStmt slots owner exitCopies .continue) vars state .continue := by
  simpa [rewriteStmt] using
    (Step.seqStop (rest := [])
      (Step.continue : ExecStmt D (spillFuns slots sourceFuns) vars state
        .continue vars state .continue) (by decide))

theorem execRewriteExprStmt_normal {slots : SlotMap} {owner : Owner}
    {exitCopies : Block Op} {sourceFuns : FunEnv G}
    {expression : Expr Op} {vars : WordEnv}
    {startState finalState : EvmState}
    (hexpression : EvalExpr D (spillFuns slots sourceFuns) vars startState
      (rewriteExpr slots owner expression) (.vals [] finalState)) :
    ExecStmts D (spillFuns slots sourceFuns) vars startState
      (rewriteStmt slots owner exitCopies (.exprStmt expression))
      vars finalState .normal := by
  simpa [rewriteStmt] using execStmts_singleton (Step.exprStmt hexpression)

theorem execRewriteExprStmt_halt {slots : SlotMap} {owner : Owner}
    {exitCopies : Block Op} {sourceFuns : FunEnv G}
    {expression : Expr Op} {vars : WordEnv}
    {startState finalState : EvmState}
    (hexpression : EvalExpr D (spillFuns slots sourceFuns) vars startState
      (rewriteExpr slots owner expression) (.halt finalState)) :
    ExecStmts D (spillFuns slots sourceFuns) vars startState
      (rewriteStmt slots owner exitCopies (.exprStmt expression))
      vars finalState .halt := by
  simpa [rewriteStmt] using execStmts_singleton (Step.exprStmtHalt hexpression)

theorem execRewriteIf_true {slots : SlotMap} {owner : Owner}
    {exitCopies : Block Op} {sourceFuns : FunEnv G}
    {condition : Expr Op} {body : Block Op} {value : U256}
    {start bodyVars : WordEnv}
    {startState conditionState finalState : EvmState} {outcome : Outcome}
    (hcondition : EvalExpr D (spillFuns slots sourceFuns) start startState
      (rewriteExpr slots owner condition) (.vals [value] conditionState))
    (hnonzero : value ≠ 0)
    (hbody : ExecStmt D (spillFuns slots sourceFuns) start conditionState
      (.block (rewriteStmts slots owner exitCopies body))
      bodyVars finalState outcome) :
    ExecStmts D (spillFuns slots sourceFuns) start startState
      (rewriteStmt slots owner exitCopies (.cond condition body))
      bodyVars finalState outcome := by
  have hzero : Dialect.zero D = (0 : U256) := by
    change litValue (.number 0) = (0 : U256)
    decide
  simpa [rewriteStmt] using execStmts_singleton
    (Step.ifTrue hcondition (by simpa [hzero] using hnonzero) hbody)

theorem execRewriteIf_false {slots : SlotMap} {owner : Owner}
    {exitCopies : Block Op} {sourceFuns : FunEnv G}
    {condition : Expr Op} {body : Block Op}
    {start : WordEnv} {startState conditionState : EvmState}
    (hcondition : EvalExpr D (spillFuns slots sourceFuns) start startState
      (rewriteExpr slots owner condition) (.vals [0] conditionState)) :
    ExecStmts D (spillFuns slots sourceFuns) start startState
      (rewriteStmt slots owner exitCopies (.cond condition body))
      start conditionState .normal := by
  have hzero : Dialect.zero D = (0 : U256) := by
    change litValue (.number 0) = (0 : U256)
    decide
  simpa [rewriteStmt] using execStmts_singleton
    (Step.ifFalse hcondition hzero.symm)

theorem execRewriteIf_halt {slots : SlotMap} {owner : Owner}
    {exitCopies : Block Op} {sourceFuns : FunEnv G}
    {condition : Expr Op} {body : Block Op}
    {start : WordEnv} {startState conditionState : EvmState}
    (hcondition : EvalExpr D (spillFuns slots sourceFuns) start startState
      (rewriteExpr slots owner condition) (.halt conditionState)) :
    ExecStmts D (spillFuns slots sourceFuns) start startState
      (rewriteStmt slots owner exitCopies (.cond condition body))
      start conditionState .halt := by
  simpa [rewriteStmt] using execStmts_singleton (Step.ifHalt hcondition)

end YulEvmCompiler.Optimizer.MemorySpillControlSound
