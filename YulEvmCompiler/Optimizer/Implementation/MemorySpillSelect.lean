import YulEvmCompiler.Optimizer.Implementation.MemorySpill
set_option warningAsError true
/-!
# Pressure-selected memory spilling

This module separates the spill mechanism from its allocation policy.  It
mirrors the compiler's physical stack accounting to select only bindings that
actually cause a `DUP17+`/`SWAP17+` failure.  Selected bindings coupled by a
multi-result declaration or assignment move together, allowing the compiler's
direct result-distribution lowering to consume the tuple without retaining
temporary stack slots.

Within each function, memory slots follow lexical lifetimes: nested blocks,
switch alternatives, and loop body/post regions reuse slots after restoration.
Across functions, a caller's frame is placed above the maximum region needed
by any callee, while sibling call branches reuse the same range.  Consequently
the raised memory guard uses a safe call-path upper bound on live spill storage,
not the number of bindings in the object.
-/

namespace YulEvmCompiler.Optimizer.MemorySpillSelect

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open MemorySpill

abbrev Owner := Option Ident

structure SpillKey where
  owner : Owner
  name : Ident
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev SpillSet := List SpillKey
abbrev SlotMap := List (SpillKey × Nat)

def isSelected (selected : SpillSet) (owner : Owner) (x : Ident) : Bool :=
  selected.contains { owner, name := x }

abbrev SelectedPred := Owner → Ident → Bool

/-- Build the hot-path membership index once per pressure traversal.  The
proof-facing spill set remains a list, while large protocol objects avoid a
linear string scan at every variable occurrence. -/
def selectedPred (selected : SpillSet) : SelectedPred :=
  let index := Std.HashSet.ofList selected
  fun owner name => index.contains { owner, name }

inductive PressureKind
  | read
  | write
  deriving Repr, DecidableEq

structure Pressure where
  owner : Owner
  name : Ident
  kind : PressureKind
  depth : Nat
  deficit : Nat
  /-- Reserved for diagnostics.  Selection batches are assembled only from
  individually witnessed pressure records, never inferred from a layout suffix. -/
  batch : List Ident
  deriving Repr

def physicalDecls (chosen : SelectedPred) (owner : Owner) (xs : List Ident) : List Ident :=
  xs.filter fun x => !chosen owner x

mutual
  def firstPressureExpr (chosen : SelectedPred) (owner : Owner) (phi : FMap)
      (layout : List Ident) (off : Nat) : Expr Op → Option Pressure
    | .lit _ => none
    | .var x =>
        if chosen owner x then none else
        match layout.findIdx? (· = x) with
        | some idx =>
            if off + idx < 16 then none
            else some {
              owner, name := x, kind := .read, depth := off + idx
              deficit := off + idx + 1 - 16
              batch := []
            }
        | none => none
    | .builtin _ args => firstPressureArgs chosen owner phi layout off args
    | .call f args =>
        match lookupF phi f with
        | some (info, _) =>
            firstPressureArgs chosen owner phi layout (off + 1 + info.rets) args
        | none =>
            -- Parser-level pseudo-operations are diagnosed for their argument
            -- pressure here; final compilation remains the acceptance oracle.
            firstPressureArgs chosen owner phi layout off args

  def firstPressureArgs (chosen : SelectedPred) (owner : Owner) (phi : FMap)
      (layout : List Ident) (off : Nat) : List (Expr Op) → Option Pressure
    | [] => none
    | e :: rest =>
        firstPressureArgs chosen owner phi layout off rest <|>
          firstPressureExpr chosen owner phi layout (off + rest.length) e
end

def firstPressureAssigns (chosen : SelectedPred) (owner : Owner)
    (layout : List Ident) : List Ident → Option Pressure
  | [] => none
  | x :: xs =>
      if chosen owner x then firstPressureAssigns chosen owner layout xs else
      match layout.findIdx? (· = x) with
      | some idx =>
          if idx + xs.length < 16 then firstPressureAssigns chosen owner layout xs
          else some {
            owner, name := x, kind := .write, depth := idx + xs.length
            deficit := idx + xs.length + 1 - 16
            batch := []
          }
      | none => firstPressureAssigns chosen owner layout xs

def firstReturnCopyPressure (chosen : SelectedPred) (owner : Owner)
    (signature returns layout : List Ident) : Option Pressure :=
  returns.findSome? fun r =>
    if !chosen owner r then none else
    match layout.findIdx? (· = r) with
    | some idx =>
        if idx < 16 then none else
        match (layout.take idx).find? fun x => !signature.contains x with
        | some candidate => some {
            owner, name := candidate, kind := .write, depth := idx
            deficit := idx + 1 - 16
            batch := []
          }
        | none => some {
            owner, name := r, kind := .write, depth := idx
            deficit := idx + 1 - 16
            batch := []
          }
    | none => none

mutual
  def firstPressureBlock (chosen : SelectedPred) (owner : Owner)
      (signature returns : List Ident) (phi : FMap) (layout : List Ident)
      (body : Block Op) : Except Pressure Unit := do
    let (scope, _) := hoistInfos 0 body
    let _ ← firstPressureStmts chosen owner signature returns (scope :: phi) layout body
    pure ()
    termination_by 2 * sizeOf body + 1

  def firstPressureStmt (chosen : SelectedPred) (owner : Owner)
      (signature returns : List Ident) (phi : FMap) (layout : List Ident) :
      Stmt Op → Except Pressure (List Ident)
    | .exprStmt e =>
        match firstPressureExpr chosen owner phi layout 0 e with
        | some pressure => throw pressure
        | none => pure layout
    | .letDecl xs val => do
        match val.bind (firstPressureExpr chosen owner phi layout 0) with
        | some pressure => throw pressure
        | none => pure (physicalDecls chosen owner xs ++ layout)
    | .assign xs e => do
        match firstPressureExpr chosen owner phi layout 0 e with
        | some pressure => throw pressure
        | none =>
            match firstPressureAssigns chosen owner layout xs with
            | some pressure => throw pressure
            | none => pure layout
    | .block body =>
        firstPressureBlock chosen owner signature returns phi layout body *> pure layout
    | .cond c body => do
        match firstPressureExpr chosen owner phi layout 0 c with
        | some pressure => throw pressure
        | none => firstPressureBlock chosen owner signature returns phi layout body
        pure layout
    | .switch c cases dflt => do
        match firstPressureExpr chosen owner phi layout 0 c with
        | some pressure => throw pressure
        | none => firstPressureCases chosen owner signature returns phi layout cases
        match dflt with
        | some body => firstPressureBlock chosen owner signature returns phi layout body
        | none => pure ()
        pure layout
    | .forLoop init c post body => do
        let (scope, _) := hoistInfos 0 init
        let phi' := scope :: phi
        let loopLayout ←
          firstPressureStmts chosen owner signature returns phi' layout init
        match firstPressureExpr chosen owner phi' loopLayout 0 c with
        | some pressure => throw pressure
        | none => pure ()
        firstPressureBlock chosen owner signature returns phi' loopLayout body
        firstPressureBlock chosen owner signature returns phi' loopLayout post
        pure layout
    | .funDef f ps rs body => do
        firstPressureBlock chosen (some f) (ps ++ rs) rs phi (ps ++ rs) body
        match firstReturnCopyPressure chosen (some f) (ps ++ rs) rs (ps ++ rs) with
        | some pressure => throw pressure
        | none => pure ()
        pure layout
    | .leave =>
        match firstReturnCopyPressure chosen owner signature returns layout with
        | some pressure => throw pressure
        | none => pure layout
    | .break | .continue => pure layout
    termination_by s => 2 * sizeOf s

  def firstPressureStmts (chosen : SelectedPred) (owner : Owner)
      (signature returns : List Ident) (phi : FMap) (layout : List Ident) :
      Block Op → Except Pressure (List Ident)
    | [] => pure layout
    | s :: rest => do
        let layout' ← firstPressureStmt chosen owner signature returns phi layout s
        firstPressureStmts chosen owner signature returns phi layout' rest
    termination_by ss => 2 * sizeOf ss

  def firstPressureCases (chosen : SelectedPred) (owner : Owner)
      (signature returns : List Ident) (phi : FMap) (layout : List Ident) :
      List (Literal × Block Op) → Except Pressure Unit
    | [] => pure ()
    | (_, body) :: rest => do
        firstPressureBlock chosen owner signature returns phi layout body
        firstPressureCases chosen owner signature returns phi layout rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def firstPressure (selected : SpillSet) (body : Block Op) : Option Pressure :=
  let (scope, _) := hoistInfos 0 body
  match firstPressureStmts (selectedPred selected) none [] [] [scope] [] body with
  | .error pressure => some pressure
  | .ok _ => none

/-! ### Bounded structural pressure collection

`firstPressure` is deliberately a small, exact acceptance oracle: it stops at
the first inaccessible binding.  Re-running it once per selected binding is
quadratic in the size of large generated contracts, however.  The collector
below mirrors the same physical-layout traversal but records up to 32 distinct
bindings that are inaccessible under the *current* selection.  A batch never
uses a guessed deep layout suffix: every member has its own concrete read,
write, or return-copy pressure witness in this traversal.

The selection loop still invokes `firstPressure` before accepting its final
selection.  Thus this bounded collector is only an acceleration mechanism;
the original exact traversal remains the authoritative completion check. -/

def pressureBatchLimit : Nat := 32

def samePressureBinding (a b : Pressure) : Bool :=
  a.owner == b.owner && a.name == b.name

def addPressure (limit : Nat) (pressures : List Pressure)
    (pressure : Pressure) : List Pressure :=
  if limit ≤ pressures.length || pressures.any (samePressureBinding pressure) then
    pressures
  else
    pressure :: pressures

mutual
  def collectPressureExpr (limit : Nat) (chosen : SelectedPred) (owner : Owner)
      (phi : FMap) (layout : List Ident) (off : Nat) (pressures : List Pressure) :
      Expr Op → List Pressure
    | .lit _ => pressures
    | .var x =>
        if limit ≤ pressures.length || chosen owner x then pressures else
        match layout.findIdx? (· = x) with
        | some idx =>
            if off + idx < 16 then pressures
            else addPressure limit pressures {
              owner, name := x, kind := .read, depth := off + idx
              deficit := off + idx + 1 - 16
              batch := []
            }
        | none => pressures
    | .builtin _ args =>
        collectPressureArgs limit chosen owner phi layout off pressures args
    | .call f args =>
        match lookupF phi f with
        | some (info, _) =>
            collectPressureArgs limit chosen owner phi layout
              (off + 1 + info.rets) pressures args
        | none =>
            collectPressureArgs limit chosen owner phi layout off pressures args

  def collectPressureArgs (limit : Nat) (chosen : SelectedPred) (owner : Owner)
      (phi : FMap) (layout : List Ident) (off : Nat) (pressures : List Pressure) :
      List (Expr Op) → List Pressure
    | [] => pressures
    | e :: rest =>
        let pressures' :=
          collectPressureArgs limit chosen owner phi layout off pressures rest
        collectPressureExpr limit chosen owner phi layout (off + rest.length)
          pressures' e
end

def collectPressureAssigns (limit : Nat) (chosen : SelectedPred) (owner : Owner)
    (layout : List Ident) (pressures : List Pressure) :
    List Ident → List Pressure
  | [] => pressures
  | x :: xs =>
      let pressures' :=
        if limit ≤ pressures.length || chosen owner x then pressures else
        match layout.findIdx? (· = x) with
        | some idx =>
            if idx + xs.length < 16 then pressures
            else addPressure limit pressures {
              owner, name := x, kind := .write, depth := idx + xs.length
              deficit := idx + xs.length + 1 - 16
              batch := []
            }
        | none => pressures
      collectPressureAssigns limit chosen owner layout pressures' xs

def collectReturnCopyPressures (limit : Nat) (chosen : SelectedPred)
    (owner : Owner) (signature returns layout : List Ident)
    (pressures : List Pressure) : List Pressure :=
  returns.foldl (fun pressures r =>
    if limit ≤ pressures.length || !chosen owner r then pressures else
    match layout.findIdx? (· = r) with
    | some idx =>
        if idx < 16 then pressures else
        match (layout.take idx).find? fun x => !signature.contains x with
        | some candidate => addPressure limit pressures {
            owner, name := candidate, kind := .write, depth := idx
            deficit := idx + 1 - 16
            batch := []
          }
        | none => addPressure limit pressures {
            owner, name := r, kind := .write, depth := idx
            deficit := idx + 1 - 16
            batch := []
          }
    | none => pressures) pressures

mutual
  def collectPressureBlock (limit : Nat) (chosen : SelectedPred) (owner : Owner)
      (signature returns : List Ident) (phi : FMap) (layout : List Ident)
      (pressures : List Pressure) (body : Block Op) : List Pressure :=
    if limit ≤ pressures.length then pressures else
    let (scope, _) := hoistInfos 0 body
    (collectPressureStmts limit chosen owner signature returns (scope :: phi)
      layout pressures body).1
    termination_by 2 * sizeOf body + 1

  def collectPressureStmt (limit : Nat) (chosen : SelectedPred) (owner : Owner)
      (signature returns : List Ident) (phi : FMap) (layout : List Ident)
      (pressures : List Pressure) : Stmt Op → List Pressure × List Ident
    | .exprStmt e =>
        (collectPressureExpr limit chosen owner phi layout 0 pressures e, layout)
    | .letDecl xs val =>
        let pressures' := match val with
          | some e => collectPressureExpr limit chosen owner phi layout 0 pressures e
          | none => pressures
        (pressures', physicalDecls chosen owner xs ++ layout)
    | .assign xs e =>
        let pressures' :=
          collectPressureExpr limit chosen owner phi layout 0 pressures e
        (collectPressureAssigns limit chosen owner layout pressures' xs, layout)
    | .block body =>
        (collectPressureBlock limit chosen owner signature returns phi layout
          pressures body, layout)
    | .cond c body =>
        let pressures' :=
          collectPressureExpr limit chosen owner phi layout 0 pressures c
        (collectPressureBlock limit chosen owner signature returns phi layout
          pressures' body, layout)
    | .switch c cases dflt =>
        let pressures' :=
          collectPressureExpr limit chosen owner phi layout 0 pressures c
        let pressures' :=
          collectPressureCases limit chosen owner signature returns phi layout
            pressures' cases
        let pressures' := match dflt with
          | some body => collectPressureBlock limit chosen owner signature returns phi
              layout pressures' body
          | none => pressures'
        (pressures', layout)
    | .forLoop init c post body =>
        let (scope, _) := hoistInfos 0 init
        let phi' := scope :: phi
        let initResult :=
          collectPressureStmts limit chosen owner signature returns phi' layout
            pressures init
        let loopLayout := initResult.2
        let pressures' :=
          collectPressureExpr limit chosen owner phi' loopLayout 0 initResult.1 c
        let pressures' :=
          collectPressureBlock limit chosen owner signature returns phi' loopLayout
            pressures' body
        let pressures' :=
          collectPressureBlock limit chosen owner signature returns phi' loopLayout
            pressures' post
        (pressures', layout)
    | .funDef f ps rs body =>
        let pressures' := collectPressureBlock limit chosen (some f) (ps ++ rs) rs
          phi (ps ++ rs) pressures body
        (collectReturnCopyPressures limit chosen (some f) (ps ++ rs) rs (ps ++ rs)
          pressures', layout)
    | .leave =>
        (collectReturnCopyPressures limit chosen owner signature returns layout
          pressures, layout)
    | .break | .continue => (pressures, layout)
    termination_by s => 2 * sizeOf s

  def collectPressureStmts (limit : Nat) (chosen : SelectedPred) (owner : Owner)
      (signature returns : List Ident) (phi : FMap) (layout : List Ident)
      (pressures : List Pressure) : Block Op → List Pressure × List Ident
    | [] => (pressures, layout)
    | s :: rest =>
        if limit ≤ pressures.length then (pressures, layout) else
        let result := collectPressureStmt limit chosen owner signature returns phi
          layout pressures s
        collectPressureStmts limit chosen owner signature returns phi result.2
          result.1 rest
    termination_by ss => 2 * sizeOf ss

  def collectPressureCases (limit : Nat) (chosen : SelectedPred) (owner : Owner)
      (signature returns : List Ident) (phi : FMap) (layout : List Ident)
      (pressures : List Pressure) :
      List (Literal × Block Op) → List Pressure
    | [] => pressures
    | (_, body) :: rest =>
        if limit ≤ pressures.length then pressures else
        let pressures' := collectPressureBlock limit chosen owner signature returns phi
          layout pressures body
        collectPressureCases limit chosen owner signature returns phi layout
          pressures' rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def collectPressureBatch (selected : SpillSet) (body : Block Op) : List Pressure :=
  let (scope, _) := hoistInfos 0 body
  (collectPressureStmts pressureBatchLimit (selectedPred selected) none [] [] [scope]
    [] [] body).1.reverse

mutual
  def coupledStmt (owner : Owner) : Stmt Op → List (List SpillKey)
    | .block body | .cond _ body => coupledStmts owner body
    | .funDef f _ _ body => coupledStmts (some f) body
    | .letDecl xs _ | .assign xs _ =>
        if xs.length > 1 then [xs.map fun name => { owner, name }] else []
    | .switch _ cases dflt => coupledCases owner cases ++
        match dflt with | some body => coupledStmts owner body | none => []
    | .forLoop init _ post body =>
        coupledStmts owner init ++ coupledStmts owner post ++ coupledStmts owner body
    | _ => []
    termination_by s => 2 * sizeOf s

  def coupledStmts (owner : Owner) : Block Op → List (List SpillKey)
    | [] => []
    | s :: rest => coupledStmt owner s ++ coupledStmts owner rest
    termination_by ss => 2 * sizeOf ss + 1

  def coupledCases (owner : Owner) : List (Literal × Block Op) → List (List SpillKey)
    | [] => []
    | (_, body) :: rest => coupledStmts owner body ++ coupledCases owner rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def addUnique (xs : SpillSet) (x : SpillKey) : SpillSet :=
  if xs.contains x then xs else x :: xs

def addGroup (xs group : SpillSet) : SpillSet :=
  group.foldl addUnique xs

def closeGroupsOnce (groups : List SpillSet) (selected : SpillSet) : SpillSet :=
  groups.foldl (fun out group =>
    if group.any selected.contains then addGroup out group else out) selected

def closeGroups (groups : List SpillSet) : Nat → SpillSet → SpillSet
  | 0, selected => selected
  | fuel + 1, selected =>
      let selected' := closeGroupsOnce groups selected
      if selected'.length = selected.length then selected
      else closeGroups groups fuel selected'

/-- Executable certificate that every coupled multi-result group is selected
all-or-none.  The rewrite relies on this property: a tuple is either retained
entirely on the operand stack or distributed entirely into spill slots. -/
def groupsClosedCheck (groups : List SpillSet) (selected : SpillSet) : Bool :=
  groups.all fun group =>
    decide group.Nodup &&
      if group.any selected.contains then group.all selected.contains else true

def selectLoop (body : Block Op) (groups : List SpillSet) :
    Nat → SpillSet → Option SpillSet
  | 0, _ => none
  | fuel + 1, selected =>
      match collectPressureBatch selected body with
      | [] =>
          match firstPressure selected body with
          | none => if selected.isEmpty then none else some selected
          | some pressure =>
              let requested :=
                addUnique selected { owner := pressure.owner, name := pressure.name }
              let selected' := closeGroups groups fuel requested
              if selected'.length = selected.length then none
              else selectLoop body groups fuel selected'
      | pressures =>
          let requested := pressures.foldl (fun out pressure =>
            addUnique out { owner := pressure.owner, name := pressure.name }) selected
          let selected' := closeGroups groups fuel
            requested
          if selected'.length = selected.length then none
          else selectLoop body groups fuel selected'

def selectSpills (body : Block Op) : Option SpillSet :=
  let names := declaredStmts body
  selectLoop body (coupledStmts none body) (names.length + 1) []

/-! ## Lexical slot coloring inside one frame -/

structure LocalAlloc where
  next : Nat := 0
  peak : Nat := 0
  slots : List (SpillKey × Nat) := []
  deriving Repr

def allocName (selected : SpillSet) (owner : Owner) (st : LocalAlloc)
    (x : Ident) : LocalAlloc :=
  let key : SpillKey := { owner, name := x }
  if selected.contains key then {
    next := st.next + 1
    peak := max st.peak (st.next + 1)
    slots := (key, st.next) :: st.slots
  } else st

def allocNames (selected : SpillSet) (owner : Owner) : LocalAlloc → List Ident → LocalAlloc
  | st, [] => st
  | st, x :: xs => allocNames selected owner (allocName selected owner st x) xs

mutual
  def allocStmt (selected : SpillSet) (owner : Owner) (st : LocalAlloc) :
      Stmt Op → LocalAlloc
    | .letDecl xs _ => allocNames selected owner st xs
    | .block body | .cond _ body => allocScope selected owner st body
    | .switch _ cases dflt =>
        let st1 := allocCases selected owner st cases
        match dflt with | some body => allocScope selected owner st1 body | none => st1
    | .forLoop init _ post body =>
        let outer := st.next
        let loop := allocStmts selected owner st init
        let afterBody := allocScope selected owner loop body
        let afterPost := allocScope selected owner afterBody post
        { afterPost with next := outer }
    | .funDef _ _ _ _ => st
    | _ => st
    termination_by s => 2 * sizeOf s

  def allocStmts (selected : SpillSet) (owner : Owner) (st : LocalAlloc) :
      Block Op → LocalAlloc
    | [] => st
    | s :: rest => allocStmts selected owner (allocStmt selected owner st s) rest
    termination_by ss => 2 * sizeOf ss

  def allocScope (selected : SpillSet) (owner : Owner) (st : LocalAlloc)
      (body : Block Op) : LocalAlloc :=
    let next := st.next
    { allocStmts selected owner st body with next }
    termination_by 2 * sizeOf body + 1

  def allocCases (selected : SpillSet) (owner : Owner) (st : LocalAlloc) :
      List (Literal × Block Op) → LocalAlloc
    | [] => st
    | (_, body) :: rest =>
        allocCases selected owner (allocScope selected owner st body) rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

structure Frame where
  owner : Owner
  params : List Ident
  returns : List Ident
  body : Block Op

/-! ## Executable lexical-lifetime traces

The allocator restores `next` when a lexical scope ends, so historical slot
assignments may intentionally share a color.  `FrameLives` records maximal
sets of selected bindings along every lexical control-flow path.  Every live
environment on that path is a subset of one of these sets.  Retaining only
maximal sets avoids a quadratic trace for long straight-line scopes.  The
sets are retained in `Layout` and checked after placement, making scope reuse
an explicit certificate rather than an implicit allocator assumption.

Loop-initializer declarations are kept in `loopLive` while the condition,
body, and post blocks are traced.  Body and post declarations are scoped
independently.  Function parameters and return variables form the initial live
set of their frame; nested function definitions are traced in their own frame.
-/

def selectedKeys (selected : SpillSet) (owner : Owner) (xs : List Ident) : SpillSet :=
  xs.filterMap fun name =>
    let key : SpillKey := { owner, name }
    if selected.contains key then some key else none

mutual
  def liveStmt (selected : SpillSet) (owner : Owner) (live : SpillSet) :
      Stmt Op → List SpillSet × SpillSet
    | .letDecl xs _ =>
        let live' := selectedKeys selected owner xs ++ live
        ([], live')
    | .block body | .cond _ body =>
        (liveScope selected owner live body, live)
    | .switch _ cases dflt =>
        let caseSets := liveCases selected owner live cases
        let defaultSets := match dflt with
          | some body => liveScope selected owner live body
          | none => []
        (caseSets ++ defaultSets, live)
    | .forLoop init _ post body =>
        let initTrace := liveStmts selected owner live init
        let loopLive := initTrace.2
        let bodySets := liveScope selected owner loopLive body
        let postSets := liveScope selected owner loopLive post
        (initTrace.1 ++ bodySets ++ postSets, live)
    | .funDef _ _ _ _ => ([], live)
    | .exprStmt _ => ([], live)
    | .assign _ _ => ([], live)
    | .break => ([], live)
    | .continue => ([], live)
    | .leave => ([], live)
    termination_by s => 2 * sizeOf s

  def liveStmts (selected : SpillSet) (owner : Owner) (live : SpillSet) :
      Block Op → List SpillSet × SpillSet
    | [] => ([live], live)
    | stmt :: rest =>
        let stmtTrace := liveStmt selected owner live stmt
        let restTrace := liveStmts selected owner stmtTrace.2 rest
        (stmtTrace.1 ++ restTrace.1, restTrace.2)
    termination_by body => 2 * sizeOf body

  def liveScope (selected : SpillSet) (owner : Owner) (live : SpillSet)
      (body : Block Op) : List SpillSet :=
    (liveStmts selected owner live body).1
    termination_by 2 * sizeOf body + 1

  def liveCases (selected : SpillSet) (owner : Owner) (live : SpillSet) :
      List (Literal × Block Op) → List SpillSet
    | [] => []
    | (_, body) :: rest =>
        liveScope selected owner live body ++ liveCases selected owner live rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

structure FrameLives where
  owner : Owner
  sets : List SpillSet
  deriving Repr

def frameLives (selected : SpillSet) (frame : Frame) : FrameLives :=
  let initial := selectedKeys selected frame.owner (frame.params ++ frame.returns)
  { owner := frame.owner
    sets := (liveStmts selected frame.owner initial frame.body).1 }

mutual
  def nestedFramesStmt : Stmt Op → List Frame
    | .funDef f ps rs body =>
        { owner := some f, params := ps, returns := rs, body } :: nestedFramesStmts body
    | .block body | .cond _ body => nestedFramesStmts body
    | .switch _ cases dflt => nestedFramesCases cases ++
        match dflt with | some body => nestedFramesStmts body | none => []
    | .forLoop init _ post body =>
        nestedFramesStmts init ++ nestedFramesStmts post ++ nestedFramesStmts body
    | _ => []
    termination_by s => 2 * sizeOf s

  def nestedFramesStmts : Block Op → List Frame
    | [] => []
    | s :: rest => nestedFramesStmt s ++ nestedFramesStmts rest
    termination_by ss => 2 * sizeOf ss + 1

  def nestedFramesCases : List (Literal × Block Op) → List Frame
    | [] => []
    | (_, body) :: rest => nestedFramesStmts body ++ nestedFramesCases rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def frames (body : Block Op) : List Frame :=
  { owner := none, params := [], returns := [], body } :: nestedFramesStmts body

mutual
  def frameNamesStmt : Stmt Op → List Ident
    | .funDef _ _ _ _ => []
    | .letDecl xs _ => xs
    | .block body | .cond _ body => frameNamesStmts body
    | .switch _ cases dflt => frameNamesCases cases ++
        match dflt with | some body => frameNamesStmts body | none => []
    | .forLoop init _ post body =>
        frameNamesStmts init ++ frameNamesStmts post ++ frameNamesStmts body
    | _ => []
    termination_by s => 2 * sizeOf s

  def frameNamesStmts : Block Op → List Ident
    | [] => []
    | s :: rest => frameNamesStmt s ++ frameNamesStmts rest
    termination_by ss => 2 * sizeOf ss + 1

  def frameNamesCases : List (Literal × Block Op) → List Ident
    | [] => []
    | (_, body) :: rest => frameNamesStmts body ++ frameNamesCases rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def frameNames (frame : Frame) : List Ident :=
  frame.params ++ frame.returns ++ frameNamesStmts frame.body

def framesWF (fs : List Frame) : Bool :=
  (fs.map (·.owner)).Nodup

/-- Every function calling-convention environment has one unambiguous binding
per parameter/return name.  The backend already rejects duplicate signatures;
the spilling simulation needs the same fact before executing its prologue. -/
def frameSignaturesWF (fs : List Frame) : Bool :=
  fs.all fun frame => decide (frame.params ++ frame.returns).Nodup

def selectedWF (fs : List Frame) (selected : SpillSet) : Bool :=
  selected.all fun key =>
    match fs.find? fun frame => frame.owner = key.owner with
    | some frame => (frameNames frame).count key.name = 1
    | none => false

mutual
  def callsExpr : Expr Op → List Ident
    | .lit _ | .var _ => []
    | .builtin _ args => callsArgs args
    | .call f args => f :: callsArgs args

  def callsArgs : List (Expr Op) → List Ident
    | [] => []
    | e :: rest => callsExpr e ++ callsArgs rest
end

mutual
  def frameCallsStmt : Stmt Op → List Ident
    | .funDef _ _ _ _ => []
    | .block body => frameCallsStmts body
    | .cond condition body => callsExpr condition ++ frameCallsStmts body
    | .letDecl _ val => val.map callsExpr |>.getD []
    | .assign _ e | .exprStmt e => callsExpr e
    | .switch e cases dflt => callsExpr e ++ frameCallsCases cases ++
        match dflt with | some body => frameCallsStmts body | none => []
    | .forLoop init c post body => frameCallsStmts init ++ callsExpr c ++
        frameCallsStmts post ++ frameCallsStmts body
    | .break | .continue | .leave => []
    termination_by s => 2 * sizeOf s

  def frameCallsStmts : Block Op → List Ident
    | [] => []
    | s :: rest => frameCallsStmt s ++ frameCallsStmts rest
    termination_by ss => 2 * sizeOf ss + 1

  def frameCallsCases : List (Literal × Block Op) → List Ident
    | [] => []
    | (_, body) :: rest => frameCallsStmts body ++ frameCallsCases rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

structure FrameInfo where
  owner : Owner
  alloc : LocalAlloc
  callees : List Owner
  deriving Repr

def frameInfo (selected : SpillSet) (defined : List Ident) (frame : Frame) : FrameInfo :=
  let initial := allocNames selected frame.owner {} (frame.params ++ frame.returns)
  let alloc := allocStmts selected frame.owner initial frame.body
  let callees := (frameCallsStmts frame.body).filter defined.contains |>.eraseDups |>.map some
  { owner := frame.owner, alloc, callees }

def frameInfos (selected : SpillSet) (body : Block Op) : List FrameInfo :=
  let fs := frames body
  let defined := fs.filterMap (·.owner)
  fs.map (frameInfo selected defined)

def findInfo? (infos : List FrameInfo) (owner : Owner) : Option FrameInfo :=
  infos.find? fun info => info.owner = owner

abbrev NeedCache := List (Owner × Nat)

def cachedNeed? (cache : NeedCache) (owner : Owner) : Option Nat :=
  (cache.find? fun item => item.1 = owner).map Prod.snd

def needFrame (infos : List FrameInfo) : Nat → List Owner → NeedCache → Owner →
    Option (Nat × NeedCache)
  | 0, _, _, _ => none
  | fuel + 1, visiting, cache, owner =>
      match cachedNeed? cache owner with
      | some need => some (need, cache)
      | none =>
          if visiting.contains owner then none else do
          let info ← findInfo? infos owner
          let (childPeak, cache') ← info.callees.foldlM (fun (peak, cache) callee => do
            let (need, cache') ← needFrame infos fuel (owner :: visiting) cache callee
            pure (max peak need, cache')) (0, cache)
          let need := childPeak + info.alloc.peak
          some (need, (owner, need) :: cache')

def allNeeds (infos : List FrameInfo) (fuel : Nat) :
    List Owner → NeedCache → Option (Nat × NeedCache)
  | [], cache => some (0, cache)
  | owner :: rest, cache => do
      let (need, cache') ← needFrame infos fuel [] cache owner
      let (peak, cache'') ← allNeeds infos fuel rest cache'
      some (max need peak, cache'')

def maxCached (cache : NeedCache) (owners : List Owner) : Nat :=
  owners.foldl (fun peak owner => max peak ((cachedNeed? cache owner).getD 0)) 0

def placeFrame (base : Nat) (cache : NeedCache) (info : FrameInfo) : SlotMap :=
  let childPeak := maxCached cache info.callees
  info.alloc.slots.map fun (name, color) =>
    (name, base + 32 * (childPeak + color))

def placeFrames (base : Nat) (cache : NeedCache) (infos : List FrameInfo) : SlotMap :=
  infos.flatMap (placeFrame base cache)

structure Layout where
  slots : SlotMap
  /-- Maximum simultaneously reserved words along one lexical/call path.
  This is deliberately unrelated to `selected.length`: sibling scopes and
  sibling callees reuse addresses after their environments are restored. -/
  words : Nat
  infos : List FrameInfo
  cache : NeedCache
  lives : List FrameLives
  deriving Repr

def buildLayout (base : Nat) (selected : SpillSet) (body : Block Op) : Option Layout := do
  let fs := frames body
  let infos := frameInfos selected body
  let lives := fs.map (frameLives selected)
  let owners := infos.map (·.owner)
  let (words, cache) ← allNeeds infos (infos.length + 1) owners []
  some { slots := placeFrames base cache infos, words, infos, cache, lives }

def slotForKey? (slots : SlotMap) (key : SpillKey) : Option Nat :=
  (slots.find? fun item => item.1 = key).map Prod.snd

def slotFor? (slots : SlotMap) (owner : Owner) (x : Ident) : Option Nat :=
  slotForKey? slots { owner, name := x }

def localAllocCheck (alloc : LocalAlloc) : Bool :=
  decide (alloc.next ≤ alloc.peak) &&
    alloc.slots.all fun item => decide (item.2 < alloc.peak)

def slotsForKeys? (slots : SlotMap) : SpillSet → Option (List Nat)
  | [] => some []
  | key :: rest => do
      let address ← slotForKey? slots key
      let addresses ← slotsForKeys? slots rest
      some (address :: addresses)

def liveSetCheck (slots : SlotMap) (keys : SpillSet) : Bool :=
  match slotsForKeys? slots keys with
  | some addresses => decide keys.Nodup && decide addresses.Nodup
  | none => false

def lexicalLayoutCheck (layout : Layout) : Bool :=
  (layout.lives.map (fun trace => trace.owner)).Nodup &&
    layout.lives.all fun trace => trace.sets.all (liveSetCheck layout.slots)

/-- Executable proof boundary for the call-path allocator.  Cache and frame
owners are unique, every direct callee has a cached need, every frame cache
entry satisfies `calleePeak + localPeak`, and `words` is the maximum cached
frame need. -/
def needLayoutCheck (layout : Layout) : Bool :=
  ((layout.infos.map (fun info => info.owner)).Nodup &&
    (layout.cache.map Prod.fst).Nodup &&
    (layout.infos.all fun info =>
      localAllocCheck info.alloc &&
        ((info.alloc.slots.all fun item => item.1.owner == info.owner) &&
          ((info.callees.all fun callee => (cachedNeed? layout.cache callee).isSome) &&
            cachedNeed? layout.cache info.owner ==
              some (maxCached layout.cache info.callees + info.alloc.peak)))) &&
    layout.words == maxCached layout.cache (layout.infos.map fun info => info.owner)) &&
    lexicalLayoutCheck layout

/-- Executable boundary check retained in every successful layout certificate.
It makes address containment/alignment and selection coverage independent of
the allocator implementation details.  `needLayoutCheck` additionally pins
the lexical/call-path recurrence used to justify address reuse. -/
def layoutCheck (base reserved : Nat) (selected : SpillSet) (layout : Layout) : Bool :=
  ((((needLayoutCheck layout &&
    (layout.slots.all fun item =>
        selected.contains item.1 && decide (base ≤ item.2) &&
          decide (item.2 + 32 ≤ reserved) && decide ((item.2 - base) % 32 = 0))) &&
      (selected.all fun key => (layout.slots.find? fun item => item.1 = key).isSome)) &&
    decide selected.Nodup) && decide (layout.slots.map Prod.fst).Nodup)

/-! Small allocation guards pin the distinction between selected bindings and
reserved words.  Sibling lexical scopes and sibling callees reuse addresses;
only simultaneously active caller/callee frames are stacked. -/

private def lexicalReuseBody : Block Op :=
  [.letDecl ["outer"] none,
   .block [.letDecl ["left"] none],
   .block [.letDecl ["right"] none]]

private def lexicalReuseSelected : SpillSet :=
  [{ owner := none, name := "outer" },
   { owner := none, name := "left" },
   { owner := none, name := "right" }]

#guard match buildLayout 128 lexicalReuseSelected lexicalReuseBody with
  | some layout =>
      layout.words == 2 && slotFor? layout.slots none "outer" == some 128 &&
        slotFor? layout.slots none "left" == some 160 &&
        slotFor? layout.slots none "right" == some 160
  | none => false

private def callPathReuseBody : Block Op :=
  [.letDecl ["root"] none,
   .exprStmt (.call "leftFun" []),
   .exprStmt (.call "rightFun" []),
   .funDef "leftFun" [] [] [.letDecl ["left"] none],
   .funDef "rightFun" [] [] [.letDecl ["right"] none]]

private def callPathReuseSelected : SpillSet :=
  [{ owner := none, name := "root" },
   { owner := some "leftFun", name := "left" },
   { owner := some "rightFun", name := "right" }]

#guard match buildLayout 128 callPathReuseSelected callPathReuseBody with
  | some layout =>
      layout.words == 2 && slotFor? layout.slots none "root" == some 160 &&
        slotFor? layout.slots (some "leftFun") "left" == some 128 &&
        slotFor? layout.slots (some "rightFun") "right" == some 128
  | none => false

/-! ## Rewrite using the selected, colored locations -/

mutual
  def rewriteExpr (slots : SlotMap) (owner : Owner) : Expr Op → Expr Op
    | .lit l => .lit l
    | .var x =>
        match slotFor? slots owner x with
        | some slot => load slot
        | none => .var x
    | .builtin op args => .builtin op (rewriteArgs slots owner args)
    | .call f args => .call f (rewriteArgs slots owner args)

  def rewriteArgs (slots : SlotMap) (owner : Owner) : List (Expr Op) → List (Expr Op)
    | [] => []
    | e :: rest => rewriteExpr slots owner e :: rewriteArgs slots owner rest
end

def initParams (slots : SlotMap) (owner : Owner) (ps : List Ident) : Block Op :=
  ps.filterMap fun p => (slotFor? slots owner p).map fun slot => store slot (.var p)

def initReturns (slots : SlotMap) (owner : Owner) (rs : List Ident) : Block Op :=
  rs.filterMap fun r => (slotFor? slots owner r).map fun slot => store slot (word 0)

def copyBackReturns (slots : SlotMap) (owner : Owner) (rs : List Ident) : Block Op :=
  rs.filterMap fun r => (slotFor? slots owner r).map fun slot => .assign [r] (load slot)

def targetSlots? (slots : SlotMap) (owner : Owner) : List Ident → Option (List Nat)
  | [] => some []
  | x :: xs => do
      let slot ← slotFor? slots owner x
      let rest ← targetSlots? slots owner xs
      some (slot :: rest)

def tempPrefix : String := "__$spilltmp_"

def tempName (owner : Owner) (x : Ident) : Ident :=
  let ownerName := match owner with | some f => f | none => "root"
  tempPrefix ++ ownerName ++ "_" ++ x

mutual
  def rewriteStmt (slots : SlotMap) (owner : Owner) (exitCopies : Block Op) :
      Stmt Op → Block Op
    | .block body => [.block (rewriteStmts slots owner exitCopies body)]
    | .funDef f ps rs body =>
        let owner' := some f
        let copies := copyBackReturns slots owner' rs
        let prologue := initParams slots owner' ps ++ initReturns slots owner' rs
        let rewrittenBody := rewriteStmts slots owner' copies body
        [.funDef f ps rs (prologue ++ [.block rewrittenBody] ++ copies)]
    | .letDecl [x] val =>
        let val' := (val.map (rewriteExpr slots owner)).getD (word 0)
        match slotFor? slots owner x with
        | some slot => [store slot val']
        | none => [.letDecl [x] (some val')]
    | .letDecl xs val =>
        match targetSlots? slots owner xs with
        | some targets =>
            match val with
            | none => targets.map fun target => store target (word 0)
            | some e =>
                let temps := xs.map (tempName owner)
                [.block (.letDecl temps (some (rewriteExpr slots owner e)) ::
                  distributeTemps targets temps)]
        | none => [.letDecl xs (val.map (rewriteExpr slots owner))]
    | .assign [x] e =>
        match slotFor? slots owner x with
        | some slot => [store slot (rewriteExpr slots owner e)]
        | none => [.assign [x] (rewriteExpr slots owner e)]
    | .assign xs e =>
        match targetSlots? slots owner xs with
        | some targets =>
            let temps := xs.map (tempName owner)
            [.block (.letDecl temps (some (rewriteExpr slots owner e)) ::
              distributeTemps targets temps)]
        | none => [.assign xs (rewriteExpr slots owner e)]
    | .cond c body =>
        [.cond (rewriteExpr slots owner c) (rewriteStmts slots owner exitCopies body)]
    | .switch c cases dflt =>
        [.switch (rewriteExpr slots owner c) (rewriteCases slots owner exitCopies cases)
          (match dflt with
          | some body => some (rewriteStmts slots owner exitCopies body)
          | none => none)]
    | .forLoop init c post body =>
        [.forLoop (rewriteStmts slots owner exitCopies init) (rewriteExpr slots owner c)
          (rewriteStmts slots owner exitCopies post) (rewriteStmts slots owner exitCopies body)]
    | .exprStmt e => [.exprStmt (rewriteExpr slots owner e)]
    | .break => [.break]
    | .continue => [.continue]
    | .leave => if exitCopies.isEmpty then [.leave] else [.block (exitCopies ++ [.leave])]
    termination_by s => 2 * sizeOf s

  def rewriteStmts (slots : SlotMap) (owner : Owner) (exitCopies : Block Op) :
      Block Op → Block Op
    | [] => []
    | s :: rest =>
        rewriteStmt slots owner exitCopies s ++ rewriteStmts slots owner exitCopies rest
    termination_by ss => 2 * sizeOf ss + 1

  def rewriteCases (slots : SlotMap) (owner : Owner) (exitCopies : Block Op) :
      List (Literal × Block Op) → List (Literal × Block Op)
    | [] => []
    | (l, body) :: rest =>
        (l, rewriteStmts slots owner exitCopies body) ::
          rewriteCases slots owner exitCopies rest
    termination_by cases => 2 * sizeOf cases + 1
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

structure Result where
  block : Block Op
  base : Nat
  reserved : Nat
  selection : SpillSet
  layout : Layout
  deriving Repr

def spillBlock? (body : Block Op) : Option Result := do
  if containsMsizeStmts body then none else
  let guards ← collectMemoryGuardsStmts? body
  let base ← guards.head?
  if guards.isEmpty || !guards.all (· = base) then none else
  let selected ← selectSpills body
  let provisional ← buildLayout base selected body
  if provisional.words = 0 then none else
  let reserved := base + 32 * provisional.words
  if !(reserved < 2 ^ 256) then none else
  /- Rebuild every proof-facing policy certificate on the exact source block
  interpreted by `GuardedRun`.  Guard resolution changes only the marker
  literal, but checking the resolved tree directly avoids asking the semantic
  proof to reconstruct that shape-preservation fact. -/
  let guarded := resolveMemoryGuardStmts base reserved body
  let guardedFrames := frames guarded
  if !framesWF guardedFrames then none else
  if !frameSignaturesWF guardedFrames then none else
  if !selectedWF guardedFrames selected then none else
  if !groupsClosedCheck (coupledStmts none guarded) selected then none else
  let layout ← buildLayout base selected guarded
  if layout.words != provisional.words then none else
  if !layoutCheck base reserved selected layout then none else
  if (declaredStmts guarded).any (·.startsWith tempPrefix) then none else
  let rewritten := rewriteStmts layout.slots none [] guarded
  if (firstPressure [] rewritten).isSome then none else
  some {
    block := rewritten
    base, reserved, selection := selected, layout
  }

inductive ObjectPlan where
  | mk (code : Option Result) (subs : List ObjectPlan)
  deriving Repr

structure ObjectResult where
  object : Object Op
  plan : ObjectPlan
  selected : Nat

/-- Resolve valid guards in an object code block that itself needs no spill.
The returned pointer remains the original base, exactly matching the ordinary
`memoryguard(k) -> k` compatibility lowering.  This is needed when a sibling
object spills: the recursive fallback must still eliminate parser-level guard
markers throughout the whole object tree before ordinary object compilation. -/
def resolveUnspilledBlock? (body : Block Op) : Option (Block Op) := do
  let guards ← collectMemoryGuardsStmts? body
  match guards with
  | [] => some body
  | base :: _ =>
      if guards.all (· = base) then
        some (resolveMemoryGuardStmts base base body)
      else none

mutual
  def spillObject : Object Op → ObjectResult
    | .mk name code subs segs =>
        let codeResult := spillBlock? code
        let (subs', childPlans, childCount) := spillObjects subs
        let code' := match codeResult with
          | some result => result.block
          | none => (resolveUnspilledBlock? code).getD code
        let ownCount := codeResult.map (fun r => r.selection.length) |>.getD 0
        { object := .mk name code' subs' segs,
          plan := .mk codeResult childPlans,
          selected := ownCount + childCount }

  def spillObjects : List (Object Op) → List (Object Op) × List ObjectPlan × Nat
    | [] => ([], [], 0)
    | o :: rest =>
        let o' := spillObject o
        let (rest', plans, restCount) := spillObjects rest
        (o'.object :: rest', o'.plan :: plans, o'.selected + restCount)
end

/-! ### Pairing guarded spill nodes with an ordinary verified fallback

An object can contain code sections with no memory-guard authority.  They must
not be spilled, but they also need not fall back to the large raw block: the
caller already has a semantics-preserving, recursively optimized ordinary
object with the same object/data shape.  The paired constructor uses that code
only at nodes where spilling is unavailable, while guarded nodes still use the
spill result.  Existing compile candidates run before this path, so it cannot
change bytecode or gas for an already-compilable source.
-/

mutual
  def spillObjectWithFallback : Object Op → Object Op → Option ObjectResult
    | .mk rawName rawCode rawSubs rawSegs,
        .mk fallbackName fallbackCode fallbackSubs _ => do
      if rawName != fallbackName then none else
      let (subs, childPlans, childCount) ←
        spillObjectsWithFallback rawSubs fallbackSubs
      let codeResult := spillBlock? rawCode
      let code := match codeResult with
        | some result => result.block
        | none => fallbackCode
      let ownCount := codeResult.map (fun result => result.selection.length) |>.getD 0
      some {
        object := .mk rawName code subs rawSegs
        plan := .mk codeResult childPlans
        selected := ownCount + childCount }
    termination_by raw fallback => sizeOf raw + sizeOf fallback

  def spillObjectsWithFallback : List (Object Op) → List (Object Op) →
      Option (List (Object Op) × List ObjectPlan × Nat)
    | [], [] => some ([], [], 0)
    | raw :: rawRest, fallback :: fallbackRest => do
      let head ← spillObjectWithFallback raw fallback
      let (tail, plans, count) ←
        spillObjectsWithFallback rawRest fallbackRest
      some (head.object :: tail, head.plan :: plans, head.selected + count)
    | _, _ => none
    termination_by raws fallbacks => sizeOf raws + sizeOf fallbacks
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

/-! ## Executable acceptance guards -/

private def pressureNames : List Ident :=
  (List.range 17).map fun i => s!"pressure_{i}"

private def guardedPressureBlock : Block Op :=
  .exprStmt (.builtin .mstore [word 64, .call "memoryguard" [word 128]]) ::
    pressureNames.map (fun x => .letDecl [x] none) ++
    [.exprStmt (.builtin .sstore [word 0, .var "pressure_0"])]

#guard match spillBlock? guardedPressureBlock with
  | some result => result.layout.words == 1 && result.selection.length == 1 &&
      (compileProgram result.block).isSome
  | none => false

private def guardedNoPressureBlock : Block Op :=
  [.exprStmt (.builtin .mstore [word 64, .call "memoryguard" [word 128]])]

private def mixedPressureObject : Object Op :=
  .mk "root" guardedPressureBlock
    [.mk "child" guardedNoPressureBlock [] []] []

/- Once any code block selects the recursive object fallback, valid guard
markers in no-spill siblings must still be resolved before object compilation. -/
#guard match resolveUnspilledBlock? guardedNoPressureBlock with
  | some block => collectMemoryGuardsStmts? block == some []
  | none => false
#guard (spillObject mixedPressureObject).selected == 1

private def unguardedPressureBlock : Block Op :=
  pressureNames.map (fun x => .letDecl [x] none) ++
    [.exprStmt (.builtin .sstore [word 0, .var "pressure_0"])]

private def hybridFallbackBlock : Block Op :=
  [.letDecl ["kept"] (some (word 7)),
   .exprStmt (.builtin .sstore [word 0, .var "kept"])]

private def hybridRawObject : Object Op :=
  .mk "root" guardedPressureBlock
    [.mk "child" unguardedPressureBlock [] []] []

private def hybridFallbackObject : Object Op :=
  .mk "root" [] [.mk "child" hybridFallbackBlock [] []] []

/- Guarded nodes spill, while unguarded nodes use the paired verified fallback
code without acquiring memory authority. -/
#guard match spillObjectWithFallback hybridRawObject hybridFallbackObject with
  | some result =>
      result.selected == 1 &&
        match result.object with
        | .mk _ rootCode [.mk _ childCode [] []] [] =>
            (firstPressure [] rootCode).isNone &&
              reprStr childCode == reprStr hybridFallbackBlock
        | _ => false
  | none => false

private def recursivePressureBlock : Block Op :=
  [.exprStmt (.builtin .mstore [word 64, .call "memoryguard" [word 128]]),
   .funDef "recur" [] []
      (pressureNames.map (fun x => .letDecl [x] none) ++
       [.exprStmt (.builtin .sstore [word 0, .var "pressure_0"]),
        .exprStmt (.call "recur" [])])]

#guard (spillBlock? recursivePressureBlock).isNone

private def duplicateSignaturePressureBlock : Block Op :=
  [.exprStmt (.builtin .mstore [word 64, .call "memoryguard" [word 128]]),
   .funDef "badSignature" ["duplicate"] ["duplicate"]
      (pressureNames.map (fun x => .letDecl [x] none) ++
       [.exprStmt (.builtin .sstore [word 0, .var "pressure_0"])])]

/- The spill prologue and the ordinary backend both require unambiguous
parameter/return bindings.  Reject the duplicate signature before rewriting. -/
#guard (spillBlock? duplicateSignaturePressureBlock).isNone

private def overflowingPressureBlock : Block Op :=
  .exprStmt (.builtin .mstore
      [word 64, .call "memoryguard" [word (2 ^ 256 - 16)]]) ::
    pressureNames.map (fun x => .letDecl [x] none) ++
    [.exprStmt (.builtin .sstore [word 0, .var "pressure_0"])]

#guard (spillBlock? overflowingPressureBlock).isNone

private def msizePressureBlock : Block Op :=
  .exprStmt (.builtin .mstore [word 64, .call "memoryguard" [word 128]]) ::
    .exprStmt (.builtin .msize []) ::
    pressureNames.map (fun x => .letDecl [x] none) ++
    [.exprStmt (.builtin .sstore [word 0, .var "pressure_0"])]

#guard (spillBlock? msizePressureBlock).isNone

end YulEvmCompiler.Optimizer.MemorySpillSelect
