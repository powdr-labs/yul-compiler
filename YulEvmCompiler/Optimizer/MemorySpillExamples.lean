import YulEvmCompiler.Examples
import YulEvmCompiler.ObjectCompile
import YulEvmCompiler.Optimizer.Implementation.MemorySpillSelect
set_option warningAsError true
/-!
# Executable memory-spilling regressions

Focused differentials for the binding and control-flow shapes whose rewrite is
easy to get subtly wrong.  Each check compares the observable storage of the
identity-resolved guarded source, the compiler-chosen guard resolution, and
the spilled source.  It then compiles and executes the spilled program through
the ordinary EVM backend.
-/

namespace YulEvmCompiler.Optimizer.MemorySpillExamples

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler
open MemorySpill
open MemorySpillSelect

def lit (n : Nat) : Expr Op := .lit (.number n)

def builtin (op : Op) (args : List (Expr Op)) : Expr Op := .builtin op args

def guard : Stmt Op :=
  .exprStmt (builtin .mstore [lit 64, .call "memoryguard" [lit 128]])

def decl (name : Ident) (value : Nat) : Stmt Op :=
  .letDecl [name] (some (lit value))

def fillers (stem : String) (count : Nat) : Block Op :=
  (List.range count).map fun i => decl (stem ++ toString i) (i + 1)

def store (key : Nat) (value : Expr Op) : Stmt Op :=
  .exprStmt (builtin .sstore [lit key, value])

def run? (prog : Block Op) : Option EvmState :=
  match Interp.run YulSemantics.EVM.exec 500000 prog EvmState.init with
  | .ok (_, st, _) => some st
  | _ => none

def storageMatches (st : EvmState) (expected : List (Nat × Nat)) : Bool :=
  expected.all fun item => (st.storage (BitVec.ofNat 256 item.1)).toNat == item.2

def sameTerminalView (a b : EvmState) : Bool :=
  a.returndata == b.returndata && a.logs == b.logs &&
    a.selfdestructs == b.selfdestructs && a.halted == b.halted

def checkSpill (raw : Block Op) (expected : List (Nat × Nat)) : Bool :=
  match spillBlock? raw with
  | none => false
  | some result =>
      let identity := resolveMemoryGuardStmts result.base result.base raw
      let chosen := resolveMemoryGuardStmts result.base result.reserved raw
      match run? identity, run? chosen, run? result.block with
      | some original, some guarded, some spilled =>
          storageMatches original expected && storageMatches guarded expected &&
            storageMatches spilled expected && sameTerminalView original guarded &&
            sameTerminalView guarded spilled &&
            YulEvmCompiler.Examples.agreeOn result.block (expected.map Prod.fst)
      | _, _, _ => false

def checkReturnSpill (raw : Block Op) : Bool :=
  match spillBlock? raw with
  | none => false
  | some result =>
      let identity := resolveMemoryGuardStmts result.base result.base raw
      let chosen := resolveMemoryGuardStmts result.base result.reserved raw
      match run? identity, run? chosen, run? result.block with
      | some original, some guarded, some spilled =>
          sameTerminalView original guarded && sameTerminalView guarded spilled &&
            (match spilled.halted with | some (.ret, _) => true | _ => false) &&
            YulEvmCompiler.Examples.agreeReturn result.block []
      | _, _, _ => false

def selectsAll (raw : Block Op) (owner : Owner) (names : List Ident) : Bool :=
  match spillBlock? raw with
  | some result => names.all fun name => result.selection.contains { owner, name }
  | none => false

/-! A selected singleton is zero-initialized, assigned, read, and reassigned. -/
def singletonLetAssign : Block Op :=
  [guard, .letDecl ["x"] none, .assign ["x"] (lit 5)] ++
    fillers "single_filler_" 16 ++
    [.assign ["x"] (builtin .add [.var "x", lit 7]), store 0 (.var "x")]

#guard checkSpill singletonLetAssign [(0, 12)]
#guard selectsAll singletonLetAssign none ["x"]

/-! A selected multi-result declaration is distributed through fresh temps. -/
def multiLet : Block Op :=
  [guard,
   .funDef "pair" [] ["a", "b"]
      [.assign ["a"] (lit 3), .assign ["b"] (lit 4)],
   .letDecl ["x", "y"] (some (.call "pair" []))] ++
    fillers "multi_let_filler_" 15 ++
    [store 0 (.var "x"), store 1 (.var "y")]

#guard checkSpill multiLet [(0, 3), (1, 4)]
#guard selectsAll multiLet none ["x", "y"]

/-! A zero-initialized selected tuple receives a multi-result assignment. -/
def multiAssign : Block Op :=
  [guard,
   .funDef "swapped" [] ["a", "b"]
      [.assign ["a"] (lit 9), .assign ["b"] (lit 8)],
   .letDecl ["x", "y"] none] ++
    fillers "multi_assign_filler_" 15 ++
    [.assign ["x", "y"] (.call "swapped" []),
     store 0 (.var "x"), store 1 (.var "y")]

#guard checkSpill multiAssign [(0, 9), (1, 8)]
#guard selectsAll multiAssign none ["x", "y"]

/-! Spilled parameters and return variables are materialized on both normal
fall-through and early `leave`. -/
def paramsReturnsLeave : Block Op :=
  [guard,
   .funDef "makePair" ["a"] ["u", "v"]
      [.assign ["u"] (builtin .add [.var "a", lit 1]),
       .assign ["v"] (builtin .add [.var "a", lit 2])],
   .funDef "calc" ["p", "early"] ["r", "s"]
      (fillers "calc_filler_" 16 ++
       [.cond (.var "early")
          [.assign ["r", "s"] (.call "makePair" [.var "p"]), .leave],
        .assign ["r", "s"]
          (.call "makePair" [builtin .add [.var "p", lit 10]])]),
   .letDecl ["a", "b"] (some (.call "calc" [lit 5, lit 1])),
   store 0 (.var "a"), store 1 (.var "b"),
   .letDecl ["c", "d"] (some (.call "calc" [lit 5, lit 0])),
   store 2 (.var "c"), store 3 (.var "d")]

#guard checkSpill paramsReturnsLeave [(0, 6), (1, 7), (2, 16), (3, 17)]
#guard selectsAll paramsReturnsLeave (some "calc") ["p", "early", "r", "s"]

/-! Nested bindings overlap an outer spill, while sibling blocks may reuse the
same colored slot after their scopes end. -/
def nestedSiblingScopes : Block Op :=
  [guard, .letDecl ["outer"] (some (lit 10))] ++
    fillers "outer_filler_" 16 ++
    [store 0 (.var "outer"),
     .block ([.letDecl ["left"] (some (lit 20))] ++
       fillers "left_filler_" 16 ++
       [.assign ["left"] (builtin .add [.var "left", lit 1]),
        store 1 (.var "left")]),
     .block ([.letDecl ["right"] (some (lit 30))] ++
       fillers "right_filler_" 16 ++
       [.assign ["right"] (builtin .add [.var "right", lit 2]),
        store 2 (.var "right")]),
     store 3 (.var "outer")]

def nestedSiblingSlotsReuse : Bool :=
  match spillBlock? nestedSiblingScopes with
  | some result =>
      slotFor? result.layout.slots none "left" ==
        slotFor? result.layout.slots none "right"
  | none => false

#guard nestedSiblingSlotsReuse
#guard checkSpill nestedSiblingScopes [(0, 10), (1, 21), (2, 32), (3, 10)]
#guard selectsAll nestedSiblingScopes none ["outer", "left", "right"]

/-! Loop-init spills stay live across condition/body/post.  Body and post
locals exercise separate nested lifetimes and loop-carried writes. -/
def loopRegions : Block Op :=
  [guard, .letDecl ["total"] (some (lit 0)),
   .forLoop
      ([.letDecl ["i"] (some (lit 0))] ++ fillers "init_filler_" 16)
      (builtin .lt [.var "i", lit 3])
      ([.letDecl ["step"] (some (lit 1))] ++ fillers "post_filler_" 16 ++
       [.assign ["i"] (builtin .add [.var "i", .var "step"])])
      ([.letDecl ["term"] (some (builtin .add [.var "i", lit 10]))] ++
       fillers "body_filler_" 16 ++
       [.assign ["total"] (builtin .add [.var "total", .var "term"])]),
   store 0 (.var "total")]

#guard checkSpill loopRegions [(0, 33)]
#guard selectsAll loopRegions none ["total", "i", "step", "term"]

/-! Caller spills remain intact while the callee uses a disjoint spill frame. -/
def callerCallee : Block Op :=
  [guard,
   .funDef "bump" ["p"] ["r"]
      (fillers "callee_filler_" 16 ++
       [.assign ["r"] (builtin .add [.var "p", lit 1])]),
   .letDecl ["keep"] (some (lit 40))] ++
    fillers "caller_filler_" 16 ++
    [.letDecl ["got"] (some (.call "bump" [.var "keep"])),
     store 0 (.var "keep"), store 1 (.var "got")]

def callerCalleeSlotsDisjoint : Bool :=
  match spillBlock? callerCallee with
  | some result =>
      match slotFor? result.layout.slots none "keep",
          slotFor? result.layout.slots (some "bump") "p" with
      | some caller, some callee => caller != callee
      | _, _ => false
  | none => false

#guard callerCalleeSlotsDisjoint
#guard checkSpill callerCallee [(0, 40), (1, 41)]
#guard selectsAll callerCallee none ["keep"]
#guard selectsAll callerCallee (some "bump") ["p", "r"]

/-! A call used only as an `if` condition still contributes a call-graph edge.
The caller's live spill must therefore sit above the callee frame rather than
aliasing it. -/
def conditionOnlyCallerCallee : Block Op :=
  [guard,
   .funDef "truthy" [] ["r"]
      (fillers "condition_callee_filler_" 16 ++
       [.assign ["r"] (lit 1)]),
   .letDecl ["keep"] (some (lit 40))] ++
    fillers "condition_caller_filler_" 16 ++
    [.cond (.call "truthy" []) [store 0 (.var "keep")],
     store 1 (.var "keep")]

def conditionOnlyCallLayoutSafe : Bool :=
  match spillBlock? conditionOnlyCallerCallee with
  | some result =>
      match findInfo? result.layout.infos none,
          slotFor? result.layout.slots none "keep",
          slotFor? result.layout.slots (some "truthy") "r" with
      | some callerInfo, some callerSlot, some calleeSlot =>
          callerInfo.callees.contains (some "truthy") && callerSlot != calleeSlot
      | _, _, _ => false
  | none => false

#guard conditionOnlyCallLayoutSafe
#guard checkSpill conditionOnlyCallerCallee [(0, 40), (1, 40)]
#guard selectsAll conditionOnlyCallerCallee none ["keep"]
#guard selectsAll conditionOnlyCallerCallee (some "truthy") ["r"]

/-! `msize()` in a condition is just as observable as `msize()` in a body;
pressure must not enable spilling around it. -/
def msizeConditionUnderPressure : Block Op :=
  [guard, .letDecl ["keep"] (some (lit 1))] ++
    fillers "msize_condition_filler_" 16 ++
    [.cond (builtin .msize []) [store 0 (.var "keep")],
     store 1 (.var "keep")]

#guard (spillBlock? msizeConditionUnderPressure).isNone

/-! User memory beginning at the guard result moves above the spill interval.
The identity source writes/returns from `base`; the chosen source and spilled
program write/return the same payload from `reserved`. -/
def relocatedGuardAllocation : Block Op :=
  [guard,
   .letDecl ["ptr"] (some (.call "memoryguard" [lit 128])),
   .exprStmt (builtin .mstore [.var "ptr", lit 0x1234]),
   .letDecl ["deep"] (some (lit 1))] ++
    fillers "relocation_filler_" 16 ++
    [.assign ["deep"] (builtin .add [.var "deep", lit 1]),
     .exprStmt (builtin .ret [.var "ptr", lit 32])]

#guard selectsAll relocatedGuardAllocation none ["ptr", "deep"]
#guard checkReturnSpill relocatedGuardAllocation

/-! Recursive object traversal applies the same rewrite independently to root
and child code, retaining an inspectable plan for both. -/
def objectRoot : Block Op := singletonLetAssign
def objectChild : Block Op := multiAssign

def nestedObject : Object Op :=
  .mk "root" objectRoot [.mk "child" objectChild [] []] []

def checkObjectSpill : Bool :=
  let result := spillObject nestedObject
  match result.object, result.plan with
  | .mk "root" rootCode [.mk "child" childCode [] []] [],
      .mk (some rootPlan) [.mk (some childPlan) []] =>
      result.selected == rootPlan.selection.length + childPlan.selection.length &&
        (compileObject result.object).isSome &&
        (match run? rootCode, run? childCode with
         | some rootState, some childState =>
             storageMatches rootState [(0, 12)] &&
               storageMatches childState [(0, 9), (1, 8)] &&
               YulEvmCompiler.Examples.agreeOn rootCode [0] &&
               YulEvmCompiler.Examples.agreeOn childCode [0, 1]
         | _, _ => false)
  | _, _ => false

#guard checkObjectSpill

end YulEvmCompiler.Optimizer.MemorySpillExamples
