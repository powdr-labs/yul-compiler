import YulEvmCompiler.Optimizer.Spec.MemoryGuard
set_option warningAsError true
/-!
# Erasing the dynamic memory-guard instrument

Every derivation in `guardedEvm` is also a derivation in the ordinary
open-world EVM dialect: the instrument only conjoins `OpMemorySafe` to each
builtin premise.  Keeping this transport explicit prevents later spill proofs
from treating the guarded source contract as an unproved dialect cast.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}
variable {base reserved : Nat}

local notation "G" => guardedEvm calls creates base reserved
local notation "D" => evmWithExternal calls creates

def eraseGuardedEResult : EResult G → EResult D
  | .vals values state => .vals values state
  | .halt state => .halt state

def eraseGuardedRes : Res G → Res D
  | .eres result => .eres (eraseGuardedEResult result)
  | .sres vars state outcome => .sres vars state outcome

def eraseGuardedDecl (decl : FDecl G) : FDecl D :=
  { params := decl.params, rets := decl.rets, body := decl.body }

def eraseGuardedScope (scope : FScope G) : FScope D :=
  scope.map fun item => (item.1, eraseGuardedDecl item.2)

def eraseGuardedFuns (funs : FunEnv G) : FunEnv D :=
  funs.map eraseGuardedScope

@[simp] theorem eraseGuardedScope_hoist (body : Block Op) :
    eraseGuardedScope (hoist G body) = hoist D body := by
  induction body with
  | nil => rfl
  | cons stmt rest ih =>
      cases stmt <;>
        simpa [hoist, eraseGuardedScope, eraseGuardedDecl] using ih

private theorem eraseGuardedScope_find (scope : FScope G) (fn : Ident) :
    (eraseGuardedScope scope).find? (fun item => item.1 = fn) =
      (scope.find? fun item => item.1 = fn).map
        (fun item => (item.1, eraseGuardedDecl item.2)) := by
  unfold eraseGuardedScope
  rw [List.find?_map]
  rfl

@[simp] theorem eraseGuardedFuns_lookup (funs : FunEnv G) (fn : Ident) :
    lookupFun (eraseGuardedFuns funs) fn =
      (lookupFun funs fn).map fun result =>
        (eraseGuardedDecl result.1, eraseGuardedFuns result.2) := by
  induction funs with
  | nil => rfl
  | cons scope rest ih =>
      simp only [eraseGuardedFuns, List.map_cons, lookupFun]
      rw [eraseGuardedScope_find]
      cases hfind : scope.find? (fun item => item.1 = fn) with
      | none =>
          simp only [Option.map_none]
          exact ih
      | some item =>
          obtain ⟨name, decl⟩ := item
          simp only [Option.map_some]
          rfl

theorem eraseGuardedFuns_lookup_some {funs : FunEnv G} {fn : Ident}
    {decl : FDecl G} {closure : FunEnv G}
    (hlookup : lookupFun funs fn = some (decl, closure)) :
    lookupFun (eraseGuardedFuns funs) fn =
      some (eraseGuardedDecl decl, eraseGuardedFuns closure) := by
  rw [eraseGuardedFuns_lookup, hlookup]
  rfl

@[simp] theorem guarded_bindZeros (names : List Ident) :
    bindZeros G names = bindZeros D names := rfl

@[simp] theorem guarded_selectSwitch (value : U256)
    (cases : List (Literal × Block Op)) (dflt : Option (Block Op)) :
    selectSwitch G value cases dflt = selectSwitch D value cases dflt := by
  have hp : (fun p : Literal × Block Op =>
      decide (value = Dialect.litValue G p.1)) =
      (fun p : Literal × Block Op =>
        decide (value = Dialect.litValue D p.1)) := by
    funext p
    congr
  unfold selectSwitch
  rw [hp]
  cases List.find? (fun p => decide (value = Dialect.litValue D p.1)) cases <;> rfl

@[simp] theorem guarded_set (vars : VEnv G) (name : Ident) (value : U256) :
    @VEnv.set G vars name value = @VEnv.set D vars name value := by
  induction vars with
  | nil => rfl
  | cons item rest ih =>
      obtain ⟨head, old⟩ := item
      by_cases hhead : head = name
      · simp [VEnv.set, hhead]
      · simp [VEnv.set, hhead, ih]

private theorem guarded_set_fold (items : List (Ident × U256)) (vars : VEnv G) :
    items.foldl (fun env item => @VEnv.set G env item.1 item.2) vars =
      items.foldl (fun env item => @VEnv.set D env item.1 item.2) vars := by
  induction items generalizing vars with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.foldl_cons]
      rw [guarded_set]
      exact ih _

@[simp] theorem guarded_setMany (vars : VEnv G) (names : List Ident)
    (values : List U256) :
    @VEnv.setMany G vars names values = @VEnv.setMany D vars names values := by
  unfold VEnv.setMany
  exact guarded_set_fold (names.zip values) vars

theorem guardedStep_to_step {funs : FunEnv G} {vars : VEnv G}
    {state : EvmState} {code : Code Op} {result : Res G}
    (hstep : Step G funs vars state code result) :
    Step D (eraseGuardedFuns funs) vars state code (eraseGuardedRes result) := by
  induction hstep with
  | lit => exact .lit
  | var hget => exact .var hget
  | builtinOk hargs hop ih =>
      exact .builtinOk ih hop.1
  | builtinHalt hargs hop ih =>
      exact .builtinHalt ih hop.1
  | builtinArgsHalt hargs ih => exact .builtinArgsHalt ih
  | callOk hargs hlookup hlen hbody hout ihArgs ihBody =>
      have hlookup' := eraseGuardedFuns_lookup_some hlookup
      exact .callOk ihArgs hlookup' hlen
        (by simpa [eraseGuardedRes, eraseGuardedDecl] using ihBody) hout
  | callHalt hargs hlookup hlen hbody ihArgs ihBody =>
      have hlookup' := eraseGuardedFuns_lookup_some hlookup
      exact .callHalt ihArgs hlookup' hlen
        (by simpa [eraseGuardedRes, eraseGuardedDecl] using ihBody)
  | callArgsHalt hargs ih => exact .callArgsHalt ih
  | argsNil => exact .argsNil
  | argsCons hrest hhead ihRest ihHead => exact .argsCons ihRest ihHead
  | argsRestHalt hrest ih => exact .argsRestHalt ih
  | argsHeadHalt hrest hhead ihRest ihHead => exact .argsHeadHalt ihRest ihHead
  | funDef => exact .funDef
  | block hbody ih =>
      apply Step.block
      simpa [eraseGuardedFuns, eraseGuardedRes] using ih
  | letZero => exact .letZero
  | letVal heval hlen ih => exact .letVal ih hlen
  | letHalt heval ih => exact .letHalt ih
  | assignVal heval hlen ih =>
      simpa [eraseGuardedRes] using Step.assignVal ih hlen
  | assignHalt heval ih => exact .assignHalt ih
  | exprStmt heval ih => exact .exprStmt ih
  | exprStmtHalt heval ih => exact .exprStmtHalt ih
  | ifTrue hcond hnzero hbody ihCond ihBody => exact .ifTrue ihCond hnzero ihBody
  | ifFalse hcond hzero ih => exact .ifFalse ih hzero
  | ifHalt hcond ih => exact .ifHalt ih
  | switchExec hcond hbody ihCond ihBody =>
      exact .switchExec ihCond (by simpa [eraseGuardedRes] using ihBody)
  | switchHalt hcond ih => exact .switchHalt ih
  | forLoop hinit hloop ihInit ihLoop =>
      apply Step.forLoop
      · simpa [eraseGuardedFuns, eraseGuardedRes] using ihInit
      · simpa [eraseGuardedFuns, eraseGuardedRes] using ihLoop
  | forInitHalt hinit ih =>
      apply Step.forInitHalt
      simpa [eraseGuardedFuns, eraseGuardedRes] using ih
  | «break» => exact .break
  | «continue» => exact .continue
  | leave => exact .leave
  | seqNil => exact .seqNil
  | seqCons hhead hrest ihHead ihRest => exact .seqCons ihHead ihRest
  | seqStop hhead hne ih => exact .seqStop ih hne
  | loopDone hcond hzero ih => exact .loopDone ih hzero
  | loopCondHalt hcond ih => exact .loopCondHalt ih
  | loopStep hcond hnzero hbody hout hpost hloop ihCond ihBody ihPost ihLoop =>
      exact .loopStep ihCond hnzero ihBody hout ihPost ihLoop
  | loopPostHalt hcond hnzero hbody hout hpost ihCond ihBody ihPost =>
      exact .loopPostHalt ihCond hnzero ihBody hout ihPost
  | loopBreak hcond hnzero hbody ihCond ihBody => exact .loopBreak ihCond hnzero ihBody
  | loopLeave hcond hnzero hbody ihCond ihBody => exact .loopLeave ihCond hnzero ihBody
  | loopBodyHalt hcond hnzero hbody ihCond ihBody =>
      exact .loopBodyHalt ihCond hnzero ihBody

theorem guardedRun_to_run {prog : Block Op} {state : EvmState}
    {vars : VEnv G} {state' : EvmState} {outcome : Outcome}
    (hrun : Run G prog state vars state' outcome) :
    Run D prog state vars state' outcome := by
  exact guardedStep_to_step hrun

end YulEvmCompiler.Optimizer
