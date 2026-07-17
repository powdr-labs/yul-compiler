import YulEvmCompiler.Optimizer.Spec.Pass
import YulEvmCompiler.Optimizer.Implementation.Simplify
import YulSemantics.Determinism

/-!
# Inline exact identity helpers

This pass removes the full user-function call protocol around exact identity
helpers.  If lexical Yul lookup resolves `f` to

```
function f(p) -> r { r := p }
```

then `f(e)` becomes `add(e, 0)`.  The apparently redundant `add` is the
soundness fence: both sides require `e` to produce exactly one value.  Replacing
the call directly by `e` would change stuckness for arbitrary multi-valued Yul
expressions.  A following `Simplify` pass removes the `add` for its already
proved variable/literal cases.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-- Exact syntactic identity declaration accepted by the pass. -/
def ExactIdentity (decl : FDecl D) : Prop :=
  match decl.params, decl.rets, decl.body with
  | [param], [ret], [.assign [ret'] (.var param')] => param = param' ∧ ret = ret'
  | _, _, _ => False

/-- Decidable recognizer for `ExactIdentity`. -/
def exactIdentity? (decl : FDecl D) : Bool :=
  match decl.params, decl.rets, decl.body with
  | [param], [ret], [.assign [ret'] (.var param')] => param == param' && ret == ret'
  | _, _, _ => false

theorem exactIdentity?_eq_true {decl : FDecl D} :
    exactIdentity? decl = true ↔ ExactIdentity decl := by
  unfold exactIdentity? ExactIdentity
  split <;> simp

theorem exactIdentity_shape {decl : FDecl D} (h : exactIdentity? decl = true) :
    ∃ param ret, decl =
      { params := [param], rets := [ret], body := [.assign [ret] (.var param)] } := by
  rcases decl with ⟨params, rets, body⟩
  unfold exactIdentity? at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    simp_all
  · contradiction

/-- Does ordinary ordered lexical lookup resolve `fn` to an exact identity? -/
def resolvesIdentity (static : FunEnv D) (fn : Ident) : Bool :=
  match lookupFun static fn with
  | some (decl, _) => exactIdentity? decl
  | none => false

mutual

/-- Rewrite expressions under the original program's lexical scope stack. -/
def inlineIdentityExpr (static : FunEnv D) : Expr Op → Expr Op
  | .lit l => .lit l
  | .var x => .var x
  | .builtin op args => .builtin op (inlineIdentityArgs static args)
  | .call fn args =>
      let args' := inlineIdentityArgs static args
      match args' with
      | [arg] =>
          if resolvesIdentity static fn then .builtin .add [arg, .lit (.number 0)]
          else .call fn args'
      | _ => .call fn args'

/-- Rewrite an argument list. -/
def inlineIdentityArgs (static : FunEnv D) : List (Expr Op) → List (Expr Op)
  | [] => []
  | e :: rest => inlineIdentityExpr static e :: inlineIdentityArgs static rest

end

mutual

/-- Rewrite a statement.  Every nested block pushes its own hoisted scope. -/
def inlineIdentityStmt (static : FunEnv D) : Stmt Op → Stmt Op
  | .block body =>
      .block (inlineIdentityStmts (hoist D body :: static) body)
  | .funDef fn params rets body =>
      .funDef fn params rets (inlineIdentityStmts (hoist D body :: static) body)
  | .letDecl vars value => .letDecl vars (value.map (inlineIdentityExpr static))
  | .assign vars value => .assign vars (inlineIdentityExpr static value)
  | .cond c body =>
      .cond (inlineIdentityExpr static c)
        (inlineIdentityStmts (hoist D body :: static) body)
  | .switch c cases dflt =>
      .switch (inlineIdentityExpr static c) (inlineIdentityCases static cases)
        (match dflt with
        | none => none
        | some body => some (inlineIdentityStmts (hoist D body :: static) body))
  | .forLoop init c post body =>
      let loopStatic := hoist D init :: static
      .forLoop (inlineIdentityStmts loopStatic init) (inlineIdentityExpr loopStatic c)
        (inlineIdentityStmts (hoist D post :: loopStatic) post)
        (inlineIdentityStmts (hoist D body :: loopStatic) body)
  | .exprStmt e => .exprStmt (inlineIdentityExpr static e)
  | .break => .break
  | .continue => .continue
  | .leave => .leave
  termination_by statement => 2 * sizeOf statement + 1
  decreasing_by all_goals simp_wf <;> omega

/-- Rewrite a statement sequence under an already-established scope stack. -/
def inlineIdentityStmts (static : FunEnv D) : Block Op → Block Op
  | [] => []
  | s :: rest => inlineIdentityStmt static s :: inlineIdentityStmts static rest
  termination_by statements => 2 * sizeOf statements
  decreasing_by all_goals simp_wf <;> omega

/-- Rewrite switch cases, each of whose body is a block. -/
def inlineIdentityCases (static : FunEnv D) :
    List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, body) :: rest =>
      (l, inlineIdentityStmts (hoist D body :: static) body) ::
        inlineIdentityCases static rest
  termination_by cases => 2 * sizeOf cases
  decreasing_by all_goals simp_wf <;> omega

end


/-- Rewrite a block, installing its hoisted scope before traversing it. -/
def inlineIdentityBlock (outer : FunEnv D) (body : Block Op) : Block Op :=
  inlineIdentityStmts (hoist D body :: outer) body

/-- Transform a declaration body under its definition-site static closure. -/
def inlineIdentityDecl (static : FunEnv D) (decl : FDecl D) : FDecl D :=
  { decl with body := inlineIdentityBlock static decl.body }

/-- Transform every declaration in one ordered scope. -/
def inlineIdentityScope (static : FunEnv D) (scope : FScope D) : FScope D :=
  scope.map fun entry => (entry.1, inlineIdentityDecl static entry.2)

/-- Transform a complete static scope stack.  A declaration in each scope sees
that scope and every following (outer) scope as its closure. -/
def inlineIdentityFuns : FunEnv D → FunEnv D
  | [] => []
  | scope :: outer =>
      inlineIdentityScope (scope :: outer) scope :: inlineIdentityFuns outer

/-- Transform any of the five semantic code classes. -/
def inlineIdentityCode (static : FunEnv D) : Code Op → Code Op
  | .expr e => .expr (inlineIdentityExpr static e)
  | .args args => .args (inlineIdentityArgs static args)
  | .stmt s => .stmt (inlineIdentityStmt static s)
  | .stmts ss => .stmts (inlineIdentityStmts static ss)
  | .loop c post body =>
      .loop (inlineIdentityExpr static c)
        (inlineIdentityStmts (hoist D post :: static) post)
        (inlineIdentityStmts (hoist D body :: static) body)

theorem inlineIdentityExpr_call_false (static : FunEnv D) (fn : Ident)
    (args : List (Expr Op)) (h : resolvesIdentity static fn = false) :
    inlineIdentityExpr static (.call fn args) =
      .call fn (inlineIdentityArgs static args) := by
  rw [inlineIdentityExpr]
  cases ha : inlineIdentityArgs static args with
  | nil => rfl
  | cons a rest => cases rest <;> simp [h]

theorem inlineIdentityExpr_call_true (static : FunEnv D) (fn : Ident)
    (e : Expr Op) (h : resolvesIdentity static fn = true) :
    inlineIdentityExpr static (.call fn [e]) =
      .builtin .add [inlineIdentityExpr static e, .lit (.number 0)] := by
  simp [inlineIdentityExpr, inlineIdentityArgs, h]

@[simp] theorem inlineIdentityStmt_switch (static : FunEnv D) (c : Expr Op)
    (cases : List (Literal × Block Op)) (dflt : Option (Block Op)) :
    inlineIdentityStmt static (.switch c cases dflt) =
      .switch (inlineIdentityExpr static c) (inlineIdentityCases static cases)
        (dflt.map (inlineIdentityBlock static)) := by
  cases dflt <;> rw [inlineIdentityStmt.eq_def] <;> rfl

/-! ## Structural scope facts -/

theorem hoist_inlineIdentityStmts (static : FunEnv D) : ∀ body : Block Op,
    hoist D (inlineIdentityStmts static body) =
      inlineIdentityScope static (hoist D body)
  | [] => by simp [inlineIdentityStmts, hoist, inlineIdentityScope]
  | .funDef fn params rets body :: rest => by
      rw [inlineIdentityStmts, inlineIdentityStmt]
      simp only [hoist, List.filterMap_cons, inlineIdentityScope, List.map_cons,
        Prod.fst, Prod.snd, inlineIdentityDecl]
      congr 1
      change hoist D (inlineIdentityStmts static rest) =
        inlineIdentityScope static (hoist D rest)
      exact hoist_inlineIdentityStmts static rest
  | .block _ :: rest => by
      rw [inlineIdentityStmts, inlineIdentityStmt]
      simpa [hoist, inlineIdentityScope] using hoist_inlineIdentityStmts static rest
  | .letDecl _ _ :: rest => by
      rw [inlineIdentityStmts, inlineIdentityStmt]
      simpa [hoist, inlineIdentityScope] using hoist_inlineIdentityStmts static rest
  | .assign _ _ :: rest => by
      rw [inlineIdentityStmts, inlineIdentityStmt]
      simpa [hoist, inlineIdentityScope] using hoist_inlineIdentityStmts static rest
  | .cond _ _ :: rest => by
      rw [inlineIdentityStmts, inlineIdentityStmt]
      simpa [hoist, inlineIdentityScope] using hoist_inlineIdentityStmts static rest
  | .switch c cases dflt :: rest => by
      cases dflt <;>
      rw [inlineIdentityStmts, inlineIdentityStmt]
      all_goals
        change hoist D (inlineIdentityStmts static rest) =
          inlineIdentityScope static (hoist D rest)
        exact hoist_inlineIdentityStmts static rest
  | .forLoop _ _ _ _ :: rest => by
      rw [inlineIdentityStmts, inlineIdentityStmt]
      simpa [hoist, inlineIdentityScope] using hoist_inlineIdentityStmts static rest
  | .exprStmt _ :: rest => by
      rw [inlineIdentityStmts, inlineIdentityStmt]
      simpa [hoist, inlineIdentityScope] using hoist_inlineIdentityStmts static rest
  | .break :: rest => by
      rw [inlineIdentityStmts, inlineIdentityStmt]
      simpa [hoist, inlineIdentityScope] using hoist_inlineIdentityStmts static rest
  | .continue :: rest => by
      rw [inlineIdentityStmts, inlineIdentityStmt]
      simpa [hoist, inlineIdentityScope] using hoist_inlineIdentityStmts static rest
  | .leave :: rest => by
      rw [inlineIdentityStmts, inlineIdentityStmt]
      simpa [hoist, inlineIdentityScope] using hoist_inlineIdentityStmts static rest

@[simp] theorem hoist_inlineIdentityBlock (outer : FunEnv D) (body : Block Op) :
    hoist D (inlineIdentityBlock outer body) =
      inlineIdentityScope (hoist D body :: outer) (hoist D body) := by
  exact hoist_inlineIdentityStmts _ body

@[simp] theorem inlineIdentityFuns_cons (scope : FScope D) (outer : FunEnv D) :
    inlineIdentityFuns (scope :: outer) =
      inlineIdentityScope (scope :: outer) scope :: inlineIdentityFuns outer := rfl

@[simp] theorem inlineIdentityBlock_exact (outer : FunEnv D) (param ret : Ident) :
    inlineIdentityBlock outer [.assign [ret] (.var param)] =
      [.assign [ret] (.var param)] := by
  rw [inlineIdentityBlock, inlineIdentityStmts, inlineIdentityStmt,
    inlineIdentityExpr, inlineIdentityStmts]

@[simp] theorem inlineIdentityDecl_exact (static : FunEnv D) (param ret : Ident) :
    inlineIdentityDecl static
      { params := [param], rets := [ret], body := [.assign [ret] (.var param)] } =
      { params := [param], rets := [ret], body := [.assign [ret] (.var param)] } := by
  simp [inlineIdentityDecl]

theorem selectSwitch_inlineIdentity (static : FunEnv D) (value : U256)
    (cases : List (Literal × Block Op)) (dflt : Option (Block Op)) :
    selectSwitch evm value (inlineIdentityCases static cases)
        (dflt.map (inlineIdentityBlock static)) =
      inlineIdentityBlock static (selectSwitch evm value cases dflt) := by
  induction cases with
  | nil => cases dflt <;>
      simp [selectSwitch, inlineIdentityCases, inlineIdentityBlock, inlineIdentityStmts]
  | cons head rest ih =>
      rcases head with ⟨l, body⟩
      by_cases h : decide (value = litValue l) = true
      · simp [selectSwitch, inlineIdentityCases, inlineIdentityBlock, h]
      · simpa [selectSwitch, inlineIdentityCases, h] using ih

/-! ## Lexical lookup through the transformed scope stack -/

theorem find?_inlineIdentityScope (static : FunEnv D) (scope : FScope D)
    (fn : Ident) :
    (inlineIdentityScope static scope).find? (fun entry => entry.1 = fn) =
      (scope.find? (fun entry => entry.1 = fn)).map
        (fun entry => (entry.1, inlineIdentityDecl static entry.2)) := by
  rw [inlineIdentityScope, List.find?_map]
  rfl

theorem lookupFun_append_of_some {static closure outer : FunEnv D}
    {fn : Ident} {decl : FDecl D}
    (h : lookupFun static fn = some (decl, closure)) :
    lookupFun (static ++ outer) fn = some (decl, closure ++ outer) := by
  induction static with
  | nil => simp [lookupFun] at h
  | cons scope rest ih =>
      cases hs : scope.find? (fun entry => entry.1 = fn) with
      | some entry =>
          rw [lookupFun, hs] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp [lookupFun, hs]
      | none =>
          rw [lookupFun, hs] at h
          rw [List.cons_append, lookupFun, hs]
          exact ih h

theorem lookupFun_append_of_none {static outer : FunEnv D} {fn : Ident}
    (h : lookupFun static fn = none) :
    lookupFun (static ++ outer) fn = lookupFun outer fn := by
  induction static with
  | nil => rfl
  | cons scope rest ih =>
      cases hs : scope.find? (fun entry => entry.1 = fn) with
      | some entry => simp [lookupFun, hs] at h
      | none =>
          rw [lookupFun, hs] at h
          rw [List.cons_append, lookupFun, hs, ih h]

theorem lookupFun_inlineIdentityFuns {static closure : FunEnv D}
    {fn : Ident} {decl : FDecl D}
    (h : lookupFun static fn = some (decl, closure)) :
    lookupFun (inlineIdentityFuns static) fn =
      some (inlineIdentityDecl closure decl, inlineIdentityFuns closure) := by
  induction static with
  | nil => simp [lookupFun] at h
  | cons scope rest ih =>
      cases hs : scope.find? (fun entry => entry.1 = fn) with
      | some entry =>
          rw [lookupFun, hs] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [inlineIdentityFuns, lookupFun, find?_inlineIdentityScope, hs]
          rfl
      | none =>
          rw [lookupFun, hs] at h
          rw [inlineIdentityFuns, lookupFun, find?_inlineIdentityScope, hs]
          exact ih h

theorem lookupFun_inline_append_of_some {static closure outer : FunEnv D}
    {fn : Ident} {decl : FDecl D}
    (h : lookupFun static fn = some (decl, closure)) :
    lookupFun (inlineIdentityFuns static ++ outer) fn =
      some (inlineIdentityDecl closure decl, inlineIdentityFuns closure ++ outer) :=
  lookupFun_append_of_some (lookupFun_inlineIdentityFuns h)

theorem lookupFun_inline_append_of_none {static outer : FunEnv D} {fn : Ident}
    (h : lookupFun static fn = none) :
    lookupFun (inlineIdentityFuns static ++ outer) fn = lookupFun outer fn := by
  apply lookupFun_append_of_none
  induction static with
  | nil => rfl
  | cons scope rest ih =>
      cases hs : scope.find? (fun entry => entry.1 = fn) with
      | some entry => simp [lookupFun, hs] at h
      | none =>
          rw [lookupFun, hs] at h
          rw [inlineIdentityFuns, lookupFun, find?_inlineIdentityScope, hs]
          exact ih h

theorem lookupFun_inline_append (static outer : FunEnv D) (fn : Ident) :
    lookupFun (inlineIdentityFuns static ++ outer) fn =
      match lookupFun static fn with
      | none => lookupFun outer fn
      | some (decl, closure) =>
          some (inlineIdentityDecl closure decl, inlineIdentityFuns closure ++ outer) := by
  cases h : lookupFun static fn with
  | none => exact lookupFun_inline_append_of_none h
  | some found =>
      rcases found with ⟨decl, closure⟩
      exact lookupFun_inline_append_of_some (outer := outer) h

/-! ## The local identity-call equivalence -/

theorem args_singleton_value_inv {funs : FunEnv D} {V st e vals st'}
    (h : Step D funs V st (.args [e]) (.eres (.vals vals st'))) :
    ∃ v, vals = [v] ∧ Step D funs V st (.expr e) (.eres (.vals [v] st')) := by
  cases h with
  | argsCons hnil he => cases hnil; exact ⟨_, rfl, he⟩

theorem args_singleton_halt_inv {funs : FunEnv D} {V st e st'}
    (h : Step D funs V st (.args [e]) (.eres (.halt st'))) :
    Step D funs V st (.expr e) (.eres (.halt st')) := by
  cases h with
  | argsRestHalt hnil => cases hnil
  | argsHeadHalt hnil he => cases hnil; exact he

theorem args_add_zero_value {funs : FunEnv D} {V st e v st'}
    (h : Step D funs V st (.expr e) (.eres (.vals [v] st'))) :
    Step D funs V st (.args [e, .lit (.number 0)])
      (.eres (.vals [v, 0] st')) := by
  exact Step.argsCons (Step.argsCons Step.argsNil Step.lit) h

theorem args_add_zero_halt {funs : FunEnv D} {V st e st'}
    (h : Step D funs V st (.expr e) (.eres (.halt st'))) :
    Step D funs V st (.args [e, .lit (.number 0)]) (.eres (.halt st')) := by
  exact Step.argsHeadHalt (Step.argsCons Step.argsNil Step.lit) h

theorem args_add_zero_value_inv {funs : FunEnv D} {V st e vals st'}
    (h : Step D funs V st (.args [e, .lit (.number 0)]) (.eres (.vals vals st'))) :
    ∃ v, vals = [v, 0] ∧ Step D funs V st (.expr e) (.eres (.vals [v] st')) := by
  cases h with
  | argsCons hzero he =>
      cases hzero with
      | argsCons hnil hz => cases hnil; cases hz; exact ⟨_, rfl, he⟩

theorem args_add_zero_halt_inv {funs : FunEnv D} {V st e st'}
    (h : Step D funs V st (.args [e, .lit (.number 0)]) (.eres (.halt st'))) :
    Step D funs V st (.expr e) (.eres (.halt st')) := by
  cases h with
  | argsRestHalt hzero =>
      cases hzero with
      | argsRestHalt hnil => cases hnil
      | argsHeadHalt hnil hz => cases hnil; cases hz
  | argsHeadHalt hzero he =>
      cases hzero with
      | argsCons hnil hz => cases hnil; cases hz; exact he

theorem venv_set_length (V : VEnv D) (x : Ident) (v : U256) :
    (VEnv.set V x v).length = V.length := by
  induction V with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨y, w⟩
      simp only [VEnv.set]
      split <;> simp [ih]

theorem venv_setMany_length (V : VEnv D) (xs : List Ident) (vs : List U256) :
    (VEnv.setMany V xs vs).length = V.length := by
  unfold VEnv.setMany
  induction xs.zip vs generalizing V with
  | nil => rfl
  | cons entry rest ih =>
      rw [List.foldl_cons, ih, venv_set_length]

@[simp] theorem restore_setMany_same (V : VEnv D) (xs : List Ident) (vs : List U256) :
    restore V (VEnv.setMany V xs vs) = VEnv.setMany V xs vs := by
  rw [restore, venv_setMany_length]
  simp

/-- Executing the exact identity body returns its input word and leaves state
unchanged.  The `param = ret` shadowing corner is handled explicitly. -/
theorem identity_body_value (cenv : FunEnv D) (param ret : Ident) (v : U256)
    (st : EvmState) :
    ∃ Vend, Step D cenv
        (([param].zip [v]) ++ bindZeros D [ret]) st
        (.stmt (.block [.assign [ret] (.var param)]))
        (.sres Vend st .normal) ∧ VEnv.get Vend ret = some v := by
  let V0 : VEnv D := ([param].zip [v]) ++ bindZeros D [ret]
  let V1 : VEnv D := VEnv.setMany V0 [ret] ([v] : List U256)
  refine ⟨restore V0 V1, ?_, ?_⟩
  · apply Step.block
    exact Step.seqCons
      (Step.assignVal (Step.var (by simp [V0, VEnv.get])) (by simp)) Step.seqNil
  · by_cases hpr : param = ret <;>
      simp [V0, V1, bindZeros, VEnv.get, VEnv.setMany, VEnv.set, restore,
        venv_set_length, hpr]

theorem identity_body_inv {cenv : FunEnv D} {param ret : Ident} {v : U256}
    {st Vend st' o}
    (h : Step D cenv (([param].zip [v]) ++ bindZeros D [ret]) st
      (.stmt (.block [.assign [ret] (.var param)])) (.sres Vend st' o)) :
    st' = st ∧ o = .normal ∧ VEnv.get Vend ret = some v := by
  cases h with
  | block hb =>
      cases hb with
      | seqCons hass hnil =>
          cases hnil
          cases hass with
          | assignVal hvar _ =>
              cases hvar with
              | @var _ _ _ _ v' hv =>
                  have hv' : v' = v := by
                    by_cases hpr : param = ret <;> simpa [VEnv.get, hpr] using hv.symm
                  subst v'
                  refine ⟨rfl, rfl, ?_⟩
                  rw [restore_setMany_same]
                  by_cases hpr : param = ret <;>
                    simp [bindZeros, VEnv.get, VEnv.setMany, VEnv.set, hpr]
      | seqStop hass hne =>
          cases hass with
          | assignVal _ _ => exact absurd rfl hne
          | assignHalt hvar => cases hvar

theorem identity_call_value {funs cenv : FunEnv D} {V st st' fn e}
    {param ret : Ident} {v : U256}
    (he : Step D funs V st (.expr e) (.eres (.vals [v] st')))
    (hl : lookupFun funs fn = some
      ({ params := [param], rets := [ret],
         body := [.assign [ret] (.var param)] }, cenv)) :
    Step D funs V st (.expr (.call fn [e])) (.eres (.vals [v] st')) := by
  obtain ⟨Vend, hbody, hret⟩ := identity_body_value cenv param ret v st'
  have hc := Step.callOk (Step.argsCons Step.argsNil he) hl (by simp) hbody (Or.inl rfl)
  simpa [hret] using hc

theorem identity_call_halt {funs : FunEnv D} {V st st' fn e}
    (he : Step D funs V st (.expr e) (.eres (.halt st'))) :
    Step D funs V st (.expr (.call fn [e])) (.eres (.halt st')) :=
  Step.callArgsHalt (Step.argsHeadHalt Step.argsNil he)

/-- Under a lookup equation for an exact identity declaration, the call and its
arity-preserving `add(e, 0)` replacement have exactly the same derivations. -/
theorem identity_call_add_iff {funs cenv : FunEnv D} {V st fn e}
    {param ret : Ident} {result : EResult D}
    (hl : lookupFun funs fn = some
      ({ params := [param], rets := [ret],
         body := [.assign [ret] (.var param)] }, cenv)) :
    Step D funs V st (.expr (.call fn [e])) (.eres result) ↔
      Step D funs V st (.expr (.builtin .add [e, .lit (.number 0)])) (.eres result) := by
  constructor
  · intro hcall
    cases hcall with
    | callOk hargs hlookup _ hbody hout =>
        obtain ⟨v, rfl, he⟩ := args_singleton_value_inv hargs
        rw [hl] at hlookup
        injection hlookup with heq
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
        obtain ⟨rfl, rfl, hret⟩ := identity_body_inv hbody
        simp only [List.map_cons, List.map_nil, Option.getD_some] at *
        rw [hret] at *
        exact Step.builtinOk (args_add_zero_value he)
          (pureFn_builtin (calls := calls) (creates := creates) (by simp [pureFn]) _)
    | callHalt hargs hlookup _ hbody =>
        obtain ⟨v, rfl, he⟩ := args_singleton_value_inv hargs
        rw [hl] at hlookup
        injection hlookup with heq
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
        have := identity_body_inv hbody
        simp_all
    | callArgsHalt hargs =>
        exact Step.builtinArgsHalt (args_add_zero_halt (args_singleton_halt_inv hargs))
  · intro hadd
    cases hadd with
    | builtinOk hargs hb =>
        obtain ⟨v, rfl, he⟩ := args_add_zero_value_inv hargs
        have hr := pureFn_builtin_inv (calls := calls) (creates := creates) (w := v)
          (h := by simp [pureFn]) hb
        injection hr with hvals hst
        subst hvals; subst hst
        exact identity_call_value he hl
    | builtinHalt hargs hb =>
        obtain ⟨v, rfl, he⟩ := args_add_zero_value_inv hargs
        have hr := pureFn_builtin_inv (calls := calls) (creates := creates) (w := v)
          (h := by simp [pureFn]) hb
        simp at hr
    | builtinArgsHalt hargs =>
        exact identity_call_halt (args_add_zero_halt_inv hargs)

/-! ## Scope-indexed semantic simulation -/

/-- A derivation transports from the original lexical scope stack to the
transformed one.  `outer` is deliberately untouched: the pass never assumes
anything about functions supplied by an enclosing context. -/
theorem Step.inlineIdentity_forward {funs : FunEnv D} {V st code result}
    (h : Step D funs V st code result) : ∀ (static outer : FunEnv D),
    funs = static ++ outer →
    Step D (inlineIdentityFuns static ++ outer) V st
      (inlineIdentityCode static code) result := by
  induction h with
  | lit => intro static outer rfl; exact Step.lit
  | var hv => intro static outer rfl; exact Step.var hv
  | builtinOk _ hb iha =>
      intro static outer rfl
      exact Step.builtinOk (iha static outer rfl) hb
  | builtinHalt _ hb iha =>
      intro static outer rfl
      exact Step.builtinHalt (iha static outer rfl) hb
  | builtinArgsHalt _ iha =>
      intro static outer rfl
      exact Step.builtinArgsHalt (iha static outer rfl)
  | @callOk funs V st fn args argvals st1 decl cenv Vend st2 o
      hargs hlookup hlen hbody hout ihargs ihbody =>
      intro static outer hfun
      subst funs
      have hargs' := ihargs static outer rfl
      cases hs : lookupFun static fn with
      | none =>
          have hlookup' : lookupFun outer fn = some (decl, cenv) := by
            simpa [lookupFun_append_of_none hs] using hlookup
          have htarget : lookupFun (inlineIdentityFuns static ++ outer) fn =
              some (decl, cenv) := by
            simpa [lookupFun_inline_append_of_none hs] using hlookup'
          have hc := Step.callOk hargs' htarget hlen hbody hout
          rw [inlineIdentityCode, inlineIdentityExpr_call_false static fn args
            (by simp [resolvesIdentity, hs])]
          exact hc
      | some found =>
          rcases found with ⟨sdecl, closure⟩
          have hsource := lookupFun_append_of_some (outer := outer) hs
          rw [hsource] at hlookup
          injection hlookup with heq
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
          have htarget := lookupFun_inline_append_of_some (outer := outer) hs
          have hbody' := ihbody closure outer rfl
          have hbody'' : Step D (inlineIdentityFuns closure ++ outer)
              ((inlineIdentityDecl closure sdecl).params.zip argvals ++
                bindZeros D (inlineIdentityDecl closure sdecl).rets) st1
              (.stmt (.block (inlineIdentityDecl closure sdecl).body))
              (.sres Vend st2 o) := by
            simpa [inlineIdentityCode, inlineIdentityStmt, inlineIdentityDecl,
              inlineIdentityBlock] using hbody'
          have hc := Step.callOk hargs' htarget
            (by simpa [inlineIdentityDecl] using hlen) hbody'' hout
          cases args with
          | nil =>
              simpa [inlineIdentityCode, inlineIdentityExpr, inlineIdentityArgs,
                resolvesIdentity, hs, inlineIdentityDecl] using hc
          | cons e rest =>
              cases rest with
              | nil =>
                  by_cases hid : exactIdentity? sdecl = true
                  · obtain ⟨param, ret, hdecl⟩ := exactIdentity_shape hid
                    subst sdecl
                    rw [inlineIdentityDecl_exact] at htarget
                    have hi := (identity_call_add_iff (hl := htarget)).mp hc
                    simpa [inlineIdentityCode, inlineIdentityExpr, inlineIdentityArgs,
                      resolvesIdentity, hs, hid, inlineIdentityDecl] using hi
                  · simpa [inlineIdentityCode, inlineIdentityExpr, inlineIdentityArgs,
                      resolvesIdentity, hs, hid, inlineIdentityDecl] using hc
              | cons e2 rest =>
                  simpa [inlineIdentityCode, inlineIdentityExpr, inlineIdentityArgs,
                    resolvesIdentity, hs, inlineIdentityDecl] using hc
  | @callHalt funs V st fn args argvals st1 decl cenv Vend st2
      hargs hlookup hlen hbody ihargs ihbody =>
      intro static outer hfun
      subst funs
      have hargs' := ihargs static outer rfl
      cases hs : lookupFun static fn with
      | none =>
          have hlookup' : lookupFun outer fn = some (decl, cenv) := by
            simpa [lookupFun_append_of_none hs] using hlookup
          have htarget : lookupFun (inlineIdentityFuns static ++ outer) fn =
              some (decl, cenv) := by
            simpa [lookupFun_inline_append_of_none hs] using hlookup'
          have hc := Step.callHalt hargs' htarget hlen hbody
          rw [inlineIdentityCode, inlineIdentityExpr_call_false static fn args
            (by simp [resolvesIdentity, hs])]
          exact hc
      | some found =>
          rcases found with ⟨sdecl, closure⟩
          have hsource := lookupFun_append_of_some (outer := outer) hs
          rw [hsource] at hlookup
          injection hlookup with heq
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
          have htarget := lookupFun_inline_append_of_some (outer := outer) hs
          have hbody' := ihbody closure outer rfl
          have hbody'' : Step D (inlineIdentityFuns closure ++ outer)
              ((inlineIdentityDecl closure sdecl).params.zip argvals ++
                bindZeros D (inlineIdentityDecl closure sdecl).rets) st1
              (.stmt (.block (inlineIdentityDecl closure sdecl).body))
              (.sres Vend st2 .halt) := by
            simpa [inlineIdentityCode, inlineIdentityStmt, inlineIdentityDecl,
              inlineIdentityBlock] using hbody'
          have hc := Step.callHalt hargs' htarget
            (by simpa [inlineIdentityDecl] using hlen) hbody''
          cases args with
          | nil =>
              simpa [inlineIdentityCode, inlineIdentityExpr, inlineIdentityArgs,
                resolvesIdentity, hs] using hc
          | cons e rest =>
              cases rest with
              | nil =>
                  by_cases hid : exactIdentity? sdecl = true
                  · obtain ⟨param, ret, hdecl⟩ := exactIdentity_shape hid
                    subst sdecl
                    rw [inlineIdentityDecl_exact] at htarget
                    have hi := (identity_call_add_iff (hl := htarget)).mp hc
                    simpa [inlineIdentityCode, inlineIdentityExpr, inlineIdentityArgs,
                      resolvesIdentity, hs, hid] using hi
                  · simpa [inlineIdentityCode, inlineIdentityExpr, inlineIdentityArgs,
                      resolvesIdentity, hs, hid, inlineIdentityDecl] using hc
              | cons e2 rest =>
                  simpa [inlineIdentityCode, inlineIdentityExpr, inlineIdentityArgs,
                    resolvesIdentity, hs, inlineIdentityDecl] using hc
  | @callArgsHalt funs V st fn args st1 hargs ihargs =>
      intro static outer hfun
      subst funs
      have hargs' := ihargs static outer rfl
      have hc : Step D (inlineIdentityFuns static ++ outer) V st
          (.expr (.call fn (inlineIdentityArgs static args))) (.eres (.halt st1)) :=
        Step.callArgsHalt hargs'
      cases hs : lookupFun static fn with
      | none =>
          rw [inlineIdentityCode, inlineIdentityExpr_call_false static fn args
            (by simp [resolvesIdentity, hs])]
          exact hc
      | some found =>
          rcases found with ⟨sdecl, closure⟩
          cases args with
          | nil =>
              simpa [inlineIdentityCode, inlineIdentityExpr, inlineIdentityArgs,
                resolvesIdentity, hs] using hc
          | cons e rest =>
              cases rest with
              | nil =>
                  by_cases hid : exactIdentity? sdecl = true
                  · obtain ⟨param, ret, hdecl⟩ := exactIdentity_shape hid
                    subst sdecl
                    have htarget := lookupFun_inline_append_of_some (outer := outer) hs
                    have hi := (identity_call_add_iff
                      (hl := by simpa [inlineIdentityDecl] using htarget)).mp hc
                    simpa [inlineIdentityCode, inlineIdentityExpr, inlineIdentityArgs,
                      resolvesIdentity, hs, hid] using hi
                  · simpa [inlineIdentityCode, inlineIdentityExpr, inlineIdentityArgs,
                      resolvesIdentity, hs, hid] using hc
              | cons e2 rest =>
                  simpa [inlineIdentityCode, inlineIdentityExpr, inlineIdentityArgs,
                    resolvesIdentity, hs] using hc
  | argsNil => intro static outer rfl; exact Step.argsNil
  | argsCons _ _ ihrest ihe =>
      intro static outer rfl
      exact Step.argsCons (ihrest static outer rfl) (ihe static outer rfl)
  | argsRestHalt _ ihrest =>
      intro static outer rfl
      exact Step.argsRestHalt (ihrest static outer rfl)
  | argsHeadHalt _ _ ihrest ihe =>
      intro static outer rfl
      exact Step.argsHeadHalt (ihrest static outer rfl) (ihe static outer rfl)
  | funDef =>
      intro static outer rfl
      rw [inlineIdentityCode, inlineIdentityStmt.eq_def]
      exact Step.funDef
  | @block funs V st body Vb stb o hbody ihbody =>
      intro static outer hfun
      subst funs
      have hb := ihbody (hoist D body :: static) outer rfl
      rw [inlineIdentityCode] at hb
      have hb' : Step D
          (hoist D (inlineIdentityBlock static body) ::
            (inlineIdentityFuns static ++ outer)) V st
          (.stmts (inlineIdentityBlock static body)) (.sres Vb stb o) := by
        simpa [inlineIdentityBlock, inlineIdentityFuns,
          hoist_inlineIdentityStmts] using hb
      rw [inlineIdentityCode, inlineIdentityStmt.eq_def]
      exact Step.block hb'
  | letZero =>
      intro static outer rfl
      rw [inlineIdentityCode, inlineIdentityStmt]
      exact Step.letZero
  | letVal _ hlen ihe =>
      intro static outer rfl
      simpa [inlineIdentityCode, inlineIdentityStmt] using
        Step.letVal (ihe static outer rfl) hlen
  | letHalt _ ihe =>
      intro static outer rfl
      simpa [inlineIdentityCode, inlineIdentityStmt] using
        Step.letHalt (ihe static outer rfl)
  | assignVal _ hlen ihe =>
      intro static outer rfl
      simpa [inlineIdentityCode, inlineIdentityStmt] using
        Step.assignVal (ihe static outer rfl) hlen
  | assignHalt _ ihe =>
      intro static outer rfl
      simpa [inlineIdentityCode, inlineIdentityStmt] using
        Step.assignHalt (ihe static outer rfl)
  | exprStmt _ ihe =>
      intro static outer rfl
      simpa [inlineIdentityCode, inlineIdentityStmt] using
        Step.exprStmt (ihe static outer rfl)
  | exprStmtHalt _ ihe =>
      intro static outer rfl
      simpa [inlineIdentityCode, inlineIdentityStmt] using
        Step.exprStmtHalt (ihe static outer rfl)
  | ifTrue _ hnz _ ihc ihb =>
      intro static outer rfl
      have hc' := ihc static outer rfl
      have hb' := ihb static outer rfl
      rw [inlineIdentityCode] at hc'
      rw [inlineIdentityCode, inlineIdentityStmt] at hb'
      rw [inlineIdentityCode, inlineIdentityStmt]
      exact Step.ifTrue hc' hnz hb'
  | @ifFalse funs V st c body cv st1 hc hz ihc =>
      intro static outer rfl
      have hc' := ihc static outer rfl
      rw [inlineIdentityCode] at hc'
      rw [inlineIdentityCode, inlineIdentityStmt]
      exact Step.ifFalse (body := inlineIdentityBlock static body) hc' hz
  | @ifHalt funs V st c body st1 hc ihc =>
      intro static outer rfl
      have hc' := ihc static outer rfl
      rw [inlineIdentityCode] at hc'
      rw [inlineIdentityCode, inlineIdentityStmt]
      exact Step.ifHalt (body := inlineIdentityBlock static body) hc'
  | @switchExec funs V st c cases dflt cv st1 V' st2 o hc hb ihc ihb =>
      intro static outer hfun
      subst funs
      have hc' := ihc static outer rfl
      have hb' := ihb static outer rfl
      rw [inlineIdentityCode] at hc'
      rw [inlineIdentityCode, inlineIdentityStmt] at hb'
      rw [selectSwitch_open_eq] at hb'
      have hb'' : Step D (inlineIdentityFuns static ++ outer) V st1
          (.stmt (.block (selectSwitch evm cv (inlineIdentityCases static cases)
            (dflt.map (inlineIdentityBlock static))))) (.sres V' st2 o) := by
        rw [selectSwitch_inlineIdentity]
        exact hb'
      rw [inlineIdentityCode, inlineIdentityStmt_switch]
      exact Step.switchExec hc' (by simpa only [selectSwitch_open_eq] using hb'')
  | @switchHalt funs V st c cases dflt st1 hc ihc =>
      intro static outer rfl
      have hc' := ihc static outer rfl
      rw [inlineIdentityCode] at hc'
      cases dflt <;> rw [inlineIdentityCode, inlineIdentityStmt.eq_def]
      · exact Step.switchHalt hc'
      · exact Step.switchHalt hc'
  | @forLoop funs V st init c post body Vinit stinit Vend stend o
      hinit hloop ihinit ihloop =>
      intro static outer hfun
      subst funs
      have hi := ihinit (hoist D init :: static) outer rfl
      have hl := ihloop (hoist D init :: static) outer rfl
      rw [inlineIdentityCode.eq_def] at hi hl
      have hi' : Step D
          (hoist D (inlineIdentityStmts (hoist D init :: static) init) ::
            (inlineIdentityFuns static ++ outer)) V st
          (.stmts (inlineIdentityStmts (hoist D init :: static) init))
          (.sres Vinit stinit .normal) := by
        simpa [inlineIdentityFuns, hoist_inlineIdentityStmts] using hi
      have hl' : Step D
          (hoist D (inlineIdentityStmts (hoist D init :: static) init) ::
            (inlineIdentityFuns static ++ outer)) Vinit stinit
          (.loop (inlineIdentityExpr (hoist D init :: static) c)
            (inlineIdentityStmts (hoist D post :: hoist D init :: static) post)
            (inlineIdentityStmts (hoist D body :: hoist D init :: static) body))
          (.sres Vend stend o) := by
        simpa [inlineIdentityFuns, hoist_inlineIdentityStmts] using hl
      rw [inlineIdentityCode, inlineIdentityStmt.eq_def]
      exact Step.forLoop hi' hl'
  | @forInitHalt funs V st init c post body Vinit stinit hinit ihinit =>
      intro static outer hfun
      subst funs
      have hi := ihinit (hoist D init :: static) outer rfl
      rw [inlineIdentityCode.eq_def] at hi
      have hi' : Step D
          (hoist D (inlineIdentityStmts (hoist D init :: static) init) ::
            (inlineIdentityFuns static ++ outer)) V st
          (.stmts (inlineIdentityStmts (hoist D init :: static) init))
          (.sres Vinit stinit .halt) := by
        simpa [inlineIdentityFuns, hoist_inlineIdentityStmts] using hi
      rw [inlineIdentityCode, inlineIdentityStmt.eq_def]
      exact Step.forInitHalt hi'
  | «break» =>
      intro static outer rfl
      rw [inlineIdentityCode, inlineIdentityStmt.eq_def]
      exact Step.«break»
  | «continue» =>
      intro static outer rfl
      rw [inlineIdentityCode, inlineIdentityStmt.eq_def]
      exact Step.«continue»
  | leave =>
      intro static outer rfl
      rw [inlineIdentityCode, inlineIdentityStmt.eq_def]
      exact Step.leave
  | seqNil =>
      intro static outer rfl
      rw [inlineIdentityCode, inlineIdentityStmts]
      exact Step.seqNil
  | seqCons _ _ ihs ihrest =>
      intro static outer rfl
      simpa [inlineIdentityCode, inlineIdentityStmts] using
        Step.seqCons (ihs static outer rfl) (ihrest static outer rfl)
  | @seqStop funs V st s rest V1 st1 o hs hne ihs =>
      intro static outer rfl
      simpa [inlineIdentityCode, inlineIdentityStmts] using
        (Step.seqStop (rest := inlineIdentityStmts static rest)
          (ihs static outer rfl) hne)
  | loopDone _ hz ihc =>
      intro static outer rfl
      have hc' := ihc static outer rfl
      rw [inlineIdentityCode] at hc'
      rw [inlineIdentityCode]
      exact Step.loopDone hc' hz
  | loopCondHalt _ ihc =>
      intro static outer rfl
      have hc' := ihc static outer rfl
      rw [inlineIdentityCode] at hc'
      rw [inlineIdentityCode]
      exact Step.loopCondHalt hc'
  | loopStep _ hnz _ hob _ _ ihc ihb ihp ihr =>
      intro static outer rfl
      have hc' := ihc static outer rfl
      have hb' := ihb static outer rfl
      have hp' := ihp static outer rfl
      have hr' := ihr static outer rfl
      rw [inlineIdentityCode] at hc'
      rw [inlineIdentityCode.eq_def] at hr'
      rw [inlineIdentityCode, inlineIdentityStmt] at hb' hp'
      rw [inlineIdentityCode]
      exact Step.loopStep hc' hnz hb' hob hp' hr'
  | loopPostHalt _ hnz _ hob _ ihc ihb ihp =>
      intro static outer rfl
      have hc' := ihc static outer rfl
      have hb' := ihb static outer rfl
      have hp' := ihp static outer rfl
      rw [inlineIdentityCode] at hc'
      rw [inlineIdentityCode, inlineIdentityStmt] at hb' hp'
      rw [inlineIdentityCode]
      exact Step.loopPostHalt hc' hnz hb' hob hp'
  | loopBreak _ hnz _ ihc ihb =>
      intro static outer rfl
      have hc' := ihc static outer rfl
      have hb' := ihb static outer rfl
      rw [inlineIdentityCode] at hc'
      rw [inlineIdentityCode, inlineIdentityStmt] at hb'
      rw [inlineIdentityCode]
      exact Step.loopBreak hc' hnz hb'
  | loopLeave _ hnz _ ihc ihb =>
      intro static outer rfl
      have hc' := ihc static outer rfl
      have hb' := ihb static outer rfl
      rw [inlineIdentityCode] at hc'
      rw [inlineIdentityCode, inlineIdentityStmt] at hb'
      rw [inlineIdentityCode]
      exact Step.loopLeave hc' hnz hb'
  | loopBodyHalt _ hnz _ ihc ihb =>
      intro static outer rfl
      have hc' := ihc static outer rfl
      have hb' := ihb static outer rfl
      rw [inlineIdentityCode] at hc'
      rw [inlineIdentityCode, inlineIdentityStmt] at hb'
      rw [inlineIdentityCode]
      exact Step.loopBodyHalt hc' hnz hb'

theorem inlineIdentityArgs_eq_nil {static : FunEnv D} {args : List (Expr Op)}
    (h : inlineIdentityArgs static args = []) : args = [] := by
  cases args <;> simp [inlineIdentityArgs] at h ⊢

theorem inlineIdentityArgs_eq_cons {static : FunEnv D} {args : List (Expr Op)} {e rest}
    (h : inlineIdentityArgs static args = e :: rest) :
    ∃ e0 rest0, args = e0 :: rest0 ∧
      inlineIdentityExpr static e0 = e ∧ inlineIdentityArgs static rest0 = rest := by
  cases args with
  | nil => simp [inlineIdentityArgs] at h
  | cons e0 rest0 =>
      simp only [inlineIdentityArgs, List.cons.injEq] at h
      exact ⟨e0, rest0, rfl, h.1, h.2⟩

theorem inlineIdentityExpr_eq_lit {static : FunEnv D} {e : Expr Op} {l}
    (h : inlineIdentityExpr static e = .lit l) : e = .lit l := by
  cases e with
  | lit l0 => simpa [inlineIdentityExpr] using h
  | var => simp [inlineIdentityExpr] at h
  | builtin => simp [inlineIdentityExpr] at h
  | call fn args =>
      rw [inlineIdentityExpr] at h
      split at h
      · split at h <;> contradiction
      · contradiction

theorem inlineIdentityExpr_eq_var {static : FunEnv D} {e : Expr Op} {x}
    (h : inlineIdentityExpr static e = .var x) : e = .var x := by
  cases e with
  | lit => simp [inlineIdentityExpr] at h
  | var x0 => simpa [inlineIdentityExpr] using h
  | builtin => simp [inlineIdentityExpr] at h
  | call fn args =>
      rw [inlineIdentityExpr] at h
      split at h
      · split at h <;> contradiction
      · contradiction

theorem inlineIdentityExpr_eq_builtin {static : FunEnv D} {e : Expr Op} {op argsT}
    (h : inlineIdentityExpr static e = .builtin op argsT) :
    (∃ args, e = .builtin op args ∧ argsT = inlineIdentityArgs static args) ∨
    (op = .add ∧ ∃ fn arg, e = .call fn [arg] ∧
      resolvesIdentity static fn = true ∧
      argsT = [inlineIdentityExpr static arg, .lit (.number 0)]) := by
  cases e with
  | lit => simp [inlineIdentityExpr] at h
  | var => simp [inlineIdentityExpr] at h
  | builtin op0 args0 =>
      simp only [inlineIdentityExpr, Expr.builtin.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨args0, rfl, rfl⟩
  | call fn args0 =>
      rw [inlineIdentityExpr] at h
      cases args0 with
      | nil => simp [inlineIdentityArgs] at h
      | cons arg rest0 =>
          cases rest0 with
          | nil =>
              simp only [inlineIdentityArgs] at h
              by_cases hr : resolvesIdentity static fn = true
              · simp [hr] at h
                obtain ⟨rfl, rfl⟩ := h
                exact Or.inr ⟨rfl, fn, arg, rfl, hr, rfl⟩
              · simp [hr] at h
          | cons arg2 rest2 =>
              simp [inlineIdentityArgs] at h

theorem inlineIdentityExpr_eq_call {static : FunEnv D} {e : Expr Op} {fn argsT}
    (h : inlineIdentityExpr static e = .call fn argsT) :
    ∃ args, e = .call fn args ∧ argsT = inlineIdentityArgs static args ∧
      ¬ (∃ arg, args = [arg] ∧ resolvesIdentity static fn = true) := by
  cases e with
  | lit => simp [inlineIdentityExpr] at h
  | var => simp [inlineIdentityExpr] at h
  | builtin => simp [inlineIdentityExpr] at h
  | call fn0 args0 =>
      rw [inlineIdentityExpr] at h
      cases args0 with
      | nil =>
          simp [inlineIdentityArgs] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨[], rfl, by simp [inlineIdentityArgs], by simp⟩
      | cons arg rest0 =>
          cases rest0 with
          | nil =>
              simp only [inlineIdentityArgs] at h
              by_cases hr : resolvesIdentity static fn0 = true
              · simp [hr] at h
              · simp [hr] at h
                obtain ⟨rfl, rfl⟩ := h
                exact ⟨[arg], rfl, rfl, by simp [hr]⟩
          | cons arg2 rest2 =>
              simp [inlineIdentityArgs] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨arg :: arg2 :: rest2, rfl, rfl, by simp⟩

theorem inlineIdentityStmts_eq_nil {static : FunEnv D} {ss : Block Op}
    (h : inlineIdentityStmts static ss = []) : ss = [] := by
  cases ss <;> simp [inlineIdentityStmts] at h ⊢

theorem inlineIdentityStmts_eq_cons {static : FunEnv D} {ss : Block Op} {s rest}
    (h : inlineIdentityStmts static ss = s :: rest) :
    ∃ s0 rest0, ss = s0 :: rest0 ∧ inlineIdentityStmt static s0 = s ∧
      inlineIdentityStmts static rest0 = rest := by
  cases ss with
  | nil => simp [inlineIdentityStmts] at h
  | cons s0 rest0 =>
      simp only [inlineIdentityStmts, List.cons.injEq] at h
      exact ⟨s0, rest0, rfl, h.1, h.2⟩

theorem Step.inlineIdentity_reverse {funsT : FunEnv D} {V st codeT result}
    (h : Step D funsT V st codeT result) : ∀ (static outer : FunEnv D) (code : Code Op),
    funsT = inlineIdentityFuns static ++ outer →
    codeT = inlineIdentityCode static code →
    Step D (static ++ outer) V st code result := by
  induction h <;> intro static outer code hf hc
  case lit funs V st l =>
    cases code with
    | expr e =>
        have he := inlineIdentityExpr_eq_lit (static := static)
          (by simpa [inlineIdentityCode] using hc.symm)
        subst e
        exact Step.lit
    | args => simp [inlineIdentityCode] at hc
    | stmt => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case var funs V st x v hv =>
    cases code with
    | expr e =>
        have he := inlineIdentityExpr_eq_var (static := static)
          (by simpa [inlineIdentityCode] using hc.symm)
        subst e
        exact Step.var hv
    | args => simp [inlineIdentityCode] at hc
    | stmt => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case builtinOk funs V st op args argvals st1 rets st2 hargs hb ihargs =>
    cases code with
    | expr e =>
        rcases inlineIdentityExpr_eq_builtin (static := static)
            (by simpa [inlineIdentityCode] using hc.symm) with
          ⟨args0, rfl, hargsEq⟩ | ⟨rfl, fn, arg, rfl, hr, hargsEq⟩
        · exact Step.builtinOk
            (ihargs static outer (.args args0) hf
              (by simpa [inlineIdentityCode] using congrArg Code.args hargsEq)) hb
        · have ha0 := ihargs static outer
              (.args [arg, .lit (.number 0)]) hf
              (by simpa [inlineIdentityCode, inlineIdentityArgs, inlineIdentityExpr]
                using congrArg Code.args hargsEq)
          have hadd : Step D (static ++ outer) V st
              (.expr (.builtin .add [arg, .lit (.number 0)]))
              (.eres (.vals rets st2)) := Step.builtinOk ha0 hb
          unfold resolvesIdentity at hr
          cases hs : lookupFun static fn with
          | none => simp [hs] at hr
          | some found =>
              rcases found with ⟨decl, closure⟩
              rw [hs] at hr
              obtain ⟨param, ret, hdecl⟩ := exactIdentity_shape hr
              subst decl
              exact (identity_call_add_iff
                (hl := lookupFun_append_of_some (outer := outer) hs)).mpr hadd
    | args => simp [inlineIdentityCode] at hc
    | stmt => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case builtinHalt funs V st op args argvals st1 st2 hargs hb ihargs =>
    cases code with
    | expr e =>
        rcases inlineIdentityExpr_eq_builtin (static := static)
            (by simpa [inlineIdentityCode] using hc.symm) with
          ⟨args0, rfl, hargsEq⟩ | ⟨rfl, fn, arg, rfl, hr, hargsEq⟩
        · exact Step.builtinHalt
            (ihargs static outer (.args args0) hf
              (by simpa [inlineIdentityCode] using congrArg Code.args hargsEq)) hb
        · have ha0 := ihargs static outer
              (.args [arg, .lit (.number 0)]) hf
              (by simpa [inlineIdentityCode, inlineIdentityArgs, inlineIdentityExpr]
                using congrArg Code.args hargsEq)
          have hadd : Step D (static ++ outer) V st
              (.expr (.builtin .add [arg, .lit (.number 0)]))
              (.eres (.halt st2)) := Step.builtinHalt ha0 hb
          unfold resolvesIdentity at hr
          cases hs : lookupFun static fn with
          | none => simp [hs] at hr
          | some found =>
              rcases found with ⟨decl, closure⟩
              rw [hs] at hr
              obtain ⟨param, ret, hdecl⟩ := exactIdentity_shape hr
              subst decl
              exact (identity_call_add_iff
                (hl := lookupFun_append_of_some (outer := outer) hs)).mpr hadd
    | args => simp [inlineIdentityCode] at hc
    | stmt => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case builtinArgsHalt funs V st op args st1 hargs ihargs =>
    cases code with
    | expr e =>
        rcases inlineIdentityExpr_eq_builtin (static := static)
            (by simpa [inlineIdentityCode] using hc.symm) with
          ⟨args0, rfl, hargsEq⟩ | ⟨rfl, fn, arg, rfl, hr, hargsEq⟩
        · exact Step.builtinArgsHalt
            (ihargs static outer (.args args0) hf
              (by simpa [inlineIdentityCode] using congrArg Code.args hargsEq))
        · have ha0 := ihargs static outer
              (.args [arg, .lit (.number 0)]) hf
              (by simpa [inlineIdentityCode, inlineIdentityArgs, inlineIdentityExpr]
                using congrArg Code.args hargsEq)
          have hadd : Step D (static ++ outer) V st
              (.expr (.builtin .add [arg, .lit (.number 0)]))
              (.eres (.halt st1)) := Step.builtinArgsHalt ha0
          unfold resolvesIdentity at hr
          cases hs : lookupFun static fn with
          | none => simp [hs] at hr
          | some found =>
              rcases found with ⟨decl, closure⟩
              rw [hs] at hr
              obtain ⟨param, ret, hdecl⟩ := exactIdentity_shape hr
              subst decl
              exact (identity_call_add_iff
                (hl := lookupFun_append_of_some (outer := outer) hs)).mpr hadd
    | args => simp [inlineIdentityCode] at hc
    | stmt => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case callOk funs V st fn args argvals st1 decl cenv Vend st2 o
      hargs hlookup hlen hbody hout ihargs ihbody =>
    cases code with
    | expr e =>
        obtain ⟨args0, rfl, hargsEq, hn⟩ := inlineIdentityExpr_eq_call
          (static := static) (by simpa [inlineIdentityCode] using hc.symm)
        have hargs0 := ihargs static outer (.args args0) hf
          (by simpa [inlineIdentityCode] using congrArg Code.args hargsEq)
        rw [hf] at hlookup
        cases hs : lookupFun static fn with
        | none =>
            have ho : lookupFun outer fn = some (decl, cenv) := by
              simpa [lookupFun_inline_append_of_none hs] using hlookup
            have hsource : lookupFun (static ++ outer) fn = some (decl, cenv) := by
              rw [lookupFun_append_of_none hs]
              exact ho
            exact Step.callOk hargs0 hsource hlen hbody hout
        | some found =>
            rcases found with ⟨sdecl, closure⟩
            have ht := lookupFun_inline_append_of_some (outer := outer) hs
            rw [ht] at hlookup
            injection hlookup with heq
            obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
            have hb0 := ihbody closure outer
              (.stmt (.block sdecl.body)) rfl
              (by simp [inlineIdentityCode, inlineIdentityStmt, inlineIdentityDecl,
                inlineIdentityBlock])
            have hcall0 : Step D (static ++ outer) V st
                (.expr (.call fn args0))
                (.eres (.vals
                  (sdecl.rets.map (fun r => (VEnv.get Vend r).getD
                    (evmWithExternal calls creates).zero)) st2)) :=
              Step.callOk hargs0
                (lookupFun_append_of_some (outer := outer) hs)
                (by simpa [inlineIdentityDecl] using hlen) hb0 hout
            simpa [inlineIdentityDecl] using hcall0
    | args => simp [inlineIdentityCode] at hc
    | stmt => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case callHalt funs V st fn args argvals st1 decl cenv Vend st2
      hargs hlookup hlen hbody ihargs ihbody =>
    cases code with
    | expr e =>
        obtain ⟨args0, rfl, hargsEq, hn⟩ := inlineIdentityExpr_eq_call
          (static := static) (by simpa [inlineIdentityCode] using hc.symm)
        have hargs0 := ihargs static outer (.args args0) hf
          (by simpa [inlineIdentityCode] using congrArg Code.args hargsEq)
        rw [hf] at hlookup
        cases hs : lookupFun static fn with
        | none =>
            have ho : lookupFun outer fn = some (decl, cenv) := by
              simpa [lookupFun_inline_append_of_none hs] using hlookup
            have hsource : lookupFun (static ++ outer) fn = some (decl, cenv) := by
              rw [lookupFun_append_of_none hs]
              exact ho
            exact Step.callHalt hargs0 hsource hlen hbody
        | some found =>
            rcases found with ⟨sdecl, closure⟩
            have ht := lookupFun_inline_append_of_some (outer := outer) hs
            rw [ht] at hlookup
            injection hlookup with heq
            obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
            have hb0 := ihbody closure outer
              (.stmt (.block sdecl.body)) rfl
              (by simp [inlineIdentityCode, inlineIdentityStmt, inlineIdentityDecl,
                inlineIdentityBlock])
            have hcall0 : Step D (static ++ outer) V st
                (.expr (.call fn args0)) (.eres (.halt st2)) :=
              Step.callHalt hargs0
                (lookupFun_append_of_some (outer := outer) hs)
                (by simpa [inlineIdentityDecl] using hlen) hb0
            exact hcall0
    | args => simp [inlineIdentityCode] at hc
    | stmt => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case callArgsHalt funs V st fn args st1 hargs ihargs =>
    cases code with
    | expr e =>
        obtain ⟨args0, rfl, hargsEq, hn⟩ := inlineIdentityExpr_eq_call
          (static := static) (by simpa [inlineIdentityCode] using hc.symm)
        exact Step.callArgsHalt
          (ihargs static outer (.args args0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.args hargsEq))
    | args => simp [inlineIdentityCode] at hc
    | stmt => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case argsNil funs V st =>
    cases code with
    | args args0 =>
        have ha : inlineIdentityArgs static args0 = [] := by
          simpa [inlineIdentityCode] using hc.symm
        have : args0 = [] := inlineIdentityArgs_eq_nil ha
        subst args0
        exact Step.argsNil
    | expr => simp [inlineIdentityCode] at hc
    | stmt => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case argsCons funs V st e rest restvals st1 v st2 hrest he ihrest ihe =>
    cases code with
    | args args0 =>
        have ha : inlineIdentityArgs static args0 = e :: rest := by
          simpa [inlineIdentityCode] using hc.symm
        obtain ⟨e0, rest0, rfl, heq, hreq⟩ := inlineIdentityArgs_eq_cons ha
        exact Step.argsCons
          (ihrest static outer (.args rest0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.args hreq.symm))
          (ihe static outer (.expr e0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.expr heq.symm))
    | expr => simp [inlineIdentityCode] at hc
    | stmt => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case argsRestHalt funs V st e rest st1 hrest ihrest =>
    cases code with
    | args args0 =>
        have ha : inlineIdentityArgs static args0 = e :: rest := by
          simpa [inlineIdentityCode] using hc.symm
        obtain ⟨e0, rest0, rfl, heq, hreq⟩ := inlineIdentityArgs_eq_cons ha
        exact Step.argsRestHalt
          (ihrest static outer (.args rest0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.args hreq.symm))
    | expr => simp [inlineIdentityCode] at hc
    | stmt => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case argsHeadHalt funs V st e rest restvals st1 st2 hrest he ihrest ihe =>
    cases code with
    | args args0 =>
        have ha : inlineIdentityArgs static args0 = e :: rest := by
          simpa [inlineIdentityCode] using hc.symm
        obtain ⟨e0, rest0, rfl, heq, hreq⟩ := inlineIdentityArgs_eq_cons ha
        exact Step.argsHeadHalt
          (ihrest static outer (.args rest0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.args hreq.symm))
          (ihe static outer (.expr e0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.expr heq.symm))
    | expr => simp [inlineIdentityCode] at hc
    | stmt => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case funDef funs V st n ps rs body =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineIdentityCode, inlineIdentityStmt] at hc
        exact Step.funDef
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case block funs V st bodyT Vb stb o hbody ihbody =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineIdentityCode, inlineIdentityStmt] at hc
        rename_i body
        have hbodyEq := hc
        have hfunEq : hoist D bodyT :: funs =
            inlineIdentityFuns (hoist D body :: static) ++ outer := by
          rw [hf, inlineIdentityFuns]
          simpa [hbodyEq, hoist_inlineIdentityStmts]
        have hcodeEq : Code.stmts bodyT = inlineIdentityCode
            (hoist D body :: static) (.stmts body) := by
          simpa [inlineIdentityCode, inlineIdentityBlock] using
            congrArg Code.stmts hbodyEq
        exact Step.block
          (ihbody (hoist D body :: static) outer (.stmts body) hfunEq hcodeEq)
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case letZero funs V st vars =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineIdentityCode, inlineIdentityStmt] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact Step.letZero
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case letVal funs V st vars eT vals st1 he hlen ihe =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineIdentityCode, inlineIdentityStmt] at hc
        rename_i vars0 val0
        cases val0 <;> simp at hc
        rename_i e0
        obtain ⟨rfl, heq⟩ := hc
        exact Step.letVal
          (ihe static outer (.expr e0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.expr heq.symm)) hlen
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case letHalt funs V st vars eT st1 he ihe =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineIdentityCode, inlineIdentityStmt] at hc
        rename_i vars0 val0
        cases val0 <;> simp at hc
        rename_i e0
        obtain ⟨rfl, heq⟩ := hc
        exact Step.letHalt
          (ihe static outer (.expr e0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.expr heq.symm))
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case assignVal funs V st vars eT vals st1 he hlen ihe =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineIdentityCode, inlineIdentityStmt] at hc
        rename_i vars0 e0
        obtain ⟨rfl, heq⟩ := hc
        exact Step.assignVal
          (ihe static outer (.expr e0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.expr heq)) hlen
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case assignHalt funs V st vars eT st1 he ihe =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineIdentityCode, inlineIdentityStmt] at hc
        rename_i vars0 e0
        obtain ⟨rfl, heq⟩ := hc
        exact Step.assignHalt
          (ihe static outer (.expr e0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.expr heq))
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case exprStmt funs V st eT st1 he ihe =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineIdentityCode, inlineIdentityStmt] at hc
        rename_i e0
        exact Step.exprStmt
          (ihe static outer (.expr e0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.expr hc))
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case exprStmtHalt funs V st eT st1 he ihe =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineIdentityCode, inlineIdentityStmt] at hc
        rename_i e0
        exact Step.exprStmtHalt
          (ihe static outer (.expr e0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.expr hc))
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case ifTrue funs V st cT bodyT cv st1 V' st2 o hcond hnz hbody ihcond ihbody =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineIdentityCode, inlineIdentityStmt] at hc
        rename_i c0 body0
        obtain ⟨hceq, hbeq⟩ := hc
        exact Step.ifTrue
          (ihcond static outer (.expr c0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.expr hceq)) hnz
          (ihbody static outer (.stmt (.block body0)) hf
            (by simpa [inlineIdentityCode, inlineIdentityStmt] using
              congrArg (fun b => Code.stmt (.block b)) hbeq))
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case ifFalse funs V st cT bodyT cv st1 hcond hz ihcond =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineIdentityCode, inlineIdentityStmt] at hc
        rename_i c0 body0
        obtain ⟨hceq, hbeq⟩ := hc
        exact Step.ifFalse (body := body0)
          (ihcond static outer (.expr c0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.expr hceq)) hz
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case ifHalt funs V st cT bodyT st1 hcond ihcond =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineIdentityCode, inlineIdentityStmt] at hc
        rename_i c0 body0
        obtain ⟨hceq, hbeq⟩ := hc
        exact Step.ifHalt (body := body0)
          (ihcond static outer (.expr c0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.expr hceq))
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case switchExec funs V st cT casesT dfltT cv st1 V' st2 o hcond hbody ihcond ihbody =>
    cases code with
    | stmt s =>
        cases s with
        | block body => simp [inlineIdentityCode, inlineIdentityStmt] at hc
        | funDef fn ps rs body => simp [inlineIdentityCode, inlineIdentityStmt] at hc
        | letDecl vars val => simp [inlineIdentityCode, inlineIdentityStmt] at hc
        | assign vars e => simp [inlineIdentityCode, inlineIdentityStmt] at hc
        | cond c body => simp [inlineIdentityCode, inlineIdentityStmt] at hc
        | forLoop init c post body => simp [inlineIdentityCode, inlineIdentityStmt] at hc
        | exprStmt e => simp [inlineIdentityCode, inlineIdentityStmt] at hc
        | «break» => simp [inlineIdentityCode, inlineIdentityStmt] at hc
        | «continue» => simp [inlineIdentityCode, inlineIdentityStmt] at hc
        | leave => simp [inlineIdentityCode, inlineIdentityStmt] at hc
        | switch c0 cases0 dflt0 =>
          rw [inlineIdentityCode, inlineIdentityStmt_switch] at hc
          simp only [Stmt.switch.injEq] at hc
          obtain ⟨hceq, rfl, rfl⟩ := hc
          have hc0 := ihcond static outer (.expr c0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.expr hceq)
          have hsel : selectSwitch D cv (inlineIdentityCases static cases0)
              (dflt0.map (inlineIdentityBlock static)) =
              inlineIdentityBlock static (selectSwitch D cv cases0 dflt0) := by
            simpa only [selectSwitch_open_eq] using
              selectSwitch_inlineIdentity static cv cases0 dflt0
          have hb0 := ihbody static outer
            (.stmt (.block (selectSwitch D cv cases0 dflt0))) hf
            (by simpa [inlineIdentityCode, inlineIdentityStmt, inlineIdentityBlock] using
              congrArg (fun b => Code.stmt (.block b)) hsel)
          exact Step.switchExec hc0 hb0
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case switchHalt funs V st cT casesT dfltT st1 hcond ihcond =>
    cases code with
    | stmt s =>
        cases s with
        | block body => simp [inlineIdentityCode, inlineIdentityStmt] at hc
        | funDef fn ps rs body => simp [inlineIdentityCode, inlineIdentityStmt] at hc
        | letDecl vars val => simp [inlineIdentityCode, inlineIdentityStmt] at hc
        | assign vars e => simp [inlineIdentityCode, inlineIdentityStmt] at hc
        | cond c body => simp [inlineIdentityCode, inlineIdentityStmt] at hc
        | forLoop init c post body => simp [inlineIdentityCode, inlineIdentityStmt] at hc
        | exprStmt e => simp [inlineIdentityCode, inlineIdentityStmt] at hc
        | «break» => simp [inlineIdentityCode, inlineIdentityStmt] at hc
        | «continue» => simp [inlineIdentityCode, inlineIdentityStmt] at hc
        | leave => simp [inlineIdentityCode, inlineIdentityStmt] at hc
        | switch c0 cases0 dflt0 =>
          rw [inlineIdentityCode, inlineIdentityStmt_switch] at hc
          simp only [Stmt.switch.injEq] at hc
          obtain ⟨hceq, rfl, rfl⟩ := hc
          exact Step.switchHalt (cases := cases0) (dflt := dflt0)
            (ihcond static outer (.expr c0) hf
              (by simpa [inlineIdentityCode] using congrArg Code.expr hceq))
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case forLoop funs V st initT cT postT bodyT Vinit stinit Vend stend o
      hinit hloop ihinit ihloop =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineIdentityCode, inlineIdentityStmt] at hc
        rename_i init0 c0 post0 body0
        obtain ⟨hiEq, hcEq, hpEq, hbEq⟩ := hc
        let loopStatic := hoist D init0 :: static
        have hfunEq : hoist D initT :: funs =
            inlineIdentityFuns loopStatic ++ outer := by
          rw [hf, inlineIdentityFuns]
          simpa [loopStatic, hiEq, hoist_inlineIdentityStmts]
        have hiCode : Code.stmts initT =
            inlineIdentityCode loopStatic (.stmts init0) := by
          simpa [inlineIdentityCode, loopStatic] using congrArg Code.stmts hiEq
        have hlCode : Code.loop cT postT bodyT =
            inlineIdentityCode loopStatic (.loop c0 post0 body0) := by
          simp only [inlineIdentityCode, Code.loop.injEq]
          exact ⟨hcEq, hpEq, hbEq⟩
        exact Step.forLoop
          (ihinit loopStatic outer (.stmts init0) hfunEq hiCode)
          (ihloop loopStatic outer (.loop c0 post0 body0) hfunEq hlCode)
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case forInitHalt funs V st initT cT postT bodyT Vinit stinit hinit ihinit =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineIdentityCode, inlineIdentityStmt] at hc
        rename_i init0 c0 post0 body0
        obtain ⟨hiEq, hcEq, hpEq, hbEq⟩ := hc
        let loopStatic := hoist D init0 :: static
        have hfunEq : hoist D initT :: funs =
            inlineIdentityFuns loopStatic ++ outer := by
          rw [hf, inlineIdentityFuns]
          simpa [loopStatic, hiEq, hoist_inlineIdentityStmts]
        have hiCode : Code.stmts initT =
            inlineIdentityCode loopStatic (.stmts init0) := by
          simpa [inlineIdentityCode, loopStatic] using congrArg Code.stmts hiEq
        exact Step.forInitHalt
          (ihinit loopStatic outer (.stmts init0) hfunEq hiCode)
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case «break» funs V st =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineIdentityCode, inlineIdentityStmt] at hc
        exact Step.break
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case «continue» funs V st =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineIdentityCode, inlineIdentityStmt] at hc
        exact Step.continue
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case leave funs V st =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineIdentityCode, inlineIdentityStmt] at hc
        exact Step.leave
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case seqNil funs V st =>
    cases code with
    | stmts ss0 =>
        have hs : inlineIdentityStmts static ss0 = [] := by
          simpa [inlineIdentityCode] using hc.symm
        have : ss0 = [] := inlineIdentityStmts_eq_nil hs
        subst ss0
        exact Step.seqNil
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmt => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case seqCons funs V st sT restT V1 st1 V2 st2 o hs hrest ihs ihrest =>
    cases code with
    | stmts ss0 =>
        have heq : inlineIdentityStmts static ss0 = sT :: restT := by
          simpa [inlineIdentityCode] using hc.symm
        obtain ⟨s0, rest0, rfl, hseq, hreq⟩ := inlineIdentityStmts_eq_cons heq
        exact Step.seqCons
          (ihs static outer (.stmt s0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.stmt hseq.symm))
          (ihrest static outer (.stmts rest0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.stmts hreq.symm))
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmt => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case seqStop funs V st sT restT V1 st1 o hs hne ihs =>
    cases code with
    | stmts ss0 =>
        have heq : inlineIdentityStmts static ss0 = sT :: restT := by
          simpa [inlineIdentityCode] using hc.symm
        obtain ⟨s0, rest0, rfl, hseq, hreq⟩ := inlineIdentityStmts_eq_cons heq
        exact Step.seqStop
          (ihs static outer (.stmt s0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.stmt hseq.symm)) hne
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmt => simp [inlineIdentityCode] at hc
    | loop => simp [inlineIdentityCode] at hc
  case loopDone funs V st cT postT bodyT cv st1 hcond hz ihcond =>
    cases code with
    | loop c0 post0 body0 =>
        simp only [inlineIdentityCode, Code.loop.injEq] at hc
        obtain ⟨hcEq, hpEq, hbEq⟩ := hc
        exact Step.loopDone
          (ihcond static outer (.expr c0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.expr hcEq)) hz
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmt => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
  case loopCondHalt funs V st cT postT bodyT st1 hcond ihcond =>
    cases code with
    | loop c0 post0 body0 =>
        simp only [inlineIdentityCode, Code.loop.injEq] at hc
        obtain ⟨hcEq, hpEq, hbEq⟩ := hc
        exact Step.loopCondHalt (post := post0) (body := body0)
          (ihcond static outer (.expr c0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.expr hcEq))
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmt => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
  case loopStep funs V st cT postT bodyT cv st1 Vb stb ob Vp stp Vend stend o
      hcond hnz hbody hob hpost hloop ihcond ihbody ihpost ihloop =>
    cases code with
    | loop c0 post0 body0 =>
        simp only [inlineIdentityCode, Code.loop.injEq] at hc
        obtain ⟨hcEq, hpEq, hbEq⟩ := hc
        exact Step.loopStep
          (ihcond static outer (.expr c0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.expr hcEq)) hnz
          (ihbody static outer (.stmt (.block body0)) hf
            (by simpa [inlineIdentityCode, inlineIdentityStmt] using
              congrArg (fun b => Code.stmt (.block b)) hbEq)) hob
          (ihpost static outer (.stmt (.block post0)) hf
            (by simpa [inlineIdentityCode, inlineIdentityStmt] using
              congrArg (fun b => Code.stmt (.block b)) hpEq))
          (ihloop static outer (.loop c0 post0 body0) hf
            (by simp only [inlineIdentityCode, Code.loop.injEq]; exact ⟨hcEq, hpEq, hbEq⟩))
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmt => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
  case loopPostHalt funs V st cT postT bodyT cv st1 Vb stb ob Vp stp
      hcond hnz hbody hob hpost ihcond ihbody ihpost =>
    cases code with
    | loop c0 post0 body0 =>
        simp only [inlineIdentityCode, Code.loop.injEq] at hc
        obtain ⟨hcEq, hpEq, hbEq⟩ := hc
        exact Step.loopPostHalt
          (ihcond static outer (.expr c0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.expr hcEq)) hnz
          (ihbody static outer (.stmt (.block body0)) hf
            (by simpa [inlineIdentityCode, inlineIdentityStmt] using
              congrArg (fun b => Code.stmt (.block b)) hbEq)) hob
          (ihpost static outer (.stmt (.block post0)) hf
            (by simpa [inlineIdentityCode, inlineIdentityStmt] using
              congrArg (fun b => Code.stmt (.block b)) hpEq))
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmt => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
  case loopBreak funs V st cT postT bodyT cv st1 Vb stb hcond hnz hbody ihcond ihbody =>
    cases code with
    | loop c0 post0 body0 =>
        simp only [inlineIdentityCode, Code.loop.injEq] at hc
        obtain ⟨hcEq, hpEq, hbEq⟩ := hc
        exact Step.loopBreak (post := post0)
          (ihcond static outer (.expr c0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.expr hcEq)) hnz
          (ihbody static outer (.stmt (.block body0)) hf
            (by simpa [inlineIdentityCode, inlineIdentityStmt] using
              congrArg (fun b => Code.stmt (.block b)) hbEq))
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmt => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
  case loopLeave funs V st cT postT bodyT cv st1 Vb stb hcond hnz hbody ihcond ihbody =>
    cases code with
    | loop c0 post0 body0 =>
        simp only [inlineIdentityCode, Code.loop.injEq] at hc
        obtain ⟨hcEq, hpEq, hbEq⟩ := hc
        exact Step.loopLeave (post := post0)
          (ihcond static outer (.expr c0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.expr hcEq)) hnz
          (ihbody static outer (.stmt (.block body0)) hf
            (by simpa [inlineIdentityCode, inlineIdentityStmt] using
              congrArg (fun b => Code.stmt (.block b)) hbEq))
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmt => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc
  case loopBodyHalt funs V st cT postT bodyT cv st1 Vb stb hcond hnz hbody ihcond ihbody =>
    cases code with
    | loop c0 post0 body0 =>
        simp only [inlineIdentityCode, Code.loop.injEq] at hc
        obtain ⟨hcEq, hpEq, hbEq⟩ := hc
        exact Step.loopBodyHalt (post := post0)
          (ihcond static outer (.expr c0) hf
            (by simpa [inlineIdentityCode] using congrArg Code.expr hcEq)) hnz
          (ihbody static outer (.stmt (.block body0)) hf
            (by simpa [inlineIdentityCode, inlineIdentityStmt] using
              congrArg (fun b => Code.stmt (.block b)) hbEq))
    | expr => simp [inlineIdentityCode] at hc
    | args => simp [inlineIdentityCode] at hc
    | stmt => simp [inlineIdentityCode] at hc
    | stmts => simp [inlineIdentityCode] at hc

theorem inlineIdentityBlock_equiv (b : Block Op) :
    EquivBlock D b (inlineIdentityBlock (calls := calls) (creates := creates)
      ([] : FunEnv D) b) := by
  intro funs V st V' st' o
  constructor
  · intro h
    have hf := YulEvmCompiler.Optimizer.Step.inlineIdentity_forward h
      ([] : FunEnv D) funs rfl
    simpa [inlineIdentityCode, inlineIdentityStmt, inlineIdentityBlock,
      inlineIdentityFuns] using hf
  · intro h
    exact YulEvmCompiler.Optimizer.Step.inlineIdentity_reverse h
      ([] : FunEnv D) funs
      (.stmt (.block b)) (by simp [inlineIdentityFuns])
      (by simp [inlineIdentityCode, inlineIdentityStmt, inlineIdentityBlock])

def inlineIdentityPass : Pass D where
  run := inlineIdentityBlock (calls := calls) (creates := creates) []
  sound := inlineIdentityBlock_equiv


end YulEvmCompiler.Optimizer
