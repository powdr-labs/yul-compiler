import YulEvmCompiler.Optimizer.Spec.Pass
import YulEvmCompiler.Optimizer.Implementation.Simplify
import YulEvmCompiler.Optimizer.Core.Subst
import YulSemantics.Determinism
set_option warningAsError true
/-!
# Inline pure expression-body helpers, via Core

This pass generalizes (and replaces) the former exact-identity inliner: any
helper whose body is a single assignment of an intrinsically scoped, pure Core
term over its parameters is inlined at compatible call sites.

If lexical Yul lookup resolves `f` to

```
function f(p₁, …, pₙ) -> r { r := e }
```

where `e` ingests into the Core expression fragment over `Γ = [p₁, …, pₙ]`
(one pure built-in over parameters and literals, or a bare parameter), then:

* **bare parameter** (`r := p`) — `f(e)` becomes `add(e, 0)` for *any* single
  argument. The apparently redundant `add` is the soundness fence: both sides
  require `e` to produce exactly one value, and `e` may be an arbitrary
  effectful expression. A following `Simplify` pass removes the fence where it
  has proved that removal sound.
* **pure built-in body** (`r := op(…)`) — `f(v₁, …, vₙ)` becomes the body with
  each parameter replaced by its argument (`Term.substEmit`), provided every
  argument is *value-shaped* (a variable or non-string literal). This is
  closed-term instantiation on the Core term: capture and dangling references
  are unrepresentable, and the ANF discipline makes discarding or duplicating
  an argument sound because value-shaped arguments are pure. Classification
  requires every parameter to be *read* by the body, so the rewrite also
  preserves stuckness on unbound argument variables.

Call sites Core does not cover — recursive helpers, multi-statement or
effectful bodies, non-value arguments of built-in-body helpers, arity
mismatches — keep the ordinary call and the full verified call protocol.

The `litOK` flag selects the classification used by the object pipeline:
object-layout resolution rewrites `dataoffset`/`datasize` applications into
number literals, so classification of a body *containing literals* is not
stable under resolution. With `litOK := false` bodies must read variables
only, which resolution can neither create nor destroy; the block pipeline
uses `litOK := true`.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler.Optimizer.Core (Ctx Term Value Var Args PureOp ingest ingest_emit
  isValueExpr valueEval valuesEval)

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-! ## Classification -/

/-- A classified helper: parameters, the single return variable, and the
intrinsically scoped Core body term, together with the invariants the rewrite
arms rely on. `used` guarantees every parameter is read (so dropping the call
protocol cannot un-stick an unbound argument variable); `stringFree` keeps the
inlined syntax disjoint from the object-layout hooks; `shape` restricts to the
two supported body shapes. -/
structure Helper where
  /-- The helper's parameter names, innermost Core context order. -/
  params : Ctx
  /-- The helper's single return variable. -/
  ret : Ident
  /-- The body's right-hand side, as an intrinsically scoped Core term. -/
  term : Term params 1
  /-- Parameters are distinct. -/
  nodup : params.Nodup
  /-- Every parameter is read by the body. -/
  used : ∀ p ∈ params, p ∈ term.vars
  /-- The body mentions no string literal. -/
  stringFree : term.stringFree = true
  /-- The body is a bare parameter or a pure built-in application. -/
  shape : term.inlinableShape = true

/-- Decide the `Helper` classification of a declaration. With
`litOK := false`, built-in bodies must read variables only (the
resolution-stable fragment); `litOK := true` also admits literal arguments. -/
def helper? (litOK : Bool) (decl : FDecl D) : Option Helper :=
  match decl with
  | ⟨params, [ret], [.assign [ret'] body]⟩ =>
      if ret' = ret then
        match ingest params body with
        | some term =>
            if hcond : params.Nodup ∧ (∀ p ∈ params, p ∈ term.vars) ∧
                term.stringFree = true ∧ term.inlinableShape = true ∧
                (litOK || term.argsVarsOnly) = true then
              some ⟨params, ret, term, hcond.1, hcond.2.1, hcond.2.2.1, hcond.2.2.2.1⟩
            else none
        | none => none
      else none
  | _ => none

/-- Successful classification pins the declaration exactly: it is the single
assignment of the classified term's erasure (by the Core boundary theorem),
and under the resolution-stable mode the term reads variables only. -/
theorem helper?_shape {litOK : Bool} {decl : FDecl D} {h : Helper}
    (hcl : helper? (calls := calls) (creates := creates) litOK decl = some h) :
    decl = ⟨h.params, [h.ret], [.assign [h.ret] h.term.emit]⟩ ∧
      (litOK || h.term.argsVarsOnly) = true := by
  unfold helper? at hcl
  split at hcl
  next params ret ret' body =>
    split at hcl
    next hret =>
      subst hret
      split at hcl
      next term hingest =>
        split at hcl
        next hcond =>
          injection hcl with hcl
          subst hcl
          exact ⟨by rw [ingest_emit hingest], hcond.2.2.2.2⟩
        next => cases hcl
      next => cases hcl
    next => cases hcl
  next => cases hcl

/-- A nodup list in which every member equals `x`, containing `x`, is `[x]`. -/
theorem list_eq_singleton_of_nodup {l : List Ident} {x : Ident}
    (hnd : l.Nodup) (hx : x ∈ l) (hall : ∀ p ∈ l, p = x) : l = [x] := by
  cases l with
  | nil => cases hx
  | cons p rest =>
      have hp : p = x := hall p (by simp)
      subst hp
      cases rest with
      | nil => rfl
      | cons q qrest =>
          have hq : q = p := hall q (by simp)
          have hpnotin := (List.nodup_cons.mp hnd).1
          exact absurd (by simp [hq]) hpnotin

/-- A bare-parameter body forces a single parameter: the helper is an exact
identity `function f(x) -> r { r := x }`. -/
theorem Helper.atom_params (h : Helper) {ref : Var h.params}
    (hterm : h.term = .atom (.var ref)) : h.params = [ref.name] := by
  have hused := h.used
  rw [hterm] at hused
  simp only [Core.Term.vars, Core.Value.vars, List.mem_singleton] at hused
  exact list_eq_singleton_of_nodup h.nodup ref.bound hused

/-- An atom-shaped classified term is a bare parameter (bare literals are
rejected by `shape`). -/
theorem Helper.atom_isVar (h : Helper) {value : Value h.params}
    (hterm : h.term = .atom value) : ∃ ref : Var h.params, value = .var ref := by
  have hshape := h.shape
  rw [hterm] at hshape
  cases value with
  | var ref => exact ⟨ref, rfl⟩
  | lit literal => simp [Core.Term.inlinableShape, Core.Value.isVar] at hshape

/-- The two body shapes a classified helper can have. -/
theorem Helper.term_cases (h : Helper) :
    (∃ ref : Var h.params, h.term = .atom (.var ref)) ∨
    (∃ (arity : Nat) (op : PureOp arity) (targs : Args h.params arity),
      h.term = .builtin op targs) := by
  obtain ⟨params, ret, term, nodup, used, hsf, hshape⟩ := h
  cases term with
  | atom value =>
      cases value with
      | var ref => exact Or.inl ⟨ref, rfl⟩
      | lit literal => simp [Core.Term.inlinableShape, Core.Value.isVar] at hshape
  | builtin op targs => exact Or.inr ⟨_, op, targs, rfl⟩

/-- Does ordinary ordered lexical lookup resolve `fn` to an inlinable helper? -/
def resolveHelper (litOK : Bool) (static : FunEnv D) (fn : Ident) : Option Helper :=
  match lookupFun static fn with
  | some (decl, _) => helper? litOK decl
  | none => none

/-! ## The transform -/

/-- The argument shapes the substitution arm accepts. `litOK := true` admits
any value-shaped argument; `litOK := false` restricts to bare variables — the
shape object-layout resolution can neither create nor destroy, keeping the
rewrite decision stable across resolution. -/
def argOK (litOK : Bool) (e : Expr Op) : Prop :=
  isValueExpr e = true ∧ (litOK = true ∨ Core.isVarExpr e = true)

instance {litOK : Bool} {e : Expr Op} : Decidable (argOK litOK e) := by
  unfold argOK
  infer_instance

/-- Rewrite one call whose callee classified as `h`. The bare-parameter arm
fires at any single argument (the `add(e, 0)` fence); the built-in arm fires
when the arguments are acceptable and arity-correct, and substitutes them
into the body term. Anything else keeps the call. -/
def rewriteCall (litOK : Bool) (h : Helper) (fn : Ident) (args : List (Expr Op)) : Expr Op :=
  match h.term with
  | .atom _ =>
      match args with
      | [arg] => .builtin .add [arg, .lit (.number 0)]
      | _ => .call fn args
  | .builtin op targs =>
      if args.length = h.params.length ∧ (∀ e ∈ args, argOK litOK e) then
        (Term.builtin op targs).substEmit args
      else .call fn args

/-- Reduce the rewrite at a bare-parameter helper. -/
theorem rewriteCall_atom {litOK : Bool} {h : Helper} {ref : Var h.params}
    (hterm : h.term = .atom (.var ref)) (fn : Ident) (args : List (Expr Op)) :
    rewriteCall litOK h fn args =
      match args with
      | [arg] => .builtin .add [arg, .lit (.number 0)]
      | _ => .call fn args := by
  rw [rewriteCall.eq_def, hterm]

/-- Reduce the rewrite at a built-in-body helper whose site is flat. -/
theorem rewriteCall_builtin_pos {litOK : Bool} {h : Helper} {arity : Nat} {op : PureOp arity}
    {targs : Args h.params arity} (hterm : h.term = .builtin op targs)
    {fn : Ident} {args : List (Expr Op)}
    (hcond : args.length = h.params.length ∧ (∀ e ∈ args, argOK litOK e)) :
    rewriteCall litOK h fn args = (Term.builtin op targs).substEmit args := by
  have hred : rewriteCall litOK h fn args =
      if args.length = h.params.length ∧ (∀ e ∈ args, argOK litOK e) then
        (Term.builtin op targs).substEmit args
      else .call fn args := by
    rw [rewriteCall.eq_def, hterm]
  rw [hred, if_pos hcond]

/-- Reduce the rewrite at a built-in-body helper whose site is not flat. -/
theorem rewriteCall_builtin_neg {litOK : Bool} {h : Helper} {arity : Nat} {op : PureOp arity}
    {targs : Args h.params arity} (hterm : h.term = .builtin op targs)
    {fn : Ident} {args : List (Expr Op)}
    (hcond : ¬(args.length = h.params.length ∧ (∀ e ∈ args, argOK litOK e))) :
    rewriteCall litOK h fn args = .call fn args := by
  have hred : rewriteCall litOK h fn args =
      if args.length = h.params.length ∧ (∀ e ∈ args, argOK litOK e) then
        (Term.builtin op targs).substEmit args
      else .call fn args := by
    rw [rewriteCall.eq_def, hterm]
  rw [hred, if_neg hcond]

/-- The rewrite never produces a variable or a literal. -/
theorem rewriteCall_not_value {litOK : Bool} (h : Helper) (fn : Ident) (args : List (Expr Op)) :
    isValueExpr (rewriteCall litOK h fn args) = false := by
  rw [rewriteCall.eq_def]
  split
  · split <;> rfl
  · split
    · rfl
    · rfl

mutual

/-- Rewrite expressions under the original program's lexical scope stack. -/
def inlineHelpersExpr (litOK : Bool) (static : FunEnv D) : Expr Op → Expr Op
  | .lit l => .lit l
  | .var x => .var x
  | .builtin op args => .builtin op (inlineHelpersArgs litOK static args)
  | .call fn args =>
      let args' := inlineHelpersArgs litOK static args
      match resolveHelper (calls := calls) (creates := creates) litOK static fn with
      | some h => rewriteCall litOK h fn args'
      | none => .call fn args'

/-- Rewrite an argument list. -/
def inlineHelpersArgs (litOK : Bool) (static : FunEnv D) : List (Expr Op) → List (Expr Op)
  | [] => []
  | e :: rest => inlineHelpersExpr litOK static e :: inlineHelpersArgs litOK static rest

end

mutual

/-- Rewrite a statement. Every nested block pushes its own hoisted scope. -/
def inlineHelpersStmt (litOK : Bool) (static : FunEnv D) : Stmt Op → Stmt Op
  | .block body =>
      .block (inlineHelpersStmts litOK (hoist D body :: static) body)
  | .funDef fn params rets body =>
      .funDef fn params rets (inlineHelpersStmts litOK (hoist D body :: static) body)
  | .letDecl vars value => .letDecl vars (value.map (inlineHelpersExpr litOK static))
  | .assign vars value => .assign vars (inlineHelpersExpr litOK static value)
  | .cond c body =>
      .cond (inlineHelpersExpr litOK static c)
        (inlineHelpersStmts litOK (hoist D body :: static) body)
  | .switch c cases dflt =>
      .switch (inlineHelpersExpr litOK static c) (inlineHelpersCases litOK static cases)
        (match dflt with
        | none => none
        | some body => some (inlineHelpersStmts litOK (hoist D body :: static) body))
  | .forLoop init c post body =>
      let loopStatic := hoist D init :: static
      .forLoop (inlineHelpersStmts litOK loopStatic init)
        (inlineHelpersExpr litOK loopStatic c)
        (inlineHelpersStmts litOK (hoist D post :: loopStatic) post)
        (inlineHelpersStmts litOK (hoist D body :: loopStatic) body)
  | .exprStmt e => .exprStmt (inlineHelpersExpr litOK static e)
  | .break => .break
  | .continue => .continue
  | .leave => .leave
  termination_by statement => 2 * sizeOf statement + 1
  decreasing_by all_goals simp_wf <;> omega

/-- Rewrite a statement sequence under an already-established scope stack. -/
def inlineHelpersStmts (litOK : Bool) (static : FunEnv D) : Block Op → Block Op
  | [] => []
  | s :: rest => inlineHelpersStmt litOK static s :: inlineHelpersStmts litOK static rest
  termination_by statements => 2 * sizeOf statements
  decreasing_by all_goals simp_wf <;> omega

/-- Rewrite switch cases, each of whose body is a block. -/
def inlineHelpersCases (litOK : Bool) (static : FunEnv D) :
    List (Literal × Block Op) → List (Literal × Block Op)
  | [] => []
  | (l, body) :: rest =>
      (l, inlineHelpersStmts litOK (hoist D body :: static) body) ::
        inlineHelpersCases litOK static rest
  termination_by cases => 2 * sizeOf cases
  decreasing_by all_goals simp_wf <;> omega

end

/-- Rewrite a block, installing its hoisted scope before traversing it. -/
def inlineHelpersBlock (litOK : Bool) (outer : FunEnv D) (body : Block Op) : Block Op :=
  inlineHelpersStmts litOK (hoist D body :: outer) body

/-- Transform a declaration body under its definition-site static closure. -/
def inlineHelpersDecl (litOK : Bool) (static : FunEnv D) (decl : FDecl D) : FDecl D :=
  { decl with body := inlineHelpersBlock litOK static decl.body }

/-- Transform every declaration in one ordered scope. -/
def inlineHelpersScope (litOK : Bool) (static : FunEnv D) (scope : FScope D) : FScope D :=
  scope.map fun entry => (entry.1, inlineHelpersDecl litOK static entry.2)

/-- Transform a complete static scope stack. A declaration in each scope sees
that scope and every following (outer) scope as its closure. -/
def inlineHelpersFuns (litOK : Bool) : FunEnv D → FunEnv D
  | [] => []
  | scope :: outer =>
      inlineHelpersScope litOK (scope :: outer) scope :: inlineHelpersFuns litOK outer

/-- Transform any of the five semantic code classes. -/
def inlineHelpersCode (litOK : Bool) (static : FunEnv D) : Code Op → Code Op
  | .expr e => .expr (inlineHelpersExpr litOK static e)
  | .args args => .args (inlineHelpersArgs litOK static args)
  | .stmt s => .stmt (inlineHelpersStmt litOK static s)
  | .stmts ss => .stmts (inlineHelpersStmts litOK static ss)
  | .loop c post body =>
      .loop (inlineHelpersExpr litOK static c)
        (inlineHelpersStmts litOK (hoist D post :: static) post)
        (inlineHelpersStmts litOK (hoist D body :: static) body)

/-! ## Rewrite equations -/

theorem inlineHelpersExpr_call_none {litOK : Bool} (static : FunEnv D) (fn : Ident)
    (args : List (Expr Op))
    (h : resolveHelper (calls := calls) (creates := creates) litOK static fn = none) :
    inlineHelpersExpr litOK static (.call fn args) =
      .call fn (inlineHelpersArgs litOK static args) := by
  rw [inlineHelpersExpr, h]

theorem inlineHelpersExpr_call_some {litOK : Bool} (static : FunEnv D) (fn : Ident)
    (args : List (Expr Op)) {h : Helper}
    (hres : resolveHelper (calls := calls) (creates := creates) litOK static fn = some h) :
    inlineHelpersExpr litOK static (.call fn args) =
      rewriteCall litOK h fn (inlineHelpersArgs litOK static args) := by
  rw [inlineHelpersExpr, hres]

@[simp] theorem inlineHelpersStmt_switch {litOK : Bool} (static : FunEnv D) (c : Expr Op)
    (cases : List (Literal × Block Op)) (dflt : Option (Block Op)) :
    inlineHelpersStmt litOK static (.switch c cases dflt) =
      .switch (inlineHelpersExpr litOK static c) (inlineHelpersCases litOK static cases)
        (dflt.map (inlineHelpersBlock litOK static)) := by
  cases dflt <;> rw [inlineHelpersStmt.eq_def] <;> rfl

/-! ## Structural scope facts -/

theorem hoist_inlineHelpersStmts {litOK : Bool} (static : FunEnv D) : ∀ body : Block Op,
    hoist D (inlineHelpersStmts litOK static body) =
      inlineHelpersScope litOK static (hoist D body)
  | [] => by simp [inlineHelpersStmts, hoist, inlineHelpersScope]
  | .funDef fn params rets body :: rest => by
      rw [inlineHelpersStmts, inlineHelpersStmt]
      simp only [hoist, List.filterMap_cons, inlineHelpersScope, List.map_cons,
        inlineHelpersDecl]
      congr 1
      change hoist D (inlineHelpersStmts litOK static rest) =
        inlineHelpersScope litOK static (hoist D rest)
      exact hoist_inlineHelpersStmts static rest
  | .block _ :: rest => by
      rw [inlineHelpersStmts, inlineHelpersStmt]
      simpa [hoist, inlineHelpersScope] using hoist_inlineHelpersStmts static rest
  | .letDecl _ _ :: rest => by
      rw [inlineHelpersStmts, inlineHelpersStmt]
      simpa [hoist, inlineHelpersScope] using hoist_inlineHelpersStmts static rest
  | .assign _ _ :: rest => by
      rw [inlineHelpersStmts, inlineHelpersStmt]
      simpa [hoist, inlineHelpersScope] using hoist_inlineHelpersStmts static rest
  | .cond _ _ :: rest => by
      rw [inlineHelpersStmts, inlineHelpersStmt]
      simpa [hoist, inlineHelpersScope] using hoist_inlineHelpersStmts static rest
  | .switch c cases dflt :: rest => by
      cases dflt <;>
      rw [inlineHelpersStmts, inlineHelpersStmt]
      all_goals
        change hoist D (inlineHelpersStmts litOK static rest) =
          inlineHelpersScope litOK static (hoist D rest)
        exact hoist_inlineHelpersStmts static rest
  | .forLoop _ _ _ _ :: rest => by
      rw [inlineHelpersStmts, inlineHelpersStmt]
      simpa [hoist, inlineHelpersScope] using hoist_inlineHelpersStmts static rest
  | .exprStmt _ :: rest => by
      rw [inlineHelpersStmts, inlineHelpersStmt]
      simpa [hoist, inlineHelpersScope] using hoist_inlineHelpersStmts static rest
  | .break :: rest => by
      rw [inlineHelpersStmts, inlineHelpersStmt]
      simpa [hoist, inlineHelpersScope] using hoist_inlineHelpersStmts static rest
  | .continue :: rest => by
      rw [inlineHelpersStmts, inlineHelpersStmt]
      simpa [hoist, inlineHelpersScope] using hoist_inlineHelpersStmts static rest
  | .leave :: rest => by
      rw [inlineHelpersStmts, inlineHelpersStmt]
      simpa [hoist, inlineHelpersScope] using hoist_inlineHelpersStmts static rest

@[simp] theorem hoist_inlineHelpersBlock {litOK : Bool} (outer : FunEnv D) (body : Block Op) :
    hoist D (inlineHelpersBlock litOK outer body) =
      inlineHelpersScope litOK (hoist D body :: outer) (hoist D body) := by
  exact hoist_inlineHelpersStmts _ body

@[simp] theorem inlineHelpersFuns_cons {litOK : Bool} (scope : FScope D) (outer : FunEnv D) :
    inlineHelpersFuns litOK (scope :: outer) =
      inlineHelpersScope litOK (scope :: outer) scope :: inlineHelpersFuns litOK outer := rfl

theorem selectSwitch_inlineHelpers {litOK : Bool} (static : FunEnv D) (value : U256)
    (cases : List (Literal × Block Op)) (dflt : Option (Block Op)) :
    selectSwitch evm value (inlineHelpersCases litOK static cases)
        (dflt.map (inlineHelpersBlock litOK static)) =
      inlineHelpersBlock litOK static (selectSwitch evm value cases dflt) := by
  induction cases with
  | nil => cases dflt <;>
      simp [selectSwitch, inlineHelpersCases, inlineHelpersBlock, inlineHelpersStmts]
  | cons head rest ih =>
      rcases head with ⟨l, body⟩
      by_cases h : decide (value = litValue l) = true
      · simp [selectSwitch, inlineHelpersCases, inlineHelpersBlock, h]
      · simpa [selectSwitch, inlineHelpersCases, h] using ih

/-! ## Value expressions are fixed points of the transform -/

theorem inlineHelpersExpr_value {litOK : Bool} (static : FunEnv D) {e : Expr Op}
    (he : isValueExpr e = true) : inlineHelpersExpr litOK static e = e := by
  cases e with
  | lit l => rfl
  | var x => rfl
  | builtin op args => simp [isValueExpr] at he
  | call fn args => simp [isValueExpr] at he

theorem inlineHelpersArgs_values {litOK : Bool} (static : FunEnv D) {args : List (Expr Op)}
    (hargs : ∀ e ∈ args, isValueExpr e = true) :
    inlineHelpersArgs litOK static args = args := by
  induction args with
  | nil => rfl
  | cons e rest ih =>
      rw [inlineHelpersArgs, inlineHelpersExpr_value static (hargs e (by simp)),
        ih (fun e' h' => hargs e' (by simp [h']))]

/-- The transform never *creates* a value-shaped expression: an output
variable or literal was already that variable or literal. -/
theorem inlineHelpersExpr_value_inv {litOK : Bool} (static : FunEnv D) {e : Expr Op}
    (he : isValueExpr (inlineHelpersExpr litOK static e) = true) :
    inlineHelpersExpr litOK static e = e ∧ isValueExpr e = true := by
  cases e with
  | lit l => exact ⟨rfl, he⟩
  | var x => exact ⟨rfl, he⟩
  | builtin op args =>
      rw [inlineHelpersExpr] at he
      simp [isValueExpr] at he
  | call fn args =>
      rw [inlineHelpersExpr] at he
      split at he
      · rw [rewriteCall_not_value] at he
        cases he
      · simp [isValueExpr] at he

/-! ## Classified helpers are fixed points of the transform -/

/-- The emitted body of a classified term is unchanged by the transform: its
argument positions hold only variables and literals. -/
theorem inlineHelpersExpr_emit_fixed {litOK : Bool} (static : FunEnv D) {Γ : Ctx}
    (term : Term Γ 1) (hsf : term.stringFree = true) :
    inlineHelpersExpr litOK static term.emit = term.emit := by
  cases term with
  | atom value =>
      exact inlineHelpersExpr_value static
        (Core.emit_isValue (by simpa [Core.Term.stringFree] using hsf))
  | builtin op targs =>
      have hvals : ∀ e ∈ targs.emit, isValueExpr e = true := by
        intro e he
        rw [Core.Args.emit] at he
        obtain ⟨value, hvmem, rfl⟩ := List.mem_map.mp he
        refine Core.emit_isValue ?_
        rw [Core.Term.stringFree] at hsf
        exact List.all_eq_true.mp hsf value hvmem
      show inlineHelpersExpr litOK static (.builtin op.toOp targs.emit) =
        Expr.builtin op.toOp targs.emit
      rw [inlineHelpersExpr, inlineHelpersArgs_values static hvals]

/-- A classified helper's declaration is untouched by the transform, in any
static scope. This is what lets a call site's rewrite consult the *original*
body shape after the pass has run over every declaration. -/
theorem inlineHelpersDecl_helper {litOK litOK' : Bool} (static : FunEnv D) {decl : FDecl D}
    {h : Helper}
    (hcl : helper? (calls := calls) (creates := creates) litOK' decl = some h) :
    inlineHelpersDecl litOK static decl = decl := by
  obtain ⟨hdecl, -⟩ := helper?_shape hcl
  subst hdecl
  have hbody : inlineHelpersBlock (calls := calls) (creates := creates) litOK static
      [Stmt.assign [h.ret] h.term.emit] = [Stmt.assign [h.ret] h.term.emit] := by
    rw [inlineHelpersBlock, inlineHelpersStmts, inlineHelpersStmt,
      inlineHelpersExpr_emit_fixed _ _ h.stringFree, inlineHelpersStmts]
  simp [inlineHelpersDecl, hbody]

/-! ## Lexical lookup through the transformed scope stack -/

theorem find?_inlineHelpersScope {litOK : Bool} (static : FunEnv D) (scope : FScope D)
    (fn : Ident) :
    (inlineHelpersScope litOK static scope).find? (fun entry => entry.1 = fn) =
      (scope.find? (fun entry => entry.1 = fn)).map
        (fun entry => (entry.1, inlineHelpersDecl litOK static entry.2)) := by
  rw [inlineHelpersScope, List.find?_map]
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

theorem lookupFun_inlineHelpersFuns {litOK : Bool} {static closure : FunEnv D}
    {fn : Ident} {decl : FDecl D}
    (h : lookupFun static fn = some (decl, closure)) :
    lookupFun (inlineHelpersFuns litOK static) fn =
      some (inlineHelpersDecl litOK closure decl, inlineHelpersFuns litOK closure) := by
  induction static with
  | nil => simp [lookupFun] at h
  | cons scope rest ih =>
      cases hs : scope.find? (fun entry => entry.1 = fn) with
      | some entry =>
          rw [lookupFun, hs] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [inlineHelpersFuns, lookupFun, find?_inlineHelpersScope, hs]
          rfl
      | none =>
          rw [lookupFun, hs] at h
          rw [inlineHelpersFuns, lookupFun, find?_inlineHelpersScope, hs]
          exact ih h

theorem lookupFun_inline_append_of_some {litOK : Bool} {static closure outer : FunEnv D}
    {fn : Ident} {decl : FDecl D}
    (h : lookupFun static fn = some (decl, closure)) :
    lookupFun (inlineHelpersFuns litOK static ++ outer) fn =
      some (inlineHelpersDecl litOK closure decl, inlineHelpersFuns litOK closure ++ outer) :=
  lookupFun_append_of_some (lookupFun_inlineHelpersFuns h)

theorem lookupFun_inline_append_of_none {litOK : Bool} {static outer : FunEnv D} {fn : Ident}
    (h : lookupFun static fn = none) :
    lookupFun (inlineHelpersFuns litOK static ++ outer) fn = lookupFun outer fn := by
  apply lookupFun_append_of_none
  induction static with
  | nil => rfl
  | cons scope rest ih =>
      cases hs : scope.find? (fun entry => entry.1 = fn) with
      | some entry => simp [lookupFun, hs] at h
      | none =>
          rw [lookupFun, hs] at h
          rw [inlineHelpersFuns, lookupFun, find?_inlineHelpersScope, hs]
          exact ih h

/-! ## Argument-list facts for the identity fence -/

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

/-! ## Variable-environment plumbing -/

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

/-- Setting a bound variable and reading it back yields the new value. -/
theorem venv_get_set_of_mem {V : VEnv D} {x : Ident} (v : U256)
    (hx : x ∈ V.map Prod.fst) :
    VEnv.get (VEnv.set V x v) x = some v := by
  induction V with
  | nil => simp at hx
  | cons entry rest ih =>
      rcases entry with ⟨y, w⟩
      by_cases hyx : y = x
      · subst hyx
        simp [VEnv.set, VEnv.get]
      · simp only [List.map_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact absurd rfl hyx
        · rw [VEnv.set, if_neg hyx]
          unfold VEnv.get at ih ⊢
          rw [List.find?_cons_of_neg (by simpa using hyx)]
          exact ih hx

/-- The single return variable is bound in the callee frame. -/
theorem ret_mem_frame {params : Ctx} {argvals : List U256} {ret : Ident} :
    ret ∈ (((params.zip argvals : VEnv D) ++ bindZeros D [ret]) : VEnv D).map Prod.fst := by
  simp [bindZeros]

/-! ## The identity-fence call equivalence (bare-parameter bodies) -/

/-- Executing the exact identity body returns its input word and leaves state
unchanged. The `param = ret` shadowing corner is handled explicitly. -/
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
      (Step.assignVal (Step.var (by simp [VEnv.get])) (by simp)) Step.seqNil
  · by_cases hpr : param = ret <;>
      simp [V0, V1, bindZeros, VEnv.get, VEnv.setMany, VEnv.set, restore, hpr]

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
        simp only [List.map_cons, List.map_nil] at *
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

/-! ## The substitution call equivalence (pure built-in bodies) -/

/-- A typed pure operation applied at its arity always folds. -/
theorem pureOp_pureFn {arity : Nat} (op : PureOp arity) {vs : List U256}
    (hlen : vs.length = arity) : ∃ w, pureFn op.toOp vs = some w := by
  cases op <;>
    first
      | (obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen
         exact ⟨_, rfl⟩)
      | (obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
         exact ⟨_, rfl⟩)
      | (obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hlen
         exact ⟨_, rfl⟩)

/-- Construct the evaluation of an emitted built-in term from the functional
evaluation of its values. -/
theorem term_emit_eval {funs : FunEnv D} {V : VEnv D} {st : EvmState} {Γ : Ctx}
    {arity : Nat} {op : PureOp arity} {targs : Args Γ arity}
    (hsf : (Term.builtin op targs).stringFree = true)
    {ws : List U256} {w : U256}
    (hvals : valuesEval (calls := calls) (creates := creates) V
      (targs.values.map Value.emit) = some ws)
    (hop : pureFn op.toOp ws = some w) :
    Step D funs V st (.expr (Term.builtin op targs).emit) (.eres (.vals [w] st)) := by
  refine Step.builtinOk ?_ (pureFn_builtin (calls := calls) (creates := creates) hop st)
  show Step D funs V st (.args (targs.values.map Value.emit)) _
  exact (Core.valuesEval_args_iff (fun e he => by
    obtain ⟨value, hvmem, rfl⟩ := List.mem_map.mp he
    exact Core.emit_isValue (by
      rw [Core.Term.stringFree] at hsf
      exact List.all_eq_true.mp hsf value hvmem))).mpr ⟨ws, hvals, rfl⟩

/-- Invert any evaluation of an emitted built-in term: the values evaluate
functionally, the operation folds, and the result is the folded word with the
state untouched. -/
theorem term_emit_eval_inv {funs : FunEnv D} {V : VEnv D} {st : EvmState} {Γ : Ctx}
    {arity : Nat} {op : PureOp arity} {targs : Args Γ arity}
    (hsf : (Term.builtin op targs).stringFree = true) {r : EResult D}
    (h : Step D funs V st (.expr (Term.builtin op targs).emit) (.eres r)) :
    ∃ ws w, valuesEval (calls := calls) (creates := creates) V
        (targs.values.map Value.emit) = some ws ∧
      pureFn op.toOp ws = some w ∧ r = .vals [w] st := by
  have hval : ∀ e ∈ targs.values.map Value.emit, isValueExpr e = true := by
    intro e he
    obtain ⟨value, hvmem, rfl⟩ := List.mem_map.mp he
    exact Core.emit_isValue (by
      rw [Core.Term.stringFree] at hsf
      exact List.all_eq_true.mp hsf value hvmem)
  cases h with
  | builtinOk hargs hb =>
      obtain ⟨ws, hws, hr⟩ := (Core.valuesEval_args_iff hval).mp hargs
      injection hr with hvals hst
      subst hst
      have hlen : ws.length = arity := by
        rw [Core.valuesEval_length hws, List.length_map, targs.length_eq]
      obtain ⟨w, hw⟩ := pureOp_pureFn op hlen
      rw [hvals] at hb
      have hres := pureFn_builtin_inv (calls := calls) (creates := creates) hw hb
      injection hres with hrets hst2
      subst hrets
      subst hst2
      exact ⟨ws, w, hws, hw, rfl⟩
  | builtinHalt hargs hb =>
      obtain ⟨ws, hws, hr⟩ := (Core.valuesEval_args_iff hval).mp hargs
      injection hr with hvals hst
      subst hst
      have hlen : ws.length = arity := by
        rw [Core.valuesEval_length hws, List.length_map, targs.length_eq]
      obtain ⟨w, hw⟩ := pureOp_pureFn op hlen
      rw [hvals] at hb
      have hres := pureFn_builtin_inv (calls := calls) (creates := creates) hw hb
      cases hres
  | builtinArgsHalt hargs =>
      obtain ⟨ws, _, hr⟩ := (Core.valuesEval_args_iff hval).mp hargs
      cases hr

/-- Invert any evaluation of a *substituted* built-in term (the caller-side
form): the substituted values evaluate functionally, the operation folds, and
the result is the folded word with the state untouched. -/
theorem term_subst_eval_inv {funs : FunEnv D} {V : VEnv D} {st : EvmState} {Γ : Ctx}
    {arity : Nat} {op : PureOp arity} {targs : Args Γ arity}
    (hsf : (Term.builtin op targs).stringFree = true)
    {args : List (Expr Op)} (hargs : ∀ e ∈ args, isValueExpr e = true)
    {r : EResult D}
    (h : Step D funs V st (.expr ((Term.builtin op targs).substEmit args)) (.eres r)) :
    ∃ ws w, valuesEval (calls := calls) (creates := creates) V
        (targs.values.map (Value.substEmit args)) = some ws ∧
      pureFn op.toOp ws = some w ∧ r = .vals [w] st := by
  have hval : ∀ e ∈ targs.values.map (Value.substEmit args), isValueExpr e = true := by
    intro e he
    obtain ⟨value, hvmem, rfl⟩ := List.mem_map.mp he
    exact Core.substEmit_isValue hargs (by
      rw [Core.Term.stringFree] at hsf
      exact List.all_eq_true.mp hsf value hvmem)
  rw [Term.substEmit] at h
  cases h with
  | builtinOk hargs' hb =>
      obtain ⟨ws, hws, hr⟩ := (Core.valuesEval_args_iff hval).mp hargs'
      injection hr with hvals hst
      subst hst
      have hlen : ws.length = arity := by
        rw [Core.valuesEval_length hws, List.length_map, targs.length_eq]
      obtain ⟨w, hw⟩ := pureOp_pureFn op hlen
      rw [hvals] at hb
      have hres := pureFn_builtin_inv (calls := calls) (creates := creates) hw hb
      injection hres with hrets hst2
      subst hrets
      subst hst2
      exact ⟨ws, w, hws, hw, rfl⟩
  | builtinHalt hargs' hb =>
      obtain ⟨ws, hws, hr⟩ := (Core.valuesEval_args_iff hval).mp hargs'
      injection hr with hvals hst
      subst hst
      have hlen : ws.length = arity := by
        rw [Core.valuesEval_length hws, List.length_map, targs.length_eq]
      obtain ⟨w, hw⟩ := pureOp_pureFn op hlen
      rw [hvals] at hb
      have hres := pureFn_builtin_inv (calls := calls) (creates := creates) hw hb
      cases hres
  | builtinArgsHalt hargs' =>
      obtain ⟨ws, _, hr⟩ := (Core.valuesEval_args_iff hval).mp hargs'
      cases hr

/-- Execute a classified built-in body: the frame evaluation of the emitted
term determines the body's unique behavior — normal completion, unchanged
state, and the folded word readable from the return variable. -/
theorem helper_body_value {cenv : FunEnv D} {params : Ctx} {ret : Ident}
    {argvals : List U256} {st : EvmState} {e : Expr Op} {w : U256}
    (heval : ∀ funs : FunEnv D, Step D funs
      ((params.zip argvals : VEnv D) ++ bindZeros D [ret]) st
      (.expr e) (.eres (.vals [w] st))) :
    ∃ Vend, Step D cenv ((params.zip argvals : VEnv D) ++ bindZeros D [ret]) st
        (.stmt (.block [.assign [ret] e]))
        (.sres Vend st .normal) ∧ VEnv.get Vend ret = some w := by
  set V0 : VEnv D := (params.zip argvals : VEnv D) ++ bindZeros D [ret] with hV0
  refine ⟨VEnv.setMany V0 [ret] [w], ?_, ?_⟩
  · have hb : Step D (hoist D [Stmt.assign [ret] e] :: cenv) V0 st
        (.stmts [.assign [ret] e])
        (.sres (VEnv.setMany V0 [ret] [w]) st .normal) :=
      Step.seqCons (Step.assignVal (heval _) (by simp)) Step.seqNil
    have := Step.block hb
    rwa [restore_setMany_same] at this
  · show VEnv.get (VEnv.setMany V0 [ret] [w]) ret = some w
    have : VEnv.setMany V0 [ret] [w] = VEnv.set V0 ret w := rfl
    rw [this]
    exact venv_get_set_of_mem w ret_mem_frame

/-- Invert the execution of a classified built-in body: it must have run the
assignment to normal completion, with the term evaluating in the frame. -/
theorem helper_body_inv {cenv : FunEnv D} {params : Ctx} {ret : Ident}
    {argvals : List U256} {st : EvmState} {Γ : Ctx}
    {arity : Nat} {op : PureOp arity} {targs : Args Γ arity}
    (hsf : (Term.builtin op targs).stringFree = true)
    {Vend st' o}
    (h : Step D cenv ((params.zip argvals : VEnv D) ++ bindZeros D [ret]) st
      (.stmt (.block [.assign [ret] (Term.builtin op targs).emit]))
      (.sres Vend st' o)) :
    o = .normal ∧ st' = st ∧ ∃ w,
      Step D (hoist D [Stmt.assign [ret] (Term.builtin op targs).emit] :: cenv)
        ((params.zip argvals : VEnv D) ++ bindZeros D [ret]) st
        (.expr (Term.builtin op targs).emit) (.eres (.vals [w] st)) ∧
      VEnv.get Vend ret = some w := by
  cases h with
  | block hb =>
      cases hb with
      | seqCons hass hnil =>
          cases hnil
          cases hass with
          | assignVal hval hlen =>
              obtain ⟨ws, w, hws, hw, hr⟩ := term_emit_eval_inv hsf hval
              injection hr with hvals hst
              subst hvals
              subst hst
              refine ⟨rfl, rfl, w, term_emit_eval hsf hws hw, ?_⟩
              rw [restore_setMany_same]
              have : VEnv.setMany ((params.zip argvals : VEnv D) ++ bindZeros D [ret])
                  [ret] [w] = VEnv.set _ ret w := rfl
              rw [this]
              exact venv_get_set_of_mem w ret_mem_frame
      | seqStop hass hne =>
          cases hass with
          | assignVal _ _ => exact absurd rfl hne
          | assignHalt hval =>
              obtain ⟨_, _, _, _, hr⟩ := term_emit_eval_inv hsf hval
              cases hr

/-- **The substitution β equivalence.** Under a lookup equation classifying
`fn` as a built-in-body helper, a call with value-shaped, arity-correct
arguments has exactly the same derivations as the substituted body — under
*any* target function environment, since the substituted expression consults
none. -/
theorem helper_call_subst_iff {litOK : Bool} {funs funs' cenv : FunEnv D} {V st fn}
    {decl : FDecl D} {h : Helper}
    (hl : lookupFun funs fn = some (decl, cenv))
    (hcl : helper? (calls := calls) (creates := creates) litOK decl = some h)
    {arity : Nat} {op : PureOp arity} {targs : Args h.params arity}
    (hterm : h.term = .builtin op targs)
    {args : List (Expr Op)}
    (hlen : args.length = h.params.length)
    (hargs : ∀ e ∈ args, isValueExpr e = true)
    {result : EResult D} :
    Step D funs V st (.expr (.call fn args)) (.eres result) ↔
      Step D funs' V st (.expr (h.term.substEmit args)) (.eres result) := by
  obtain ⟨hdecl, -⟩ := helper?_shape hcl
  have hsf : (Term.builtin op targs).stringFree = true := hterm ▸ h.stringFree
  have hval : ∀ e ∈ targs.values.map (Value.substEmit args),
      isValueExpr e = true := by
    intro e he
    obtain ⟨value, hvmem, rfl⟩ := List.mem_map.mp he
    exact Core.substEmit_isValue hargs (by
      rw [Core.Term.stringFree] at hsf
      exact List.all_eq_true.mp hsf value hvmem)
  constructor
  · intro hcall
    cases hcall with
    | callOk hargsE hlookup hlen' hbody hout =>
        rw [hl] at hlookup
        injection hlookup with heq
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
        rw [hdecl] at hbody
        obtain ⟨argvals, hargvals, hr⟩ := (Core.valuesEval_args_iff hargs).mp hargsE
        injection hr with hvals hst
        subst hvals
        subst hst
        rw [hterm] at hbody
        obtain ⟨rfl, rfl, w, hweval, hwret⟩ := helper_body_inv hsf hbody
        obtain ⟨ws, w', hws, hw', hr'⟩ := term_emit_eval_inv hsf hweval
        injection hr' with hvals'
        have hww : w = w' := by simpa using hvals'
        subst hww
        have hcorr := Core.substEmit_values_correspond
          (suffix := bindZeros D [h.ret]) hlen hargvals targs.values
        rw [hterm]
        simp only [hdecl, List.map_cons, List.map_nil, hwret, Option.getD_some,
          Term.substEmit]
        exact Step.builtinOk
          ((Core.valuesEval_args_iff hval).mpr ⟨ws, by rw [hcorr]; exact hws, rfl⟩)
          (pureFn_builtin (calls := calls) (creates := creates) hw' _)
    | callHalt hargsE hlookup hlen' hbody =>
        rw [hl] at hlookup
        injection hlookup with heq
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
        rw [hdecl] at hbody
        obtain ⟨argvals, hargvals, hr⟩ := (Core.valuesEval_args_iff hargs).mp hargsE
        injection hr with hvals hst
        subst hvals
        subst hst
        rw [hterm] at hbody
        obtain ⟨ho, -, -⟩ := helper_body_inv hsf hbody
        cases ho
    | callArgsHalt hargsE =>
        obtain ⟨_, -, hr⟩ := (Core.valuesEval_args_iff hargs).mp hargsE
        cases hr
  · intro hsub
    rw [hterm] at hsub
    obtain ⟨ws, w, hws, hw, hr⟩ := term_subst_eval_inv hsf hargs hsub
    subst hr
    -- recover the functional evaluation of *all* arguments
    have hall : ∀ e ∈ args,
        (valueEval (calls := calls) (creates := creates) V e).isSome := by
      intro e hemem
      obtain ⟨p, hp⟩ := Core.exists_zip_left hlen hemem
      have hpmem : p ∈ h.params := (List.of_mem_zip hp).1
      have hpused : p ∈ h.term.vars := h.used p hpmem
      rw [hterm] at hpused
      obtain ⟨ref, hrefname, hrefmem⟩ := Core.mem_vars_builtin hpused
      have hfind := Core.find?_zip_eq_of_nodup h.nodup (hrefname ▸ hp)
      have hsubval : Value.substEmit (params := h.params) args (.var ref) = e := by
        rw [Value.substEmit, hfind]
      have hmapped : Value.substEmit (params := h.params) args (.var ref) ∈
          targs.values.map (Value.substEmit args) :=
        List.mem_map.mpr ⟨.var ref, hrefmem, rfl⟩
      rw [hsubval] at hmapped
      exact Core.valuesEval_mem_isSome hws hmapped
    obtain ⟨argvals, hargvals⟩ :=
      Option.isSome_iff_exists.mp (Core.valuesEval_isSome_of_forall hall)
    have hcorr := Core.substEmit_values_correspond
      (suffix := bindZeros D [h.ret]) hlen hargvals targs.values
    rw [hcorr] at hws
    have hbody := helper_body_value (cenv := cenv)
      (params := h.params) (ret := h.ret) (argvals := argvals) (st := st)
      (e := (Term.builtin op targs).emit) (w := w)
      (fun funs'' => term_emit_eval hsf hws hw)
    obtain ⟨Vend, hbodyExec, hVret⟩ := hbody
    have hlenv : argvals.length = h.params.length := by
      rw [Core.valuesEval_length hargvals, hlen]
    have hcall := Step.callOk (fn := fn)
      ((Core.valuesEval_args_iff hargs).mpr ⟨argvals, hargvals, rfl⟩)
      (hdecl ▸ hl) (by simpa [hdecl] using hlenv)
      (by simpa [hdecl, hterm] using hbodyExec) (Or.inl rfl)
    simpa [hdecl, hVret] using hcall

/-! ## Argument lists that come out value-shaped went in value-shaped -/

theorem inlineHelpersArgs_value_inv {litOK : Bool} (static : FunEnv D)
    {args : List (Expr Op)}
    (hvals : ∀ e ∈ inlineHelpersArgs litOK static args, isValueExpr e = true) :
    inlineHelpersArgs litOK static args = args ∧
      ∀ e ∈ args, isValueExpr e = true := by
  induction args with
  | nil => exact ⟨rfl, by simp⟩
  | cons e rest ih =>
      rw [inlineHelpersArgs] at hvals ⊢
      obtain ⟨heq, hev⟩ := inlineHelpersExpr_value_inv static
        (hvals (inlineHelpersExpr litOK static e) (by simp))
      obtain ⟨hreq, hrev⟩ := ih (fun e' h' => hvals e' (by simp [h']))
      rw [heq, hreq]
      refine ⟨rfl, ?_⟩
      intro e' h'
      rcases List.mem_cons.mp h' with rfl | h''
      exacts [hev, hrev e' h'']

/-! ## Scope-indexed semantic simulation, forward -/

/-- A derivation transports from the original lexical scope stack to the
transformed one. `outer` is deliberately untouched: the pass never assumes
anything about functions supplied by an enclosing context. -/
theorem Step.inlineHelpers_forward {litOK : Bool} {funs : FunEnv D} {V st code result}
    (h : Step D funs V st code result) : ∀ (static outer : FunEnv D),
    funs = static ++ outer →
    Step D (inlineHelpersFuns litOK static ++ outer) V st
      (inlineHelpersCode litOK static code) result := by
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
          have htarget : lookupFun
              (inlineHelpersFuns (calls := calls) (creates := creates) litOK static
                ++ outer) fn = some (decl, cenv) := by
            simpa [lookupFun_inline_append_of_none hs] using hlookup'
          have hc := Step.callOk hargs' htarget hlen hbody hout
          rw [inlineHelpersCode, inlineHelpersExpr_call_none static fn args
            (by simp [resolveHelper, hs])]
          exact hc
      | some found =>
          rcases found with ⟨sdecl, closure⟩
          have hsource := lookupFun_append_of_some (outer := outer) hs
          rw [hsource] at hlookup
          injection hlookup with heq
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
          have htarget := lookupFun_inline_append_of_some (litOK := litOK)
            (outer := outer) hs
          have hbody' := ihbody closure outer rfl
          have hbody'' : Step D (inlineHelpersFuns litOK closure ++ outer)
              ((inlineHelpersDecl litOK closure sdecl).params.zip argvals ++
                bindZeros D (inlineHelpersDecl litOK closure sdecl).rets) st1
              (.stmt (.block (inlineHelpersDecl litOK closure sdecl).body))
              (.sres Vend st2 o) := by
            simpa [inlineHelpersCode, inlineHelpersStmt, inlineHelpersDecl,
              inlineHelpersBlock] using hbody'
          have hc := Step.callOk hargs' htarget
            (by simpa [inlineHelpersDecl] using hlen) hbody'' hout
          cases hh : helper? (calls := calls) (creates := creates) litOK sdecl with
          | none =>
              rw [inlineHelpersCode, inlineHelpersExpr_call_none static fn args
                (by simp [resolveHelper, hs, hh])]
              simpa [inlineHelpersDecl] using hc
          | some hp =>
              have hfix := inlineHelpersDecl_helper (litOK := litOK) closure hh
              rw [hfix] at htarget hc
              rw [inlineHelpersCode, inlineHelpersExpr_call_some (h := hp) static fn args
                (by simp [resolveHelper, hs, hh])]
              rcases hp.term_cases with ⟨ref, hterm⟩ | ⟨tarity, top, ttargs, hterm⟩
              · have hparams := hp.atom_params hterm
                obtain ⟨hdecl, -⟩ := helper?_shape hh
                rw [hterm] at hdecl
                simp only [Core.Term.emit, Core.Value.emit, Core.Var.emit] at hdecl
                set x := Core.Var.name ref with hx
                rw [hparams] at hdecl
                rw [rewriteCall_atom hterm]
                cases hargsShape : inlineHelpersArgs litOK static args with
                | nil => simpa [hargsShape] using hc
                | cons arg rest =>
                    cases rest with
                    | nil =>
                        have hi := (identity_call_add_iff
                          (hl := by simpa [hdecl] using htarget)).mp
                          (by simpa [hargsShape] using hc)
                        simpa using hi
                    | cons arg2 rest2 => simpa [hargsShape] using hc
              · by_cases hcond : (inlineHelpersArgs litOK static args).length =
                    hp.params.length ∧
                    (∀ e ∈ inlineHelpersArgs litOK static args, argOK litOK e)
                · obtain ⟨hfixargs, hargsval⟩ :=
                    inlineHelpersArgs_value_inv static
                      (fun e he => (hcond.2 e he).1)
                  have hlenargs : args.length = hp.params.length := by
                    rw [← hcond.1, hfixargs]
                  have hi := (helper_call_subst_iff
                    (funs' := inlineHelpersFuns (calls := calls) (creates := creates)
                      litOK static ++ outer)
                    (hl := htarget) (hcl := hh) (hterm := hterm)
                    hlenargs hargsval).mp (by rw [hfixargs] at hc; exact hc)
                  rw [rewriteCall_builtin_pos hterm hcond, hfixargs]
                  rw [hterm] at hi
                  exact hi
                · rw [rewriteCall_builtin_neg hterm hcond]
                  exact hc
  | @callHalt funs V st fn args argvals st1 decl cenv Vend st2
      hargs hlookup hlen hbody ihargs ihbody =>
      intro static outer hfun
      subst funs
      have hargs' := ihargs static outer rfl
      cases hs : lookupFun static fn with
      | none =>
          have hlookup' : lookupFun outer fn = some (decl, cenv) := by
            simpa [lookupFun_append_of_none hs] using hlookup
          have htarget : lookupFun
              (inlineHelpersFuns (calls := calls) (creates := creates) litOK static
                ++ outer) fn = some (decl, cenv) := by
            simpa [lookupFun_inline_append_of_none hs] using hlookup'
          have hc := Step.callHalt hargs' htarget hlen hbody
          rw [inlineHelpersCode, inlineHelpersExpr_call_none static fn args
            (by simp [resolveHelper, hs])]
          exact hc
      | some found =>
          rcases found with ⟨sdecl, closure⟩
          have hsource := lookupFun_append_of_some (outer := outer) hs
          rw [hsource] at hlookup
          injection hlookup with heq
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
          have htarget := lookupFun_inline_append_of_some (litOK := litOK)
            (outer := outer) hs
          have hbody' := ihbody closure outer rfl
          have hbody'' : Step D (inlineHelpersFuns litOK closure ++ outer)
              ((inlineHelpersDecl litOK closure sdecl).params.zip argvals ++
                bindZeros D (inlineHelpersDecl litOK closure sdecl).rets) st1
              (.stmt (.block (inlineHelpersDecl litOK closure sdecl).body))
              (.sres Vend st2 .halt) := by
            simpa [inlineHelpersCode, inlineHelpersStmt, inlineHelpersDecl,
              inlineHelpersBlock] using hbody'
          have hc := Step.callHalt hargs' htarget
            (by simpa [inlineHelpersDecl] using hlen) hbody''
          cases hh : helper? (calls := calls) (creates := creates) litOK sdecl with
          | none =>
              rw [inlineHelpersCode, inlineHelpersExpr_call_none static fn args
                (by simp [resolveHelper, hs, hh])]
              simpa [inlineHelpersDecl] using hc
          | some hp =>
              have hfix := inlineHelpersDecl_helper (litOK := litOK) closure hh
              rw [hfix] at htarget
              rw [inlineHelpersCode, inlineHelpersExpr_call_some (h := hp) static fn args
                (by simp [resolveHelper, hs, hh])]
              rcases hp.term_cases with ⟨ref, hterm⟩ | ⟨tarity, top, ttargs, hterm⟩
              · have hparams := hp.atom_params hterm
                obtain ⟨hdecl, -⟩ := helper?_shape hh
                rw [hterm] at hdecl
                simp only [Core.Term.emit, Core.Value.emit, Core.Var.emit] at hdecl
                set x := Core.Var.name ref with hx
                rw [hparams] at hdecl
                rw [rewriteCall_atom hterm]
                cases hargsShape : inlineHelpersArgs litOK static args with
                | nil => simpa [hargsShape] using hc
                | cons arg rest =>
                    cases rest with
                    | nil =>
                        have hi := (identity_call_add_iff
                          (hl := by simpa [hdecl] using htarget)).mp
                          (by simpa [hargsShape] using hc)
                        simpa using hi
                    | cons arg2 rest2 => simpa [hargsShape] using hc
              · by_cases hcond : (inlineHelpersArgs litOK static args).length =
                    hp.params.length ∧
                    (∀ e ∈ inlineHelpersArgs litOK static args, argOK litOK e)
                · obtain ⟨hfixargs, hargsval⟩ :=
                    inlineHelpersArgs_value_inv static
                      (fun e he => (hcond.2 e he).1)
                  have hlenargs : args.length = hp.params.length := by
                    rw [← hcond.1, hfixargs]
                  have hi := (helper_call_subst_iff
                    (funs' := inlineHelpersFuns (calls := calls) (creates := creates)
                      litOK static ++ outer)
                    (hl := htarget) (hcl := hh) (hterm := hterm)
                    hlenargs hargsval).mp (by rw [hfixargs] at hc; exact hc)
                  rw [rewriteCall_builtin_pos hterm hcond, hfixargs]
                  rw [hterm] at hi
                  exact hi
                · rw [rewriteCall_builtin_neg hterm hcond]
                  exact hc
  | @callArgsHalt funs V st fn args st1 hargs ihargs =>
      intro static outer hfun
      subst funs
      have hargs' := ihargs static outer rfl
      have hc : Step D (inlineHelpersFuns litOK static ++ outer) V st
          (.expr (.call fn (inlineHelpersArgs litOK static args)))
          (.eres (.halt st1)) :=
        Step.callArgsHalt hargs'
      cases hs : lookupFun static fn with
      | none =>
          rw [inlineHelpersCode, inlineHelpersExpr_call_none static fn args
            (by simp [resolveHelper, hs])]
          exact hc
      | some found =>
          rcases found with ⟨sdecl, closure⟩
          cases hh : helper? (calls := calls) (creates := creates) litOK sdecl with
          | none =>
              rw [inlineHelpersCode, inlineHelpersExpr_call_none static fn args
                (by simp [resolveHelper, hs, hh])]
              exact hc
          | some hp =>
              have htarget := lookupFun_inline_append_of_some (litOK := litOK)
                (outer := outer) hs
              have hfix := inlineHelpersDecl_helper (litOK := litOK) closure hh
              rw [hfix] at htarget
              rw [inlineHelpersCode, inlineHelpersExpr_call_some (h := hp) static fn args
                (by simp [resolveHelper, hs, hh])]
              rcases hp.term_cases with ⟨ref, hterm⟩ | ⟨tarity, top, ttargs, hterm⟩
              · have hparams := hp.atom_params hterm
                obtain ⟨hdecl, -⟩ := helper?_shape hh
                rw [hterm] at hdecl
                simp only [Core.Term.emit, Core.Value.emit, Core.Var.emit] at hdecl
                set x := Core.Var.name ref with hx
                rw [hparams] at hdecl
                rw [rewriteCall_atom hterm]
                cases hargsShape : inlineHelpersArgs litOK static args with
                | nil => simpa [hargsShape] using hc
                | cons arg rest =>
                    cases rest with
                    | nil =>
                        have hi := (identity_call_add_iff
                          (hl := by simpa [hdecl] using htarget)).mp
                          (by simpa [hargsShape] using hc)
                        simpa using hi
                    | cons arg2 rest2 => simpa [hargsShape] using hc
              · by_cases hcond : (inlineHelpersArgs litOK static args).length =
                    hp.params.length ∧
                    (∀ e ∈ inlineHelpersArgs litOK static args, argOK litOK e)
                · obtain ⟨hfixargs, hargsval⟩ :=
                    inlineHelpersArgs_value_inv static
                      (fun e he => (hcond.2 e he).1)
                  have hlenargs : args.length = hp.params.length := by
                    rw [← hcond.1, hfixargs]
                  have hi := (helper_call_subst_iff
                    (funs' := inlineHelpersFuns (calls := calls) (creates := creates)
                      litOK static ++ outer)
                    (hl := htarget) (hcl := hh) (hterm := hterm)
                    hlenargs hargsval).mp (by rw [hfixargs] at hc; exact hc)
                  rw [rewriteCall_builtin_pos hterm hcond, hfixargs]
                  rw [hterm] at hi
                  exact hi
                · rw [rewriteCall_builtin_neg hterm hcond]
                  exact hc
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
      rw [inlineHelpersCode, inlineHelpersStmt.eq_def]
      exact Step.funDef
  | @block funs V st body Vb stb o hbody ihbody =>
      intro static outer hfun
      subst funs
      have hb := ihbody (hoist D body :: static) outer rfl
      rw [inlineHelpersCode] at hb
      have hb' : Step D
          (hoist D (inlineHelpersBlock litOK static body) ::
            (inlineHelpersFuns litOK static ++ outer)) V st
          (.stmts (inlineHelpersBlock litOK static body)) (.sres Vb stb o) := by
        simpa [inlineHelpersBlock, inlineHelpersFuns,
          hoist_inlineHelpersStmts] using hb
      rw [inlineHelpersCode, inlineHelpersStmt.eq_def]
      exact Step.block hb'
  | letZero =>
      intro static outer rfl
      rw [inlineHelpersCode, inlineHelpersStmt]
      exact Step.letZero
  | letVal _ hlen ihe =>
      intro static outer rfl
      simpa [inlineHelpersCode, inlineHelpersStmt] using
        Step.letVal (ihe static outer rfl) hlen
  | letHalt _ ihe =>
      intro static outer rfl
      simpa [inlineHelpersCode, inlineHelpersStmt] using
        Step.letHalt (ihe static outer rfl)
  | assignVal _ hlen ihe =>
      intro static outer rfl
      simpa [inlineHelpersCode, inlineHelpersStmt] using
        Step.assignVal (ihe static outer rfl) hlen
  | assignHalt _ ihe =>
      intro static outer rfl
      simpa [inlineHelpersCode, inlineHelpersStmt] using
        Step.assignHalt (ihe static outer rfl)
  | exprStmt _ ihe =>
      intro static outer rfl
      simpa [inlineHelpersCode, inlineHelpersStmt] using
        Step.exprStmt (ihe static outer rfl)
  | exprStmtHalt _ ihe =>
      intro static outer rfl
      simpa [inlineHelpersCode, inlineHelpersStmt] using
        Step.exprStmtHalt (ihe static outer rfl)
  | ifTrue _ hnz _ ihc ihb =>
      intro static outer rfl
      have hc' := ihc static outer rfl
      have hb' := ihb static outer rfl
      rw [inlineHelpersCode] at hc'
      rw [inlineHelpersCode, inlineHelpersStmt] at hb'
      rw [inlineHelpersCode, inlineHelpersStmt]
      exact Step.ifTrue hc' hnz hb'
  | @ifFalse funs V st c body cv st1 hc hz ihc =>
      intro static outer rfl
      have hc' := ihc static outer rfl
      rw [inlineHelpersCode] at hc'
      rw [inlineHelpersCode, inlineHelpersStmt]
      exact Step.ifFalse (body := inlineHelpersBlock litOK static body) hc' hz
  | @ifHalt funs V st c body st1 hc ihc =>
      intro static outer rfl
      have hc' := ihc static outer rfl
      rw [inlineHelpersCode] at hc'
      rw [inlineHelpersCode, inlineHelpersStmt]
      exact Step.ifHalt (body := inlineHelpersBlock litOK static body) hc'
  | @switchExec funs V st c cases dflt cv st1 V' st2 o hc hb ihc ihb =>
      intro static outer hfun
      subst funs
      have hc' := ihc static outer rfl
      have hb' := ihb static outer rfl
      rw [inlineHelpersCode] at hc'
      rw [inlineHelpersCode, inlineHelpersStmt] at hb'
      rw [selectSwitch_open_eq] at hb'
      have hb'' : Step D (inlineHelpersFuns litOK static ++ outer) V st1
          (.stmt (.block (selectSwitch evm cv (inlineHelpersCases litOK static cases)
            (dflt.map (inlineHelpersBlock litOK static))))) (.sres V' st2 o) := by
        rw [selectSwitch_inlineHelpers]
        exact hb'
      rw [inlineHelpersCode, inlineHelpersStmt_switch]
      exact Step.switchExec hc' (by simpa only [selectSwitch_open_eq] using hb'')
  | @switchHalt funs V st c cases dflt st1 hc ihc =>
      intro static outer rfl
      have hc' := ihc static outer rfl
      rw [inlineHelpersCode] at hc'
      cases dflt <;> rw [inlineHelpersCode, inlineHelpersStmt.eq_def]
      · exact Step.switchHalt hc'
      · exact Step.switchHalt hc'
  | @forLoop funs V st init c post body Vinit stinit Vend stend o
      hinit hloop ihinit ihloop =>
      intro static outer hfun
      subst funs
      have hi := ihinit (hoist D init :: static) outer rfl
      have hl := ihloop (hoist D init :: static) outer rfl
      rw [inlineHelpersCode.eq_def] at hi hl
      have hi' : Step D
          (hoist D (inlineHelpersStmts litOK (hoist D init :: static) init) ::
            (inlineHelpersFuns litOK static ++ outer)) V st
          (.stmts (inlineHelpersStmts litOK (hoist D init :: static) init))
          (.sres Vinit stinit .normal) := by
        simpa [inlineHelpersFuns, hoist_inlineHelpersStmts] using hi
      have hl' : Step D
          (hoist D (inlineHelpersStmts litOK (hoist D init :: static) init) ::
            (inlineHelpersFuns litOK static ++ outer)) Vinit stinit
          (.loop (inlineHelpersExpr litOK (hoist D init :: static) c)
            (inlineHelpersStmts litOK (hoist D post :: hoist D init :: static) post)
            (inlineHelpersStmts litOK (hoist D body :: hoist D init :: static) body))
          (.sres Vend stend o) := by
        simpa [inlineHelpersFuns, hoist_inlineHelpersStmts] using hl
      rw [inlineHelpersCode, inlineHelpersStmt.eq_def]
      exact Step.forLoop hi' hl'
  | @forInitHalt funs V st init c post body Vinit stinit hinit ihinit =>
      intro static outer hfun
      subst funs
      have hi := ihinit (hoist D init :: static) outer rfl
      rw [inlineHelpersCode.eq_def] at hi
      have hi' : Step D
          (hoist D (inlineHelpersStmts litOK (hoist D init :: static) init) ::
            (inlineHelpersFuns litOK static ++ outer)) V st
          (.stmts (inlineHelpersStmts litOK (hoist D init :: static) init))
          (.sres Vinit stinit .halt) := by
        simpa [inlineHelpersFuns, hoist_inlineHelpersStmts] using hi
      rw [inlineHelpersCode, inlineHelpersStmt.eq_def]
      exact Step.forInitHalt hi'
  | «break» =>
      intro static outer rfl
      rw [inlineHelpersCode, inlineHelpersStmt.eq_def]
      exact Step.«break»
  | «continue» =>
      intro static outer rfl
      rw [inlineHelpersCode, inlineHelpersStmt.eq_def]
      exact Step.«continue»
  | leave =>
      intro static outer rfl
      rw [inlineHelpersCode, inlineHelpersStmt.eq_def]
      exact Step.leave
  | seqNil =>
      intro static outer rfl
      rw [inlineHelpersCode, inlineHelpersStmts]
      exact Step.seqNil
  | seqCons _ _ ihs ihrest =>
      intro static outer rfl
      simpa [inlineHelpersCode, inlineHelpersStmts] using
        Step.seqCons (ihs static outer rfl) (ihrest static outer rfl)
  | @seqStop funs V st s rest V1 st1 o hs hne ihs =>
      intro static outer rfl
      simpa [inlineHelpersCode, inlineHelpersStmts] using
        (Step.seqStop (rest := inlineHelpersStmts litOK static rest)
          (ihs static outer rfl) hne)
  | loopDone _ hz ihc =>
      intro static outer rfl
      have hc' := ihc static outer rfl
      rw [inlineHelpersCode] at hc'
      rw [inlineHelpersCode]
      exact Step.loopDone hc' hz
  | loopCondHalt _ ihc =>
      intro static outer rfl
      have hc' := ihc static outer rfl
      rw [inlineHelpersCode] at hc'
      rw [inlineHelpersCode]
      exact Step.loopCondHalt hc'
  | loopStep _ hnz _ hob _ _ ihc ihb ihp ihr =>
      intro static outer rfl
      have hc' := ihc static outer rfl
      have hb' := ihb static outer rfl
      have hp' := ihp static outer rfl
      have hr' := ihr static outer rfl
      rw [inlineHelpersCode] at hc'
      rw [inlineHelpersCode.eq_def] at hr'
      rw [inlineHelpersCode, inlineHelpersStmt] at hb' hp'
      rw [inlineHelpersCode]
      exact Step.loopStep hc' hnz hb' hob hp' hr'
  | loopPostHalt _ hnz _ hob _ ihc ihb ihp =>
      intro static outer rfl
      have hc' := ihc static outer rfl
      have hb' := ihb static outer rfl
      have hp' := ihp static outer rfl
      rw [inlineHelpersCode] at hc'
      rw [inlineHelpersCode, inlineHelpersStmt] at hb' hp'
      rw [inlineHelpersCode]
      exact Step.loopPostHalt hc' hnz hb' hob hp'
  | loopBreak _ hnz _ ihc ihb =>
      intro static outer rfl
      have hc' := ihc static outer rfl
      have hb' := ihb static outer rfl
      rw [inlineHelpersCode] at hc'
      rw [inlineHelpersCode, inlineHelpersStmt] at hb'
      rw [inlineHelpersCode]
      exact Step.loopBreak hc' hnz hb'
  | loopLeave _ hnz _ ihc ihb =>
      intro static outer rfl
      have hc' := ihc static outer rfl
      have hb' := ihb static outer rfl
      rw [inlineHelpersCode] at hc'
      rw [inlineHelpersCode, inlineHelpersStmt] at hb'
      rw [inlineHelpersCode]
      exact Step.loopLeave hc' hnz hb'
  | loopBodyHalt _ hnz _ ihc ihb =>
      intro static outer rfl
      have hc' := ihc static outer rfl
      have hb' := ihb static outer rfl
      rw [inlineHelpersCode] at hc'
      rw [inlineHelpersCode, inlineHelpersStmt] at hb'
      rw [inlineHelpersCode]
      exact Step.loopBodyHalt hc' hnz hb'

/-! ## Inversion of the transform's output shapes -/

/-- The rewrite produces a built-in application or a call (never a variable,
literal, or user-call under a different name). -/
theorem rewriteCall_shape {litOK : Bool} (h : Helper) (fn : Ident) (args : List (Expr Op)) :
    (∃ (op : Op) (bargs : List (Expr Op)),
      rewriteCall litOK h fn args = .builtin op bargs) ∨
    rewriteCall litOK h fn args = .call fn args := by
  rw [rewriteCall.eq_def]
  split
  · split
    · exact Or.inl ⟨_, _, rfl⟩
    · exact Or.inr rfl
  · split
    · exact Or.inl ⟨_, _, rfl⟩
    · exact Or.inr rfl

theorem resolveHelper_some {litOK : Bool} {static : FunEnv D} {fn : Ident} {h : Helper}
    (hres : resolveHelper (calls := calls) (creates := creates) litOK static fn = some h) :
    ∃ decl closure, lookupFun static fn = some (decl, closure) ∧
      helper? (calls := calls) (creates := creates) litOK decl = some h := by
  unfold resolveHelper at hres
  split at hres
  next decl closure heq => exact ⟨decl, closure, heq, hres⟩
  next => cases hres

theorem inlineHelpersArgs_eq_nil {litOK : Bool} {static : FunEnv D} {args : List (Expr Op)}
    (h : inlineHelpersArgs litOK static args = []) : args = [] := by
  cases args <;> simp [inlineHelpersArgs] at h ⊢

theorem inlineHelpersArgs_eq_cons {litOK : Bool} {static : FunEnv D}
    {args : List (Expr Op)} {e rest}
    (h : inlineHelpersArgs litOK static args = e :: rest) :
    ∃ e0 rest0, args = e0 :: rest0 ∧
      inlineHelpersExpr litOK static e0 = e ∧
      inlineHelpersArgs litOK static rest0 = rest := by
  cases args with
  | nil => simp [inlineHelpersArgs] at h
  | cons e0 rest0 =>
      simp only [inlineHelpersArgs, List.cons.injEq] at h
      exact ⟨e0, rest0, rfl, h.1, h.2⟩

theorem inlineHelpersExpr_eq_lit {litOK : Bool} {static : FunEnv D} {e : Expr Op} {l}
    (h : inlineHelpersExpr litOK static e = .lit l) : e = .lit l := by
  cases e with
  | lit l0 => simpa [inlineHelpersExpr] using h
  | var x => simp [inlineHelpersExpr] at h
  | builtin op args => simp [inlineHelpersExpr] at h
  | call fn args =>
      rw [inlineHelpersExpr] at h
      split at h
      next hp heq =>
        rcases rewriteCall_shape hp fn (inlineHelpersArgs litOK static args) with
          ⟨op, bargs, hb⟩ | hcall
        · rw [hb] at h; cases h
        · rw [hcall] at h; cases h
      next => cases h

theorem inlineHelpersExpr_eq_var {litOK : Bool} {static : FunEnv D} {e : Expr Op} {x}
    (h : inlineHelpersExpr litOK static e = .var x) : e = .var x := by
  cases e with
  | lit l0 => simp [inlineHelpersExpr] at h
  | var x0 => simpa [inlineHelpersExpr] using h
  | builtin op args => simp [inlineHelpersExpr] at h
  | call fn args =>
      rw [inlineHelpersExpr] at h
      split at h
      next hp heq =>
        rcases rewriteCall_shape hp fn (inlineHelpersArgs litOK static args) with
          ⟨op, bargs, hb⟩ | hcall
        · rw [hb] at h; cases h
        · rw [hcall] at h; cases h
      next => cases h

/-- An output built-in is a transformed built-in or a rewritten helper call. -/
theorem inlineHelpersExpr_eq_builtin {litOK : Bool} {static : FunEnv D} {e : Expr Op}
    {op argsT}
    (h : inlineHelpersExpr litOK static e = .builtin op argsT) :
    (∃ args, e = .builtin op args ∧ argsT = inlineHelpersArgs litOK static args) ∨
    (∃ fn args hp, e = .call fn args ∧
      resolveHelper (calls := calls) (creates := creates) litOK static fn = some hp ∧
      rewriteCall litOK hp fn (inlineHelpersArgs litOK static args) = .builtin op argsT) := by
  cases e with
  | lit l0 => simp [inlineHelpersExpr] at h
  | var x0 => simp [inlineHelpersExpr] at h
  | builtin op0 args0 =>
      simp only [inlineHelpersExpr, Expr.builtin.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨args0, rfl, rfl⟩
  | call fn args =>
      rw [inlineHelpersExpr] at h
      split at h
      next hp heq => exact Or.inr ⟨fn, args, hp, rfl, heq, h⟩
      next => cases h

/-- An output call is a transformed call to the same function. -/
theorem inlineHelpersExpr_eq_call {litOK : Bool} {static : FunEnv D} {e : Expr Op}
    {fn argsT}
    (h : inlineHelpersExpr litOK static e = .call fn argsT) :
    ∃ args, e = .call fn args ∧ argsT = inlineHelpersArgs litOK static args := by
  cases e with
  | lit l0 => simp [inlineHelpersExpr] at h
  | var x0 => simp [inlineHelpersExpr] at h
  | builtin op0 args0 => simp [inlineHelpersExpr] at h
  | call fn0 args0 =>
      rw [inlineHelpersExpr] at h
      split at h
      next hp heq =>
        rcases rewriteCall_shape hp fn0 (inlineHelpersArgs litOK static args0) with
          ⟨op, bargs, hb⟩ | hcall
        · rw [hb] at h; cases h
        · rw [hcall] at h
          injection h with hfn hargs
          subst hfn
          exact ⟨args0, rfl, hargs.symm⟩
      next =>
        injection h with hfn hargs
        subst hfn
        exact ⟨args0, rfl, hargs.symm⟩

theorem inlineHelpersStmts_eq_nil {litOK : Bool} {static : FunEnv D} {ss : Block Op}
    (h : inlineHelpersStmts litOK static ss = []) : ss = [] := by
  cases ss <;> simp [inlineHelpersStmts] at h ⊢

theorem inlineHelpersStmts_eq_cons {litOK : Bool} {static : FunEnv D} {ss : Block Op}
    {s rest}
    (h : inlineHelpersStmts litOK static ss = s :: rest) :
    ∃ s0 rest0, ss = s0 :: rest0 ∧ inlineHelpersStmt litOK static s0 = s ∧
      inlineHelpersStmts litOK static rest0 = rest := by
  cases ss with
  | nil => simp [inlineHelpersStmts] at h
  | cons s0 rest0 =>
      simp only [inlineHelpersStmts, List.cons.injEq] at h
      exact ⟨s0, rest0, rfl, h.1, h.2⟩

/-! ## Scope-indexed semantic simulation, reverse -/

theorem Step.inlineHelpers_reverse {litOK : Bool} {funsT : FunEnv D} {V st codeT result}
    (h : Step D funsT V st codeT result) : ∀ (static outer : FunEnv D) (code : Code Op),
    funsT = inlineHelpersFuns litOK static ++ outer →
    codeT = inlineHelpersCode litOK static code →
    Step D (static ++ outer) V st code result := by
  induction h <;> intro static outer code hf hc
  case lit funs V st l =>
    cases code with
    | expr e =>
        have he := inlineHelpersExpr_eq_lit (static := static)
          (by simpa [inlineHelpersCode] using hc.symm)
        subst e
        exact Step.lit
    | args => simp [inlineHelpersCode] at hc
    | stmt => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case var funs V st x v hv =>
    cases code with
    | expr e =>
        have he := inlineHelpersExpr_eq_var (static := static)
          (by simpa [inlineHelpersCode] using hc.symm)
        subst e
        exact Step.var hv
    | args => simp [inlineHelpersCode] at hc
    | stmt => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case builtinOk funs V st op args argvals st1 rets st2 hargs hb ihargs =>
    cases code with
    | expr e =>
        rcases inlineHelpersExpr_eq_builtin (static := static)
            (by simpa [inlineHelpersCode] using hc.symm) with
          ⟨args0, rfl, hargsEq⟩ | ⟨fn, args0, hp, rfl, hres, hrw⟩
        · exact Step.builtinOk
            (ihargs static outer (.args args0) hf
              (by simpa [inlineHelpersCode] using congrArg Code.args hargsEq)) hb
        · obtain ⟨decl, closure, hlk, hcl⟩ := resolveHelper_some hres
          have hlsrc := lookupFun_append_of_some (outer := outer) hlk
          rcases hp.term_cases with ⟨ref, hterm⟩ | ⟨tarity, top, ttargs, hterm⟩
          · rw [rewriteCall_atom hterm] at hrw
            cases hargsShape : inlineHelpersArgs litOK static args0 with
            | nil => rw [hargsShape] at hrw; cases hrw
            | cons arg rest =>
                cases rest with
                | cons arg2 rest2 => rw [hargsShape] at hrw; cases hrw
                | nil =>
                    rw [hargsShape] at hrw
                    injection hrw with hop hargsT
                    subst hop
                    obtain ⟨a0, rest0, rfl, ha0, hrest0⟩ :=
                      inlineHelpersArgs_eq_cons hargsShape
                    have hrest0nil : rest0 = [] := inlineHelpersArgs_eq_nil hrest0
                    subst hrest0nil
                    have hargsC : Code.args args =
                        inlineHelpersCode litOK static
                          (.args [a0, .lit (.number 0)]) := by
                      simp [inlineHelpersCode, inlineHelpersArgs,
                        inlineHelpersExpr, ha0, ← hargsT]
                    have ha0' := ihargs static outer
                      (.args [a0, .lit (.number 0)]) hf hargsC
                    have hadd : Step D (static ++ outer) V st
                        (.expr (.builtin .add [a0, .lit (.number 0)]))
                        (.eres (.vals rets st2)) := Step.builtinOk ha0' hb
                    have hparams := hp.atom_params hterm
                    obtain ⟨hdecl, -⟩ := helper?_shape hcl
                    rw [hterm] at hdecl
                    simp only [Core.Term.emit, Core.Value.emit, Core.Var.emit] at hdecl
                    set x := Core.Var.name ref with hx
                    rw [hparams] at hdecl
                    rw [hdecl] at hlsrc
                    exact (identity_call_add_iff (hl := hlsrc)).mpr hadd
          · by_cases hcond : (inlineHelpersArgs litOK static args0).length =
                hp.params.length ∧
                (∀ e' ∈ inlineHelpersArgs litOK static args0, argOK litOK e')
            · obtain ⟨hfixargs, hargsval⟩ :=
                inlineHelpersArgs_value_inv static
                  (fun e' he' => (hcond.2 e' he').1)
              rw [rewriteCall_builtin_pos hterm hcond, hfixargs] at hrw
              have hlenargs : args0.length = hp.params.length := by
                rw [← hcond.1, hfixargs]
              have htgt : Step D funs V st
                  (.expr (hp.term.substEmit args0)) (.eres (.vals rets st2)) := by
                rw [hterm, hrw]
                exact Step.builtinOk hargs hb
              exact (helper_call_subst_iff (funs := static ++ outer) (funs' := funs)
                (hl := hlsrc) (hcl := hcl) (hterm := hterm)
                hlenargs hargsval).mpr htgt
            · rw [rewriteCall_builtin_neg hterm hcond] at hrw
              cases hrw
    | args => simp [inlineHelpersCode] at hc
    | stmt => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case builtinHalt funs V st op args argvals st1 st2 hargs hb ihargs =>
    cases code with
    | expr e =>
        rcases inlineHelpersExpr_eq_builtin (static := static)
            (by simpa [inlineHelpersCode] using hc.symm) with
          ⟨args0, rfl, hargsEq⟩ | ⟨fn, args0, hp, rfl, hres, hrw⟩
        · exact Step.builtinHalt
            (ihargs static outer (.args args0) hf
              (by simpa [inlineHelpersCode] using congrArg Code.args hargsEq)) hb
        · obtain ⟨decl, closure, hlk, hcl⟩ := resolveHelper_some hres
          have hlsrc := lookupFun_append_of_some (outer := outer) hlk
          rcases hp.term_cases with ⟨ref, hterm⟩ | ⟨tarity, top, ttargs, hterm⟩
          · rw [rewriteCall_atom hterm] at hrw
            cases hargsShape : inlineHelpersArgs litOK static args0 with
            | nil => rw [hargsShape] at hrw; cases hrw
            | cons arg rest =>
                cases rest with
                | cons arg2 rest2 => rw [hargsShape] at hrw; cases hrw
                | nil =>
                    rw [hargsShape] at hrw
                    injection hrw with hop hargsT
                    subst hop
                    obtain ⟨a0, rest0, rfl, ha0, hrest0⟩ :=
                      inlineHelpersArgs_eq_cons hargsShape
                    have hrest0nil : rest0 = [] := inlineHelpersArgs_eq_nil hrest0
                    subst hrest0nil
                    have hargsC : Code.args args =
                        inlineHelpersCode litOK static
                          (.args [a0, .lit (.number 0)]) := by
                      simp [inlineHelpersCode, inlineHelpersArgs,
                        inlineHelpersExpr, ha0, ← hargsT]
                    have ha0' := ihargs static outer
                      (.args [a0, .lit (.number 0)]) hf hargsC
                    have hadd : Step D (static ++ outer) V st
                        (.expr (.builtin .add [a0, .lit (.number 0)]))
                        (.eres (.halt st2)) := Step.builtinHalt ha0' hb
                    have hparams := hp.atom_params hterm
                    obtain ⟨hdecl, -⟩ := helper?_shape hcl
                    rw [hterm] at hdecl
                    simp only [Core.Term.emit, Core.Value.emit, Core.Var.emit] at hdecl
                    set x := Core.Var.name ref with hx
                    rw [hparams] at hdecl
                    rw [hdecl] at hlsrc
                    exact (identity_call_add_iff (hl := hlsrc)).mpr hadd
          · by_cases hcond : (inlineHelpersArgs litOK static args0).length =
                hp.params.length ∧
                (∀ e' ∈ inlineHelpersArgs litOK static args0, argOK litOK e')
            · obtain ⟨hfixargs, hargsval⟩ :=
                inlineHelpersArgs_value_inv static
                  (fun e' he' => (hcond.2 e' he').1)
              rw [rewriteCall_builtin_pos hterm hcond, hfixargs] at hrw
              have hlenargs : args0.length = hp.params.length := by
                rw [← hcond.1, hfixargs]
              have htgt : Step D funs V st
                  (.expr (hp.term.substEmit args0)) (.eres (.halt st2)) := by
                rw [hterm, hrw]
                exact Step.builtinHalt hargs hb
              exact (helper_call_subst_iff (funs := static ++ outer) (funs' := funs)
                (hl := hlsrc) (hcl := hcl) (hterm := hterm)
                hlenargs hargsval).mpr htgt
            · rw [rewriteCall_builtin_neg hterm hcond] at hrw
              cases hrw
    | args => simp [inlineHelpersCode] at hc
    | stmt => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case builtinArgsHalt funs V st op args st1 hargs ihargs =>
    cases code with
    | expr e =>
        rcases inlineHelpersExpr_eq_builtin (static := static)
            (by simpa [inlineHelpersCode] using hc.symm) with
          ⟨args0, rfl, hargsEq⟩ | ⟨fn, args0, hp, rfl, hres, hrw⟩
        · exact Step.builtinArgsHalt
            (ihargs static outer (.args args0) hf
              (by simpa [inlineHelpersCode] using congrArg Code.args hargsEq))
        · obtain ⟨decl, closure, hlk, hcl⟩ := resolveHelper_some hres
          have hlsrc := lookupFun_append_of_some (outer := outer) hlk
          rcases hp.term_cases with ⟨ref, hterm⟩ | ⟨tarity, top, ttargs, hterm⟩
          · rw [rewriteCall_atom hterm] at hrw
            cases hargsShape : inlineHelpersArgs litOK static args0 with
            | nil => rw [hargsShape] at hrw; cases hrw
            | cons arg rest =>
                cases rest with
                | cons arg2 rest2 => rw [hargsShape] at hrw; cases hrw
                | nil =>
                    rw [hargsShape] at hrw
                    injection hrw with hop hargsT
                    subst hop
                    obtain ⟨a0, rest0, rfl, ha0, hrest0⟩ :=
                      inlineHelpersArgs_eq_cons hargsShape
                    have hrest0nil : rest0 = [] := inlineHelpersArgs_eq_nil hrest0
                    subst hrest0nil
                    have hargsC : Code.args args =
                        inlineHelpersCode litOK static
                          (.args [a0, .lit (.number 0)]) := by
                      simp [inlineHelpersCode, inlineHelpersArgs,
                        inlineHelpersExpr, ha0, ← hargsT]
                    have ha0' := ihargs static outer
                      (.args [a0, .lit (.number 0)]) hf hargsC
                    have hadd : Step D (static ++ outer) V st
                        (.expr (.builtin .add [a0, .lit (.number 0)]))
                        (.eres (.halt st1)) := Step.builtinArgsHalt ha0'
                    have hparams := hp.atom_params hterm
                    obtain ⟨hdecl, -⟩ := helper?_shape hcl
                    rw [hterm] at hdecl
                    simp only [Core.Term.emit, Core.Value.emit, Core.Var.emit] at hdecl
                    set x := Core.Var.name ref with hx
                    rw [hparams] at hdecl
                    rw [hdecl] at hlsrc
                    exact (identity_call_add_iff (hl := hlsrc)).mpr hadd
          · by_cases hcond : (inlineHelpersArgs litOK static args0).length =
                hp.params.length ∧
                (∀ e' ∈ inlineHelpersArgs litOK static args0, argOK litOK e')
            · obtain ⟨hfixargs, hargsval⟩ :=
                inlineHelpersArgs_value_inv static
                  (fun e' he' => (hcond.2 e' he').1)
              rw [rewriteCall_builtin_pos hterm hcond, hfixargs] at hrw
              have hlenargs : args0.length = hp.params.length := by
                rw [← hcond.1, hfixargs]
              have htgt : Step D funs V st
                  (.expr (hp.term.substEmit args0)) (.eres (.halt st1)) := by
                rw [hterm, hrw]
                exact Step.builtinArgsHalt hargs
              exact (helper_call_subst_iff (funs := static ++ outer) (funs' := funs)
                (hl := hlsrc) (hcl := hcl) (hterm := hterm)
                hlenargs hargsval).mpr htgt
            · rw [rewriteCall_builtin_neg hterm hcond] at hrw
              cases hrw
    | args => simp [inlineHelpersCode] at hc
    | stmt => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case callOk funs V st fn args argvals st1 decl cenv Vend st2 o
      hargs hlookup hlen hbody hout ihargs ihbody =>
    cases code with
    | expr e =>
        obtain ⟨args0, rfl, hargsEq⟩ := inlineHelpersExpr_eq_call
          (static := static) (by simpa [inlineHelpersCode] using hc.symm)
        have hargs0 := ihargs static outer (.args args0) hf
          (by simpa [inlineHelpersCode] using congrArg Code.args hargsEq)
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
            have ht := lookupFun_inline_append_of_some (litOK := litOK)
              (outer := outer) hs
            rw [ht] at hlookup
            injection hlookup with heq
            obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
            have hb0 := ihbody closure outer
              (.stmt (.block sdecl.body)) rfl
              (by simp [inlineHelpersCode, inlineHelpersStmt, inlineHelpersDecl,
                inlineHelpersBlock])
            have hcall0 : Step D (static ++ outer) V st
                (.expr (.call fn args0))
                (.eres (.vals
                  (sdecl.rets.map (fun r => (VEnv.get Vend r).getD
                    (evmWithExternal calls creates).zero)) st2)) :=
              Step.callOk hargs0
                (lookupFun_append_of_some (outer := outer) hs)
                (by simpa [inlineHelpersDecl] using hlen) hb0 hout
            simpa [inlineHelpersDecl] using hcall0
    | args => simp [inlineHelpersCode] at hc
    | stmt => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case callHalt funs V st fn args argvals st1 decl cenv Vend st2
      hargs hlookup hlen hbody ihargs ihbody =>
    cases code with
    | expr e =>
        obtain ⟨args0, rfl, hargsEq⟩ := inlineHelpersExpr_eq_call
          (static := static) (by simpa [inlineHelpersCode] using hc.symm)
        have hargs0 := ihargs static outer (.args args0) hf
          (by simpa [inlineHelpersCode] using congrArg Code.args hargsEq)
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
            have ht := lookupFun_inline_append_of_some (litOK := litOK)
              (outer := outer) hs
            rw [ht] at hlookup
            injection hlookup with heq
            obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
            have hb0 := ihbody closure outer
              (.stmt (.block sdecl.body)) rfl
              (by simp [inlineHelpersCode, inlineHelpersStmt, inlineHelpersDecl,
                inlineHelpersBlock])
            exact Step.callHalt hargs0
              (lookupFun_append_of_some (outer := outer) hs)
              (by simpa [inlineHelpersDecl] using hlen) hb0
    | args => simp [inlineHelpersCode] at hc
    | stmt => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case callArgsHalt funs V st fn args st1 hargs ihargs =>
    cases code with
    | expr e =>
        obtain ⟨args0, rfl, hargsEq⟩ := inlineHelpersExpr_eq_call
          (static := static) (by simpa [inlineHelpersCode] using hc.symm)
        exact Step.callArgsHalt
          (ihargs static outer (.args args0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.args hargsEq))
    | args => simp [inlineHelpersCode] at hc
    | stmt => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case argsNil funs V st =>
    cases code with
    | args args0 =>
        have ha : inlineHelpersArgs litOK static args0 = [] := by
          simpa [inlineHelpersCode] using hc.symm
        have : args0 = [] := inlineHelpersArgs_eq_nil ha
        subst args0
        exact Step.argsNil
    | expr => simp [inlineHelpersCode] at hc
    | stmt => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case argsCons funs V st e rest restvals st1 v st2 hrest he ihrest ihe =>
    cases code with
    | args args0 =>
        have ha : inlineHelpersArgs litOK static args0 = e :: rest := by
          simpa [inlineHelpersCode] using hc.symm
        obtain ⟨e0, rest0, rfl, heq, hreq⟩ := inlineHelpersArgs_eq_cons ha
        exact Step.argsCons
          (ihrest static outer (.args rest0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.args hreq.symm))
          (ihe static outer (.expr e0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.expr heq.symm))
    | expr => simp [inlineHelpersCode] at hc
    | stmt => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case argsRestHalt funs V st e rest st1 hrest ihrest =>
    cases code with
    | args args0 =>
        have ha : inlineHelpersArgs litOK static args0 = e :: rest := by
          simpa [inlineHelpersCode] using hc.symm
        obtain ⟨e0, rest0, rfl, heq, hreq⟩ := inlineHelpersArgs_eq_cons ha
        exact Step.argsRestHalt
          (ihrest static outer (.args rest0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.args hreq.symm))
    | expr => simp [inlineHelpersCode] at hc
    | stmt => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case argsHeadHalt funs V st e rest restvals st1 st2 hrest he ihrest ihe =>
    cases code with
    | args args0 =>
        have ha : inlineHelpersArgs litOK static args0 = e :: rest := by
          simpa [inlineHelpersCode] using hc.symm
        obtain ⟨e0, rest0, rfl, heq, hreq⟩ := inlineHelpersArgs_eq_cons ha
        exact Step.argsHeadHalt
          (ihrest static outer (.args rest0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.args hreq.symm))
          (ihe static outer (.expr e0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.expr heq.symm))
    | expr => simp [inlineHelpersCode] at hc
    | stmt => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case funDef funs V st n ps rs body =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineHelpersCode, inlineHelpersStmt] at hc
        exact Step.funDef
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case block funs V st bodyT Vb stb o hbody ihbody =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineHelpersCode, inlineHelpersStmt] at hc
        rename_i body
        have hbodyEq := hc
        have hfunEq : hoist D bodyT :: funs =
            inlineHelpersFuns litOK (hoist D body :: static) ++ outer := by
          rw [hf, inlineHelpersFuns]
          simp [hbodyEq, hoist_inlineHelpersStmts]
        have hcodeEq : Code.stmts bodyT = inlineHelpersCode litOK
            (hoist D body :: static) (.stmts body) := by
          simpa [inlineHelpersCode, inlineHelpersBlock] using
            congrArg Code.stmts hbodyEq
        exact Step.block
          (ihbody (hoist D body :: static) outer (.stmts body) hfunEq hcodeEq)
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case letZero funs V st vars =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineHelpersCode, inlineHelpersStmt] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact Step.letZero
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case letVal funs V st vars eT vals st1 he hlen ihe =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineHelpersCode, inlineHelpersStmt] at hc
        rename_i vars0 val0
        cases val0 <;> simp at hc
        rename_i e0
        obtain ⟨rfl, heq⟩ := hc
        exact Step.letVal
          (ihe static outer (.expr e0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.expr heq.symm)) hlen
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case letHalt funs V st vars eT st1 he ihe =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineHelpersCode, inlineHelpersStmt] at hc
        rename_i vars0 val0
        cases val0 <;> simp at hc
        rename_i e0
        obtain ⟨rfl, heq⟩ := hc
        exact Step.letHalt
          (ihe static outer (.expr e0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.expr heq.symm))
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case assignVal funs V st vars eT vals st1 he hlen ihe =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineHelpersCode, inlineHelpersStmt] at hc
        rename_i vars0 e0
        obtain ⟨rfl, heq⟩ := hc
        exact Step.assignVal
          (ihe static outer (.expr e0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.expr heq)) hlen
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case assignHalt funs V st vars eT st1 he ihe =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineHelpersCode, inlineHelpersStmt] at hc
        rename_i vars0 e0
        obtain ⟨rfl, heq⟩ := hc
        exact Step.assignHalt
          (ihe static outer (.expr e0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.expr heq))
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case exprStmt funs V st eT st1 he ihe =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineHelpersCode, inlineHelpersStmt] at hc
        rename_i e0
        exact Step.exprStmt
          (ihe static outer (.expr e0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.expr hc))
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case exprStmtHalt funs V st eT st1 he ihe =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineHelpersCode, inlineHelpersStmt] at hc
        rename_i e0
        exact Step.exprStmtHalt
          (ihe static outer (.expr e0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.expr hc))
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case ifTrue funs V st cT bodyT cv st1 V' st2 o hcond hnz hbody ihcond ihbody =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineHelpersCode, inlineHelpersStmt] at hc
        rename_i c0 body0
        obtain ⟨hceq, hbeq⟩ := hc
        exact Step.ifTrue
          (ihcond static outer (.expr c0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.expr hceq)) hnz
          (ihbody static outer (.stmt (.block body0)) hf
            (by simpa [inlineHelpersCode, inlineHelpersStmt] using
              congrArg (fun b => Code.stmt (.block b)) hbeq))
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case ifFalse funs V st cT bodyT cv st1 hcond hz ihcond =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineHelpersCode, inlineHelpersStmt] at hc
        rename_i c0 body0
        obtain ⟨hceq, hbeq⟩ := hc
        exact Step.ifFalse (body := body0)
          (ihcond static outer (.expr c0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.expr hceq)) hz
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case ifHalt funs V st cT bodyT st1 hcond ihcond =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineHelpersCode, inlineHelpersStmt] at hc
        rename_i c0 body0
        obtain ⟨hceq, hbeq⟩ := hc
        exact Step.ifHalt (body := body0)
          (ihcond static outer (.expr c0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.expr hceq))
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case switchExec funs V st cT casesT dfltT cv st1 V' st2 o hcond hbody ihcond ihbody =>
    cases code with
    | stmt s =>
        cases s with
        | block body => simp [inlineHelpersCode, inlineHelpersStmt] at hc
        | funDef fn ps rs body => simp [inlineHelpersCode, inlineHelpersStmt] at hc
        | letDecl vars val => simp [inlineHelpersCode, inlineHelpersStmt] at hc
        | assign vars e => simp [inlineHelpersCode, inlineHelpersStmt] at hc
        | cond c body => simp [inlineHelpersCode, inlineHelpersStmt] at hc
        | forLoop init c post body => simp [inlineHelpersCode, inlineHelpersStmt] at hc
        | exprStmt e => simp [inlineHelpersCode, inlineHelpersStmt] at hc
        | «break» => simp [inlineHelpersCode, inlineHelpersStmt] at hc
        | «continue» => simp [inlineHelpersCode, inlineHelpersStmt] at hc
        | leave => simp [inlineHelpersCode, inlineHelpersStmt] at hc
        | switch c0 cases0 dflt0 =>
          rw [inlineHelpersCode, inlineHelpersStmt_switch] at hc
          simp only at hc
          obtain ⟨_, rfl, rfl⟩ := hc
          have hc0 := ihcond static outer (.expr c0) hf
            (by simp [inlineHelpersCode])
          have hsel : selectSwitch D cv (inlineHelpersCases litOK static cases0)
              (dflt0.map (inlineHelpersBlock litOK static)) =
              inlineHelpersBlock litOK static (selectSwitch D cv cases0 dflt0) := by
            simpa only [selectSwitch_open_eq] using
              selectSwitch_inlineHelpers static cv cases0 dflt0
          have hb0 := ihbody static outer
            (.stmt (.block (selectSwitch D cv cases0 dflt0))) hf
            (by simpa [inlineHelpersCode, inlineHelpersStmt, inlineHelpersBlock] using
              congrArg (fun b => Code.stmt (.block b)) hsel)
          exact Step.switchExec hc0 hb0
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case switchHalt funs V st cT casesT dfltT st1 hcond ihcond =>
    cases code with
    | stmt s =>
        cases s with
        | block body => simp [inlineHelpersCode, inlineHelpersStmt] at hc
        | funDef fn ps rs body => simp [inlineHelpersCode, inlineHelpersStmt] at hc
        | letDecl vars val => simp [inlineHelpersCode, inlineHelpersStmt] at hc
        | assign vars e => simp [inlineHelpersCode, inlineHelpersStmt] at hc
        | cond c body => simp [inlineHelpersCode, inlineHelpersStmt] at hc
        | forLoop init c post body => simp [inlineHelpersCode, inlineHelpersStmt] at hc
        | exprStmt e => simp [inlineHelpersCode, inlineHelpersStmt] at hc
        | «break» => simp [inlineHelpersCode, inlineHelpersStmt] at hc
        | «continue» => simp [inlineHelpersCode, inlineHelpersStmt] at hc
        | leave => simp [inlineHelpersCode, inlineHelpersStmt] at hc
        | switch c0 cases0 dflt0 =>
          rw [inlineHelpersCode, inlineHelpersStmt_switch] at hc
          simp only at hc
          obtain ⟨_, rfl, rfl⟩ := hc
          exact Step.switchHalt (cases := cases0) (dflt := dflt0)
            (ihcond static outer (.expr c0) hf
              (by simp [inlineHelpersCode]))
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case forLoop funs V st initT cT postT bodyT Vinit stinit Vend stend o
      hinit hloop ihinit ihloop =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineHelpersCode, inlineHelpersStmt] at hc
        rename_i init0 c0 post0 body0
        obtain ⟨hiEq, hcEq, hpEq, hbEq⟩ := hc
        let loopStatic := hoist D init0 :: static
        have hfunEq : hoist D initT :: funs =
            inlineHelpersFuns litOK loopStatic ++ outer := by
          rw [hf, inlineHelpersFuns]
          simp [hiEq, hoist_inlineHelpersStmts]
        have hiCode : Code.stmts initT =
            inlineHelpersCode litOK loopStatic (.stmts init0) := by
          simpa [inlineHelpersCode, loopStatic] using congrArg Code.stmts hiEq
        have hlCode : Code.loop cT postT bodyT =
            inlineHelpersCode litOK loopStatic (.loop c0 post0 body0) := by
          simp only [inlineHelpersCode, Code.loop.injEq]
          exact ⟨hcEq, hpEq, hbEq⟩
        exact Step.forLoop
          (ihinit loopStatic outer (.stmts init0) hfunEq hiCode)
          (ihloop loopStatic outer (.loop c0 post0 body0) hfunEq hlCode)
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case forInitHalt funs V st initT cT postT bodyT Vinit stinit hinit ihinit =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineHelpersCode, inlineHelpersStmt] at hc
        rename_i init0 c0 post0 body0
        obtain ⟨hiEq, hcEq, hpEq, hbEq⟩ := hc
        let loopStatic := hoist D init0 :: static
        have hfunEq : hoist D initT :: funs =
            inlineHelpersFuns litOK loopStatic ++ outer := by
          rw [hf, inlineHelpersFuns]
          simp [hiEq, hoist_inlineHelpersStmts]
        have hiCode : Code.stmts initT =
            inlineHelpersCode litOK loopStatic (.stmts init0) := by
          simpa [inlineHelpersCode, loopStatic] using congrArg Code.stmts hiEq
        exact Step.forInitHalt
          (ihinit loopStatic outer (.stmts init0) hfunEq hiCode)
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case «break» funs V st =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineHelpersCode, inlineHelpersStmt] at hc
        exact Step.break
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case «continue» funs V st =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineHelpersCode, inlineHelpersStmt] at hc
        exact Step.continue
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case leave funs V st =>
    cases code with
    | stmt s =>
        cases s <;> simp [inlineHelpersCode, inlineHelpersStmt] at hc
        exact Step.leave
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case seqNil funs V st =>
    cases code with
    | stmts ss0 =>
        have hs : inlineHelpersStmts litOK static ss0 = [] := by
          simpa [inlineHelpersCode] using hc.symm
        have : ss0 = [] := inlineHelpersStmts_eq_nil hs
        subst ss0
        exact Step.seqNil
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmt => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case seqCons funs V st sT restT V1 st1 V2 st2 o hs hrest ihs ihrest =>
    cases code with
    | stmts ss0 =>
        have heq : inlineHelpersStmts litOK static ss0 = sT :: restT := by
          simpa [inlineHelpersCode] using hc.symm
        obtain ⟨s0, rest0, rfl, hseq, hreq⟩ := inlineHelpersStmts_eq_cons heq
        exact Step.seqCons
          (ihs static outer (.stmt s0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.stmt hseq.symm))
          (ihrest static outer (.stmts rest0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.stmts hreq.symm))
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmt => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case seqStop funs V st sT restT V1 st1 o hs hne ihs =>
    cases code with
    | stmts ss0 =>
        have heq : inlineHelpersStmts litOK static ss0 = sT :: restT := by
          simpa [inlineHelpersCode] using hc.symm
        obtain ⟨s0, rest0, rfl, hseq, hreq⟩ := inlineHelpersStmts_eq_cons heq
        exact Step.seqStop
          (ihs static outer (.stmt s0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.stmt hseq.symm)) hne
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmt => simp [inlineHelpersCode] at hc
    | loop => simp [inlineHelpersCode] at hc
  case loopDone funs V st cT postT bodyT cv st1 hcond hz ihcond =>
    cases code with
    | loop c0 post0 body0 =>
        simp only [inlineHelpersCode, Code.loop.injEq] at hc
        obtain ⟨hcEq, hpEq, hbEq⟩ := hc
        exact Step.loopDone
          (ihcond static outer (.expr c0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.expr hcEq)) hz
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmt => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
  case loopCondHalt funs V st cT postT bodyT st1 hcond ihcond =>
    cases code with
    | loop c0 post0 body0 =>
        simp only [inlineHelpersCode, Code.loop.injEq] at hc
        obtain ⟨hcEq, hpEq, hbEq⟩ := hc
        exact Step.loopCondHalt (post := post0) (body := body0)
          (ihcond static outer (.expr c0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.expr hcEq))
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmt => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
  case loopStep funs V st cT postT bodyT cv st1 Vb stb ob Vp stp Vend stend o
      hcond hnz hbody hob hpost hloop ihcond ihbody ihpost ihloop =>
    cases code with
    | loop c0 post0 body0 =>
        simp only [inlineHelpersCode, Code.loop.injEq] at hc
        obtain ⟨hcEq, hpEq, hbEq⟩ := hc
        exact Step.loopStep
          (ihcond static outer (.expr c0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.expr hcEq)) hnz
          (ihbody static outer (.stmt (.block body0)) hf
            (by simpa [inlineHelpersCode, inlineHelpersStmt] using
              congrArg (fun b => Code.stmt (.block b)) hbEq)) hob
          (ihpost static outer (.stmt (.block post0)) hf
            (by simpa [inlineHelpersCode, inlineHelpersStmt] using
              congrArg (fun b => Code.stmt (.block b)) hpEq))
          (ihloop static outer (.loop c0 post0 body0) hf
            (by simp only [inlineHelpersCode, Code.loop.injEq]; exact ⟨hcEq, hpEq, hbEq⟩))
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmt => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
  case loopPostHalt funs V st cT postT bodyT cv st1 Vb stb ob Vp stp
      hcond hnz hbody hob hpost ihcond ihbody ihpost =>
    cases code with
    | loop c0 post0 body0 =>
        simp only [inlineHelpersCode, Code.loop.injEq] at hc
        obtain ⟨hcEq, hpEq, hbEq⟩ := hc
        exact Step.loopPostHalt
          (ihcond static outer (.expr c0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.expr hcEq)) hnz
          (ihbody static outer (.stmt (.block body0)) hf
            (by simpa [inlineHelpersCode, inlineHelpersStmt] using
              congrArg (fun b => Code.stmt (.block b)) hbEq)) hob
          (ihpost static outer (.stmt (.block post0)) hf
            (by simpa [inlineHelpersCode, inlineHelpersStmt] using
              congrArg (fun b => Code.stmt (.block b)) hpEq))
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmt => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
  case loopBreak funs V st cT postT bodyT cv st1 Vb stb hcond hnz hbody ihcond ihbody =>
    cases code with
    | loop c0 post0 body0 =>
        simp only [inlineHelpersCode, Code.loop.injEq] at hc
        obtain ⟨hcEq, hpEq, hbEq⟩ := hc
        exact Step.loopBreak (post := post0)
          (ihcond static outer (.expr c0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.expr hcEq)) hnz
          (ihbody static outer (.stmt (.block body0)) hf
            (by simpa [inlineHelpersCode, inlineHelpersStmt] using
              congrArg (fun b => Code.stmt (.block b)) hbEq))
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmt => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
  case loopLeave funs V st cT postT bodyT cv st1 Vb stb hcond hnz hbody ihcond ihbody =>
    cases code with
    | loop c0 post0 body0 =>
        simp only [inlineHelpersCode, Code.loop.injEq] at hc
        obtain ⟨hcEq, hpEq, hbEq⟩ := hc
        exact Step.loopLeave (post := post0)
          (ihcond static outer (.expr c0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.expr hcEq)) hnz
          (ihbody static outer (.stmt (.block body0)) hf
            (by simpa [inlineHelpersCode, inlineHelpersStmt] using
              congrArg (fun b => Code.stmt (.block b)) hbEq))
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmt => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc
  case loopBodyHalt funs V st cT postT bodyT cv st1 Vb stb hcond hnz hbody ihcond ihbody =>
    cases code with
    | loop c0 post0 body0 =>
        simp only [inlineHelpersCode, Code.loop.injEq] at hc
        obtain ⟨hcEq, hpEq, hbEq⟩ := hc
        exact Step.loopBodyHalt (post := post0)
          (ihcond static outer (.expr c0) hf
            (by simpa [inlineHelpersCode] using congrArg Code.expr hcEq)) hnz
          (ihbody static outer (.stmt (.block body0)) hf
            (by simpa [inlineHelpersCode, inlineHelpersStmt] using
              congrArg (fun b => Code.stmt (.block b)) hbEq))
    | expr => simp [inlineHelpersCode] at hc
    | args => simp [inlineHelpersCode] at hc
    | stmt => simp [inlineHelpersCode] at hc
    | stmts => simp [inlineHelpersCode] at hc


theorem inlineHelpersBlock_equiv {litOK : Bool} (b : Block Op) :
    EquivBlock D b (inlineHelpersBlock (calls := calls) (creates := creates) litOK
      ([] : FunEnv D) b) := by
  intro funs V st V' st' o
  constructor
  · intro h
    have hfwd := YulEvmCompiler.Optimizer.Step.inlineHelpers_forward (litOK := litOK) h
      ([] : FunEnv D) funs rfl
    simpa [inlineHelpersCode, inlineHelpersStmt, inlineHelpersBlock,
      inlineHelpersFuns] using hfwd
  · intro h
    exact YulEvmCompiler.Optimizer.Step.inlineHelpers_reverse (litOK := litOK) h
      ([] : FunEnv D) funs
      (.stmt (.block b)) (by simp [inlineHelpersFuns])
      (by simp [inlineHelpersCode, inlineHelpersStmt, inlineHelpersBlock])

/-- **The Core-backed helper inliner is a verified pass.** `litOK := true` is
the block-pipeline classification; `litOK := false` restricts to the
resolution-stable fragment used by the object pipeline. -/
def inlineHelpersPass (litOK : Bool) : Pass D where
  run := inlineHelpersBlock (calls := calls) (creates := creates) litOK []
  sound := inlineHelpersBlock_equiv

end YulEvmCompiler.Optimizer
