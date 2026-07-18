import YulEvmCompiler.Optimizer.Core.Basic
import YulSemantics.Equiv

set_option warningAsError true

/-!
# Core substitution: closed-term instantiation of parameter contexts

The payoff of intrinsically scoped Core terms: a term over a parameter context
`Γ = params` is *closed* over those parameters, so instantiating it with caller
arguments is first-occurrence name lookup — no capture, no renaming, no
freshness discipline. This module provides:

* `Value.substEmit`/`Term.substEmit` — substitute caller argument expressions
  for the parameter context and erase to raw Yul in one step;
* `isValueExpr` — the raw argument shapes substitution accepts (variables and
  non-string literals: exactly the ANF values, whose evaluation is pure);
* `valueEval` — the *functional* semantics of value-shaped expressions, with
  `valueEval_eval_iff`/`valuesEval_args_iff` reflecting the relational `Step`
  judgment into `Option`-equational reasoning; and
* the zip/find alignment lemmas connecting `substEmit`'s argument choice, the
  callee frame built by `Step.callOk`, and pointwise argument evaluation.

First-occurrence lookup deliberately mirrors `VEnv.get` (`List.find?`), so the
correspondence between a substituted caller value and the callee's frame
lookup (`substEmit_value_correspond`) is definitional rather than index
arithmetic.
-/

namespace YulEvmCompiler.Optimizer.Core

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}
local notation "D" => evmWithExternal calls creates

/-! ## Syntax: variables read by a term, substitution, string-freeness -/

/-- The source names a Core value reads. -/
def Value.vars {Γ : Ctx} : Value Γ → List Ident
  | .lit _ => []
  | .var ref => [ref.name]

/-- The source names a Core term reads. Always a subset of `Γ`, by
construction of `Var`. -/
def Term.vars {Γ : Ctx} : Term Γ outputs → List Ident
  | .atom value => value.vars
  | .builtin _ args => args.values.flatMap Value.vars

/-- Substitute caller arguments for a parameter-context value: a literal is
itself; a parameter is replaced by the argument paired with the parameter's
*first* occurrence (mirroring `VEnv.get`). The fallback branch is unreachable
whenever `args.length = params.length` (`zip_find_of_mem`). -/
def Value.substEmit {params : Ctx} (args : List (Expr Op)) :
    Value params → Expr Op
  | .lit literal => .lit literal
  | .var ref =>
      match (params.zip args).find? (fun entry => entry.1 = ref.name) with
      | some entry => entry.2
      | none => .var ref.name

/-- Substitute caller arguments through a term and erase to raw Yul. -/
def Term.substEmit {params : Ctx} (args : List (Expr Op)) :
    Term params outputs → Expr Op
  | .atom value => value.substEmit args
  | .builtin op termArgs =>
      .builtin op.toOp (termArgs.values.map (Value.substEmit args))

/-- No string literal appears in the value (string literals are the layout
hooks `dataoffset`/`datasize` consume; keeping them out of inlined terms keeps
the transform disjoint from object-layout resolution). -/
def Value.stringFree {Γ : Ctx} : Value Γ → Bool
  | .lit (.string _) => false
  | _ => true

/-- No string literal appears anywhere in the term. -/
def Term.stringFree {Γ : Ctx} : Term Γ outputs → Bool
  | .atom value => value.stringFree
  | .builtin _ args => args.values.all Value.stringFree

/-- Is the value a variable reference? -/
def Value.isVar {Γ : Ctx} : Value Γ → Bool
  | .var _ => true
  | .lit _ => false

/-- Every value read by the term is a variable. Object-layout resolution never
produces a bare variable, so terms of this shape are exactly the ones whose
classification is stable under resolution (see the resolution congruence). -/
def Term.argsVarsOnly {Γ : Ctx} : Term Γ outputs → Bool
  | .atom value => value.isVar
  | .builtin _ args => args.values.all Value.isVar

/-- The term shapes the inliner accepts: a bare parameter (handled by the
arity-preserving `add(e, 0)` fence) or a pure built-in application (handled by
substitution). A bare literal is rejected — it can only classify for
zero-parameter helpers, which are not worth a rewrite arm. -/
def Term.inlinableShape {Γ : Ctx} : Term Γ outputs → Bool
  | .atom value => value.isVar
  | .builtin _ _ => true

/-! ## Value-shaped raw expressions and their functional semantics -/

/-- The raw argument shapes substitution accepts: variables and non-string
literals. These are exactly the expressions whose evaluation reads at most the
variable environment — pure, non-halting, function-environment-independent. -/
def isValueExpr : Expr Op → Bool
  | .var _ => true
  | .lit (.string _) => false
  | .lit _ => true
  | _ => false

/-- Is the raw expression a bare variable? Object-layout resolution never
creates or destroys this shape, so var-shaped call arguments are the
resolution-stable fragment. -/
def isVarExpr : Expr Op → Bool
  | .var _ => true
  | _ => false

/-- Variables are value-shaped. -/
theorem isVarExpr_value {e : Expr Op} (h : isVarExpr e = true) :
    isValueExpr e = true := by
  cases e <;> simp [isVarExpr, isValueExpr] at h ⊢

/-- The value of a value-shaped expression, as a function of the variable
environment alone. -/
def valueEval (V : VEnv D) : Expr Op → Option U256
  | .var x => VEnv.get V x
  | .lit literal => some ((evmWithExternal calls creates).litValue literal)
  | _ => none

/-- Reflection of `Step` on a value-shaped expression into `valueEval`: the
expression evaluates exactly to its functional value, leaves the state
untouched, and cannot halt. -/
theorem valueEval_eval_iff {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {e : Expr Op} (he : isValueExpr e = true) {r : EResult D} :
    Step D funs V st (.expr e) (.eres r) ↔
      ∃ w, valueEval (calls := calls) (creates := creates) V e = some w ∧
        r = .vals [w] st := by
  cases e with
  | var x =>
      constructor
      · intro h
        cases h with
        | var hv => exact ⟨_, hv, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        exact Step.var hw
  | lit literal =>
      constructor
      · intro h
        cases h with
        | lit => exact ⟨_, rfl, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        simp only [valueEval, Option.some.injEq] at hw
        subst hw
        exact Step.lit
  | builtin op args => simp [isValueExpr] at he
  | call fn args => simp [isValueExpr] at he

/-- A value-shaped expression's evaluation does not consult the function
environment. -/
theorem valueExpr_funs_iff {funs funs' : FunEnv D} {V : VEnv D} {st : EvmState}
    {e : Expr Op} (he : isValueExpr e = true) {r : EResult D} :
    Step D funs V st (.expr e) (.eres r) ↔ Step D funs' V st (.expr e) (.eres r) := by
  rw [valueEval_eval_iff he, valueEval_eval_iff he]

/-- Evaluate a list of value-shaped expressions functionally. -/
def valuesEval (V : VEnv D) (es : List (Expr Op)) : Option (List U256) :=
  es.mapM (valueEval (calls := calls) (creates := creates) V)

@[simp] theorem valuesEval_nil {V : VEnv D} :
    valuesEval (calls := calls) (creates := creates) V [] = some [] := rfl

@[simp] theorem valuesEval_cons {V : VEnv D} {e : Expr Op} {es : List (Expr Op)} :
    valuesEval (calls := calls) (creates := creates) V (e :: es) =
      (valueEval (calls := calls) (creates := creates) V e).bind fun w =>
        (valuesEval (calls := calls) (creates := creates) V es).map (w :: ·) := by
  simp only [valuesEval, List.mapM_cons, Option.pure_def, Option.bind_eq_bind]
  cases valueEval (calls := calls) (creates := creates) V e with
  | none => rfl
  | some w =>
      cases List.mapM (valueEval (calls := calls) (creates := creates) V) es <;> rfl

/-- Reflection of the `args` judgment on value-shaped expressions: the list
evaluates exactly to its functional values with the state untouched, and
cannot halt. -/
theorem valuesEval_args_iff {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    {es : List (Expr Op)} (hes : ∀ e ∈ es, isValueExpr e = true) {r : EResult D} :
    Step D funs V st (.args es) (.eres r) ↔
      ∃ ws, valuesEval (calls := calls) (creates := creates) V es = some ws ∧
        r = .vals ws st := by
  induction es generalizing r with
  | nil =>
      constructor
      · intro h
        cases h with
        | argsNil => exact ⟨[], rfl, rfl⟩
      · rintro ⟨ws, hws, rfl⟩
        simp only [valuesEval_nil, Option.some.injEq] at hws
        subst hws
        exact Step.argsNil
  | cons e rest ih =>
      have he : isValueExpr e = true := hes e (by simp)
      have hrest : ∀ e' ∈ rest, isValueExpr e' = true :=
        fun e' h' => hes e' (by simp [h'])
      constructor
      · intro h
        cases h with
        | argsCons ha hh =>
            obtain ⟨ws, hws, hr⟩ := (ih hrest).mp ha
            injection hr with hvals hst
            subst hvals
            subst hst
            obtain ⟨w, hw, hr'⟩ := (valueEval_eval_iff he).mp hh
            injection hr' with hvals' hst'
            simp only [List.cons.injEq, and_true] at hvals'
            subst hvals'
            subst hst'
            exact ⟨_, by simp [hw, hws], rfl⟩
        | argsRestHalt ha =>
            obtain ⟨ws, _, hr⟩ := (ih hrest).mp ha
            simp at hr
        | argsHeadHalt ha hh =>
            obtain ⟨w, _, hr'⟩ := (valueEval_eval_iff he).mp hh
            simp at hr'
      · rintro ⟨ws, hws, rfl⟩
        simp only [valuesEval_cons, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hws
        obtain ⟨w, hw, ws', hws', rfl⟩ := hws
        exact Step.argsCons ((ih hrest).mpr ⟨ws', hws', rfl⟩)
          ((valueEval_eval_iff he).mpr ⟨w, hw, rfl⟩)

/-- Every element of a functionally evaluated list evaluates. -/
theorem valuesEval_mem_isSome {V : VEnv D} {es : List (Expr Op)} {ws : List U256}
    (h : valuesEval (calls := calls) (creates := creates) V es = some ws)
    {e : Expr Op} (he : e ∈ es) :
    (valueEval (calls := calls) (creates := creates) V e).isSome := by
  induction es generalizing ws with
  | nil => cases he
  | cons e' rest ih =>
      simp only [valuesEval_cons, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨w, hw, ws', hws', rfl⟩ := h
      cases he with
      | head => simp [hw]
      | tail _ hmem => exact ih hws' hmem

/-- Functional evaluation preserves list length. -/
theorem valuesEval_length {V : VEnv D} {es : List (Expr Op)} {ws : List U256}
    (h : valuesEval (calls := calls) (creates := creates) V es = some ws) :
    ws.length = es.length := by
  induction es generalizing ws with
  | nil =>
      simp only [valuesEval_nil, Option.some.injEq] at h
      subst h
      rfl
  | cons e rest ih =>
      simp only [valuesEval_cons, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨w, _, ws', hws', rfl⟩ := h
      simp [ih hws']

/-- A list whose elements all evaluate, evaluates. -/
theorem valuesEval_isSome_of_forall {V : VEnv D} {es : List (Expr Op)}
    (h : ∀ e ∈ es, (valueEval (calls := calls) (creates := creates) V e).isSome) :
    (valuesEval (calls := calls) (creates := creates) V es).isSome := by
  induction es with
  | nil => simp
  | cons e rest ih =>
      have he := h e (by simp)
      have hrest := ih (fun e' h' => h e' (by simp [h']))
      rw [Option.isSome_iff_exists] at he hrest
      obtain ⟨w, hw⟩ := he
      obtain ⟨ws, hws⟩ := hrest
      simp [hw, hws]

/-! ## Alignment: substitution choice, frame lookup, argument evaluation -/

/-- With matching lengths, first-occurrence lookup in a parameter/argument zip
succeeds for every parameter and returns a pair keyed by that parameter. -/
theorem zip_find_of_mem {params : Ctx} {args : List (Expr Op)}
    (hlen : args.length = params.length) {x : Ident} (hx : x ∈ params) :
    ∃ e, (params.zip args).find? (fun entry => entry.1 = x) = some (x, e) := by
  induction params generalizing args with
  | nil => cases hx
  | cons p rest ih =>
      cases args with
      | nil => simp at hlen
      | cons a arest =>
          by_cases hpx : p = x
          · subst hpx
            exact ⟨a, by rw [List.zip_cons_cons, List.find?_cons_of_pos (by simp)]⟩
          · have hx' : x ∈ rest := by
              cases hx with
              | head => exact absurd rfl hpx
              | tail _ h => exact h
            obtain ⟨e, he⟩ := ih (by simpa using hlen) hx'
            exact ⟨e, by
              rw [List.zip_cons_cons, List.find?_cons_of_neg (by simp [hpx])]
              exact he⟩

/-- With `Nodup` parameters, first-occurrence lookup finds *each* zip entry:
the entry present in the zip is the one selected for its key. -/
theorem find?_zip_eq_of_nodup {params : Ctx} {args : List (Expr Op)}
    (hnd : params.Nodup) {x : Ident} {e : Expr Op}
    (hmem : (x, e) ∈ params.zip args) :
    (params.zip args).find? (fun entry => entry.1 = x) = some (x, e) := by
  induction params generalizing args with
  | nil => simp at hmem
  | cons p rest ih =>
      cases args with
      | nil => simp at hmem
      | cons a arest =>
          rw [List.zip_cons_cons] at hmem
          cases hmem with
          | head =>
              rw [List.zip_cons_cons, List.find?_cons_of_pos (by simp)]
          | tail _ hmem' =>
              have hp : p ∉ rest := (List.nodup_cons.mp hnd).1
              have hx : x ∈ rest := by
                have := List.of_mem_zip hmem'
                exact this.1
              have hpx : p ≠ x := fun h => hp (h ▸ hx)
              rw [List.zip_cons_cons, List.find?_cons_of_neg (by simp [hpx])]
              exact ih (List.nodup_cons.mp hnd).2 hmem'

/-- With matching lengths, every argument is paired with some parameter. -/
theorem exists_zip_left {params : Ctx} {args : List (Expr Op)}
    (hlen : args.length = params.length) {e : Expr Op} (he : e ∈ args) :
    ∃ p, (p, e) ∈ params.zip args := by
  induction params generalizing args with
  | nil =>
      cases args with
      | nil => cases he
      | cons a arest => simp at hlen
  | cons p rest ih =>
      cases args with
      | nil => cases he
      | cons a arest =>
          cases he with
          | head => exact ⟨p, by simp⟩
          | tail _ hmem =>
              obtain ⟨p', hp'⟩ := ih (by simpa using hlen) hmem
              exact ⟨p', by simp [hp']⟩

/-- Transport a zip lookup along a successful functional evaluation: if the
arguments evaluate to `argvals`, the value chosen for a parameter is the
evaluation of the argument chosen for it. -/
theorem zip_find_valuesEval {params : Ctx} {args : List (Expr Op)}
    {argvals : List U256} {V : VEnv D}
    (hvals : valuesEval (calls := calls) (creates := creates) V args = some argvals)
    {x : Ident} {e : Expr Op}
    (hfind : (params.zip args).find? (fun entry => entry.1 = x) = some (x, e)) :
    ∃ w, (params.zip argvals).find? (fun entry => entry.1 = x) = some (x, w) ∧
      valueEval (calls := calls) (creates := creates) V e = some w := by
  induction params generalizing args argvals with
  | nil => simp at hfind
  | cons p rest ih =>
      cases args with
      | nil => simp at hfind
      | cons a arest =>
          simp only [valuesEval_cons, Option.bind_eq_some_iff,
            Option.map_eq_some_iff] at hvals
          obtain ⟨w, hw, ws, hws, rfl⟩ := hvals
          by_cases hpx : p = x
          · subst hpx
            rw [List.zip_cons_cons, List.find?_cons_of_pos (by simp)] at hfind
            injection hfind with hfind'
            obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ hfind'
            exact ⟨w, by rw [List.zip_cons_cons, List.find?_cons_of_pos (by simp)], hw⟩
          · rw [List.zip_cons_cons, List.find?_cons_of_neg (by simp [hpx])] at hfind
            obtain ⟨w', hw', he'⟩ := ih hws hfind
            exact ⟨w', by
              rw [List.zip_cons_cons, List.find?_cons_of_neg (by simp [hpx])]
              exact hw', he'⟩

/-- The callee frame agrees with the zip lookup on every parameter: reading a
parameter from `params.zip argvals ++ suffix` is first-occurrence zip lookup,
regardless of the suffix (the return-variable bindings). -/
theorem frame_get_of_zip_find {params : Ctx} {argvals : List U256}
    {suffix : VEnv D} {x : Ident} {w : U256}
    (hfind : (params.zip argvals).find? (fun entry => entry.1 = x) = some (x, w)) :
    VEnv.get ((params.zip argvals : VEnv D) ++ suffix) x = some w := by
  unfold VEnv.get
  rw [List.find?_append, hfind]
  rfl

/-! ## The substitution correspondence

The heart of the β argument: under a caller environment `V` in which the
arguments functionally evaluate to `argvals`, a substituted value evaluates in
`V` exactly as the original value evaluates in the callee frame
`params.zip argvals ++ suffix`. Purely equational. -/

theorem substEmit_value_correspond {params : Ctx} {args : List (Expr Op)}
    {argvals : List U256} {V : VEnv D} {suffix : VEnv D}
    (hlen : args.length = params.length)
    (hvals : valuesEval (calls := calls) (creates := creates) V args = some argvals)
    (value : Value params) :
    valueEval (calls := calls) (creates := creates) V (value.substEmit args) =
      valueEval (calls := calls) (creates := creates)
        ((params.zip argvals : VEnv D) ++ suffix) value.emit := by
  cases value with
  | lit literal => rfl
  | var ref =>
      obtain ⟨e, hfind⟩ := zip_find_of_mem hlen ref.bound
      obtain ⟨w, hfind', he⟩ := zip_find_valuesEval (V := V) hvals hfind
      have hsub : Value.substEmit (params := params) args (.var ref) = e := by
        simp only [Value.substEmit, hfind]
      rw [hsub, he]
      have hget := frame_get_of_zip_find (suffix := suffix) hfind'
      simp only [Value.emit, Var.emit, valueEval]
      exact hget.symm

/-- The whole-term argument correspondence: the substituted values evaluate in
the caller environment exactly as the emitted originals evaluate in the callee
frame. -/
theorem substEmit_values_correspond {params : Ctx} {args : List (Expr Op)}
    {argvals : List U256} {V : VEnv D} {suffix : VEnv D}
    (hlen : args.length = params.length)
    (hvals : valuesEval (calls := calls) (creates := creates) V args = some argvals)
    (values : List (Value params)) :
    valuesEval (calls := calls) (creates := creates) V
        (values.map (Value.substEmit args)) =
      valuesEval (calls := calls) (creates := creates)
        ((params.zip argvals : VEnv D) ++ suffix) (values.map Value.emit) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.map_cons, valuesEval_cons, ih,
        substEmit_value_correspond (suffix := suffix) hlen hvals value]

/-! ## Shape facts -/

/-- Substituted values of a string-free term are value-shaped whenever the
caller arguments are. -/
theorem substEmit_isValue {params : Ctx} {args : List (Expr Op)}
    {value : Value params}
    (hargs : ∀ e ∈ args, isValueExpr e = true)
    (hsf : value.stringFree = true) :
    isValueExpr (Value.substEmit (params := params) args value) = true := by
  cases value with
  | lit literal =>
      cases literal with
      | string s => simp [Value.stringFree] at hsf
      | number n => rfl
      | bool b => rfl
  | var ref =>
      rw [Value.substEmit]
      cases hfind : (params.zip args).find? (fun entry => entry.1 = ref.name) with
      | none => rfl
      | some entry =>
          have hmem := List.mem_of_find?_eq_some hfind
          exact hargs entry.2 (List.of_mem_zip hmem).2

/-- The emitted form of a string-free value is value-shaped. -/
theorem emit_isValue {Γ : Ctx} {value : Value Γ}
    (hsf : value.stringFree = true) : isValueExpr value.emit = true := by
  cases value with
  | lit literal =>
      cases literal with
      | string s => simp [Value.stringFree] at hsf
      | number n => rfl
      | bool b => rfl
  | var ref => rfl

/-- A parameter read by a term names one of the term's values. -/
theorem mem_vars_builtin {Γ : Ctx} {arity : Nat} {op : PureOp arity}
    {termArgs : Args Γ arity} {x : Ident}
    (hx : x ∈ (Term.builtin op termArgs).vars) :
    ∃ ref : Var Γ, ref.name = x ∧ Value.var ref ∈ termArgs.values := by
  simp only [Term.vars, List.mem_flatMap] at hx
  obtain ⟨value, hvmem, hxv⟩ := hx
  cases value with
  | lit literal => simp [Value.vars] at hxv
  | var ref =>
      simp only [Value.vars, List.mem_singleton] at hxv
      exact ⟨ref, hxv.symm, hvmem⟩

end YulEvmCompiler.Optimizer.Core
