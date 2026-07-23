import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate
import YulSemantics.Equiv
/-!
# Semantic soundness of name disambiguation — foundations

Goal: `EquivBlock D b (disambiguate b)` for well-formed `b`. Disambiguation
renames only *declared* (bound) names, and every declaration in a block is
dropped from the variable environment on block exit (`restore`) — so the renaming
is invisible in the observable result. Proving it, however, needs a bisimulation
that carries a *renaming* through the big-step judgment (`Step`).

This file builds the reusable variable-environment layer: `renVEnv σ V` renames a
variable environment's keys by `σ`, and the transport lemmas show the semantic
helpers (`get`, `set`, `setMany`, `bindZeros`, `restore`) commute with an
*injective* key-renaming. Injectivity is the semantic content of Yul's
no-shadowing rule (in-scope names are distinct) together with disambiguation's
globally-fresh, capture-avoiding `dsName`s.

The function-environment side and the `Step` induction proper build on top.
-/

namespace YulEvmCompiler.Optimizer.Normalize

open YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-! ### Renaming a variable environment -/

/-- `renVEnv σ V` is `V` with every key renamed by `σ` (values untouched). -/
def renVEnv (σ : Ident → Ident) (V : VEnv D) : VEnv D := V.map (fun p => (σ p.1, p.2))

@[simp] theorem renVEnv_nil (σ : Ident → Ident) : renVEnv σ ([] : VEnv D) = [] := rfl

@[simp] theorem renVEnv_cons (σ : Ident → Ident) (x : Ident) (v : D.Value) (V : VEnv D) :
    renVEnv σ ((x, v) :: V) = (σ x, v) :: renVEnv σ V := rfl

@[simp] theorem renVEnv_length (σ : Ident → Ident) (V : VEnv D) :
    (renVEnv σ V).length = V.length := by simp [renVEnv]

@[simp] theorem renVEnv_append (σ : Ident → Ident) (V W : VEnv D) :
    renVEnv σ (V ++ W) = renVEnv σ V ++ renVEnv σ W := by simp [renVEnv]

/-- Keys of a renamed environment are the σ-images of the keys. -/
theorem renVEnv_keys (σ : Ident → Ident) (V : VEnv D) :
    (renVEnv σ V).map Prod.fst = (V.map Prod.fst).map σ := by
  simp [renVEnv, List.map_map, Function.comp]

/-! ### `get` transport

For a *specific* looked-up name `x`, `get` needs only that `σ` does not merge any
other in-scope key onto `σ x` — captured by `hne : ∀ y ∈ keys, σ y = σ x → y = x`. -/

theorem renVEnv_get (σ : Ident → Ident) (V : VEnv D) (x : Ident)
    (hne : ∀ p ∈ V, σ p.1 = σ x → p.1 = x) :
    VEnv.get (renVEnv σ V) (σ x) = VEnv.get V x := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      simp only [renVEnv_cons, VEnv.get, List.find?_cons]
      by_cases hyx : y = x
      · subst hyx; simp
      · have hσ : ¬ (σ y = σ x) := fun h => hyx (hne (y, w) (List.mem_cons_self ..) h)
        simp only [hyx, hσ, decide_false, cond_false]
        exact ih (fun p hp => hne p (List.mem_cons_of_mem _ hp))
/-! ### `set` transport (same per-name no-merge condition as `get`) -/

theorem renVEnv_set (σ : Ident → Ident) (V : VEnv D) (x : Ident) (v : D.Value)
    (hne : ∀ p ∈ V, σ p.1 = σ x → p.1 = x) :
    VEnv.set (renVEnv σ V) (σ x) v = renVEnv σ (VEnv.set V x v) := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      simp only [renVEnv_cons, VEnv.set]
      by_cases hyx : y = x
      · subst hyx; simp
      · have hσ : ¬ (σ y = σ x) := fun h => hyx (hne (y, w) (List.mem_cons_self ..) h)
        rw [if_neg hyx, if_neg hσ, renVEnv_cons,
          ih (fun p hp => hne p (List.mem_cons_of_mem _ hp))]

/-! ### `bindZeros` and `restore` transport (unconditional) -/

@[simp] theorem renVEnv_bindZeros (σ : Ident → Ident) (xs : List Ident) :
    renVEnv σ (bindZeros D xs) = bindZeros D (xs.map σ) := by
  simp [renVEnv, bindZeros, List.map_map, Function.comp]

theorem renVEnv_restore (σ : Ident → Ident) (V W : VEnv D) :
    renVEnv σ (restore V W) = restore (renVEnv σ V) (renVEnv σ W) := by
  simp only [restore, renVEnv, List.map_drop, List.length_map]

/-! ### `setMany` transport (under a genuinely injective renaming) -/

theorem VEnv.setMany_cons (V : VEnv D) (x : Ident) (v : D.Value)
    (xs : List Ident) (vs : List D.Value) :
    VEnv.setMany V (x :: xs) (v :: vs) = VEnv.setMany (VEnv.set V x v) xs vs := by
  simp [VEnv.setMany, List.zip_cons_cons, List.foldl_cons]

theorem renVEnv_setMany (σ : Ident → Ident) (hinj : Function.Injective σ) :
    ∀ (vars : List Ident) (vals : List D.Value) (V : VEnv D),
      VEnv.setMany (renVEnv σ V) (vars.map σ) vals = renVEnv σ (VEnv.setMany V vars vals) := by
  intro vars
  induction vars with
  | nil => intro vals V; simp [VEnv.setMany]
  | cons x xs ih =>
      intro vals V
      cases vals with
      | nil => simp [VEnv.setMany]
      | cons v vs =>
          rw [List.map_cons, VEnv.setMany_cons, VEnv.setMany_cons,
            renVEnv_set σ V x v (fun _ _ h => hinj h), ih vs (VEnv.set V x v)]

/-! ### Renaming a function environment

The function-environment side of the bisimulation. `RenScopeRel φ BR` relates a
source scope to a target scope whose keys are `φ`-renamed and whose declarations
are related by an (abstract) body relation `BR` — instantiated later with the
syntactic translation. A single `φ` serves the whole stack: Yul forbids shadowing
a visible function, so function names across the in-scope stack are distinct and
one injective `φ` renames them all consistently. -/

/-- Source/target function scopes: `φ`-renamed keys, `BR`-related declarations. -/
def RenScopeRel (φ : Ident → Ident) (BR : FDecl D → FDecl D → Prop) (s₁ s₂ : FScope D) : Prop :=
  List.Forall₂ (fun p q => q.1 = φ p.1 ∧ BR p.2 q.2) s₁ s₂

/-- Source/target function environments: related scope-by-scope under one `φ`. -/
def RenFunsRel (φ : Ident → Ident) (BR : FDecl D → FDecl D → Prop) (f₁ f₂ : FunEnv D) : Prop :=
  List.Forall₂ (RenScopeRel φ BR) f₁ f₂

theorem RenFunsRel.cons {φ : Ident → Ident} {BR : FDecl D → FDecl D → Prop}
    {s₁ s₂ : FScope D} {f₁ f₂ : FunEnv D} (hs : RenScopeRel φ BR s₁ s₂)
    (hf : RenFunsRel φ BR f₁ f₂) : RenFunsRel φ BR (s₁ :: f₁) (s₂ :: f₂) :=
  List.Forall₂.cons hs hf

/-- A scope lookup transports across `RenScopeRel`: if `φ` merges no other key of
`s₁` onto `φ fn`, then `fn` resolves in `s₁` exactly when `φ fn` resolves in `s₂`,
to `BR`-related declarations. -/
theorem renScopeRel_find {φ : Ident → Ident} {BR : FDecl D → FDecl D → Prop}
    {s₁ s₂ : FScope D} (h : RenScopeRel φ BR s₁ s₂) (fn : Ident)
    (hinj : ∀ p ∈ s₁, φ p.1 = φ fn → p.1 = fn) :
    (s₁.find? (fun p => p.1 = fn) = none ∧ s₂.find? (fun p => p.1 = φ fn) = none) ∨
    (∃ p q, s₁.find? (fun p => p.1 = fn) = some p ∧ s₂.find? (fun p => p.1 = φ fn) = some q ∧
      q.1 = φ p.1 ∧ BR p.2 q.2) := by
  induction h with
  | nil => left; simp
  | @cons p q u₁ u₂ hpq _ ih =>
      by_cases hp : p.1 = fn
      · right
        refine ⟨p, q, List.find?_cons_of_pos (by simp [hp]),
          List.find?_cons_of_pos (by simp [hpq.1, hp]), hpq.1, hpq.2⟩
      · have hφ : ¬ (q.1 = φ fn) := by
          rw [hpq.1]; exact fun hc => hp (hinj p (List.mem_cons_self ..) hc)
        rw [List.find?_cons_of_neg (by simp [hp]), List.find?_cons_of_neg (by simp [hφ])]
        exact ih (fun p hp => hinj p (List.mem_cons_of_mem _ hp))

/-- `lookupFun` transports across `RenFunsRel` under an injective `φ`: a resolved
function has a `φ`-renamed counterpart with a `BR`-related declaration and a
related closure environment. -/
theorem lookupFun_renFunsRel {φ : Ident → Ident} {BR : FDecl D → FDecl D → Prop}
    (hinj : Function.Injective φ) {f₁ f₂ : FunEnv D} (hR : RenFunsRel φ BR f₁ f₂) :
    ∀ {fn : Ident} {decl : FDecl D} {cenv : FunEnv D},
      lookupFun f₁ fn = some (decl, cenv) →
      ∃ decl' cenv', lookupFun f₂ (φ fn) = some (decl', cenv') ∧
        BR decl decl' ∧ RenFunsRel φ BR cenv cenv' := by
  induction hR with
  | nil => intro fn decl cenv h; simp [lookupFun] at h
  | @cons s₁ s₂ t₁ t₂ hs hR' ih =>
      intro fn decl cenv h
      rcases renScopeRel_find hs fn (fun _ _ hc => hinj hc) with
        ⟨hn₁, hn₂⟩ | ⟨p, q, hp₁, hp₂, hkey, hd⟩
      · rw [lookupFun, hn₁] at h
        obtain ⟨decl', cenv', hl', hbody, hRc⟩ := ih h
        exact ⟨decl', cenv', by rw [lookupFun, hn₂]; exact hl', hbody, hRc⟩
      · rw [lookupFun, hp₁] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hd_eq, hcenv_eq⟩ := h
        subst hd_eq; subst hcenv_eq
        exact ⟨q.2, s₂ :: t₂, by rw [lookupFun, hp₂], hd, List.Forall₂.cons hs hR'⟩

/-! ### α-equivalence: the renaming relation the bisimulation ranges over

`AlphaExpr σ φ e₁ e₂` says `e₂` is `e₁` with free variable names renamed by `σ`
and free function names by `φ`. Expressions have no binders, so `σ`/`φ` are fixed
here; statement-level binders extend them (built on top). Expression *results*
(`EResult`: values + state) contain no environment keys, so a renaming leaves
them unchanged — the bisimulation target produces the identical `EResult`. -/

variable {Op : Type}

mutual
inductive AlphaExpr (σ φ : Ident → Ident) : Expr Op → Expr Op → Prop
  | lit {l} : AlphaExpr σ φ (.lit l) (.lit l)
  | var {x} : AlphaExpr σ φ (.var x) (.var (σ x))
  | builtin {op as₁ as₂} : AlphaArgs σ φ as₁ as₂ → AlphaExpr σ φ (.builtin op as₁) (.builtin op as₂)
  | call {fn as₁ as₂} : AlphaArgs σ φ as₁ as₂ → AlphaExpr σ φ (.call fn as₁) (.call (φ fn) as₂)
inductive AlphaArgs (σ φ : Ident → Ident) : List (Expr Op) → List (Expr Op) → Prop
  | nil : AlphaArgs σ φ [] []
  | cons {e₁ e₂ r₁ r₂} :
      AlphaExpr σ φ e₁ e₂ → AlphaArgs σ φ r₁ r₂ → AlphaArgs σ φ (e₁ :: r₁) (e₂ :: r₂)
end

/-- α-equivalence of optional initializers (`let` with/without a value). -/
inductive AlphaOExpr (σ φ : Ident → Ident) : Option (Expr Op) → Option (Expr Op) → Prop
  | none : AlphaOExpr σ φ none none
  | some {e₁ e₂} : AlphaExpr σ φ e₁ e₂ → AlphaOExpr σ φ (some e₁) (some e₂)

/-! ### Expression-level forward simulation

Renaming an expression (and its environment) preserves evaluation: the result is
identical. `call` is deferred to the statement-level mutual bisimulation (a call
runs a function body, which is a block). -/

mutual
theorem alphaExpr_fwd {σ φ : Ident → Ident} (hσ : Function.Injective σ)
    {BR : FDecl D → FDecl D → Prop} {funs₁ funs₂ : FunEnv D} (hfuns : RenFunsRel φ BR funs₁ funs₂)
    {e₁ e₂ : Expr D.Op} (hα : AlphaExpr σ φ e₁ e₂)
    {V₁ : VEnv D} {mst : D.State} {r : EResult D} (h : EvalExpr D funs₁ V₁ mst e₁ r) :
    EvalExpr D funs₂ (renVEnv σ V₁) mst e₂ r := by
  cases hα with
  | lit => cases h with | lit => exact Step.lit
  | @var x =>
      cases h with
      | var hv => exact Step.var (by rw [renVEnv_get σ V₁ x (fun p _ hh => hσ hh)]; exact hv)
  | builtin ha =>
      cases h with
      | builtinOk hargs hb => exact Step.builtinOk (alphaArgs_fwd hσ hfuns ha hargs) hb
      | builtinHalt hargs hb => exact Step.builtinHalt (alphaArgs_fwd hσ hfuns ha hargs) hb
      | builtinArgsHalt hargs => exact Step.builtinArgsHalt (alphaArgs_fwd hσ hfuns ha hargs)
  | call ha => sorry
theorem alphaArgs_fwd {σ φ : Ident → Ident} (hσ : Function.Injective σ)
    {BR : FDecl D → FDecl D → Prop} {funs₁ funs₂ : FunEnv D} (hfuns : RenFunsRel φ BR funs₁ funs₂)
    {as₁ as₂ : List (Expr D.Op)} (hα : AlphaArgs σ φ as₁ as₂)
    {V₁ : VEnv D} {mst : D.State} {r : EResult D} (h : EvalArgs D funs₁ V₁ mst as₁ r) :
    EvalArgs D funs₂ (renVEnv σ V₁) mst as₂ r := by
  cases hα with
  | nil => cases h with | argsNil => exact Step.argsNil
  | cons he hr =>
      cases h with
      | argsCons ha hh => exact Step.argsCons (alphaArgs_fwd hσ hfuns hr ha) (alphaExpr_fwd hσ hfuns he hh)
      | argsRestHalt ha => exact Step.argsRestHalt (alphaArgs_fwd hσ hfuns hr ha)
      | argsHeadHalt ha hh =>
          exact Step.argsHeadHalt (alphaArgs_fwd hσ hfuns hr ha) (alphaExpr_fwd hσ hfuns he hh)
end
