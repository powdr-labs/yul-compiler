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


/-! ### α-equivalence: statements

Statement-level α-equivalence threads the renamings through binders. `AlphaSeqExt
σ φ ss₁ ss₂ σ' φ'` relates a source sequence to its renaming and reports the
renamings `σ'`/`φ'` in force after the sequence's declarations (a `for`-loop's
`init` needs them for its condition/body/post). A block/`init` first prescans its
top-level function names into `φ` (Yul's forward visibility), via `AlphaBlockExt`. -/

/-- Extend a renaming with an association list (later lookups shadow `σ`). -/
def updRen (σ : Ident → Ident) (l : List (Ident × Ident)) : Ident → Ident :=
  fun z => match l.find? (fun p => p.1 = z) with
    | some p => p.2
    | none => σ z

mutual
/-- Single-statement α-equivalence, reporting the renamings after the statement's
declarations (only `let` extends `σ`; `funDef` names are prescanned into `φ`). -/
inductive AlphaStmt1 :
    (Ident → Ident) → (Ident → Ident) → Stmt Op → Stmt Op →
    (Ident → Ident) → (Ident → Ident) → Prop
  | letD {σ φ vars vars' eo eo'} :
      AlphaOExpr σ φ eo eo' →
      AlphaStmt1 σ φ (.letDecl vars eo) (.letDecl vars' eo') (updRen σ (vars.zip vars')) φ
  | assignD {σ φ vars e e'} :
      AlphaExpr σ φ e e' →
      AlphaStmt1 σ φ (.assign vars e) (.assign (vars.map σ) e') σ φ
  | exprD {σ φ e e'} :
      AlphaExpr σ φ e e' → AlphaStmt1 σ φ (.exprStmt e) (.exprStmt e') σ φ
  | funD {σ φ fn ps ps' rs rs' body body' σb φb} :
      AlphaBlockExt (updRen σ (ps.zip ps' ++ rs.zip rs')) φ body body' σb φb →
      AlphaStmt1 σ φ (.funDef fn ps rs body) (.funDef (φ fn) ps' rs' body') σ φ
  | blockD {σ φ body body' σb φb} :
      AlphaBlockExt σ φ body body' σb φb → AlphaStmt1 σ φ (.block body) (.block body') σ φ
  | condD {σ φ c c' body body' σb φb} :
      AlphaExpr σ φ c c' → AlphaBlockExt σ φ body body' σb φb →
      AlphaStmt1 σ φ (.cond c body) (.cond c' body') σ φ
  | switchD {σ φ c c' cases cases' dflt dflt'} :
      AlphaExpr σ φ c c' → AlphaCases σ φ cases cases' → AlphaDflt σ φ dflt dflt' →
      AlphaStmt1 σ φ (.switch c cases dflt) (.switch c' cases' dflt') σ φ
  | forD {σ φ init init' c c' post post' body body' σi φi σb φb σp φp} :
      AlphaBlockExt σ φ init init' σi φi →
      AlphaExpr σi φi c c' →
      AlphaBlockExt σi φi body body' σb φb →
      AlphaBlockExt σi φi post post' σp φp →
      AlphaStmt1 σ φ (.forLoop init c post body) (.forLoop init' c' post' body') σ φ
  | breakD {σ φ} : AlphaStmt1 σ φ .break .break σ φ
  | contD {σ φ} : AlphaStmt1 σ φ .continue .continue σ φ
  | leaveD {σ φ} : AlphaStmt1 σ φ .leave .leave σ φ
inductive AlphaSeqExt :
    (Ident → Ident) → (Ident → Ident) → List (Stmt Op) → List (Stmt Op) →
    (Ident → Ident) → (Ident → Ident) → Prop
  | nil {σ φ} : AlphaSeqExt σ φ [] [] σ φ
  | cons {σ φ s s' rest rest' σ' φ' σ'' φ''} :
      AlphaStmt1 σ φ s s' σ' φ' → AlphaSeqExt σ' φ' rest rest' σ'' φ'' →
      AlphaSeqExt σ φ (s :: rest) (s' :: rest') σ'' φ''
inductive AlphaBlockExt :
    (Ident → Ident) → (Ident → Ident) → List (Stmt Op) → List (Stmt Op) →
    (Ident → Ident) → (Ident → Ident) → Prop
  | mk {σ φ : Ident → Ident} {b₁ b₂ : List (Stmt Op)} {σ' φ' : Ident → Ident} :
      AlphaSeqExt σ (updRen φ ((funNames b₁).zip (funNames b₂))) b₁ b₂ σ' φ' →
      AlphaBlockExt σ φ b₁ b₂ σ' φ'
inductive AlphaCases :
    (Ident → Ident) → (Ident → Ident) →
    List (Literal × List (Stmt Op)) → List (Literal × List (Stmt Op)) → Prop
  | nil {σ φ} : AlphaCases σ φ [] []
  | cons {σ φ l body body' rest rest' σb φb} :
      AlphaBlockExt σ φ body body' σb φb → AlphaCases σ φ rest rest' →
      AlphaCases σ φ ((l, body) :: rest) ((l, body') :: rest')
inductive AlphaDflt :
    (Ident → Ident) → (Ident → Ident) →
    Option (List (Stmt Op)) → Option (List (Stmt Op)) → Prop
  | none {σ φ} : AlphaDflt σ φ none none
  | some {σ φ body body' σb φb} :
      AlphaBlockExt σ φ body body' σb φb → AlphaDflt σ φ (some body) (some body')
end

/-! ### The forward bisimulation

`renRes σ'` renames a statement result's environment by the post-renaming `σ'`
(expression results carry no keys, so are untouched). `AlphaCode` bundles the
per-class α-relation with the reported post-renamings, so a single `Step`
induction can range over every code class. `FDeclRen φ` is the body relation
carried in the function environment: a callee's params/rets are renamed by an
injective `σc` and its body is α-equivalent under `σc`/`φ`. -/

/-- Rename a result's environment by `σ'` (expression results are unchanged). -/
def renRes (σ' : Ident → Ident) : Res D → Res D
  | .eres r => .eres r
  | .sres V st o => .sres (renVEnv σ' V) st o

/-- Function-declaration renaming: params/rets renamed by an injective `σc`,
body α-equivalent under `σc` (variables) and `φ` (functions). -/
def FDeclRen (φ : Ident → Ident) (d₁ d₂ : FDecl D) : Prop :=
  ∃ σc σc' φc', Function.Injective σc ∧
    d₂.params = d₁.params.map σc ∧ d₂.rets = d₁.rets.map σc ∧
    AlphaBlockExt σc φ d₁.body d₂.body σc' φc'

/-- α-relation on `Code`, carrying input and post renamings. -/
inductive AlphaCode :
    (Ident → Ident) → (Ident → Ident) → (Ident → Ident) → (Ident → Ident) →
    Code D.Op → Code D.Op → Prop
  | expr {σ φ e₁ e₂} : AlphaExpr σ φ e₁ e₂ → AlphaCode σ φ σ φ (.expr e₁) (.expr e₂)
  | args {σ φ a₁ a₂} : AlphaArgs σ φ a₁ a₂ → AlphaCode σ φ σ φ (.args a₁) (.args a₂)
  | stmt {σ φ s₁ s₂ σ' φ'} : AlphaStmt1 σ φ s₁ s₂ σ' φ' → AlphaCode σ φ σ' φ' (.stmt s₁) (.stmt s₂)
  | stmts {σ φ ss₁ ss₂ σ' φ'} :
      AlphaSeqExt σ φ ss₁ ss₂ σ' φ' → AlphaCode σ φ σ' φ' (.stmts ss₁) (.stmts ss₂)
  | loop {σ φ c₁ c₂ p₁ p₂ b₁ b₂ σb φb σp φp} :
      AlphaExpr σ φ c₁ c₂ → AlphaBlockExt σ φ b₁ b₂ σb φb → AlphaBlockExt σ φ p₁ p₂ σp φp →
      AlphaCode σ φ σ φ (.loop c₁ p₁ b₁) (.loop c₂ p₂ b₂)

/-- **Forward simulation.** A source `Step` transports to the renamed program,
with the result renamed by the post-renaming. Expression, argument, and simple
statement cases are proven; the scope-heavy cases (block/call/for/if/switch/seq)
are being filled in, isolated in the final catch-all branch. -/
theorem sim_fwd {funs₁ : FunEnv D} {V₁ mst code₁ res₁} (h : Step D funs₁ V₁ mst code₁ res₁) :
    ∀ {σ φ σ' φ' funs₂ code₂}, Function.Injective σ → Function.Injective φ →
      RenFunsRel φ (FDeclRen φ) funs₁ funs₂ → AlphaCode σ φ σ' φ' code₁ code₂ →
      Step D funs₂ (renVEnv σ V₁) mst code₂ (renRes σ' res₁) := by
  induction h with
  | @lit funs V st l =>
      intro σ φ σ' φ' funs₂ code₂ hσ hφ hfuns hcode
      cases hcode with | expr hae => cases hae; exact Step.lit
  | @var funs V st x v hv =>
      intro σ φ σ' φ' funs₂ code₂ hσ hφ hfuns hcode
      cases hcode with
      | expr hae => cases hae with | var =>
          exact Step.var (by rw [renVEnv_get σ V x (fun p _ hh => hσ hh)]; exact hv)
  | @builtinOk funs V st op args argvals st1 rets st2 ha hb iha =>
      intro σ φ σ' φ' funs₂ code₂ hσ hφ hfuns hcode
      cases hcode with | expr hae => cases hae with | builtin ha2 =>
          exact Step.builtinOk (iha hσ hφ hfuns (.args ha2)) hb
  | @builtinHalt funs V st op args argvals st1 st2 ha hb iha =>
      intro σ φ σ' φ' funs₂ code₂ hσ hφ hfuns hcode
      cases hcode with | expr hae => cases hae with | builtin ha2 =>
          exact Step.builtinHalt (iha hσ hφ hfuns (.args ha2)) hb
  | @builtinArgsHalt funs V st op args st1 ha iha =>
      intro σ φ σ' φ' funs₂ code₂ hσ hφ hfuns hcode
      cases hcode with | expr hae => cases hae with | builtin ha2 =>
          exact Step.builtinArgsHalt (iha hσ hφ hfuns (.args ha2))
  | @callArgsHalt funs V st fn args st1 ha iha =>
      intro σ φ σ' φ' funs₂ code₂ hσ hφ hfuns hcode
      cases hcode with | expr hae => cases hae with | call ha2 =>
          exact Step.callArgsHalt (iha hσ hφ hfuns (.args ha2))
  | @argsNil funs V st =>
      intro σ φ σ' φ' funs₂ code₂ hσ hφ hfuns hcode
      cases hcode with | args hae => cases hae; exact Step.argsNil
  | @argsCons funs V st e rest restvals st1 v st2 hrest he ihrest ihe =>
      intro σ φ σ' φ' funs₂ code₂ hσ hφ hfuns hcode
      cases hcode with | args hae => cases hae with | cons he2 hr2 =>
          exact Step.argsCons (ihrest hσ hφ hfuns (.args hr2)) (ihe hσ hφ hfuns (.expr he2))
  | @argsRestHalt funs V st e rest st1 hrest ihrest =>
      intro σ φ σ' φ' funs₂ code₂ hσ hφ hfuns hcode
      cases hcode with | args hae => cases hae with | cons he2 hr2 =>
          exact Step.argsRestHalt (ihrest hσ hφ hfuns (.args hr2))
  | @argsHeadHalt funs V st e rest restvals st1 st2 hrest he ihrest ihe =>
      intro σ φ σ' φ' funs₂ code₂ hσ hφ hfuns hcode
      cases hcode with | args hae => cases hae with | cons he2 hr2 =>
          exact Step.argsHeadHalt (ihrest hσ hφ hfuns (.args hr2)) (ihe hσ hφ hfuns (.expr he2))
  | @funDef funs V st n ps rs b =>
      intro σ φ σ' φ' funs₂ code₂ hσ hφ hfuns hcode
      cases hcode with | stmt hs => cases hs with | funD _ => exact Step.funDef
  | @«break» funs V st =>
      intro σ φ σ' φ' funs₂ code₂ hσ hφ hfuns hcode
      cases hcode with | stmt hs => cases hs with | breakD => exact Step.break
  | @«continue» funs V st =>
      intro σ φ σ' φ' funs₂ code₂ hσ hφ hfuns hcode
      cases hcode with | stmt hs => cases hs with | contD => exact Step.continue
  | @leave funs V st =>
      intro σ φ σ' φ' funs₂ code₂ hσ hφ hfuns hcode
      cases hcode with | stmt hs => cases hs with | leaveD => exact Step.leave
  | @seqNil funs V st =>
      intro σ φ σ' φ' funs₂ code₂ hσ hφ hfuns hcode
      cases hcode with | stmts hs => cases hs with | nil => exact Step.seqNil
  | _ => intro σ φ σ' φ' funs₂ code₂ hσ hφ hfuns hcode; sorry
