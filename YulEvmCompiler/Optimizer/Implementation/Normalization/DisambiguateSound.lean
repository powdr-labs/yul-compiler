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

/-- `x` is not a disambiguation-fresh name (holds for every source identifier in a
well-formed program; the α-relation only relates such source references). -/
def NotFresh (x : Ident) : Prop := ∀ k, x ≠ dsName k

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
  | var {x} : NotFresh x → AlphaExpr σ φ (.var x) (.var (σ x))
  | builtin {op as₁ as₂} : AlphaArgs σ φ as₁ as₂ → AlphaExpr σ φ (.builtin op as₁) (.builtin op as₂)
  | call {fn as₁ as₂} :
      NotFresh fn → AlphaArgs σ φ as₁ as₂ → AlphaExpr σ φ (.call fn as₁) (.call (φ fn) as₂)
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
      (∀ x ∈ vars, NotFresh x) → AlphaExpr σ φ e e' →
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

-- The forward simulation `sim_fwd` is defined at the end of the file, once the
-- `RenCfg` config (injective-on-keys, the satisfiable condition) is in scope.
-- (An earlier version here assumed a globally injective `σ`, which the
-- disambiguation renaming does not satisfy — see `RenCfg`.)

/-! ### Renaming-agreement lemmas

The scope-heavy `Step` cases extend the renaming when a binder is entered. On the
already-bound variables (disjoint from the fresh binder names — Yul's no-shadowing
rule) the extended renaming agrees with the old one, so the environment relation
is preserved. -/

/-- `renVEnv` depends only on the renaming's values at the present keys. -/
theorem renVEnv_congr {σ τ : Ident → Ident} {V : VEnv D} (h : ∀ p ∈ V, σ p.1 = τ p.1) :
    renVEnv σ V = renVEnv τ V :=
  List.map_congr_left (fun p hp => by simp only [h p hp])

/-- Outside the association list's keys, `updRen σ l` agrees with `σ`. -/
theorem updRen_of_not_mem {σ : Ident → Ident} {l : List (Ident × Ident)} {z : Ident}
    (h : ∀ p ∈ l, p.1 ≠ z) : updRen σ l z = σ z := by
  simp only [updRen]
  induction l with
  | nil => rfl
  | cons p rest ih =>
      have hp : ¬ (p.1 = z) := h p (List.mem_cons_self ..)
      simp only [List.find?_cons, hp, decide_false, cond_false]
      exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq))

/-- On a key `z` present in the association list, `updRen σ l z` is the paired value
of the first occurrence. -/
theorem updRen_of_find {σ : Ident → Ident} {l : List (Ident × Ident)} {z : Ident}
    {p : Ident × Ident} (h : l.find? (fun q => q.1 = z) = some p) : updRen σ l z = p.2 := by
  simp only [updRen, h]

/-! ### Boundary renaming: renamed inner prefix over a shared outer suffix

For the *arbitrary-context* `EquivBlock`, the target environment is the source
with only the block's own (freshly-renamed) declarations changed, over an
identical outer suffix. A reference to an outer name is left unchanged by the
renaming and falls through the fresh inner keys to the shared suffix; a reference
to an inner name is renamed and resolves in the inner prefix. -/

/-- `get` distributes over `++`: the first list wins, else the second. -/
theorem VEnv.get_append (A B : VEnv D) (k : Ident) :
    VEnv.get (A ++ B) k = (VEnv.get A k).orElse (fun _ => VEnv.get B k) := by
  simp only [VEnv.get, List.find?_append]
  cases A.find? (fun p => p.1 = k) <;> simp

/-- `get` transport across a boundary renaming. A lookup of `σ x`:
* if `x` is an inner (renamed) key, resolves in the renamed prefix to `x`'s value;
* otherwise `σ x = x` (outer names unrenamed) and, the fresh inner keys being
  disjoint from `x`, falls through to the shared suffix. -/
theorem get_boundary (σ : Ident → Ident) (inner outer : VEnv D) (x : Ident)
    (hinj : ∀ p ∈ inner, σ p.1 = σ x → p.1 = x)
    (hid : VEnv.get inner x = none → σ x = x) :
    VEnv.get (renVEnv σ inner ++ outer) (σ x) = VEnv.get (inner ++ outer) x := by
  rw [VEnv.get_append, VEnv.get_append, renVEnv_get σ inner x hinj]
  cases hgi : VEnv.get inner x with
  | some v => simp
  | none => simp [hid hgi]

/-- `set` over `++`: an in-place update hits the first list if the key occurs
there, otherwise the second (mirrors `VEnv.set`'s first-match, no-op-if-absent
behavior). The building block for boundary `set` transport. -/
theorem VEnv.set_append (A B : VEnv D) (k : Ident) (v : D.Value) :
    VEnv.set (A ++ B) k v =
      if (A.find? (fun p => p.1 = k)).isSome then VEnv.set A k v ++ B else A ++ VEnv.set B k v := by
  induction A with
  | nil => simp [VEnv.set]
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      by_cases hyk : y = k
      · simp [VEnv.set, List.find?_cons, hyk]
      · simp only [List.cons_append, VEnv.set, if_neg hyk, List.find?_cons, hyk,
          decide_false, cond_false, ih]
        cases (rest.find? (fun p => p.1 = k)).isSome <;> simp

/-- `set` is a no-op when the key is absent. -/
theorem VEnv.set_of_find_none (V : VEnv D) (k : Ident) (v : D.Value)
    (h : V.find? (fun p => p.1 = k) = none) : VEnv.set V k v = V := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      rw [List.find?_cons] at h
      by_cases hyk : y = k
      · simp [hyk] at h
      · simp only [VEnv.set, if_neg hyk]
        rw [ih (by simpa only [hyk, decide_false, cond_false] using h)]

theorem VEnv.get_eq_none_iff_find (V : VEnv D) (k : Ident) :
    VEnv.get V k = none ↔ V.find? (fun p => p.1 = k) = none := by
  simp only [VEnv.get, Option.map_eq_none_iff]

/-- `set` transport across a boundary renaming when `x` is an **inner** key: the
update hits the renamed prefix (searched first), leaving the shared outer suffix
untouched — no freshness-vs-outer condition needed, since the prefix wins even if
the fresh key coincides with an outer key. This is exactly what preserves the
boundary form for an `assign`/`set` to a block-local variable. -/
theorem set_boundary_hit (σ : Ident → Ident) (inner outer : VEnv D) (x : Ident) (v : D.Value)
    (hinj : ∀ p ∈ inner, σ p.1 = σ x → p.1 = x) (hx : VEnv.get inner x ≠ none) :
    VEnv.set (renVEnv σ inner ++ outer) (σ x) v = renVEnv σ (VEnv.set inner x v) ++ outer := by
  have hget : VEnv.get (renVEnv σ inner) (σ x) = VEnv.get inner x := renVEnv_get σ inner x hinj
  rw [VEnv.set_append, if_pos, renVEnv_set σ inner x v hinj]
  exact Option.isSome_iff_ne_none.mpr
    (fun hc => hx (hget ▸ (VEnv.get_eq_none_iff_find _ _).mpr hc))

/-- `set` transport when `x` is **not** an inner key: `σ x = x` and the update
falls through the fresh prefix (which lacks `x`) to the shared outer suffix. -/
theorem set_boundary_miss (σ : Ident → Ident) (inner outer : VEnv D) (x : Ident) (v : D.Value)
    (hinj : ∀ p ∈ inner, σ p.1 = σ x → p.1 = x)
    (hx : VEnv.get inner x = none) (hid : σ x = x) :
    VEnv.set (renVEnv σ inner ++ outer) (σ x) v = renVEnv σ inner ++ VEnv.set outer x v := by
  have hget : VEnv.get (renVEnv σ inner) (σ x) = VEnv.get inner x := renVEnv_get σ inner x hinj
  have hrn : (renVEnv σ inner).find? (fun p => p.1 = σ x) = none :=
    (VEnv.get_eq_none_iff_find _ _).mp (hget.trans hx)
  rw [VEnv.set_append, if_neg (by rw [hrn]; simp), hid]

/-- A block/scope exit (`restore`) drops exactly the bindings it introduced,
returning to the entry environment. Both source and target satisfy this at their
respective (equal-length) boundaries, so the boundary relation is preserved. -/
theorem restore_prefix (A E : VEnv D) : restore A (E ++ A) = A := by
  have hd : (E ++ A).drop E.length = A := by
    induction E with
    | nil => simp
    | cons e rest ih => simpa using ih
  simp only [restore, List.length_append, Nat.add_sub_cancel, hd]

/-! ### Fresh-name disjointness (no `String` internals)

A source identifier is "not fresh" iff it is not any `dsName`. Under
well-formedness every identifier in the source program is not fresh, while every
renamed (inner) key is a `dsName` — so a lookup of an outer source name never
collides with a renamed inner key, discharging the boundary `get`/`set` no-merge
obligation for outer references. -/

/-- Fresh names really are fresh. -/
theorem not_notFresh_dsName (k : Nat) : ¬ NotFresh (dsName k) := fun h => h k rfl

/-- Every `freshVars` entry is some `dsName`. -/
theorem freshVars_isFresh {n : Nat} {vars : List Ident} {v : Ident}
    (h : v ∈ freshVars n vars) : ∃ k, v = dsName k := by
  induction vars generalizing n with
  | nil => simp [freshVars] at h
  | cons a rest ih =>
      rw [freshVars] at h
      rcases List.mem_cons.mp h with h1 | h2
      · exact ⟨n, h1⟩
      · exact ih h2

/-- A not-fresh name differs from any fresh name. -/
theorem notFresh_ne_dsName {x : Ident} (hx : NotFresh x) (k : Nat) : x ≠ dsName k := hx k

/-! ### The boundary config and its lookup interface

`RenCfg σ inner`: the renaming `σ` is injective on the inner (program-declared)
keys, is the identity below the boundary, and maps every inner key to a fresh
`dsName`. From it we derive the per-lookup no-merge hypotheses that `get_boundary`
/`set_boundary_*` require, for any not-fresh (source) name. -/

def RenCfg (σ : Ident → Ident) (inner : VEnv D) : Prop :=
  (∀ p ∈ inner, ∀ q ∈ inner, σ p.1 = σ q.1 → p.1 = q.1) ∧
  (∀ z, VEnv.get inner z = none → σ z = z) ∧
  (∀ p ∈ inner, ∃ k, σ p.1 = dsName k)

/-- The `get_boundary`/`renVEnv_get` no-merge condition for a not-fresh name `x`:
no inner key renames onto `σ x`. -/
theorem RenCfg.no_merge {σ : Ident → Ident} {inner : VEnv D} (h : RenCfg σ inner)
    {x : Ident} (hx : NotFresh x) : ∀ p ∈ inner, σ p.1 = σ x → p.1 = x := by
  intro p hp hpq
  by_cases hxi : VEnv.get inner x = none
  · obtain ⟨k, hk⟩ := h.2.2 p hp
    rw [h.2.1 x hxi, hk] at hpq
    exact absurd hpq.symm (hx k)
  · have hne : inner.find? (fun q => q.1 = x) ≠ none :=
      fun hc => hxi ((VEnv.get_eq_none_iff_find _ _).mpr hc)
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hne
    have hqmem : q ∈ inner := List.mem_of_find?_eq_some hq
    have hqx : q.1 = x := by simpa using List.find?_some hq
    rw [← hqx] at hpq ⊢
    exact h.1 p hp q hqmem hpq

/-- `σ x = x` for a not-fresh name absent from the inner prefix. -/
theorem RenCfg.id_at {σ : Ident → Ident} {inner : VEnv D} (h : RenCfg σ inner)
    {x : Ident} (hxi : VEnv.get inner x = none) : σ x = x := h.2.1 x hxi

/-- `get` transport at the boundary for a not-fresh name. -/
theorem RenCfg.get {σ : Ident → Ident} {inner : VEnv D} (h : RenCfg σ inner)
    (outer : VEnv D) {x : Ident} (hx : NotFresh x) :
    VEnv.get (renVEnv σ inner ++ outer) (σ x) = VEnv.get (inner ++ outer) x :=
  get_boundary σ inner outer x (h.no_merge hx) (fun hn => h.id_at hn)

/-! ### `setMany` transport under injectivity-on-keys (not global)

The disambiguation renaming is injective only on the in-scope keys, not globally,
so the multi-assignment transport is re-based onto a per-key no-merge condition
(`VEnv.set` preserves keys, so the condition threads through the fold). -/

theorem VEnv.set_keys (V : VEnv D) (x : Ident) (v : D.Value) :
    (VEnv.set V x v).map Prod.fst = V.map Prod.fst := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      by_cases hyx : y = x
      · simp [VEnv.set, hyx]
      · simp only [VEnv.set, if_neg hyx, List.map_cons, ih]

theorem renVEnv_setMany_dom (σ : Ident → Ident) :
    ∀ (vars : List Ident) (vals : List D.Value) (V : VEnv D),
      (∀ x ∈ vars, ∀ k ∈ V.map Prod.fst, σ k = σ x → k = x) →
      VEnv.setMany (renVEnv σ V) (vars.map σ) vals = renVEnv σ (VEnv.setMany V vars vals) := by
  intro vars
  induction vars with
  | nil => intro vals V _; simp [VEnv.setMany]
  | cons x xs ih =>
      intro vals V hnm
      cases vals with
      | nil => simp [VEnv.setMany]
      | cons v vs =>
          have hx : ∀ p ∈ V, σ p.1 = σ x → p.1 = x := fun p hp =>
            hnm x (List.mem_cons_self ..) p.1 (List.mem_map_of_mem hp)
          rw [List.map_cons, VEnv.setMany_cons, VEnv.setMany_cons, renVEnv_set σ V x v hx]
          refine ih vs (VEnv.set V x v) (fun y hy k hk => ?_)
          rw [VEnv.set_keys] at hk
          exact hnm y (List.mem_cons_of_mem _ hy) k hk

/-! ### RenCfg preservation (keys-only dependence)

`RenCfg` depends only on the environment's key-set, which `set`/`setMany`
preserve — so it survives an assignment. -/

theorem VEnv.get_eq_none_iff_not_mem (V : VEnv D) (z : Ident) :
    VEnv.get V z = none ↔ z ∉ V.map Prod.fst := by
  induction V with
  | nil => simp [VEnv.get]
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      by_cases hyz : y = z
      · subst hyz; simp [VEnv.get]
      · have hzy : (z = y) = False := eq_false (fun h => hyz h.symm)
        simp only [VEnv.get, List.find?_cons, hyz, decide_false, cond_false, List.map_cons,
          List.mem_cons, hzy, false_or]
        exact ih

theorem VEnv.setMany_keys (V : VEnv D) (xs : List Ident) (vs : List D.Value) :
    (VEnv.setMany V xs vs).map Prod.fst = V.map Prod.fst := by
  induction xs generalizing V vs with
  | nil => simp [VEnv.setMany]
  | cons x xs ih =>
      cases vs with
      | nil => simp [VEnv.setMany]
      | cons v vs => rw [VEnv.setMany_cons, ih, VEnv.set_keys]

theorem RenCfg.of_keys {σ : Ident → Ident} {V V' : VEnv D}
    (hk : V'.map Prod.fst = V.map Prod.fst) (h : RenCfg σ V) : RenCfg σ V' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro p hp q hq hpq
    have hp' : p.1 ∈ V.map Prod.fst := hk ▸ List.mem_map_of_mem hp
    have hq' : q.1 ∈ V.map Prod.fst := hk ▸ List.mem_map_of_mem hq
    obtain ⟨p₀, hp₀, hp₀e⟩ := List.mem_map.mp hp'
    obtain ⟨q₀, hq₀, hq₀e⟩ := List.mem_map.mp hq'
    rw [← hp₀e, ← hq₀e] at hpq ⊢
    exact h1 p₀ hp₀ q₀ hq₀ hpq
  · intro z hz
    exact h2 z ((VEnv.get_eq_none_iff_not_mem V z).mpr
      (fun hc => (VEnv.get_eq_none_iff_not_mem V' z).mp hz (hk ▸ hc)))
  · intro p hp
    obtain ⟨p₀, hp₀, hp₀e⟩ := List.mem_map.mp (hk ▸ List.mem_map_of_mem hp : p.1 ∈ V.map Prod.fst)
    rw [← hp₀e]; exact h3 p₀ hp₀

theorem RenCfg.setMany {σ : Ident → Ident} {V : VEnv D} (h : RenCfg σ V)
    (xs : List Ident) (vs : List D.Value) : RenCfg σ (VEnv.setMany V xs vs) :=
  RenCfg.of_keys (VEnv.setMany_keys V xs vs) h

/-! ### Forward simulation (on the `RenCfg` foundation)

Whole-environment form (`outer = []`), the shape needed for whole-program
`Run`-equivalence: every in-scope variable is a program variable, renamed by `σ`.
`ResOK σ'` carries `RenCfg σ'` on a statement result so it threads to the
continuation. Expression / argument / simple-statement cases are proven; the
scope-heavy cases are isolated in the final catch-all branch. -/

def ResOK (σ' : Ident → Ident) : Res D → Prop
  | .eres _ => True
  | .sres V _ _ => RenCfg σ' V

theorem sim_fwd {funs₁ : FunEnv D} {V₁ mst code₁ res₁} (h : Step D funs₁ V₁ mst code₁ res₁) :
    ∀ {σ φ σ' φ' funs₂ code₂}, RenCfg σ V₁ → Function.Injective φ →
      RenFunsRel φ (FDeclRen φ) funs₁ funs₂ → AlphaCode σ φ σ' φ' code₁ code₂ →
      Step D funs₂ (renVEnv σ V₁) mst code₂ (renRes σ' res₁) ∧ ResOK σ' res₁ := by
  induction h with
  | @lit funs V st l =>
      intro σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hcode
      cases hcode with | expr hae => cases hae; exact ⟨Step.lit, trivial⟩
  | @var funs V st x v hv =>
      intro σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hcode
      cases hcode with | expr hae => cases hae with | var hx =>
          exact ⟨Step.var (by rw [renVEnv_get σ V x (hcfg.no_merge hx)]; exact hv), trivial⟩
  | @builtinOk funs V st op args argvals st1 rets st2 ha hb iha =>
      intro σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hcode
      cases hcode with | expr hae => cases hae with | builtin ha2 =>
          exact ⟨Step.builtinOk (iha hcfg hφ hfuns (.args ha2)).1 hb, trivial⟩
  | @builtinHalt funs V st op args argvals st1 st2 ha hb iha =>
      intro σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hcode
      cases hcode with | expr hae => cases hae with | builtin ha2 =>
          exact ⟨Step.builtinHalt (iha hcfg hφ hfuns (.args ha2)).1 hb, trivial⟩
  | @builtinArgsHalt funs V st op args st1 ha iha =>
      intro σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hcode
      cases hcode with | expr hae => cases hae with | builtin ha2 =>
          exact ⟨Step.builtinArgsHalt (iha hcfg hφ hfuns (.args ha2)).1, trivial⟩
  | @callArgsHalt funs V st fn args st1 ha iha =>
      intro σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hcode
      cases hcode with | expr hae => cases hae with | call hfn ha2 =>
          exact ⟨Step.callArgsHalt (iha hcfg hφ hfuns (.args ha2)).1, trivial⟩
  | @argsNil funs V st =>
      intro σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hcode
      cases hcode with | args hae => cases hae; exact ⟨Step.argsNil, trivial⟩
  | @argsCons funs V st e rest restvals st1 v st2 hrest he ihrest ihe =>
      intro σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hcode
      cases hcode with | args hae => cases hae with | cons he2 hr2 =>
          exact ⟨Step.argsCons (ihrest hcfg hφ hfuns (.args hr2)).1
            (ihe hcfg hφ hfuns (.expr he2)).1, trivial⟩
  | @argsRestHalt funs V st e rest st1 hrest ihrest =>
      intro σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hcode
      cases hcode with | args hae => cases hae with | cons he2 hr2 =>
          exact ⟨Step.argsRestHalt (ihrest hcfg hφ hfuns (.args hr2)).1, trivial⟩
  | @argsHeadHalt funs V st e rest restvals st1 st2 hrest he ihrest ihe =>
      intro σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hcode
      cases hcode with | args hae => cases hae with | cons he2 hr2 =>
          exact ⟨Step.argsHeadHalt (ihrest hcfg hφ hfuns (.args hr2)).1
            (ihe hcfg hφ hfuns (.expr he2)).1, trivial⟩
  | @funDef funs V st n ps rs b =>
      intro σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hcode
      cases hcode with | stmt hs => cases hs with | funD _ => exact ⟨Step.funDef, hcfg⟩
  | @«break» funs V st =>
      intro σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hcode
      cases hcode with | stmt hs => cases hs with | breakD => exact ⟨Step.break, hcfg⟩
  | @«continue» funs V st =>
      intro σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hcode
      cases hcode with | stmt hs => cases hs with | contD => exact ⟨Step.continue, hcfg⟩
  | @leave funs V st =>
      intro σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hcode
      cases hcode with | stmt hs => cases hs with | leaveD => exact ⟨Step.leave, hcfg⟩
  | @seqNil funs V st =>
      intro σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hcode
      cases hcode with | stmts hs => cases hs with | nil => exact ⟨Step.seqNil, hcfg⟩
  | @exprStmt funs V st e st1 he ihe =>
      intro σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hcode
      cases hcode with | stmt hs => cases hs with | exprD he2 =>
          exact ⟨Step.exprStmt (ihe hcfg hφ hfuns (.expr he2)).1, hcfg⟩
  | @exprStmtHalt funs V st e st1 he ihe =>
      intro σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hcode
      cases hcode with | stmt hs => cases hs with | exprD he2 =>
          exact ⟨Step.exprStmtHalt (ihe hcfg hφ hfuns (.expr he2)).1, hcfg⟩
  | @assignVal funs V st vars e vals st1 he hlen ihe =>
      intro σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hcode
      cases hcode with | stmt hs => cases hs with | assignD hvars he2 =>
          have hnm : ∀ x ∈ vars, ∀ k ∈ V.map Prod.fst, σ k = σ x → k = x := by
            intro x hx k hk hkeq
            obtain ⟨p, hp, hpk⟩ := List.mem_map.mp hk
            subst hpk
            exact hcfg.no_merge (hvars x hx) p hp hkeq
          refine ⟨?_, RenCfg.setMany hcfg vars vals⟩
          simp only [renRes]
          rw [← renVEnv_setMany_dom σ vars vals V hnm]
          exact Step.assignVal (ihe hcfg hφ hfuns (.expr he2)).1 (by rw [List.length_map]; exact hlen)
  | @assignHalt funs V st vars e st1 he ihe =>
      intro σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hcode
      cases hcode with | stmt hs => cases hs with | assignD hvars he2 =>
          exact ⟨Step.assignHalt (ihe hcfg hφ hfuns (.expr he2)).1, hcfg⟩
  | @ifHalt funs V st c body st1 hc ihc =>
      intro σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hcode
      cases hcode with | stmt hs => cases hs with | condD hc2 hb2 =>
          exact ⟨Step.ifHalt (ihc hcfg hφ hfuns (.expr hc2)).1, hcfg⟩
  | @switchHalt funs V st c cs dflt st1 hc ihc =>
      intro σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hcode
      cases hcode with | stmt hs => cases hs with | switchD hc2 hcs2 hd2 =>
          exact ⟨Step.switchHalt (ihc hcfg hφ hfuns (.expr hc2)).1, hcfg⟩
  | @loopCondHalt funs V st c post body st1 hc ihc =>
      intro σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hcode
      cases hcode with | loop hc2 hb2 hp2 =>
          exact ⟨Step.loopCondHalt (ihc hcfg hφ hfuns (.expr hc2)).1, hcfg⟩
  | @loopDone funs V st c post body cv st1 hc hz ihc =>
      intro σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hcode
      cases hcode with | loop hc2 hb2 hp2 =>
          exact ⟨Step.loopDone (ihc hcfg hφ hfuns (.expr hc2)).1 hz, hcfg⟩
  | _ => intro σ φ σ' φ' funs₂ code₂ hcfg hφ hfuns hcode; sorry
