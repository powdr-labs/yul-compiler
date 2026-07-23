import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate
import YulEvmCompiler.Optimizer.Implementation.Normalization.NormalForm
/-!
# Disambiguation α-equivalence (syntax only)

The renaming relation the disambiguation bisimulation ranges over, together with
its purely syntactic lemmas. Nothing semantic lives here — this file depends only
on the AST, the pass (`dsName`/`freshVars`/`funNames`), and the shared
`NormalForm` scoping predicates — so it compiles fast and the semantic layers
(`DisambiguateRen`, `DisambiguateSound`) build on top of its olean.

Contents:
* `NotFresh` and fresh-name disjointness lemmas;
* `updRen`, extending a renaming by an association list, with lookup lemmas;
* `AlphaExpr`/`AlphaArgs`/`AlphaOExpr` — expression α-equivalence under a
  variable renaming `σ` and a function renaming `φ`;
* `AlphaStmt1`/`AlphaSeqExt`/`AlphaBlockExt`/`AlphaCases`/`AlphaDflt` —
  statement α-equivalence, threading binder extensions and the per-block
  function-name prescan;
* `WScoped*`/`FScoped*` — source no-shadowing (variables / functions);
* φ-congruence: the α-relations depend on `φ` only at the *referenced* function
  names, so a `φ` that agrees on the visible functions relates the same pair.

The freshness side conditions are deliberately restricted to `NotFresh`
arguments: the pass's renaming is the identity on fresh (`dsName`) inputs, so an
unrestricted `∀ z, σ z ≠ v'` would be unsatisfiable at `z = v'`.
-/

namespace YulEvmCompiler.Optimizer.Normalize

open YulSemantics

variable {Op : Type}

/-- `x` is not a disambiguation-fresh name (holds for every source identifier in a
well-formed program; the α-relation only relates such source references). -/
def NotFresh (x : Ident) : Prop := ∀ k, x ≠ dsName k

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

/-! ### Extending a renaming -/

/-- Extend a renaming with an association list (later lookups shadow `σ`). -/
def updRen (σ : Ident → Ident) (l : List (Ident × Ident)) : Ident → Ident :=
  fun z => match l.find? (fun p => p.1 = z) with
    | some p => p.2
    | none => σ z

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

theorem updRen_cons_eq (σ : Ident → Ident) (a b : Ident) (l : List (Ident × Ident)) :
    updRen σ ((a, b) :: l) a = b := by simp [updRen, List.find?_cons]

theorem updRen_cons_ne {σ : Ident → Ident} {a b z : Ident} {l : List (Ident × Ident)}
    (h : a ≠ z) : updRen σ ((a, b) :: l) z = updRen σ l z := by
  simp [updRen, List.find?_cons, h]

/-- A lookup past a prefix that doesn't contain the key skips to the suffix. -/
theorem updRen_append_skip {σ : Ident → Ident} {l₁ l₂ : List (Ident × Ident)} {z : Ident}
    (h : ∀ p ∈ l₁, p.1 ≠ z) : updRen σ (l₁ ++ l₂) z = updRen σ l₂ z := by
  have h1 : l₁.find? (fun p => p.1 = z) = none :=
    List.find?_eq_none.mpr (fun p hp => by simpa using h p hp)
  simp [updRen, List.find?_append, h1]

/-- The renaming sends `xs` to `ys`, even with a trailing binding list `tl` (the
lookup of an `xs`-key hits the `xs.zip ys` prefix first). -/
theorem map_updRen_zip_pre {σ : Ident → Ident} (tl : List (Ident × Ident)) :
    ∀ {xs ys : List Ident}, xs.Nodup → xs.length = ys.length →
      xs.map (updRen σ (xs.zip ys ++ tl)) = ys
  | [], [], _, _ => rfl
  | [], _ :: _, _, hlen => by simp at hlen
  | _ :: _, [], _, hlen => by simp at hlen
  | x :: xs, y :: ys, hnd, hlen => by
      have hx : x ∉ xs := (List.nodup_cons.mp hnd).1
      simp only [List.zip_cons_cons, List.cons_append, List.map_cons, updRen_cons_eq]
      have htail : xs.map (updRen σ ((x, y) :: (xs.zip ys ++ tl))) =
          xs.map (updRen σ (xs.zip ys ++ tl)) :=
        List.map_congr_left (fun z hz => updRen_cons_ne (fun heq => hx (heq ▸ hz)))
      rw [htail, map_updRen_zip_pre tl (List.nodup_cons.mp hnd).2 (by simpa using hlen)]

/-- The `let`-extended renaming sends the declared variables to their fresh names. -/
theorem map_updRen_zip {σ : Ident → Ident} {xs ys : List Ident} (hnd : xs.Nodup)
    (hlen : xs.length = ys.length) : xs.map (updRen σ (xs.zip ys)) = ys := by
  have := map_updRen_zip_pre (σ := σ) [] hnd hlen
  simpa using this

/-! ### α-equivalence: expressions

`AlphaExpr σ φ e₁ e₂` says `e₂` is `e₁` with free variable names renamed by `σ`
and free function names by `φ`. Expressions have no binders, so `σ`/`φ` are fixed
here; statement-level binders extend them (built on top). Expression *results*
(`EResult`: values + state) contain no environment keys, so a renaming leaves
them unchanged — the bisimulation target produces the identical `EResult`. -/

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

/-! ### α-relation φ-congruence (expression level)

`AlphaExpr` depends on `φ` only through the function names it *calls*; for a
well-scoped expression those calls resolve in the visible functions `fs`, so a
`φ` that agrees on `fs` relates the same pair. This is what lets a block's
`φ`-extension leave the outer functions' relation intact. Proven by structural
recursion on the *expression* (the relation is `Prop`-valued, so its derivations
carry no size measure to recurse on). -/

mutual
theorem alphaExpr_congr_phi {σ φ φ2 : Ident → Ident} {vs fs : List Ident} :
    ∀ {e e' : Expr Op}, AlphaExpr σ φ e e' → NormalForm.ScopedExpr vs fs e →
      (∀ fn ∈ fs, φ2 fn = φ fn) → AlphaExpr σ φ2 e e'
  | .lit _, _, h, _, _ => by cases h; exact .lit
  | .var _, _, h, _, _ => by cases h with | var hx => exact .var hx
  | .builtin _ as, _, h, hsc, hag => by
      cases h with | builtin ha =>
        exact .builtin (alphaArgs_congr_phi ha hsc hag)
  | .call fn as, _, h, hsc, hag => by
      cases h with | call hfn ha =>
        obtain ⟨hfnmem, hargs⟩ := hsc
        have hc := AlphaExpr.call (σ := σ) (φ := φ2) hfn (alphaArgs_congr_phi ha hargs hag)
        rwa [hag fn hfnmem] at hc
theorem alphaArgs_congr_phi {σ φ φ2 : Ident → Ident} {vs fs : List Ident} :
    ∀ {as as' : List (Expr Op)}, AlphaArgs σ φ as as' → NormalForm.ScopedArgs vs fs as →
      (∀ fn ∈ fs, φ2 fn = φ fn) → AlphaArgs σ φ2 as as'
  | [], _, h, _, _ => by cases h; exact .nil
  | _ :: _, _, h, hsc, hag => by
      cases h with | cons he hr =>
        obtain ⟨hse, hsr⟩ := hsc
        exact .cons (alphaExpr_congr_phi he hse hag) (alphaArgs_congr_phi hr hsr hag)
end

/-- Optional-initializer φ-congruence. -/
theorem alphaOExpr_congr_phi {σ φ φ2 : Ident → Ident} {vs fs : List Ident}
    {eo eo' : Option (Expr Op)} (h : AlphaOExpr σ φ eo eo')
    (hsc : ∀ e, eo = some e → NormalForm.ScopedExpr vs fs e)
    (hag : ∀ fn ∈ fs, φ2 fn = φ fn) : AlphaOExpr σ φ2 eo eo' := by
  cases h with
  | none => exact .none
  | @some e₁ e₂ he => exact .some (alphaExpr_congr_phi he (hsc e₁ rfl) hag)

/-! ### α-equivalence: statements

Statement-level α-equivalence threads the renamings through binders. `AlphaSeqExt
σ φ ss₁ ss₂ σ' φ'` relates a source sequence to its renaming and reports the
renamings `σ'`/`φ'` in force after the sequence's declarations (a `for`-loop's
`init` needs them for its condition/body/post). A block/`init` first prescans its
top-level function names into `φ` (Yul's forward visibility), via `AlphaBlockExt`.

Freshness side conditions are `NotFresh`-restricted (see the module docstring):
* source binders are `NotFresh` (no source identifier is a `dsName`);
* target binders are `dsName`s, pairwise distinct, and distinct from the image
  of any `NotFresh` name under the incoming renaming (fresh-counter discipline).
-/

mutual
/-- Single-statement α-equivalence, reporting the renamings after the statement's
declarations (only `let` extends `σ`; `funDef` names are prescanned into `φ`). -/
inductive AlphaStmt1 :
    (Ident → Ident) → (Ident → Ident) → Stmt Op → Stmt Op →
    (Ident → Ident) → (Ident → Ident) → Prop
  | letD {σ φ vars vars' eo eo'} :
      vars.Nodup → vars'.Nodup → vars.length = vars'.length →
      (∀ x ∈ vars, NotFresh x) →
      (∀ v' ∈ vars', ∃ k, v' = dsName k) →
      (∀ v' ∈ vars', ∀ z, NotFresh z → σ z ≠ v') →
      AlphaOExpr σ φ eo eo' →
      AlphaStmt1 σ φ (.letDecl vars eo) (.letDecl vars' eo') (updRen σ (vars.zip vars')) φ
  | assignD {σ φ vars e e'} :
      (∀ x ∈ vars, NotFresh x) → AlphaExpr σ φ e e' →
      AlphaStmt1 σ φ (.assign vars e) (.assign (vars.map σ) e') σ φ
  | exprD {σ φ e e'} :
      AlphaExpr σ φ e e' → AlphaStmt1 σ φ (.exprStmt e) (.exprStmt e') σ φ
  | funD {σ φ fn ps ps' rs rs' body body' σb φb} :
      (ps ++ rs).Nodup → (ps' ++ rs').Nodup → ps.length = ps'.length → rs.length = rs'.length →
      (∀ x ∈ ps ++ rs, NotFresh x) →
      (∀ v' ∈ ps' ++ rs', ∃ k, v' = dsName k) →
      AlphaBlockExt (updRen id (ps.zip ps' ++ rs.zip rs')) φ body body' σb φb →
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
      (funNames b₁).Nodup → (funNames b₁).length = (funNames b₂).length → (funNames b₂).Nodup →
      (∀ x ∈ funNames b₁, NotFresh x) →
      (∀ v' ∈ funNames b₂, ∃ k, v' = dsName k) →
      (∀ v' ∈ funNames b₂, ∀ z, NotFresh z → φ z ≠ v') →
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

/-- A single statement never changes the function renaming (function names are
prescanned at the block level). -/
theorem AlphaStmt1.phi_eq {σ φ : Ident → Ident} {s s' : Stmt Op} {σ' φ' : Ident → Ident}
    (h : AlphaStmt1 σ φ s s' σ' φ') : φ' = φ := by cases h <;> rfl

/-! ### Scope-safety (no-shadowing) for the source program -/

/-- Variables a statement adds to the current scope (only `let`). -/
def declVars : Stmt Op → List Ident
  | .letDecl vars _ => vars
  | _ => []

/-- Variables a statement *sequence* adds to the current scope. -/
def declVarsSeq : List (Stmt Op) → List Ident
  | [] => []
  | s :: rest => declVars s ++ declVarsSeq rest

mutual
def WScopedStmts (dom : List Ident) : List (Stmt Op) → Prop
  | [] => True
  | s :: rest => WScopedStmt dom s ∧ WScopedStmts (declVars s ++ dom) rest
def WScopedStmt (dom : List Ident) : Stmt Op → Prop
  | .letDecl vars _ => ∀ x ∈ vars, x ∉ dom
  | .block body => WScopedStmts dom body
  | .cond _ body => WScopedStmts dom body
  | .switch _ cases dflt => WScopedCases dom cases ∧ WScopedDflt dom dflt
  | .funDef _ ps rs body => (ps ++ rs).Nodup ∧ WScopedStmts (ps ++ rs) body
  | .forLoop init _ post body =>
      WScopedStmts dom init ∧ WScopedStmts (declVarsSeq init ++ dom) body ∧
        WScopedStmts (declVarsSeq init ++ dom) post
  | _ => True
def WScopedCases (dom : List Ident) : List (Literal × List (Stmt Op)) → Prop
  | [] => True
  | (_, body) :: rest => WScopedStmts dom body ∧ WScopedCases dom rest
def WScopedDflt (dom : List Ident) : Option (List (Stmt Op)) → Prop
  | none => True
  | some body => WScopedStmts dom body
end

/-! ### Function-scope-safety (no function shadows a visible one) -/

mutual
def FScopedStmts (fdom : List Ident) : List (Stmt Op) → Prop
  | [] => True
  | s :: rest => FScopedStmt fdom s ∧ FScopedStmts fdom rest
def FScopedStmt (fdom : List Ident) : Stmt Op → Prop
  | .block body => (∀ fn ∈ funNames body, fn ∉ fdom) ∧ FScopedStmts (funNames body ++ fdom) body
  | .cond _ body => (∀ fn ∈ funNames body, fn ∉ fdom) ∧ FScopedStmts (funNames body ++ fdom) body
  | .funDef _ _ _ body =>
      (∀ fn ∈ funNames body, fn ∉ fdom) ∧ FScopedStmts (funNames body ++ fdom) body
  | .switch _ cases dflt => FScopedCases fdom cases ∧ FScopedDflt fdom dflt
  | .forLoop init _ post body =>
      (∀ fn ∈ funNames init, fn ∉ fdom) ∧ FScopedStmts (funNames init ++ fdom) init ∧
        ((∀ fn ∈ funNames body, fn ∉ funNames init ++ fdom) ∧
          FScopedStmts (funNames body ++ funNames init ++ fdom) body) ∧
        ((∀ fn ∈ funNames post, fn ∉ funNames init ++ fdom) ∧
          FScopedStmts (funNames post ++ funNames init ++ fdom) post)
  | _ => True
def FScopedCases (fdom : List Ident) : List (Literal × List (Stmt Op)) → Prop
  | [] => True
  | (_, body) :: rest =>
      ((∀ fn ∈ funNames body, fn ∉ fdom) ∧ FScopedStmts (funNames body ++ fdom) body) ∧
        FScopedCases fdom rest
def FScopedDflt (fdom : List Ident) : Option (List (Stmt Op)) → Prop
  | none => True
  | some body => (∀ fn ∈ funNames body, fn ∉ fdom) ∧ FScopedStmts (funNames body ++ fdom) body
end

/-! ### Syntactic agreement lemmas -/

/-- The output variable-renaming of a sequence agrees with the input off the
sequence's declared variables (used for the block/for `restore` step). -/
theorem alphaSeq_agrees : ∀ {ss ss' : List (Stmt Op)} {σ φ σ' φ' : Ident → Ident},
    AlphaSeqExt σ φ ss ss' σ' φ' → ∀ z, z ∉ declVarsSeq ss → σ' z = σ z
  | [], _, _, _, _, _, h, z, _ => by cases h; rfl
  | s :: rest, _, σ0, φ0, _, _, h, z, hz => by
      cases h with
      | @cons _ _ _ s' _ rest' σmid φmid _ _ hs1 hrest =>
      have htail : _ = σmid z :=
        alphaSeq_agrees hrest z (fun hc => hz (by
          rw [declVarsSeq]; exact List.mem_append.mpr (Or.inr hc)))
      rw [htail]
      cases hs1 with
      | letD _ _ _ _ _ _ _ =>
          exact updRen_of_not_mem (fun p hp hpz => hz (by
            rw [declVarsSeq, declVars]
            exact List.mem_append.mpr (Or.inl (hpz ▸ (List.of_mem_zip hp).1))))
      | _ => rfl

/-- A well-scoped sequence's declared variables are disjoint from the domain. -/
theorem wscoped_declVars_disjoint : ∀ {ss : List (Stmt Op)} {dom : List Ident},
    WScopedStmts dom ss → ∀ z ∈ dom, z ∉ declVarsSeq ss
  | [], _, _, z, _ => by simp [declVarsSeq]
  | s :: rest, dom, hws, z, hz => by
      simp only [WScopedStmts] at hws
      obtain ⟨hs, hrest⟩ := hws
      rw [declVarsSeq, List.mem_append, not_or]
      refine ⟨?_, wscoped_declVars_disjoint hrest z (List.mem_append.mpr (Or.inr hz))⟩
      intro hc
      cases s with
      | letDecl vars val => exact hs z hc hz
      | _ => simp [declVars] at hc

end YulEvmCompiler.Optimizer.Normalize
