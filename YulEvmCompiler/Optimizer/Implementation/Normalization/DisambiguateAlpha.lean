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

/-! ### α-equivalence: statements (range-indexed)

Statement-level α-equivalence threads the renamings through binders, **indexed
by a fresh-name counter range `[lo, hi)`**: every fresh target name bound in the
related text is `dsName k` with `lo ≤ k < hi` (`RangeNodup`), and ranges thread
left-to-right exactly like the pass's counter. This replaces per-node renaming
collision-freedom side conditions (which made the relation `φ`-dependent and
blocked congruence): collision-freedom becomes arithmetic — a renaming whose
image is below `lo` cannot hit a binder at or above `lo`.

`AlphaSeqExt lo hi σ φ ss₁ ss₂ σ' φ'` relates a source sequence to its renaming
and reports the renamings `σ'`/`φ'` in force after the sequence's declarations.
A block first prescans its top-level function names into `φ` (Yul's forward
visibility), via `AlphaBlockExt`. -/

mutual
/-- Single-statement α-equivalence, reporting the renamings after the statement's
declarations (only `let` extends `σ`; `funDef` names are prescanned into `φ`). -/
inductive AlphaStmt1 :
    Nat → Nat → (Ident → Ident) → (Ident → Ident) → Stmt Op → Stmt Op →
    (Ident → Ident) → (Ident → Ident) → Prop
  | letD {lo hi σ φ vars vars' eo eo'} :
      vars.Nodup → vars.length = vars'.length →
      (∀ x ∈ vars, NotFresh x) →
      RangeNodup vars' lo hi →
      AlphaOExpr σ φ eo eo' →
      AlphaStmt1 lo hi σ φ (.letDecl vars eo) (.letDecl vars' eo') (updRen σ (vars.zip vars')) φ
  | assignD {lo hi σ φ vars e e'} :
      lo ≤ hi → (∀ x ∈ vars, NotFresh x) → AlphaExpr σ φ e e' →
      AlphaStmt1 lo hi σ φ (.assign vars e) (.assign (vars.map σ) e') σ φ
  | exprD {lo hi σ φ e e'} :
      lo ≤ hi → AlphaExpr σ φ e e' →
      AlphaStmt1 lo hi σ φ (.exprStmt e) (.exprStmt e') σ φ
  | funD {lo m hi σ φ fn ps ps' rs rs' body body' σb φb} :
      (ps ++ rs).Nodup → ps.length = ps'.length → rs.length = rs'.length →
      (∀ x ∈ ps ++ rs, NotFresh x) →
      RangeNodup (ps' ++ rs') lo m →
      AlphaBlockExt m hi (updRen id (ps.zip ps' ++ rs.zip rs')) φ body body' σb φb →
      AlphaStmt1 lo hi σ φ (.funDef fn ps rs body) (.funDef (φ fn) ps' rs' body') σ φ
  | blockD {lo hi σ φ body body' σb φb} :
      AlphaBlockExt lo hi σ φ body body' σb φb →
      AlphaStmt1 lo hi σ φ (.block body) (.block body') σ φ
  | condD {lo hi σ φ c c' body body' σb φb} :
      AlphaExpr σ φ c c' → AlphaBlockExt lo hi σ φ body body' σb φb →
      AlphaStmt1 lo hi σ φ (.cond c body) (.cond c' body') σ φ
  | switchD {lo m hi σ φ c c' cases cases' dflt dflt'} :
      AlphaExpr σ φ c c' → AlphaCases lo m σ φ cases cases' → AlphaDflt m hi σ φ dflt dflt' →
      AlphaStmt1 lo hi σ φ (.switch c cases dflt) (.switch c' cases' dflt') σ φ
  | forD {lo m₁ m₂ hi σ φ init init' c c' post post' body body' σi φi σb φb σp φp} :
      AlphaBlockExt lo m₁ σ φ init init' σi φi →
      AlphaExpr σi φi c c' →
      AlphaBlockExt m₁ m₂ σi φi body body' σb φb →
      AlphaBlockExt m₂ hi σi φi post post' σp φp →
      AlphaStmt1 lo hi σ φ (.forLoop init c post body) (.forLoop init' c' post' body') σ φ
  | breakD {lo hi σ φ} : lo ≤ hi → AlphaStmt1 lo hi σ φ .break .break σ φ
  | contD {lo hi σ φ} : lo ≤ hi → AlphaStmt1 lo hi σ φ .continue .continue σ φ
  | leaveD {lo hi σ φ} : lo ≤ hi → AlphaStmt1 lo hi σ φ .leave .leave σ φ
inductive AlphaSeqExt :
    Nat → Nat → (Ident → Ident) → (Ident → Ident) → List (Stmt Op) → List (Stmt Op) →
    (Ident → Ident) → (Ident → Ident) → Prop
  | nil {lo hi σ φ} : lo ≤ hi → AlphaSeqExt lo hi σ φ [] [] σ φ
  | cons {lo m hi σ φ s s' rest rest' σ' φ' σ'' φ''} :
      AlphaStmt1 lo m σ φ s s' σ' φ' → AlphaSeqExt m hi σ' φ' rest rest' σ'' φ'' →
      AlphaSeqExt lo hi σ φ (s :: rest) (s' :: rest') σ'' φ''
inductive AlphaBlockExt :
    Nat → Nat → (Ident → Ident) → (Ident → Ident) → List (Stmt Op) → List (Stmt Op) →
    (Ident → Ident) → (Ident → Ident) → Prop
  | mk {lo m hi σ φ : _} {b₁ b₂ : List (Stmt Op)} {σ' φ' : Ident → Ident} :
      (funNames b₁).Nodup → (funNames b₁).length = (funNames b₂).length →
      (∀ x ∈ funNames b₁, NotFresh x) →
      RangeNodup (funNames b₂) lo m →
      AlphaSeqExt m hi σ (updRen φ ((funNames b₁).zip (funNames b₂))) b₁ b₂ σ' φ' →
      AlphaBlockExt lo hi σ φ b₁ b₂ σ' φ'
inductive AlphaCases :
    Nat → Nat → (Ident → Ident) → (Ident → Ident) →
    List (Literal × List (Stmt Op)) → List (Literal × List (Stmt Op)) → Prop
  | nil {lo hi σ φ} : lo ≤ hi → AlphaCases lo hi σ φ [] []
  | cons {lo m hi σ φ l body body' rest rest' σb φb} :
      AlphaBlockExt lo m σ φ body body' σb φb → AlphaCases m hi σ φ rest rest' →
      AlphaCases lo hi σ φ ((l, body) :: rest) ((l, body') :: rest')
inductive AlphaDflt :
    Nat → Nat → (Ident → Ident) → (Ident → Ident) →
    Option (List (Stmt Op)) → Option (List (Stmt Op)) → Prop
  | none {lo hi σ φ} : lo ≤ hi → AlphaDflt lo hi σ φ none none
  | some {lo hi σ φ body body' σb φb} :
      AlphaBlockExt lo hi σ φ body body' σb φb → AlphaDflt lo hi σ φ (some body) (some body')
end

/-- A single statement never changes the function renaming (function names are
prescanned at the block level). -/
theorem AlphaStmt1.phi_eq {lo hi : Nat} {σ φ : Ident → Ident} {s s' : Stmt Op}
    {σ' φ' : Ident → Ident} (h : AlphaStmt1 lo hi σ φ s s' σ' φ') : φ' = φ := by
  cases h <;> rfl

/-- A sequence never changes the function renaming either (only `mk`'s prescan
does, before the sequence starts). -/
theorem alphaSeq_phi_eq : ∀ {ss : List (Stmt Op)} {ss' lo hi σ φ σ' φ'},
    AlphaSeqExt lo hi σ φ ss ss' σ' φ' → φ' = φ
  | [], _, _, _, _, _, _, _, h => by cases h; rfl
  | s :: rest, _, _, _, _, _, _, _, h => by
      cases h with
      | cons h1 hrest => exact (alphaSeq_phi_eq hrest).trans h1.phi_eq

/-- A block's output function renaming is the prescan extension of its input. -/
theorem AlphaBlockExt.phi_out {lo hi : Nat} {σ φ : Ident → Ident}
    {b₁ b₂ : List (Stmt Op)} {σ' φ' : Ident → Ident}
    (h : AlphaBlockExt lo hi σ φ b₁ b₂ σ' φ') :
    φ' = updRen φ ((funNames b₁).zip (funNames b₂)) := by
  cases h with
  | mk _ _ _ _ hseq => exact alphaSeq_phi_eq hseq

/-- Related blocks bind the same number of top-level function names. -/
theorem AlphaBlockExt.fn_len {lo hi : Nat} {σ φ : Ident → Ident}
    {b₁ b₂ : List (Stmt Op)} {σ' φ' : Ident → Ident}
    (h : AlphaBlockExt lo hi σ φ b₁ b₂ σ' φ') :
    (funNames b₁).length = (funNames b₂).length := by
  cases h with
  | mk _ hlen _ _ _ => exact hlen

/-! ### Range monotonicity: every α-node spans a valid interval -/

mutual
theorem alphaStmt1_le : ∀ {s : Stmt Op} {s' lo hi σ φ σ' φ'},
    AlphaStmt1 lo hi σ φ s s' σ' φ' → lo ≤ hi
  | .letDecl _ _, _, _, _, _, _, _, _, h => by
      cases h with | letD _ _ _ hrn _ => exact hrn.2.2
  | .assign _ _, _, _, _, _, _, _, _, h => by
      cases h with | assignD hle _ _ => exact hle
  | .exprStmt _, _, _, _, _, _, _, _, h => by
      cases h with | exprD hle _ => exact hle
  | .funDef _ _ _ body, _, _, _, _, _, _, _, h => by
      cases h with | funD _ _ _ _ hrn hbe =>
      cases hbe with | mk _ _ _ hrnB hseq =>
      exact Nat.le_trans hrn.2.2 (Nat.le_trans hrnB.2.2 (alphaSeqExt_le hseq))
  | .block body, _, _, _, _, _, _, _, h => by
      cases h with | blockD hbe =>
      cases hbe with | mk _ _ _ hrn hseq =>
      exact Nat.le_trans hrn.2.2 (alphaSeqExt_le hseq)
  | .cond _ body, _, _, _, _, _, _, _, h => by
      cases h with | condD _ hbe =>
      cases hbe with | mk _ _ _ hrn hseq =>
      exact Nat.le_trans hrn.2.2 (alphaSeqExt_le hseq)
  | .switch _ _ _, _, _, _, _, _, _, _, h => by
      cases h with | switchD _ hcs hd =>
        exact Nat.le_trans (alphaCases_le hcs) (alphaDflt_le hd)
  | .forLoop init _ post body, _, _, _, _, _, _, _, h => by
      cases h with | forD hI _ hb hp =>
      cases hI with | mk _ _ _ hrnI hseqI =>
      cases hb with | mk _ _ _ hrnB hseqB =>
      cases hp with | mk _ _ _ hrnP hseqP =>
      exact Nat.le_trans hrnI.2.2 (Nat.le_trans (alphaSeqExt_le hseqI)
        (Nat.le_trans hrnB.2.2 (Nat.le_trans (alphaSeqExt_le hseqB)
          (Nat.le_trans hrnP.2.2 (alphaSeqExt_le hseqP)))))
  | .«break», _, _, _, _, _, _, _, h => by cases h with | breakD hle => exact hle
  | .«continue», _, _, _, _, _, _, _, h => by cases h with | contD hle => exact hle
  | .leave, _, _, _, _, _, _, _, h => by cases h with | leaveD hle => exact hle
theorem alphaSeqExt_le : ∀ {ss : List (Stmt Op)} {ss' lo hi σ φ σ' φ'},
    AlphaSeqExt lo hi σ φ ss ss' σ' φ' → lo ≤ hi
  | [], _, _, _, _, _, _, _, h => by cases h with | nil hle => exact hle
  | s :: rest, _, _, _, _, _, _, _, h => by
      cases h with
      | cons h1 hrest => exact Nat.le_trans (alphaStmt1_le h1) (alphaSeqExt_le hrest)
theorem alphaCases_le : ∀ {cs : List (Literal × List (Stmt Op))} {cs' lo hi σ φ},
    AlphaCases lo hi σ φ cs cs' → lo ≤ hi
  | [], _, _, _, _, _, h => by cases h with | nil hle => exact hle
  | (l, body) :: rest, _, _, _, _, _, h => by
      cases h with
      | cons hb hrest =>
          cases hb with | mk _ _ _ hrn hseq =>
          exact Nat.le_trans hrn.2.2 (Nat.le_trans (alphaSeqExt_le hseq) (alphaCases_le hrest))
theorem alphaDflt_le : ∀ {dflt : Option (List (Stmt Op))} {dflt' lo hi σ φ},
    AlphaDflt lo hi σ φ dflt dflt' → lo ≤ hi
  | none, _, _, _, _, _, h => by cases h with | none hle => exact hle
  | some body, _, _, _, _, _, h => by
      cases h with
      | some hb =>
          cases hb with | mk _ _ _ hrn hseq =>
          exact Nat.le_trans hrn.2.2 (alphaSeqExt_le hseq)
end

/-- A block spans a valid interval. -/
theorem alphaBlockExt_le {b₁ b₂ : List (Stmt Op)} {lo hi σ φ σ' φ'}
    (h : AlphaBlockExt lo hi σ φ b₁ b₂ σ' φ') : lo ≤ hi := by
  cases h with
  | mk _ _ _ hrn hseq => exact Nat.le_trans hrn.2.2 (alphaSeqExt_le hseq)

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
theorem alphaSeq_agrees : ∀ {ss ss' : List (Stmt Op)} {lo hi} {σ φ σ' φ' : Ident → Ident},
    AlphaSeqExt lo hi σ φ ss ss' σ' φ' → ∀ z, z ∉ declVarsSeq ss → σ' z = σ z
  | [], _, _, _, _, _, _, _, h, z, _ => by cases h; rfl
  | s :: rest, _, _, _, σ0, φ0, _, _, h, z, hz => by
      cases h with
      | @cons _ _ _ _ _ _ s' _ rest' σmid φmid _ _ hs1 hrest =>
      have htail : _ = σmid z :=
        alphaSeq_agrees hrest z (fun hc => hz (by
          rw [declVarsSeq]; exact List.mem_append.mpr (Or.inr hc)))
      rw [htail]
      cases hs1 with
      | letD _ _ _ _ _ =>
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


/-! ### α-relation φ-congruence (statement level)

The α-relations depend on `φ` only through the function names the code
*references*: for well-scoped code (`NormalForm.Scoped*`) those resolve in the
visible functions, so a `φ` that agrees on them relates the same pair. Nothing
else in the relation mentions `φ` (the range indices replaced the old
`φ`-dependent freshness conditions), so the congruence is purely structural.
This is what transports a stored function declaration's body relation across a
block's `φ`-extension (the `FDeclRen` transport in the bisimulation). -/

/-- A full zip's `find?`-miss means the key is absent. -/
theorem find?_zip_none_not_mem {xs ys : List Ident} {x : Ident} (hlen : xs.length ≤ ys.length)
    (h : (xs.zip ys).find? (fun p => p.1 = x) = none) : x ∉ xs := by
  intro hx
  have hkeys : (xs.zip ys).map Prod.fst = xs := List.map_fst_zip hlen
  have hx' : x ∈ (xs.zip ys).map Prod.fst := by rw [hkeys]; exact hx
  obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hx'
  have := List.find?_eq_none.mp h p hp
  simp [hpx] at this

/-- Agreement on `fs` extends through a prescan `updRen` to `fs ++ new`. -/
theorem updRen_agree_extend {φ φ2 : Ident → Ident} {fs new new' : List Ident}
    (hag : ∀ fn ∈ fs, φ2 fn = φ fn) (hlen : new.length = new'.length) :
    ∀ fn ∈ fs ++ new, updRen φ2 (new.zip new') fn = updRen φ (new.zip new') fn := by
  intro fn hfn
  simp only [updRen]
  cases hfind : (new.zip new').find? (fun p => p.1 = fn) with
  | some p => rfl
  | none =>
      have hnn : fn ∉ new := find?_zip_none_not_mem (Nat.le_of_eq hlen) hfind
      have hfs : fn ∈ fs := by
        rcases List.mem_append.mp hfn with h | h
        · exact h
        · exact absurd h hnn
      exact hag fn hfs

/-- The pass's block-level function-name collector agrees with the shared spec's. -/
theorem funNames_eq_funDefNames : ∀ ss : List (Stmt Op),
    funNames ss = NormalForm.funDefNames ss
  | [] => rfl
  | s :: rest => by
      cases s <;>
        simp [funNames, NormalForm.funDefNames, NormalForm.funDefName?,
          List.filterMap_cons, ← funNames_eq_funDefNames rest,
          funNames_eq_funDefNames rest]

set_option maxHeartbeats 1600000 in
mutual
theorem alphaStmt1_congr_phi {vs fs : List Ident} {φ2 : Ident → Ident} :
    ∀ {s : Stmt Op} {s' lo hi σ φ σ' φ'}, AlphaStmt1 lo hi σ φ s s' σ' φ' →
      NormalForm.ScopedStmt vs fs s →
      (∀ f, NormalForm.funDefName? s = some f → f ∈ fs) →
      (∀ fn ∈ fs, φ2 fn = φ fn) →
      AlphaStmt1 lo hi σ φ2 s s' σ' φ2
  | .letDecl vars eo, _, _, _, _, _, _, _, h, hsc, _, hag => by
      cases h with
      | letD hvnd hlen hvNF hrn hoe =>
          refine .letD hvnd hlen hvNF hrn ?_
          refine alphaOExpr_congr_phi (vs := vs) hoe ?_ hag
          cases eo with
          | none => intro e he; cases he
          | some e0 =>
              intro e he
              cases he
              exact (hsc : NormalForm.ScopedExpr vs fs e0)
  | .assign vars e, _, _, _, _, _, _, _, h, hsc, _, hag => by
      cases h with
      | assignD hle hNF he =>
          exact .assignD hle hNF (alphaExpr_congr_phi he
            (hsc : (∀ x ∈ vars, x ∈ vs) ∧ NormalForm.ScopedExpr vs fs e).2 hag)
  | .exprStmt e, _, _, _, _, _, _, _, h, hsc, _, hag => by
      cases h with
      | exprD hle he =>
          exact .exprD hle (alphaExpr_congr_phi he (hsc : NormalForm.ScopedExpr vs fs e) hag)
  | .funDef fn ps rs body, _, _, _, σ0, φ0, _, _, h, hsc, hfd, hag => by
      cases h with
      | funD hnd hlp hlr hNF hrn hbe =>
          have hb2 := alphaBlockExt_congr_phi hbe
            (hsc : NormalForm.ScopedStmts (ps ++ rs)
              (fs ++ NormalForm.funDefNames body) body) hag
          have hc := AlphaStmt1.funD (fn := fn) (σ := σ0) (φ := φ2) hnd hlp hlr hNF hrn hb2
          rwa [hag fn (hfd fn rfl)] at hc
  | .block body, _, _, _, _, _, _, _, h, hsc, _, hag => by
      cases h with
      | blockD hbe =>
          exact .blockD (alphaBlockExt_congr_phi hbe
            (hsc : NormalForm.ScopedStmts vs (fs ++ NormalForm.funDefNames body) body) hag)
  | .cond c body, _, _, _, _, _, _, _, h, hsc, _, hag => by
      obtain ⟨hscc, hscb⟩ := (hsc : NormalForm.ScopedExpr vs fs c ∧
        NormalForm.ScopedStmts vs (fs ++ NormalForm.funDefNames body) body)
      cases h with
      | condD hce hbe =>
          exact .condD (alphaExpr_congr_phi hce hscc hag)
            (alphaBlockExt_congr_phi hbe hscb hag)
  | .switch c cases dflt, _, _, _, _, _, _, _, h, hsc, _, hag => by
      obtain ⟨hscc, hsccs, hscd⟩ := (hsc : NormalForm.ScopedExpr vs fs c ∧
        NormalForm.ScopedCases vs fs cases ∧ NormalForm.ScopedDflt vs fs dflt)
      cases h with
      | switchD hce hcs hd =>
          exact .switchD (alphaExpr_congr_phi hce hscc hag)
            (alphaCases_congr_phi hcs hsccs hag) (alphaDflt_congr_phi hd hscd hag)
  | .forLoop init c post body, _, _, _, _, _, _, _, h, hsc, _, hag => by
      obtain ⟨hsci, hscc, hscp, hscb⟩ := (hsc :
        NormalForm.ScopedStmts vs (fs ++ NormalForm.funDefNames init) init ∧
        NormalForm.ScopedExpr (vs ++ NormalForm.declTopVarsL init)
          (fs ++ NormalForm.funDefNames init) c ∧
        NormalForm.ScopedStmts (vs ++ NormalForm.declTopVarsL init)
          ((fs ++ NormalForm.funDefNames init) ++ NormalForm.funDefNames post) post ∧
        NormalForm.ScopedStmts (vs ++ NormalForm.declTopVarsL init)
          ((fs ++ NormalForm.funDefNames init) ++ NormalForm.funDefNames body) body)
      cases h with
      | @forD _ _ _ _ _ _ _ init' _ _ _ _ _ _ σi φi _ _ _ _ hInit hce hb hp =>
          have hI2 := alphaBlockExt_congr_phi hInit hsci hag
          have hagI : ∀ f ∈ fs ++ NormalForm.funDefNames init,
              updRen φ2 ((funNames init).zip (funNames init')) f = φi f := by
            have h0 := updRen_agree_extend
              (new := funNames init) (new' := funNames init') hag hInit.fn_len
            intro f hf
            rw [← funNames_eq_funDefNames] at hf
            rw [h0 f hf, ← hInit.phi_out]
          have hout2 := hI2.phi_out
          rw [← hout2] at hagI
          exact .forD hI2 (alphaExpr_congr_phi hce hscc hagI)
            (alphaBlockExt_congr_phi hb hscb hagI)
            (alphaBlockExt_congr_phi hp hscp hagI)
  | .«break», _, _, _, _, _, _, _, h, _, _, _ => by
      cases h with | breakD hle => exact .breakD hle
  | .«continue», _, _, _, _, _, _, _, h, _, _, _ => by
      cases h with | contD hle => exact .contD hle
  | .leave, _, _, _, _, _, _, _, h, _, _, _ => by
      cases h with | leaveD hle => exact .leaveD hle
theorem alphaSeqExt_congr_phi {vs fs : List Ident} {φ2 : Ident → Ident} :
    ∀ {ss : List (Stmt Op)} {ss' lo hi σ φ σ' φ'}, AlphaSeqExt lo hi σ φ ss ss' σ' φ' →
      NormalForm.ScopedStmts vs fs ss →
      (∀ f ∈ NormalForm.funDefNames ss, f ∈ fs) →
      (∀ fn ∈ fs, φ2 fn = φ fn) →
      AlphaSeqExt lo hi σ φ2 ss ss' σ' φ2
  | [], _, _, _, _, _, _, _, h, _, _, _ => by
      cases h with | nil hle => exact .nil hle
  | s :: rest, _, _, _, _, _, _, _, h, hsc, hfd, hag => by
      obtain ⟨hscs, hscr⟩ := (hsc : NormalForm.ScopedStmt vs fs s ∧
        NormalForm.ScopedStmts (vs ++ NormalForm.declTopVars s) fs rest)
      have hfds : ∀ f, NormalForm.funDefName? s = some f → f ∈ fs := by
        intro f hf
        refine hfd f ?_
        rw [NormalForm.funDefNames, List.filterMap_cons, hf]
        exact List.mem_cons_self ..
      have hfdr : ∀ f ∈ NormalForm.funDefNames rest, f ∈ fs := by
        intro f hf
        refine hfd f ?_
        rw [NormalForm.funDefNames, List.filterMap_cons]
        cases NormalForm.funDefName? s with
        | none => exact hf
        | some g => exact List.mem_cons_of_mem _ hf
      cases h with
      | cons h1 hrest =>
          have hpe := h1.phi_eq
          subst hpe
          exact .cons (alphaStmt1_congr_phi h1 hscs hfds hag)
            (alphaSeqExt_congr_phi hrest hscr hfdr hag)
theorem alphaBlockExt_congr_phi {vs fs : List Ident} {φ2 : Ident → Ident} :
    ∀ {b₁ : List (Stmt Op)} {b₂ lo hi σ φ σ' φ'}, AlphaBlockExt lo hi σ φ b₁ b₂ σ' φ' →
      NormalForm.ScopedStmts vs (fs ++ NormalForm.funDefNames b₁) b₁ →
      (∀ fn ∈ fs, φ2 fn = φ fn) →
      AlphaBlockExt lo hi σ φ2 b₁ b₂ σ' (updRen φ2 ((funNames b₁).zip (funNames b₂)))
  | b₁, b₂, _, _, _, φ0, _, _, h, hsc, hag => by
      cases h with
      | mk hnd hlen hNF hrn hseq =>
          have hagB : ∀ fn ∈ fs ++ NormalForm.funDefNames b₁,
              updRen φ2 ((funNames b₁).zip (funNames b₂)) fn
              = updRen φ0 ((funNames b₁).zip (funNames b₂)) fn := by
            have h0 := updRen_agree_extend
              (new := funNames b₁) (new' := funNames b₂) hag hlen
            intro fn hfn
            rw [← funNames_eq_funDefNames] at hfn
            exact h0 fn hfn
          have hfdB : ∀ f ∈ NormalForm.funDefNames b₁,
              f ∈ fs ++ NormalForm.funDefNames b₁ :=
            fun f hf => List.mem_append.mpr (Or.inr hf)
          exact AlphaBlockExt.mk hnd hlen hNF hrn
            (alphaSeqExt_congr_phi hseq hsc hfdB hagB)
theorem alphaCases_congr_phi {vs fs : List Ident} {φ2 : Ident → Ident} :
    ∀ {cs : List (Literal × List (Stmt Op))} {cs' lo hi σ φ}, AlphaCases lo hi σ φ cs cs' →
      NormalForm.ScopedCases vs fs cs → (∀ fn ∈ fs, φ2 fn = φ fn) →
      AlphaCases lo hi σ φ2 cs cs'
  | [], _, _, _, _, _, h, _, _ => by
      cases h with | nil hle => exact .nil hle
  | (l, body) :: rest, _, _, _, _, _, h, hsc, hag => by
      obtain ⟨hscb, hscr⟩ := (hsc :
        NormalForm.ScopedStmts vs (fs ++ NormalForm.funDefNames body) body ∧
        NormalForm.ScopedCases vs fs rest)
      cases h with
      | cons hb hrest =>
          exact .cons (alphaBlockExt_congr_phi hb hscb hag)
            (alphaCases_congr_phi hrest hscr hag)
theorem alphaDflt_congr_phi {vs fs : List Ident} {φ2 : Ident → Ident} :
    ∀ {dflt : Option (List (Stmt Op))} {dflt' lo hi σ φ}, AlphaDflt lo hi σ φ dflt dflt' →
      NormalForm.ScopedDflt vs fs dflt → (∀ fn ∈ fs, φ2 fn = φ fn) →
      AlphaDflt lo hi σ φ2 dflt dflt'
  | none, _, _, _, _, _, h, _, _ => by
      cases h with | none hle => exact .none hle
  | some body, _, _, _, _, _, h, hsc, hag => by
      have hscb : NormalForm.ScopedStmts vs
          (fs ++ NormalForm.funDefNames body) body := hsc
      cases h with
      | some hb => exact .some (alphaBlockExt_congr_phi hb hscb hag)
end


end YulEvmCompiler.Optimizer.Normalize
