import YulEvmCompiler.Optimizer.Implementation.Normalization.Normalize
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.OrderedMonoid
set_option warningAsError true
/-!
# The normalization front-end establishes the shared `NormalForm` vocabulary

This module connects the normalization passes to the **canonical** normal-form
spec in `NormalForm.lean`, so downstream passes speak a single vocabulary rather
than each pass's private predicate.

Three "same notion, different phrasing" reconciliations live here, all pointing
at the canonical predicates in `NormalForm.lean`:

* **Uniqueness.** The hoist pass's `Normalization.UniqueFunNames` (function names
  distinct) is exactly the function-name projection of the canonical
  `NormalForm.UniqueNames` (*all* declared names distinct): every function name
  is a declared name, so `funNamesStmts` is a sublist of `declaredNamesStmts`,
  and `Nodup` passes to sublists (`uniqueNames_uniqueFunNames`).

* **Well-scopedness.** The hoist pass's `Normalization.WellScoped` is the
  *function-call-scoping fragment* of the canonical `NormalForm.WellScoped` (which
  also tracks variable scope): the canonical predicate implies it
  (`wellScoped_callsScoped`), via a scope-inclusion-generalized induction and the
  collector identity `funNamesTop = funDefNames` (`funNamesTop_eq_funDefNames`).

* **The postcondition.** `normalize` establishes `NormalForm.UniqueNames`
  (`normalize_uniqueNames`): disambiguation makes all names distinct
  (`disambiguate_uniqueNames`) and function hoisting only permutes statements, so
  it preserves the multiset of declared names (`declaredNamesStmts_liftFunDefs_perm`)
  and hence `Nodup`.

`FunctionsHoisted (normalize b)` — the other half of the front-end's normal form
— additionally needs the guard to be observed to fire, i.e. a `Bool`-completeness
bridge `NormalForm.WellScoped b → wellScopedB (disambiguate b) = true` together
with a proof that disambiguation *preserves* `NormalForm.WellScoped`; that (and
raising the remaining `NormalForm` fields via the not-yet-landed ANF / for-init /
flatten passes, plus the per-stage preservation obligations) is the follow-up
tracked in `NormalForm.lean` and `Optimizer/IDEAS.md`.
-/

namespace YulEvmCompiler.Optimizer.Normalize

open YulSemantics
open scoped List

variable {D : Dialect}

/-! ### Uniqueness: `UniqueFunNames` is the function-name projection of `UniqueNames` -/

mutual
/-- Every function name declared in a statement is one of its declared names. -/
theorem funNamesStmt_sublist_declared : ∀ (s : Stmt D.Op),
    (Normalization.funNamesStmt s).Sublist (NormalForm.declaredNamesStmt s)
  | .funDef n ps rs body => by
      simp only [Normalization.funNamesStmt, NormalForm.declaredNamesStmt]
      exact ((funNamesStmts_sublist_declared body).trans
        (List.sublist_append_right (ps ++ rs) _)).cons_cons n
  | .block bb => by
      simp only [Normalization.funNamesStmt, NormalForm.declaredNamesStmt]
      exact funNamesStmts_sublist_declared bb
  | .cond _ bb => by
      simp only [Normalization.funNamesStmt, NormalForm.declaredNamesStmt]
      exact funNamesStmts_sublist_declared bb
  | .switch _ cs d => by
      simp only [Normalization.funNamesStmt, NormalForm.declaredNamesStmt]
      exact (funNamesCases_sublist_declared cs).append (funNamesDflt_sublist_declared d)
  | .forLoop init _ post body => by
      simp only [Normalization.funNamesStmt, NormalForm.declaredNamesStmt]
      exact ((funNamesStmts_sublist_declared init).append
        (funNamesStmts_sublist_declared post)).append (funNamesStmts_sublist_declared body)
  | .letDecl _ _ => by simp only [Normalization.funNamesStmt]; exact List.nil_sublist _
  | .assign _ _ => by simp only [Normalization.funNamesStmt]; exact List.nil_sublist _
  | .exprStmt _ => by simp only [Normalization.funNamesStmt]; exact List.nil_sublist _
  | .«break» => by simp only [Normalization.funNamesStmt]; exact List.nil_sublist _
  | .«continue» => by simp only [Normalization.funNamesStmt]; exact List.nil_sublist _
  | .leave => by simp only [Normalization.funNamesStmt]; exact List.nil_sublist _
theorem funNamesStmts_sublist_declared : ∀ (b : List (Stmt D.Op)),
    (Normalization.funNamesStmts b).Sublist (NormalForm.declaredNamesStmts b)
  | [] => by simp [Normalization.funNamesStmts, NormalForm.declaredNamesStmts]
  | s :: rest => by
      simp only [Normalization.funNamesStmts, NormalForm.declaredNamesStmts]
      exact (funNamesStmt_sublist_declared s).append (funNamesStmts_sublist_declared rest)
theorem funNamesCases_sublist_declared : ∀ (cs : List (Literal × Block D.Op)),
    (Normalization.funNamesCases cs).Sublist (NormalForm.declaredNamesCases cs)
  | [] => by simp [Normalization.funNamesCases, NormalForm.declaredNamesCases]
  | (_, b) :: rest => by
      simp only [Normalization.funNamesCases, NormalForm.declaredNamesCases]
      exact (funNamesStmts_sublist_declared b).append (funNamesCases_sublist_declared rest)
theorem funNamesDflt_sublist_declared : ∀ (d : Option (Block D.Op)),
    (Normalization.funNamesDflt d).Sublist (NormalForm.declaredNamesDflt d)
  | none => by simp [Normalization.funNamesDflt, NormalForm.declaredNamesDflt]
  | some b => by
      simp only [Normalization.funNamesDflt, NormalForm.declaredNamesDflt]
      exact funNamesStmts_sublist_declared b
end

/-- **`UniqueNames` (all declared names distinct) implies `UniqueFunNames`**
(function names distinct): the canonical uniqueness normal form subsumes the
hoist pass's function-only precondition. -/
theorem uniqueNames_uniqueFunNames {b : Block D.Op} (h : NormalForm.UniqueNames b) :
    Normalization.UniqueFunNames b :=
  (funNamesStmts_sublist_declared b).nodup h

/-! ### Function hoisting preserves the multiset of declared names

`liftFunDefs b = collectStmts b ++ stripStmts b` only relocates function
definitions, so the multiset of *declared* names is unchanged — a `List.Perm`.
Each case reduces, via the `Multiset` coercion, to an additive-commutative-monoid
identity closed by `ac_rfl` after rewriting with the sub-block hypotheses. -/

theorem declaredNamesStmts_append : ∀ (a b : List (Stmt Op)),
    NormalForm.declaredNamesStmts (a ++ b)
      = NormalForm.declaredNamesStmts a ++ NormalForm.declaredNamesStmts b
  | [], _ => by simp [NormalForm.declaredNamesStmts]
  | s :: a', b => by
      simp only [List.cons_append, NormalForm.declaredNamesStmts, declaredNamesStmts_append a' b,
        List.append_assoc]

mutual
/-- Hoisting a block's function definitions to the front permutes, but does not
change, the multiset of declared names. -/
theorem declaredNamesStmts_liftPerm : ∀ (b : List (Stmt D.Op)),
    (NormalForm.declaredNamesStmts (Normalization.collectStmts b)
      ++ NormalForm.declaredNamesStmts (Normalization.stripStmts b)).Perm
      (NormalForm.declaredNamesStmts b)
  | [] => by
      simp [Normalization.collectStmts, Normalization.stripStmts, NormalForm.declaredNamesStmts]
  | s :: rest => by
      have ihr := declaredNamesStmts_liftPerm rest
      cases s with
      | funDef n ps rs body =>
          have ihb := declaredNamesStmts_liftPerm body
          simp only [Normalization.collectStmts, Normalization.collectStmt, Normalization.stripStmts,
            List.cons_append, declaredNamesStmts_append, NormalForm.declaredNamesStmts,
            NormalForm.declaredNamesStmt]
          rw [← Multiset.coe_eq_coe] at ihb ihr ⊢
          simp only [← Multiset.coe_add, ← Multiset.cons_coe, ← Multiset.singleton_add] at ihb ihr ⊢
          rw [← ihb, ← ihr]; ac_rfl
      | block bb =>
          have ihb := declaredNamesStmts_liftPerm bb
          simp only [Normalization.collectStmts, Normalization.collectStmt, Normalization.stripStmts,
            Normalization.stripStmt, declaredNamesStmts_append, NormalForm.declaredNamesStmts,
            NormalForm.declaredNamesStmt]
          rw [← Multiset.coe_eq_coe] at ihb ihr ⊢
          simp only [← Multiset.coe_add] at ihb ihr ⊢
          rw [← ihb, ← ihr]; ac_rfl
      | cond c bb =>
          have ihb := declaredNamesStmts_liftPerm bb
          simp only [Normalization.collectStmts, Normalization.collectStmt, Normalization.stripStmts,
            Normalization.stripStmt, declaredNamesStmts_append, NormalForm.declaredNamesStmts,
            NormalForm.declaredNamesStmt]
          rw [← Multiset.coe_eq_coe] at ihb ihr ⊢
          simp only [← Multiset.coe_add] at ihb ihr ⊢
          rw [← ihb, ← ihr]; ac_rfl
      | switch c cs d =>
          have ihc := declaredNamesCases_liftPerm cs
          have ihd := declaredNamesDflt_liftPerm d
          simp only [Normalization.collectStmts, Normalization.collectStmt, Normalization.stripStmts,
            Normalization.stripStmt, declaredNamesStmts_append, NormalForm.declaredNamesStmts,
            NormalForm.declaredNamesStmt]
          rw [← Multiset.coe_eq_coe] at ihc ihd ihr ⊢
          simp only [← Multiset.coe_add] at ihc ihd ihr ⊢
          rw [← ihc, ← ihd, ← ihr]; ac_rfl
      | forLoop init c post body =>
          have ihi := declaredNamesStmts_liftPerm init
          have ihp := declaredNamesStmts_liftPerm post
          have ihbo := declaredNamesStmts_liftPerm body
          simp only [Normalization.collectStmts, Normalization.collectStmt, Normalization.stripStmts,
            Normalization.stripStmt, declaredNamesStmts_append, NormalForm.declaredNamesStmts,
            NormalForm.declaredNamesStmt]
          rw [← Multiset.coe_eq_coe] at ihi ihp ihbo ihr ⊢
          simp only [← Multiset.coe_add] at ihi ihp ihbo ihr ⊢
          rw [← ihi, ← ihp, ← ihbo, ← ihr]; ac_rfl
      | letDecl vs v =>
          simp only [Normalization.collectStmts, Normalization.collectStmt, Normalization.stripStmts,
            Normalization.stripStmt, NormalForm.declaredNamesStmts,
            NormalForm.declaredNamesStmt, List.nil_append]
          rw [← Multiset.coe_eq_coe] at ihr ⊢
          simp only [← Multiset.coe_add] at ihr ⊢
          rw [← ihr]; ac_rfl
      | assign vs e =>
          simp only [Normalization.collectStmts, Normalization.collectStmt, Normalization.stripStmts,
            Normalization.stripStmt, NormalForm.declaredNamesStmts, NormalForm.declaredNamesStmt,
            List.nil_append]
          exact ihr
      | exprStmt e =>
          simp only [Normalization.collectStmts, Normalization.collectStmt, Normalization.stripStmts,
            Normalization.stripStmt, NormalForm.declaredNamesStmts, NormalForm.declaredNamesStmt,
            List.nil_append]
          exact ihr
      | «break» =>
          simp only [Normalization.collectStmts, Normalization.collectStmt, Normalization.stripStmts,
            Normalization.stripStmt, NormalForm.declaredNamesStmts, NormalForm.declaredNamesStmt,
            List.nil_append]
          exact ihr
      | «continue» =>
          simp only [Normalization.collectStmts, Normalization.collectStmt, Normalization.stripStmts,
            Normalization.stripStmt, NormalForm.declaredNamesStmts, NormalForm.declaredNamesStmt,
            List.nil_append]
          exact ihr
      | leave =>
          simp only [Normalization.collectStmts, Normalization.collectStmt, Normalization.stripStmts,
            Normalization.stripStmt, NormalForm.declaredNamesStmts, NormalForm.declaredNamesStmt,
            List.nil_append]
          exact ihr
theorem declaredNamesCases_liftPerm : ∀ (cs : List (Literal × Block D.Op)),
    (NormalForm.declaredNamesStmts (Normalization.collectCases cs)
      ++ NormalForm.declaredNamesCases (Normalization.stripCases cs)).Perm
      (NormalForm.declaredNamesCases cs)
  | [] => by
      simp [Normalization.collectCases, Normalization.stripCases, NormalForm.declaredNamesCases,
        NormalForm.declaredNamesStmts]
  | (l, b) :: rest => by
      have ihb := declaredNamesStmts_liftPerm b
      have ihr := declaredNamesCases_liftPerm rest
      simp only [Normalization.collectCases, Normalization.stripCases, declaredNamesStmts_append,
        NormalForm.declaredNamesCases]
      rw [← Multiset.coe_eq_coe] at ihb ihr ⊢
      simp only [← Multiset.coe_add] at ihb ihr ⊢
      rw [← ihb, ← ihr]; ac_rfl
theorem declaredNamesDflt_liftPerm : ∀ (d : Option (Block D.Op)),
    (NormalForm.declaredNamesStmts (Normalization.collectDflt d)
      ++ NormalForm.declaredNamesDflt (Normalization.stripDflt d)).Perm
      (NormalForm.declaredNamesDflt d)
  | none => by
      simp [Normalization.collectDflt, Normalization.stripDflt, NormalForm.declaredNamesDflt,
        NormalForm.declaredNamesStmts]
  | some b => by
      simp only [Normalization.collectDflt, Normalization.stripDflt, NormalForm.declaredNamesDflt]
      exact declaredNamesStmts_liftPerm b
end

/-- **Function hoisting preserves the multiset of declared names.** -/
theorem declaredNamesStmts_liftFunDefs_perm (b : Block D.Op) :
    (NormalForm.declaredNamesStmts (Normalization.liftFunDefs b)).Perm
      (NormalForm.declaredNamesStmts b) := by
  rw [Normalization.liftFunDefs, declaredNamesStmts_append]
  exact declaredNamesStmts_liftPerm b

/-- Function hoisting preserves `NormalForm.UniqueNames`. -/
theorem uniqueNames_liftFunDefs {b : Block D.Op} (h : NormalForm.UniqueNames b) :
    NormalForm.UniqueNames (Normalization.liftFunDefs b) :=
  (declaredNamesStmts_liftFunDefs_perm b).nodup_iff.mpr h

/-- The guarded hoister preserves `NormalForm.UniqueNames`. -/
theorem uniqueNames_hoistBlock {b : Block D.Op} (h : NormalForm.UniqueNames b) :
    NormalForm.UniqueNames (Normalization.hoistBlock b) := by
  simp only [Normalization.hoistBlock, guardedBlock]
  by_cases hb : Normalization.hoistGuard b = true
  · rw [if_pos hb]; exact uniqueNames_liftFunDefs h
  · rw [if_neg hb]; exact h

/-- **`normalize` establishes the canonical `UniqueNames` normal form.** For a
valid source block, no name is declared twice after normalization: disambiguation
makes names distinct and hoisting preserves that. -/
theorem normalize_uniqueNames {b : Block D.Op} (h : SourceValid b) :
    NormalForm.UniqueNames (normalize b) :=
  uniqueNames_hoistBlock (disambiguate_uniqueNames b h.2.1)

/-! ### Well-scopedness: the canonical predicate implies the hoist pass's

The hoist pass's `Normalization.WellScoped` is the **function-call-scoping
fragment** of the canonical `NormalForm.WellScoped`: it checks only that every
call resolves in the visible function scope, ignoring variable scope. So the
canonical predicate (which additionally tracks variables) implies it. This lets
the hoister's precondition be discharged from the single canonical spec. -/

/-- The two "top-level function names of a block" collectors coincide
(`Normalization.funNamesTop` = `NormalForm.funDefNames`). -/
theorem funNamesTop_eq_funDefNames (b : List (Stmt D.Op)) :
    Normalization.funNamesTop b = NormalForm.funDefNames b := by
  unfold Normalization.funNamesTop NormalForm.funDefNames
  apply List.filterMap_congr
  intro s _; cases s <;> rfl

/-- Extend a function-scope inclusion by a block's hoisted functions on both
sides: if `fs ⊆ scope` then `fs ++ funDefNames body ⊆ funNamesTop body ++ scope`. -/
theorem funScope_ext {fs scope : List Ident} (hsub : ∀ x ∈ fs, x ∈ scope)
    (body : List (Stmt D.Op)) :
    ∀ x ∈ (fs ++ NormalForm.funDefNames body), x ∈ (Normalization.funNamesTop body ++ scope) := by
  intro x hx
  rw [List.mem_append] at hx ⊢
  rcases hx with h | h
  · exact Or.inr (hsub x h)
  · exact Or.inl (by rw [funNamesTop_eq_funDefNames]; exact h)

mutual
theorem callsScoped_expr : ∀ {vs fs scope : List Ident} (_ : ∀ x ∈ fs, x ∈ scope)
    {e : Expr D.Op}, NormalForm.ScopedExpr vs fs e → Normalization.ScopedExpr scope e
  | _, _, _, _, .lit _, _ => by simp [Normalization.ScopedExpr]
  | _, _, _, _, .var _, _ => by simp [Normalization.ScopedExpr]
  | _, _, _, hsub, .builtin _ args, h => by
      simp only [NormalForm.ScopedExpr] at h
      simpa only [Normalization.ScopedExpr] using callsScoped_args hsub h
  | _, _, _, hsub, .call fn args, h => by
      simp only [NormalForm.ScopedExpr] at h
      exact ⟨hsub fn h.1, callsScoped_args hsub h.2⟩
theorem callsScoped_args : ∀ {vs fs scope : List Ident} (_ : ∀ x ∈ fs, x ∈ scope)
    {es : List (Expr D.Op)}, NormalForm.ScopedArgs vs fs es → Normalization.ScopedArgs scope es
  | _, _, _, _, [], _ => by simp [Normalization.ScopedArgs]
  | _, _, _, hsub, _ :: _, h => by
      simp only [NormalForm.ScopedArgs] at h
      exact ⟨callsScoped_expr hsub h.1, callsScoped_args hsub h.2⟩
theorem callsScoped_stmt : ∀ {vs fs scope : List Ident} (_ : ∀ x ∈ fs, x ∈ scope)
    {s : Stmt D.Op}, NormalForm.ScopedStmt vs fs s → Normalization.ScopedStmt scope s
  | _, _, _, hsub, .block body, h => by
      simp only [NormalForm.ScopedStmt] at h
      exact callsScoped_stmts (funScope_ext hsub body) h
  | _, _, _, hsub, .funDef _ ps rs body, h => by
      simp only [NormalForm.ScopedStmt] at h
      exact callsScoped_stmts (funScope_ext hsub body) h
  | _, _, _, hsub, .cond c body, h => by
      simp only [NormalForm.ScopedStmt] at h
      exact ⟨callsScoped_expr hsub h.1, callsScoped_stmts (funScope_ext hsub body) h.2⟩
  | _, _, _, hsub, .switch c cases dflt, h => by
      simp only [NormalForm.ScopedStmt] at h
      exact ⟨callsScoped_expr hsub h.1, callsScoped_cases hsub h.2.1, callsScoped_dflt hsub h.2.2⟩
  | _, _, _, hsub, .forLoop init c post body, h => by
      simp only [NormalForm.ScopedStmt] at h
      obtain ⟨hi, hc, hp, hb⟩ := h
      have hInit := funScope_ext hsub init
      refine ⟨callsScoped_stmts hInit hi, callsScoped_expr hInit hc,
        callsScoped_stmts (funScope_ext hInit post) hp,
        callsScoped_stmts (funScope_ext hInit body) hb⟩
  | _, _, _, hsub, .letDecl _ (some e), h => by
      simp only [NormalForm.ScopedStmt] at h
      simpa only [Normalization.ScopedStmt] using callsScoped_expr hsub h
  | _, _, _, _, .letDecl _ none, _ => by simp [Normalization.ScopedStmt]
  | _, _, _, hsub, .assign _ e, h => by
      simp only [NormalForm.ScopedStmt] at h
      simpa only [Normalization.ScopedStmt] using callsScoped_expr hsub h.2
  | _, _, _, hsub, .exprStmt e, h => by
      simp only [NormalForm.ScopedStmt] at h
      simpa only [Normalization.ScopedStmt] using callsScoped_expr hsub h
  | _, _, _, _, .«break», _ => by simp [Normalization.ScopedStmt]
  | _, _, _, _, .«continue», _ => by simp [Normalization.ScopedStmt]
  | _, _, _, _, .leave, _ => by simp [Normalization.ScopedStmt]
theorem callsScoped_stmts : ∀ {vs fs scope : List Ident} (_ : ∀ x ∈ fs, x ∈ scope)
    {b : List (Stmt D.Op)}, NormalForm.ScopedStmts vs fs b → Normalization.ScopedStmts scope b
  | _, _, _, _, [], _ => by simp [Normalization.ScopedStmts]
  | _, _, _, hsub, _ :: _, h => by
      simp only [NormalForm.ScopedStmts] at h
      exact ⟨callsScoped_stmt hsub h.1, callsScoped_stmts hsub h.2⟩
theorem callsScoped_cases : ∀ {vs fs scope : List Ident} (_ : ∀ x ∈ fs, x ∈ scope)
    {cs : List (Literal × Block D.Op)},
    NormalForm.ScopedCases vs fs cs → Normalization.ScopedCases scope cs
  | _, _, _, _, [], _ => by simp [Normalization.ScopedCases]
  | _, _, _, hsub, (_, b) :: _, h => by
      simp only [NormalForm.ScopedCases] at h
      exact ⟨callsScoped_stmts (funScope_ext hsub b) h.1, callsScoped_cases hsub h.2⟩
theorem callsScoped_dflt : ∀ {vs fs scope : List Ident} (_ : ∀ x ∈ fs, x ∈ scope)
    {d : Option (Block D.Op)},
    NormalForm.ScopedDflt vs fs d → Normalization.ScopedDflt scope d
  | _, _, _, _, none, _ => by simp [Normalization.ScopedDflt]
  | _, _, _, hsub, some b, h => by
      simp only [NormalForm.ScopedDflt] at h
      exact callsScoped_stmts (funScope_ext hsub b) h
end

/-- **The canonical `WellScoped` implies the hoist pass's function-call
`WellScoped`.** The initial function scopes coincide (`funDefNames = funNamesTop`),
so the inclusion is reflexive at the root. -/
theorem wellScoped_callsScoped {b : Block D.Op} (h : NormalForm.WellScoped b) :
    Normalization.WellScoped b :=
  callsScoped_stmts
    (fun x hx => by rw [funNamesTop_eq_funDefNames]; exact hx) h

end YulEvmCompiler.Optimizer.Normalize
