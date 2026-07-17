import YulEvmCompiler.Optimizer.Implementation.Simplify
import YulEvmCompiler.ObjectResolve

/-!
# YulEvmCompiler.Optimizer.Implementation.ResolveCongr

The **resolution congruence** for the `Simplify` pass: layout resolution commutes
with the pass up to semantic equivalence,

```
EquivBlock D (resolveForLayoutStmts L b) (resolveForLayoutStmts L (simplifyStmts b))
```

It holds because the pass touches only *pure* ops (folding all-literal
applications) and *neutral* `var`/`lit` operands — node kinds that resolution
leaves alone (resolution rewrites only `dataoffset`/`datasize`). This is the
missing link for the object path: with it, compiling `simplifyObject o` correctly
simulates the **original** object's resolved run under the compiler's layout
(`Pass.optimizeObject_correct`, in `ObjectPass`).
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler (resolveForLayoutExpr resolveForLayoutExprs resolveForLayoutStmt
  resolveForLayoutStmts resolveForLayoutCases)

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### Resolution leaves the pass's rewrite targets alone -/

/-- Resolution is the identity on a list of literals. -/
theorem resolve_lits (L : Layout) (lits : List Literal) :
    resolveForLayoutExprs L (lits.map Expr.lit) = lits.map Expr.lit := by
  induction lits with
  | nil => rfl
  | cons l rest ih => rw [List.map_cons, resolveForLayoutExprs, ih]; rfl

/-- On a non-`dataoffset`/`datasize` built-in, resolution just recurses into args. -/
theorem resolve_builtin_nondata (L : Layout) {op : Op} (args : List (Expr Op))
    (h1 : op ≠ .dataoffset) (h2 : op ≠ .datasize) :
    resolveForLayoutExpr L (.builtin op args) = .builtin op (resolveForLayoutExprs L args) := by
  cases op <;> first
    | (exact absurd rfl h1)
    | (exact absurd rfl h2)
    | rfl

/-- On any built-in whose args are not a lone string literal, resolution just
recurses into the args (neither `dataoffset` nor `datasize` special case fires). -/
theorem resolveForLayoutExpr_builtin_other (L : Layout) (op : Op) (args : List (Expr Op))
    (h : ∀ n, args ≠ [.lit (.string n)]) :
    resolveForLayoutExpr L (.builtin op args) = .builtin op (resolveForLayoutExprs L args) := by
  unfold resolveForLayoutExpr
  split
  · rename_i name; exact absurd rfl (h name)
  · rename_i name; exact absurd rfl (h name)
  · rfl

/-- A folded op is not a layout read. -/
theorem pureFold_nondata {op : Op} {lits : List Literal} {l : Literal}
    (h : pureFold op lits = some l) : op ≠ .dataoffset ∧ op ≠ .datasize := by
  refine ⟨?_, ?_⟩ <;> (rintro rfl; simp [pureFold, pureFn] at h)

/-- A neutral op is not a layout read. -/
theorem neutral_nondata {op : Op} {args : List (Expr Op)} {e : Expr Op}
    (h : neutral op args = some e) : op ≠ .dataoffset ∧ op ≠ .datasize := by
  refine ⟨?_, ?_⟩ <;> (rintro rfl; simp [neutral] at h)

/-- A neutral rewrite always yields a variable. -/
theorem neutral_isVar {op : Op} {args : List (Expr Op)} {e : Expr Op}
    (h : neutral op args = some e) : ∃ x, e = .var x := by
  unfold neutral at h
  split at h <;>
    first
      | contradiction
      | (split_ifs at h <;>
          first
            | contradiction
            | (obtain rfl := Option.some.inj h; exact ⟨_, rfl⟩))

/-- A neutral op's operands (a `var` and a `lit`) and result (a `var`) are all
fixed by resolution. -/
theorem neutral_resolve (L : Layout) {op : Op} {args : List (Expr Op)} {e : Expr Op}
    (h : neutral op args = some e) :
    resolveForLayoutExprs L args = args ∧ resolveForLayoutExpr L e = e := by
  unfold neutral at h
  split at h <;>
    first
      | contradiction
      | (split_ifs at h <;>
          first
            | contradiction
            | (obtain rfl := Option.some.inj h; exact ⟨rfl, rfl⟩))

/-! ### The pass never manufactures a string literal

Folding produces number literals; neutral rewrites produce variables. So a string
literal in the output was already there — which is what preserves the
`dataoffset("name")`/`datasize("name")` shape that resolution keys on. -/

/-- `simplifyBuiltin` never returns a string literal (folds give numbers, neutral
gives variables). -/
theorem simplifyBuiltin_not_stringlit (op : Op) (args : List (Expr Op)) (n : String) :
    simplifyBuiltin op args ≠ .lit (.string n) := by
  unfold simplifyBuiltin
  split
  · rename_i l hb
    rw [Option.bind_eq_some_iff] at hb
    obtain ⟨lits, _, hf⟩ := hb
    rw [pureFold, Option.map_eq_some_iff] at hf
    obtain ⟨w, _, rfl⟩ := hf
    simp
  · cases hn : neutral op args with
    | none => simp
    | some e => obtain ⟨x, rfl⟩ := neutral_isVar hn; simp

theorem simplifyExpr_stringlit {e : Expr Op} {n : String}
    (h : simplifyExpr e = .lit (.string n)) : e = .lit (.string n) := by
  cases e with
  | lit l => rw [simplifyExpr] at h; exact h
  | var x => rw [simplifyExpr] at h; exact absurd h (by simp)
  | call f args => rw [simplifyExpr] at h; exact absurd h (by simp)
  | builtin op args =>
      rw [simplifyExpr] at h
      exact absurd h (simplifyBuiltin_not_stringlit op (simplifyArgs args) n)

theorem simplifyArgs_stringlit {args : List (Expr Op)} {n : String}
    (h : simplifyArgs args = [.lit (.string n)]) : args = [.lit (.string n)] := by
  cases args with
  | nil => rw [simplifyArgs] at h; exact absurd h (by simp)
  | cons a rest =>
      rw [simplifyArgs] at h
      simp only [List.cons.injEq] at h
      obtain ⟨ha, hrest⟩ := h
      have hnil : rest = [] := by
        cases rest with
        | nil => rfl
        | cons _ _ => rw [simplifyArgs] at hrest; exact absurd hrest (by simp)
      subst hnil
      rw [simplifyExpr_stringlit ha]

/-! ### The local built-in rewrite commutes with resolution -/

theorem resolveSimplifyBuiltin_equiv (L : Layout) (op : Op) (args : List (Expr Op)) :
    EquivExpr D (resolveForLayoutExpr L (.builtin op args))
      (resolveForLayoutExpr L (simplifyBuiltin op args)) := by
  unfold simplifyBuiltin
  split
  · -- constant folding
    rename_i l hbind
    rw [Option.bind_eq_some_iff] at hbind
    obtain ⟨lits, hlits, hfold⟩ := hbind
    obtain ⟨hd1, hd2⟩ := pureFold_nondata hfold
    rw [asLits_map hlits, resolve_builtin_nondata L _ hd1 hd2, resolve_lits]
    exact fold_equiv hfold
  · cases hn : neutral op args with
    | none => exact EquivExpr.refl _
    | some e =>
        obtain ⟨hd1, hd2⟩ := neutral_nondata hn
        obtain ⟨hargs, he⟩ := neutral_resolve L hn
        simp only [Option.getD_some]
        rw [resolve_builtin_nondata L _ hd1 hd2, hargs, he]
        exact neutral_equiv hn

/-- Simplifying a built-in's arguments commutes with resolution up to equivalence
(the `dataoffset`/`datasize` string-literal shape is preserved by the pass). -/
theorem resolve_builtin_argEquiv (L : Layout) (op : Op) (args : List (Expr Op))
    (hargs : List.Forall₂ (EquivExpr D) (resolveForLayoutExprs L args)
      (resolveForLayoutExprs L (simplifyArgs args))) :
    EquivExpr D (resolveForLayoutExpr L (.builtin op args))
      (resolveForLayoutExpr L (.builtin op (simplifyArgs args))) := by
  by_cases hstr : ∃ n, args = [.lit (.string n)]
  · obtain ⟨n, rfl⟩ := hstr
    have h : simplifyArgs [Expr.lit (.string n)] = [Expr.lit (.string n)] := rfl
    rw [h]; exact EquivExpr.refl _
  · push_neg at hstr
    have hstr' : ∀ n, simplifyArgs args ≠ [.lit (.string n)] :=
      fun n hc => hstr n (simplifyArgs_stringlit hc)
    rw [resolveForLayoutExpr_builtin_other L op args hstr,
        resolveForLayoutExpr_builtin_other L op (simplifyArgs args) hstr']
    exact EquivExpr.builtin_congr op (EquivArgs.of_forall₂ hargs)

/-! ### The resolution congruence — expressions and arguments -/

mutual

/-- Resolution commutes with `simplifyExpr` up to equivalence. -/
theorem resolveSimplifyExpr_equiv (L : Layout) : ∀ e : Expr Op,
    EquivExpr D (resolveForLayoutExpr L e) (resolveForLayoutExpr L (simplifyExpr e))
  | .lit _ => EquivExpr.refl _
  | .var _ => EquivExpr.refl _
  | .builtin op args => by
      rw [simplifyExpr]
      exact (resolve_builtin_argEquiv L op args (resolveSimplifyArgs_forall2 L args)).trans
        (resolveSimplifyBuiltin_equiv L op (simplifyArgs args))
  | .call f args => by
      rw [simplifyExpr, resolveForLayoutExpr, resolveForLayoutExpr]
      exact EquivExpr.call_congr f (EquivArgs.of_forall₂ (resolveSimplifyArgs_forall2 L args))

/-- Resolution commutes with `simplifyArgs` up to pairwise equivalence. -/
theorem resolveSimplifyArgs_forall2 (L : Layout) : ∀ args : List (Expr Op),
    List.Forall₂ (EquivExpr D) (resolveForLayoutExprs L args)
      (resolveForLayoutExprs L (simplifyArgs args))
  | [] => .nil
  | e :: rest => by
      rw [simplifyArgs, resolveForLayoutExprs, resolveForLayoutExprs]
      exact .cons (resolveSimplifyExpr_equiv L e) (resolveSimplifyArgs_forall2 L rest)

end

/-! ### The resolution congruence — statements and blocks -/

mutual

/-- Resolution commutes with `simplifyStmt` up to equivalence. -/
theorem resolveSimplifyStmt_equiv (L : Layout) : ∀ s : Stmt Op,
    EquivStmt D (resolveForLayoutStmt L s) (resolveForLayoutStmt L (simplifyStmt s))
  | .block body => by
      simp only [simplifyStmt, resolveForLayoutStmt]
      exact EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (resolveSimplifyStmts_forall2 L body))
        (scopeRel_resolveSimplify L body)
  | .funDef n ps rs body => by
      simp only [simplifyStmt, resolveForLayoutStmt]
      exact funDef_equiv n ps rs (resolveForLayoutStmts L body)
        (resolveForLayoutStmts L (simplifyStmts body))
  | .letDecl names (some e) => by
      simp only [simplifyStmt, resolveForLayoutStmt, Option.map_some]
      exact EquivStmt.letDecl_congr _ (resolveSimplifyExpr_equiv L e)
  | .letDecl names none => EquivStmt.refl _
  | .assign names e => by
      simp only [simplifyStmt, resolveForLayoutStmt]
      exact EquivStmt.assign_congr _ (resolveSimplifyExpr_equiv L e)
  | .cond c body => by
      simp only [simplifyStmt, resolveForLayoutStmt]
      exact EquivStmt.cond_congr (resolveSimplifyExpr_equiv L c)
        (EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (resolveSimplifyStmts_forall2 L body))
          (scopeRel_resolveSimplify L body))
  | .switch c cases dflt => by
      simp only [simplifyStmt, resolveForLayoutStmt_switch]
      cases dflt with
      | none =>
          refine EquivStmt.switch_congr (resolveSimplifyExpr_equiv L c)
            (resolveSimplifyCases_forall2 L cases) ?_
          exact EquivBlock.refl _
      | some b =>
          simp only [simplifyDflt]
          refine EquivStmt.switch_congr (resolveSimplifyExpr_equiv L c)
            (resolveSimplifyCases_forall2 L cases) ?_
          exact EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (resolveSimplifyStmts_forall2 L b))
            (scopeRel_resolveSimplify L b)
  | .forLoop init c post body => by
      simp only [simplifyStmt, resolveForLayoutStmt]
      exact EquivStmt.forLoop_congr (resolveForLayoutStmts L init) (resolveSimplifyExpr_equiv L c)
        (EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (resolveSimplifyStmts_forall2 L post))
          (scopeRel_resolveSimplify L post))
        (EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (resolveSimplifyStmts_forall2 L body))
          (scopeRel_resolveSimplify L body))
  | .exprStmt e => by
      simp only [simplifyStmt, resolveForLayoutStmt]
      exact EquivStmt.exprStmt_congr (resolveSimplifyExpr_equiv L e)
  | .break => EquivStmt.refl _
  | .continue => EquivStmt.refl _
  | .leave => EquivStmt.refl _

/-- Resolution commutes with `simplifyStmts` up to pairwise equivalence. -/
theorem resolveSimplifyStmts_forall2 (L : Layout) : ∀ ss : List (Stmt Op),
    List.Forall₂ (EquivStmt D) (resolveForLayoutStmts L ss)
      (resolveForLayoutStmts L (simplifyStmts ss))
  | [] => by simp only [simplifyStmts, resolveForLayoutStmts]; exact .nil
  | s :: rest => by
      simp only [simplifyStmts, resolveForLayoutStmts]
      exact .cons (resolveSimplifyStmt_equiv L s) (resolveSimplifyStmts_forall2 L rest)

/-- Resolution commutes with `simplifyCases` up to pairwise (label-equal,
body-equivalent) relation. -/
theorem resolveSimplifyCases_forall2 (L : Layout) : ∀ cs : List (Literal × Block Op),
    List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock D p.2 q.2)
      (resolveForLayoutCases L cs) (resolveForLayoutCases L (simplifyCases cs))
  | [] => by simp only [simplifyCases, resolveForLayoutCases]; exact .nil
  | (l, b) :: rest => by
      simp only [simplifyCases, resolveForLayoutCases]
      exact .cons ⟨rfl, EquivBlock.of_stmts_funs
        (EquivStmts.of_forall₂ (resolveSimplifyStmts_forall2 L b)) (scopeRel_resolveSimplify L b)⟩
        (resolveSimplifyCases_forall2 L rest)

/-- The hoisted scope of the resolved block maps to a `ScopeRel`-related one — the
side condition needed to lift the block congruence through `of_stmts_funs`. -/
theorem scopeRel_resolveSimplify (L : Layout) : ∀ ss : List (Stmt Op),
    ScopeRel D (hoist D (resolveForLayoutStmts L ss))
      (hoist D (resolveForLayoutStmts L (simplifyStmts ss)))
  | [] => by simp only [simplifyStmts, resolveForLayoutStmts, hoist]; exact .nil
  | .funDef n ps rs body :: rest => by
      simp only [simplifyStmts, simplifyStmt, resolveForLayoutStmts, resolveForLayoutStmt,
        hoist, List.filterMap_cons]
      exact .cons ⟨rfl, rfl, rfl, EquivBlock.of_stmts_funs
        (EquivStmts.of_forall₂ (resolveSimplifyStmts_forall2 L body))
        (scopeRel_resolveSimplify L body)⟩ (scopeRel_resolveSimplify L rest)
  | .block _ :: rest => by
      simp only [simplifyStmts, simplifyStmt, resolveForLayoutStmts, resolveForLayoutStmt,
        hoist, List.filterMap_cons]; exact scopeRel_resolveSimplify L rest
  | .letDecl _ (some _) :: rest => by
      simp only [simplifyStmts, simplifyStmt, resolveForLayoutStmts, resolveForLayoutStmt,
        hoist, List.filterMap_cons]; exact scopeRel_resolveSimplify L rest
  | .letDecl _ none :: rest => by
      simp only [simplifyStmts, simplifyStmt, resolveForLayoutStmts, resolveForLayoutStmt,
        hoist, List.filterMap_cons]; exact scopeRel_resolveSimplify L rest
  | .assign _ _ :: rest => by
      simp only [simplifyStmts, simplifyStmt, resolveForLayoutStmts, resolveForLayoutStmt,
        hoist, List.filterMap_cons]; exact scopeRel_resolveSimplify L rest
  | .cond _ _ :: rest => by
      simp only [simplifyStmts, simplifyStmt, resolveForLayoutStmts, resolveForLayoutStmt,
        hoist, List.filterMap_cons]; exact scopeRel_resolveSimplify L rest
  | .switch _ _ _ :: rest => by
      simp only [simplifyStmts, simplifyStmt, resolveForLayoutStmts, resolveForLayoutStmt_switch,
        hoist, List.filterMap_cons]; exact scopeRel_resolveSimplify L rest
  | .forLoop _ _ _ _ :: rest => by
      simp only [simplifyStmts, simplifyStmt, resolveForLayoutStmts, resolveForLayoutStmt,
        hoist, List.filterMap_cons]; exact scopeRel_resolveSimplify L rest
  | .exprStmt _ :: rest => by
      simp only [simplifyStmts, simplifyStmt, resolveForLayoutStmts, resolveForLayoutStmt,
        hoist, List.filterMap_cons]; exact scopeRel_resolveSimplify L rest
  | .break :: rest => by
      simp only [simplifyStmts, simplifyStmt, resolveForLayoutStmts, resolveForLayoutStmt,
        hoist, List.filterMap_cons]; exact scopeRel_resolveSimplify L rest
  | .continue :: rest => by
      simp only [simplifyStmts, simplifyStmt, resolveForLayoutStmts, resolveForLayoutStmt,
        hoist, List.filterMap_cons]; exact scopeRel_resolveSimplify L rest
  | .leave :: rest => by
      simp only [simplifyStmts, simplifyStmt, resolveForLayoutStmts, resolveForLayoutStmt,
        hoist, List.filterMap_cons]; exact scopeRel_resolveSimplify L rest

end

/-- **Resolution congruence for `Simplify`.** Layout resolution commutes with the
pass up to semantic equivalence, at the block level. -/
theorem resolveSimplifyBlock_equiv (L : Layout) (b : List (Stmt Op)) :
    EquivBlock D (resolveForLayoutStmts L b) (resolveForLayoutStmts L (simplifyStmts b)) :=
  EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (resolveSimplifyStmts_forall2 L b))
    (scopeRel_resolveSimplify L b)

end YulEvmCompiler.Optimizer
