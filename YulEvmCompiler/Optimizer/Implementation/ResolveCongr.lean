import YulEvmCompiler.Optimizer.Implementation.Simplify
import YulEvmCompiler.ObjectResolve

set_option warningAsError true

/-!
# YulEvmCompiler.Optimizer.Implementation.ResolveCongr

The **resolution congruence** for the `Simplify` pass: layout resolution commutes
with the pass up to semantic equivalence,

```
EquivBlock D (resolveForLayoutStmts L b) (resolveForLayoutStmts L (simplifyStmts b))
```

It holds because expression rewrites avoid `dataoffset`/`datasize`, while
literal control-flow selection commutes with resolving every case/default body.
This is the missing link for the object path: with it, compiling
`simplifyObject o` correctly simulates the **original** object's resolved run
under the compiler's layout (`simplifyObject_correct`, in `ObjectPass`).
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
      | (split_ifs at h;
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
      | (split_ifs at h;
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
  · push Not at hstr
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

/-! ### Resolution commutes with constant control-flow selection -/

/-- Resolving a statically selected switch block is the same as selecting from
the resolved cases/default.  This mirrors the resolver's internal preservation
lemma, restated here because that theorem is private to `ObjectResolve`. -/
theorem resolve_selectSwitch (L : Layout) (value : U256)
    (cases : List (Literal × Block Op)) (dflt : Option (Block Op)) :
    resolveForLayoutStmts L (selectSwitch evm value cases dflt) =
      selectSwitch evm value (resolveForLayoutCases L cases)
        (dflt.map (resolveForLayoutStmts L)) := by
  induction cases with
  | nil => cases dflt <;> simp [selectSwitch, resolveForLayoutCases]
  | cons head rest ih =>
      rcases head with ⟨l, body⟩
      by_cases h : decide (value = litValue l) = true
      · simp [selectSwitch, resolveForLayoutCases, h]
      · simpa [selectSwitch, resolveForLayoutCases, h] using ih

/-- Resolving a folded `if` agrees with resolving its condition/body first and
then executing the original `if`. -/
theorem resolveSimplifyCond_equiv (L : Layout) (c : Expr Op) (body : Block Op) :
    EquivStmt D
      (.cond (resolveForLayoutExpr L c) (resolveForLayoutStmts L body))
      (resolveForLayoutStmt L (simplifyCond c body)) := by
  cases c with
  | lit l =>
      rw [simplifyCond]
      by_cases hz : litValue l = 0
      · rw [if_pos hz]
        simpa only [resolveForLayoutExpr, resolveForLayoutStmt, resolveForLayoutStmts] using
          (cond_lit_zero_equiv (calls := calls) (creates := creates) l
            (resolveForLayoutStmts L body) hz)
      · rw [if_neg hz]
        simpa only [resolveForLayoutExpr, resolveForLayoutStmt] using
          (cond_lit_nonzero_equiv (calls := calls) (creates := creates) l
            (resolveForLayoutStmts L body) hz)
  | var x =>
      simp only [simplifyCond, resolveForLayoutStmt_cond]
      exact EquivStmt.refl _
  | builtin op args =>
      simp only [simplifyCond, resolveForLayoutStmt_cond]
      exact EquivStmt.refl _
  | call fn args =>
      simp only [simplifyCond, resolveForLayoutStmt_cond]
      exact EquivStmt.refl _

/-- Resolving a folded `switch` agrees with resolving its condition/cases first
and then executing the original `switch`. -/
theorem resolveSimplifySwitch_equiv (L : Layout) (c : Expr Op)
    (cases : List (Literal × Block Op)) (dflt : Option (Block Op)) :
    EquivStmt D
      (.switch (resolveForLayoutExpr L c) (resolveForLayoutCases L cases)
        (dflt.map (resolveForLayoutStmts L)))
      (resolveForLayoutStmt L (simplifySwitch c cases dflt)) := by
  cases c with
  | lit l =>
      rw [simplifySwitch]
      simp only [resolveForLayoutStmt]
      rw [resolve_selectSwitch]
      exact switch_lit_equiv (calls := calls) (creates := creates) l
        (resolveForLayoutCases L cases)
        (dflt.map (resolveForLayoutStmts L))
  | var x =>
      simp only [simplifySwitch, resolveForLayoutStmt_switch]
      exact EquivStmt.refl _
  | builtin op args =>
      simp only [simplifySwitch, resolveForLayoutStmt_switch]
      exact EquivStmt.refl _
  | call fn args =>
      simp only [simplifySwitch, resolveForLayoutStmt_switch]
      exact EquivStmt.refl _

/-- A resolved folded `if` still contributes no declaration to its enclosing
hoisted scope. -/
theorem hoist_resolve_simplifyCond_cons (L : Layout) (c : Expr Op)
    (body rest : Block Op) :
    hoist D (resolveForLayoutStmts L (simplifyCond c body :: rest)) =
      hoist D (resolveForLayoutStmts L rest) := by
  cases c with
  | lit l => rw [simplifyCond]; split <;>
      simp [hoist]
  | var _ => simp [simplifyCond, hoist]
  | builtin _ _ => simp [simplifyCond, hoist]
  | call _ _ => simp [simplifyCond, hoist]

/-- A resolved folded `switch` still contributes no declaration to its enclosing
hoisted scope. -/
theorem hoist_resolve_simplifySwitch_cons (L : Layout) (c : Expr Op)
    (cases : List (Literal × Block Op)) (dflt : Option (Block Op)) (rest : Block Op) :
    hoist D (resolveForLayoutStmts L (simplifySwitch c cases dflt :: rest)) =
      hoist D (resolveForLayoutStmts L rest) := by
  cases c <;> simp [simplifySwitch, hoist]

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
      exact (EquivStmt.cond_congr (resolveSimplifyExpr_equiv L c)
        (EquivBlock.of_stmts_funs (EquivStmts.of_forall₂ (resolveSimplifyStmts_forall2 L body))
          (scopeRel_resolveSimplify L body))).trans
        (resolveSimplifyCond_equiv L (simplifyExpr c) (simplifyStmts body))
  | .switch c cases dflt => by
      have hswitch : EquivStmt D
          (.switch (resolveForLayoutExpr L c) (resolveForLayoutCases L cases)
            (dflt.map (resolveForLayoutStmts L)))
          (.switch (resolveForLayoutExpr L (simplifyExpr c))
            (resolveForLayoutCases L (simplifyCases cases))
            ((simplifyDflt dflt).map (resolveForLayoutStmts L))) := by
        apply EquivStmt.switch_congr (resolveSimplifyExpr_equiv L c)
          (resolveSimplifyCases_forall2 L cases)
        cases dflt with
        | none => exact EquivBlock.refl _
        | some b =>
            exact (EquivBlock.of_stmts_funs
              (EquivStmts.of_forall₂ (resolveSimplifyStmts_forall2 L b))
              (scopeRel_resolveSimplify L b))
      simpa only [simplifyStmt, resolveForLayoutStmt_switch] using hswitch.trans
        (resolveSimplifySwitch_equiv L (simplifyExpr c)
          (simplifyCases cases) (simplifyDflt dflt))
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
  | .cond c body :: rest => by
      have hleft : hoist D (resolveForLayoutStmts L (.cond c body :: rest)) =
          hoist D (resolveForLayoutStmts L rest) := by
        simp [hoist]
      rw [hleft, simplifyStmts, simplifyStmt]
      rw [hoist_resolve_simplifyCond_cons]
      exact scopeRel_resolveSimplify L rest
  | .switch c cases dflt :: rest => by
      have hleft : hoist D (resolveForLayoutStmts L (.switch c cases dflt :: rest)) =
          hoist D (resolveForLayoutStmts L rest) := by
        simp [hoist]
      rw [hleft, simplifyStmts, simplifyStmt]
      rw [hoist_resolve_simplifySwitch_cons]
      exact scopeRel_resolveSimplify L rest
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
