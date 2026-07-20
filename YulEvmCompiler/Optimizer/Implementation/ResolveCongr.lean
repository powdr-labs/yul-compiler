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

It holds because expression rewrites avoid `dataoffset`/`datasize`, literal
control-flow selection commutes with resolving every case/default body, and the
`iszero(eq(x,x))` validator pattern contains only resolution-fixed operations
and variables.
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

/-! ### Resolution leaves the pass's Core rewrite targets alone -/

/-- On a non-`dataoffset`/`datasize` built-in, resolution just recurses into args. -/
theorem resolve_builtin_nondata (L : Layout) {op : Op} (args : List (Expr Op))
    (h1 : op ≠ .dataoffset) (h2 : op ≠ .datasize) :
    resolveForLayoutExpr L (.builtin op args) = .builtin op (resolveForLayoutExprs L args) := by
  cases op <;> first
    | (exact absurd rfl h1)
    | (exact absurd rfl h2)
    | rfl

/-! ### Resolution is the identity on Core terms

The Core type admits only literals, scoped variables, and typed pure operations;
layout reads are unrepresentable.  Consequently resolution is structurally the
identity before and after any Core rule. -/

theorem Core.resolveValue (L : Layout) (value : Core.Value Γ) :
    resolveForLayoutExpr L value.emit = value.emit := by
  cases value <;> rfl

theorem Core.resolveArgs (L : Layout) (args : Core.Args Γ arity) :
    resolveForLayoutExprs L args.emit = args.emit := by
  have helper : ∀ values : List (Core.Value Γ),
      resolveForLayoutExprs L (values.map Core.Value.emit) =
        values.map Core.Value.emit := by
    intro values
    induction values with
    | nil => rfl
    | cons value rest ih =>
        simp only [List.map_cons, resolveForLayoutExprs]
        rw [Core.resolveValue L value, ih]
  exact helper args.values

theorem Core.resolveTerm (L : Layout) (term : Core.Term Γ outputs) :
    resolveForLayoutExpr L term.emit = term.emit := by
  cases term with
  | atom value => exact Core.resolveValue L value
  | builtin op args =>
      rw [Core.Term.emit, resolve_builtin_nondata L args.emit]
      · rw [Core.resolveArgs L args]
      · cases op <;> simp [Core.PureOp.toOp]
      · cases op <;> simp [Core.PureOp.toOp]

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

/-! ### The pass never manufactures a string literal

Folding produces number literals; neutral rewrites produce variables. So a string
literal in the output was already there — which is what preserves the
`dataoffset("name")`/`datasize("name")` shape that resolution keys on. -/

/-- `simplifyBuiltin` never returns a string literal: Core either retains the
input built-in, folds to a number, or returns a variable; syntax outside Core
is unchanged. -/
theorem simplifyBuiltin_not_stringlit (op : Op) (args : List (Expr Op)) (n : String) :
    simplifyBuiltin op args ≠ .lit (.string n) := by
  simp only [simplifyBuiltin]
  cases hcore : Core.ingestSelf (Expr.builtin op args) with
  | none => simp
  | some core =>
      intro hstring
      change (Core.simplifyTerm core).emit = .lit (.string n) at hstring
      rcases Core.simplifyTerm_shape core with hsame | hnumber | hvar
      · rw [hsame] at hstring
        have herase := Core.ingestSelf_emit hcore
        rw [herase] at hstring
        simp at hstring
      · obtain ⟨value, hvalue⟩ := hnumber
        rw [hvalue] at hstring
        simp [Core.Term.emit, Core.Value.emit] at hstring
      · obtain ⟨ref, href⟩ := hvar
        rw [href] at hstring
        simp [Core.Term.emit, Core.Value.emit] at hstring

theorem simplifyExpr_stringlit {e : Expr Op} {n : String}
    (h : simplifyExpr e = .lit (.string n)) : e = .lit (.string n) := by
  cases e with
  | lit l => rw [simplifyExpr] at h; exact h
  | var x => rw [simplifyExpr] at h; exact absurd h (by simp)
  | call f args => rw [simplifyExpr] at h; exact absurd h (by simp)
  | builtin op args =>
      rw [simplifyExpr] at h
      exact absurd h (simplifyBuiltin_not_stringlit op (simplifyArgs args) n)

/-- A successful open-operand rewrite returns an allowed survivor. -/
theorem openNeutral_survivorOK {op : Op} {args : List (Expr Op)} {e : Expr Op}
    (h : openNeutral op args = some e) : survivorOK e = true := by
  unfold openNeutral at h
  split at h <;>
    first
      | contradiction
      | (split_ifs at h with hc
         · obtain rfl := Option.some.inj h; exact hc.2)

/-- The top-level open-operand rewrite never manufactures a string literal
(the survivor fence `survivorOK`). -/
theorem openTop_stringlit {e : Expr Op} {n : String}
    (h : openTop e = .lit (.string n)) : e = .lit (.string n) := by
  cases e with
  | lit l => simpa [openTop] using h
  | var x => simp [openTop] at h
  | call f args => simp [openTop] at h
  | builtin op args =>
      rw [openTop] at h
      cases hn : openNeutral op args with
      | none => rw [hn] at h; simp at h
      | some e' =>
          rw [hn] at h
          simp only [Option.getD_some] at h
          subst h
          have := openNeutral_survivorOK hn
          simp [survivorOK] at this

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
      rw [simplifyExpr_stringlit (openTop_stringlit ha)]

/-! ### The local built-in rewrite commutes with resolution -/

/-- Core simplification commutes with resolution because every Core term is
layout-independent; unsupported syntax is unchanged. -/
theorem resolveSimplifyBuiltin_equiv (L : Layout) (op : Op) (args : List (Expr Op)) :
    EquivExpr D (resolveForLayoutExpr L (.builtin op args))
      (resolveForLayoutExpr L (simplifyBuiltin op args)) := by
  simp only [simplifyBuiltin]
  cases hcore : Core.ingestSelf (Expr.builtin op args) with
  | none => exact EquivExpr.refl _
  | some core =>
      have herase := Core.ingestSelf_emit hcore
      have hleft : resolveForLayoutExpr L (.builtin op args) = core.emit :=
        (congrArg (resolveForLayoutExpr L) herase.symm).trans (Core.resolveTerm L core)
      have hright : resolveForLayoutExpr L (Core.simplifyTerm core).emit =
          (Core.simplifyTerm core).emit := Core.resolveTerm L (Core.simplifyTerm core)
      rw [hleft, hright]
      exact Core.simplifyTerm_sound core

/-- Resolution pushes into a two-argument built-in pointwise (the
`dataoffset`/`datasize` special shape is single-argument). -/
theorem resolve_two_args (L : Layout) (op : Op) (a b : Expr Op) :
    resolveForLayoutExpr L (.builtin op [a, b]) =
      .builtin op [resolveForLayoutExpr L a, resolveForLayoutExpr L b] := by
  rw [resolveForLayoutExpr_builtin_other L op [a, b] (by intro n; simp)]
  rfl

@[simp] theorem resolve_lit (L : Layout) (c : Literal) :
    resolveForLayoutExpr L (.lit c) = .lit c := rfl

/-- **Resolution respects the open-operand rewrite, value-restrictedly.** The
proof re-runs the per-pattern neutral-element soundness at the *resolved*
operands. It deliberately does not re-match `openNeutral` on the resolved
arguments: resolution can turn the surviving operand into a literal, changing
which pattern (if any) would fire — but the fired rule's algebraic fact holds
at resolved operands regardless. -/
theorem resolve_openTop_equiv1 (L : Layout) (e : Expr Op) :
    EquivExpr1 (calls := calls) (creates := creates)
      (resolveForLayoutExpr L e) (resolveForLayoutExpr L (openTop e)) := by
  cases e with
  | lit _ => exact EquivExpr1.refl _
  | var _ => exact EquivExpr1.refl _
  | call _ _ => exact EquivExpr1.refl _
  | builtin op args =>
      rw [openTop]
      cases hn : openNeutral op args with
      | none => exact EquivExpr1.refl _
      | some e' =>
          simp only [Option.getD_some]
          unfold openNeutral at hn
          split at hn <;>
            first
              | contradiction
              | (split_ifs at hn with hc
                 · obtain rfl := Option.some.inj hn
                   simp only [resolve_two_args, resolve_lit]
                   first
                     | exact open_right_equiv1 (fun v => by
                         rw [hc.1]; simp only [pureFn, Option.some.injEq]
                         first | simp | (rw [allOnes]; exact BitVec.and_allOnes))
                     | exact open_left_equiv1 (fun v => by
                         rw [hc.1]; simp only [pureFn, Option.some.injEq]
                         first | simp | (rw [allOnes]; exact BitVec.allOnes_and)))

/-- Simplifying a built-in's arguments commutes with resolution up to equivalence
(the `dataoffset`/`datasize` string-literal shape is preserved by the pass). -/
theorem resolve_builtin_argEquiv (L : Layout) (op : Op) (args : List (Expr Op))
    (hargs : EquivArgs D (resolveForLayoutExprs L args)
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
    exact EquivExpr.builtin_congr op hargs

/-! ### The resolution congruence — expressions and arguments -/

mutual

/-- Resolution commutes with `simplifyExpr` up to equivalence. -/
theorem resolveSimplifyExpr_equiv (L : Layout) : ∀ e : Expr Op,
    EquivExpr D (resolveForLayoutExpr L e) (resolveForLayoutExpr L (simplifyExpr e))
  | .lit _ => EquivExpr.refl _
  | .var _ => EquivExpr.refl _
  | .builtin op args => by
      rw [simplifyExpr]
      exact (resolve_builtin_argEquiv L op args (resolveSimplifyArgs_equivArgs L args)).trans
        (resolveSimplifyBuiltin_equiv L op (simplifyArgs args))
  | .call f args => by
      rw [simplifyExpr, resolveForLayoutExpr, resolveForLayoutExpr]
      exact EquivExpr.call_congr f (resolveSimplifyArgs_equivArgs L args)

/-- Resolution commutes with `simplifyArgs` up to argument-list equivalence.
Elements carry the open-operand rewrite, related only value-restrictedly; the
argument context lifts that to full list equivalence (`EquivArgs.cons1`). -/
theorem resolveSimplifyArgs_equivArgs (L : Layout) : ∀ args : List (Expr Op),
    EquivArgs D (resolveForLayoutExprs L args)
      (resolveForLayoutExprs L (simplifyArgs args))
  | [] => EquivArgs.refl _
  | e :: rest => by
      rw [simplifyArgs, resolveForLayoutExprs, resolveForLayoutExprs]
      exact EquivArgs.cons1
        (EquivExpr1.trans (EquivExpr.toEquivExpr1 (resolveSimplifyExpr_equiv L e))
          (resolve_openTop_equiv1 L (simplifyExpr e)))
        (resolveSimplifyArgs_equivArgs L rest)

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
      simp only [simplifyCond, selfEqVar?, resolveForLayoutStmt_cond]
      exact fun _ _ _ _ _ _ => Iff.rfl
  | builtin op args =>
      cases hself : selfEqVar? (.builtin op args) with
      | none =>
          simp only [simplifyCond, hself, resolveForLayoutStmt_cond]
          exact fun _ _ _ _ _ _ => Iff.rfl
      | some x =>
          have hshape := selfEqVar?_some hself
          rw [hshape]
          simpa [simplifyCond, selfEqVar?, resolveForLayoutExpr,
            resolveForLayoutExprs, resolveForLayoutStmt] using
            (cond_selfEq_equiv (calls := calls) (creates := creates) x
              (resolveForLayoutStmts L body))
  | call fn args =>
      simp only [simplifyCond, selfEqVar?, resolveForLayoutStmt_cond]
      exact fun _ _ _ _ _ _ => Iff.rfl

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
  | var _ => simp [simplifyCond, selfEqVar?, hoist]
  | builtin op args =>
      cases hself : selfEqVar? (.builtin op args) <;>
        simp [simplifyCond, hself, hoist]
  | call _ _ => simp [simplifyCond, selfEqVar?, hoist]

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
  | .letDecl [x] (some e) => by
      simp only [simplifyStmt, resolveForLayoutStmt, Option.map_some]
      exact (EquivStmt.letDecl_congr _ (resolveSimplifyExpr_equiv L e)).trans
        (EquivStmt.letDecl1_congr (resolve_openTop_equiv1 L (simplifyExpr e)))
  | .letDecl [] (some e) => by
      simp only [simplifyStmt, resolveForLayoutStmt, Option.map_some]
      exact EquivStmt.letDecl_congr _ (resolveSimplifyExpr_equiv L e)
  | .letDecl (_ :: _ :: _) (some e) => by
      simp only [simplifyStmt, resolveForLayoutStmt, Option.map_some]
      exact EquivStmt.letDecl_congr _ (resolveSimplifyExpr_equiv L e)
  | .letDecl [_] none => EquivStmt.refl _
  | .letDecl [] none => EquivStmt.refl _
  | .letDecl (_ :: _ :: _) none => EquivStmt.refl _
  | .assign [x] e => by
      simp only [simplifyStmt, resolveForLayoutStmt]
      exact (EquivStmt.assign_congr _ (resolveSimplifyExpr_equiv L e)).trans
        (EquivStmt.assign1_congr (resolve_openTop_equiv1 L (simplifyExpr e)))
  | .assign [] e => by
      simp only [simplifyStmt, resolveForLayoutStmt]
      exact EquivStmt.assign_congr _ (resolveSimplifyExpr_equiv L e)
  | .assign (_ :: _ :: _) e => by
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
  | .letDecl [_] (some _) :: rest => by
      simp only [simplifyStmts, simplifyStmt, resolveForLayoutStmts, resolveForLayoutStmt,
        hoist, List.filterMap_cons]; exact scopeRel_resolveSimplify L rest
  | .letDecl [] (some _) :: rest => by
      simp only [simplifyStmts, simplifyStmt, resolveForLayoutStmts, resolveForLayoutStmt,
        hoist, List.filterMap_cons]; exact scopeRel_resolveSimplify L rest
  | .letDecl (_ :: _ :: _) (some _) :: rest => by
      simp only [simplifyStmts, simplifyStmt, resolveForLayoutStmts, resolveForLayoutStmt,
        hoist, List.filterMap_cons]; exact scopeRel_resolveSimplify L rest
  | .letDecl [_] none :: rest => by
      simp only [simplifyStmts, simplifyStmt, resolveForLayoutStmts, resolveForLayoutStmt,
        hoist, List.filterMap_cons]; exact scopeRel_resolveSimplify L rest
  | .letDecl [] none :: rest => by
      simp only [simplifyStmts, simplifyStmt, resolveForLayoutStmts, resolveForLayoutStmt,
        hoist, List.filterMap_cons]; exact scopeRel_resolveSimplify L rest
  | .letDecl (_ :: _ :: _) none :: rest => by
      simp only [simplifyStmts, simplifyStmt, resolveForLayoutStmts, resolveForLayoutStmt,
        hoist, List.filterMap_cons]; exact scopeRel_resolveSimplify L rest
  | .assign [_] _ :: rest => by
      simp only [simplifyStmts, simplifyStmt, resolveForLayoutStmts, resolveForLayoutStmt,
        hoist, List.filterMap_cons]; exact scopeRel_resolveSimplify L rest
  | .assign [] _ :: rest => by
      simp only [simplifyStmts, simplifyStmt, resolveForLayoutStmts, resolveForLayoutStmt,
        hoist, List.filterMap_cons]; exact scopeRel_resolveSimplify L rest
  | .assign (_ :: _ :: _) _ :: rest => by
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
