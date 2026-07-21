import YulEvmCompiler.Optimizer.Implementation.Propagate
import YulEvmCompiler.Optimizer.Implementation.ResolveCongr
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.PropagateResolve

**The propagation relation is closed under object-layout resolution** — the
object-path bridge for the `Propagate` pass.

There is no syntactic commutation `resolve ∘ prop = prop ∘ resolve`: resolution
*creates* number literals from `dataoffset`/`datasize` calls, so the transform
acts at more sites on resolved code. The relation absorbs exactly this
mismatch through its skip rules: this file proves, by a purely syntactic
induction over `PropRel` derivations, that resolving both sides of a related
pair yields a related pair — with the *same* tracked environments, because
every classified shape (number literal, bare variable) and every substituted
occurrence is preserved verbatim by resolution, and write sets are structural.

The payoff `resolvePropagateBlock_equiv` is the resolution congruence the
whole-tree object correctness theorem composes with: the resolved source block
is `EquivBlock`-equivalent to the resolved propagated block, via the semantic
simulation applied to the resolved derivation of the relation.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### Resolution commutes with substitution -/

/-- A classifiable expression (number literal or variable) resolves to itself. -/
theorem classify_resolve {e : Expr Op} {r : PRhs} (h : classify e = some r)
    (L : Layout) : resolveForLayoutExpr L e = e := by
  cases r with
  | lit n => rw [classify_lit h]; rfl
  | var y => rw [classify_var h]; rfl

/-- Tracked right-hand sides resolve to themselves. -/
theorem toExpr_resolve (r : PRhs) (L : Layout) :
    resolveForLayoutExpr L (PRhs.toExpr r) = PRhs.toExpr r := by
  cases r <;> rfl

/-- Substitution never produces a lone-string-literal argument list from one
that was not (tracked entries carry only number literals and variables). -/
theorem substArgs_stringlit_inv {σ : PEnv} {args : List (Expr Op)} {n : String}
    (h : substArgs σ args = [.lit (.string n)]) : args = [.lit (.string n)] := by
  cases args with
  | nil => rw [substArgs] at h; cases h
  | cons e rest =>
      cases rest with
      | cons _ _ => simp [substArgs] at h
      | nil =>
          rw [substArgs, substArgs] at h
          injection h with h1
          cases e with
          | lit l =>
              rw [substExpr] at h1
              injection h1 with h2
              rw [h2]
          | var x =>
              rw [substExpr] at h1
              cases hlook : lookupEnv σ x with
              | none => rw [hlook] at h1; cases h1
              | some r =>
                  rw [hlook] at h1
                  cases r <;> simp [PRhs.toExpr] at h1
          | builtin _ _ => rw [substExpr] at h1; cases h1
          | call _ _ => rw [substExpr] at h1; cases h1

mutual

/-- Resolution commutes with substitution: tracked environments carry only
number literals and variables, which resolution preserves, and substitution
neither creates nor destroys the `dataoffset`/`datasize` pattern. -/
theorem resolve_substExpr (L : Layout) (σ : PEnv) :
    ∀ e : Expr Op, resolveForLayoutExpr L (substExpr σ e) =
      substExpr σ (resolveForLayoutExpr L e)
  | .lit l => rfl
  | .var x => by
      rw [substExpr]
      show resolveForLayoutExpr L _ = substExpr σ (.var x)
      rw [substExpr]
      cases lookupEnv σ x with
      | none => rfl
      | some r => exact toExpr_resolve r L
  | .builtin op args => by
      by_cases hop : op = .dataoffset ∨ op = .datasize
      · by_cases hstr : ∃ n, args = [.lit (.string n)]
        · obtain ⟨n, rfl⟩ := hstr
          have hsub : substArgs σ [.lit (.string n)] = [.lit (.string n)] := rfl
          rw [substExpr, hsub]
          have hshape : resolveForLayoutExpr L (.builtin op [.lit (.string n)]) =
              .lit (.number ((L.dataOffset (litValue (.string n))).toNat)) ∨
              resolveForLayoutExpr L (.builtin op [.lit (.string n)]) =
              .lit (.number ((L.dataSize (litValue (.string n))).toNat)) := by
            rcases hop with rfl | rfl
            · left; rfl
            · right; rfl
          rcases hshape with hshape | hshape <;> rw [hshape] <;> rfl
        · rw [not_exists] at hstr
          have hstr' : ∀ m, substArgs σ args ≠ [.lit (.string m)] := by
            intro m hcontra
            exact hstr m (substArgs_stringlit_inv hcontra)
          rw [substExpr, resolveForLayoutExpr_builtin_other L op _ hstr',
              resolveForLayoutExpr_builtin_other L op _ hstr, substExpr,
              resolve_substArgs L σ args]
      · rw [not_or] at hop
        rw [substExpr, resolve_builtin_nondata L _ hop.1 hop.2,
            resolve_builtin_nondata L _ hop.1 hop.2, substExpr,
            resolve_substArgs L σ args]
  | .call f args => by
      rw [substExpr]
      show Expr.call f (resolveForLayoutExprs L (substArgs σ args)) = _
      rw [show resolveForLayoutExpr L (.call f args) =
            .call f (resolveForLayoutExprs L args) from rfl,
          substExpr, resolve_substArgs L σ args]

/-- Argument-list version of `resolve_substExpr`. -/
theorem resolve_substArgs (L : Layout) (σ : PEnv) :
    ∀ es : List (Expr Op), resolveForLayoutExprs L (substArgs σ es) =
      substArgs σ (resolveForLayoutExprs L es)
  | [] => rfl
  | e :: rest => by
      rw [substArgs]
      show resolveForLayoutExpr L (substExpr σ e) ::
          resolveForLayoutExprs L (substArgs σ rest) = _
      rw [resolve_substExpr L σ e, resolve_substArgs L σ rest]
      rfl

end

/-! ### Resolution preserves write sets -/

mutual

theorem writeSet_resolveStmt (L : Layout) :
    ∀ s : Stmt Op, writeSetStmt (resolveForLayoutStmt L s) = writeSetStmt s
  | .block body => by
      rw [resolveForLayoutStmt_block]
      show writeSetStmts (resolveForLayoutStmts L body) = writeSetStmts body
      exact writeSet_resolveStmts L body
  | .funDef n ps rs body => by rw [resolveForLayoutStmt_funDef]; rfl
  | .letDecl xs v => by rw [resolveForLayoutStmt_letDecl]; rfl
  | .assign xs e => by rw [resolveForLayoutStmt_assign]; rfl
  | .cond c body => by
      rw [resolveForLayoutStmt_cond]
      show writeSetStmts (resolveForLayoutStmts L body) = writeSetStmts body
      exact writeSet_resolveStmts L body
  | .switch c cases dflt => by
      rw [resolveForLayoutStmt_switch]
      show writeSetCases (resolveForLayoutCases L cases) ++
          writeSetDflt (dflt.map (resolveForLayoutStmts L)) =
        writeSetCases cases ++ writeSetDflt dflt
      rw [writeSet_resolveCases L cases]
      cases dflt with
      | none => rfl
      | some b =>
          show _ ++ writeSetStmts (resolveForLayoutStmts L b) = _
          rw [writeSet_resolveStmts L b]
          rfl
  | .forLoop init c post body => by
      rw [resolveForLayoutStmt_forLoop]
      show writeSetStmts (resolveForLayoutStmts L init) ++
          writeSetStmts (resolveForLayoutStmts L post) ++
          writeSetStmts (resolveForLayoutStmts L body) = _
      rw [writeSet_resolveStmts L init, writeSet_resolveStmts L post,
          writeSet_resolveStmts L body]
      rfl
  | .exprStmt e => by rw [resolveForLayoutStmt_exprStmt]; rfl
  | .break => by rw [resolveForLayoutStmt_break]
  | .continue => by rw [resolveForLayoutStmt_continue]
  | .leave => by rw [resolveForLayoutStmt_leave]

theorem writeSet_resolveStmts (L : Layout) :
    ∀ ss : List (Stmt Op), writeSetStmts (resolveForLayoutStmts L ss) = writeSetStmts ss
  | [] => by rw [resolveForLayoutStmts_nil]
  | s :: rest => by
      rw [resolveForLayoutStmts_cons]
      show writeSetStmt (resolveForLayoutStmt L s) ++
          writeSetStmts (resolveForLayoutStmts L rest) = _
      rw [writeSet_resolveStmt L s, writeSet_resolveStmts L rest]
      rfl

theorem writeSet_resolveCases (L : Layout) :
    ∀ cs : List (Literal × Block Op),
      writeSetCases (resolveForLayoutCases L cs) = writeSetCases cs
  | [] => by rw [resolveForLayoutCases]
  | (l, b) :: rest => by
      rw [resolveForLayoutCases]
      show writeSetStmts (resolveForLayoutStmts L b) ++
          writeSetCases (resolveForLayoutCases L rest) = _
      rw [writeSet_resolveStmts L b, writeSet_resolveCases L rest]
      rfl

end

/-! ### The rhs choice is closed under resolution -/

/-- A pure op is never an object-data op. -/
theorem pureFn_ne_data {op : Op} {vs : List U256} {w : U256}
    (h : pureFn op vs = some w) : op ≠ .dataoffset ∧ op ≠ .datasize := by
  constructor <;> (intro heq; subst heq; simp [pureFn] at h)

/-- All-literal argument lists resolve to themselves. -/
theorem resolve_lits (L : Layout) (lits : List Literal) :
    resolveForLayoutExprs L (lits.map Expr.lit) = lits.map Expr.lit := by
  induction lits with
  | nil => rfl
  | cons l rest ih =>
      rw [List.map_cons]
      show resolveForLayoutExpr L (.lit l) :: resolveForLayoutExprs L (rest.map Expr.lit) = _
      rw [ih]
      rfl

/-- The fold either does nothing or produces the folded literal. -/
theorem rhsExpr_cases (σ : PEnv) (e : Expr Op) :
    rhsExpr σ e = substExpr σ e ∨
    ∃ op args lits l, substExpr σ e = .builtin op args ∧ asLits args = some lits ∧
      pureFold op lits = some l ∧ rhsExpr σ e = .lit l := by
  rw [rhsExpr]
  cases hsub : substExpr σ e with
  | lit l => exact Or.inl (by rw [foldRhs_lit])
  | var x => exact Or.inl rfl
  | call f args => exact Or.inl (by rw [foldRhs_call])
  | builtin op args =>
      cases hlits : asLits args with
      | none => exact Or.inl (foldRhs_builtin_nolits hlits)
      | some lits =>
          cases hfold : pureFold op lits with
          | none => exact Or.inl (foldRhs_builtin_nofold hlits hfold)
          | some l =>
              exact Or.inr ⟨op, args, lits, l, rfl, hlits, hfold,
                foldRhs_builtin_fold hlits hfold⟩

/-- The rhs choice transports across resolution: the same choice is available
for the resolved source, producing the resolved target. -/
theorem RhsRel.resolve {σ : PEnv} {e e' : Expr Op} (h : RhsRel σ e e') (L : Layout) :
    RhsRel σ (resolveForLayoutExpr L e) (resolveForLayoutExpr L e') := by
  rcases h.eq_or_fold with rfl | rfl
  · rw [resolve_substExpr L σ e]
    exact .subst
  · rcases rhsExpr_cases σ e with heq | ⟨op, args, lits, l, hsub, hlits, hfold, heq⟩
    · rw [heq, resolve_substExpr L σ e]
      exact .subst
    · rw [heq]
      have hargs : args = lits.map Expr.lit := asLits_map hlits
      have hnd : op ≠ .dataoffset ∧ op ≠ .datasize := by
        rw [pureFold, Option.map_eq_some_iff] at hfold
        obtain ⟨w, hw, _⟩ := hfold
        exact pureFn_ne_data hw
      have hresolve_sub : substExpr σ (resolveForLayoutExpr L e) = .builtin op args := by
        rw [← resolve_substExpr L σ e, hsub,
            resolve_builtin_nondata L args hnd.1 hnd.2, hargs, resolve_lits]
      have hfoldr : rhsExpr σ (resolveForLayoutExpr L e) = .lit l := by
        rw [rhsExpr, hresolve_sub, foldRhs_builtin_fold hlits hfold]
      show RhsRel σ (resolveForLayoutExpr L e) (resolveForLayoutExpr L (.lit l))
      show RhsRel σ (resolveForLayoutExpr L e) (.lit l)
      rw [← hfoldr]
      exact .fold

/-! ### The relation is closed under resolution -/

/-- Resolution over the relation's syntactic classes. -/
def resolvePCode (L : Layout) : PCode Op → PCode Op
  | .expr e => .expr (resolveForLayoutExpr L e)
  | .args es => .args (resolveForLayoutExprs L es)
  | .stmt s => .stmt (resolveForLayoutStmt L s)
  | .stmts ss => .stmts (resolveForLayoutStmts L ss)
  | .loop c post body =>
      .loop (resolveForLayoutExpr L c) (resolveForLayoutStmts L post)
        (resolveForLayoutStmts L body)
  | .cases cs => .cases (resolveForLayoutCases L cs)
  | .odflt d => .odflt (d.map (resolveForLayoutStmts L))

/-- **Closure under resolution**: resolving both sides of a related pair yields
a related pair with the same tracked environments. -/
theorem PropRel.resolve {σ σ' : PEnv} {pc pc' : PCode Op}
    (h : PropRel σ σ' pc pc') (L : Layout) :
    PropRel σ σ' (resolvePCode L pc) (resolvePCode L pc') := by
  induction h with
  | expr hrhs => exact .expr (hrhs.resolve L)
  | @args σ es =>
      show PropRel σ σ (.args (resolveForLayoutExprs L es))
        (.args (resolveForLayoutExprs L (substArgs σ es)))
      rw [resolve_substArgs L σ es]
      exact .args
  | @blockS σ σb body body' _ ih =>
      show PropRel σ (prune σ (writeSetStmts body))
        (.stmt (resolveForLayoutStmt L (.block body)))
        (.stmt (resolveForLayoutStmt L (.block body')))
      rw [resolveForLayoutStmt_block, resolveForLayoutStmt_block,
          ← writeSet_resolveStmts L body]
      exact .blockS ih
  | @funDefS σ σb n ps rs body body' _ ih =>
      show PropRel σ σ (.stmt (resolveForLayoutStmt L (.funDef n ps rs body)))
        (.stmt (resolveForLayoutStmt L (.funDef n ps rs body')))
      rw [resolveForLayoutStmt_funDef, resolveForLayoutStmt_funDef]
      exact .funDefS ih
  | @letSomeS σ σ2 xs e rhs' hrhs henv =>
      show PropRel σ σ2 (.stmt (resolveForLayoutStmt L (.letDecl xs (some e))))
        (.stmt (resolveForLayoutStmt L (.letDecl xs (some rhs'))))
      rw [resolveForLayoutStmt_letDecl, resolveForLayoutStmt_letDecl]
      show PropRel σ σ2 (.stmt (.letDecl xs (some (resolveForLayoutExpr L e))))
        (.stmt (.letDecl xs (some (resolveForLayoutExpr L rhs'))))
      refine .letSomeS (hrhs.resolve L) ?_
      cases henv with
      | skip => exact .skip
      | create hx hcl =>
          rw [classify_resolve hcl L]
          exact .create hx hcl
  | @letNoneS σ σ2 xs henv =>
      show PropRel σ σ2 (.stmt (resolveForLayoutStmt L (.letDecl xs none)))
        (.stmt (resolveForLayoutStmt L (.letDecl xs none)))
      rw [resolveForLayoutStmt_letDecl]
      exact .letNoneS henv
  | @assignS σ σ2 xs e rhs' hrhs henv =>
      show PropRel σ σ2 (.stmt (resolveForLayoutStmt L (.assign xs e)))
        (.stmt (resolveForLayoutStmt L (.assign xs rhs')))
      rw [resolveForLayoutStmt_assign, resolveForLayoutStmt_assign]
      refine .assignS (hrhs.resolve L) ?_
      cases henv with
      | skip => exact .skip
      | refresh hx hbound hcl =>
          rw [classify_resolve hcl L]
          exact .refresh hx hbound hcl
  | @condS σ σb c body body' _ ih =>
      show PropRel σ (prune σ (writeSetStmts body))
        (.stmt (resolveForLayoutStmt L (.cond c body)))
        (.stmt (resolveForLayoutStmt L (.cond (substExpr σ c) body')))
      rw [resolveForLayoutStmt_cond, resolveForLayoutStmt_cond,
          resolve_substExpr L σ c, ← writeSet_resolveStmts L body]
      exact .condS ih
  | @switchS σ c cases cases' dflt dflt' _ _ ihc ihd =>
      show PropRel σ (prune σ (writeSetCases cases ++ writeSetDflt dflt))
        (.stmt (resolveForLayoutStmt L (.switch c cases dflt)))
        (.stmt (resolveForLayoutStmt L (.switch (substExpr σ c) cases' dflt')))
      rw [resolveForLayoutStmt_switch, resolveForLayoutStmt_switch,
          resolve_substExpr L σ c]
      have hwc : writeSetCases cases ++ writeSetDflt dflt =
          writeSetCases (resolveForLayoutCases L cases) ++
            writeSetDflt (dflt.map (resolveForLayoutStmts L)) := by
        rw [writeSet_resolveCases L cases]
        cases dflt with
        | none => rfl
        | some b =>
            show _ = _ ++ writeSetStmts (resolveForLayoutStmts L b)
            rw [writeSet_resolveStmts L b]
            rfl
      rw [hwc]
      exact .switchS ihc ihd
  | @forS σ σi σp σb σL init init' c post post' body body' _ hσL _ _ ihi ihp ihb =>
      show PropRel σ
        (prune σ (writeSetStmts init ++ writeSetStmts post ++ writeSetStmts body))
        (.stmt (resolveForLayoutStmt L (.forLoop init c post body)))
        (.stmt (resolveForLayoutStmt L (.forLoop init' (substExpr σL c) post' body')))
      rw [resolveForLayoutStmt_forLoop, resolveForLayoutStmt_forLoop,
          resolve_substExpr L σL c, ← writeSet_resolveStmts L init,
          ← writeSet_resolveStmts L post, ← writeSet_resolveStmts L body]
      refine .forS ihi ?_ ihp ihb
      rw [writeSet_resolveStmts L post, writeSet_resolveStmts L body]
      exact hσL
  | @exprStmtS σ e =>
      show PropRel σ σ (.stmt (resolveForLayoutStmt L (.exprStmt e)))
        (.stmt (resolveForLayoutStmt L (.exprStmt (substExpr σ e))))
      rw [resolveForLayoutStmt_exprStmt, resolveForLayoutStmt_exprStmt,
          resolve_substExpr L σ e]
      exact .exprStmtS
  | @breakS σ =>
      show PropRel σ σ (.stmt (resolveForLayoutStmt L .break))
        (.stmt (resolveForLayoutStmt L .break))
      rw [resolveForLayoutStmt_break]
      exact .breakS
  | @continueS σ =>
      show PropRel σ σ (.stmt (resolveForLayoutStmt L .continue))
        (.stmt (resolveForLayoutStmt L .continue))
      rw [resolveForLayoutStmt_continue]
      exact .continueS
  | @leaveS σ =>
      show PropRel σ σ (.stmt (resolveForLayoutStmt L .leave))
        (.stmt (resolveForLayoutStmt L .leave))
      rw [resolveForLayoutStmt_leave]
      exact .leaveS
  | nilSS =>
      show PropRel _ _ (.stmts (resolveForLayoutStmts L []))
        (.stmts (resolveForLayoutStmts L []))
      rw [resolveForLayoutStmts_nil]
      exact .nilSS
  | @consSS σ σ1 σ' s s' rest rest' _ _ ihs ihrest =>
      show PropRel σ σ' (.stmts (resolveForLayoutStmts L (s :: rest)))
        (.stmts (resolveForLayoutStmts L (s' :: rest')))
      rw [resolveForLayoutStmts_cons, resolveForLayoutStmts_cons]
      exact .consSS ihs ihrest
  | @loopL σ σp σb c post body post' body' hstable _ _ ihp ihb =>
      show PropRel σ σ
        (.loop (resolveForLayoutExpr L c) (resolveForLayoutStmts L post)
          (resolveForLayoutStmts L body))
        (.loop (resolveForLayoutExpr L (substExpr σ c)) (resolveForLayoutStmts L post')
          (resolveForLayoutStmts L body'))
      rw [resolve_substExpr L σ c]
      refine .loopL ?_ ihp ihb
      rw [writeSet_resolveStmts L post, writeSet_resolveStmts L body]
      exact hstable
  | casesNil =>
      show PropRel _ _ (.cases (resolveForLayoutCases L []))
        (.cases (resolveForLayoutCases L []))
      rw [resolveForLayoutCases]
      exact .casesNil
  | @casesCons σ σb l b b' rest rest' _ _ ihb ihrest =>
      show PropRel σ σ (.cases (resolveForLayoutCases L ((l, b) :: rest)))
        (.cases (resolveForLayoutCases L ((l, b') :: rest')))
      rw [resolveForLayoutCases, resolveForLayoutCases]
      exact .casesCons ihb ihrest
  | odfltNone => exact .odfltNone
  | @odfltSome σ σb b b' _ ih => exact .odfltSome ih

/-! ### The payoff: the resolution congruence for the pass -/

/-- Resolving the source and resolving the propagated program are semantically
equivalent — the object-path bridge, with the *full* pass (no `litOK`-style
restriction). -/
theorem resolvePropagateBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L (propagateBlock b)) :=
  PropRel.equivBlock ((propStmts_rel (copyGate 0 b) [] b).resolve L)

end YulEvmCompiler.Optimizer
