import YulEvmCompiler.Optimizer.Implementation.PruneDefsSound
import YulEvmCompiler.Optimizer.Implementation.ObjectPass
set_option warningAsError true
/-!
# Layout-resolution congruence for `PruneDefs`

Layout resolution rewrites `dataoffset`/`datasize` **builtins** into number
literals and leaves every `.call` untouched, so call names — and therefore
`rootDefs`, `rootCalls`, the reachability closure, and the kept/dropped
decision — are resolution-invariant.  Pruning consequently **commutes**
syntactically with `resolveForLayoutStmts`, and the object-path congruence is
the pass's own soundness on the resolved code (the `CoalesceCopies` recipe).
-/

namespace YulEvmCompiler.Optimizer.PruneDefs

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler

variable {calls : ExternalCalls} {creates : ExternalCreates} {gasOracle : ExternalGas}
local notation "D" => evmWithExternal calls creates gasOracle

/-! ### Call names are resolution-invariant -/

mutual
theorem callNames_resolveExpr (L : Layout) : ∀ (e : Expr Op),
    callNamesExpr (resolveForLayoutExpr L e) = callNamesExpr e
  | .lit l => by rw [resolveForLayoutExpr]
  | .var x => by rw [resolveForLayoutExpr]
  | .builtin op args => by
      have hgen : callNamesExpr (Expr.builtin op (resolveForLayoutExprs L args))
          = callNamesExpr (Expr.builtin op args) := by
        simp only [callNamesExpr]
        exact callNames_resolveArgs L args
      cases op <;> try exact hgen
      case dataoffset =>
        cases args with
        | nil => exact hgen
        | cons e rest =>
            cases e <;> try exact hgen
            case lit literal =>
              cases literal <;> try exact hgen
              case string name =>
                cases rest with
                | nil => rfl
                | cons _ _ => exact hgen
      case datasize =>
        cases args with
        | nil => exact hgen
        | cons e rest =>
            cases e <;> try exact hgen
            case lit literal =>
              cases literal <;> try exact hgen
              case string name =>
                cases rest with
                | nil => rfl
                | cons _ _ => exact hgen
  | .call f args => by
      rw [resolveForLayoutExpr]
      simp only [callNamesExpr]
      rw [callNames_resolveArgs L args]

theorem callNames_resolveArgs (L : Layout) : ∀ (args : List (Expr Op)),
    callNamesArgs (resolveForLayoutExprs L args) = callNamesArgs args
  | [] => by rw [resolveForLayoutExprs]
  | e :: rest => by
      rw [resolveForLayoutExprs]
      simp only [callNamesArgs]
      rw [callNames_resolveExpr L e, callNames_resolveArgs L rest]
end

mutual
theorem callNames_resolveStmt (L : Layout) : ∀ (s : Stmt Op),
    callNamesStmt (resolveForLayoutStmt L s) = callNamesStmt s
  | .block body => by
      simp only [resolveForLayoutStmt_block, callNamesStmt]
      exact callNames_resolveStmts L body
  | .funDef n ps rs body => by
      simp only [resolveForLayoutStmt_funDef, callNamesStmt]
      exact callNames_resolveStmts L body
  | .letDecl xs none => by simp [callNamesStmt]
  | .letDecl xs (some e) => by
      simp only [resolveForLayoutStmt_letDecl, Option.map_some, callNamesStmt]
      exact callNames_resolveExpr L e
  | .assign xs e => by
      simp only [resolveForLayoutStmt_assign, callNamesStmt]
      exact callNames_resolveExpr L e
  | .exprStmt e => by
      simp only [resolveForLayoutStmt_exprStmt, callNamesStmt]
      exact callNames_resolveExpr L e
  | .cond c body => by
      simp only [resolveForLayoutStmt_cond, callNamesStmt]
      rw [callNames_resolveExpr L c, callNames_resolveStmts L body]
  | .switch c cases dflt => by
      simp only [resolveForLayoutStmt_switch, callNamesStmt]
      rw [callNames_resolveExpr L c, callNames_resolveCases L cases]
      congr 1
      cases dflt with
      | none => rfl
      | some b =>
          simp only [Option.map_some, callNamesDflt]
          exact callNames_resolveStmts L b
  | .forLoop init c post body => by
      simp only [resolveForLayoutStmt_forLoop, callNamesStmt]
      rw [callNames_resolveStmts L init, callNames_resolveExpr L c,
        callNames_resolveStmts L post, callNames_resolveStmts L body]
  | .break => by simp [callNamesStmt]
  | .continue => by simp [callNamesStmt]
  | .leave => by simp [callNamesStmt]
  termination_by s => 2 * sizeOf s + 1
  decreasing_by all_goals simp_wf <;> omega

theorem callNames_resolveStmts (L : Layout) : ∀ (ss : List (Stmt Op)),
    callNamesStmts (resolveForLayoutStmts L ss) = callNamesStmts ss
  | [] => by simp [callNamesStmts]
  | s :: rest => by
      simp only [resolveForLayoutStmts_cons, callNamesStmts]
      rw [callNames_resolveStmt L s, callNames_resolveStmts L rest]
  termination_by ss => 2 * sizeOf ss

theorem callNames_resolveCases (L : Layout) :
    ∀ (cs : List (Literal × List (Stmt Op))),
      callNamesCases (resolveForLayoutCases L cs) = callNamesCases cs
  | [] => by rw [resolveForLayoutCases]
  | (l, b) :: rest => by
      rw [resolveForLayoutCases]
      simp only [callNamesCases]
      rw [callNames_resolveStmts L b, callNames_resolveCases L rest]
  termination_by cs => 2 * sizeOf cs
end

/-! ### The transform commutes with resolution -/

theorem rootDefs_resolve (L : Layout) : ∀ (ss : List (Stmt Op)),
    rootDefs (resolveForLayoutStmts L ss) = rootDefs ss
  | [] => by simp [rootDefs]
  | s :: rest => by
      rw [resolveForLayoutStmts_cons]
      cases s
      case funDef n ps rs b =>
        rw [resolveForLayoutStmt_funDef]
        show (n, callNamesStmts (resolveForLayoutStmts L b)) ::
          rootDefs (resolveForLayoutStmts L rest) = _
        rw [callNames_resolveStmts L b, rootDefs_resolve L rest]
        rfl
      case block body =>
        rw [resolveForLayoutStmt_block]
        exact rootDefs_resolve L rest
      case letDecl xs rhs =>
        rw [resolveForLayoutStmt_letDecl]
        exact rootDefs_resolve L rest
      case assign xs e =>
        rw [resolveForLayoutStmt_assign]
        exact rootDefs_resolve L rest
      case exprStmt e =>
        rw [resolveForLayoutStmt_exprStmt]
        exact rootDefs_resolve L rest
      case cond c body =>
        rw [resolveForLayoutStmt_cond]
        exact rootDefs_resolve L rest
      case «switch» c cs d =>
        rw [resolveForLayoutStmt_switch]
        exact rootDefs_resolve L rest
      case forLoop i c p b =>
        rw [resolveForLayoutStmt_forLoop]
        exact rootDefs_resolve L rest
      case «break» =>
        rw [resolveForLayoutStmt_break]
        exact rootDefs_resolve L rest
      case «continue» =>
        rw [resolveForLayoutStmt_continue]
        exact rootDefs_resolve L rest
      case «leave» =>
        rw [resolveForLayoutStmt_leave]
        exact rootDefs_resolve L rest

theorem rootCalls_resolve (L : Layout) : ∀ (ss : List (Stmt Op)),
    rootCalls (resolveForLayoutStmts L ss) = rootCalls ss
  | [] => by simp [rootCalls]
  | s :: rest => by
      rw [resolveForLayoutStmts_cons]
      cases s
      case funDef n ps rs b =>
        rw [resolveForLayoutStmt_funDef]
        exact rootCalls_resolve L rest
      case block body =>
        rw [resolveForLayoutStmt_block]
        show callNamesStmt (Stmt.block (resolveForLayoutStmts L body)) ++
          rootCalls (resolveForLayoutStmts L rest) = _
        rw [show callNamesStmt (Stmt.block (resolveForLayoutStmts L body)) =
          callNamesStmt (resolveForLayoutStmt L (Stmt.block body)) from by
            rw [resolveForLayoutStmt_block],
          callNames_resolveStmt, rootCalls_resolve L rest]
        rfl
      case letDecl xs rhs =>
        rw [resolveForLayoutStmt_letDecl]
        show callNamesStmt (Stmt.letDecl xs (rhs.map (resolveForLayoutExpr L))) ++
          rootCalls (resolveForLayoutStmts L rest) = _
        rw [show callNamesStmt (Stmt.letDecl xs (rhs.map (resolveForLayoutExpr L))) =
          callNamesStmt (resolveForLayoutStmt L (Stmt.letDecl xs rhs)) from by
            rw [resolveForLayoutStmt_letDecl],
          callNames_resolveStmt, rootCalls_resolve L rest]
        rfl
      case assign xs e =>
        rw [resolveForLayoutStmt_assign]
        show callNamesStmt (Stmt.assign xs (resolveForLayoutExpr L e)) ++
          rootCalls (resolveForLayoutStmts L rest) = _
        rw [show callNamesStmt (Stmt.assign xs (resolveForLayoutExpr L e)) =
          callNamesStmt (resolveForLayoutStmt L (Stmt.assign xs e)) from by
            rw [resolveForLayoutStmt_assign],
          callNames_resolveStmt, rootCalls_resolve L rest]
        rfl
      case exprStmt e =>
        rw [resolveForLayoutStmt_exprStmt]
        show callNamesStmt (Stmt.exprStmt (resolveForLayoutExpr L e)) ++
          rootCalls (resolveForLayoutStmts L rest) = _
        rw [show callNamesStmt (Stmt.exprStmt (resolveForLayoutExpr L e)) =
          callNamesStmt (resolveForLayoutStmt L (Stmt.exprStmt e)) from by
            rw [resolveForLayoutStmt_exprStmt],
          callNames_resolveStmt, rootCalls_resolve L rest]
        rfl
      case cond c body =>
        rw [resolveForLayoutStmt_cond]
        show callNamesStmt (Stmt.cond (resolveForLayoutExpr L c)
          (resolveForLayoutStmts L body)) ++
          rootCalls (resolveForLayoutStmts L rest) = _
        rw [show callNamesStmt (Stmt.cond (resolveForLayoutExpr L c)
            (resolveForLayoutStmts L body)) =
          callNamesStmt (resolveForLayoutStmt L (Stmt.cond c body)) from by
            rw [resolveForLayoutStmt_cond],
          callNames_resolveStmt, rootCalls_resolve L rest]
        rfl
      case «switch» c cs d =>
        rw [resolveForLayoutStmt_switch]
        show callNamesStmt (Stmt.switch (resolveForLayoutExpr L c)
          (resolveForLayoutCases L cs) (d.map (resolveForLayoutStmts L))) ++
          rootCalls (resolveForLayoutStmts L rest) = _
        rw [show callNamesStmt (Stmt.switch (resolveForLayoutExpr L c)
            (resolveForLayoutCases L cs) (d.map (resolveForLayoutStmts L))) =
          callNamesStmt (resolveForLayoutStmt L (Stmt.switch c cs d)) from by
            rw [resolveForLayoutStmt_switch],
          callNames_resolveStmt, rootCalls_resolve L rest]
        rfl
      case forLoop i c p b =>
        rw [resolveForLayoutStmt_forLoop]
        show callNamesStmt (Stmt.forLoop (resolveForLayoutStmts L i)
          (resolveForLayoutExpr L c) (resolveForLayoutStmts L p)
          (resolveForLayoutStmts L b)) ++
          rootCalls (resolveForLayoutStmts L rest) = _
        rw [show callNamesStmt (Stmt.forLoop (resolveForLayoutStmts L i)
            (resolveForLayoutExpr L c) (resolveForLayoutStmts L p)
            (resolveForLayoutStmts L b)) =
          callNamesStmt (resolveForLayoutStmt L (Stmt.forLoop i c p b)) from by
            rw [resolveForLayoutStmt_forLoop],
          callNames_resolveStmt, rootCalls_resolve L rest]
        rfl
      case «break» =>
        rw [resolveForLayoutStmt_break]
        show callNamesStmt Stmt.break ++ rootCalls (resolveForLayoutStmts L rest) = _
        rw [rootCalls_resolve L rest]
        rfl
      case «continue» =>
        rw [resolveForLayoutStmt_continue]
        show callNamesStmt Stmt.continue ++ rootCalls (resolveForLayoutStmts L rest) = _
        rw [rootCalls_resolve L rest]
        rfl
      case «leave» =>
        rw [resolveForLayoutStmt_leave]
        show callNamesStmt Stmt.leave ++ rootCalls (resolveForLayoutStmts L rest) = _
        rw [rootCalls_resolve L rest]
        rfl

theorem liveDefs_resolve (L : Layout) (ss : List (Stmt Op)) :
    liveDefs (resolveForLayoutStmts L ss) = liveDefs ss := by
  unfold liveDefs
  rw [rootDefs_resolve, rootCalls_resolve]

theorem pruneRoot_resolve (L : Layout) (live : List Ident) :
    ∀ (ss : List (Stmt Op)),
      pruneRoot live (resolveForLayoutStmts L ss) =
        resolveForLayoutStmts L (pruneRoot live ss)
  | [] => by simp [pruneRoot]
  | s :: rest => by
      rw [resolveForLayoutStmts_cons]
      cases s
      case funDef n ps rs b =>
        rw [resolveForLayoutStmt_funDef]
        by_cases hn : live.contains n
        · rw [show pruneRoot live (Stmt.funDef n ps rs
              (resolveForLayoutStmts L b) :: resolveForLayoutStmts L rest) =
            Stmt.funDef n ps rs (resolveForLayoutStmts L b) ::
              pruneRoot live (resolveForLayoutStmts L rest) from by
                simp only [pruneRoot, if_pos hn]]
          rw [show pruneRoot live (Stmt.funDef n ps rs b :: rest) =
            Stmt.funDef n ps rs b :: pruneRoot live rest from by
              simp only [pruneRoot, if_pos hn]]
          rw [pruneRoot_resolve L live rest, resolveForLayoutStmts_cons,
            resolveForLayoutStmt_funDef]
        · rw [show pruneRoot live (Stmt.funDef n ps rs
              (resolveForLayoutStmts L b) :: resolveForLayoutStmts L rest) =
            pruneRoot live (resolveForLayoutStmts L rest) from by
              simp only [pruneRoot, if_neg hn]]
          rw [show pruneRoot live (Stmt.funDef n ps rs b :: rest) =
            pruneRoot live rest from by simp only [pruneRoot, if_neg hn]]
          exact pruneRoot_resolve L live rest
      all_goals {
        simp only [resolveForLayoutStmt_block, resolveForLayoutStmt_letDecl,
          resolveForLayoutStmt_assign, resolveForLayoutStmt_exprStmt,
          resolveForLayoutStmt_cond, resolveForLayoutStmt_switch,
          resolveForLayoutStmt_forLoop, resolveForLayoutStmt_break,
          resolveForLayoutStmt_continue, resolveForLayoutStmt_leave]
        show _ :: pruneRoot live (resolveForLayoutStmts L rest) =
          resolveForLayoutStmts L (_ :: pruneRoot live rest)
        rw [pruneRoot_resolve L live rest, resolveForLayoutStmts_cons]
        simp only [resolveForLayoutStmt_block, resolveForLayoutStmt_letDecl,
          resolveForLayoutStmt_assign, resolveForLayoutStmt_exprStmt,
          resolveForLayoutStmt_cond, resolveForLayoutStmt_switch,
          resolveForLayoutStmt_forLoop, resolveForLayoutStmt_break,
          resolveForLayoutStmt_continue, resolveForLayoutStmt_leave]
      }

/-- Pruning commutes with layout resolution. -/
theorem resolve_pruneDefsBlock (L : Layout) (b : Block Op) :
    resolveForLayoutStmts L (pruneDefsBlock b) =
      pruneDefsBlock (resolveForLayoutStmts L b) := by
  unfold pruneDefsBlock
  rw [liveDefs_resolve, pruneRoot_resolve]

end YulEvmCompiler.Optimizer.PruneDefs
