import YulEvmCompiler.Optimizer.Implementation.CoalesceCopies
import YulEvmCompiler.Optimizer.Implementation.DeadLitsResolve
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Implementation.CoalesceCopiesResolve

**Coalescing commutes with object-layout resolution, syntactically.** The pass
inspects only statement shapes (`letDecl` binder lists and a bare-variable
right-hand side) and identifier occurrence sets — resolution rewrites
`dataoffset`/`datasize` builtins into number literals, which changes neither.
In particular resolution can never *create* a bare-variable right-hand side
(it creates literals) nor destroy one, so the pass fires at exactly the same
sites before and after resolution:

```
resolveForLayoutStmts L (coalesceCopiesBlock b) =
  coalesceCopiesBlock (resolveForLayoutStmts L b)
```

This gives the object-path congruence `resolveCoalesceCopiesBlock_equiv`
directly from the pass's own `Sound` proof on the resolved block, with no
relational closure needed.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### Resolution preserves the pattern shapes -/

/-- Resolution yields a bare variable only from that bare variable. -/
theorem resolveExpr_eq_var {L : Layout} {e : Expr Op} {z : Ident}
    (h : resolveForLayoutExpr L e = .var z) : e = .var z := by
  cases e with
  | lit l => exact h
  | var w => exact h
  | builtin op args =>
      by_cases hstr : ∃ n, args = [.lit (.string n)]
      · obtain ⟨n, rfl⟩ := hstr
        by_cases hop : op = .dataoffset ∨ op = .datasize
        · rcases hop with rfl | rfl <;> exact absurd h (by simp [resolveForLayoutExpr])
        · rw [not_or] at hop
          rw [resolve_builtin_nondata L _ hop.1 hop.2] at h
          exact absurd h (by simp)
      · rw [not_exists] at hstr
        rw [resolveForLayoutExpr_builtin_other L op args
          (fun n hc => hstr n hc)] at h
        exact absurd h (by simp)
  | call f args => exact absurd h (by simp [resolveForLayoutExpr])

/-- Resolution yields a singleton-`letDecl` statement only from one. -/
theorem resolveStmt_eq_letDecl {L : Layout} {s : Stmt Op} {xs : List Ident}
    {v : Option (Expr Op)}
    (h : resolveForLayoutStmt L s = .letDecl xs v) :
    ∃ v₀, s = .letDecl xs v₀ ∧ v = v₀.map (resolveForLayoutExpr L) := by
  cases s with
  | letDecl ys w =>
      rw [resolveForLayoutStmt_letDecl] at h
      injection h with h1 h2
      subst h1
      exact ⟨w, rfl, h2.symm⟩
  | block body => rw [resolveForLayoutStmt_block] at h; cases h
  | funDef n ps rs body => rw [resolveForLayoutStmt_funDef] at h; cases h
  | assign ys e => rw [resolveForLayoutStmt_assign] at h; cases h
  | cond c body => rw [resolveForLayoutStmt_cond] at h; cases h
  | «switch» c cs dflt => rw [resolveForLayoutStmt_switch] at h; cases h
  | forLoop init c post body => rw [resolveForLayoutStmt_forLoop] at h; cases h
  | exprStmt e => rw [resolveForLayoutStmt_exprStmt] at h; cases h
  | «break» => rw [resolveForLayoutStmt_break] at h; cases h
  | «continue» => rw [resolveForLayoutStmt_continue] at h; cases h
  | «leave» => rw [resolveForLayoutStmt_leave] at h; cases h

/-! ### The commutation -/

theorem resolve_ccPairs (L : Layout) : ∀ ss : List (Stmt Op),
    resolveForLayoutStmts L (ccPairs ss) =
      ccPairs (resolveForLayoutStmts L ss) := by
  intro ss
  induction ss using ccPairs.induct with
  | case1 x rhs y x' rest hg ih =>
      obtain ⟨rfl, hxy, hm⟩ := hg
      rw [ccPairs.eq_1, if_pos ⟨rfl, hxy, hm⟩, ih,
        resolveForLayoutStmts_cons, resolveForLayoutStmts_cons,
        resolveForLayoutStmts_cons,
        resolveForLayoutStmt_letDecl, resolveForLayoutStmt_letDecl,
        resolveForLayoutStmt_letDecl]
      rw [show (some (.var x') : Option (Expr Op)).map (resolveForLayoutExpr L) =
        some (.var x') from rfl]
      rw [ccPairs.eq_1,
        if_pos ⟨rfl, hxy, by rw [mentions_resolveStmts]; exact hm⟩]
  | case2 x rhs y x' rest hng ih =>
      have hvar : resolveForLayoutExpr L (.var x') = .var x' := rfl
      rw [ccPairs.eq_1, if_neg hng]
      simp only [resolveForLayoutStmts_cons, resolveForLayoutStmt_letDecl,
        Option.map_some, hvar]
      rw [ih]
      simp only [resolveForLayoutStmts_cons, resolveForLayoutStmt_letDecl,
        Option.map_some, hvar]
      rw [ccPairs.eq_1, if_neg (fun hres => hng
        ⟨hres.1, hres.2.1, by
          rw [← mentions_resolveStmts L x rest]; exact hres.2.2⟩)]
  | case3 s rest hno ih =>
      rw [ccPairs.eq_2 s rest hno, resolveForLayoutStmts_cons,
        resolveForLayoutStmts_cons, ih]
      rw [ccPairs.eq_2]
      intro x rhs y x' rest₁ hs hrest
      obtain ⟨v₀, rfl, -⟩ := resolveStmt_eq_letDecl hs
      cases hres : resolveForLayoutStmts L rest with
      | nil => rw [hres] at hrest; cases hrest
      | cons a b =>
          rw [hres] at hrest
          injection hrest with ha hb
          cases rest with
          | nil => rw [resolveForLayoutStmts_nil] at hres; cases hres
          | cons r rest₂ =>
              rw [resolveForLayoutStmts_cons] at hres
              injection hres with hr hrest₂
              rw [← hr] at ha
              obtain ⟨w₀, rfl, hw⟩ := resolveStmt_eq_letDecl ha
              cases w₀ with
              | none => cases hw
              | some e =>
                  rw [show (some e : Option (Expr Op)).map (resolveForLayoutExpr L) =
                    some (resolveForLayoutExpr L e) from rfl] at hw
                  injection hw with hw
                  exact hno x v₀ y x' rest₂ rfl
                    (by rw [resolveExpr_eq_var hw.symm])
  | case4 =>
      rw [ccPairs.eq_3, resolveForLayoutStmts_nil, ccPairs.eq_3]

mutual

theorem resolve_ccStmt (L : Layout) : ∀ s : Stmt Op,
    resolveForLayoutStmt L (ccStmt s) = ccStmt (resolveForLayoutStmt L s)
  | .block body => by
      simp only [ccStmt, resolveForLayoutStmt_block]
      rw [resolve_ccPairs, resolve_ccStmts L body]
  | .funDef n ps rs body => by
      simp only [ccStmt, resolveForLayoutStmt_funDef]
      rw [resolve_ccPairs, resolve_ccStmts L body]
  | .cond c body => by
      simp only [ccStmt, resolveForLayoutStmt_cond]
      rw [resolve_ccPairs, resolve_ccStmts L body]
  | .switch c cases dflt => by
      simp only [ccStmt, resolveForLayoutStmt_switch]
      rw [resolve_ccCases L cases]
      cases dflt with
      | none => simp only [ccDflt, Option.map_none]
      | some b =>
          simp only [ccDflt, Option.map_some]
          rw [resolve_ccPairs, resolve_ccStmts L b]
  | .forLoop init c post body => by
      simp only [ccStmt, resolveForLayoutStmt_forLoop]
      rw [resolve_ccPairs, resolve_ccPairs, resolve_ccStmts L post,
        resolve_ccStmts L body]
  | .letDecl xs v => by simp only [ccStmt, resolveForLayoutStmt_letDecl]
  | .assign xs e => by simp only [ccStmt, resolveForLayoutStmt_assign]
  | .exprStmt e => by simp only [ccStmt, resolveForLayoutStmt_exprStmt]
  | .break => by simp only [ccStmt, resolveForLayoutStmt_break]
  | .continue => by simp only [ccStmt, resolveForLayoutStmt_continue]
  | .leave => by simp only [ccStmt, resolveForLayoutStmt_leave]

theorem resolve_ccStmts (L : Layout) : ∀ ss : List (Stmt Op),
    resolveForLayoutStmts L (ccStmts ss) = ccStmts (resolveForLayoutStmts L ss)
  | [] => by simp only [ccStmts, resolveForLayoutStmts_nil]
  | s :: rest => by
      simp only [ccStmts, resolveForLayoutStmts_cons]
      rw [resolve_ccStmt L s, resolve_ccStmts L rest]

theorem resolve_ccCases (L : Layout) : ∀ cs : List (Literal × Block Op),
    resolveForLayoutCases L (ccCases cs) = ccCases (resolveForLayoutCases L cs)
  | [] => by
      simp only [ccCases]
      rw [resolveForLayoutCases]
      simp only [ccCases]
  | (l, b) :: rest => by
      simp only [ccCases]
      rw [resolveForLayoutCases, resolveForLayoutCases]
      simp only [ccCases]
      rw [resolve_ccPairs, resolve_ccStmts L b, resolve_ccCases L rest]

end

/-- The whole-block commutation. -/
theorem resolve_coalesceCopiesBlock (L : Layout) (b : Block Op) :
    resolveForLayoutStmts L (coalesceCopiesBlock b) =
      coalesceCopiesBlock (resolveForLayoutStmts L b) := by
  unfold coalesceCopiesBlock
  rw [resolve_ccPairs, resolve_ccStmts]

/-- **Object-path congruence**: running the pass before layout resolution is
pointwise equivalent to not running it, on the resolved code. -/
theorem resolveCoalesceCopiesBlock_equiv (L : Layout) (b : Block Op) :
    EquivBlock D (resolveForLayoutStmts L b)
      (resolveForLayoutStmts L
        ((coalesceCopies (calls := calls) (creates := creates)).run b)) := by
  have h := (coalesceCopies (calls := calls) (creates := creates)).sound
    (resolveForLayoutStmts L b)
  show EquivBlock D (resolveForLayoutStmts L b)
    (resolveForLayoutStmts L (coalesceCopiesBlock b))
  rw [resolve_coalesceCopiesBlock]
  exact h

end YulEvmCompiler.Optimizer
