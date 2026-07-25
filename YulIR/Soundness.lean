import YulIR.ToYul
import YulSemantics.Equiv
import YulSemantics.Rewrites

/-!
# YulIR.Soundness — semantic soundness of the IR, and of the rewrites its passes perform

The IR's meaning is its erasure `toYul` into `yul-semantics` (`YulIR.ToYul`, now a *structural*
definition so it carries equation lemmas). Soundness of an IR transformation `f : Block → Block`
is therefore

    EquivBlock EVM.evm (toYul (f b)) (toYul b)

i.e. the erased optimized program is pointwise big-step equivalent to the erased original — which,
by `EquivBlock.run_iff`, gives identical whole-program `Run` results from every initial state.

This file:

* names the IR-level equivalences (`IREquivStmts`, `IREquivBlock`) on top of
  `YulSemantics.Equiv`, and re-exports the top-level `Run` corollary;
* proves, machine-checked, the semantic rewrites the `structural` pass performs — dropping a
  dead `if 0`, collapsing `if 1 { b }` to `{ b }`, and selecting a constant `switch`.

## Scope / what is *not* yet proven

Composing these into a whole-pass theorem (`∀ b, IREquivBlock (structural b) b`) needs a
congruence for rewriting inside **function bodies**, which the upstream meta-theory does not yet
provide (`YulSemantics.Equiv`: "no `funDef` congruence yet"). Until that keystone lands, whole-pass
soundness is available only for the `funDef`-free fragment; the rewrite lemmas here are the
per-transformation obligations such a proof composes.
-/

namespace YulIR

open YulSemantics
open YulSemantics.EVM (evm)

/-- Pointwise big-step equivalence of two IR statements. -/
def IREquivStmt (s₁ s₂ : Stmt) : Prop := EquivStmt evm s₁.toYul s₂.toYul

/-- Pointwise big-step equivalence of two IR blocks *as statement sequences* (no `funDef`-hoisting
side condition — the tool for local, within-block rewrites). -/
def IREquivStmts (b₁ b₂ : Block) : Prop := EquivStmts evm (toYul b₁) (toYul b₂)

/-- Pointwise big-step equivalence of two IR blocks *as blocks* (brings each block's `funDef`s into
scope; carries the `hoist` side condition of `EquivBlock`). -/
def IREquivBlock (b₁ b₂ : Block) : Prop := EquivBlock evm (toYul b₁) (toYul b₂)

/-- Whole-program corollary: IR-equivalent top-level blocks have identical `Run` results from every
initial state (and, with determinism, identical unique results). -/
theorem IREquivBlock.run_iff {b₁ b₂ : Block} (h : IREquivBlock b₁ b₂)
    {st0 V' st' o} : Run evm (toYul b₁) st0 V' st' o ↔ Run evm (toYul b₂) st0 V' st' o :=
  EquivBlock.run_iff h

/-! ### `structural`: a dead `if 0 { body }` is equivalent to nothing -/

/-- Erasing an IR `if 0 { body }` (a constant-false conditional) yields a statement sequence that is
equivalent to the empty sequence: the branch never runs and evaluating the literal has no effect. -/
theorem structural_dead_if (body : Block) :
    IREquivStmts [Stmt.cond (.lit (.number 0)) body] [] := by
  -- `toYul [cond (lit 0) body] = [cond (lit 0) (toYulBlock body)]`; `toYul [] = []`.
  show EquivStmts evm [Stmt.toYul (.cond (.lit (.number 0)) body)] []
  simp only [Stmt.toYul, Atom.toYul]
  intro funs V st V' st' o
  constructor
  · intro h
    -- invert the singleton sequence, then the conditional and its literal condition
    cases h with
    | seqCons hcond hrest =>
        cases hcond with
        | ifTrue hc hne _ => cases hc; exact absurd rfl hne     -- `1 ≠ 0` is false here (cv = 0)
        | ifFalse hc _ =>
            cases hc                                            -- forces the tail state to `st`
            cases hrest with
            | seqNil => exact Step.seqNil
    | seqStop hcond hne =>
        cases hcond with
        | ifTrue hc hcv _ => cases hc; exact absurd rfl hcv
        | ifFalse _ _     => exact absurd rfl hne               -- `.normal ≠ .normal`
        | ifHalt hc       => cases hc                           -- a literal cannot halt
  · intro h
    -- from `[]`: `seqNil` gives `V'=V, st'=st, o=normal`; rebuild the dead `if` then the tail
    cases h with
    | seqNil => exact Step.seqCons (Step.ifFalse Step.lit rfl) Step.seqNil

/-! ### `structural`: `if 1 { body }` collapses to the block `{ body }` -/

/-- A constant-true conditional runs its body unconditionally, so it is equivalent to that body as a
block. (`structural`'s `if 1 → block` rewrite.) -/
theorem structural_if_true (body : Block) :
    IREquivStmt (Stmt.cond (.lit (.number 1)) body) (Stmt.block body) := by
  show EquivStmt evm (Stmt.toYul (.cond (.lit (.number 1)) body)) (Stmt.toYul (.block body))
  simp only [Stmt.toYul, Atom.toYul]
  intro funs V st V' st' o
  constructor
  · intro h
    cases h with
    | ifTrue hc _ hbody => cases hc; exact hbody               -- `1 ≠ 0`, body runs
    | ifFalse hc hcv    => cases hc; exact absurd hcv (by decide)
    | ifHalt hc         => cases hc                            -- a literal cannot halt
  · intro h
    exact Step.ifTrue Step.lit (by decide) h

/-! ### `structural`: a constant `switch` selects its matching case

This is stated at the `yul-semantics` level (the erased form): a `switch` on a literal reduces to
the block `selectSwitch` picks — exactly the case `structural` chooses for a constant scrutinee. -/

theorem switch_lit_selects (L : Literal) (cs : List (Literal × YulSemantics.Block EVM.Op))
    (d : Option (YulSemantics.Block EVM.Op)) :
    EquivStmt evm (.switch (.lit L) cs d) (.block (selectSwitch evm (EVM.litValue L) cs d)) := by
  intro funs V st V' st' o
  constructor
  · intro h
    cases h with
    | switchExec hc hbody => cases hc; exact hbody
    | switchHalt hc       => cases hc
  · intro h
    exact Step.switchExec Step.lit h

/-! ### `valueNumber`/`simplify`: constant folding in a `let` binding

The IR keeps every built-in in ANF, so folding happens on a `let t := op(lits)` binding. Reusing the
upstream proven fold `add(2,3) ≈ 5` and the `letDecl` congruence gives the IR-level rewrite. -/

theorem fold_let_add (t : Ident) :
    IREquivStmt (Stmt.letD [t] (.builtin .add [.lit (.number 2), .lit (.number 3)]))
                (Stmt.letD [t] (.atom (.lit (.number 5)))) := by
  show EquivStmt evm (Stmt.toYul (.letD [t] (.builtin .add [.lit (.number 2), .lit (.number 3)])))
                     (Stmt.toYul (.letD [t] (.atom (.lit (.number 5)))))
  simp only [Stmt.toYul, Rhs.toYul, Atom.toYul, List.map_cons, List.map_nil]
  exact EquivStmt.letDecl_congr [t] YulSemantics.Rewrites.fold_add_2_3

/-! ### Composition to a whole-program guarantee

The local rewrites lift through `YulSemantics.Equiv`'s congruence to `IREquivBlock`, and thence — by
`IREquivBlock.run_iff` — to identical `Run` results. Shown here for `if 1 { body }` ⇝ `{ body }` on a
top-level block; the `hoist` side condition is `rfl` because the rewrite touches no `funDef`. -/

theorem structural_if_true_block (body : Block) :
    IREquivBlock [Stmt.cond (.lit (.number 1)) body] [Stmt.block body] := by
  show EquivBlock evm [(Stmt.cond (.lit (.number 1)) body).toYul] [(Stmt.block body).toYul]
  exact EquivBlock.of_forall₂ (.cons (structural_if_true body) .nil) rfl

/-- The payoff: an `if 1 { body }` top-level program and its collapsed `{ body }` form have exactly
the same observable `Run` behaviour from every initial state. -/
theorem structural_if_true_run (body : Block) {st0 V' st' o} :
    Run evm (toYul [Stmt.cond (.lit (.number 1)) body]) st0 V' st' o ↔
    Run evm (toYul [Stmt.block body]) st0 V' st' o :=
  (structural_if_true_block body).run_iff

end YulIR
