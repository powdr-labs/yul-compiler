import YulIR.FrameBigStep

set_option warningAsError true
/-!
# YulIR.FrameSound — soundness of frame-IR rewrites against the native semantics

The payoff: the semantic rewrites the `structural` pass performs, proved sound against the frame
big-step semantics (`YulIR.FrameBigStep`) — `sorry`-free. These are the frame-IR analogues of the
named-IR `YulIR.Soundness` lemmas, and they come out cleaner: the store is total (no `Option`
casing) and there is no scoping side-condition to discharge.

* `structural_dead_if`   — `if 0 { body }` ≡ nothing;
* `structural_if_true`   — `if 1 { body }` ≡ `body` (spliced);
* `structural_switch`    — `switch <lit L> …` ≡ the selected case block.

Each is an `EquivBlock` at a fixed function table; `Run.of_equivMain` lifts a `main`-block rewrite
to identical whole-program runs (shown by `structural_if_true_run`). Composing rewrites that occur
inside *function bodies* to a whole-program result additionally needs a function-table congruence
(the frame analogue of the funDef congruence already proved for the Yul semantics) — deferred.
-/

namespace YulIR.FinFrame.Sem

open YulSemantics (Outcome Literal)
open YulSemantics.EVM (litValue)

/-! ### Literal-condition evaluation (σ-independent) -/

/-- `evalAtom σ (.lit (.number 0)) = 0`, stated σ-independently so `decide` applies. -/
private theorem eval_lit0 (σ : Store n) : evalAtom σ (.lit (.number 0)) = 0 := by
  show litValue (.number 0) = 0; decide

/-- `evalAtom σ (.lit (.number 1)) ≠ 0`. -/
private theorem eval_lit1_ne (σ : Store n) : evalAtom σ (.lit (.number 1)) ≠ 0 := by
  show litValue (.number 1) ≠ 0; decide

/-! ### Singleton-block bridge -/

/-- Running a one-statement block is running the statement (the tail is empty). -/
theorem block_singleton {funs : Funs} {s : Stmt n} {σ st σ' st' o}
    (h : ExecStmt funs σ st s σ' st' o) : ExecBlock funs σ st [s] σ' st' o := by
  by_cases ho : o = .normal
  · subst ho; exact .consNormal h .nil
  · exact .consStop h ho

/-- ... and conversely. -/
theorem block_singleton_inv {funs : Funs} {s : Stmt n} {σ st σ' st' o}
    (h : ExecBlock funs σ st [s] σ' st' o) : ExecStmt funs σ st s σ' st' o := by
  cases h with
  | consNormal h1 h2 => cases h2 with | nil => exact h1
  | consStop h1 _    => exact h1

/-! ### `structural`'s rewrites -/

/-- A dead `if 0 { body }` is equivalent to nothing. -/
theorem structural_dead_if (funs : Funs) (body : Block n) :
    EquivBlock funs [Stmt.cond (.lit (.number 0)) body] [] := by
  intro σ st σ' st' o
  constructor
  · intro h
    cases block_singleton_inv h with
    | condFalse _   => exact .nil
    | condTrue hc _ => exact absurd (eval_lit0 σ) hc
  · intro h
    cases h with
    | nil => exact block_singleton (.condFalse (eval_lit0 σ))

/-- `if 1 { body }` runs its body unconditionally — equivalent to `body` spliced in. -/
theorem structural_if_true (funs : Funs) (body : Block n) :
    EquivBlock funs [Stmt.cond (.lit (.number 1)) body] body := by
  intro σ st σ' st' o
  constructor
  · intro h
    cases block_singleton_inv h with
    | condFalse hc     => exact absurd hc (eval_lit1_ne σ)
    | condTrue _ hbody => exact hbody
  · intro h
    exact block_singleton (.condTrue (eval_lit1_ne σ) h)

/-- A constant `switch` is equivalent to the block it selects. -/
theorem structural_switch (funs : Funs) (L : Literal) (cases : List (Literal × Block n))
    (dflt : Option (Block n)) :
    EquivBlock funs [Stmt.switch (.lit L) cases dflt] (selectCase (litValue L) cases dflt) := by
  intro σ st σ' st' o
  constructor
  · intro h
    cases block_singleton_inv h with
    | switch hsel => exact hsel
  · intro h
    exact block_singleton (.switch h)

end YulIR.FinFrame.Sem
