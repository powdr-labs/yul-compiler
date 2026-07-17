import YulEvmCompiler.Optimizer.Spec.Pass
import YulEvmCompiler.Optimizer.Implementation.Frame
import YulSemantics.Dialect.EVM

/-!
# YulEvmCompiler.Optimizer.Implementation.DeadCode

**Dead-`let` elimination.** Drops a `let x := e` whose bound variable `x` is
never used again and whose initialiser `e` is *side-effect-free* (it neither
writes state nor halts). Under the `WellScoped` precondition (`Spec/Scoped.lean`)
this is sound in both directions of the pointwise `EquivBlock`: well-scopedness
guarantees `e` still evaluates from every reachable environment, so removing the
`let` cannot turn a stuck program into a running one (the pathology that makes
binding-removal unsound in general — see `Spec/Scoped.lean`).

The soundness is carried by the **frame lemma** (`Implementation/Frame.lean`):
the dropped binding is invisible to the (unmentioning) rest of the block, and the
block's `restore` drops it on exit, so both programs reach the same result.
-/

namespace YulEvmCompiler.Optimizer

open YulSemantics
open YulSemantics.EVM

variable {calls : ExternalCalls} {creates : ExternalCreates}

local notation "D" => evmWithExternal calls creates

/-! ### Side-effect-free initialisers

The fragment of expressions safe to drop: those that always evaluate to a single
value with the state unchanged and never halt. Variables and literals qualify;
richer pure fragments (total non-halting built-ins over side-effect-free
arguments) can be added later — this covers the copy/const temporaries that
dominate `solc`'s `--via-ir` output. -/

/-- Side-effect-free (droppable) initialisers: variables and literals. -/
def SideEffectFree : Expr Op → Bool
  | .var _ => true
  | .lit _ => true
  | _ => false

/-! ### Evaluation adequacy under scoping -/

/-- A variable present in an environment's domain reads to some value. -/
theorem get_some_of_mem_dom {V : VEnv D} {y : Ident} (h : y ∈ V.map Prod.fst) :
    ∃ w, V.get y = some w := by
  induction V with
  | nil => simp at h
  | cons p rest ih =>
      simp only [List.map_cons, List.mem_cons] at h
      unfold VEnv.get
      by_cases hp : p.1 = y
      · rw [List.find?_cons_of_pos (by simp [hp])]; exact ⟨p.2, rfl⟩
      · rw [List.find?_cons_of_neg (by simp [hp])]
        rcases h with h | h
        · exact absurd h.symm hp
        · exact ih h

/-- **Evaluation adequacy.** A side-effect-free expression that is well-scoped in
`Γ`, run from an environment whose domain covers `Γ`, evaluates to a single value
with the state unchanged (and never halts). This is what makes dropping a dead
`let x := e` sound in the *backward* direction: the removed `e` still runs. -/
theorem sef_eval {Γ : List Ident} {e : Expr Op} {funs : FunEnv D} {V : VEnv D} {st : EvmState}
    (hsef : SideEffectFree e = true) (hsc : ScopedExpr Γ e)
    (hdom : ∀ y ∈ Γ, y ∈ V.map Prod.fst) :
    ∃ w, Step D funs V st (.expr e) (.eres (.vals [w] st)) := by
  cases e with
  | lit l => exact ⟨litValue l, Step.lit⟩
  | var y =>
      obtain ⟨w, hw⟩ := get_some_of_mem_dom (hdom y hsc)
      exact ⟨w, Step.var hw⟩
  | builtin op args => simp [SideEffectFree] at hsef
  | call f args => simp [SideEffectFree] at hsef

/-! ### Statement-sequence append decomposition -/

/-- Executing `pre ++ suf` either runs `pre` to a `normal` outcome and then `suf`,
or `pre` short-circuits (a non-`normal` outcome) and `suf` never runs. -/
theorem stmts_append_fwd {funs : FunEnv D} {pre suf : List (Stmt Op)} {V st Vb st' o}
    (h : Step D funs V st (.stmts (pre ++ suf)) (.sres Vb st' o)) :
    (∃ V1 st1, Step D funs V st (.stmts pre) (.sres V1 st1 .normal) ∧
       Step D funs V1 st1 (.stmts suf) (.sres Vb st' o)) ∨
    (o ≠ .normal ∧ Step D funs V st (.stmts pre) (.sres Vb st' o)) := by
  induction pre generalizing V st with
  | nil => exact Or.inl ⟨V, st, Step.seqNil, h⟩
  | cons s pre' ih =>
      rw [List.cons_append] at h
      cases h with
      | seqCons hs htail =>
          rcases ih htail with ⟨V1, st1, hpre', hsuf⟩ | ⟨hne, hpre'⟩
          · exact Or.inl ⟨V1, st1, Step.seqCons hs hpre', hsuf⟩
          · exact Or.inr ⟨hne, Step.seqCons hs hpre'⟩
      | seqStop hs hne => exact Or.inr ⟨hne, Step.seqStop hs hne⟩

/-- Reassembling: `pre` to `normal` then `suf` runs `pre ++ suf`. -/
theorem stmts_append_normal {funs : FunEnv D} {pre suf : List (Stmt Op)} {V st V1 st1 Vb st' o}
    (hpre : Step D funs V st (.stmts pre) (.sres V1 st1 .normal))
    (hsuf : Step D funs V1 st1 (.stmts suf) (.sres Vb st' o)) :
    Step D funs V st (.stmts (pre ++ suf)) (.sres Vb st' o) := by
  induction pre generalizing V st with
  | nil => cases hpre with | seqNil => exact hsuf
  | cons s pre' ih =>
      cases hpre with
      | seqCons hs hpre' => exact Step.seqCons hs (ih hpre')
      | seqStop _ hne => exact absurd rfl hne

end YulEvmCompiler.Optimizer
