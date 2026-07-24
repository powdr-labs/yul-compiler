import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate.Sound
import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate.SoundBwd
import YulEvmCompiler.Optimizer.Implementation.Normalization.Disambiguate.Instance
import YulEvmCompiler.Optimizer.Spec.GlobalPass
/-!
# Semantic soundness of name disambiguation

**The main theorem**: for a valid source program, `disambiguate` preserves
whole-program behaviour — `RunEquivBlock D b (disambiguate b)`, the official
`GlobalPass` obligation (`Spec/GlobalPass.lean`): from the empty environment,
source and disambiguated program produce exactly the same final environment,
state, and outcome, in both directions.

Assembled from:
* `alpha_disambiguate` (`Instance`) — the pass's output is
  α-related to its input at the pass's own renamings;
* `sim_fwd` (`Sound`) — a source step transports to a target step
  with renamed result;
* `sim_bwd` (`SoundBwd`) — a target step pulls back to a source
  step whose renamed result it is.

At the top level every configuration is trivial (empty environments, identity
renaming), and the final variable environment of a whole-program run is always
empty (the root block restores everything it declared), so the renaming is
invisible in the observables.

The hypotheses are the standing validity facts for source Yul programs:
* `SVStmts` — every identifier is `NUL`-free (`NotFresh`) and binder lists are
  duplicate-free;
* `WellFormed` — per-block distinct function names;
* `NormalForm.WellScoped` — every referenced name resolves;
* `WScopedStmts []`/`FScopedStmts` — no variable or function shadows a visible
  one.
-/

namespace YulEvmCompiler.Optimizer.Normalize

open YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-- A whole-program run's final variable environment is empty: the root block
restores everything it declared over the initially empty environment. -/
theorem run_block_env_nil {funs : FunEnv D} {st0 : D.State} {prog : Block D.Op}
    {V' : VEnv D} {st' : D.State} {o : Outcome}
    (h : Step D funs ([] : VEnv D) st0 (.stmt (.block prog)) (.sres V' st' o)) :
    V' = [] := by
  cases h with
  | block hb => simp [restore]

/-- A renamed environment is empty iff the original is. -/
theorem renVEnv_eq_nil {σ : Ident → Ident} {V : VEnv D} (h : renVEnv σ V = []) : V = [] := by
  cases V with
  | nil => rfl
  | cons p rest => simp [renVEnv] at h

/-- The trivial variable-renaming configuration at the empty environment. -/
theorem renCfg_empty : RenCfg (substOf ([] : Subst)) ([] : VEnv D) 0 :=
  ⟨fun p hp => (List.not_mem_nil hp).elim,
    fun z _ => by simp [substOf],
    fun p hp => (List.not_mem_nil hp).elim,
    fun p hp => (List.not_mem_nil hp).elim⟩

/-- The trivial function-renaming configuration at the empty environment. -/
theorem renFCfg_empty : RenFCfg (substOf ([] : Subst)) ([] : FunEnv D) 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    simp [funNamesOf] at ha
  · intro z _
    simp [substOf]
  · intro a ha
    simp [funNamesOf] at ha
  · intro a ha
    simp [funNamesOf] at ha

/-- **Semantic soundness of disambiguation** — the `GlobalPass` obligation:
for a valid source block, the disambiguated program has exactly the same
whole-program behaviour. -/
theorem disambiguate_runEquivBlock (b : Block D.Op)
    (hsv : SVStmts b) (hwf : WellFormed b) (hns : NormalForm.WellScoped b)
    (hws : WScopedStmts ([] : List Ident) b)
    (hfs : FScopedStmts (funNames b) b) :
    Optimizer.RunEquivBlock D b (disambiguate b) := by
  intro st0 V' st' o
  have hab := alpha_disambiguate b hsv hwf hns
  have hsc0 : WScopedCode (D := D) (([] : VEnv D).map Prod.fst) (.stmt (.block b)) := hws
  have hfsc0 : FScopedCode (D := D) (funNamesOf ([] : FunEnv D)) (.stmt (.block b)) := by
    show (∀ fn ∈ funNames b, fn ∉ funNamesOf ([] : FunEnv D)) ∧
      FScopedStmts (funNames b ++ funNamesOf ([] : FunEnv D)) b
    refine ⟨fun fn _ hc => by simp [funNamesOf] at hc, ?_⟩
    show FScopedStmts (funNames b ++ ([] : List Ident)) b
    rw [List.append_nil]
    exact hfs
  have hns0 : NScopedCode (D := D) (([] : VEnv D).map Prod.fst)
      (funNamesOf ([] : FunEnv D)) (.stmt (.block b)) := by
    show NormalForm.ScopedStmts ([] : List Ident)
      (funNamesOf ([] : FunEnv D) ++ NormalForm.funDefNames b) b
    show NormalForm.ScopedStmts ([] : List Ident)
      (([] : List Ident) ++ NormalForm.funDefNames b) b
    rw [List.nil_append]
    exact hns
  constructor
  · intro h
    have hV' : V' = [] := run_block_env_nil h
    subst hV'
    obtain ⟨hstep, -⟩ := sim_fwd (funs₂ := ([] : FunEnv D)) h renCfg_empty renFCfg_empty
      trivial hsc0 hfsc0 hns0 (.stmt (.blockD hab))
    exact hstep
  · intro h
    have hV' : V' = [] := run_block_env_nil h
    subst hV'
    obtain ⟨res₁, hstep, hreq, -⟩ := sim_bwd (funs₁ := ([] : FunEnv D)) h rfl renCfg_empty
      renFCfg_empty trivial hsc0 hfsc0 hns0 (.stmt (.blockD hab))
    obtain ⟨V₁', hres₁eq, hV₁⟩ := renRes_sres_inv hreq
    subst hres₁eq
    have hV₁nil : V₁' = [] := renVEnv_eq_nil hV₁.symm
    subst hV₁nil
    exact hstep

end YulEvmCompiler.Optimizer.Normalize
