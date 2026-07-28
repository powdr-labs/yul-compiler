import YulEvmCompiler.AsmSem
import YulEvmCompiler.AsmPeephole
set_option warningAsError true
/-!
# YulEvmCompiler.AsmPeepholeSound

Forward simulation for the Asm-level peephole optimizer
(`YulEvmCompiler.AsmPeephole`), against the phase-A step relation
(`YulEvmCompiler.AsmSem`).

`AStep` is parameterized by the *whole* program (jumps resolve labels to
suffixes via `findLabel`), so the soundness statement is a whole-program
forward simulation, not a local equivalence:

* `Match` — the configuration relation. Because the `push v ; swap1 ; pop ⟶
  pop ; push v` rewrite changes the intermediate stack shape mid-window,
  `Match` carries two "in-flight" constructors (`mid1`, `mid2`) besides the
  synchronized `sync` state.
* `step_sim` / `steps_sim` / `halt_sim` — every source `AStep`/`AHalt` is
  matched by finitely many optimized steps preserving `Match`. The optimized
  side *stutters* only on the initial `push` of a window and always catches
  up within the window, so both runs reach the same endpoint.
* `optimizeAsm_asteps` / `optimizeAsm_ahalt` — the packaged bridge lemmas
  consumed by `YulEvmCompiler.Correctness`, which inserts `optimizeAsm`
  between `compileProgram` and `lowerProg`.
-/

namespace YulEvmCompiler.Peephole

open YulSemantics.EVM (U256 EvmState Op)

/-- A configuration correspondence between a source run (in `prog`) and its
optimized run (in `optimizeAsm prog`). `sync` is the aligned state; `mid1`
(source has done the window's `push`, optimized has done nothing) and `mid2`
(source has done `push; swap1`, optimized has done `pop`) capture the two
in-flight states inside a rewritten window, where the operand stacks differ. -/
inductive Match : AConf → AConf → Prop
  | sync {sc oc : List Asm} {σ : List AVal} {y : EvmState} :
      CodeRel sc oc → Match ⟨sc, σ, y⟩ ⟨oc, σ, y⟩
  | mid1 {v : U256} {n : Fin 16} (hn : n.val = 0) {S : List AVal}
      {sc oc : List Asm} {y : EvmState} :
      CodeRel sc oc →
      Match ⟨.swap n :: .pop :: sc, .word v :: S, y⟩
            ⟨.pop :: .push v :: oc, S, y⟩
  | mid2 {v : U256} {x : AVal} {ρ : List AVal} {sc oc : List Asm} {y : EvmState} :
      CodeRel sc oc →
      Match ⟨.pop :: sc, x :: .word v :: ρ, y⟩ ⟨.push v :: oc, ρ, y⟩

/-- Single-step forward simulation: one source `AStep` is simulated by finitely
many optimized steps preserving `Match`. -/
theorem step_sim [model : ExternalModel] {prog prog' : List Asm}
    (hpp : CodeRel prog prog') {a b a' : AConf}
    (hstep : AStep (model := model) prog a b) (hm : Match a a') :
    ∃ b', ASteps (model := model) prog' a' b' ∧ Match b b' := by
  cases hm with
  | @sync sc oc σ y hc =>
    cases hstep with
    | @push v c σ2 yst =>
      cases hc with
      | keep _ hc' => exact ⟨_, .single .push, .sync hc'⟩
      | window hn hc' => exact ⟨_, .refl _, .mid1 hn hc'⟩
    | @op yop args rets c σ2 yst yst' hb =>
      cases hc with
      | keep _ hc' => exact ⟨_, .single (.op hb), .sync hc'⟩
    | @dup n v τ ρ c yst hτ =>
      cases hc with
      | keep _ hc' => exact ⟨_, .single (.dup hτ), .sync hc'⟩
    | @swap n aa bb τ ρ c yst hτ =>
      cases hc with
      | keep _ hc' => exact ⟨_, .single (.swap hτ), .sync hc'⟩
    | @pop v c σ2 yst =>
      cases hc with
      | keep _ hc' => exact ⟨_, .single .pop, .sync hc'⟩
    | @label l c σ2 yst =>
      cases hc with
      | keep _ hc' => exact ⟨_, .single .label, .sync hc'⟩
    | @jump l c c'0 σ2 yst hf =>
      cases hc with
      | keep _ hc' =>
        obtain ⟨otgt, ho, hr⟩ := codeRel_findLabel hpp hf
        exact ⟨_, .single (.jump ho), .sync hr⟩
    | @jumpiTaken l v c c'0 σ2 yst hv hf =>
      cases hc with
      | keep _ hc' =>
        obtain ⟨otgt, ho, hr⟩ := codeRel_findLabel hpp hf
        exact ⟨_, .single (.jumpiTaken hv ho), .sync hr⟩
    | @jumpiFall l v c σ2 yst hv =>
      cases hc with
      | keep _ hc' => exact ⟨_, .single (.jumpiFall hv), .sync hc'⟩
    | @pushLabel l c σ2 yst hl =>
      cases hc with
      | keep _ hc' =>
        exact ⟨_, .single (.pushLabel (by rw [← codeRel_labelDefs hpp]; exact hl)), .sync hc'⟩
    | @dynJump l c c'0 σ2 yst hf =>
      cases hc with
      | keep _ hc' =>
        obtain ⟨otgt, ho, hr⟩ := codeRel_findLabel hpp hf
        exact ⟨_, .single (.dynJump ho), .sync hr⟩
  | @mid1 v n hn S sc oc y hc =>
    cases hstep with
    | @swap n2 aa bb τ ρ c yst hτ =>
      -- code head is `swap n`; τ.length = n.val = 0 ⇒ τ = []
      obtain rfl : τ = [] := List.length_eq_zero_iff.mp (hτ.trans hn)
      -- opt does one `pop`, landing in the `mid2` state
      exact ⟨_, .single .pop, .mid2 hc⟩
  | @mid2 v x ρ sc oc y hc =>
    cases hstep with
    | @pop v2 c σ2 yst =>
      exact ⟨_, .single .push, .sync hc⟩

/-- Multi-step forward simulation (reflexive-transitive closure). -/
theorem steps_sim [model : ExternalModel] {prog prog' : List Asm}
    (hpp : CodeRel prog prog') {a b a' : AConf}
    (hsteps : ASteps (model := model) prog a b) (hm : Match a a') :
    ∃ b', ASteps (model := model) prog' a' b' ∧ Match b b' := by
  induction hsteps generalizing a' with
  | refl a => exact ⟨a', .refl _, hm⟩
  | head hstep _ ih =>
    obtain ⟨c', hc', hmc⟩ := step_sim hpp hstep hm
    obtain ⟨b', hb', hmb⟩ := ih hmc
    exact ⟨b', hc'.trans hb', hmb⟩

/-- Halting-step simulation. -/
theorem halt_sim [model : ExternalModel] {prog prog' : List Asm}
    {b a' : AConf} {yf : EvmState}
    (hhalt : AHalt (model := model) prog b yf) (hm : Match b a') :
    AHalt (model := model) prog' a' yf := by
  cases hhalt with
  | @op yop args c σ yst yst' hb =>
    cases hm with
    | @sync sc oc σ2 y hc =>
      cases hc with
      | keep _ hc' => exact .op hb

/-! ### Endpoint inversion and the packaged bridge lemmas -/

/-- With empty source code, `Match` forces the optimized configuration to be
identical (same empty code, stack, and state). -/
theorem match_empty_left {σ : List AVal} {y : EvmState}
    {a' : AConf} (hm : Match ⟨[], σ, y⟩ a') :
    a' = ⟨[], σ, y⟩ := by
  cases hm with
  | sync hc => rw [codeRel_nil_left hc]

/-- **Bridge (normal case).** A full source run from the whole program to
empty code is simulated by the optimized program to the same endpoint. -/
theorem optimizeAsm_asteps [model : ExternalModel] {asm : List Asm}
    {σ σf : List AVal} {y yf : EvmState}
    (hsteps : ASteps (model := model) asm ⟨asm, σ, y⟩ ⟨[], σf, yf⟩) :
    ASteps (model := model) (optimizeAsm asm) ⟨optimizeAsm asm, σ, y⟩ ⟨[], σf, yf⟩ := by
  have hcr := codeRel_optimize asm
  obtain ⟨b', hb', hmb⟩ := steps_sim hcr hsteps (.sync hcr)
  rw [match_empty_left hmb] at hb'
  exact hb'

/-- **Bridge (halt case).** A source run that halts is simulated by the
optimized program to a halting configuration with the same final state. -/
theorem optimizeAsm_ahalt [model : ExternalModel] {asm : List Asm}
    {σ : List AVal} {y : EvmState} {bconf : AConf} {yf : EvmState}
    (hsteps : ASteps (model := model) asm ⟨asm, σ, y⟩ bconf)
    (hhalt : AHalt (model := model) asm bconf yf) :
    ∃ b', ASteps (model := model) (optimizeAsm asm) ⟨optimizeAsm asm, σ, y⟩ b'
      ∧ AHalt (model := model) (optimizeAsm asm) b' yf := by
  have hcr := codeRel_optimize asm
  obtain ⟨b', hb', hmb⟩ := steps_sim hcr hsteps (.sync hcr)
  exact ⟨b', hb', halt_sim hhalt hmb⟩

end YulEvmCompiler.Peephole
