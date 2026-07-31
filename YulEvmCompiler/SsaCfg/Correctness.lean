import YulEvmCompiler.Correctness
import YulEvmCompiler.SsaCfg.Compile
import YulEvmCompiler.SsaCfg.Sem
import YulEvmCompiler.Optimizer.Spec.EvmBackend
/-!
# YulEvmCompiler.SsaCfg.Correctness

The SSA backend's correctness theorem, `compileViaSsa_correct`, with the
**same statement** as `compile_correct` — and its packaging as the second
`Optimizer.EvmBackend` instance.

The proof decomposes along the pipeline, mirroring `Correctness.lean`:

1. `ofBlock_sound` — construction: a Yul `Run` derivation maps to an
   SSA-CFG execution with the same final state and outcome;
2. `optimizeProg_sound` — the SSA pass pipeline preserves SSA executions;
3. `emitProg_asteps`/`emitProg_ahalt` — code generation: an SSA execution
   maps to an Asm trace over the emitted program (the symbolic-stack
   tracking in `ToAsm` is the simulation invariant);
4. the composition below is **fully proved**: it transports the trace
   through the verified Asm peephole (`Peephole.optimizeAsm_asteps`/
   `_ahalt`) and lowers it with the verified Phase B
   (`asteps_sim`/`arun_halt_sim`), exactly as the classic backend does —
   no Phase B, peephole, certificate, or assembler proof is reopened.

The three simulation lemmas (1–3) are the deliberate `sorry` frontier of
this branch — see the PR description; everything else in this file is real.
-/

namespace YulEvmCompiler.SsaCfg

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM (U256 EvmState Op evmWithExternal)
open YulSemantics (Outcome VEnv)
open YulEvmCompiler

variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates

/-- **Construction soundness** (proof in progress): if the construction
accepts `prog` and the Yul semantics runs it, the SSA program runs to the
same final state and outcome. Non-local top-level outcomes
(`break`/`continue`/`leave`) are impossible because the construction rejects
them (no loop/function context at the top level). -/
theorem ofBlock_sound {prog : YulSemantics.Block Op} {P : Prog}
    {yst0 : EvmState} {V' : VEnv yulD} {yst' : EvmState} {o : Outcome}
    (hof : ofBlock prog = some P)
    (hrun : YulSemantics.Run yulD prog yst0 V' yst' o) :
    Run (model := model) P yst0 yst' o := by
  sorry

/-- **SSA pass soundness** (proof in progress): the optimization pipeline
preserves SSA executions of well-formed programs. -/
theorem optimizeProg_sound {P : Prog} {yst0 yst' : EvmState} {o : Outcome}
    (hwf : P.wfCheck = true)
    (hrun : Run (model := model) P yst0 yst' o) :
    Run (model := model) (optimizeProg P) yst0 yst' o := by
  sorry

/-- **Codegen simulation, normal outcome** (proof in progress): a normal SSA
execution maps to an Asm trace from the program start to the end of the code
with an empty stack (main's `ret []` pops everything and jumps to the
terminal label). -/
theorem emitProg_asteps {P : Prog} {asm : List Asm} {yst0 yst' : EvmState}
    (hemit : ToAsm.emitProg P = some asm)
    (hrun : Run (model := model) P yst0 yst' .normal) :
    ASteps (model := model) asm ⟨asm, [], yst0⟩ ⟨[], [], yst'⟩ := by
  sorry

/-- **Codegen simulation, halting outcome** (proof in progress): a halting
SSA execution maps to an Asm trace reaching a configuration whose head
instruction halts with the source's final state. -/
theorem emitProg_ahalt {P : Prog} {asm : List Asm} {yst0 yst' : EvmState}
    (hemit : ToAsm.emitProg P = some asm)
    (hrun : Run (model := model) P yst0 yst' .halt) :
    ∃ conf, ASteps (model := model) asm ⟨asm, [], yst0⟩ conf ∧
      AHalt (model := model) asm conf yst' := by
  sorry

omit model in
/-- Invert a successful `finishProg` into the shared final gates. -/
theorem finishProg_inv {P : Prog} {is : List YulEvmCompiler.Instr}
    (h : finishProg P = some is) :
    ∃ asm : List Asm,
      ToAsm.emitProg P = some asm
      ∧ wfCheck asm = true
      ∧ stackOK2 (optimizeAsm asm) = true
      ∧ lowerProg (optimizeAsm asm) = some is := by
  unfold finishProg at h
  rcases hemit : ToAsm.emitProg P with _ | asm <;> rw [hemit] at h
  · exact absurd h (by simp)
  simp only [bind, Option.bind] at h
  by_cases hwf : wfCheck asm
  · by_cases hstk : stackOK2 (optimizeAsm asm)
    · simp only [hwf, hstk, Bool.not_true, Bool.false_eq_true, if_false,
        if_true] at h
      exact ⟨asm, rfl, hwf, hstk, h⟩
    · simp [hwf, hstk] at h
  · simp [hwf] at h

omit model in
/-- Invert a successful `compileViaSsa`: the construction succeeded, and the
accepted bytecode came from `finishProg` on either the optimized or the
original SSA program (the best-of-two emission). -/
theorem compileViaSsa_inv {prog : YulSemantics.Block Op}
    {is : List YulEvmCompiler.Instr}
    (h : compileViaSsa prog = some is) :
    ∃ (P Q : Prog),
      ofBlock prog = some P
      ∧ (Q = optimizeProg P ∨ Q = P)
      ∧ finishProg Q = some is := by
  unfold compileViaSsa at h
  rcases hof : ofBlock prog with _ | P <;> rw [hof] at h
  · exact absurd h (by simp)
  simp only [bind, Option.bind] at h
  split at h
  · rename_i a b h1 h2
    split at h
    · obtain rfl := Option.some.inj h
      exact ⟨P, optimizeProg P, rfl, Or.inl rfl, h1⟩
    · obtain rfl := Option.some.inj h
      exact ⟨P, P, rfl, Or.inr rfl, h2⟩
  · rename_i a h1 h2
    obtain rfl := Option.some.inj h
    exact ⟨P, optimizeProg P, rfl, Or.inl rfl, h1⟩
  · rename_i b h1 h2
    obtain rfl := Option.some.inj h
    exact ⟨P, P, rfl, Or.inr rfl, h2⟩
  · exact absurd h (by simp)

/-- **The shared gate composition is correct** for any SSA program whose
execution matches the source run: transport the Asm trace through the
verified peephole and Phase B, exactly as `compile_correct` does. This part
is fully proved — it rests on the codegen simulation lemmas above. -/
theorem finishProg_correct (hexternal : ExternalsRealized model)
    {Q : Prog} {is : List YulEvmCompiler.Instr}
    (hfin : finishProg Q = some is)
    {yst0 yst' : EvmState} {o : Outcome}
    (hssa : Run (model := model) Q yst0 yst' o) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (assemble is) s0 → StateMatch yst0 s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst' s' ∧
        ((o = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (o = .halt ∧ HaltedMatch yst' s')) := by
  obtain ⟨asm, hemit, hwf, hstk, hlow⟩ := finishProg_inv hfin
  have hnodup : (labelDefs asm).Nodup := (wfCheck_iff.mp hwf).nodup
  have hlen : (assembleBytes is).length = codeSize (optimizeAsm asm) :=
    lowerFrag_length hlow
  have hsmallO : codeSize (optimizeAsm asm) < 256 ^ labelWidth := by
    have := codeSize_optimizeAsm_le asm
    have := (wfCheck_iff.mp hwf).small
    omega
  cases hssa with
  | normal heb hexec =>
    have hsteps0 : ASteps (model := model) asm ⟨asm, [], yst0⟩ ⟨[], [], yst'⟩ :=
      emitProg_asteps hemit (.normal heb hexec)
    have hstepsO := Peephole.optimizeAsm_asteps hnodup hsteps0
    obtain ⟨bnd, Hb⟩ :=
      asteps_sim hexternal hlow hsmallO hstepsO
        (List.suffix_refl (optimizeAsm asm)) (stackOK2_run_bound hstk yst0)
    refine ⟨bnd, ?_⟩
    intro s0 hf hm hpc hstk0 hgas
    have hcm0 : ConfMatch (optimizeAsm asm) is ⟨optimizeAsm asm, [], yst0⟩ s0 :=
      ⟨by simpa using hf, hm, by rw [hpc]; simp, by rw [hstk0]; simp⟩
    obtain ⟨s1, hsteps1, hcm1, -⟩ := Hb s0 hcm0 hgas
    have hpc1 : s1.pc = UInt256.ofNat (assembleBytes is).length := by
      rw [hcm1.pc]; simp [hlen]
    have hframe1 : FrameOK (assemble is) s1 := by
      simpa using hcm1.frame
    obtain ⟨s2, hstep2, hsm2, hcs2, hhalt2, hret2⟩ :=
      stopStep (is := is) hframe1 hcm1.smatch (assemble_eq_mkCode is) hpc1 (by
        have hb := stackOK2_run_bound hstk yst0 _ hstepsO
        have hp : Operation.pushArity Operation.STOP = 0 := rfl
        have hq : Operation.popArity Operation.STOP = 0 := rfl
        dsimp only at hb
        rw [hcm1.stack]
        simp only [mapStk, List.length_map, hp, hq]
        omega)
    exact ⟨s2, hsteps1.snoc hstep2, hcs2, hsm2, Or.inl ⟨rfl, hhalt2, hret2⟩⟩
  | halt heb hexec =>
    obtain ⟨conf, hsteps0, hhalt0⟩ :=
      emitProg_ahalt hemit (.halt heb hexec)
    obtain ⟨confO, hstepsO, hhaltO⟩ :=
      Peephole.optimizeAsm_ahalt hnodup hsteps0 hhalt0
    obtain ⟨bnd, Hb⟩ :=
      arun_halt_sim hexternal hlow hsmallO hstepsO hhaltO
        (List.suffix_refl (optimizeAsm asm)) (stackOK2_run_bound hstk yst0)
    refine ⟨bnd, ?_⟩
    intro s0 hf hm hpc hstk0 hgas
    have hcm0 : ConfMatch (optimizeAsm asm) is ⟨optimizeAsm asm, [], yst0⟩ s0 :=
      ⟨by simpa using hf, hm, by rw [hpc]; simp, by rw [hstk0]; simp⟩
    obtain ⟨s', hsteps', hsm', hcs', hhm'⟩ := Hb s0 hcm0 hgas
    exact ⟨s', hsteps', hcs', hsm', Or.inr ⟨rfl, hhm'⟩⟩

/-- **SSA backend correctness** — the exact `compile_correct` statement for
`compileViaSsa`. The best-of-two emission dispatches to `finishProg_correct`
on either the optimized program (through the pass-soundness lemma) or the
original construction (which needs no pass soundness at all). -/
theorem compileViaSsa_correct (hexternal : ExternalsRealized model)
    {prog : YulSemantics.Block Op} {is : List YulEvmCompiler.Instr}
    (hcomp : compileViaSsa prog = some is)
    {yst0 : EvmState} {V' : VEnv yulD} {yst' : EvmState} {o : Outcome}
    (hrun : YulSemantics.Run yulD prog yst0 V' yst' o) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (assemble is) s0 → StateMatch yst0 s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst' s' ∧
        ((o = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (o = .halt ∧ HaltedMatch yst' s')) := by
  obtain ⟨P, Q, hof, hQ, hfin⟩ := compileViaSsa_inv hcomp
  have hbase : Run (model := model) P yst0 yst' o := ofBlock_sound hof hrun
  have hssa : Run (model := model) Q yst0 yst' o := by
    rcases hQ with rfl | rfl
    · exact optimizeProg_sound (ofBlock_wfCheck hof) hbase
    · exact hbase
  exact finishProg_correct hexternal hfin hssa

/-- The SSA backend, packaged under the generalized backend contract: the
second `Optimizer.EvmBackend` inhabitant, next to `EvmBackend.classic`. -/
def evmBackend : Optimizer.EvmBackend where
  compile := compileViaSsa
  correct := by
    intro model hext prog is hcomp yst0 V' yst' o hrun
    exact compileViaSsa_correct hext hcomp hrun

end YulEvmCompiler.SsaCfg
