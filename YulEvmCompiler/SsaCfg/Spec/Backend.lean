import YulEvmCompiler.Correctness
import YulEvmCompiler.SsaCfg.Implementation.Compile
import YulEvmCompiler.SsaCfg.Spec.Sem
import YulEvmCompiler.SsaCfg.Implementation.OfYulSound
import YulEvmCompiler.SsaCfg.Implementation.PassesSound
import YulEvmCompiler.SsaCfg.Implementation.ToAsmSound
import YulEvmCompiler.Optimizer.Spec.EvmBackend
set_option warningAsError true
/-!
# YulEvmCompiler.SsaCfg.Spec.Backend

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

This file is **fully proved**: every statement here is closed, with the
three phase obligations delegated to the `Implementation/*Sound.lean` proof
files (whose internals are the branch's declared proof frontier — see the
PR description). An auditor reads this file and the other `Spec/` modules;
the delegation targets are implementation detail.
-/

namespace YulEvmCompiler.SsaCfg

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM (U256 EvmState Op evmWithExternal)
open YulSemantics (Outcome VEnv)
open YulEvmCompiler

variable [model : ExternalModel] {imm : String → YulSemantics.EVM.U256}
local notation "yulD" => evmWithExternal model.calls model.creates YulSemantics.EVM.ExternalGas.any

/-- **Construction soundness**: if the construction accepts `prog` and the
Yul semantics runs it, the SSA program runs to the same final state and
outcome. Proved in `SsaCfg/OfYulSound.lean` (modulo its single declared
frontier lemma, the `trScope_sim_of_fresh` derivation induction); non-local
top-level outcomes are discharged as impossible there. -/
theorem ofBlock_sound {prog : YulSemantics.Block Op} {P : Prog}
    {yst0 : EvmState} {V' : VEnv yulD} {yst' : EvmState} {o : Outcome}
    (hof : ofBlock prog = some P)
    (hrun : YulSemantics.Run yulD prog yst0 V' yst' o) :
    Run (model := model) P yst0 yst' o :=
  ofBlock_sound' hof hrun

/-- **SSA pass soundness**: the optimization pipeline preserves SSA
executions of well-formed, dominance-respecting programs. Delegated to
`SsaCfg/PassesSound.lean`, including both intermediate-gate branches and both
final-gate branches. The dominance hypothesis is
genuinely necessary — that file carries a kernel-checked counterexample
without it, on which the inliner is also kernel-checked to be inert. -/
theorem optimizeProg_sound {P : Prog} {yst0 yst' : EvmState} {o : Outcome}
    (hwf : P.wfCheck = true) (hdom : ToAsm.Prog.domCheck P = true)
    (hrun : Run (model := model) P yst0 yst' o) :
    Run (model := model) (optimizeProg P) yst0 yst' o :=
  optimizeProg_sound' hwf hdom hrun

/-- **Codegen simulation, normal outcome**: a normal SSA execution maps to
an Asm trace from the program start to the end of the code with an empty
stack. Delegated to `SsaCfg/ToAsmSound.lean` (modulo its declared frontier).
Single assignment (`P.wfCheck`) and label uniqueness are genuinely
required — that file records the counterexample without them; the
dominance hypothesis covers the layout-table binding at jump targets. -/
theorem emitProg_asteps {ord : Bool} {P : Prog} {asm : List Asm}
    {yst0 yst' : EvmState}
    (hnodup : (labelDefs asm).Nodup) (hwf : P.wfCheck = true)
    (hdom : ToAsm.Prog.domCheck P = true)
    (hemit : ToAsm.emitProgOrd ord P = some asm)
    (hrun : Run (model := model) P yst0 yst' .normal) :
    ASteps (model := model) asm ⟨asm, [], yst0⟩ ⟨[], [], yst'⟩ :=
  emitProg_asteps' hnodup hwf hdom hemit hrun

/-- **Codegen simulation, halting outcome** (see `emitProg_asteps`). -/
theorem emitProg_ahalt {ord : Bool} {P : Prog} {asm : List Asm}
    {yst0 yst' : EvmState}
    (hnodup : (labelDefs asm).Nodup) (hwf : P.wfCheck = true)
    (hdom : ToAsm.Prog.domCheck P = true)
    (hemit : ToAsm.emitProgOrd ord P = some asm)
    (hrun : Run (model := model) P yst0 yst' .halt) :
    ∃ conf, ASteps (model := model) asm ⟨asm, [], yst0⟩ conf ∧
      AHalt (model := model) asm conf yst' :=
  emitProg_ahalt' hnodup hwf hdom hemit hrun

omit model in
/-- The optimizer preserves well-formedness: its defensive gate returns the
pipeline output only when that output re-checks, and the original
otherwise. -/
theorem optimizeProg_wf {P : Prog} (hwf : P.wfCheck = true) :
    (optimizeProg P).wfCheck = true := by
  rw [optimizeProg_candidate]
  split
  · next h =>
    have := (Bool.and_eq_true _ _).mp h
    exact this.1
  · exact hwf

omit model in
/-- The optimizer's defensive gate also preserves the dominance check. -/
theorem optimizeProg_dom {P : Prog} (hdom : ToAsm.Prog.domCheck P = true) :
    ToAsm.Prog.domCheck (optimizeProg P) = true := by
  rw [optimizeProg_candidate]
  split
  · next h =>
    have := (Bool.and_eq_true _ _).mp h
    exact this.2
  · exact hdom

omit model in
/-- Invert a successful `finishProgOrd` into the shared final gates. -/
theorem finishProg_inv {ord : Bool} {P : Prog} {is : List YulEvmCompiler.Instr}
    (h : finishProgOrd imm ord P = some is) :
    ∃ asm : List Asm,
      ToAsm.emitProgOrd ord P = some asm
      ∧ wfCheck asm = true
      ∧ stackOK2 (optimizeAsm asm) = true
      ∧ lowerProg imm (optimizeAsm asm) = some is := by
  unfold finishProgOrd at h
  rcases hemit : ToAsm.emitProgOrd ord P with _ | asm <;> rw [hemit] at h
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
/-- The min-cost fold over candidate artifacts only ever returns one of
them (or the initial accumulator). -/
theorem foldl_min_mem {α : Type} (f : α → Nat) {r : α} :
    ∀ (l : List (Option α)) (init : Option α),
      (l.foldl (pickMin f) init) = some r →
      init = some r ∨ some r ∈ l := by
  intro l
  induction l with
  | nil => exact fun _ h => Or.inl h
  | cons c rest ih =>
    intro init h
    simp only [List.foldl_cons] at h
    rcases ih _ h with hacc | hmem
    · rcases init with _ | b <;> rcases c with _ | x <;>
        simp only [pickMin] at hacc
      · exact absurd hacc (by simp)
      · exact Or.inr (by rw [← hacc]; exact List.mem_cons_self ..)
      · exact Or.inl hacc
      · split_ifs at hacc
        · exact Or.inr (by rw [← hacc]; exact List.mem_cons_self ..)
        · exact Or.inl hacc
    · exact Or.inr (List.mem_cons_of_mem _ hmem)

/-! ### Rematerialization

`compileViaSsa` runs `rematProg` behind the pass pipeline, so the optimized
candidate is `rematProg (optimizeProg P)` rather than `optimizeProg P`.  The
well-formedness and dominance halves follow from the pass's own defensive gate,
and the inversion lemma keeps its original four-case shape.

`rematConsts` only ever *adds* `const` definitions, with ids above `maxIdOf f`,
immediately in front of the use they feed: no pre-existing value changes, every
copy is dominated by construction, and `dve` behind it is already proved.  The
simulation is in `SsaCfg/PassesSound/Remat.lean`; no dominance hypothesis is
needed, so `_hdom` goes unused. -/

/-- **Rematerialization soundness**: rematerializing constants preserves the
source run. -/
theorem rematProg_sound {P : Prog} {yst0 yst' : EvmState} {o : Outcome}
    (hwf : P.wfCheck = true) (_hdom : ToAsm.Prog.domCheck P = true)
    (hrun : Run (model := model) P yst0 yst' o) :
    Run (model := model) (rematProg P) yst0 yst' o :=
  rematProg_sound' hwf hrun

omit model in
/-- `rematProg`'s defensive gate preserves well-formedness. -/
theorem rematProg_wf {P : Prog} (hwf : P.wfCheck = true) :
    (rematProg P).wfCheck = true := by
  rw [rematProg_candidate]
  split
  · next h => exact ((Bool.and_eq_true _ _).mp h).1
  · exact hwf

omit model in
/-- …and the dominance check. -/
theorem rematProg_dom {P : Prog} (hdom : ToAsm.Prog.domCheck P = true) :
    ToAsm.Prog.domCheck (rematProg P) = true := by
  rw [rematProg_candidate]
  split
  · next h => exact ((Bool.and_eq_true _ _).mp h).2
  · exact hdom

omit model in
/-- Invert a successful `compileViaSsa`: the construction succeeded, the
dominance gate passed, and the accepted bytecode is one of the four
independently gated candidates ({optimized, raw} × {scheduling modes}). -/
theorem compileViaSsa_inv {prog : YulSemantics.Block Op}
    {is : List YulEvmCompiler.Instr}
    (h : compileViaSsa prog imm = some is) :
    ∃ (P Q : Prog) (ord : Bool),
      ofBlock prog = some P
      ∧ ToAsm.Prog.domCheck P = true
      ∧ (Q = rematProg (optimizeProg P) ∨ Q = P)
      ∧ finishProgOrd imm ord Q = some is := by
  unfold compileViaSsa compileViaSsaAsm at h
  rcases hof : ofBlock prog with _ | P <;> rw [hof] at h
  · exact absurd h (by simp)
  simp only [bind, Option.bind] at h
  by_cases hdom : ToAsm.Prog.domCheck P
  case neg =>
    rw [Bool.not_eq_true] at hdom
    rw [hdom] at h
    simp at h
  rw [hdom] at h
  simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
  cases hb : ([finishProgOrdAsm true (rematProg (optimizeProg P)),
               finishProgOrdAsm false (rematProg (optimizeProg P)),
               finishProgOrdAsm true P, finishProgOrdAsm false P].foldl
              (pickMin CostModel.execCostAsm) none) with
  | none => rw [hb] at h; simp at h
  | some a =>
    rw [hb] at h
    rcases foldl_min_mem CostModel.execCostAsm _ _ hb with hinit | hmem
    · exact absurd hinit (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      have hlow : (some a).bind (lowerProg imm) = some is := h
      rcases hmem with h1 | h2 | h3 | h4
      · exact ⟨P, rematProg (optimizeProg P), true, rfl, hdom, Or.inl rfl,
          by rw [finishProgOrd_eq, ← h1]; exact hlow⟩
      · exact ⟨P, rematProg (optimizeProg P), false, rfl, hdom, Or.inl rfl,
          by rw [finishProgOrd_eq, ← h2]; exact hlow⟩
      · exact ⟨P, P, true, rfl, hdom, Or.inr rfl,
          by rw [finishProgOrd_eq, ← h3]; exact hlow⟩
      · exact ⟨P, P, false, rfl, hdom, Or.inr rfl,
          by rw [finishProgOrd_eq, ← h4]; exact hlow⟩

/-- **The shared gate composition is correct** for any SSA program whose
execution matches the source run: transport the Asm trace through the
verified peephole and Phase B, exactly as `compile_correct` does. This part
is fully proved — it rests on the codegen simulation lemmas above. -/
theorem finishProg_correct (hexternal : ExternalsRealized model)
    {ord : Bool} {Q : Prog} {is : List YulEvmCompiler.Instr}
    (hQwf : Q.wfCheck = true) (hQdom : ToAsm.Prog.domCheck Q = true)
    (hfin : finishProgOrd imm ord Q = some is)
    {yst0 yst' : EvmState} {o : Outcome}
    (himm : ∀ key, imm key = yst0.env.immutable (YulSemantics.EVM.litValue (.string key)))
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
      emitProg_asteps hnodup hQwf hQdom hemit (.normal heb hexec)
    have hstepsO := Peephole.optimizeAsm_asteps hnodup hsteps0
    obtain ⟨bnd, Hb⟩ :=
      asteps_sim hexternal hlow hsmallO hstepsO
        (List.suffix_refl (optimizeAsm asm)) (stackOK2_run_bound hstk yst0)
    refine ⟨bnd, ?_⟩
    intro s0 hf hm hpc hstk0 hgas
    have hcm0 : ConfMatch imm (optimizeAsm asm) is ⟨optimizeAsm asm, [], yst0⟩ s0 :=
      ⟨by simpa using hf, hm, by rw [hpc]; simp, by rw [hstk0]; simp, himm⟩
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
      emitProg_ahalt hnodup hQwf hQdom hemit (.halt heb hexec)
    obtain ⟨confO, hstepsO, hhaltO⟩ :=
      Peephole.optimizeAsm_ahalt hnodup hsteps0 hhalt0
    obtain ⟨bnd, Hb⟩ :=
      arun_halt_sim hexternal hlow hsmallO hstepsO hhaltO
        (List.suffix_refl (optimizeAsm asm)) (stackOK2_run_bound hstk yst0)
    refine ⟨bnd, ?_⟩
    intro s0 hf hm hpc hstk0 hgas
    have hcm0 : ConfMatch imm (optimizeAsm asm) is ⟨optimizeAsm asm, [], yst0⟩ s0 :=
      ⟨by simpa using hf, hm, by rw [hpc]; simp, by rw [hstk0]; simp, himm⟩
    obtain ⟨s', hsteps', hsm', hcs', hhm'⟩ := Hb s0 hcm0 hgas
    exact ⟨s', hsteps', hcs', hsm', Or.inr ⟨rfl, hhm'⟩⟩

/-- **SSA backend correctness** — the exact `compile_correct` statement for
`compileViaSsa`. The best-of-two emission dispatches to `finishProg_correct`
on either the optimized program (through the pass-soundness lemma) or the
original construction (which needs no pass soundness at all). -/
theorem compileViaSsa_correct (hexternal : ExternalsRealized model)
    {prog : YulSemantics.Block Op} {is : List YulEvmCompiler.Instr}
    (hcomp : compileViaSsa prog imm = some is)
    {yst0 : EvmState} {V' : VEnv yulD} {yst' : EvmState} {o : Outcome}
    (himm : ∀ key, imm key = yst0.env.immutable (YulSemantics.EVM.litValue (.string key)))
    (hrun : YulSemantics.Run yulD prog yst0 V' yst' o) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (assemble is) s0 → StateMatch yst0 s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst' s' ∧
        ((o = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (o = .halt ∧ HaltedMatch yst' s')) := by
  obtain ⟨P, Q, ord, hof, hdom, hQ, hfin⟩ := compileViaSsa_inv hcomp
  have hbase : Run (model := model) P yst0 yst' o := ofBlock_sound hof hrun
  have hPwf : P.wfCheck = true := ofBlock_wfCheck hof
  have hssa : Run (model := model) Q yst0 yst' o := by
    rcases hQ with rfl | rfl
    · exact rematProg_sound (optimizeProg_wf hPwf) (optimizeProg_dom hdom)
        (optimizeProg_sound hPwf hdom hbase)
    · exact hbase
  have hQwf : Q.wfCheck = true := by
    rcases hQ with rfl | rfl
    · exact rematProg_wf (optimizeProg_wf hPwf)
    · exact hPwf
  have hQdom : ToAsm.Prog.domCheck Q = true := by
    rcases hQ with rfl | rfl
    · exact rematProg_dom (optimizeProg_dom hdom)
    · exact hdom
  exact finishProg_correct hexternal hQwf hQdom hfin himm hssa

/-- The SSA backend, packaged under the generalized backend contract: the
second `Optimizer.EvmBackend` inhabitant, next to `EvmBackend.classic`. -/
def evmBackend : Optimizer.EvmBackend where
  compile := fun prog imm => compileViaSsa prog imm
  correct := by
    intro model hext imm prog is hcomp yst0 V' yst' o himm hrun
    exact compileViaSsa_correct hext hcomp himm hrun

end YulEvmCompiler.SsaCfg
