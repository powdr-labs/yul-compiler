import YulEvmCompiler.FnLayout

/-!
# YulEvmCompiler.FnSim

Phase 4 of the function-verification plan (see `FUNCTIONS_PLAN.md`): the
*code-fixed* simulation relation the function-aware induction needs.

The existing `SimSP` (in `Correctness`) quantifies over the whole `code` and an
arbitrary suffix `post`, which is exactly what makes it position-independent and
composable — but it also means it cannot express a **call**, whose callee body
lives inside that universally-quantified `post`. `SimSPC` fixes `code`, so a
separate `ProgLayout code` hypothesis can locate every callee. Every
code-quantified `SimSP` result lifts into `SimSPC` for any concrete code
(`SimSP.toSimSPC`), and `SimSPC` composes just like `SimSP` (`SimSPC.comp`).
-/

namespace YulEvmCompiler

open EvmSemantics EvmSemantics.EVM
open YulSemantics.EVM (EvmState)
open YulSemantics (VEnv)

/-- Code-fixed, position-aware statement simulation: like `SimSP`, but the whole
program `code` is a fixed parameter rather than universally quantified, so a
`ProgLayout code` side-hypothesis can be used to reach callees. -/
def SimSPC (code : ByteArray) (pcc : Nat) (yst : EvmState) (V : VEnv yul)
    (is : List Instr) (yst' : EvmState) (V' : VEnv yul) : Prop :=
  ∃ b : Nat, ∀ (preIs : List Instr) (post : List UInt8) (σ : List UInt256) (s : State),
    code = mkCode (assembleBytes preIs ++ assembleBytes is ++ post) →
    (assembleBytes preIs).length = pcc →
    FrameOK code s → StateMatch yst s →
    s.pc = UInt256.ofNat pcc →
    s.stack = vimg V ++ σ →
    b ≤ s.gasAvailable →
    ∃ s', Steps s s' ∧ FrameOK code s' ∧ StateMatch yst' s'
      ∧ s'.pc = UInt256.ofNat (pcc + (assembleBytes is).length)
      ∧ s'.stack = vimg V' ++ σ
      ∧ s.gasAvailable - b ≤ s'.gasAvailable

/-- Every code-quantified `SimSP` result specializes to `SimSPC` at any concrete
`code`. This is the bridge that carries the function-free fragment (proved via
the existing `Correctness.sim`) into the code-fixed setting. -/
theorem SimSP.toSimSPC {pcc : Nat} {yst : EvmState} {V : VEnv yul} {is : List Instr}
    {yst' : EvmState} {V' : VEnv yul} (h : SimSP pcc yst V is yst' V') (code : ByteArray) :
    SimSPC code pcc yst V is yst' V' := by
  obtain ⟨b, H⟩ := h
  exact ⟨b, fun preIs post σ s => H code preIs post σ s⟩

/-- `SimSPC` composes sequentially, exactly like `SimSP.comp`. -/
theorem SimSPC.comp {code : ByteArray} {pcc : Nat} {yst : EvmState} {V V1 V2 : VEnv yul}
    {is1 is2 : List Instr} {yst1 yst2 : EvmState}
    (h1 : SimSPC code pcc yst V is1 yst1 V1)
    (h2 : SimSPC code (pcc + (assembleBytes is1).length) yst1 V1 is2 yst2 V2) :
    SimSPC code pcc yst V (is1 ++ is2) yst2 V2 := by
  obtain ⟨b1, H1⟩ := h1
  obtain ⟨b2, H2⟩ := h2
  refine ⟨b1 + b2, ?_⟩
  intro preIs post σ s hcode hpre hf hm hpc hstk hgas
  obtain ⟨s1, st1, hf1, hm1, hpc1, hstk1, hg1⟩ :=
    H1 preIs (assembleBytes is2 ++ post) σ s
      (by rw [hcode]; congr 1; simp [assembleBytes_append]) hpre hf hm hpc hstk (by omega)
  obtain ⟨s2, st2, hf2, hm2, hpc2, hstk2, hg2⟩ :=
    H2 (preIs ++ is1) post σ s1
      (by rw [hcode]; congr 1; simp [assembleBytes_append, List.append_assoc])
      (by rw [assembleBytes_append, List.length_append, hpre]) hf1 hm1
      hpc1 hstk1 (by omega)
  refine ⟨s2, st1.append st2, hf2, hm2, ?_, hstk2, by omega⟩
  have hpceq : pcc + (assembleBytes is1).length + (assembleBytes is2).length
      = pcc + (assembleBytes (is1 ++ is2)).length := by
    rw [assembleBytes_append, List.length_append]; omega
  rw [hpc2, hpceq]

/-- The empty statement fragment: `SimSPC` for `[]` (no steps, same state). -/
theorem SimSPC.nil {code : ByteArray} {pcc : Nat} {yst : EvmState} {V : VEnv yul} :
    SimSPC code pcc yst V [] yst V := by
  refine ⟨0, fun preIs post σ s _ _ hf hm hpc hstk _ => ?_⟩
  exact ⟨s, .refl s, hf, hm, by simpa using hpc, hstk, by omega⟩

end YulEvmCompiler
