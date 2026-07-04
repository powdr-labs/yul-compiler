import YulEvmCompiler.SimAsm
import YulEvmCompiler.LowerCorrect
import YulEvmCompiler.OpStep

/-!
# YulEvmCompiler.Correctness

The **end-to-end correctness theorem** for the labeled-assembly pipeline
(`compile = compileProgram ≫ lowerProg`), composing the two proved
simulations:

* **Phase A** (`YulEvmCompiler.SimA.sim`): the Yul big-step semantics is
  simulated by the byte-free, gas-free Asm machine.
* **Phase B** (`asteps_sim`/`arun_halt_sim`): the Asm machine is simulated by
  the EVM small-step semantics on the assembled bytecode, with an
  existential gas bound.

The top-level Yul program is a block, so `Run` decomposes (block rule) into a
`.stmts` derivation over the hoisted top scope; `hoist_ok` establishes the
initial `FEnvOK`, and a trailing implicit `STOP` (`stopStep`) turns a
fall-through `.normal` outcome into `.Success`.
-/

namespace YulEvmCompiler

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM (U256 EvmState Op stepOp)
open YulSemantics (Outcome Ident VEnv)

/-- Invert a successful `compileProgram`: it hoisted the top scope,
checked its names `Nodup`, compiled the statements, and passed `wfCheck`. -/
theorem compileProgramAsm_inv {prog : YulSemantics.Block Op} {asm : List Asm}
    (h : compileProgram prog = some asm) :
    ∃ (scope : FScopeInfo) (n0 : Nat) (Γ' : List Ident) (n' : Nat),
      hoistInfos 0 prog = (scope, n0)
      ∧ (scope.map Prod.fst).Nodup
      ∧ compileStmts [scope] [] none none n0 prog = some (asm, Γ', n')
      ∧ wfCheck asm = true := by
  unfold compileProgram at h
  rcases hh : hoistInfos 0 prog with ⟨scope, n0⟩
  rw [hh] at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  · next hc =>
    have hnd : (scope.map Prod.fst).Nodup := by
      by_contra h'
      exact hc (by simp [h'])
    rcases hcs : compileStmts [scope] [] none none n0 prog with _ | ⟨asm2, Γ2, n2⟩
    · rw [hcs] at h; exact absurd h (by simp)
    · rw [hcs] at h
      change (if wfCheck asm2 = true then some asm2 else none) = some asm at h
      by_cases hwf : wfCheck asm2 = true
      · rw [if_pos hwf] at h
        obtain rfl := Option.some.inj h
        exact ⟨scope, n0, Γ2, n2, rfl, hnd, hcs, hwf⟩
      · rw [if_neg hwf] at h; exact absurd h (by simp)

/-! ### The main theorem -/

/-- **Compiler correctness** (Yul → labeled assembly → EVM bytecode; with
variables, nested blocks, `if`, `for`/`break`/`continue`, and
`function`/`leave`/calls, single-value returns). If `compile` accepts
`prog` and the Yul big-step semantics runs `prog` from `yst0` to `yst'` with
outcome `o`, then there is a gas bound `b` such that from *every* initial EVM
state that matches `yst0`, runs the assembled bytecode from `pc = 0` with an
empty stack and at least `b` gas, the EVM semantics reaches a matching final
state:

* `o = .normal` — the code runs off its end (implicit `STOP`) and halts with
  `.Success`;
* `o = .halt` — the code halts exactly as `yst'.halted` records. -/
theorem compile_correct {prog : YulSemantics.Block Op} {is : List Instr}
    (hcomp : compile prog = some is)
    {yst0 : EvmState} {V' : VEnv yul} {yst' : EvmState} {o : Outcome}
    (hrun : YulSemantics.Run yul prog yst0 V' yst' o) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (assemble is) s0 → StateMatch yst0 s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst' s' ∧
        ((o = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (o = .halt ∧ HaltedMatch yst' s')) := by
  -- unfold the pipeline
  rcases hpa : compileProgram prog with _ | asm
  · simp [compile, hpa] at hcomp
  · simp only [compile, hpa] at hcomp
    -- `hcomp : lowerProg asm = some is`
    obtain ⟨scope, n0, Γ', n', hh, hnd, hcs, hwf⟩ := compileProgramAsm_inv hpa
    have hnodup : (labelDefs asm).Nodup := (wfCheck_iff.mp hwf).nodup
    -- the block rule exposes the `.stmts` derivation over the hoisted scope
    cases hrun with
    | block hbody =>
      -- Phase A: simulate the statement sequence
      have hM := SimA.sim hnodup hbody
      have hout := hM [scope] none none n0 asm Γ' n' trivial trivial hcs
      -- the initial function environment agreement
      have hΦ0 : SimA.FEnvOK asm (YulSemantics.hoist yul prog :: []) [scope] :=
        SimA.hoist_ok SimA.FEnvOK.nil hh hnd hcs (List.infix_refl asm)
      -- (assembleBytes is).length = codeSize asm
      have hlen : (assembleBytes is).length = codeSize asm := lowerFrag_length hcomp
      cases o with
      | normal =>
        obtain ⟨-, -, hsimS⟩ := hout
        have hsteps0 := (hsimS hΦ0) [] [] [] (by simp)
        simp only [List.append_nil] at hsteps0
        obtain ⟨bnd, Hb⟩ := asteps_sim hcomp hsteps0 (List.suffix_refl asm)
        refine ⟨bnd, ?_⟩
        intro s0 hf hm hpc hstk hgas
        have hcm0 : ConfMatch asm is ⟨asm, [], yst0⟩ s0 :=
          ⟨hf, hm, by rw [hpc]; simp, by rw [hstk]; simp⟩
        obtain ⟨s1, hsteps1, hcm1, -⟩ := Hb s0 hcm0 hgas
        have hpc1 : s1.pc = UInt256.ofNat (assembleBytes is).length := by
          rw [hcm1.pc]; simp [hlen]
        obtain ⟨s2, hstep2, hsm2, hcs2, hhalt2, hret2⟩ :=
          stopStep (is := is) hcm1.frame hcm1.smatch (assemble_eq_mkCode is) hpc1
        exact ⟨s2, hsteps1.snoc hstep2, hcs2, hsm2, Or.inl ⟨rfl, hhalt2, hret2⟩⟩
      | halt =>
        have hAS := hout hΦ0
        obtain ⟨conf, hsteps0, hhalt0⟩ := hAS [] [] [] (by simp)
        simp only [List.append_nil] at hsteps0
        obtain ⟨bnd, Hb⟩ := arun_halt_sim hcomp hsteps0 hhalt0 (List.suffix_refl asm)
        refine ⟨bnd, ?_⟩
        intro s0 hf hm hpc hstk hgas
        have hcm0 : ConfMatch asm is ⟨asm, [], yst0⟩ s0 :=
          ⟨hf, hm, by rw [hpc]; simp, by rw [hstk]; simp⟩
        obtain ⟨s', hsteps', hsm', hcs', hhm'⟩ := Hb s0 hcm0 hgas
        exact ⟨s', hsteps', hcs', hsm', Or.inr ⟨rfl, hhm'⟩⟩
      | «break» => rcases hout with ⟨lc, hlc, -⟩; exact absurd hlc (by simp)
      | «continue» => rcases hout with ⟨lc, hlc, -⟩; exact absurd hlc (by simp)
      | leave => rcases hout with ⟨fc, hfc, -⟩; exact absurd hfc (by simp)

/-- Result-level corollary: the compiled bytecode `Eval`s to the
`ExecutionResult` the Yul outcome corresponds to (`.success` for a program
that falls through; `resultOf` of the recorded halt otherwise). -/
theorem compile_correct_eval {prog : YulSemantics.Block Op} {is : List Instr}
    (hcomp : compile prog = some is)
    {yst0 : EvmState} {V' : VEnv yul} {yst' : EvmState} {o : Outcome}
    (hrun : YulSemantics.Run yul prog yst0 V' yst' o) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (assemble is) s0 → StateMatch yst0 s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      (o = .normal → Eval s0 .success) ∧
      (o = .halt → ∃ hk, yst'.halted = some hk ∧ Eval s0 (resultOf hk)) := by
  obtain ⟨b, H⟩ := compile_correct hcomp hrun
  refine ⟨b, ?_⟩
  intro s0 hf hm hpc hstk hgas
  obtain ⟨s', hsteps, hcs', hm', hres⟩ := H s0 hf hm hpc hstk hgas
  constructor
  · intro ho
    subst ho
    rcases hres with ⟨_, hhalt, _⟩ | ⟨hcontra, _⟩
    · have hr : s'.toResult = .success := State.toResult_success s' hhalt
      rw [← hr]
      exact Eval.iff_steps_halted.mpr ⟨s', hsteps, by rw [hhalt]; simp, hcs', rfl⟩
    · exact absurd hcontra (by simp)
  · intro ho
    subst ho
    rcases hres with ⟨hcontra, _⟩ | ⟨_, hhm⟩
    · exact absurd hcontra (by simp)
    · obtain ⟨hk, hyst, hhmatch⟩ := hhm
      refine ⟨hk, hyst, ?_⟩
      have hdone : s'.halt ≠ .Running ∧ s'.toResult = resultOf hk := by
        rcases hk with ⟨kind, payload⟩
        cases kind with
        | stop =>
          have hhalt : s'.halt = .Success := hhmatch
          exact ⟨by rw [hhalt]; simp, by
            rw [State.toResult_success s' hhalt]; rfl⟩
        | ret =>
          obtain ⟨hhalt, hpl⟩ := hhmatch
          have hpl' : s'.hReturn.toList = payload := hpl
          refine ⟨by rw [hhalt]; simp, ?_⟩
          rw [State.toResult_returned s' hhalt]
          show ExecutionResult.returned s'.hReturn = .returned (mkCode payload)
          rw [← hpl', mkCode_toList]
        | revert =>
          obtain ⟨hhalt, hpl⟩ := hhmatch
          have hpl' : s'.hReturn.toList = payload := hpl
          refine ⟨by rw [hhalt]; simp, ?_⟩
          rw [State.toResult_reverted s' hhalt]
          show ExecutionResult.reverted s'.hReturn = .reverted (mkCode payload)
          rw [← hpl', mkCode_toList]
        | invalid =>
          have hhalt : s'.halt = .Exception .InvalidInstruction := hhmatch
          exact ⟨by rw [hhalt]; simp, by
            rw [State.toResult_exception s' _ hhalt]; rfl⟩
      rw [← hdone.2]
      exact Eval.iff_steps_halted.mpr ⟨s', hsteps, hdone.1, hcs', rfl⟩

end YulEvmCompiler
