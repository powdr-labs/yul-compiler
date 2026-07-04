import YulEvmCompiler.LowerDefs
/-!
# YulEvmCompiler.LowerCorrect

**Phase B**, the simulation theorems: each Asm step maps to 1–3 EVM steps
on the lowered bytecode, preserving the configuration correspondence
(`ConfMatch`, see `YulEvmCompiler.LowerDefs`), with existential gas bounds
that add along executions.
-/

namespace YulEvmCompiler

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM (U256 EvmState Op stepOp)

/-- **Phase B, one step**: each Asm step is simulated by 1–3 EVM steps on
the lowered bytecode, preserving the configuration correspondence, with an
existential gas bound. -/
theorem astep_sim {prog : List Asm} {is : List Instr}
    (hlow : lowerProg prog = some is)
    {a b : AConf} (hstep : AStep prog a b) (hsuf : a.code <:+ prog) :
    ∃ bnd : Nat, ∀ s : State, ConfMatch prog is a s → bnd ≤ s.gasAvailable →
      ∃ s', Steps s s' ∧ ConfMatch prog is b s'
        ∧ s.gasAvailable - bnd ≤ s'.gasAvailable := by
  cases hstep with
  | @push v c σ yst =>
    obtain ⟨pre, isPre, isI, isC, hsplit, hI, hC, hbytes, hlenPre, hsize⟩ :=
      locate hlow hsuf
    obtain rfl : [Instr.push (conv v)] = isI := by
      simpa [lowerInstr] using hI
    refine ⟨40000, ?_⟩
    intro s hm hgas
    have hpos : codeSize prog - codeSize (Asm.push v :: c) = codeSize pre := by
      rw [codeSize_cons]
      omega
    obtain ⟨s', hstep, hf', hsm', hpc', hstk', hg'⟩ :=
      pushStepU (u := conv v)
        (pre := assembleBytes isPre) (post := assembleBytes isC)
        (assemble_at₁ hbytes)
        hm.frame hm.smatch
        (by rw [hm.pc, hpos, hlenPre])
        hm.stack hgas
    refine ⟨s', .trans hstep (.refl _), ⟨hf', hsm', ?_, ?_⟩, hg'⟩
    · show s'.pc = UInt256.ofNat (codeSize prog - codeSize c)
      rw [hpc', hlenPre]
      exact congrArg UInt256.ofNat (by
        simp only [Asm.size] at hsize
        omega)
    · rw [hstk']
      rfl
  | @op yop args rets c σ yst yst' hstepOp =>
    obtain ⟨pre, isPre, isI, isC, hsplit, hI, hC, hbytes, hlenPre, hsize⟩ :=
      locate hlow hsuf
    simp only [lowerInstr] at hI
    obtain ⟨o, hop, rfl⟩ := Option.map_eq_some_iff.mp hI
    refine ⟨opBound yop args, ?_⟩
    intro s hm hgas
    have hpos : codeSize prog - codeSize (Asm.op yop :: c) = codeSize pre := by
      rw [codeSize_cons]
      omega
    have hok := opStep hop hstepOp
      (σ := mapStk prog σ)
      (assemble_at₁ hbytes)
      hm.frame hm.smatch
      (by rw [hm.pc, hpos, hlenPre])
      (by rw [hm.stack, mapStk_words]) hgas
    obtain ⟨s', hstep, hf', hsm', hpc', hstk', hg'⟩ := hok
    refine ⟨s', .trans hstep (.refl _), ⟨hf', hsm', ?_, ?_⟩, hg'⟩
    · show s'.pc = UInt256.ofNat (codeSize prog - codeSize c)
      rw [hpc', hlenPre]
      exact congrArg UInt256.ofNat (by
        simp only [Asm.size] at hsize
        omega)
    · rw [hstk', mapStk_words]
  | @dup n v τ ρ c yst hτ =>
    obtain ⟨pre, isPre, isI, isC, hsplit, hI, hC, hbytes, hlenPre, hsize⟩ :=
      locate hlow hsuf
    obtain rfl : [Instr.op (.Dup ⟨n⟩)] = isI := by
      simpa [lowerInstr] using hI
    refine ⟨40000, ?_⟩
    intro s hm hgas
    have hpos : codeSize prog - codeSize (Asm.dup n :: c) = codeSize pre := by
      rw [codeSize_cons]
      omega
    have hget : s.stack[n.val]? = some (mapAVal prog v) := by
      rw [hm.stack]
      show (mapStk prog (τ ++ v :: ρ))[n.val]? = _
      rw [mapStk_append, List.getElem?_append_right (by simp [mapStk, hτ]),
        show n.val - (mapStk prog τ).length = 0 from by simp [mapStk, hτ]]
      rfl
    obtain ⟨s', hstep, hf', hsm', hpc', hstk', hg'⟩ :=
      dupStep (n := n)
        (assemble_at₁ hbytes)
        hm.frame hm.smatch
        (by rw [hm.pc, hpos, hlenPre])
        hget hgas
    refine ⟨s', .trans hstep (.refl _), ⟨hf', hsm', ?_, ?_⟩, hg'⟩
    · show s'.pc = UInt256.ofNat (codeSize prog - codeSize c)
      rw [hpc', hlenPre]
      exact congrArg UInt256.ofNat (by
        simp only [Asm.size] at hsize
        omega)
    · rw [hstk', hm.stack]
      rfl
  | @swap n x y τ ρ c yst hτ =>
    obtain ⟨pre, isPre, isI, isC, hsplit, hI, hC, hbytes, hlenPre, hsize⟩ :=
      locate hlow hsuf
    obtain rfl : [Instr.op (.Swap ⟨n⟩)] = isI := by
      simpa [lowerInstr] using hI
    refine ⟨40000, ?_⟩
    intro s hm hgas
    have hpos : codeSize prog - codeSize (Asm.swap n :: c) = codeSize pre := by
      rw [codeSize_cons]
      omega
    have hswap : s.stack.exchange 0 (n.val + 1)
        = some (mapStk prog (y :: (τ ++ x :: ρ))) := by
      rw [hm.stack]
      show List.exchange (mapStk prog (x :: (τ ++ y :: ρ))) 0 (n.val + 1) = _
      rw [mapStk_cons, mapStk_append, mapStk_cons]
      rw [show n.val = (mapStk prog τ).length from by simp [mapStk, hτ]]
      rw [exchange_swap]
      rw [mapStk_cons, mapStk_append, mapStk_cons]
    obtain ⟨s', hstep, hf', hsm', hpc', hstk', hg'⟩ :=
      swapStep (n := n)
        (assemble_at₁ hbytes)
        hm.frame hm.smatch
        (by rw [hm.pc, hpos, hlenPre])
        hswap hgas
    refine ⟨s', .trans hstep (.refl _), ⟨hf', hsm', ?_, hstk'⟩, hg'⟩
    · show s'.pc = UInt256.ofNat (codeSize prog - codeSize c)
      rw [hpc', hlenPre]
      exact congrArg UInt256.ofNat (by
        simp only [Asm.size] at hsize
        omega)
  | @pop v σ c yst =>
    obtain ⟨pre, isPre, isI, isC, hsplit, hI, hC, hbytes, hlenPre, hsize⟩ :=
      locate hlow hsuf
    obtain rfl : [Instr.op .POP] = isI := by
      simpa [lowerInstr] using hI
    refine ⟨40000, ?_⟩
    intro s hm hgas
    have hpos : codeSize prog - codeSize (Asm.pop :: c) = codeSize pre := by
      rw [codeSize_cons]
      omega
    obtain ⟨s', hstep, hf', hsm', hpc', hstk', hg'⟩ :=
      popStep
        (assemble_at₁ hbytes)
        hm.frame hm.smatch
        (by rw [hm.pc, hpos, hlenPre])
        (by rw [hm.stack]; rfl) hgas
    refine ⟨s', .trans hstep (.refl _), ⟨hf', hsm', ?_, hstk'⟩, hg'⟩
    · show s'.pc = UInt256.ofNat (codeSize prog - codeSize c)
      rw [hpc', hlenPre]
      exact congrArg UInt256.ofNat (by
        simp only [Asm.size] at hsize
        omega)
  | @label l c σ yst =>
    obtain ⟨pre, isPre, isI, isC, hsplit, hI, hC, hbytes, hlenPre, hsize⟩ :=
      locate hlow hsuf
    obtain rfl : [Instr.op .JUMPDEST] = isI := by
      simpa [lowerInstr] using hI
    refine ⟨40000, ?_⟩
    intro s hm hgas
    have hpos : codeSize prog - codeSize (Asm.label l :: c) = codeSize pre := by
      rw [codeSize_cons]
      omega
    obtain ⟨s', hstep, hf', hsm', hpc', hstk', hg'⟩ :=
      jumpdestStep
        (assemble_at₁ hbytes)
        hm.frame hm.smatch
        (by rw [hm.pc, hpos, hlenPre]) hgas
    refine ⟨s', .trans hstep (.refl _), ⟨hf', hsm', ?_, by rw [hstk', hm.stack]⟩, hg'⟩
    · show s'.pc = UInt256.ofNat (codeSize prog - codeSize c)
      rw [hpc', hlenPre]
      exact congrArg UInt256.ofNat (by
        simp only [Asm.size] at hsize
        omega)
  | @jump l c c' σ yst hfind =>
    obtain ⟨pre, isPre, isI, isC, hsplit, hI, hC, hbytes, hlenPre, hsize⟩ :=
      locate hlow hsuf
    obtain ⟨aL, isPreL, isC', hres, hposL, hbytesL, hlenPreL, hvalid⟩ :=
      locate_label hlow hfind
    simp only [lowerInstr, hres] at hI
    obtain rfl : [Instr.push (UInt256.ofNat aL), Instr.op .JUMP] = isI := by
      simpa using hI
    refine ⟨40000 + 40000 + 40000, ?_⟩
    intro s hm hgas
    have hpos : codeSize prog - codeSize (Asm.jump l :: c) = codeSize pre := by
      rw [codeSize_cons]
      omega
    have haLlt : aL < 2 ^ 256 := by
      have := codeSize_lt hlow hm.frame
      omega
    obtain ⟨s1, st1, hf1, hsm1, hpc1, hstk1, hg1⟩ :=
      pushStepU (u := UInt256.ofNat aL)
        (pre := assembleBytes isPre)
        (post := (Instr.op .JUMP).bytes ++ assembleBytes isC)
        (assemble_at₂ hbytes)
        hm.frame hm.smatch
        (by rw [hm.pc, hpos, hlenPre])
        hm.stack (by omega)
    obtain ⟨s2, st2, hf2, hsm2, hpc2, hstk2, hg2⟩ :=
      jumpStep (dest := UInt256.ofNat aL)
        (pre := assembleBytes isPre ++ (Instr.push (UInt256.ofNat aL)).bytes)
        (post := assembleBytes isC)
        (assemble_at₂' hbytes)
        hf1 hsm1
        (by rw [hpc1]
            exact congrArg UInt256.ofNat
              (by rw [List.length_append, Instr.length_bytes_push]))
        hstk1
        (by rw [toNat_ofNat_of_lt haLlt]; exact hvalid)
        (by omega)
    obtain ⟨s3, st3, hf3, hsm3, hpc3, hstk3, hg3⟩ :=
      jumpdestStep
        (pre := assembleBytes isPreL) (post := assembleBytes isC')
        (by rw [assemble_eq_mkCode, hbytesL])
        hf2 hsm2
        (by rw [hpc2, hlenPreL]) (by omega)
    refine ⟨s3, .trans st1 (.trans st2 (.trans st3 (.refl _))),
      ⟨hf3, hsm3, ?_, ?_⟩, gasChain₃' hg1 hg2 hg3⟩
    · show s3.pc = UInt256.ofNat (codeSize prog - codeSize c')
      rw [hpc3, hlenPreL]
      exact congrArg UInt256.ofNat (by omega)
    · rw [hstk3, hstk2]
  | @jumpiTaken l v c c' σ yst hv hfind =>
    obtain ⟨pre, isPre, isI, isC, hsplit, hI, hC, hbytes, hlenPre, hsize⟩ :=
      locate hlow hsuf
    obtain ⟨aL, isPreL, isC', hres, hposL, hbytesL, hlenPreL, hvalid⟩ :=
      locate_label hlow hfind
    simp only [lowerInstr, hres] at hI
    obtain rfl : [Instr.push (UInt256.ofNat aL), Instr.op .JUMPI] = isI := by
      simpa using hI
    refine ⟨40000 + 40000 + 40000, ?_⟩
    intro s hm hgas
    have hpos : codeSize prog - codeSize (Asm.jumpi l :: c) = codeSize pre := by
      rw [codeSize_cons]
      omega
    have haLlt : aL < 2 ^ 256 := by
      have := codeSize_lt hlow hm.frame
      omega
    obtain ⟨s1, st1, hf1, hsm1, hpc1, hstk1, hg1⟩ :=
      pushStepU (u := UInt256.ofNat aL)
        (pre := assembleBytes isPre)
        (post := (Instr.op .JUMPI).bytes ++ assembleBytes isC)
        (assemble_at₂ hbytes)
        hm.frame hm.smatch
        (by rw [hm.pc, hpos, hlenPre])
        hm.stack (by omega)
    have hcond : (conv v).toNat ≠ 0 := by
      rw [conv_toNat]
      intro h0
      exact hv (by
        apply BitVec.eq_of_toNat_eq
        simpa using h0)
    obtain ⟨s2, st2, hf2, hsm2, hpc2, hstk2, hg2⟩ :=
      jumpiTakenStep (dest := UInt256.ofNat aL) (cond := conv v)
        (pre := assembleBytes isPre ++ (Instr.push (UInt256.ofNat aL)).bytes)
        (post := assembleBytes isC)
        (assemble_at₂' hbytes)
        hf1 hsm1
        (by rw [hpc1]
            exact congrArg UInt256.ofNat
              (by rw [List.length_append, Instr.length_bytes_push]))
        (by rw [hstk1]; rfl)
        hcond
        (by rw [toNat_ofNat_of_lt haLlt]; exact hvalid)
        (by omega)
    obtain ⟨s3, st3, hf3, hsm3, hpc3, hstk3, hg3⟩ :=
      jumpdestStep
        (pre := assembleBytes isPreL) (post := assembleBytes isC')
        (by rw [assemble_eq_mkCode, hbytesL])
        hf2 hsm2
        (by rw [hpc2, hlenPreL]) (by omega)
    refine ⟨s3, .trans st1 (.trans st2 (.trans st3 (.refl _))),
      ⟨hf3, hsm3, ?_, ?_⟩, gasChain₃' hg1 hg2 hg3⟩
    · show s3.pc = UInt256.ofNat (codeSize prog - codeSize c')
      rw [hpc3, hlenPreL]
      exact congrArg UInt256.ofNat (by omega)
    · rw [hstk3, hstk2]
      rfl
  | @jumpiFall l v c σ yst hv =>
    obtain ⟨pre, isPre, isI, isC, hsplit, hI, hC, hbytes, hlenPre, hsize⟩ :=
      locate hlow hsuf
    simp only [lowerInstr] at hI
    obtain ⟨aL, hres, rfl⟩ := Option.map_eq_some_iff.mp hI
    refine ⟨40000 + 40000, ?_⟩
    intro s hm hgas
    have hpos : codeSize prog - codeSize (Asm.jumpi l :: c) = codeSize pre := by
      rw [codeSize_cons]
      omega
    obtain ⟨s1, st1, hf1, hsm1, hpc1, hstk1, hg1⟩ :=
      pushStepU (u := UInt256.ofNat aL)
        (pre := assembleBytes isPre)
        (post := (Instr.op .JUMPI).bytes ++ assembleBytes isC)
        (assemble_at₂ hbytes)
        hm.frame hm.smatch
        (by rw [hm.pc, hpos, hlenPre])
        hm.stack (by omega)
    have hcond : (conv v).toNat = 0 := by
      rw [conv_toNat, hv]
      rfl
    obtain ⟨s2, st2, hf2, hsm2, hpc2, hstk2, hg2⟩ :=
      jumpiNotTakenStep (dest := UInt256.ofNat aL) (cond := conv v)
        (pre := assembleBytes isPre ++ (Instr.push (UInt256.ofNat aL)).bytes)
        (post := assembleBytes isC)
        (assemble_at₂' hbytes)
        hf1 hsm1
        (by rw [hpc1]
            exact congrArg UInt256.ofNat
              (by rw [List.length_append, Instr.length_bytes_push]))
        (by rw [hstk1]; rfl)
        hcond
        (by omega)
    refine ⟨s2, .trans st1 (.trans st2 (.refl _)), ⟨hf2, hsm2, ?_, hstk2⟩,
      gasChain₂' hg1 hg2⟩
    · show s2.pc = UInt256.ofNat (codeSize prog - codeSize c)
      rw [hpc2, List.length_append, Instr.length_bytes_push, hlenPre]
      exact congrArg UInt256.ofNat (by
        simp only [Asm.size] at hsize
        omega)
  | @pushLabel l c σ yst hdef =>
    obtain ⟨pre, isPre, isI, isC, hsplit, hI, hC, hbytes, hlenPre, hsize⟩ :=
      locate hlow hsuf
    simp only [lowerInstr] at hI
    obtain ⟨aL, hres, rfl⟩ := Option.map_eq_some_iff.mp hI
    refine ⟨40000, ?_⟩
    intro s hm hgas
    have hpos : codeSize prog - codeSize (Asm.pushLabel l :: c) = codeSize pre := by
      rw [codeSize_cons]
      omega
    obtain ⟨s', hstep, hf', hsm', hpc', hstk', hg'⟩ :=
      pushStepU (u := UInt256.ofNat aL)
        (pre := assembleBytes isPre)
        (post := assembleBytes isC)
        (assemble_at₁ hbytes)
        hm.frame hm.smatch
        (by rw [hm.pc, hpos, hlenPre])
        hm.stack hgas
    refine ⟨s', .trans hstep (.refl _), ⟨hf', hsm', ?_, ?_⟩, hg'⟩
    · show s'.pc = UInt256.ofNat (codeSize prog - codeSize c)
      rw [hpc', hlenPre]
      exact congrArg UInt256.ofNat (by
        simp only [Asm.size] at hsize
        omega)
    · rw [hstk']
      show UInt256.ofNat aL :: mapStk prog σ
        = UInt256.ofNat ((resolve l prog).getD 0) :: mapStk prog σ
      rw [hres]
      rfl
  | @dynJump l c c' σ yst hfind =>
    obtain ⟨pre, isPre, isI, isC, hsplit, hI, hC, hbytes, hlenPre, hsize⟩ :=
      locate hlow hsuf
    obtain ⟨aL, isPreL, isC', hres, hposL, hbytesL, hlenPreL, hvalid⟩ :=
      locate_label hlow hfind
    obtain rfl : [Instr.op .JUMP] = isI := by
      simpa [lowerInstr] using hI
    refine ⟨40000 + 40000, ?_⟩
    intro s hm hgas
    have hpos : codeSize prog - codeSize (Asm.dynJump :: c) = codeSize pre := by
      rw [codeSize_cons]
      omega
    have haLlt : aL < 2 ^ 256 := by
      have := codeSize_lt hlow hm.frame
      omega
    have hstktop : s.stack = UInt256.ofNat aL :: mapStk prog σ := by
      rw [hm.stack, mapStk_cons]
      show UInt256.ofNat ((resolve l prog).getD 0) :: _ = _
      rw [hres]
      rfl
    obtain ⟨s1, st1, hf1, hsm1, hpc1, hstk1, hg1⟩ :=
      jumpStep (dest := UInt256.ofNat aL)
        (pre := assembleBytes isPre)
        (post := assembleBytes isC)
        (assemble_at₁ hbytes)
        hm.frame hm.smatch
        (by rw [hm.pc, hpos, hlenPre])
        hstktop
        (by rw [toNat_ofNat_of_lt haLlt]; exact hvalid)
        (by omega)
    obtain ⟨s2, st2, hf2, hsm2, hpc2, hstk2, hg2⟩ :=
      jumpdestStep
        (pre := assembleBytes isPreL) (post := assembleBytes isC')
        (by rw [assemble_eq_mkCode, hbytesL])
        hf1 hsm1
        (by rw [hpc1, hlenPreL]) (by omega)
    refine ⟨s2, .trans st1 (.trans st2 (.refl _)), ⟨hf2, hsm2, ?_, ?_⟩,
      gasChain₂' hg1 hg2⟩
    · show s2.pc = UInt256.ofNat (codeSize prog - codeSize c')
      rw [hpc2, hlenPreL]
      exact congrArg UInt256.ofNat (by omega)
    · rw [hstk2, hstk1]

/-- **Phase B, halting step**: a halting built-in maps to one halting EVM
step. -/
theorem ahalt_sim {prog : List Asm} {is : List Instr}
    (hlow : lowerProg prog = some is)
    {a : AConf} {yst' : EvmState} (hstep : AHalt prog a yst')
    (hsuf : a.code <:+ prog) :
    ∃ bnd : Nat, ∀ s : State, ConfMatch prog is a s → bnd ≤ s.gasAvailable →
      ∃ s', Steps s s' ∧ StateMatch yst' s' ∧ s'.callStack = []
        ∧ HaltedMatch yst' s' := by
  cases hstep with
  | @op yop args c σ yst yst'' hstepOp =>
    obtain ⟨pre, isPre, isI, isC, hsplit, hI, hC, hbytes, hlenPre, hsize⟩ :=
      locate hlow hsuf
    simp only [lowerInstr] at hI
    obtain ⟨o, hop, rfl⟩ := Option.map_eq_some_iff.mp hI
    refine ⟨opBound yop args, ?_⟩
    intro s hm hgas
    have hpos : codeSize prog - codeSize (Asm.op yop :: c) = codeSize pre := by
      rw [codeSize_cons]
      omega
    have hhalt := opStep hop hstepOp
      (σ := mapStk prog σ)
      (assemble_at₁ hbytes)
      hm.frame hm.smatch
      (by rw [hm.pc, hpos, hlenPre])
      (by rw [hm.stack, mapStk_words]) hgas
    obtain ⟨s', hstep, hsm', hcs', hhm'⟩ := hhalt
    exact ⟨s', .trans hstep (.refl _), hsm', hcs', hhm'⟩

/-- **Phase B, many steps**: bounds add along an Asm execution. -/
theorem asteps_sim {prog : List Asm} {is : List Instr}
    (hlow : lowerProg prog = some is)
    {a b : AConf} (hsteps : ASteps prog a b) (hsuf : a.code <:+ prog) :
    ∃ bnd : Nat, ∀ s : State, ConfMatch prog is a s → bnd ≤ s.gasAvailable →
      ∃ s', Steps s s' ∧ ConfMatch prog is b s'
        ∧ s.gasAvailable - bnd ≤ s'.gasAvailable := by
  induction hsteps with
  | refl a =>
    exact ⟨0, fun s hm _ => ⟨s, .refl _, hm, by omega⟩⟩
  | @head a₁ a₂ a₃ hstep hrest ih =>
    obtain ⟨b1, H1⟩ := astep_sim hlow hstep hsuf
    obtain ⟨b2, H2⟩ := ih (hstep.suffix hsuf)
    refine ⟨b1 + b2, ?_⟩
    intro s hm hgas
    obtain ⟨s1, st1, hm1, hg1⟩ := H1 s hm (by omega)
    obtain ⟨s2, st2, hm2, hg2⟩ := H2 s1 hm1 (by omega)
    exact ⟨s2, st1.append st2, hm2, by omega⟩

/-- **Phase B, halting run**: an Asm execution ending in a halt maps to an
EVM execution ending in the matching halted state. -/
theorem arun_halt_sim {prog : List Asm} {is : List Instr}
    (hlow : lowerProg prog = some is)
    {a b : AConf} {yst' : EvmState}
    (hsteps : ASteps prog a b) (hhalt : AHalt prog b yst')
    (hsuf : a.code <:+ prog) :
    ∃ bnd : Nat, ∀ s : State, ConfMatch prog is a s → bnd ≤ s.gasAvailable →
      ∃ s', Steps s s' ∧ StateMatch yst' s' ∧ s'.callStack = []
        ∧ HaltedMatch yst' s' := by
  obtain ⟨b1, H1⟩ := asteps_sim hlow hsteps hsuf
  obtain ⟨b2, H2⟩ := ahalt_sim hlow hhalt (hsteps.suffix hsuf)
  refine ⟨b1 + b2, ?_⟩
  intro s hm hgas
  obtain ⟨s1, st1, hm1, hg1⟩ := H1 s hm (by omega)
  obtain ⟨s2, st2, hsm2, hcs2, hhm2⟩ := H2 s1 hm1 (by omega)
  exact ⟨s2, st1.append st2, hsm2, hcs2, hhm2⟩

end YulEvmCompiler
