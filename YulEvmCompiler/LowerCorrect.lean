import YulEvmCompiler.LowerDefs

set_option warningAsError true
/-!
# YulEvmCompiler.LowerCorrect

**Phase B**, the simulation theorems: each local Asm step maps to 1–3 EVM
steps on the lowered bytecode. An external call/create step maps to an
arbitrary finite EVM trace supplied by `ExternalsRealized`; placing no
invariant on its intermediate states admits arbitrary init/callee code,
nested calls and creations, and reentrancy. Both cases
preserve the configuration correspondence (`ConfMatch`, see
`YulEvmCompiler.LowerDefs`) and have existential gas bounds that add along
executions.
-/

namespace YulEvmCompiler

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM (U256 EvmState Op stepOp builtinWithExternal)

/-- **Phase B, one step**: each local Asm step is simulated by 1–3 EVM steps;
an external call or creation is simulated by the unrestricted finite trace
provided by `ExternalsRealized`. The endpoint preserves the configuration correspondence and
each case has an existential gas bound. -/
theorem astep_sim [model : ExternalModel] (hexternal : ExternalsRealized model)
    {prog : List Asm} {is : List Instr} {payload : List UInt8}
    (hlow : lowerProg prog = some is)
    {a b : AConf} (hstep : AStep prog a b) (hsuf : a.code <:+ prog) :
    ∃ bnd : Nat, ∀ s : State, ConfMatch (payload := payload) prog is a s →
      bnd ≤ s.gasAvailable →
      ∃ s', Steps s s' ∧ ConfMatch (payload := payload) prog is b s'
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
        (pre := assembleBytes isPre) (post := assembleBytes isC ++ payload)
        (assembleWithPayload_at₁ hbytes payload)
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
    have hpos : codeSize prog - codeSize (Asm.op yop :: c) = codeSize pre := by
      rw [codeSize_cons]
      omega
    by_cases hcall : IsCallOp yop
    · have hsource := (builtinWithExternal_iff_builtin_of_call hcall).mp hstepOp
      obtain ⟨bnd, H⟩ := hexternal.calls.call hcall hop hsource
      refine ⟨bnd, ?_⟩
      intro s hm hgas
      have hdec := decoded_op hm.frame (assembleWithPayload_at₁ hbytes payload)
        (by rw [hm.pc, hpos, hlenPre])
        (opTable_roundtrip hop).1 (opTable_roundtrip hop).2
        (opTable_available hop)
      obtain ⟨s', hsteps, hf', hsm', hpc', hstk', hg'⟩ :=
        H hm.frame hm.smatch hdec (by rw [hm.stack, mapStk_words]) hgas
      refine ⟨s', hsteps, ⟨hf', hsm', ?_, ?_⟩, hg'⟩
      · show s'.pc = UInt256.ofNat (codeSize prog - codeSize c)
        rw [hpc', hm.pc, hpos]
        have := hf'.codeSmall
        rw [assembleWithPayload, size_mkCode, List.length_append,
          lowerFrag_length hlow] at this
        simp only [Asm.size] at hsize
        rw [succ_ofNat (by omega)]
        congr 1
        omega
      · rw [hstk', mapStk_words]
    · by_cases hcreate : IsCreateOp yop
      · have hsource :=
          (builtinWithExternal_iff_createOnly_of_create hcreate).mp hstepOp
        obtain ⟨bnd, H⟩ := hexternal.creates.create hcreate hop hsource
        refine ⟨bnd, ?_⟩
        intro s hm hgas
        have hdec := decoded_op hm.frame (assembleWithPayload_at₁ hbytes payload)
          (by rw [hm.pc, hpos, hlenPre])
          (opTable_roundtrip hop).1 (opTable_roundtrip hop).2
          (opTable_available hop)
        obtain ⟨s', hsteps, hf', hsm', hpc', hstk', hg'⟩ :=
          H hm.frame hm.smatch hdec (by rw [hm.stack, mapStk_words]) hgas
        refine ⟨s', hsteps, ⟨hf', hsm', ?_, ?_⟩, hg'⟩
        · show s'.pc = UInt256.ofNat (codeSize prog - codeSize c)
          rw [hpc', hm.pc, hpos]
          have := hf'.codeSmall
          rw [assembleWithPayload, size_mkCode, List.length_append,
            lowerFrag_length hlow] at this
          simp only [Asm.size] at hsize
          rw [succ_ofNat (by omega)]
          congr 1
          omega
        · rw [hstk', mapStk_words]
      · have hnotExternal : ¬ IsExternalOp yop := by
          intro h
          rcases h with hcall' | hcreate' | hgas
          · exact hcall hcall'
          · exact hcreate hcreate'
          · subst yop
            simp [opTable] at hop
        have hlocal :=
          (builtinWithExternal_iff_stepOp_of_not_external hnotExternal).mp hstepOp
        refine ⟨opBound yop args, ?_⟩
        intro s hm hgas
        have hok := opStep hop hlocal
          (σ := mapStk prog σ)
          (assembleWithPayload_at₁ hbytes payload)
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
        (assembleWithPayload_at₁ hbytes payload)
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
        (assembleWithPayload_at₁ hbytes payload)
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
        (assembleWithPayload_at₁ hbytes payload)
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
        (assembleWithPayload_at₁ hbytes payload)
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
      locate_label_withPayload hlow hfind payload
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
        (post := (Instr.op .JUMP).bytes ++ assembleBytes isC ++ payload)
        (assembleWithPayload_at₂ hbytes payload)
        hm.frame hm.smatch
        (by rw [hm.pc, hpos, hlenPre])
        hm.stack (by omega)
    obtain ⟨s2, st2, hf2, hsm2, hpc2, hstk2, hg2⟩ :=
      jumpStep (dest := UInt256.ofNat aL)
        (pre := assembleBytes isPre ++ (Instr.push (UInt256.ofNat aL)).bytes)
        (post := assembleBytes isC ++ payload)
        (assembleWithPayload_at₂' hbytes payload)
        hf1 hsm1
        (by rw [hpc1]
            exact congrArg UInt256.ofNat
              (by rw [List.length_append, Instr.length_bytes_push]))
        hstk1
        (by rw [toNat_ofNat_of_lt haLlt]; exact hvalid)
        (by omega)
    obtain ⟨s3, st3, hf3, hsm3, hpc3, hstk3, hg3⟩ :=
      jumpdestStep
        (pre := assembleBytes isPreL) (post := assembleBytes isC' ++ payload)
        (by
          rw [assembleWithPayload, hbytesL]
          simp only [List.append_assoc])
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
      locate_label_withPayload hlow hfind payload
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
        (post := (Instr.op .JUMPI).bytes ++ assembleBytes isC ++ payload)
        (assembleWithPayload_at₂ hbytes payload)
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
        (post := assembleBytes isC ++ payload)
        (assembleWithPayload_at₂' hbytes payload)
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
        (pre := assembleBytes isPreL) (post := assembleBytes isC' ++ payload)
        (by
          rw [assembleWithPayload, hbytesL]
          simp only [List.append_assoc])
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
        (post := (Instr.op .JUMPI).bytes ++ assembleBytes isC ++ payload)
        (assembleWithPayload_at₂ hbytes payload)
        hm.frame hm.smatch
        (by rw [hm.pc, hpos, hlenPre])
        hm.stack (by omega)
    have hcond : (conv v).toNat = 0 := by
      rw [conv_toNat, hv]
      rfl
    obtain ⟨s2, st2, hf2, hsm2, hpc2, hstk2, hg2⟩ :=
      jumpiNotTakenStep (dest := UInt256.ofNat aL) (cond := conv v)
        (pre := assembleBytes isPre ++ (Instr.push (UInt256.ofNat aL)).bytes)
        (post := assembleBytes isC ++ payload)
        (assembleWithPayload_at₂' hbytes payload)
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
        (post := assembleBytes isC ++ payload)
        (assembleWithPayload_at₁ hbytes payload)
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
      locate_label_withPayload hlow hfind payload
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
        (post := assembleBytes isC ++ payload)
        (assembleWithPayload_at₁ hbytes payload)
        hm.frame hm.smatch
        (by rw [hm.pc, hpos, hlenPre])
        hstktop
        (by rw [toNat_ofNat_of_lt haLlt]; exact hvalid)
        (by omega)
    obtain ⟨s2, st2, hf2, hsm2, hpc2, hstk2, hg2⟩ :=
      jumpdestStep
        (pre := assembleBytes isPreL) (post := assembleBytes isC' ++ payload)
        (by
          rw [assembleWithPayload, hbytesL]
          simp only [List.append_assoc])
        hf1 hsm1
        (by rw [hpc1, hlenPreL]) (by omega)
    refine ⟨s2, .trans st1 (.trans st2 (.refl _)), ⟨hf2, hsm2, ?_, ?_⟩,
      gasChain₂' hg1 hg2⟩
    · show s2.pc = UInt256.ofNat (codeSize prog - codeSize c')
      rw [hpc2, hlenPreL]
      exact congrArg UInt256.ofNat (by omega)
    · rw [hstk2, hstk1]

/-- **Phase B, open-world static halt**: a state-modifying external built-in
attempted in a static frame. `call` (value-bearing) / `create` / `create2`
halt with `Exception .StaticModeViolation` via their dedicated target static
gates, matching the source's `.staticViolation`. `callcode` (value-bearing
`callcode` is a self-transfer, a world-state no-op, so it is *not* rejected in
a static frame — matching EIP-214 / the EVM), `delegatecall`, `staticcall`, and
`gas` never produce a relational halt. -/
theorem externalStaticHaltStep [model : ExternalModel]
    {yop : Op} {o : Operation} (hop : opTable yop = some o)
    (hexternal : IsExternalOp yop)
    {args : List U256} {yst yst' : EvmState}
    (hhalt : builtinWithExternal model.calls model.creates yop args yst (.halt yst'))
    {code : ByteArray} {pre post : List UInt8} {σ : List UInt256} {s : State}
    (hcode : code = mkCode (pre ++ (Instr.op o).bytes ++ post))
    (hf : FrameOK code s) (hm : StateMatch yst s)
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hstk : s.stack = args.map conv ++ σ) :
    HaltStep s yst' := by
  have hstatic : yst.env.static = true :=
    builtinWithExternal_halt_external_imp_static hexternal hhalt
  have hperm : s.executionEnv.permitStateMutation = false :=
    hm.perm_of_static_true hstatic
  obtain ⟨hb, hplain⟩ := opTable_roundtrip hop
  have hdec : s.decodedOp = some o :=
    decoded_op hf hcode hpc hb hplain (opTable_available hop)
  cases yop
  case call =>
    obtain rfl : o = .CALL := by simpa [opTable] using hop.symm
    rcases args with _|⟨g,_|⟨t,_|⟨val,_|⟨ao,_|⟨al,_|⟨ro,_|⟨rl,_|⟨e,rest⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      simp only [builtinWithExternal, hstatic, true_and] at hhalt
    split at hhalt
    · rename_i hval
      obtain rfl : yst' = { yst with halted := some (.staticViolation, []) } := by
        simpa using hhalt
      have hstk7 : s.stack = conv g :: conv t :: conv val :: conv ao :: conv al ::
          conv ro :: conv rl :: σ := by simpa using hstk
      exact staticHaltStepGen hm hf.callStack
        (EVM.Step.running hf.running hf.noPrecompile
          (StepRunning.callStatic s (conv g) (conv t) (conv val) (conv ao) (conv al)
            (conv ro) (conv rl) σ hdec hstk7 hperm
            (by rw [conv_toNat]; intro h; exact hval (BitVec.toNat_injective (by simpa using h)))))
    · exfalso
      obtain ⟨resp, -, heq⟩ := hhalt
      simp at heq
  case callcode =>
    exfalso
    rcases args with _|⟨g,_|⟨t,_|⟨val,_|⟨ao,_|⟨al,_|⟨ro,_|⟨rl,_|⟨e,rest⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      simp [builtinWithExternal, YulSemantics.EVM.externalCall] at hhalt
  case create =>
    obtain rfl : o = .CREATE := by simpa [opTable] using hop.symm
    rcases args with _|⟨val,_|⟨off,_|⟨sz,_|⟨e,rest⟩⟩⟩⟩ <;>
      simp only [builtinWithExternal, hstatic, if_true] at hhalt
    obtain rfl : yst' = { yst with halted := some (.staticViolation, []) } := by
      simpa using hhalt
    have hstk3 : s.stack = conv val :: conv off :: conv sz :: σ := by simpa using hstk
    exact staticHaltStepGen hm hf.callStack
      (EVM.Step.running hf.running hf.noPrecompile
        (StepRunning.createStatic s (conv val) (conv off) (conv sz) σ hdec hstk3 hperm))
  case create2 =>
    obtain rfl : o = .CREATE2 := by simpa [opTable] using hop.symm
    rcases args with _|⟨val,_|⟨off,_|⟨sz,_|⟨salt,_|⟨e,rest⟩⟩⟩⟩⟩ <;>
      simp only [builtinWithExternal, hstatic, if_true] at hhalt
    obtain rfl : yst' = { yst with halted := some (.staticViolation, []) } := by
      simpa using hhalt
    have hstk4 : s.stack = conv val :: conv off :: conv sz :: conv salt :: σ := by
      simpa using hstk
    exact staticHaltStepGen hm hf.callStack
      (EVM.Step.running hf.running hf.noPrecompile
        (StepRunning.create2Static s (conv val) (conv off) (conv sz) (conv salt) σ
          hdec hstk4 hperm))
  case delegatecall =>
    exfalso
    rcases args with _|⟨g,_|⟨t,_|⟨io,_|⟨isz,_|⟨oo,_|⟨ol,_|⟨e,rest⟩⟩⟩⟩⟩⟩⟩ <;>
      simp [builtinWithExternal, YulSemantics.EVM.externalCall] at hhalt
  case staticcall =>
    exfalso
    rcases args with _|⟨g,_|⟨t,_|⟨io,_|⟨isz,_|⟨oo,_|⟨ol,_|⟨e,rest⟩⟩⟩⟩⟩⟩⟩ <;>
      simp [builtinWithExternal, YulSemantics.EVM.externalCall] at hhalt
  case gas => simp [opTable] at hop
  all_goals exact absurd hexternal (by decide)

/-- **Phase B, halting step**: a halting built-in maps to one halting EVM
step. -/
theorem ahalt_sim [model : ExternalModel]
    {prog : List Asm} {is : List Instr} {payload : List UInt8}
    (hlow : lowerProg prog = some is)
    {a : AConf} {yst' : EvmState} (hstep : AHalt prog a yst')
    (hsuf : a.code <:+ prog) :
    ∃ bnd : Nat, ∀ s : State, ConfMatch (payload := payload) prog is a s →
      bnd ≤ s.gasAvailable →
      ∃ s', Steps s s' ∧ StateMatch yst' s' ∧ s'.callStack = []
        ∧ HaltedMatch yst' s' := by
  cases hstep with
  | @op yop args c σ yst yst'' hstepOp =>
    obtain ⟨pre, isPre, isI, isC, hsplit, hI, hC, hbytes, hlenPre, hsize⟩ :=
      locate hlow hsuf
    simp only [lowerInstr] at hI
    obtain ⟨o, hop, rfl⟩ := Option.map_eq_some_iff.mp hI
    by_cases hexternal : IsExternalOp yop
    · refine ⟨0, ?_⟩
      intro s hm hgas
      have hpos : codeSize prog - codeSize (Asm.op yop :: c) = codeSize pre := by
        rw [codeSize_cons]
        omega
      have hhalt := externalStaticHaltStep hop hexternal hstepOp
        (σ := mapStk prog σ)
        (assembleWithPayload_at₁ hbytes payload)
        hm.frame hm.smatch
        (by rw [hm.pc, hpos, hlenPre])
        (by rw [hm.stack, mapStk_words])
      obtain ⟨s', hstep, hsm', hcs', hhm'⟩ := hhalt
      exact ⟨s', .trans hstep (.refl _), hsm', hcs', hhm'⟩
    · have hstepLocal :=
        (builtinWithExternal_halt_iff_stepOp_of_not_external hexternal).mp hstepOp
      refine ⟨opBound yop args, ?_⟩
      intro s hm hgas
      have hpos : codeSize prog - codeSize (Asm.op yop :: c) = codeSize pre := by
        rw [codeSize_cons]
        omega
      have hhalt := opStep hop hstepLocal
        (σ := mapStk prog σ)
        (assembleWithPayload_at₁ hbytes payload)
        hm.frame hm.smatch
        (by rw [hm.pc, hpos, hlenPre])
        (by rw [hm.stack, mapStk_words]) hgas
      obtain ⟨s', hstep, hsm', hcs', hhm'⟩ := hhalt
      exact ⟨s', .trans hstep (.refl _), hsm', hcs', hhm'⟩

/-- **Phase B, many steps**: bounds add along an Asm execution. -/
theorem asteps_sim [model : ExternalModel] (hexternal : ExternalsRealized model)
    {prog : List Asm} {is : List Instr} {payload : List UInt8}
    (hlow : lowerProg prog = some is)
    {a b : AConf} (hsteps : ASteps prog a b) (hsuf : a.code <:+ prog) :
    ∃ bnd : Nat, ∀ s : State, ConfMatch (payload := payload) prog is a s →
      bnd ≤ s.gasAvailable →
      ∃ s', Steps s s' ∧ ConfMatch (payload := payload) prog is b s'
        ∧ s.gasAvailable - bnd ≤ s'.gasAvailable := by
  induction hsteps with
  | refl a =>
    exact ⟨0, fun s hm _ => ⟨s, .refl _, hm, by omega⟩⟩
  | @head a₁ a₂ a₃ hstep hrest ih =>
    obtain ⟨b1, H1⟩ := astep_sim hexternal hlow hstep hsuf
    obtain ⟨b2, H2⟩ := ih (hstep.suffix hsuf)
    refine ⟨b1 + b2, ?_⟩
    intro s hm hgas
    obtain ⟨s1, st1, hm1, hg1⟩ := H1 s hm (by omega)
    obtain ⟨s2, st2, hm2, hg2⟩ := H2 s1 hm1 (by omega)
    exact ⟨s2, st1.append st2, hm2, by omega⟩

/-- **Phase B, halting run**: an Asm execution ending in a halt maps to an
EVM execution ending in the matching halted state. -/
theorem arun_halt_sim [model : ExternalModel] (hexternal : ExternalsRealized model)
    {prog : List Asm} {is : List Instr} {payload : List UInt8}
    (hlow : lowerProg prog = some is)
    {a b : AConf} {yst' : EvmState}
    (hsteps : ASteps prog a b) (hhalt : AHalt prog b yst')
    (hsuf : a.code <:+ prog) :
    ∃ bnd : Nat, ∀ s : State, ConfMatch (payload := payload) prog is a s →
      bnd ≤ s.gasAvailable →
      ∃ s', Steps s s' ∧ StateMatch yst' s' ∧ s'.callStack = []
        ∧ HaltedMatch yst' s' := by
  obtain ⟨b1, H1⟩ := asteps_sim hexternal hlow hsteps hsuf
  obtain ⟨b2, H2⟩ := ahalt_sim hlow hhalt (hsteps.suffix hsuf)
  refine ⟨b1 + b2, ?_⟩
  intro s hm hgas
  obtain ⟨s1, st1, hm1, hg1⟩ := H1 s hm (by omega)
  obtain ⟨s2, st2, hsm2, hcs2, hhm2⟩ := H2 s1 hm1 (by omega)
  exact ⟨s2, st1.append st2, hsm2, hcs2, hhm2⟩

end YulEvmCompiler
