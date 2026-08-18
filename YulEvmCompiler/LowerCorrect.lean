import YulEvmCompiler.LowerDefs
import YulEvmCompiler.GasTx
set_option warningAsError true
/-! # YulEvmCompiler.LowerCorrect

**Phase B**, the simulation theorems: each local Asm step maps to 1–3 EVM
steps on the lowered bytecode. An external call/create step maps to an
arbitrary finite EVM trace supplied by `ExternalsRealized`; placing no
invariant on its intermediate states admits arbitrary init/callee code,
nested calls and creations, and reentrancy. Both cases
preserve the configuration correspondence (`ConfMatch`, see
`YulEvmCompiler.LowerDefs`).

Gas is tracked by an existential threshold (nothing is claimed for
underfunded runs) together with a residual lower bound given by a monotone,
unbounded transformer (`GasTx`): a step funded with `bnd` gas finishes with
at least `tx.f s.gasAvailable` gas. Every step of the current instruction
set instantiates the additive transformer `GasTx.sub` (lose at most a
constant), but composition (`asteps_sim`) is stated and proved for the
general class, so a step whose loss is proportional to the starting gas — an
EIP-150 gas-forwarding call, `GasTx.callLoss` — composes without changing
any statement again (`GasOracle.no_additive_bound_under_eip150` is why the
additive special case cannot express it).
-/

namespace YulEvmCompiler

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM (U256 EvmState Op stepOp builtinWithExternal)

/-- **Phase B, one step**: each local Asm step is simulated by 1–3 EVM steps;
an external call or creation is simulated by the unrestricted finite trace
provided by `ExternalsRealized`. The endpoint preserves the configuration correspondence and
each case has an existential gas bound. -/
theorem op_arity_bound (o : Operation) : Operation.pushArity o ≤ Operation.popArity o + 1 := by
  cases o <;> simp only [Operation.pushArity, Operation.popArity] <;> (first | omega | (split <;> omega))

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem baseCost_le_40000 (o : Operation) : Gas.baseCost .Osaka o ≤ 40000 := by
  cases o <;>
    simp only [Gas.baseCost] <;>
    first
      | decide
      | (split <;> decide)
      | (rename_i x; cases x <;> simp only [Gas.baseCost] <;>
          (first | decide | (split <;> decide) | (rename_i y; have := y.isLt; omega)))
      | (rename_i x; have := x.isLt; omega)

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem astep_sim [model : ExternalModel] (hexternal : ExternalsRealized model)
    {prog : List Asm} {is : List Instr} {payload : List UInt8}
    (hlow : lowerProg imm prog = some is) (hsmall : codeSize prog < 256 ^ labelWidth)
    {a b : AConf} (hstep : AStep prog a b) (hsuf : a.code <:+ prog)
    (hcap : a.stk.length ≤ 1023) :
    ∃ (bnd : Nat) (tx : GasTx), ∀ s : State, ConfMatch (payload := payload) imm prog is a s →
      bnd ≤ s.gasAvailable →
      ∃ s', Steps s s' ∧ ConfMatch (payload := payload) imm prog is b s'
        ∧ tx.f s.gasAvailable ≤ s'.gasAvailable := by
  cases hstep with
  | @push v c σ yst =>
    obtain ⟨pre, isPre, isI, isC, hsplit, hI, hC, hbytes, hlenPre, hsize⟩ :=
      locate hlow hsuf
    obtain rfl : [Instr.pushMin (conv v)] = isI := by
      simpa [lowerInstr] using hI
    refine ⟨40000, .sub (40000), ?_⟩
    intro s hm hgas
    have hpos : codeSize prog - codeSize (Asm.push v :: c) = codeSize pre := by
      rw [codeSize_cons]
      omega
    obtain ⟨s', hstep, hf', hsm', hpc', hstk', hg'⟩ :=
      pushStepU (w := Instr.widthOf (conv v)) (u := conv v)
        (hwf := Instr.pushMin_wf (conv v))
        (pre := assembleBytes isPre) (post := assembleBytes isC ++ payload)
        (assembleWithPayload_at₁ hbytes payload)
        hm.frame hm.smatch
        (by rw [hm.pc, hpos, hlenPre])
        hm.stack (by have hlen : s.stack.length ≤ 1023 := (by rw [hm.stack]; simp only [mapStk, List.length_map]; exact hcap); first | ((try simp only [Operation.pushArity, Operation.popArity]); omega) | (have := op_arity_bound o; omega)) hgas
    refine ⟨s', .trans hstep (.refl _), ⟨hf', hsm', ?_, ?_, hm.imms_step (by first | rfl | exact builtinWithExternal_immutable_eq hstepOp)⟩, hg'⟩
    · show s'.pc = UInt256.ofNat (codeSize prog - codeSize c)
      rw [hpc', hlenPre]
      exact congrArg UInt256.ofNat (by
        simp only [Asm.size, Instr.widthOf_val] at hsize ⊢
        omega)
    · rw [hstk']
      rfl
  | @pushImmutable key c σ yst =>
    -- Identical to `push` except the width is pinned to 32, which is what makes
    -- the immediate's byte position independent of the value stored there.
    obtain ⟨pre, isPre, isI, isC, hsplit, hI, hC, hbytes, hlenPre, hsize⟩ :=
      locate hlow hsuf
    obtain rfl : [Instr.push ⟨32, by norm_num⟩ (conv (imm key))] = isI := by
      simpa [lowerInstr] using hI
    refine ⟨40000, .sub (40000), ?_⟩
    intro s hm hgas
    have hpos : codeSize prog - codeSize (Asm.pushImmutable key :: c) = codeSize pre := by
      rw [codeSize_cons]
      omega
    obtain ⟨s', hstep, hf', hsm', hpc', hstk', hg'⟩ :=
      pushStepU (w := ⟨32, by norm_num⟩) (u := conv (imm key))
        (hwf := by
          show (conv (imm key)).toNat < 256 ^ 32
          rw [conv_toNat, show (256:Nat) ^ 32 = 2 ^ 256 by norm_num]
          exact (imm key).isLt)
        (pre := assembleBytes isPre) (post := assembleBytes isC ++ payload)
        (assembleWithPayload_at₁ hbytes payload)
        hm.frame hm.smatch
        (by rw [hm.pc, hpos, hlenPre])
        hm.stack (by have hlen : s.stack.length ≤ 1023 := (by rw [hm.stack]; simp only [mapStk, List.length_map]; exact hcap); omega) hgas
    refine ⟨s', .trans hstep (.refl _), ⟨hf', hsm', ?_, ?_, hm.imms_step (by first | rfl | exact builtinWithExternal_immutable_eq hstepOp)⟩, hg'⟩
    · show s'.pc = UInt256.ofNat (codeSize prog - codeSize c)
      rw [hpc', hlenPre]
      exact congrArg UInt256.ofNat (by
        simp only [Asm.size] at hsize ⊢
        omega)
    · rw [hstk', ← hm.imms key]
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
      refine ⟨bnd, .sub (bnd), ?_⟩
      intro s hm hgas
      have hdec := decoded_op hm.frame (assembleWithPayload_at₁ hbytes payload)
        (by rw [hm.pc, hpos, hlenPre])
        (opTable_roundtrip hop).1 (opTable_roundtrip hop).2
        (opTable_available hop)
      obtain ⟨s', hsteps, hf', hsm', hpc', hstk', hg'⟩ :=
        H hm.frame hm.smatch hdec (by rw [hm.stack, mapStk_words]) hgas
          (by have hlen : s.stack.length ≤ 1023 := (by rw [hm.stack]; simp only [mapStk, List.length_map]; exact hcap); first | ((try simp only [Operation.pushArity, Operation.popArity]); omega) | (have := op_arity_bound o; omega))
      refine ⟨s', hsteps, ⟨hf', hsm', ?_, ?_, hm.imms_step (by first | rfl | exact builtinWithExternal_immutable_eq hstepOp)⟩, hg'⟩
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
        refine ⟨bnd, .sub (bnd), ?_⟩
        intro s hm hgas
        have hdec := decoded_op hm.frame (assembleWithPayload_at₁ hbytes payload)
          (by rw [hm.pc, hpos, hlenPre])
          (opTable_roundtrip hop).1 (opTable_roundtrip hop).2
          (opTable_available hop)
        obtain ⟨s', hsteps, hf', hsm', hpc', hstk', hg'⟩ :=
          H hm.frame hm.smatch hdec (by rw [hm.stack, mapStk_words]) hgas
            (by have hlen : s.stack.length ≤ 1023 := (by rw [hm.stack]; simp only [mapStk, List.length_map]; exact hcap); first | ((try simp only [Operation.pushArity, Operation.popArity]); omega) | (have := op_arity_bound o; omega))
        refine ⟨s', hsteps, ⟨hf', hsm', ?_, ?_, hm.imms_step (by first | rfl | exact builtinWithExternal_immutable_eq hstepOp)⟩, hg'⟩
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
        refine ⟨opBound yop args, .sub (opBound yop args), ?_⟩
        intro s hm hgas
        have hok := opStep hop hlocal
          (σ := mapStk prog σ)
          (assembleWithPayload_at₁ hbytes payload)
          hm.frame hm.smatch
          (by rw [hm.pc, hpos, hlenPre])
          (by rw [hm.stack, mapStk_words])
          (by have hlen : s.stack.length ≤ 1023 := (by rw [hm.stack]; simp only [mapStk, List.length_map]; exact hcap); first | ((try simp only [Operation.pushArity, Operation.popArity]); omega) | (have := op_arity_bound o; omega)) hgas
        obtain ⟨s', hstep, hf', hsm', hpc', hstk', hg'⟩ := hok
        refine ⟨s', .trans hstep (.refl _), ⟨hf', hsm', ?_, ?_, hm.imms_step (by first | rfl | exact builtinWithExternal_immutable_eq hstepOp)⟩, hg'⟩
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
    refine ⟨40000, .sub (40000), ?_⟩
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
        hget (by have hlen : s.stack.length ≤ 1023 := (by rw [hm.stack]; simp only [mapStk, List.length_map]; exact hcap); first | ((try simp only [Operation.pushArity, Operation.popArity]); omega) | (have := op_arity_bound o; omega)) hgas
    refine ⟨s', .trans hstep (.refl _), ⟨hf', hsm', ?_, ?_, hm.imms_step (by first | rfl | exact builtinWithExternal_immutable_eq hstepOp)⟩, hg'⟩
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
    refine ⟨40000, .sub (40000), ?_⟩
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
        hswap (by have hlen : s.stack.length ≤ 1023 := (by rw [hm.stack]; simp only [mapStk, List.length_map]; exact hcap); first | ((try simp only [Operation.pushArity, Operation.popArity]); omega) | (have := op_arity_bound o; omega)) hgas
    refine ⟨s', .trans hstep (.refl _), ⟨hf', hsm', ?_, hstk', hm.imms_step (by first | rfl | exact builtinWithExternal_immutable_eq hstepOp)⟩, hg'⟩
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
    refine ⟨40000, .sub (40000), ?_⟩
    intro s hm hgas
    have hpos : codeSize prog - codeSize (Asm.pop :: c) = codeSize pre := by
      rw [codeSize_cons]
      omega
    obtain ⟨s', hstep, hf', hsm', hpc', hstk', hg'⟩ :=
      popStep
        (assembleWithPayload_at₁ hbytes payload)
        hm.frame hm.smatch
        (by rw [hm.pc, hpos, hlenPre])
        (by rw [hm.stack]; rfl) (by have hlen : s.stack.length ≤ 1023 := (by rw [hm.stack]; simp only [mapStk, List.length_map]; exact hcap); first | ((try simp only [Operation.pushArity, Operation.popArity]); omega) | (have := op_arity_bound o; omega)) hgas
    refine ⟨s', .trans hstep (.refl _), ⟨hf', hsm', ?_, hstk', hm.imms_step (by first | rfl | exact builtinWithExternal_immutable_eq hstepOp)⟩, hg'⟩
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
    refine ⟨40000, .sub (40000), ?_⟩
    intro s hm hgas
    have hpos : codeSize prog - codeSize (Asm.label l :: c) = codeSize pre := by
      rw [codeSize_cons]
      omega
    obtain ⟨s', hstep, hf', hsm', hpc', hstk', hg'⟩ :=
      jumpdestStep
        (assembleWithPayload_at₁ hbytes payload)
        hm.frame hm.smatch
        (by rw [hm.pc, hpos, hlenPre]) (by have hlen : s.stack.length ≤ 1023 := (by rw [hm.stack]; simp only [mapStk, List.length_map]; exact hcap); first | ((try simp only [Operation.pushArity, Operation.popArity]); omega) | (have := op_arity_bound o; omega)) hgas
    refine ⟨s', .trans hstep (.refl _), ⟨hf', hsm', ?_, by rw [hstk', hm.stack], hm.imms_step (by first | rfl | exact builtinWithExternal_immutable_eq hstepOp)⟩, hg'⟩
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
    obtain rfl : [Instr.push labelWidthFin (UInt256.ofNat aL), Instr.op .JUMP] = isI := by
      simpa using hI
    refine ⟨40000 + 40000 + 40000, .sub (40000 + 40000 + 40000), ?_⟩
    intro s hm hgas
    have hpos : codeSize prog - codeSize (Asm.jump l :: c) = codeSize pre := by
      rw [codeSize_cons]
      omega
    have haLsmall : aL < 256 ^ labelWidth := by omega
    have haLlt : aL < 2 ^ 256 := by
      have := codeSize_lt hlow hm.frame
      omega
    have hwfL : (UInt256.ofNat aL).toNat < 256 ^ labelWidthFin.val := by
      rw [labelWidthFin_val, toNat_ofNat_of_lt haLlt]; exact haLsmall
    obtain ⟨s1, st1, hf1, hsm1, hpc1, hstk1, hg1⟩ :=
      pushStepU (u := UInt256.ofNat aL) (hwf := hwfL)
        (pre := assembleBytes isPre)
        (post := (Instr.op .JUMP).bytes ++ assembleBytes isC ++ payload)
        (assembleWithPayload_at₂ hbytes payload)
        hm.frame hm.smatch
        (by rw [hm.pc, hpos, hlenPre])
        hm.stack (by have hlen : s.stack.length ≤ 1023 := (by rw [hm.stack]; simp only [mapStk, List.length_map]; exact hcap); first | ((try simp only [Operation.pushArity, Operation.popArity]); omega) | (have := op_arity_bound o; omega)) (by omega)
    obtain ⟨s2, st2, hf2, hsm2, hpc2, hstk2, hg2⟩ :=
      jumpStep (dest := UInt256.ofNat aL)
        (pre := assembleBytes isPre ++ (Instr.push labelWidthFin (UInt256.ofNat aL)).bytes)
        (post := assembleBytes isC ++ payload)
        (assembleWithPayload_at₂' hbytes payload)
        hf1 hsm1
        (by rw [hpc1]
            exact congrArg UInt256.ofNat
              (by rw [List.length_append, Instr.length_bytes_push]))
        hstk1
        (by rw [toNat_ofNat_of_lt haLlt]; exact hvalid)
        (by simp only [hstk1, hm.stack, mapStk, List.length_map, List.length_cons, Operation.pushArity, Operation.popArity] at hcap ⊢; omega)
        (by omega)
    obtain ⟨s3, st3, hf3, hsm3, hpc3, hstk3, hg3⟩ :=
      jumpdestStep
        (pre := assembleBytes isPreL) (post := assembleBytes isC' ++ payload)
        (by
          rw [assembleWithPayload, hbytesL]
          simp only [List.append_assoc])
        hf2 hsm2
        (by rw [hpc2, hlenPreL])
        (by simp only [hstk2, hm.stack, mapStk, List.length_map, List.length_cons, Operation.pushArity, Operation.popArity] at hcap ⊢; omega) (by omega)
    refine ⟨s3, .trans st1 (.trans st2 (.trans st3 (.refl _))),
      ⟨hf3, hsm3, ?_, ?_, hm.imms_step (by first | rfl | exact builtinWithExternal_immutable_eq hstepOp)⟩, gasChain₃' hg1 hg2 hg3⟩
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
    obtain rfl : [Instr.push labelWidthFin (UInt256.ofNat aL), Instr.op .JUMPI] = isI := by
      simpa using hI
    refine ⟨40000 + 40000 + 40000, .sub (40000 + 40000 + 40000), ?_⟩
    intro s hm hgas
    have hpos : codeSize prog - codeSize (Asm.jumpi l :: c) = codeSize pre := by
      rw [codeSize_cons]
      omega
    have haLsmall : aL < 256 ^ labelWidth := by omega
    have haLlt : aL < 2 ^ 256 := by
      have := codeSize_lt hlow hm.frame
      omega
    have hwfL : (UInt256.ofNat aL).toNat < 256 ^ labelWidthFin.val := by
      rw [labelWidthFin_val, toNat_ofNat_of_lt haLlt]; exact haLsmall
    obtain ⟨s1, st1, hf1, hsm1, hpc1, hstk1, hg1⟩ :=
      pushStepU (u := UInt256.ofNat aL) (hwf := hwfL)
        (pre := assembleBytes isPre)
        (post := (Instr.op .JUMPI).bytes ++ assembleBytes isC ++ payload)
        (assembleWithPayload_at₂ hbytes payload)
        hm.frame hm.smatch
        (by rw [hm.pc, hpos, hlenPre])
        hm.stack (by have hlen : s.stack.length ≤ 1023 := (by rw [hm.stack]; simp only [mapStk, List.length_map]; exact hcap); first | ((try simp only [Operation.pushArity, Operation.popArity]); omega) | (have := op_arity_bound o; omega)) (by omega)
    have hcond : (conv v).toNat ≠ 0 := by
      rw [conv_toNat]
      intro h0
      exact hv (by
        apply BitVec.eq_of_toNat_eq
        simpa using h0)
    obtain ⟨s2, st2, hf2, hsm2, hpc2, hstk2, hg2⟩ :=
      jumpiTakenStep (dest := UInt256.ofNat aL) (cond := conv v)
        (pre := assembleBytes isPre ++ (Instr.push labelWidthFin (UInt256.ofNat aL)).bytes)
        (post := assembleBytes isC ++ payload)
        (assembleWithPayload_at₂' hbytes payload)
        hf1 hsm1
        (by rw [hpc1]
            exact congrArg UInt256.ofNat
              (by rw [List.length_append, Instr.length_bytes_push]))
        (by rw [hstk1]; rfl)
        hcond
        (by rw [toNat_ofNat_of_lt haLlt]; exact hvalid)
        (by simp only [hstk1, hm.stack, mapStk, List.length_map, List.length_cons, Operation.pushArity, Operation.popArity] at hcap ⊢; omega)
        (by omega)
    obtain ⟨s3, st3, hf3, hsm3, hpc3, hstk3, hg3⟩ :=
      jumpdestStep
        (pre := assembleBytes isPreL) (post := assembleBytes isC' ++ payload)
        (by
          rw [assembleWithPayload, hbytesL]
          simp only [List.append_assoc])
        hf2 hsm2
        (by rw [hpc2, hlenPreL])
        (by simp only [hstk2, hm.stack, mapStk, List.length_map, List.length_cons, Operation.pushArity, Operation.popArity] at hcap ⊢; omega) (by omega)
    refine ⟨s3, .trans st1 (.trans st2 (.trans st3 (.refl _))),
      ⟨hf3, hsm3, ?_, ?_, hm.imms_step (by first | rfl | exact builtinWithExternal_immutable_eq hstepOp)⟩, gasChain₃' hg1 hg2 hg3⟩
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
    refine ⟨40000 + 40000, .sub (40000 + 40000), ?_⟩
    intro s hm hgas
    have hpos : codeSize prog - codeSize (Asm.jumpi l :: c) = codeSize pre := by
      rw [codeSize_cons]
      omega
    have hres_lt := resolve_lt hres
    have haLsmall : aL < 256 ^ labelWidth := by omega
    have haLlt : aL < 2 ^ 256 := by
      have := codeSize_lt hlow hm.frame; omega
    have hwfL : (UInt256.ofNat aL).toNat < 256 ^ labelWidthFin.val := by
      rw [labelWidthFin_val, toNat_ofNat_of_lt haLlt]; exact haLsmall
    obtain ⟨s1, st1, hf1, hsm1, hpc1, hstk1, hg1⟩ :=
      pushStepU (u := UInt256.ofNat aL) (hwf := hwfL)
        (pre := assembleBytes isPre)
        (post := (Instr.op .JUMPI).bytes ++ assembleBytes isC ++ payload)
        (assembleWithPayload_at₂ hbytes payload)
        hm.frame hm.smatch
        (by rw [hm.pc, hpos, hlenPre])
        hm.stack (by have hlen : s.stack.length ≤ 1023 := (by rw [hm.stack]; simp only [mapStk, List.length_map]; exact hcap); first | ((try simp only [Operation.pushArity, Operation.popArity]); omega) | (have := op_arity_bound o; omega)) (by omega)
    have hcond : (conv v).toNat = 0 := by
      rw [conv_toNat, hv]
      rfl
    obtain ⟨s2, st2, hf2, hsm2, hpc2, hstk2, hg2⟩ :=
      jumpiNotTakenStep (dest := UInt256.ofNat aL) (cond := conv v)
        (pre := assembleBytes isPre ++ (Instr.push labelWidthFin (UInt256.ofNat aL)).bytes)
        (post := assembleBytes isC ++ payload)
        (assembleWithPayload_at₂' hbytes payload)
        hf1 hsm1
        (by rw [hpc1]
            exact congrArg UInt256.ofNat
              (by rw [List.length_append, Instr.length_bytes_push]))
        (by rw [hstk1]; rfl)
        hcond
        (by simp only [hstk1, hm.stack, mapStk, List.length_map, List.length_cons, Operation.pushArity, Operation.popArity] at hcap ⊢; omega)
        (by omega)
    refine ⟨s2, .trans st1 (.trans st2 (.refl _)), ⟨hf2, hsm2, ?_, hstk2, hm.imms_step (by first | rfl | exact builtinWithExternal_immutable_eq hstepOp)⟩,
      gasChain₂' hg1 hg2⟩
    · show s2.pc = UInt256.ofNat (codeSize prog - codeSize c)
      rw [hpc2, List.length_append, Instr.length_bytes_push, hlenPre]
      exact congrArg UInt256.ofNat (by
        simp only [Asm.size, labelWidthFin_val] at hsize ⊢
        omega)
  | @pushLabel l c σ yst hdef =>
    obtain ⟨pre, isPre, isI, isC, hsplit, hI, hC, hbytes, hlenPre, hsize⟩ :=
      locate hlow hsuf
    simp only [lowerInstr] at hI
    obtain ⟨aL, hres, rfl⟩ := Option.map_eq_some_iff.mp hI
    refine ⟨40000, .sub (40000), ?_⟩
    intro s hm hgas
    have hpos : codeSize prog - codeSize (Asm.pushLabel l :: c) = codeSize pre := by
      rw [codeSize_cons]
      omega
    have hres_lt := resolve_lt hres
    have haLsmall : aL < 256 ^ labelWidth := by omega
    have haLlt : aL < 2 ^ 256 := by
      have := codeSize_lt hlow hm.frame; omega
    have hwfL : (UInt256.ofNat aL).toNat < 256 ^ labelWidthFin.val := by
      rw [labelWidthFin_val, toNat_ofNat_of_lt haLlt]; exact haLsmall
    obtain ⟨s', hstep, hf', hsm', hpc', hstk', hg'⟩ :=
      pushStepU (u := UInt256.ofNat aL) (hwf := hwfL)
        (pre := assembleBytes isPre)
        (post := assembleBytes isC ++ payload)
        (assembleWithPayload_at₁ hbytes payload)
        hm.frame hm.smatch
        (by rw [hm.pc, hpos, hlenPre])
        hm.stack (by have hlen : s.stack.length ≤ 1023 := (by rw [hm.stack]; simp only [mapStk, List.length_map]; exact hcap); first | ((try simp only [Operation.pushArity, Operation.popArity]); omega) | (have := op_arity_bound o; omega)) hgas
    refine ⟨s', .trans hstep (.refl _), ⟨hf', hsm', ?_, ?_, hm.imms_step (by first | rfl | exact builtinWithExternal_immutable_eq hstepOp)⟩, hg'⟩
    · show s'.pc = UInt256.ofNat (codeSize prog - codeSize c)
      rw [hpc', hlenPre]
      exact congrArg UInt256.ofNat (by
        simp only [Asm.size, labelWidthFin_val] at hsize ⊢
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
    refine ⟨40000 + 40000, .sub (40000 + 40000), ?_⟩
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
        (by have hlen : s.stack.length ≤ 1023 := (by rw [hm.stack]; simp only [mapStk, List.length_map]; exact hcap); first | ((try simp only [Operation.pushArity, Operation.popArity]); omega) | (have := op_arity_bound o; omega))
        (by omega)
    obtain ⟨s2, st2, hf2, hsm2, hpc2, hstk2, hg2⟩ :=
      jumpdestStep
        (pre := assembleBytes isPreL) (post := assembleBytes isC' ++ payload)
        (by
          rw [assembleWithPayload, hbytesL]
          simp only [List.append_assoc])
        hf1 hsm1
        (by rw [hpc1, hlenPreL])
        (by simp only [hstk1, hm.stack, mapStk, List.length_map, List.length_cons, Operation.pushArity, Operation.popArity] at hcap ⊢; omega) (by omega)
    refine ⟨s2, .trans st1 (.trans st2 (.refl _)), ⟨hf2, hsm2, ?_, ?_, hm.imms_step (by first | rfl | exact builtinWithExternal_immutable_eq hstepOp)⟩,
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
    (hhalt : builtinWithExternal model.calls model.creates .any yop args yst (.halt yst'))
    {code : ByteArray} {pre post : List UInt8} {σ : List UInt256} {s : State}
    (hcode : code = mkCode (pre ++ (Instr.op o).bytes ++ post))
    (hf : FrameOK code s) (hm : StateMatch yst s)
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hstk : s.stack = args.map conv ++ σ)
    (hcap : s.stack.length + o.pushArity ≤ 1024 + o.popArity)
    (hgas : Gas.baseCost s.fork o ≤ s.gasAvailable) :
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
            (by rw [conv_toNat]; intro h; exact hval (BitVec.toNat_injective (by simpa using h)))
            hgas hcap))
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
        (StepRunning.createStatic s (conv val) (conv off) (conv sz) σ hdec hstk3 hperm hgas hcap))
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
          hdec hstk4 hperm hgas hcap))
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

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- **Phase B, halting step**: a halting built-in maps to one halting EVM
step. -/
theorem ahalt_sim [model : ExternalModel]
    {prog : List Asm} {is : List Instr} {payload : List UInt8}
    (hlow : lowerProg imm prog = some is)
    {a : AConf} {yst' : EvmState} (hstep : AHalt prog a yst')
    (hsuf : a.code <:+ prog) (hcap : a.stk.length ≤ 1023) :
    ∃ bnd : Nat, ∀ s : State, ConfMatch (payload := payload) imm prog is a s →
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
    · refine ⟨40000, ?_⟩
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
        (by have hlen : s.stack.length ≤ 1023 := (by rw [hm.stack]; simp only [mapStk, List.length_map]; exact hcap); first | ((try simp only [Operation.pushArity, Operation.popArity]); omega) | (have := op_arity_bound o; omega))
        (by have hfork : s.fork = .Osaka := hm.frame.fork; rw [hfork]; exact le_trans (baseCost_le_40000 o) hgas)
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
        (by rw [hm.stack, mapStk_words])
        (by have hlen : s.stack.length ≤ 1023 := (by rw [hm.stack]; simp only [mapStk, List.length_map]; exact hcap); first | ((try simp only [Operation.pushArity, Operation.popArity]); omega) | (have := op_arity_bound o; omega)) hgas
      obtain ⟨s', hstep, hsm', hcs', hhm'⟩ := hhalt
      exact ⟨s', .trans hstep (.refl _), hsm', hcs', hhm'⟩

/-- **Phase B, many steps**: transformers compose along an Asm execution —
each step's threshold is pushed back through the transformers before it
(`GasTx.exists_threshold`), and the residuals chain by monotonicity. -/
theorem asteps_sim [model : ExternalModel] (hexternal : ExternalsRealized model)
    {prog : List Asm} {is : List Instr} {payload : List UInt8}
    (hlow : lowerProg imm prog = some is) (hsmall : codeSize prog < 256 ^ labelWidth)
    {a b : AConf} (hsteps : ASteps prog a b) (hsuf : a.code <:+ prog)
    (hbound : ∀ mid, ASteps prog a mid → mid.stk.length ≤ 1023) :
    ∃ (bnd : Nat) (tx : GasTx), ∀ s : State, ConfMatch (payload := payload) imm prog is a s →
      bnd ≤ s.gasAvailable →
      ∃ s', Steps s s' ∧ ConfMatch (payload := payload) imm prog is b s'
        ∧ tx.f s.gasAvailable ≤ s'.gasAvailable := by
  induction hsteps with
  | refl a =>
    exact ⟨0, .sub 0, fun s hm _ => ⟨s, .refl _, hm, Nat.sub_le _ _⟩⟩
  | @head a₁ a₂ a₃ hstep hrest ih =>
    obtain ⟨b1, t1, H1⟩ := astep_sim hexternal hlow hsmall hstep hsuf (hbound a₁ (ASteps.refl a₁))
    obtain ⟨b2, t2, H2⟩ := ih (hstep.suffix hsuf) (fun mid h => hbound mid (ASteps.head hstep h))
    obtain ⟨b0, hb1, hb2⟩ := t1.exists_threshold b1 b2
    refine ⟨b0, t2.comp t1, ?_⟩
    intro s hm hgas
    obtain ⟨s1, st1, hm1, hg1⟩ := H1 s hm (Nat.le_trans hb1 hgas)
    obtain ⟨s2, st2, hm2, hg2⟩ := H2 s1 hm1 (Nat.le_trans (hb2 _ hgas) hg1)
    exact ⟨s2, st1.append st2, hm2, Nat.le_trans (t2.mono hg1) hg2⟩

/-- **Phase B, halting run**: an Asm execution ending in a halt maps to an
EVM execution ending in the matching halted state. -/
theorem arun_halt_sim [model : ExternalModel] (hexternal : ExternalsRealized model)
    {prog : List Asm} {is : List Instr} {payload : List UInt8}
    (hlow : lowerProg imm prog = some is) (hsmall : codeSize prog < 256 ^ labelWidth)
    {a b : AConf} {yst' : EvmState}
    (hsteps : ASteps prog a b) (hhalt : AHalt prog b yst')
    (hsuf : a.code <:+ prog)
    (hbound : ∀ mid, ASteps prog a mid → mid.stk.length ≤ 1023) :
    ∃ bnd : Nat, ∀ s : State, ConfMatch (payload := payload) imm prog is a s →
      bnd ≤ s.gasAvailable →
      ∃ s', Steps s s' ∧ StateMatch yst' s' ∧ s'.callStack = []
        ∧ HaltedMatch yst' s' := by
  obtain ⟨b1, t1, H1⟩ := asteps_sim hexternal hlow hsmall hsteps hsuf hbound
  obtain ⟨b2, H2⟩ := ahalt_sim hlow hhalt (hsteps.suffix hsuf) (hbound b hsteps)
  obtain ⟨b0, hb1, hb2⟩ := t1.exists_threshold b1 b2
  refine ⟨b0, ?_⟩
  intro s hm hgas
  obtain ⟨s1, st1, hm1, hg1⟩ := H1 s hm (Nat.le_trans hb1 hgas)
  obtain ⟨s2, st2, hsm2, hcs2, hhm2⟩ := H2 s1 hm1 (Nat.le_trans (hb2 _ hgas) hg1)
  exact ⟨s2, st1.append st2, hsm2, hcs2, hhm2⟩

end YulEvmCompiler
