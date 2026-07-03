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

private theorem gsub2 {a b c k₁ k₂ : Nat} (h₁ : a - k₁ ≤ b) (h₂ : b - k₂ ≤ c) :
    a - (k₁ + k₂) ≤ c := by omega
private theorem genough {a s₁ k₁ k₂ : Nat} (hb : k₁ + k₂ ≤ a) (h₁ : a - k₁ ≤ s₁) :
    k₂ ≤ s₁ := by omega
private theorem gstrip {x y z : Nat} (h : x + y ≤ z) : x ≤ z := by omega

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



/-- **The callee side of a procedure call executes correctly.** A procedure body
compiles to `JUMPDEST ++ bodyCode ++ [JUMP]` (no params/rets ⇒ no POPs, no
reshuffle). Given the body simulates (`SimSPC` with the empty variable region)
and the return address is a valid `JUMPDEST`, running from the callee entry
reaches `retaddr` with the caller's stack `rest` restored, in the post-body
state `st2`. -/
theorem calleeRunProc (code : ByteArray) (preIs bodyCode postIs : List Instr)
    (entry : Nat) (retaddr : UInt256) (rest : List UInt256) (yst st2 : EvmState)
    (hcode : code = mkCode (assembleBytes preIs
        ++ assembleBytes ([.op .JUMPDEST] ++ bodyCode ++ [.op .JUMP]) ++ assembleBytes postIs))
    (hentry : (assembleBytes preIs).length = entry)
    (hbody : SimSPC code (entry + 1) yst [] bodyCode st2 [])
    (hretvalid : Decode.isValidJumpDest code retaddr.toNat = true) :
    ∃ b, ∀ (s : State), FrameOK code s → StateMatch yst s →
      s.pc = UInt256.ofNat entry → s.stack = retaddr :: rest → b ≤ s.gasAvailable →
      ∃ s', Steps s s' ∧ FrameOK code s' ∧ StateMatch st2 s'
        ∧ s'.pc = retaddr ∧ s'.stack = rest ∧ s.gasAvailable - b ≤ s'.gasAvailable := by
  obtain ⟨bb, Hbody⟩ := hbody
  -- assembled callee body: JUMPDEST ++ bodyCode ++ JUMP
  have hAB : assembleBytes ([.op .JUMPDEST] ++ bodyCode ++ [.op .JUMP])
      = (Instr.op .JUMPDEST).bytes ++ assembleBytes bodyCode ++ (Instr.op .JUMP).bytes := by
    simp only [assembleBytes_append, assembleBytes_cons, assembleBytes_nil, List.append_nil]
  refine ⟨40000 + (bb + 40000), fun s hf hm hpc hstk hgas => ?_⟩
  -- 1) execute the entry JUMPDEST
  have hcode1 : code = mkCode (assembleBytes preIs ++ (Instr.op .JUMPDEST).bytes
      ++ (assembleBytes bodyCode ++ (Instr.op .JUMP).bytes ++ assembleBytes postIs)) := by
    rw [hcode, hAB]; congr 1; simp [List.append_assoc]
  obtain ⟨s1, hstep1, hf1, hm1, hpc1, hstk1, hg1⟩ :=
    jumpdestStep hcode1 hf hm (by rw [hpc, hentry]) (gstrip hgas)
  -- 2) run the body
  have hcode2 : code = mkCode (assembleBytes (preIs ++ [.op .JUMPDEST]) ++ assembleBytes bodyCode
      ++ ((Instr.op .JUMP).bytes ++ assembleBytes postIs)) := by
    rw [hcode, hAB, assembleBytes_append, assembleBytes_cons, assembleBytes_nil]
    simp [List.append_assoc]
  have hpre2 : (assembleBytes (preIs ++ [.op .JUMPDEST])).length = entry + 1 := by
    rw [assembleBytes_append, List.length_append, hentry, assembleBytes_cons, assembleBytes_nil]
    simp [Instr.length_bytes_op]
  obtain ⟨s2, st2steps, hf2, hm2, hpc2, hstk2, hg2⟩ :=
    Hbody (preIs ++ [.op .JUMPDEST]) ((Instr.op .JUMP).bytes ++ assembleBytes postIs)
      (retaddr :: rest) s1 hcode2 hpre2 hf1 hm1 (by rw [hpc1, hentry])
      (by rw [hstk1, hstk]; simp [vimg]) (gstrip (genough hgas hg1))
  -- 3) execute the return JUMP
  have hcode3 : code = mkCode ((assembleBytes (preIs ++ [.op .JUMPDEST]) ++ assembleBytes bodyCode)
      ++ (Instr.op .JUMP).bytes ++ assembleBytes postIs) := by
    rw [hcode2]; simp [List.append_assoc]
  have hpc2' : s2.pc = UInt256.ofNat
      (assembleBytes (preIs ++ [.op .JUMPDEST]) ++ assembleBytes bodyCode).length := by
    rw [hpc2, List.length_append, hpre2]
  have hstk2' : s2.stack = retaddr :: rest := by rw [hstk2]; simp [vimg]
  obtain ⟨s3, hstep3, hf3, hm3, hpc3, hstk3, hg3⟩ :=
    jumpStep hcode3 hf2 hm2 hpc2' hstk2' hretvalid
      (genough (genough hgas hg1) hg2)
  exact ⟨s3, .trans hstep1 (st2steps.snoc hstep3), hf3, hm3, hpc3, hstk3,
    gsub2 hg1 (gsub2 hg2 hg3)⟩

end YulEvmCompiler
