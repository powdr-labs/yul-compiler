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
open YulSemantics (Expr Stmt Block Ident)
open YulSemantics.EVM (Op)

private theorem gsub2 {a b c k₁ k₂ : Nat} (h₁ : a - k₁ ≤ b) (h₂ : b - k₂ ≤ c) :
    a - (k₁ + k₂) ≤ c := by omega
private theorem genough {a s₁ k₁ k₂ : Nat} (hb : k₁ + k₂ ≤ a) (h₁ : a - k₁ ≤ s₁) :
    k₂ ≤ s₁ := by omega
private theorem gstrip {x y z : Nat} (h : x + y ≤ z) : x ≤ z := by omega
private theorem p67 (n : Nat) : n + 67 + 1 = n + 68 := by omega

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

/-- Code-fixed, position-aware *expression* simulation: like `SimE`, but with the
whole program `code` a fixed parameter (so callees in argument position can be
located via `ProgLayout`). The variable region `vimg V` is fixed, `τ` are the
`off` temporaries above it, and the fragment pushes `out`. -/
def SimEC (code : ByteArray) (pcc off : Nat) (yst : EvmState) (V : VEnv yul)
    (is : List Instr) (out : List YulSemantics.EVM.U256) (yst' : EvmState) : Prop :=
  ∃ b : Nat, ∀ (preIs : List Instr) (post : List UInt8) (τ σ : List UInt256) (s : State),
    code = mkCode (assembleBytes preIs ++ assembleBytes is ++ post) →
    (assembleBytes preIs).length = pcc →
    FrameOK code s → StateMatch yst s →
    s.pc = UInt256.ofNat pcc →
    s.stack = τ ++ vimg V ++ σ →
    τ.length = off →
    b ≤ s.gasAvailable →
    ∃ s', Steps s s' ∧ FrameOK code s' ∧ StateMatch yst' s'
      ∧ s'.pc = UInt256.ofNat (pcc + (assembleBytes is).length)
      ∧ s'.stack = out.map conv ++ τ ++ vimg V ++ σ
      ∧ s.gasAvailable - b ≤ s'.gasAvailable

/-- Every code-quantified `SimE` result specializes to `SimEC` at any concrete
`code` and position. -/
theorem SimE.toSimEC {off : Nat} {yst : EvmState} {V : VEnv yul} {is : List Instr}
    {out : List YulSemantics.EVM.U256} {yst' : EvmState} (h : SimE yst V off is out yst')
    (code : ByteArray) (pcc : Nat) : SimEC code pcc off yst V is out yst' := by
  obtain ⟨b, H⟩ := h
  refine ⟨b, fun preIs post τ σ s hcode hpre hf hm hpc hstk hτ hg => ?_⟩
  obtain ⟨s', hsteps, hf', hm', hpc', hstk', hg'⟩ :=
    H code (assembleBytes preIs) post τ σ s hcode hf hm (by rw [hpc, hpre]) hstk hτ hg
  exact ⟨s', hsteps, hf', hm', by rw [hpc', hpre], hstk', hg'⟩

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

/-- **Reuse the function-free simulation for a call-free statement.** If the
source executes statement `st` normally and the *function-free* compiler
accepts it (so `st` contains no calls), then `Correctness.sim` gives its
`SimSP`, which lifts to `SimSPC` for any concrete `code`. This is how `simF`
discharges every call-free statement — the function-aware compiler produces the
same code (`compileStmtF_extends`). -/
theorem stmtF_reuse (code : ByteArray) {funs : YulSemantics.FunEnv yul} {V V' : VEnv yul}
    {yst yst' : EvmState} {st : Stmt Op} {pc : Nat} {is : List Instr} {Γ' : List Ident}
    (h : YulSemantics.Step yul funs V yst (.stmt st) (.sres V' yst' .normal))
    (hc : compileStmt pc (names V) st = some (is, Γ')) :
    Γ' = names V' ∧ SimSPC code pc yst V is yst' V' := by
  rcases sim h pc is Γ' hc with ⟨_, hΓ, hsp⟩ | ⟨ho, _⟩
  · exact ⟨hΓ, hsp.toSimSPC code⟩
  · exact absurd ho (by simp)

/-- Statement-sequence version of `stmtF_reuse`. -/
theorem stmtsF_reuse (code : ByteArray) {funs : YulSemantics.FunEnv yul} {V V' : VEnv yul}
    {yst yst' : EvmState} {ss : List (Stmt Op)} {pc : Nat} {is : List Instr} {Γ' : List Ident}
    (h : YulSemantics.Step yul funs V yst (.stmts ss) (.sres V' yst' .normal))
    (hc : compileStmts pc (names V) ss = some (is, Γ')) :
    Γ' = names V' ∧ SimSPC code pc yst V is yst' V' := by
  rcases sim h pc is Γ' hc with ⟨_, hΓ, hsp⟩ | ⟨ho, _⟩
  · exact ⟨hΓ, hsp.toSimSPC code⟩
  · exact absurd ho (by simp)



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


set_option maxHeartbeats 1000000 in

/-- **The caller prologue reaches the callee entry.** For a procedure the
scaffold prologue is `PUSH retaddr ; PUSH entry ; JUMP`; executing it pushes the
return address, then jumps to `entry`, leaving `retaddr` (as a word) on top of
the caller's stack. -/
theorem callerReachEntry (code : ByteArray) (preIs : List Instr) (post : List UInt8)
    (entry retaddr : Nat) (σ : List UInt256) (yst : EvmState) (s : State)
    (hcode : code = mkCode (assembleBytes preIs
      ++ assembleBytes [.push (UInt256.ofNat retaddr), .push (UInt256.ofNat entry), .op .JUMP]
      ++ post))
    (hf : FrameOK code s) (hm : StateMatch yst s)
    (hpc : s.pc = UInt256.ofNat (assembleBytes preIs).length)
    (hstk : s.stack = σ)
    (hentryvalid : Decode.isValidJumpDest code entry = true)
    (hentrylt : entry < 2 ^ 256)
    (hgas : 40000 + (40000 + 40000) ≤ s.gasAvailable) :
    ∃ s', Steps s s' ∧ FrameOK code s' ∧ StateMatch yst s'
      ∧ s'.pc = UInt256.ofNat entry
      ∧ s'.stack = UInt256.ofNat retaddr :: σ
      ∧ s.gasAvailable - (40000 + (40000 + 40000)) ≤ s'.gasAvailable := by
  have hbytes : assembleBytes [.push (UInt256.ofNat retaddr), .push (UInt256.ofNat entry), .op .JUMP]
      = (Instr.push (conv (BitVec.ofNat 256 retaddr))).bytes
        ++ (Instr.push (conv (BitVec.ofNat 256 entry))).bytes ++ (Instr.op .JUMP).bytes := by
    simp only [assembleBytes_cons, assembleBytes_nil, List.append_nil, List.append_assoc, conv_ofNat]
  -- 1) PUSH retaddr
  have hcode1 : code = mkCode (assembleBytes preIs ++ (Instr.push (conv (BitVec.ofNat 256 retaddr))).bytes
      ++ ((Instr.push (conv (BitVec.ofNat 256 entry))).bytes ++ (Instr.op .JUMP).bytes ++ post)) := by
    rw [hcode, hbytes]; simp only [List.append_assoc]
  obtain ⟨s1, hstep1, hf1, hm1, hpc1, hstk1, hg1⟩ :=
    pushStep hcode1 hf hm hpc hstk (gstrip hgas)
  simp only [List.map_cons, List.map_nil, conv_ofNat] at hstk1
  -- 2) PUSH entry
  have hcode2 : code = mkCode ((assembleBytes preIs ++ (Instr.push (conv (BitVec.ofNat 256 retaddr))).bytes)
      ++ (Instr.push (conv (BitVec.ofNat 256 entry))).bytes ++ ((Instr.op .JUMP).bytes ++ post)) := by
    rw [hcode, hbytes]; simp only [List.append_assoc]
  have hpc1' : s1.pc = UInt256.ofNat (assembleBytes preIs
      ++ (Instr.push (conv (BitVec.ofNat 256 retaddr))).bytes).length := by
    rw [hpc1, List.length_append, Instr.length_bytes_push]
  obtain ⟨s2, hstep2, hf2, hm2, hpc2, hstk2, hg2⟩ :=
    pushStep hcode2 hf1 hm1 hpc1' hstk1 (gstrip (genough hgas hg1))
  simp only [List.map_cons, List.map_nil, conv_ofNat] at hstk2
  -- 3) JUMP to entry
  have hcode3 : code = mkCode ((assembleBytes preIs
      ++ (Instr.push (conv (BitVec.ofNat 256 retaddr))).bytes
      ++ (Instr.push (conv (BitVec.ofNat 256 entry))).bytes) ++ (Instr.op .JUMP).bytes ++ post) := by
    rw [hcode, hbytes]; simp only [List.append_assoc]
  have hpc2' : s2.pc = UInt256.ofNat (assembleBytes preIs
      ++ (Instr.push (conv (BitVec.ofNat 256 retaddr))).bytes
      ++ (Instr.push (conv (BitVec.ofNat 256 entry))).bytes).length := by
    rw [hpc2, List.length_append, List.length_append, Instr.length_bytes_push,
      Instr.length_bytes_push, List.length_append, Instr.length_bytes_push]
  have hjvalid : Decode.isValidJumpDest code (UInt256.ofNat entry).toNat = true := by
    rw [toNat_ofNat_of_lt hentrylt]; exact hentryvalid
  obtain ⟨s3, hstep3, hf3, hm3, hpc3, hstk3, hg3⟩ :=
    jumpStep hcode3 hf2 hm2 hpc2' hstk2 hjvalid (genough (genough hgas hg1) hg2)
  exact ⟨s3, Steps.trans hstep1 (Steps.trans hstep2 (.trans hstep3 (.refl _))), hf3, hm3,
    hpc3, hstk3, gsub2 hg1 (gsub2 hg2 hg3)⟩


set_option maxHeartbeats 4000000 in

/-- **A procedure call is correct.** The call scaffold `PUSH retaddr ; PUSH entry
; JUMP ; JUMPDEST` (no args/params/rets) simulates the source `callOk` step:
given the callee body simulates (`SimSPC` over the empty region) and the entry
is a valid `JUMPDEST`, the whole scaffold advances the program to just past the
landing pad, leaving the caller's variable region and stack unchanged, in the
post-body state. -/
theorem SimCallProc (code : ByteArray) (pcc entry retaddr : Nat)
    (calleePre bodyCode calleePost : List Instr) (V : VEnv yul) (yst st2 : EvmState)
    (hretaddr : retaddr = pcc + 67)
    (hcallee : code = mkCode (assembleBytes calleePre
        ++ assembleBytes ([.op .JUMPDEST] ++ bodyCode ++ [.op .JUMP]) ++ assembleBytes calleePost))
    (hcentry : (assembleBytes calleePre).length = entry)
    (hbody : SimSPC code (entry + 1) yst [] bodyCode st2 [])
    (hentryvalid : Decode.isValidJumpDest code entry = true)
    (hentrylt : entry < 2 ^ 256) :
    SimSPC code pcc yst V (callScaffold retaddr entry 0 []) st2 V := by
  obtain ⟨bb, Hbody⟩ := hbody
  have hscaf : callScaffold retaddr entry 0 []
      = [.push (UInt256.ofNat retaddr), .push (UInt256.ofNat entry)] ++ [.op .JUMP] ++ [.op .JUMPDEST] := by
    simp [callScaffold]
  refine ⟨(40000 + (40000 + 40000)) + (40000 + (bb + (40000 + 40000))),
    fun preIs post σ s hcode hpre hf hm hpc hstk hgas => ?_⟩
  -- decompose the scaffold: prologue (2 pushes + JUMP) then the landing JUMPDEST
  set prologue : List Instr := [.push (UInt256.ofNat retaddr), .push (UInt256.ofNat entry), .op .JUMP]
    with hprol
  have hcodescaf : assembleBytes (callScaffold retaddr entry 0 [])
      = assembleBytes prologue ++ (Instr.op .JUMPDEST).bytes := by
    rw [hscaf, hprol]; simp only [assembleBytes_append, assembleBytes_cons, assembleBytes_nil,
      List.append_nil, List.append_assoc]
  -- 1) prologue: reach the callee entry (retaddr word on top)
  have hcodeP : code = mkCode (assembleBytes preIs ++ assembleBytes prologue
      ++ ((Instr.op .JUMPDEST).bytes ++ post)) := by
    rw [hcode, hcodescaf]; simp only [List.append_assoc]
  obtain ⟨s1, stP, hfP, hmP, hpcP, hstkP, hgP⟩ :=
    callerReachEntry code preIs ((Instr.op .JUMPDEST).bytes ++ post) entry retaddr
      (vimg V ++ σ) yst s hcodeP hf hm (by rw [hpc, hpre]) hstk hentryvalid hentrylt
      (gstrip hgas)
  -- 2a) callee entry JUMPDEST
  have hcode1 : code = mkCode (assembleBytes calleePre ++ (Instr.op .JUMPDEST).bytes
      ++ (assembleBytes bodyCode ++ (Instr.op .JUMP).bytes ++ assembleBytes calleePost)) := by
    rw [hcallee]; congr 1
    simp only [assembleBytes_append, assembleBytes_cons, assembleBytes_nil, List.append_nil,
      List.append_assoc]
  obtain ⟨s2, hstep2, hf2, hm2, hpc2, hstk2, hg2⟩ :=
    jumpdestStep hcode1 hfP hmP (by rw [hpcP, hcentry]) (gstrip (genough hgas hgP))
  -- 2b) body
  have hcode2 : code = mkCode (assembleBytes (calleePre ++ [.op .JUMPDEST]) ++ assembleBytes bodyCode
      ++ ((Instr.op .JUMP).bytes ++ assembleBytes calleePost)) := by
    rw [hcallee]; congr 1
    simp only [assembleBytes_append, assembleBytes_cons, assembleBytes_nil, List.append_nil,
      List.append_assoc]
  have hpre2 : (assembleBytes (calleePre ++ [.op .JUMPDEST])).length = entry + 1 := by
    rw [assembleBytes_append, List.length_append, hcentry, assembleBytes_cons, assembleBytes_nil]
    simp [Instr.length_bytes_op]
  obtain ⟨s3, st3, hf3, hm3, hpc3, hstk3, hg3⟩ :=
    Hbody (calleePre ++ [.op .JUMPDEST]) ((Instr.op .JUMP).bytes ++ assembleBytes calleePost)
      (UInt256.ofNat retaddr :: vimg V ++ σ) s2 hcode2 hpre2 hf2 hm2 (by rw [hpc2, hcentry])
      (by rw [hstk2, hstkP]; simp [vimg]) (gstrip (genough (genough hgas hgP) hg2))
  -- 2c) return JUMP — lands on the scaffold JUMPDEST at retaddr
  have hcode3 : code = mkCode ((assembleBytes (calleePre ++ [.op .JUMPDEST]) ++ assembleBytes bodyCode)
      ++ (Instr.op .JUMP).bytes ++ assembleBytes calleePost) := by
    rw [hcode2]; simp only [List.append_assoc]
  have hpc3' : s3.pc = UInt256.ofNat
      (assembleBytes (calleePre ++ [.op .JUMPDEST]) ++ assembleBytes bodyCode).length := by
    rw [hpc3, List.length_append, hpre2]
  -- retaddr < 2^256 and the landing JUMPDEST is valid
  have hretlt : retaddr < 2 ^ 256 := by
    have hsz := hf.codeSmall
    rw [hcode] at hsz; simp only [size_mkCode] at hsz
    rw [hscaf] at hsz
    simp only [assembleBytes_append, assembleBytes_cons, assembleBytes_nil, List.append_nil,
      List.length_append, Instr.length_bytes_push, Instr.length_bytes_op, hpre] at hsz
    omega
  have hlandvalid : Decode.isValidJumpDest code (UInt256.ofNat retaddr).toNat = true := by
    rw [toNat_ofNat_of_lt hretlt]
    have hb := isValidJumpDest_boundary (preIs ++ prologue) post
    rw [show (assembleBytes (preIs ++ prologue)).length = retaddr from by
        rw [assembleBytes_append, List.length_append, hpre, hprol]
        simp [assembleBytes_cons, assembleBytes_nil, Instr.length_bytes_push,
          Instr.length_bytes_op, hretaddr]] at hb
    rw [show mkCode (assembleBytes (preIs ++ prologue) ++ (Instr.op .JUMPDEST).bytes ++ post)
        = code from by
        rw [hcode, hcodescaf, assembleBytes_append]; congr 1; simp [List.append_assoc]] at hb
    exact hb
  have hstk3' : s3.stack = UInt256.ofNat retaddr :: (vimg V ++ σ) := by rw [hstk3]; simp [vimg]
  obtain ⟨s4, hstep4, hf4, hm4, hpc4, hstk4, hg4⟩ :=
    jumpStep hcode3 hf3 hm3 hpc3' hstk3' hlandvalid
      (gstrip (genough (genough (genough hgas hgP) hg2) hg3))
  -- 3) landing JUMPDEST
  have hplen : (assembleBytes (preIs ++ prologue)).length = pcc + 67 := by
    rw [assembleBytes_append, List.length_append, hpre, hprol]
    simp [assembleBytes_cons, assembleBytes_nil, Instr.length_bytes_push, Instr.length_bytes_op]
  have hslen : (assembleBytes (callScaffold retaddr entry 0 [])).length = 68 := by
    rw [length_assembleBytes_callScaffold]; simp [scaffoldLen, assembleBytes_nil]
  have hcodeL : code = mkCode (assembleBytes (preIs ++ prologue) ++ (Instr.op .JUMPDEST).bytes ++ post) := by
    rw [hcode, hcodescaf, assembleBytes_append]; congr 1; simp [List.append_assoc]
  have hpc4' : s4.pc = UInt256.ofNat (assembleBytes (preIs ++ prologue)).length := by
    rw [hpc4, hretaddr, hplen]
  obtain ⟨s5, hstep5, hf5, hm5, hpc5, hstk5, hg5⟩ :=
    jumpdestStep hcodeL hf4 hm4 hpc4' (genough (genough (genough (genough hgas hgP) hg2) hg3) hg4)
  refine ⟨s5, stP.append (Steps.trans hstep2 (st3.append (Steps.trans hstep4 (.trans hstep5 (.refl _))))),
    hf5, hm5, ?_, ?_, ?_⟩
  · rw [hpc5, hplen, hslen]
  · rw [hstk5, hstk4]
  · exact gsub2 hgP (gsub2 hg2 (gsub2 hg3 (gsub2 hg4 hg5)))

end YulEvmCompiler
