import YulEvmCompiler.OpStep

/-!
# YulEvmCompiler.Correctness

The compiler-correctness theorem: a straight-line Yul program that the
compiler accepts behaves, when compiled and executed by the EVM semantics,
exactly as the Yul big-step semantics prescribes.

The proof is a forward simulation. `SimOk`/`SimHalt` give the target-side
meaning of a source evaluation ("the compiled fragment, embedded anywhere in
the code and run with enough gas, pushes the produced values and matches the
final state" / "… halts with the matching halt"); they compose along the
structure of the source derivation (`comp`, `frame`, `extend`), with
`opStep`/`pushStep` as the leaves. The induction over the Yul `Step`
judgment (`sim`) puts it together, and `compile_correct` /
`compile_correct_eval` package the top level (including the implicit `STOP`
when a straight-line program falls off the end of the code).
-/

namespace YulEvmCompiler

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM (U256 EvmState Op stepOp)
open YulSemantics (Outcome)

/-! ### Target-side meaning of a source evaluation -/

/-- The compiled fragment `is`, embedded at any position of the code, takes
any matching state whose stack starts with `ins`'s images to a matching state
with `out`'s images in their place, ending right after the fragment, and
consumes at most `b` gas (the existentially chosen bound). -/
def SimOk (yst : EvmState) (is : List Instr) (ins out : List U256)
    (yst' : EvmState) : Prop :=
  ∃ b : Nat, ∀ (code : ByteArray) (pre post : List UInt8) (σ : List UInt256)
    (s : State),
    code = mkCode (pre ++ assembleBytes is ++ post) →
    FrameOK code s → StateMatch yst s →
    s.pc = UInt256.ofNat pre.length →
    s.stack = ins.map conv ++ σ →
    b ≤ s.gasAvailable →
    ∃ s', Steps s s' ∧ FrameOK code s' ∧ StateMatch yst' s'
      ∧ s'.pc = UInt256.ofNat (pre.length + (assembleBytes is).length)
      ∧ s'.stack = out.map conv ++ σ
      ∧ s.gasAvailable - b ≤ s'.gasAvailable

/-- Like `SimOk`, but the source evaluation halts: the target halts with the
matching halt kind and payload. -/
def SimHalt (yst : EvmState) (is : List Instr) (ins : List U256)
    (yst' : EvmState) : Prop :=
  ∃ b : Nat, ∀ (code : ByteArray) (pre post : List UInt8) (σ : List UInt256)
    (s : State),
    code = mkCode (pre ++ assembleBytes is ++ post) →
    FrameOK code s → StateMatch yst s →
    s.pc = UInt256.ofNat pre.length →
    s.stack = ins.map conv ++ σ →
    b ≤ s.gasAvailable →
    ∃ s', Steps s s' ∧ StateMatch yst' s' ∧ s'.callStack = []
      ∧ HaltedMatch yst' s'

/-! ### Structural rules -/

theorem SimOk.nil {yst : EvmState} {ins : List U256} :
    SimOk yst [] ins ins yst := by
  refine ⟨0, ?_⟩
  intro code pre post σ s hcode hf hm hpc hstk hgas
  exact ⟨s, .refl s, hf, hm, by simpa using hpc, hstk, by omega⟩

theorem SimOk.comp {yst : EvmState} {is1 is2 : List Instr}
    {ins out1 out2 : List U256} {yst1 yst2 : EvmState}
    (h1 : SimOk yst is1 ins out1 yst1) (h2 : SimOk yst1 is2 out1 out2 yst2) :
    SimOk yst (is1 ++ is2) ins out2 yst2 := by
  obtain ⟨b1, H1⟩ := h1
  obtain ⟨b2, H2⟩ := h2
  refine ⟨b1 + b2, ?_⟩
  intro code pre post σ s hcode hf hm hpc hstk hgas
  obtain ⟨s1, st1, hf1, hm1, hpc1, hstk1, hg1⟩ :=
    H1 code pre (assembleBytes is2 ++ post) σ s
      (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf hm hpc hstk
      (by omega)
  obtain ⟨s2, st2, hf2, hm2, hpc2, hstk2, hg2⟩ :=
    H2 code (pre ++ assembleBytes is1) post σ s1
      (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf1 hm1
      (by rw [hpc1]; congr 1; simp) hstk1 (by omega)
  refine ⟨s2, st1.append st2, hf2, hm2, ?_, hstk2, by omega⟩
  rw [hpc2]
  congr 1
  simp [assembleBytes_append]
  omega

theorem SimOk.frame {yst : EvmState} {is : List Instr} {ins out : List U256}
    {yst' : EvmState} (h : SimOk yst is ins out yst') (extra : List U256) :
    SimOk yst is (ins ++ extra) (out ++ extra) yst' := by
  obtain ⟨b, H⟩ := h
  refine ⟨b, ?_⟩
  intro code pre post σ s hcode hf hm hpc hstk hgas
  obtain ⟨s', hsteps, hf', hm', hpc', hstk', hg'⟩ :=
    H code pre post (extra.map conv ++ σ) s hcode hf hm hpc
      (by simpa [List.append_assoc] using hstk) hgas
  exact ⟨s', hsteps, hf', hm', hpc',
    by simpa [List.append_assoc] using hstk', hg'⟩

theorem SimOk.compHalt {yst : EvmState} {is1 is2 : List Instr}
    {ins out1 : List U256} {yst1 yst2 : EvmState}
    (h1 : SimOk yst is1 ins out1 yst1) (h2 : SimHalt yst1 is2 out1 yst2) :
    SimHalt yst (is1 ++ is2) ins yst2 := by
  obtain ⟨b1, H1⟩ := h1
  obtain ⟨b2, H2⟩ := h2
  refine ⟨b1 + b2, ?_⟩
  intro code pre post σ s hcode hf hm hpc hstk hgas
  obtain ⟨s1, st1, hf1, hm1, hpc1, hstk1, hg1⟩ :=
    H1 code pre (assembleBytes is2 ++ post) σ s
      (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf hm hpc hstk
      (by omega)
  obtain ⟨s2, st2, hm2, hcs2, hhm2⟩ :=
    H2 code (pre ++ assembleBytes is1) post σ s1
      (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf1 hm1
      (by rw [hpc1]; congr 1; simp) hstk1 (by omega)
  exact ⟨s2, st1.append st2, hm2, hcs2, hhm2⟩

theorem SimHalt.frame {yst : EvmState} {is : List Instr} {ins : List U256}
    {yst' : EvmState} (h : SimHalt yst is ins yst') (extra : List U256) :
    SimHalt yst is (ins ++ extra) yst' := by
  obtain ⟨b, H⟩ := h
  refine ⟨b, ?_⟩
  intro code pre post σ s hcode hf hm hpc hstk hgas
  exact H code pre post (extra.map conv ++ σ) s hcode hf hm hpc
    (by simpa [List.append_assoc] using hstk) hgas

/-- A fragment that halts ignores anything compiled after it. -/
theorem SimHalt.extend {yst : EvmState} {is1 : List Instr} {ins : List U256}
    {yst' : EvmState} (h : SimHalt yst is1 ins yst') (is2 : List Instr) :
    SimHalt yst (is1 ++ is2) ins yst' := by
  obtain ⟨b, H⟩ := h
  refine ⟨b, ?_⟩
  intro code pre post σ s hcode hf hm hpc hstk hgas
  exact H code pre (assembleBytes is2 ++ post) σ s
    (by rw [hcode]; congr 1; simp [assembleBytes_append]) hf hm hpc hstk hgas

/-! ### Leaves -/

theorem simOk_push {yst : EvmState} (u : U256) :
    SimOk yst [.push (conv u)] [] [u] yst := by
  refine ⟨40000, ?_⟩
  intro code pre post σ s hcode hf hm hpc hstk hgas
  have hbytes : assembleBytes [Instr.push (conv u)] = (Instr.push (conv u)).bytes := by
    simp
  have hlen : (assembleBytes [Instr.push (conv u)]).length = 33 := by
    rw [hbytes]
    exact Instr.size_push (conv u)
  have hcode' : code = mkCode (pre ++ (Instr.push (conv u)).bytes ++ post) := by
    rw [hcode, hbytes]
  obtain ⟨s', hstep, hf', hm', hpc', hstk', hg'⟩ :=
    pushStep hcode' hf hm hpc (by simpa using hstk) hgas
  refine ⟨s', .trans hstep (.refl _), hf', hm', ?_, hstk', hg'⟩
  rw [hpc', hlen]

theorem simOk_op {yop : Op} {o : Operation} (hop : opTable yop = some o)
    {args rets : List U256} {yst yst' : EvmState}
    (hyul : stepOp yop args yst = some (.ok rets yst')) :
    SimOk yst [.op o] args rets yst' := by
  refine ⟨opBound yop args, ?_⟩
  intro code pre post σ s hcode hf hm hpc hstk hgas
  have hbytes : assembleBytes [Instr.op o] = (Instr.op o).bytes := by
    simp
  have hlen : (assembleBytes [Instr.op o]).length = 1 := by
    rw [hbytes]
    exact Instr.size_op o
  have hcode' : code = mkCode (pre ++ (Instr.op o).bytes ++ post) := by
    rw [hcode, hbytes]
  obtain ⟨s', hstep, hf', hm', hpc', hstk', hg'⟩ :=
    opStep hop hyul hcode' hf hm hpc hstk hgas
  refine ⟨s', .trans hstep (.refl _), hf', hm', ?_, hstk', hg'⟩
  rw [hpc', hlen]

theorem simHalt_op {yop : Op} {o : Operation} (hop : opTable yop = some o)
    {args : List U256} {yst yst' : EvmState}
    (hyul : stepOp yop args yst = some (.halt yst')) :
    SimHalt yst [.op o] args yst' := by
  refine ⟨opBound yop args, ?_⟩
  intro code pre post σ s hcode hf hm hpc hstk hgas
  have hbytes : assembleBytes [Instr.op o] = (Instr.op o).bytes := by
    simp
  have hcode' : code = mkCode (pre ++ (Instr.op o).bytes ++ post) := by
    rw [hcode, hbytes]
  obtain ⟨s', hstep, hm', hcs', hhm'⟩ :=
    opStep hop hyul hcode' hf hm hpc hstk hgas
  exact ⟨s', .trans hstep (.refl _), hm', hcs', hhm'⟩

/-! ### Compiler inversion -/

private theorem compileArgs_cons_inv {e : YulSemantics.Expr Op}
    {rest : List (YulSemantics.Expr Op)} {is : List Instr}
    (h : compileArgs (e :: rest) = some is) :
    ∃ restCode eCode, compileArgs rest = some restCode ∧
      compileExpr e = some eCode ∧ is = restCode ++ eCode := by
  simp only [compileArgs] at h
  cases hr : compileArgs rest with
  | none => rw [hr] at h; simp at h
  | some restCode =>
    rw [hr] at h
    cases he : compileExpr e with
    | none => rw [he] at h; simp at h
    | some eCode =>
      rw [he] at h
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      exact ⟨restCode, eCode, rfl, rfl, h.symm⟩

private theorem compileExpr_builtin_inv {op : Op}
    {args : List (YulSemantics.Expr Op)} {is : List Instr}
    (h : compileExpr (.builtin op args) = some is) :
    ∃ argCode o, compileArgs args = some argCode ∧ opTable op = some o ∧
      is = argCode ++ [.op o] := by
  simp only [compileExpr] at h
  cases ha : compileArgs args with
  | none => rw [ha] at h; simp at h
  | some argCode =>
    rw [ha] at h
    cases ho : opTable op with
    | none => rw [ho] at h; simp at h
    | some o =>
      rw [ho] at h
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      exact ⟨argCode, o, rfl, rfl, h.symm⟩

private theorem compileStmts_cons_inv {st : YulSemantics.Stmt Op}
    {rest : List (YulSemantics.Stmt Op)} {is : List Instr}
    (h : compileStmts (st :: rest) = some is) :
    ∃ sCode restCode, compileStmt st = some sCode ∧
      compileStmts rest = some restCode ∧ is = sCode ++ restCode := by
  simp only [compileStmts] at h
  cases hs : compileStmt st with
  | none => rw [hs] at h; simp at h
  | some sCode =>
    rw [hs] at h
    cases hr : compileStmts rest with
    | none => rw [hr] at h; simp at h
    | some restCode =>
      rw [hr] at h
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      exact ⟨sCode, restCode, rfl, rfl, h.symm⟩

/-! ### The simulation induction -/

/-- The induction motive: what a source derivation for each syntactic class
means on the target, conditional on the compiler accepting the syntax. -/
def Motive (yst : EvmState) :
    YulSemantics.Code Op → YulSemantics.Res yul → Prop
  | .expr e, .eres (.vals vs yst') =>
      ∀ is, compileExpr e = some is → SimOk yst is [] vs yst'
  | .expr e, .eres (.halt yst') =>
      ∀ is, compileExpr e = some is → SimHalt yst is [] yst'
  | .args es, .eres (.vals vs yst') =>
      ∀ is, compileArgs es = some is → SimOk yst is [] vs yst'
  | .args es, .eres (.halt yst') =>
      ∀ is, compileArgs es = some is → SimHalt yst is [] yst'
  | .stmt st, .sres _ yst' o =>
      ∀ is, compileStmt st = some is →
        (o = .normal ∧ SimOk yst is [] [] yst') ∨
        (o = .halt ∧ SimHalt yst is [] yst')
  | .stmts ss, .sres _ yst' o =>
      ∀ is, compileStmts ss = some is →
        (o = .normal ∧ SimOk yst is [] [] yst') ∨
        (o = .halt ∧ SimHalt yst is [] yst')
  | _, _ => True

/-- Every source derivation over compiled syntax is simulated by the target. -/
theorem sim {funs : YulSemantics.FunEnv yul} {V : YulSemantics.VEnv yul}
    {yst : EvmState} {c : YulSemantics.Code Op} {res : YulSemantics.Res yul}
    (h : YulSemantics.Step yul funs V yst c res) : Motive yst c res := by
  induction h with
  | lit =>
    intro is hc
    simp only [compileExpr, Option.some.injEq] at hc
    subst hc
    exact simOk_push _
  | var _ =>
    intro is hc
    simp [compileExpr] at hc
  | builtinOk hargs hb ihargs =>
    intro is hc
    obtain ⟨argCode, o, harg, hopt, rfl⟩ := compileExpr_builtin_inv hc
    exact (ihargs argCode harg).comp (simOk_op hopt hb)
  | builtinHalt hargs hb ihargs =>
    intro is hc
    obtain ⟨argCode, o, harg, hopt, rfl⟩ := compileExpr_builtin_inv hc
    exact (ihargs argCode harg).compHalt (simHalt_op hopt hb)
  | builtinArgsHalt hargs ihargs =>
    intro is hc
    obtain ⟨argCode, o, harg, hopt, rfl⟩ := compileExpr_builtin_inv hc
    exact (ihargs argCode harg).extend [.op o]
  | callOk _ _ _ _ _ _ _ =>
    intro is hc
    simp [compileExpr] at hc
  | callHalt _ _ _ _ _ _ =>
    intro is hc
    simp [compileExpr] at hc
  | callArgsHalt _ _ =>
    intro is hc
    simp [compileExpr] at hc
  | argsNil =>
    intro is hc
    simp only [compileArgs, Option.some.injEq] at hc
    subst hc
    exact SimOk.nil
  | argsCons hrest hhead ihrest ihhead =>
    intro is hc
    obtain ⟨restCode, eCode, hr, he, rfl⟩ := compileArgs_cons_inv hc
    exact (ihrest restCode hr).comp ((ihhead eCode he).frame _)
  | argsRestHalt hrest ihrest =>
    intro is hc
    obtain ⟨restCode, eCode, hr, he, rfl⟩ := compileArgs_cons_inv hc
    exact (ihrest restCode hr).extend eCode
  | argsHeadHalt hrest hhead ihrest ihhead =>
    intro is hc
    obtain ⟨restCode, eCode, hr, he, rfl⟩ := compileArgs_cons_inv hc
    exact (ihrest restCode hr).compHalt ((ihhead eCode he).frame _)
  | funDef =>
    intro is hc
    simp [compileStmt] at hc
  | block _ _ =>
    intro is hc
    simp [compileStmt] at hc
  | letZero =>
    intro is hc
    simp [compileStmt] at hc
  | letVal _ _ _ =>
    intro is hc
    simp [compileStmt] at hc
  | letHalt _ _ =>
    intro is hc
    simp [compileStmt] at hc
  | assignVal _ _ _ =>
    intro is hc
    simp [compileStmt] at hc
  | assignHalt _ _ =>
    intro is hc
    simp [compileStmt] at hc
  | exprStmt hexp ihexp =>
    intro is hc
    simp only [compileStmt] at hc
    exact Or.inl ⟨rfl, ihexp is hc⟩
  | exprStmtHalt hexp ihexp =>
    intro is hc
    simp only [compileStmt] at hc
    exact Or.inr ⟨rfl, ihexp is hc⟩
  | ifTrue _ _ _ _ _ =>
    intro is hc
    simp [compileStmt] at hc
  | ifFalse _ _ _ =>
    intro is hc
    simp [compileStmt] at hc
  | ifHalt _ _ =>
    intro is hc
    simp [compileStmt] at hc
  | switchExec _ _ _ _ =>
    intro is hc
    simp [compileStmt] at hc
  | switchHalt _ _ =>
    intro is hc
    simp [compileStmt] at hc
  | forLoop _ _ _ _ =>
    intro is hc
    simp [compileStmt] at hc
  | forInitHalt _ _ =>
    intro is hc
    simp [compileStmt] at hc
  | «break» =>
    intro is hc
    simp [compileStmt] at hc
  | «continue» =>
    intro is hc
    simp [compileStmt] at hc
  | leave =>
    intro is hc
    simp [compileStmt] at hc
  | seqNil =>
    intro is hc
    simp only [compileStmts, Option.some.injEq] at hc
    subst hc
    exact Or.inl ⟨rfl, SimOk.nil⟩
  | seqCons hs hrest ihs ihrest =>
    intro is hc
    obtain ⟨sCode, restCode, h1, h2, rfl⟩ := compileStmts_cons_inv hc
    rcases ihs sCode h1 with ⟨_, hok1⟩ | ⟨hcontra, _⟩
    · rcases ihrest restCode h2 with ⟨ho, hok2⟩ | ⟨ho, hh2⟩
      · exact Or.inl ⟨ho, hok1.comp hok2⟩
      · exact Or.inr ⟨ho, hok1.compHalt hh2⟩
    · exact absurd hcontra (by simp)
  | seqStop hs hne ihs =>
    intro is hc
    obtain ⟨sCode, restCode, h1, h2, rfl⟩ := compileStmts_cons_inv hc
    rcases ihs sCode h1 with ⟨ho, _⟩ | ⟨ho, hh⟩
    · exact absurd ho hne
    · exact Or.inr ⟨ho, hh.extend restCode⟩
  | loopDone _ _ => trivial
  | loopCondHalt _ => trivial
  | loopStep _ _ _ _ _ _ _ _ _ _ => trivial
  | loopPostHalt _ _ _ _ _ _ _ _ => trivial
  | loopBreak _ _ _ _ _ => trivial
  | loopLeave _ _ _ _ _ => trivial
  | loopBodyHalt _ _ _ _ _ => trivial

/-! ### The main theorem -/

/-- **Compiler correctness** (straight-line fragment). If the compiler accepts
`prog` and the Yul big-step semantics runs `prog` from `st₀` to `st'` with
outcome `o`, then there is a gas bound `b` such that from *every* initial EVM
state that matches `st₀`, executes the assembled bytecode, and holds at least
`b` gas, the EVM semantics reaches a matching final state:

* `o = .normal` — the code runs off its end (implicit `STOP`) and halts with
  `.Success`, in a state whose memory/storage/transient storage match `st'`;
* `o = .halt` — the code halts exactly as `st'.halted` records
  (`stop ↦ Success`, `return ↦ Returned` + payload, `revert ↦ Reverted` +
  payload, `invalid ↦ InvalidInstruction`), again with matching state. -/
theorem compile_correct {prog : YulSemantics.Block Op} {is : List Instr}
    (hcomp : compileProgram prog = some is)
    {yst0 : EvmState} {V' : YulSemantics.VEnv yul} {yst' : EvmState}
    {o : Outcome}
    (hrun : YulSemantics.Run yul prog yst0 V' yst' o) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (assemble is) s0 → StateMatch yst0 s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst' s' ∧
        ((o = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (o = .halt ∧ HaltedMatch yst' s')) := by
  cases hrun with
  | block hbody =>
    have hsim := sim hbody is hcomp
    have hassemble : assemble is = mkCode ([] ++ assembleBytes is ++ []) := by
      show ByteArray.mk _ = ByteArray.mk _
      congr 1
      simp
    rcases hsim with ⟨ho, hok⟩ | ⟨ho, hh⟩
    · subst ho
      obtain ⟨b, H⟩ := hok
      refine ⟨b, ?_⟩
      intro s0 hf hm hpc hstk hgas
      obtain ⟨s1, hsteps, hf1, hm1, hpc1, hstk1, hg1⟩ :=
        H (assemble is) [] [] [] s0 hassemble hf hm (by simpa using hpc)
          (by simpa using hstk) hgas
      obtain ⟨s2, hstep2, hm2, hcs2, hhalt2, hret2⟩ :=
        stopStep (is := is) hf1 hm1 rfl (by simpa using hpc1)
      exact ⟨s2, hsteps.snoc hstep2, hcs2, hm2, Or.inl ⟨rfl, hhalt2, hret2⟩⟩
    · subst ho
      obtain ⟨b, H⟩ := hh
      refine ⟨b, ?_⟩
      intro s0 hf hm hpc hstk hgas
      obtain ⟨s', hsteps, hm', hcs', hhm⟩ :=
        H (assemble is) [] [] [] s0 hassemble hf hm (by simpa using hpc)
          (by simpa using hstk) hgas
      exact ⟨s', hsteps, hcs', hm', Or.inr ⟨rfl, hhm⟩⟩

/-- Result-level corollary: the compiled bytecode `Eval`s to the
`ExecutionResult` the Yul outcome corresponds to (`.success` for a program
that falls through; `resultOf` of the recorded halt otherwise). -/
theorem compile_correct_eval {prog : YulSemantics.Block Op} {is : List Instr}
    (hcomp : compileProgram prog = some is)
    {yst0 : EvmState} {V' : YulSemantics.VEnv yul} {yst' : EvmState}
    {o : Outcome}
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
