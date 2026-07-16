import YulEvmCompiler.StateRel
import YulSemantics.BigStep

/-!
# YulEvmCompiler.OpStep

The single-instruction simulation step: executing one compiled instruction
(a `PUSH32` or one supported built-in's opcode) from a matching state takes
one target `Step` to a matching state.

The file provides:
* word/pc arithmetic helpers (`toNat_ofNat_of_lt`, `ofNat_add_ofNat`);
* the per-op gas bound `opBound` and the lemmas capping every dynamic cost;
* decode-at-layout lemmas lifted to `State.decoded`;
* `OkStep`/`HaltStep`, the two conclusion shapes;
* `opStep` — the main per-built-in case analysis — and `pushStepU`.
-/

namespace YulEvmCompiler

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM (U256 EvmState Op stepOp)

/-- The Yul EVM dialect the compiler is proved against. -/
abbrev yul : YulSemantics.Dialect := YulSemantics.EVM.evm

/-! ### Word arithmetic -/

theorem toNat_ofNat_of_lt {n : Nat} (h : n < 2 ^ 256) :
    (UInt256.ofNat n).toNat = n := by
  simpa [UInt256.ofNat, UInt256.toNat, Fin.ofNat, UInt256.size] using
    Nat.mod_eq_of_lt h

theorem ofNat_add_ofNat {a b : Nat} (h : a + b < 2 ^ 256) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := by
  show UInt256.add _ _ = _
  unfold UInt256.add UInt256.ofNat
  congr 1
  apply Fin.ext
  show ((a % _) + (b % _)) % _ = (a + b) % _
  rw [Nat.mod_eq_of_lt (a := a) (by simp [UInt256.size]; omega),
      Nat.mod_eq_of_lt (a := b) (by simp [UInt256.size]; omega)]

theorem succ_ofNat {n : Nat} (h : n + 1 < 2 ^ 256) :
    (UInt256.ofNat n).succ = UInt256.ofNat (n + 1) := by
  show UInt256.ofNat n + UInt256.ofNat 1 = _
  exact ofNat_add_ofNat h

/-- The target state has halted the way the Yul state records. -/
def HaltedMatch (yst : EvmState) (s : State) : Prop :=
  ∃ hk, yst.halted = some hk ∧ HaltMatch hk s

/-! ### Gas bounds

Each supported op consumes at most `opBound op args` gas: a generous `40000`
covers every static schedule (worst case: `SSTORE`'s `20000 + 2100` cold-write
plus its EIP-2200 2300-stipend sentry headroom, or `EXP`'s `10 + 50·32`), and
the memory-touching ops add the full memory cost of their touched range, which
depends only on the argument values — never on the target state. -/

/-- Memory cost of the range `[p, p+n)` counted from an empty memory: an upper
bound for the expansion delta from *any* current activity level. -/
def memBound (p n : Nat) : Nat :=
  MachineState.memCost (MachineState.activeWordsAfter 0 p n)

private theorem nat_max_eq (a b : Nat) : Nat.max a b = max a b := rfl

theorem memExpansionDelta_le_memBound (curr p n : Nat) :
    MachineState.memExpansionDelta curr p n ≤ memBound p n := by
  unfold MachineState.memExpansionDelta memBound MachineState.activeWordsAfter
  dsimp only
  split
  · simp
  · simp only [nat_max_eq]
    rw [Nat.max_eq_right (Nat.zero_le ((p + n - 1) / 32 + 1))]
    rcases Nat.le_total curr ((p + n - 1) / 32 + 1) with hle | hle
    · rw [Nat.max_eq_right hle]
      exact Nat.sub_le _ _
    · rw [Nat.max_eq_left hle]
      simp

private theorem activeWordsAfter_ge (curr p n : Nat) :
    curr ≤ MachineState.activeWordsAfter curr p n := by
  unfold MachineState.activeWordsAfter
  split
  · exact le_rfl
  · exact Nat.le_max_left _ _

private theorem memCost_mono {a b : Nat} (h : a ≤ b) :
    MachineState.memCost a ≤ MachineState.memCost b := by
  unfold MachineState.memCost
  have hmul : 3 * a ≤ 3 * b := Nat.mul_le_mul_left 3 h
  have hpow : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left h 2
  have hdiv : a ^ 2 / 512 ≤ b ^ 2 / 512 := Nat.div_le_div_right hpow
  omega

/-- Expanding for two memory ranges costs no more than expanding from empty
memory for each range separately. This state-independent cap is used by
`MCOPY`, whose source and destination both affect the active-memory bound. -/
theorem memExpansionDelta2_le_memBounds (curr p₁ n₁ p₂ n₂ : Nat) :
    MachineState.memExpansionDelta2 curr p₁ n₁ p₂ n₂ ≤
      memBound p₁ n₁ + memBound p₂ n₂ := by
  let mid := MachineState.activeWordsAfter curr p₁ n₁
  let final := MachineState.activeWordsAfter mid p₂ n₂
  have hcurr : MachineState.memCost curr ≤ MachineState.memCost mid :=
    memCost_mono (activeWordsAfter_ge curr p₁ n₁)
  have hmid : MachineState.memCost mid ≤ MachineState.memCost final :=
    memCost_mono (activeWordsAfter_ge mid p₂ n₂)
  have h₁ := memExpansionDelta_le_memBound curr p₁ n₁
  have h₂ := memExpansionDelta_le_memBound mid p₂ n₂
  change MachineState.memCost final - MachineState.memCost curr ≤ _
  change MachineState.memCost mid - MachineState.memCost curr ≤ memBound p₁ n₁ at h₁
  change MachineState.memCost final - MachineState.memCost mid ≤ memBound p₂ n₂ at h₂
  omega

/-- Worst-case gas consumed by the single instruction compiled for `op` on
argument values `args`. -/
def opBound (op : Op) (args : List U256) : Nat :=
  40000 +
    match op, args with
    | .mload, [p] => memBound p.toNat 32
    | .mstore, [p, _] => memBound p.toNat 32
    | .mstore8, [p, _] => memBound p.toNat 1
    | .keccak256, [p, n] =>
        memBound p.toNat n.toNat + 6 * ((n.toNat + 31) / 32)
    | .mcopy, [d, s, n] =>
        memBound d.toNat n.toNat + memBound s.toNat n.toNat
          + 3 * ((n.toNat + 31) / 32)
    | .calldatacopy, [d, _, n] =>
        memBound d.toNat n.toNat + 3 * ((n.toNat + 31) / 32)
    | .returndatacopy, [d, _, n] =>
        memBound d.toNat n.toNat + 3 * ((n.toNat + 31) / 32)
    | .extcodecopy, [_, d, _, n] =>
        memBound d.toNat n.toNat + 3 * ((n.toNat + 31) / 32)
    | .log0, [p, n] => memBound p.toNat n.toNat + 8 * n.toNat
    | .log1, [p, n, _] => memBound p.toNat n.toNat + 8 * n.toNat
    | .log2, [p, n, _, _] => memBound p.toNat n.toNat + 8 * n.toNat
    | .log3, [p, n, _, _, _] => memBound p.toNat n.toNat + 8 * n.toNat
    | .log4, [p, n, _, _, _, _] => memBound p.toNat n.toNat + 8 * n.toNat
    | .ret, [p, n] => memBound p.toNat n.toNat
    | .revert, [p, n] => memBound p.toNat n.toNat
    | .codecopy, [d, _, n] => memBound d.toNat n.toNat + 3 * ((n.toNat + 31) / 32)
    | .datacopy, [d, _, n] => memBound d.toNat n.toNat + 3 * ((n.toNat + 31) / 32)
    | _, _ => 0

theorem le_opBound (op : Op) (args : List U256) : 40000 ≤ opBound op args :=
  Nat.le_add_right _ _

theorem expByteCost_le (f : Fork) (b : UInt256) : Gas.expByteCost f b ≤ 1600 := by
  unfold Gas.expByteCost
  split
  · omega
  · next h =>
    have hlog : Nat.log2 b.toNat < 256 := by
      have hlt : b.toNat < 2 ^ 256 := b.val.isLt
      have := Nat.log2_lt (n := b.toNat) h |>.mpr hlt
      exact this
    have : Nat.log2 b.toNat / 8 + 1 ≤ 32 := by omega
    have hper : (if f ≥ .SpuriousDragon then 50 else 10) ≤ 50 := by split <;> omega
    calc (if f ≥ .SpuriousDragon then 50 else 10) * (Nat.log2 b.toNat / 8 + 1)
        ≤ 50 * 32 := Nat.mul_le_mul hper this
      _ ≤ 1600 := by omega

theorem sstoreCost_le (f : Fork) (o c n : UInt256) :
    Gas.sstoreCost f o c n ≤ 20000 := by
  unfold Gas.sstoreCost
  repeat' split <;> try omega

/-! ### Decoding at a layout position -/

theorem decoded_op {code : ByteArray} {s : State} {pre post : List UInt8}
    {o : Operation}
    (hf : FrameOK code s)
    (hcode : code = mkCode (pre ++ (Instr.op o).bytes ++ post))
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hb : EVM.Decode.opcodeOf (Instr.opByte o) = some o) (hp : plainOp o)
    (havail : o.availableInFork .Osaka = true) :
    s.decodedOp = some o := by
  have hsz : code.size = pre.length + 1 + post.length := by
    subst hcode; simp [Instr.bytes]; omega
  have hlen : pre.length < 2 ^ 256 := by
    have := hf.codeSmall; omega
  have hdec : s.decoded = some (o, none) := by
    unfold State.decoded
    rw [hf.hcode, hpc, toNat_ofNat_of_lt hlen, hcode, decodeAt_op pre post o hb hp]
    have hfork : s.fork = .Osaka := hf.fork
    simp [Option.bind, hfork, havail]
  exact State.decoded_to_op hdec

theorem decoded_push {code : ByteArray} {s : State} {pre post : List UInt8}
    {v : UInt256}
    (hf : FrameOK code s)
    (hcode : code = mkCode (pre ++ (Instr.push v).bytes ++ post))
    (hpc : s.pc = UInt256.ofNat pre.length) :
    s.decoded = some (.Push ⟨32, by decide⟩, some (v, 32)) := by
  have hsz : code.size = pre.length + 33 + post.length := by
    subst hcode; simp [Instr.bytes]; omega
  have hlen : pre.length < 2 ^ 256 := by
    have := hf.codeSmall; omega
  unfold State.decoded
  rw [hf.hcode, hpc, toNat_ofNat_of_lt hlen, hcode, decodeAt_push pre post v]
  have hfork : s.fork = .Osaka := hf.fork
  simp [Option.bind, hfork]
  decide

/-! ### The two conclusion shapes -/

/-- A successful single-`Step` from `s`: matching state, pc advanced past the
instruction (starting at `preLen`, `width` bytes wide), `rets` pushed over
`σ`, and at most `bound` gas consumed. -/
def OkStep (code : ByteArray) (s : State) (bound : Nat) (rets : List U256)
    (yst' : EvmState) (preLen width : Nat) (σ : List UInt256) : Prop :=
  ∃ s', EVM.Step s s' ∧ FrameOK code s' ∧ StateMatch yst' s'
    ∧ s'.pc = UInt256.ofNat (preLen + width)
    ∧ s'.stack = rets.map conv ++ σ
    ∧ s.gasAvailable - bound ≤ s'.gasAvailable

/-- A halting single-`Step` from `s`: matching (halted) states. -/
def HaltStep (s : State) (yst' : EvmState) : Prop :=
  ∃ s', EVM.Step s s' ∧ StateMatch yst' s' ∧ s'.callStack = []
    ∧ HaltedMatch yst' s'

theorem OkStep.weaken {code s bound bound' rets yst' preLen width σ}
    (h : OkStep code s bound rets yst' preLen width σ) (hb : bound ≤ bound') :
    OkStep code s bound' rets yst' preLen width σ := by
  obtain ⟨s', h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨s', h1, h2, h3, h4, h5, le_trans (Nat.sub_le_sub_left hb _) h6⟩

/-! ### Auxiliary cost caps -/

theorem sloadCold_le (s : State) (k : UInt256) : Gas.sloadColdSurcharge s k ≤ 2000 := by
  unfold Gas.sloadColdSurcharge
  split <;> omega

theorem sstoreCold_le (s : State) (k : UInt256) : Gas.sstoreColdSurcharge s k ≤ 2100 := by
  unfold Gas.sstoreColdSurcharge
  split <;> omega

theorem accountCold_le (s : State) (a : AccountAddress) :
    Gas.accountColdSurcharge s a ≤ 2500 := by
  unfold Gas.accountColdSurcharge
  split <;> omega

theorem selfDestructSurcharge_le (f : Fork) (beneficiaryEmpty selfHasBalance : Bool) :
    Gas.selfDestructSurcharge f beneficiaryEmpty selfHasBalance ≤ 25000 := by
  by_cases hspurious : f ≥ .SpuriousDragon
  · cases beneficiaryEmpty <;> cases selfHasBalance <;>
      simp [Gas.selfDestructSurcharge, hspurious]
  · by_cases htangerine : f ≥ .TangerineWhistle
    · cases beneficiaryEmpty <;>
        simp [Gas.selfDestructSurcharge, hspurious, htangerine]
    · simp [Gas.selfDestructSurcharge, hspurious, htangerine]

theorem selfDestructColdSurcharge_le (s : State) (beneficiary : AccountAddress) :
    Gas.selfDestructColdSurcharge s beneficiary ≤ 2600 := by
  unfold Gas.selfDestructColdSurcharge
  split <;> omega

/-! ### The `PUSH32` step -/

/-- Executing an embedded `PUSH32 u` for an arbitrary target word `u` (e.g.
a resolved label address): pushes `u`, advances the pc by 33. -/
theorem pushStepU {code : ByteArray} {pre post : List UInt8} {u : UInt256}
    {yst : EvmState} {σ : List UInt256} {s : State}
    (hcode : code = mkCode (pre ++ (Instr.push u).bytes ++ post))
    (hf : FrameOK code s) (hm : StateMatch yst s)
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hstk : s.stack = σ)
    (hgas : 40000 ≤ s.gasAvailable) :
    ∃ s', EVM.Step s s' ∧ FrameOK code s' ∧ StateMatch yst s'
      ∧ s'.pc = UInt256.ofNat (pre.length + 33)
      ∧ s'.stack = u :: σ
      ∧ s.gasAvailable - 40000 ≤ s'.gasAvailable := by
  have hsz : code.size = pre.length + 33 + post.length := by
    subst hcode; simp [Instr.bytes]; omega
  have hdec := decoded_push hf hcode hpc
  have hfork : s.fork = .Osaka := hf.fork
  have hgas' : Gas.baseCost s.fork (.Push ⟨(32 : Fin 33), by decide⟩) ≤ s.gasAvailable := by
    rw [hfork]
    have : Gas.baseCost .Osaka (.Push ⟨(32 : Fin 33), by decide⟩) ≤ 40000 := by decide
    omega
  refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
    (StepRunning.pushN s ⟨32, by decide⟩ u 32 (by decide) hdec hgas'),
    ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
      hf.running⟩,
    ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen,
        hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, ?_, ?_⟩
  · show s.pc + UInt256.ofNat (32 + 1) = _
    rw [hpc, ofNat_add_ofNat (by have := hf.codeSmall; omega)]
  · show u :: s.stack = u :: σ
    rw [hstk]
  · show s.gasAvailable - Gas.baseCost s.fork (.Push ⟨(32 : Fin 33), by decide⟩)
      ≥ s.gasAvailable - 40000
    apply Nat.sub_le_sub_left
    rw [hfork]
    decide

/-! ### The implicit `STOP` at the end of the code -/

/-- Falling off the end of the bytecode halts with `.Success` (implicit
`STOP`); this is the target-side meaning of a Yul `.normal` outcome. -/
theorem stopStep {code : ByteArray} {yst : EvmState} {s : State}
    (hf : FrameOK code s) (hm : StateMatch yst s)
    (hcodes : code = mkCode (assembleBytes is))
    (hpc : s.pc = UInt256.ofNat (assembleBytes is).length) :
    ∃ s', EVM.Step s s' ∧ StateMatch yst s' ∧ s'.callStack = []
      ∧ s'.halt = .Success ∧ s'.hReturn = .empty := by
  have hlen : (assembleBytes is).length < 2 ^ 256 := by
    have := hf.codeSmall
    rw [hcodes] at this
    simpa using this
  have hdec : s.decodedOp = some .STOP := by
    apply State.decoded_to_op (imm := none)
    unfold State.decoded
    rw [hf.hcode, hpc, toNat_ofNat_of_lt hlen, hcodes,
      decodeAt_past_end _ _ (by simp)]
    have hfork : s.fork = .Osaka := hf.fork
    simp [Option.bind, hfork]
    decide
  exact ⟨_, EVM.Step.running hf.running hf.noPrecompile (StepRunning.stop s hdec),
    ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, hf.callStack, rfl, rfl⟩

/-! ### Variable-access steps: `DUPn`, `SWAPn`, `POP` -/

private theorem dup_base_le (n : Fin 16) :
    Gas.baseCost .Osaka (.Dup ⟨n⟩) ≤ 40000 := by
  revert n; decide

private theorem swap_base_le (n : Fin 16) :
    Gas.baseCost .Osaka (.Swap ⟨n⟩) ≤ 40000 := by
  revert n; decide

/-- Executing an embedded `DUP(n+1)` duplicates `stack[n]` onto the top. -/
theorem dupStep {code : ByteArray} {pre post : List UInt8} {n : Fin 16}
    {v : UInt256} {yst : EvmState} {s : State}
    (hcode : code = mkCode (pre ++ (Instr.op (.Dup ⟨n⟩)).bytes ++ post))
    (hf : FrameOK code s) (hm : StateMatch yst s)
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hget : s.stack[n.val]? = some v)
    (hgas : 40000 ≤ s.gasAvailable) :
    ∃ s', EVM.Step s s' ∧ FrameOK code s' ∧ StateMatch yst s'
      ∧ s'.pc = UInt256.ofNat (pre.length + 1)
      ∧ s'.stack = v :: s.stack
      ∧ s.gasAvailable - 40000 ≤ s'.gasAvailable := by
  obtain ⟨hb, hplain, havail⟩ := dup_roundtrip n
  have hdec := decoded_op hf hcode hpc hb hplain havail
  have hfork : s.fork = .Osaka := hf.fork
  have hgas' : Gas.baseCost s.fork (.Dup ⟨n⟩) ≤ s.gasAvailable := by
    rw [hfork]
    have := dup_base_le n
    omega
  refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
    (StepRunning.dup s n v hdec hgas' hget),
    ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
      hf.running⟩,
    ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, rfl, ?_⟩
  · show s.pc.succ = _
    rw [hpc]; apply succ_ofNat
    have hsz : code.size = pre.length + 1 + post.length := by
      subst hcode; simp [Instr.bytes]; omega
    have := hf.codeSmall; omega
  · show s.gasAvailable - Gas.baseCost s.fork (.Dup ⟨n⟩) ≥ s.gasAvailable - 40000
    apply Nat.sub_le_sub_left
    rw [hfork]
    exact dup_base_le n

/-- Executing an embedded `SWAP(n+1)` exchanges the top with `stack[n+1]`. -/
theorem swapStep {code : ByteArray} {pre post : List UInt8} {n : Fin 16}
    {stk' : List UInt256} {yst : EvmState} {s : State}
    (hcode : code = mkCode (pre ++ (Instr.op (.Swap ⟨n⟩)).bytes ++ post))
    (hf : FrameOK code s) (hm : StateMatch yst s)
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hswap : s.stack.exchange 0 (n.val + 1) = some stk')
    (hgas : 40000 ≤ s.gasAvailable) :
    ∃ s', EVM.Step s s' ∧ FrameOK code s' ∧ StateMatch yst s'
      ∧ s'.pc = UInt256.ofNat (pre.length + 1)
      ∧ s'.stack = stk'
      ∧ s.gasAvailable - 40000 ≤ s'.gasAvailable := by
  obtain ⟨hb, hplain, havail⟩ := swap_roundtrip n
  have hdec := decoded_op hf hcode hpc hb hplain havail
  have hfork : s.fork = .Osaka := hf.fork
  have hgas' : Gas.baseCost s.fork (.Swap ⟨n⟩) ≤ s.gasAvailable := by
    rw [hfork]
    have := swap_base_le n
    omega
  refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
    (StepRunning.swap s n stk' hdec hgas' hswap),
    ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
      hf.running⟩,
    ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, rfl, ?_⟩
  · show s.pc.succ = _
    rw [hpc]; apply succ_ofNat
    have hsz : code.size = pre.length + 1 + post.length := by
      subst hcode; simp [Instr.bytes]; omega
    have := hf.codeSmall; omega
  · show s.gasAvailable - Gas.baseCost s.fork (.Swap ⟨n⟩) ≥ s.gasAvailable - 40000
    apply Nat.sub_le_sub_left
    rw [hfork]
    exact swap_base_le n

/-- Executing an embedded `POP` drops the top of the stack. -/
theorem popStep {code : ByteArray} {pre post : List UInt8}
    {a : UInt256} {rest : List UInt256} {yst : EvmState} {s : State}
    (hcode : code = mkCode (pre ++ (Instr.op .POP).bytes ++ post))
    (hf : FrameOK code s) (hm : StateMatch yst s)
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hstk : s.stack = a :: rest)
    (hgas : 40000 ≤ s.gasAvailable) :
    ∃ s', EVM.Step s s' ∧ FrameOK code s' ∧ StateMatch yst s'
      ∧ s'.pc = UInt256.ofNat (pre.length + 1)
      ∧ s'.stack = rest
      ∧ s.gasAvailable - 40000 ≤ s'.gasAvailable := by
  obtain ⟨hb, hplain, havail⟩ := pop_roundtrip
  have hdec := decoded_op hf hcode hpc hb hplain havail
  have hfork : s.fork = .Osaka := hf.fork
  have hgas' : Gas.baseCost s.fork .POP ≤ s.gasAvailable := by
    rw [hfork]
    have : Gas.baseCost .Osaka Operation.POP ≤ 40000 := by decide
    omega
  refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
    (StepRunning.pop s a rest hdec hgas' hstk),
    ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
      hf.running⟩,
    ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, rfl, ?_⟩
  · show s.pc.succ = _
    rw [hpc]; apply succ_ofNat
    have hsz : code.size = pre.length + 1 + post.length := by
      subst hcode; simp [Instr.bytes]; omega
    have := hf.codeSmall; omega
  · show s.gasAvailable - Gas.baseCost s.fork .POP ≥ s.gasAvailable - 40000
    apply Nat.sub_le_sub_left
    rw [hfork]
    decide

/-! ### Generic per-arity helpers for the pure built-ins -/

section PureHelpers

variable {code : ByteArray} {pre post : List UInt8}
variable {yop : Op} {o : Operation}
variable {args : List U256} {yst : EvmState}
variable {r : YulSemantics.BuiltinResult U256 EvmState}
variable {σ : List UInt256} {s : State}

private theorem binPure
    (f : U256 → U256 → U256) (g : UInt256 → UInt256 → UInt256)
    (hyulOp : ∀ args yst, stepOp yop args yst = YulSemantics.EVM.bin f args yst)
    (hfg : ∀ a b, conv (f a b) = g (conv a) (conv b))
    (hop : opTable yop = some o)
    (hbase : Gas.baseCost .Osaka o ≤ 40000)
    (mk : ∀ (s : State) (a b : UInt256) (rest : List UInt256),
        s.decodedOp = some o →
        Gas.baseCost s.fork o ≤ s.gasAvailable →
        s.stack = a :: b :: rest →
        StepRunning s { s with
          stack := g a b :: rest, pc := s.pc.succ,
          gasAvailable := s.gasAvailable - Gas.baseCost s.fork o })
    (hyul : stepOp yop args yst = some r)
    (hcode : code = mkCode (pre ++ (Instr.op o).bytes ++ post))
    (hf : FrameOK code s) (hm : StateMatch yst s)
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hstk : s.stack = args.map conv ++ σ)
    (hgas : 40000 ≤ s.gasAvailable) :
    match r with
    | .ok rets yst' => OkStep code s 40000 rets yst' pre.length 1 σ
    | .halt _ => False := by
  rw [hyulOp] at hyul
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, args⟩⟩⟩ <;>
    simp [YulSemantics.EVM.bin] at hyul
  subst hyul
  show OkStep code s 40000 [f a b] yst pre.length 1 σ
  obtain ⟨hb', hplain⟩ := opTable_roundtrip hop
  have havail := opTable_available hop
  have hdec := decoded_op hf hcode hpc hb' hplain havail
  have hfork : s.fork = .Osaka := hf.fork
  have hstk' : s.stack = conv a :: conv b :: σ := by simpa using hstk
  have hgas' : Gas.baseCost s.fork o ≤ s.gasAvailable := by
    rw [hfork]; omega
  refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
    (mk s (conv a) (conv b) σ hdec hgas' hstk'),
    ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
      hf.running⟩,
    ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, ?_, ?_⟩
  · show s.pc.succ = _
    rw [hpc]
    apply succ_ofNat
    have hsz : code.size = pre.length + 1 + post.length := by
      subst hcode; simp [Instr.bytes]; omega
    have := hf.codeSmall
    omega
  · show g (conv a) (conv b) :: σ = [f a b].map conv ++ σ
    simp [hfg]
  · show s.gasAvailable - Gas.baseCost s.fork o ≥ s.gasAvailable - 40000
    apply Nat.sub_le_sub_left
    rw [hfork]
    exact hbase

private theorem nullaryRead {yv : U256} {sv : UInt256}
    (hop : opTable yop = some o)
    (hbase : Gas.baseCost .Osaka o ≤ 40000)
    (hval : conv yv = sv)
    (hyul : stepOp yop args yst = some r)
    (hstep : stepOp yop args yst = YulSemantics.EVM.rd0 yv args yst)
    (mk : s.decodedOp = some o →
        Gas.baseCost s.fork o ≤ s.gasAvailable →
        StepRunning s { s with
          stack := sv :: s.stack, pc := s.pc.succ,
          gasAvailable := s.gasAvailable - Gas.baseCost s.fork o })
    (hcode : code = mkCode (pre ++ (Instr.op o).bytes ++ post))
    (hf : FrameOK code s) (hm : StateMatch yst s)
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hstk : s.stack = args.map conv ++ σ)
    (hgas : 40000 ≤ s.gasAvailable) :
    match r with
    | .ok rets yst' => OkStep code s 40000 rets yst' pre.length 1 σ
    | .halt _ => False := by
  rw [hstep] at hyul
  rcases args with _ | ⟨a, args⟩ <;> simp [YulSemantics.EVM.rd0] at hyul
  subst hyul
  show OkStep code s 40000 [yv] yst pre.length 1 σ
  obtain ⟨hb', hplain⟩ := opTable_roundtrip hop
  have havail := opTable_available hop
  have hdec := decoded_op hf hcode hpc hb' hplain havail
  have hfork : s.fork = .Osaka := hf.fork
  have hstk0 : s.stack = σ := by simpa using hstk
  have hgas' : Gas.baseCost s.fork o ≤ s.gasAvailable := by rw [hfork]; omega
  refine ⟨_, EVM.Step.running hf.running hf.noPrecompile (mk hdec hgas'),
    ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
      hf.running⟩,
    ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, ?_, ?_⟩
  · show s.pc.succ = _
    rw [hpc]; apply succ_ofNat
    have hsz : code.size = pre.length + 1 + post.length := by
      subst hcode; simp [Instr.bytes]; omega
    have := hf.codeSmall; omega
  · show sv :: s.stack = [yv].map conv ++ σ
    rw [hstk0, ← hval]; rfl
  · show s.gasAvailable - Gas.baseCost s.fork o ≥ s.gasAvailable - 40000
    apply Nat.sub_le_sub_left
    rw [hfork]; exact hbase

private theorem unPure
    (f : U256 → U256) (g : UInt256 → UInt256)
    (hyulOp : ∀ args yst, stepOp yop args yst = YulSemantics.EVM.un f args yst)
    (hfg : ∀ a, conv (f a) = g (conv a))
    (hop : opTable yop = some o)
    (hbase : Gas.baseCost .Osaka o ≤ 40000)
    (mk : ∀ (s : State) (a : UInt256) (rest : List UInt256),
        s.decodedOp = some o →
        Gas.baseCost s.fork o ≤ s.gasAvailable →
        s.stack = a :: rest →
        StepRunning s { s with
          stack := g a :: rest, pc := s.pc.succ,
          gasAvailable := s.gasAvailable - Gas.baseCost s.fork o })
    (hyul : stepOp yop args yst = some r)
    (hcode : code = mkCode (pre ++ (Instr.op o).bytes ++ post))
    (hf : FrameOK code s) (hm : StateMatch yst s)
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hstk : s.stack = args.map conv ++ σ)
    (hgas : 40000 ≤ s.gasAvailable) :
    match r with
    | .ok rets yst' => OkStep code s 40000 rets yst' pre.length 1 σ
    | .halt _ => False := by
  rw [hyulOp] at hyul
  rcases args with _ | ⟨a, _ | ⟨b, args⟩⟩ <;>
    simp [YulSemantics.EVM.un] at hyul
  subst hyul
  show OkStep code s 40000 [f a] yst pre.length 1 σ
  obtain ⟨hb', hplain⟩ := opTable_roundtrip hop
  have havail := opTable_available hop
  have hdec := decoded_op hf hcode hpc hb' hplain havail
  have hfork : s.fork = .Osaka := hf.fork
  have hstk' : s.stack = conv a :: σ := by simpa using hstk
  have hgas' : Gas.baseCost s.fork o ≤ s.gasAvailable := by
    rw [hfork]; omega
  refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
    (mk s (conv a) σ hdec hgas' hstk'),
    ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
      hf.running⟩,
    ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, ?_, ?_⟩
  · show s.pc.succ = _
    rw [hpc]
    apply succ_ofNat
    have hsz : code.size = pre.length + 1 + post.length := by
      subst hcode; simp [Instr.bytes]; omega
    have := hf.codeSmall
    omega
  · show g (conv a) :: σ = [f a].map conv ++ σ
    simp [hfg]
  · show s.gasAvailable - Gas.baseCost s.fork o ≥ s.gasAvailable - 40000
    apply Nat.sub_le_sub_left
    rw [hfork]
    exact hbase

private theorem terPure
    (f : U256 → U256 → U256 → U256) (g : UInt256 → UInt256 → UInt256 → UInt256)
    (hyulOp : ∀ args yst, stepOp yop args yst = YulSemantics.EVM.ter f args yst)
    (hfg : ∀ a b c, conv (f a b c) = g (conv a) (conv b) (conv c))
    (hop : opTable yop = some o)
    (hbase : Gas.baseCost .Osaka o ≤ 40000)
    (mk : ∀ (s : State) (a b c : UInt256) (rest : List UInt256),
        s.decodedOp = some o →
        Gas.baseCost s.fork o ≤ s.gasAvailable →
        s.stack = a :: b :: c :: rest →
        StepRunning s { s with
          stack := g a b c :: rest, pc := s.pc.succ,
          gasAvailable := s.gasAvailable - Gas.baseCost s.fork o })
    (hyul : stepOp yop args yst = some r)
    (hcode : code = mkCode (pre ++ (Instr.op o).bytes ++ post))
    (hf : FrameOK code s) (hm : StateMatch yst s)
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hstk : s.stack = args.map conv ++ σ)
    (hgas : 40000 ≤ s.gasAvailable) :
    match r with
    | .ok rets yst' => OkStep code s 40000 rets yst' pre.length 1 σ
    | .halt _ => False := by
  rw [hyulOp] at hyul
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, args⟩⟩⟩⟩ <;>
    simp [YulSemantics.EVM.ter] at hyul
  subst hyul
  show OkStep code s 40000 [f a b c] yst pre.length 1 σ
  obtain ⟨hb', hplain⟩ := opTable_roundtrip hop
  have havail := opTable_available hop
  have hdec := decoded_op hf hcode hpc hb' hplain havail
  have hfork : s.fork = .Osaka := hf.fork
  have hstk' : s.stack = conv a :: conv b :: conv c :: σ := by simpa using hstk
  have hgas' : Gas.baseCost s.fork o ≤ s.gasAvailable := by
    rw [hfork]; omega
  refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
    (mk s (conv a) (conv b) (conv c) σ hdec hgas' hstk'),
    ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
      hf.running⟩,
    ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, ?_, ?_⟩
  · show s.pc.succ = _
    rw [hpc]
    apply succ_ofNat
    have hsz : code.size = pre.length + 1 + post.length := by
      subst hcode; simp [Instr.bytes]; omega
    have := hf.codeSmall
    omega
  · show g (conv a) (conv b) (conv c) :: σ = [f a b c].map conv ++ σ
    simp [hfg]
  · show s.gasAvailable - Gas.baseCost s.fork o ≥ s.gasAvailable - 40000
    apply Nat.sub_le_sub_left
    rw [hfork]
    exact hbase

end PureHelpers

/-! ### Event-log helper -/

/-- Shared simulation proof for `LOG0`–`LOG4`. The topic count is carried by
the target opcode's `Fin 5`; the five source built-ins instantiate this lemma
after their exact arities have been checked. -/
private theorem logStep {yop : Op} {topicCount : Fin 5}
    {p n : U256} {topics : List U256}
    (hop : opTable yop = some (.Log ⟨topicCount⟩))
    (htopics : topics.length = topicCount.val)
    (hbound : opBound yop (p :: n :: topics) =
      40000 + (memBound p.toNat n.toNat + 8 * n.toNat))
    {code : ByteArray} {pre post : List UInt8} {yst : EvmState}
    {σ : List UInt256} {s : State}
    (hcode : code = mkCode (pre ++ (Instr.op (.Log ⟨topicCount⟩)).bytes ++ post))
    (hf : FrameOK code s) (hm : StateMatch yst s)
    (hperm : s.executionEnv.permitStateMutation = true)
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hstk : s.stack = (p :: n :: topics).map conv ++ σ)
    (hgas : opBound yop (p :: n :: topics) ≤ s.gasAvailable) :
    OkStep code s (opBound yop (p :: n :: topics)) []
      (YulSemantics.EVM.appendLog yst topics p n) pre.length 1 σ := by
  obtain ⟨hb, hplain⟩ := opTable_roundtrip hop
  have hdec := decoded_op hf hcode hpc hb hplain (opTable_available hop)
  have hstk' : s.stack = conv p :: conv n :: topics.map conv ++ σ := by
    simpa only [List.map_cons] using hstk
  have hmem := memExpansionDelta_le_memBound s.activeWords.toNat p.toNat n.toNat
  have hbase : Gas.baseCost s.executionEnv.fork (.Log ⟨topicCount⟩) ≤ 40000 := by
    rw [hf.fork]
    change 375 * (topicCount.val + 1) ≤ 40000
    omega
  have hcost : Gas.logTotal s topicCount (conv p) (conv n)
      ≤ opBound yop (p :: n :: topics) := by
    rw [hbound]
    unfold Gas.logTotal Gas.logDataCost
    rw [conv_toNat p, conv_toNat n]
    omega
  have hgas' : Gas.logTotal s topicCount (conv p) (conv n) ≤ s.gasAvailable :=
    le_trans hcost hgas
  refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
    (StepRunning.log s topicCount (conv p) (conv n) (topics.map conv) σ
      hdec hperm (by simpa using htopics) hstk' hgas'),
    ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
      hf.running⟩, ?_, ?_, rfl, ?_⟩
  · constructor
    · exact hm.mem
    · exact hm.stor
    · exact hm.tstor
    · exact hm.cd
    · exact hm.env
    · exact hm.codeBytes
    · exact hm.codeLen
    · exact hm.selfBalance
    · exact hm.balanceOf
    · change conv (YulSemantics.EVM.touchMemory yst p.toNat n.toNat).activeWords = _
      simpa only [conv_toNat] using
        activeWordsAfter_eq hm.activeWords p.toNat n.toNat
    · exact hm.retData
    · exact hm.retDataLen
    · exact hm.externalCode
    · apply LogsMatch.append hm.logs
      refine ⟨hm.env.address, ?_, hm.mem.readBytes p.toNat n.toNat⟩
      simp
    · exact hm.selfdestructs
    · exact hm.createdThisTx
  · show s.pc.succ = _
    rw [hpc]
    apply succ_ofNat
    have hsz : code.size = pre.length + 1 + post.length := by
      subst hcode
      simp [Instr.bytes]
      omega
    have := hf.codeSmall
    omega
  · exact Nat.sub_le_sub_left hcost s.gasAvailable

/-! ### The per-built-in step -/

/-- The local, terminal `SELFDESTRUCT` simulation. This theorem is deliberately established
before the opcode is admitted to `opTable`: the table's verified domain only grows after the
world-state, gas, and halt correspondence all check. -/
theorem selfdestructStep {code : ByteArray} {pre post : List UInt8}
    {beneficiary : U256} {yst : EvmState} {σ : List UInt256} {s : State}
    (hcode : code = mkCode (pre ++ (Instr.op .SELFDESTRUCT).bytes ++ post))
    (hf : FrameOK code s) (hm : StateMatch yst s)
    (hperm : s.executionEnv.permitStateMutation = true)
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hstk : s.stack = [beneficiary].map conv ++ σ)
    (hgas : 40000 ≤ s.gasAvailable) :
    HaltStep s (YulSemantics.EVM.finishSelfdestruct yst beneficiary) := by
  have hdec : s.decodedOp = some .SELFDESTRUCT :=
    decoded_op hf hcode hpc (by decide) (by simp [plainOp]) (by decide)
  have hstk' : s.stack = conv beneficiary :: σ := by simpa using hstk
  have hbase : Gas.baseCost s.executionEnv.fork .SELFDESTRUCT ≤ 5000 := by
    rw [hf.fork]
    decide
  have hsurcharge := selfDestructSurcharge_le s.executionEnv.fork
    ((s.accountMap (AccountAddress.ofUInt256 (conv beneficiary))).isEmpty)
    ((s.accountMap s.executionEnv.address).balance.toNat != 0)
  have hcold := selfDestructColdSurcharge_le s
    (AccountAddress.ofUInt256 (conv beneficiary))
  have hgas' : Gas.selfDestructTotal s (conv beneficiary) ≤ s.gasAvailable := by
    unfold Gas.selfDestructTotal
    omega
  let sGas : State :=
    { s with gasAvailable := s.gasAvailable - Gas.selfDestructTotal s (conv beneficiary) }
  have hmGas : StateMatch yst sGas := by
    exact ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
      hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen,
      hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩
  have hm' := hmGas.finishSelfdestruct beneficiary
  refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
    (StepRunning.selfDestruct s (conv beneficiary) σ hdec hstk' hperm hgas'),
    hm', ?_, ?_⟩
  · simpa [sGas, State.selfDestructTo] using hf.callStack
  · refine ⟨(.selfdestruct, []), ?_, ?_⟩
    · simp [YulSemantics.EVM.finishSelfdestruct]
    · simp [HaltMatch, State.selfDestructTo]

/-- Package a target step that halts with `StaticModeViolation` (leaving all
state fields untouched) into a `HaltStep` matching the source's
`.staticViolation`. The source side only sets `halted` and the target gate
halts before mutating, so the `StateMatch` carries over unchanged. -/
theorem staticHaltStepGen {s : State} {yst : EvmState} (hm : StateMatch yst s)
    (hcs : s.callStack = [])
    (hstep : EVM.Step s { s with halt := .Exception .StaticModeViolation }) :
    HaltStep s { yst with halted := some (.staticViolation, []) } :=
  ⟨_, hstep,
    ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
      hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen,
      hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩,
    hcs, (.staticViolation, []), rfl, rfl⟩

/-- A state-modifying built-in attempted in a static target frame
(`permitStateMutation = false`) halts the frame with `StaticModeViolation`,
matching the source's `.staticViolation`. Used by the local guarded ops
(`sstore`/`tstore`/`log`/`selfdestruct`), all of which are `isStateMutating`
and so fire the target's generic static gate. Neither side mutates world
state: the source's `guardStatic` only sets `halted`, and the target gate
halts before writing. -/
theorem staticViolationStep {yop : Op} {o : Operation} (hop : opTable yop = some o)
    {code : ByteArray} {pre post : List UInt8} {s : State} {yst : EvmState}
    (hcode : code = mkCode (pre ++ (Instr.op o).bytes ++ post))
    (hf : FrameOK code s) (hm : StateMatch yst s)
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hmut : o.isStateMutating = true)
    (hperm : s.executionEnv.permitStateMutation = false) :
    HaltStep s { yst with halted := some (.staticViolation, []) } := by
  obtain ⟨hb, hplain⟩ := opTable_roundtrip hop
  have hdec := decoded_op hf hcode hpc hb hplain (opTable_available hop)
  exact staticHaltStepGen hm hf.callStack
    (EVM.Step.running hf.running hf.noPrecompile
      (StepRunning.staticModeViolation s o hdec hmut hperm))

set_option maxHeartbeats 1600000 in
open YulSemantics.EVM in
/-- Executing the single compiled instruction of a supported built-in from a
matching state: one target `Step` to a matching state (with `rets` replacing
the consumed arguments on the stack), or a matching halt. -/
theorem opStep {yop : Op} {o : Operation} (hop : opTable yop = some o)
    {args : List U256} {yst : EvmState}
    {r : YulSemantics.BuiltinResult U256 EvmState}
    (hyul : stepOp yop args yst = some r)
    {code : ByteArray} {pre post : List UInt8} {σ : List UInt256} {s : State}
    (hcode : code = mkCode (pre ++ (Instr.op o).bytes ++ post))
    (hf : FrameOK code s) (hm : StateMatch yst s)
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hstk : s.stack = args.map conv ++ σ)
    (hgas : opBound yop args ≤ s.gasAvailable) :
    match r with
    | .ok rets yst' => OkStep code s (opBound yop args) rets yst' pre.length 1 σ
    | .halt yst' => HaltStep s yst' := by
  have hgas40 : 40000 ≤ s.gasAvailable := le_trans (le_opBound yop args) hgas
  have hfork : s.fork = .Osaka := hf.fork
  -- common decode facts (only usable once `o` is concrete, but stated here
  -- for the bespoke cases)
  cases yop <;> simp only [opTable, Option.some.injEq, reduceCtorEq] at hop <;>
    subst hop
  case add =>
    cases r with
    | ok rets yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_add rfl (by decide)
        (fun s a b rest h1 h2 h3 => .add s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_add rfl (by decide)
        (fun s a b rest h1 h2 h3 => .add s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case sub =>
    cases r with
    | ok rets yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_sub rfl (by decide)
        (fun s a b rest h1 h2 h3 => .sub s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_sub rfl (by decide)
        (fun s a b rest h1 h2 h3 => .sub s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case mul =>
    cases r with
    | ok rets yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_mul rfl (by decide)
        (fun s a b rest h1 h2 h3 => .mul s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_mul rfl (by decide)
        (fun s a b rest h1 h2 h3 => .mul s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case div =>
    cases r with
    | ok rets yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_div rfl (by decide)
        (fun s a b rest h1 h2 h3 => .div s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_div rfl (by decide)
        (fun s a b rest h1 h2 h3 => .div s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case sdiv =>
    cases r with
    | ok rets yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_sdiv rfl (by decide)
        (fun s a b rest h1 h2 h3 => .sdiv s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_sdiv rfl (by decide)
        (fun s a b rest h1 h2 h3 => .sdiv s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case mod =>
    cases r with
    | ok rets yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_mod rfl (by decide)
        (fun s a b rest h1 h2 h3 => .mod s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_mod rfl (by decide)
        (fun s a b rest h1 h2 h3 => .mod s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case smod =>
    cases r with
    | ok rets yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_smod rfl (by decide)
        (fun s a b rest h1 h2 h3 => .smod s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_smod rfl (by decide)
        (fun s a b rest h1 h2 h3 => .smod s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case addmod =>
    cases r with
    | ok rets yst' =>
      exact (terPure _ _ (fun _ _ => rfl) conv_addmod rfl (by decide)
        (fun s a b c rest h1 h2 h3 => .addmod s a b c rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (terPure _ _ (fun _ _ => rfl) conv_addmod rfl (by decide)
        (fun s a b c rest h1 h2 h3 => .addmod s a b c rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case mulmod =>
    cases r with
    | ok rets yst' =>
      exact (terPure _ _ (fun _ _ => rfl) conv_mulmod rfl (by decide)
        (fun s a b c rest h1 h2 h3 => .mulmod s a b c rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (terPure _ _ (fun _ _ => rfl) conv_mulmod rfl (by decide)
        (fun s a b c rest h1 h2 h3 => .mulmod s a b c rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case signextend =>
    cases r with
    | ok rets yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_signextend rfl (by decide)
        (fun s a b rest h1 h2 h3 => .signextend s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_signextend rfl (by decide)
        (fun s a b rest h1 h2 h3 => .signextend s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case clz =>
    cases r with
    | ok rets yst' =>
      exact (unPure _ _ (fun _ _ => rfl) conv_clz rfl (by decide)
        (fun s a rest h1 h2 h3 => .clz s a rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (unPure _ _ (fun _ _ => rfl) conv_clz rfl (by decide)
        (fun s a rest h1 h2 h3 => .clz s a rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case lt =>
    cases r with
    | ok rets yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_lt rfl (by decide)
        (fun s a b rest h1 h2 h3 => .lt s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_lt rfl (by decide)
        (fun s a b rest h1 h2 h3 => .lt s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case gt =>
    cases r with
    | ok rets yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_gt rfl (by decide)
        (fun s a b rest h1 h2 h3 => .gt s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_gt rfl (by decide)
        (fun s a b rest h1 h2 h3 => .gt s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case slt =>
    cases r with
    | ok rets yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_slt rfl (by decide)
        (fun s a b rest h1 h2 h3 => .slt s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_slt rfl (by decide)
        (fun s a b rest h1 h2 h3 => .slt s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case sgt =>
    cases r with
    | ok rets yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_sgt rfl (by decide)
        (fun s a b rest h1 h2 h3 => .sgt s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_sgt rfl (by decide)
        (fun s a b rest h1 h2 h3 => .sgt s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case eq =>
    cases r with
    | ok rets yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_eq rfl (by decide)
        (fun s a b rest h1 h2 h3 => .eq s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_eq rfl (by decide)
        (fun s a b rest h1 h2 h3 => .eq s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case iszero =>
    cases r with
    | ok rets yst' =>
      exact (unPure _ _ (fun _ _ => rfl) conv_iszero rfl (by decide)
        (fun s a rest h1 h2 h3 => .iszero s a rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (unPure _ _ (fun _ _ => rfl) conv_iszero rfl (by decide)
        (fun s a rest h1 h2 h3 => .iszero s a rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case and =>
    cases r with
    | ok rets yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_and rfl (by decide)
        (fun s a b rest h1 h2 h3 => .and s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_and rfl (by decide)
        (fun s a b rest h1 h2 h3 => .and s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case or =>
    cases r with
    | ok rets yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_or rfl (by decide)
        (fun s a b rest h1 h2 h3 => .or s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_or rfl (by decide)
        (fun s a b rest h1 h2 h3 => .or s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case xor =>
    cases r with
    | ok rets yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_xor rfl (by decide)
        (fun s a b rest h1 h2 h3 => .xor_ s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_xor rfl (by decide)
        (fun s a b rest h1 h2 h3 => .xor_ s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case not =>
    cases r with
    | ok rets yst' =>
      exact (unPure _ _ (fun _ _ => rfl) conv_not rfl (by decide)
        (fun s a rest h1 h2 h3 => .not s a rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (unPure _ _ (fun _ _ => rfl) conv_not rfl (by decide)
        (fun s a rest h1 h2 h3 => .not s a rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case byte =>
    cases r with
    | ok rets yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_byte rfl (by decide)
        (fun s a b rest h1 h2 h3 => .byte_ s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_byte rfl (by decide)
        (fun s a b rest h1 h2 h3 => .byte_ s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case shl =>
    cases r with
    | ok rets yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_shl rfl (by decide)
        (fun s a b rest h1 h2 h3 => .shl s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_shl rfl (by decide)
        (fun s a b rest h1 h2 h3 => .shl s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case shr =>
    cases r with
    | ok rets yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_shr rfl (by decide)
        (fun s a b rest h1 h2 h3 => .shr s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_shr rfl (by decide)
        (fun s a b rest h1 h2 h3 => .shr s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case sar =>
    cases r with
    | ok rets yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_sar rfl (by decide)
        (fun s a b rest h1 h2 h3 => .sar s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (binPure _ _ (fun _ _ => rfl) conv_sar rfl (by decide)
        (fun s a b rest h1 h2 h3 => .sar s a b rest h1 h2 h3)
        hyul hcode hf hm hpc hstk hgas40).elim
  case exp =>
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, args⟩⟩⟩ <;>
      simp only [stepOp, YulSemantics.EVM.bin, Option.some.injEq,
        reduceCtorEq] at hyul
    subst hyul
    show OkStep code s (opBound .exp [a, b])
      [BitVec.ofNat 256 (a.toNat ^ b.toNat)] yst pre.length 1 σ
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .exp) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain (opTable_available (yop := .exp) rfl)
    have hstk' : s.stack = conv a :: conv b :: σ := by simpa using hstk
    have hbyte := expByteCost_le s.fork (conv b)
    have hb10 : Gas.baseCost s.fork .EXP ≤ 10 := by rw [hfork]; decide
    have hgas' : Gas.baseCost s.fork .EXP + Gas.expByteCost s.fork (conv b)
        ≤ s.gasAvailable := by omega
    refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
      (StepRunning.exp s (conv a) (conv b) σ hdec hgas' hstk'),
      ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
        hf.running⟩,
      ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, ?_, ?_⟩
    · show s.pc.succ = _
      rw [hpc]; apply succ_ofNat
      have hsz : code.size = pre.length + 1 + post.length := by
        subst hcode; simp [Instr.bytes]; omega
      have := hf.codeSmall; omega
    · show UInt256.exp (conv a) (conv b) :: σ = _
      simp [← conv_exp]
    · show s.gasAvailable - Gas.baseCost s.fork .EXP - Gas.expByteCost s.fork (conv b)
        ≥ s.gasAvailable - opBound .exp [a, b]
      have h3 : opBound Op.exp [a, b] = 40000 := rfl
      omega
  case keccak256 =>
    rcases args with _ | ⟨p, _ | ⟨n, _ | ⟨c, args⟩⟩⟩ <;> simp [stepOp] at hyul
    subst hyul
    show OkStep code s (opBound .keccak256 [p, n])
      [yst.env.keccakOf (YulSemantics.EVM.readBytes yst.memory p.toNat n.toNat)]
      (YulSemantics.EVM.touchMemory yst p.toNat n.toNat) pre.length 1 σ
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .keccak256) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain
      (opTable_available (yop := .keccak256) rfl)
    have hstk' : s.stack = conv p :: conv n :: σ := by simpa using hstk
    have h3 : opBound Op.keccak256 [p, n] =
        40000 + (memBound p.toNat n.toNat + 6 * ((n.toNat + 31) / 32)) := rfl
    have h4 : Gas.keccakWordCost (conv n) = 6 * ((n.toNat + 31) / 32) := by
      unfold Gas.keccakWordCost
      rw [conv_toNat]
    have h1 : Gas.baseCost s.executionEnv.fork Operation.KECCAK256 ≤ 30 := by
      rw [hf.fork]
      decide
    have h2 := memExpansionDelta_le_memBound s.activeWords.toNat
      (conv p).toNat (conv n).toNat
    rw [conv_toNat p, conv_toNat n] at h2
    have hgas' : Gas.keccakTotal s (conv p) (conv n) ≤ s.gasAvailable := by
      unfold Gas.keccakTotal
      rw [conv_toNat p, conv_toNat n, h4]
      omega
    refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
      (StepRunning.keccak256 s (conv p) (conv n) σ hdec hstk' hgas'),
      ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
        hf.running⟩,
      ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, ?_, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩,
      ?_, ?_, ?_⟩
    · simpa only [conv_toNat] using activeWordsAfter_eq hm.activeWords p.toNat n.toNat
    · show s.pc.succ = _
      rw [hpc]
      apply succ_ofNat
      have hsz : code.size = pre.length + 1 + post.length := by
        subst hcode
        simp [Instr.bytes]
        omega
      have := hf.codeSmall
      omega
    · have hhash := hm.env.keccak
          (YulSemantics.EVM.readBytes yst.memory p.toNat n.toNat)
      rw [hm.mem.readBytes p.toNat n.toNat, mkCode_toList] at hhash
      rw [hm.mem.readBytes p.toNat n.toNat]
      simpa using hhash.symm
    · show s.gasAvailable - Gas.keccakTotal s (conv p) (conv n)
        ≥ s.gasAvailable - opBound .keccak256 [p, n]
      unfold Gas.keccakTotal
      rw [conv_toNat p, conv_toNat n, h4, h3]
      omega
  case pop =>
    rcases args with _ | ⟨a, _ | ⟨b, args⟩⟩ <;> simp [stepOp] at hyul
    subst hyul
    show OkStep code s (opBound .pop [a]) [] yst pre.length 1 σ
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .pop) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain (opTable_available (yop := .pop) rfl)
    have hstk' : s.stack = conv a :: σ := by simpa using hstk
    have hgas' : Gas.baseCost s.fork .POP ≤ s.gasAvailable := by
      rw [hfork]
      have : Gas.baseCost .Osaka Operation.POP ≤ 40000 := by decide
      omega
    refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
      (StepRunning.pop s (conv a) σ hdec hgas' hstk'),
      ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
        hf.running⟩,
      ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, rfl, ?_⟩
    · show s.pc.succ = _
      rw [hpc]; apply succ_ofNat
      have hsz : code.size = pre.length + 1 + post.length := by
        subst hcode; simp [Instr.bytes]; omega
      have := hf.codeSmall; omega
    · show s.gasAvailable - Gas.baseCost s.fork .POP ≥ s.gasAvailable - opBound .pop [a]
      have h3 : opBound Op.pop [a] = 40000 := rfl
      have : Gas.baseCost s.fork .POP ≤ 40000 := by rw [hfork]; decide
      omega
  case mload =>
    rcases args with _ | ⟨p, _ | ⟨b, args⟩⟩ <;> simp [stepOp] at hyul
    subst hyul
    show OkStep code s (opBound .mload [p])
      [YulSemantics.EVM.loadWord yst.memory p.toNat]
      (YulSemantics.EVM.touchMemory yst p.toNat 32) pre.length 1 σ
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .mload) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain
      (opTable_available (yop := .mload) rfl)
    have hstk' : s.stack = conv p :: σ := by simpa using hstk
    have h3 : opBound Op.mload [p] = 40000 + memBound (conv p).toNat 32 := rfl
    have hgas' : Gas.mloadTotal s (conv p) ≤ s.gasAvailable := by
      unfold Gas.mloadTotal
      have h1 : Gas.baseCost s.executionEnv.fork Operation.MLOAD ≤ 3 := by
        rw [hf.fork]; decide
      have h2 := memExpansionDelta_le_memBound s.activeWords.toNat (conv p).toNat 32
      omega
    refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
      (StepRunning.mload s (conv p) σ hdec hstk' hgas'),
      ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
        hf.running⟩,
      ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, ?_, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, ?_, ?_⟩
    · simpa only [conv_toNat] using activeWordsAfter_eq hm.activeWords p.toNat 32
    · show s.pc.succ = _
      rw [hpc]; apply succ_ofNat
      have hsz : code.size = pre.length + 1 + post.length := by
        subst hcode; simp [Instr.bytes]; omega
      have := hf.codeSmall; omega
    · show MachineState.readWord s.memory p.toNat :: σ = _
      simp [← hm.mem.loadWord p.toNat]
    · show s.gasAvailable - Gas.mloadTotal s (conv p)
        ≥ s.gasAvailable - opBound .mload [p]
      have h1 : Gas.baseCost s.executionEnv.fork Operation.MLOAD ≤ 3 := by
        rw [hf.fork]; decide
      have h2 := memExpansionDelta_le_memBound s.activeWords.toNat (conv p).toNat 32
      unfold Gas.mloadTotal
      omega
  case mstore =>
    rcases args with _ | ⟨p, _ | ⟨v, _ | ⟨c, args⟩⟩⟩ <;> simp [stepOp] at hyul
    subst hyul
    show OkStep code s (opBound .mstore [p, v]) []
      { YulSemantics.EVM.touchMemory yst p.toNat 32 with
        memory := YulSemantics.EVM.storeWord yst.memory p.toNat v }
      pre.length 1 σ
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .mstore) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain
      (opTable_available (yop := .mstore) rfl)
    have hstk' : s.stack = conv p :: conv v :: σ := by simpa using hstk
    have hgas' : Gas.mstoreTotal s (conv p) ≤ s.gasAvailable := by
      unfold Gas.mstoreTotal
      have h1 : Gas.baseCost s.executionEnv.fork Operation.MSTORE ≤ 3 := by
        rw [hf.fork]; decide
      have h2 := memExpansionDelta_le_memBound s.activeWords.toNat (conv p).toNat 32
      have h3 : opBound Op.mstore [p, v] = 40000 + memBound (conv p).toNat 32 := rfl
      omega
    refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
      (StepRunning.mstore s (conv p) (conv v) σ hdec hstk' hgas'),
      ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
        hf.running⟩,
      ⟨?_, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, ?_, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, rfl, ?_⟩
    · show MemMatch (YulSemantics.EVM.storeWord yst.memory p.toNat v)
        (MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded (conv v).toNat 32) (conv p).toNat)
      rw [show (conv p).toNat = p.toNat from conv_toNat p]
      exact hm.mem.storeWord p.toNat v
    · simpa only [conv_toNat] using activeWordsAfter_eq hm.activeWords p.toNat 32
    · show s.pc.succ = _
      rw [hpc]; apply succ_ofNat
      have hsz : code.size = pre.length + 1 + post.length := by
        subst hcode; simp [Instr.bytes]; omega
      have := hf.codeSmall; omega
    · show s.gasAvailable - Gas.mstoreTotal s (conv p)
        ≥ s.gasAvailable - opBound .mstore [p, v]
      have h1 : Gas.baseCost s.executionEnv.fork Operation.MSTORE ≤ 3 := by
        rw [hf.fork]; decide
      have h2 := memExpansionDelta_le_memBound s.activeWords.toNat (conv p).toNat 32
      have h3 : opBound Op.mstore [p, v] = 40000 + memBound (conv p).toNat 32 := rfl
      unfold Gas.mstoreTotal
      omega
  case mstore8 =>
    rcases args with _ | ⟨p, _ | ⟨v, _ | ⟨c, args⟩⟩⟩ <;> simp [stepOp] at hyul
    subst hyul
    show OkStep code s (opBound .mstore8 [p, v]) []
      { YulSemantics.EVM.touchMemory yst p.toNat 1 with
        memory := YulSemantics.EVM.storeByte yst.memory p.toNat v }
      pre.length 1 σ
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .mstore8) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain
      (opTable_available (yop := .mstore8) rfl)
    have hstk' : s.stack = conv p :: conv v :: σ := by simpa using hstk
    have hgas' : Gas.mstore8Total s (conv p) ≤ s.gasAvailable := by
      unfold Gas.mstore8Total
      have h1 : Gas.baseCost s.executionEnv.fork Operation.MSTORE8 ≤ 3 := by
        rw [hf.fork]; decide
      have h2 := memExpansionDelta_le_memBound s.activeWords.toNat (conv p).toNat 1
      have h3 : opBound Op.mstore8 [p, v] = 40000 + memBound (conv p).toNat 1 := rfl
      omega
    refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
      (StepRunning.mstore8 s (conv p) (conv v) σ hdec hstk' hgas'),
      ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
        hf.running⟩,
      ⟨?_, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, ?_, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, rfl, ?_⟩
    · show MemMatch (YulSemantics.EVM.storeByte yst.memory p.toNat v)
        (MachineState.writeBytes s.memory
          (ByteArray.mk #[UInt8.ofNat ((conv v).toNat % 256)]) (conv p).toNat)
      rw [show (conv p).toNat = p.toNat from conv_toNat p]
      exact hm.mem.storeByte p.toNat v
    · simpa only [conv_toNat] using activeWordsAfter_eq hm.activeWords p.toNat 1
    · show s.pc.succ = _
      rw [hpc]; apply succ_ofNat
      have hsz : code.size = pre.length + 1 + post.length := by
        subst hcode; simp [Instr.bytes]; omega
      have := hf.codeSmall; omega
    · show s.gasAvailable - Gas.mstore8Total s (conv p)
        ≥ s.gasAvailable - opBound .mstore8 [p, v]
      have h1 : Gas.baseCost s.executionEnv.fork Operation.MSTORE8 ≤ 3 := by
        rw [hf.fork]; decide
      have h2 := memExpansionDelta_le_memBound s.activeWords.toNat (conv p).toNat 1
      have h3 : opBound Op.mstore8 [p, v] = 40000 + memBound (conv p).toNat 1 := rfl
      unfold Gas.mstore8Total
      omega
  case mcopy =>
    rcases args with _ | ⟨d, _ | ⟨src, _ | ⟨n, _ | ⟨e, args⟩⟩⟩⟩ <;>
      simp [stepOp] at hyul
    subst hyul
    show OkStep code s (opBound .mcopy [d, src, n]) []
      { YulSemantics.EVM.touchMemory2 yst d.toNat n.toNat src.toNat n.toNat with
        memory :=
          YulSemantics.EVM.copyWithin yst.memory d.toNat src.toNat n.toNat }
      pre.length 1 σ
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .mcopy) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain
      (opTable_available (yop := .mcopy) rfl)
    have hstk' : s.stack = conv d :: conv src :: conv n :: σ := by simpa using hstk
    have h3 : opBound Op.mcopy [d, src, n] =
        40000 + (memBound d.toNat n.toNat + memBound src.toNat n.toNat
          + 3 * ((n.toNat + 31) / 32)) := rfl
    have h4 : Gas.copyWordCost (conv n) = 3 * ((n.toNat + 31) / 32) := by
      unfold Gas.copyWordCost; rw [conv_toNat]
    have h1 : Gas.baseCost s.executionEnv.fork Operation.MCOPY ≤ 3 := by
      rw [hf.fork]; decide
    have h2 := memExpansionDelta2_le_memBounds s.activeWords.toNat
      (conv d).toNat (conv n).toNat (conv src).toNat (conv n).toNat
    rw [conv_toNat d, conv_toNat src, conv_toNat n] at h2
    have hgas' : Gas.mcopyTotal s (conv d) (conv src) (conv n) ≤ s.gasAvailable := by
      unfold Gas.mcopyTotal
      rw [conv_toNat d, conv_toNat src, conv_toNat n, h4]
      omega
    refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
      (StepRunning.mcopy s (conv d) (conv src) (conv n) σ hdec hstk' hgas'),
      ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
        hf.running⟩,
      ⟨?_, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, ?_, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, rfl, ?_⟩
    · show MemMatch
        (YulSemantics.EVM.copyWithin yst.memory d.toNat src.toNat n.toNat)
        (MachineState.writeBytes s.memory
          (MachineState.readPadded s.memory (conv src).toNat (conv n).toNat)
            (conv d).toNat)
      rw [conv_toNat d, conv_toNat src, conv_toNat n]
      exact hm.mem.copyWithin d.toNat src.toNat n.toNat
    · simpa only [conv_toNat] using activeWordsAfter2_eq hm.activeWords
        d.toNat n.toNat src.toNat n.toNat d.isLt n.isLt
    · show s.pc.succ = _
      rw [hpc]; apply succ_ofNat
      have hsz : code.size = pre.length + 1 + post.length := by
        subst hcode; simp [Instr.bytes]; omega
      have := hf.codeSmall; omega
    · show s.gasAvailable - Gas.mcopyTotal s (conv d) (conv src) (conv n)
        ≥ s.gasAvailable - opBound .mcopy [d, src, n]
      unfold Gas.mcopyTotal
      rw [conv_toNat d, conv_toNat src, conv_toNat n, h4, h3]
      omega
  case msize =>
    have hval := memorySize_eq hm.activeWords
    cases r with
    | ok rets yst' =>
      exact (nullaryRead rfl (by decide) hval hyul rfl
        (fun h1 h2 => .msize s h1 h2)
        hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (nullaryRead rfl (by decide) hval hyul rfl
        (fun h1 h2 => .msize s h1 h2)
        hcode hf hm hpc hstk hgas40).elim
  case calldataload =>
    rcases args with _ | ⟨p, _ | ⟨b, args⟩⟩ <;> simp [stepOp, YulSemantics.EVM.rd1] at hyul
    subst hyul
    show OkStep code s (opBound .calldataload [p])
      [YulSemantics.EVM.wordFrom yst.env.calldata p.toNat] yst pre.length 1 σ
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .calldataload) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain
      (opTable_available (yop := .calldataload) rfl)
    have hstk' : s.stack = conv p :: σ := by simpa using hstk
    have hgas' : Gas.baseCost s.fork .CALLDATALOAD ≤ s.gasAvailable := by
      rw [hfork]
      have : Gas.baseCost .Osaka Operation.CALLDATALOAD ≤ 40000 := by decide
      omega
    refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
      (StepRunning.calldataload s (conv p) σ hdec hgas' hstk'),
      ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
        hf.running⟩,
      ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, ?_, ?_⟩
    · show s.pc.succ = _
      rw [hpc]; apply succ_ofNat
      have hsz : code.size = pre.length + 1 + post.length := by
        subst hcode; simp [Instr.bytes]; omega
      have := hf.codeSmall; omega
    · show MachineState.readWord s.executionEnv.calldata (conv p).toNat :: σ
        = [YulSemantics.EVM.wordFrom yst.env.calldata p.toNat].map conv ++ σ
      simp only [List.map_cons, List.map_nil, List.singleton_append]
      congr 1
      rw [show (conv p).toNat = p.toNat from conv_toNat p]
      exact (hm.cd.loadWord p.toNat).symm
    · show s.gasAvailable - Gas.baseCost s.fork .CALLDATALOAD
        ≥ s.gasAvailable - opBound .calldataload [p]
      have h3 : opBound Op.calldataload [p] = 40000 := rfl
      have : Gas.baseCost s.fork .CALLDATALOAD ≤ 40000 := by rw [hfork]; decide
      omega
  case calldatasize =>
    have hval : conv (BitVec.ofNat 256 yst.env.calldata.length)
        = UInt256.ofNat s.executionEnv.calldata.size := by
      apply u256ext
      rw [conv_toNat, BitVec.toNat_ofNat, toNat_u256_ofNat, hm.env.calldataLen]
    cases r with
    | ok rets yst' =>
      exact (nullaryRead rfl (by decide) hval hyul rfl
        (fun h1 h2 => .calldatasize s h1 h2)
        hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (nullaryRead rfl (by decide) hval hyul rfl
        (fun h1 h2 => .calldatasize s h1 h2)
        hcode hf hm hpc hstk hgas40).elim
  case calldatacopy =>
    rcases args with _ | ⟨d, _ | ⟨s0, _ | ⟨nn, _ | ⟨e, args⟩⟩⟩⟩ <;> simp [stepOp] at hyul
    subst hyul
    show OkStep code s (opBound .calldatacopy [d, s0, nn]) []
      { YulSemantics.EVM.touchMemory yst d.toNat nn.toNat with memory :=
          (YulSemantics.EVM.copyInto yst.memory d.toNat s0.toNat nn.toNat
            yst.env.calldata) }
      pre.length 1 σ
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .calldatacopy) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain
      (opTable_available (yop := .calldatacopy) rfl)
    have hstk' : s.stack = conv d :: conv s0 :: conv nn :: σ := by simpa using hstk
    have h3 : opBound Op.calldatacopy [d, s0, nn]
        = 40000 + (memBound d.toNat nn.toNat + 3 * ((nn.toNat + 31) / 32)) := rfl
    have h4 : Gas.copyWordCost (conv nn) = 3 * ((nn.toNat + 31) / 32) := by
      unfold Gas.copyWordCost; rw [conv_toNat]
    have h1 : Gas.baseCost s.executionEnv.fork Operation.CALLDATACOPY ≤ 3 := by
      rw [hf.fork]; decide
    have h2 := memExpansionDelta_le_memBound s.activeWords.toNat
      (conv d).toNat (conv nn).toNat
    rw [conv_toNat d, conv_toNat nn] at h2
    have hgas' : Gas.calldatacopyTotal s (conv d) (conv nn) ≤ s.gasAvailable := by
      unfold Gas.calldatacopyTotal
      rw [conv_toNat d, conv_toNat nn, h4]
      omega
    refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
      (StepRunning.calldatacopy s (conv d) (conv s0) (conv nn) σ hdec hstk' hgas'),
      ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
        hf.running⟩,
      ⟨?_, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, ?_, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, rfl, ?_⟩
    · show MemMatch
        (YulSemantics.EVM.copyInto yst.memory d.toNat s0.toNat nn.toNat yst.env.calldata)
        (MachineState.writeBytes s.memory
          (MachineState.readPadded s.executionEnv.calldata
            (conv s0).toNat (conv nn).toNat) (conv d).toNat)
      rw [conv_toNat d, conv_toNat s0, conv_toNat nn]
      exact hm.mem.copyFromBytes hm.cd d.toNat s0.toNat nn.toNat
    · simpa only [conv_toNat] using activeWordsAfter_eq hm.activeWords d.toNat nn.toNat
    · show s.pc.succ = _
      rw [hpc]; apply succ_ofNat
      have hsz : code.size = pre.length + 1 + post.length := by
        subst hcode; simp [Instr.bytes]; omega
      have := hf.codeSmall; omega
    · show s.gasAvailable - Gas.calldatacopyTotal s (conv d) (conv nn)
        ≥ s.gasAvailable - opBound .calldatacopy [d, s0, nn]
      unfold Gas.calldatacopyTotal
      rw [conv_toNat d, conv_toNat nn, h4, h3]
      omega
  case returndatasize =>
    have hval : conv (BitVec.ofNat 256 yst.returndata.length)
        = UInt256.ofNat s.returnData.size := by
      apply u256ext
      rw [conv_toNat, BitVec.toNat_ofNat, toNat_u256_ofNat, hm.retDataLen]
    cases r with
    | ok rets yst' =>
      exact (nullaryRead rfl (by decide) hval hyul rfl
        (fun h1 h2 => .returndatasize s h1 h2)
        hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (nullaryRead rfl (by decide) hval hyul rfl
        (fun h1 h2 => .returndatasize s h1 h2)
        hcode hf hm hpc hstk hgas40).elim
  case returndatacopy =>
    rcases args with _ | ⟨d, _ | ⟨s0, _ | ⟨nn, _ | ⟨e, args⟩⟩⟩⟩ <;>
      simp only [stepOp] at hyul
    all_goals try contradiction
    by_cases hbound : s0.toNat + nn.toNat ≤ yst.returndata.length
    · simp [hbound] at hyul
      subst hyul
      show OkStep code s (opBound .returndatacopy [d, s0, nn]) []
        { YulSemantics.EVM.touchMemory yst d.toNat nn.toNat with memory :=
            (YulSemantics.EVM.copyInto yst.memory d.toNat s0.toNat nn.toNat
              yst.returndata) }
        pre.length 1 σ
      obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .returndatacopy) rfl
      have hdec := decoded_op hf hcode hpc hb' hplain
        (opTable_available (yop := .returndatacopy) rfl)
      have hstk' : s.stack = conv d :: conv s0 :: conv nn :: σ := by simpa using hstk
      have hin : (conv s0).toNat + (conv nn).toNat ≤ s.returnData.size := by
        rw [conv_toNat, conv_toNat, ← hm.retDataLen]
        exact hbound
      have h3 : opBound Op.returndatacopy [d, s0, nn]
          = 40000 + (memBound d.toNat nn.toNat + 3 * ((nn.toNat + 31) / 32)) := rfl
      have h4 : Gas.copyWordCost (conv nn) = 3 * ((nn.toNat + 31) / 32) := by
        unfold Gas.copyWordCost
        rw [conv_toNat]
      have h1 : Gas.baseCost s.executionEnv.fork Operation.RETURNDATACOPY ≤ 3 := by
        rw [hf.fork]
        decide
      have h2 := memExpansionDelta_le_memBound s.activeWords.toNat
        (conv d).toNat (conv nn).toNat
      rw [conv_toNat d, conv_toNat nn] at h2
      have hgas' : Gas.returndatacopyTotal s (conv d) (conv nn) ≤ s.gasAvailable := by
        unfold Gas.returndatacopyTotal
        rw [conv_toNat d, conv_toNat nn, h4]
        omega
      refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
        (StepRunning.returndatacopy s (conv d) (conv s0) (conv nn) σ
          hdec hstk' hin hgas'),
        ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
          hf.running⟩,
        ⟨?_, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
          hm.selfBalance, hm.balanceOf, ?_, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩,
        ?_, rfl, ?_⟩
      · show MemMatch
          (YulSemantics.EVM.copyInto yst.memory d.toNat s0.toNat nn.toNat
            yst.returndata)
          (MachineState.writeBytes s.memory
            (MachineState.readPadded s.returnData
              (conv s0).toNat (conv nn).toNat) (conv d).toNat)
        rw [conv_toNat d, conv_toNat s0, conv_toNat nn]
        exact hm.mem.copyFromBytes hm.retData d.toNat s0.toNat nn.toNat
      · simpa only [conv_toNat] using activeWordsAfter_eq hm.activeWords d.toNat nn.toNat
      · show s.pc.succ = _
        rw [hpc]
        apply succ_ofNat
        have hsz : code.size = pre.length + 1 + post.length := by
          subst hcode
          simp [Instr.bytes]
          omega
        have := hf.codeSmall
        omega
      · show s.gasAvailable - Gas.returndatacopyTotal s (conv d) (conv nn)
          ≥ s.gasAvailable - opBound .returndatacopy [d, s0, nn]
        unfold Gas.returndatacopyTotal
        rw [conv_toNat d, conv_toNat nn, h4, h3]
        omega
    · simp [hbound] at hyul
      subst hyul
      show HaltStep s
        { yst with halted := some (.invalidMemoryAccess, []) }
      obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .returndatacopy) rfl
      have hdec := decoded_op hf hcode hpc hb' hplain
        (opTable_available (yop := .returndatacopy) rfl)
      have hstk' : s.stack = conv d :: conv s0 :: conv nn :: σ := by simpa using hstk
      have hgas' : Gas.baseCost s.fork Operation.RETURNDATACOPY ≤ s.gasAvailable := by
        have hbase : Gas.baseCost s.fork Operation.RETURNDATACOPY ≤ 3 := by
          rw [hfork]
          decide
        omega
      have hoob : (conv s0).toNat + (conv nn).toNat > s.returnData.size := by
        rw [conv_toNat, conv_toNat, ← hm.retDataLen]
        omega
      refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
        (StepRunning.returndatacopyOob s (conv d) (conv s0) (conv nn) σ
          hdec hgas' hstk' hoob), ?_, hf.callStack, ?_⟩
      · exact ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
          hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen,
          hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩
      · exact ⟨(.invalidMemoryAccess, []), rfl, rfl⟩
  case codecopy =>
    rcases args with _ | ⟨d, _ | ⟨s0, _ | ⟨nn, _ | ⟨e, args⟩⟩⟩⟩ <;> simp [stepOp] at hyul
    subst hyul
    show OkStep code s (opBound .codecopy [d, s0, nn]) []
      { YulSemantics.EVM.touchMemory yst d.toNat nn.toNat with memory :=
          (YulSemantics.EVM.copyInto yst.memory d.toNat s0.toNat nn.toNat
            yst.env.code) }
      pre.length 1 σ
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .codecopy) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain (opTable_available (yop := .codecopy) rfl)
    have hstk' : s.stack = conv d :: conv s0 :: conv nn :: σ := by simpa using hstk
    have h3 : opBound Op.codecopy [d, s0, nn]
        = 40000 + (memBound d.toNat nn.toNat + 3 * ((nn.toNat + 31) / 32)) := rfl
    have h4 : Gas.copyWordCost (conv nn) = 3 * ((nn.toNat + 31) / 32) := by
      unfold Gas.copyWordCost; rw [conv_toNat]
    have h1 : Gas.baseCost s.executionEnv.fork Operation.CODECOPY ≤ 3 := by rw [hf.fork]; decide
    have h2 := memExpansionDelta_le_memBound s.activeWords.toNat (conv d).toNat (conv nn).toNat
    rw [conv_toNat d, conv_toNat nn] at h2
    have hgas' : Gas.codecopyTotal s (conv d) (conv nn) ≤ s.gasAvailable := by
      unfold Gas.codecopyTotal; rw [conv_toNat d, conv_toNat nn, h4]; omega
    refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
      (StepRunning.codecopy s (conv d) (conv s0) (conv nn) σ hdec hstk' hgas'),
      ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
        hf.running⟩,
      ⟨?_, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, ?_, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, rfl, ?_⟩
    · show MemMatch (YulSemantics.EVM.copyInto yst.memory d.toNat s0.toNat nn.toNat yst.env.code)
        (MachineState.writeBytes s.memory
          (MachineState.readPadded s.executionEnv.code (conv s0).toNat (conv nn).toNat)
            (conv d).toNat)
      rw [conv_toNat d, conv_toNat s0, conv_toNat nn]
      exact hm.mem.copyFromBytes hm.codeBytes d.toNat s0.toNat nn.toNat
    · simpa only [conv_toNat] using activeWordsAfter_eq hm.activeWords d.toNat nn.toNat
    · show s.pc.succ = _
      rw [hpc]; apply succ_ofNat
      have hsz : code.size = pre.length + 1 + post.length := by
        subst hcode; simp [Instr.bytes]; omega
      have := hf.codeSmall; omega
    · show s.gasAvailable - Gas.codecopyTotal s (conv d) (conv nn)
        ≥ s.gasAvailable - opBound .codecopy [d, s0, nn]
      unfold Gas.codecopyTotal; rw [conv_toNat d, conv_toNat nn, h4, h3]; omega
  case datacopy =>
    rcases args with _ | ⟨d, _ | ⟨s0, _ | ⟨nn, _ | ⟨e, args⟩⟩⟩⟩ <;> simp [stepOp] at hyul
    subst hyul
    show OkStep code s (opBound .datacopy [d, s0, nn]) []
      { YulSemantics.EVM.touchMemory yst d.toNat nn.toNat with memory :=
          (YulSemantics.EVM.copyInto yst.memory d.toNat s0.toNat nn.toNat
            yst.env.code) }
      pre.length 1 σ
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .datacopy) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain (opTable_available (yop := .datacopy) rfl)
    have hstk' : s.stack = conv d :: conv s0 :: conv nn :: σ := by simpa using hstk
    have h3 : opBound Op.datacopy [d, s0, nn]
        = 40000 + (memBound d.toNat nn.toNat + 3 * ((nn.toNat + 31) / 32)) := rfl
    have h4 : Gas.copyWordCost (conv nn) = 3 * ((nn.toNat + 31) / 32) := by
      unfold Gas.copyWordCost; rw [conv_toNat]
    have h1 : Gas.baseCost s.executionEnv.fork Operation.CODECOPY ≤ 3 := by rw [hf.fork]; decide
    have h2 := memExpansionDelta_le_memBound s.activeWords.toNat (conv d).toNat (conv nn).toNat
    rw [conv_toNat d, conv_toNat nn] at h2
    have hgas' : Gas.codecopyTotal s (conv d) (conv nn) ≤ s.gasAvailable := by
      unfold Gas.codecopyTotal; rw [conv_toNat d, conv_toNat nn, h4]; omega
    refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
      (StepRunning.codecopy s (conv d) (conv s0) (conv nn) σ hdec hstk' hgas'),
      ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
        hf.running⟩,
      ⟨?_, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, ?_, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, rfl, ?_⟩
    · show MemMatch (YulSemantics.EVM.copyInto yst.memory d.toNat s0.toNat nn.toNat yst.env.code)
        (MachineState.writeBytes s.memory
          (MachineState.readPadded s.executionEnv.code (conv s0).toNat (conv nn).toNat)
            (conv d).toNat)
      rw [conv_toNat d, conv_toNat s0, conv_toNat nn]
      exact hm.mem.copyFromBytes hm.codeBytes d.toNat s0.toNat nn.toNat
    · simpa only [conv_toNat] using activeWordsAfter_eq hm.activeWords d.toNat nn.toNat
    · show s.pc.succ = _
      rw [hpc]; apply succ_ofNat
      have hsz : code.size = pre.length + 1 + post.length := by
        subst hcode; simp [Instr.bytes]; omega
      have := hf.codeSmall; omega
    · show s.gasAvailable - Gas.codecopyTotal s (conv d) (conv nn)
        ≥ s.gasAvailable - opBound .datacopy [d, s0, nn]
      unfold Gas.codecopyTotal; rw [conv_toNat d, conv_toNat nn, h4, h3]; omega
  case codesize =>
    have hnlt : yst.env.code.length < 2 ^ 256 := by
      rw [hm.codeLen, hf.hcode]; exact hf.codeSmall
    have hval : conv (BitVec.ofNat 256 yst.env.code.length)
        = UInt256.ofNat s.executionEnv.code.size := by
      rw [conv_eq_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnlt, hm.codeLen]
    cases r with
    | ok rets yst' =>
      exact (nullaryRead rfl (by decide) hval hyul rfl
        (fun h1 h2 => .codesize s h1 h2)
        hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (nullaryRead rfl (by decide) hval hyul rfl
        (fun h1 h2 => .codesize s h1 h2)
        hcode hf hm hpc hstk hgas40).elim
  case address =>
    cases r with
    | ok rets yst' =>
      exact (nullaryRead rfl (by decide) hm.env.address hyul rfl
        (fun h1 h2 => .address s h1 h2)
        hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (nullaryRead rfl (by decide) hm.env.address hyul rfl
        (fun h1 h2 => .address s h1 h2)
        hcode hf hm hpc hstk hgas40).elim
  case origin =>
    cases r with
    | ok rets yst' =>
      exact (nullaryRead rfl (by decide) hm.env.origin hyul rfl
        (fun h1 h2 => .origin s h1 h2)
        hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (nullaryRead rfl (by decide) hm.env.origin hyul rfl
        (fun h1 h2 => .origin s h1 h2)
        hcode hf hm hpc hstk hgas40).elim
  case caller =>
    cases r with
    | ok rets yst' =>
      exact (nullaryRead rfl (by decide) hm.env.caller hyul rfl
        (fun h1 h2 => .caller s h1 h2)
        hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (nullaryRead rfl (by decide) hm.env.caller hyul rfl
        (fun h1 h2 => .caller s h1 h2)
        hcode hf hm hpc hstk hgas40).elim
  case callvalue =>
    cases r with
    | ok rets yst' =>
      exact (nullaryRead rfl (by decide) hm.env.callvalue hyul rfl
        (fun h1 h2 => .callvalue s h1 h2)
        hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (nullaryRead rfl (by decide) hm.env.callvalue hyul rfl
        (fun h1 h2 => .callvalue s h1 h2)
        hcode hf hm hpc hstk hgas40).elim
  case gasprice =>
    cases r with
    | ok rets yst' =>
      exact (nullaryRead rfl (by decide) hm.env.gasprice hyul rfl
        (fun h1 h2 => .gasprice s h1 h2)
        hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (nullaryRead rfl (by decide) hm.env.gasprice hyul rfl
        (fun h1 h2 => .gasprice s h1 h2)
        hcode hf hm hpc hstk hgas40).elim
  case selfbalance =>
    cases r with
    | ok rets yst' =>
      exact (nullaryRead rfl (by decide) hm.selfBalance hyul rfl
        (fun h1 h2 => .selfbalance s h1 h2)
        hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (nullaryRead rfl (by decide) hm.selfBalance hyul rfl
        (fun h1 h2 => .selfbalance s h1 h2)
        hcode hf hm hpc hstk hgas40).elim
  case coinbase =>
    cases r with
    | ok rets yst' =>
      exact (nullaryRead rfl (by decide) hm.env.coinbase hyul rfl
        (fun h1 h2 => .coinbase s h1 h2)
        hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (nullaryRead rfl (by decide) hm.env.coinbase hyul rfl
        (fun h1 h2 => .coinbase s h1 h2)
        hcode hf hm hpc hstk hgas40).elim
  case timestamp =>
    cases r with
    | ok rets yst' =>
      exact (nullaryRead rfl (by decide) hm.env.timestamp hyul rfl
        (fun h1 h2 => .timestamp s h1 h2)
        hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (nullaryRead rfl (by decide) hm.env.timestamp hyul rfl
        (fun h1 h2 => .timestamp s h1 h2)
        hcode hf hm hpc hstk hgas40).elim
  case number =>
    cases r with
    | ok rets yst' =>
      exact (nullaryRead rfl (by decide) hm.env.number hyul rfl
        (fun h1 h2 => .number s h1 h2)
        hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (nullaryRead rfl (by decide) hm.env.number hyul rfl
        (fun h1 h2 => .number s h1 h2)
        hcode hf hm hpc hstk hgas40).elim
  case prevrandao =>
    cases r with
    | ok rets yst' =>
      exact (nullaryRead rfl (by decide) hm.env.prevrandao hyul rfl
        (fun h1 h2 => .prevrandao s h1 h2)
        hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (nullaryRead rfl (by decide) hm.env.prevrandao hyul rfl
        (fun h1 h2 => .prevrandao s h1 h2)
        hcode hf hm hpc hstk hgas40).elim
  case gaslimit =>
    cases r with
    | ok rets yst' =>
      exact (nullaryRead rfl (by decide) hm.env.gaslimit hyul rfl
        (fun h1 h2 => .gaslimit s h1 h2)
        hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (nullaryRead rfl (by decide) hm.env.gaslimit hyul rfl
        (fun h1 h2 => .gaslimit s h1 h2)
        hcode hf hm hpc hstk hgas40).elim
  case chainid =>
    cases r with
    | ok rets yst' =>
      exact (nullaryRead rfl (by decide) hm.env.chainid hyul rfl
        (fun h1 h2 => .chainid s h1 h2)
        hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (nullaryRead rfl (by decide) hm.env.chainid hyul rfl
        (fun h1 h2 => .chainid s h1 h2)
        hcode hf hm hpc hstk hgas40).elim
  case basefee =>
    cases r with
    | ok rets yst' =>
      exact (nullaryRead rfl (by decide) hm.env.basefee hyul rfl
        (fun h1 h2 => .basefee s h1 h2)
        hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (nullaryRead rfl (by decide) hm.env.basefee hyul rfl
        (fun h1 h2 => .basefee s h1 h2)
        hcode hf hm hpc hstk hgas40).elim
  case blobbasefee =>
    cases r with
    | ok rets yst' =>
      exact (nullaryRead rfl (by decide) hm.env.blobbasefee hyul rfl
        (fun h1 h2 => .blobbasefee s h1 h2)
        hcode hf hm hpc hstk hgas40).weaken (le_opBound _ _)
    | halt yst' =>
      exact (nullaryRead rfl (by decide) hm.env.blobbasefee hyul rfl
        (fun h1 h2 => .blobbasefee s h1 h2)
        hcode hf hm hpc hstk hgas40).elim
  case balance =>
    rcases args with _ | ⟨a, _ | ⟨b, args⟩⟩ <;>
      simp [stepOp, YulSemantics.EVM.rd1] at hyul
    subst hyul
    show OkStep code s (opBound .balance [a]) [yst.env.balanceOf a]
      yst pre.length 1 σ
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .balance) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain
      (opTable_available (yop := .balance) rfl)
    have hstk' : s.stack = conv a :: σ := by simpa using hstk
    have hbase : Gas.baseCost s.executionEnv.fork .BALANCE ≤ 100 := by
      rw [hf.fork]
      decide
    have hcold := accountCold_le s (AccountAddress.ofUInt256 (conv a))
    have htotal : Gas.balanceTotal s (conv a) ≤ 40000 := by
      unfold Gas.balanceTotal
      omega
    have hgas' : Gas.balanceTotal s (conv a) ≤ s.gasAvailable :=
      le_trans htotal hgas40
    refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
      (StepRunning.balance s (conv a) σ hdec hgas' hstk'),
      ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
        hf.running⟩,
      ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, ?_, ?_⟩
    · show s.pc.succ = _
      rw [hpc]; apply succ_ofNat
      have hsz : code.size = pre.length + 1 + post.length := by
        subst hcode; simp [Instr.bytes]; omega
      have := hf.codeSmall; omega
    · show (s.accountMap (AccountAddress.ofUInt256 (conv a))).balance :: σ = _
      simp [← hm.balanceOf a]
    · show s.gasAvailable - Gas.balanceTotal s (conv a)
        ≥ s.gasAvailable - opBound .balance [a]
      have h3 : opBound Op.balance [a] = 40000 := rfl
      rw [h3]
      exact Nat.sub_le_sub_left htotal s.gasAvailable
  case extcodesize =>
    rcases args with _ | ⟨a, _ | ⟨b, args⟩⟩ <;>
      simp [stepOp, YulSemantics.EVM.rd1] at hyul
    subst hyul
    show OkStep code s (opBound .extcodesize [a])
      [BitVec.ofNat 256 (yst.env.extCodeOf a).length] yst pre.length 1 σ
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .extcodesize) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain
      (opTable_available (yop := .extcodesize) rfl)
    have hstk' : s.stack = conv a :: σ := by simpa using hstk
    have htotal : Gas.extcodesizeTotal s (conv a) ≤ 40000 := by
      unfold Gas.extcodesizeTotal
      have hbase : Gas.baseCost s.executionEnv.fork Operation.EXTCODESIZE ≤ 100 := by
        rw [hf.fork]
        decide
      have hcold := accountCold_le s (AccountAddress.ofUInt256 (conv a))
      omega
    have hgas' : Gas.extcodesizeTotal s (conv a) ≤ s.gasAvailable :=
      le_trans htotal hgas40
    have hval : conv (BitVec.ofNat 256 (yst.env.extCodeOf a).length)
        = UInt256.ofNat (s.accountMap (AccountAddress.ofUInt256 (conv a))).code.size := by
      apply u256ext
      rw [conv_toNat, BitVec.toNat_ofNat, toNat_u256_ofNat,
        hm.externalCode.length a]
    refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
      (StepRunning.extcodesize s (conv a) σ hdec hgas' hstk'),
      ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
        hf.running⟩,
      ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen,
        hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, ?_, ?_⟩
    · show s.pc.succ = _
      rw [hpc]
      apply succ_ofNat
      have hsz : code.size = pre.length + 1 + post.length := by
        subst hcode
        simp [Instr.bytes]
        omega
      have := hf.codeSmall
      omega
    · show UInt256.ofNat
          (s.accountMap (AccountAddress.ofUInt256 (conv a))).code.size :: σ = _
      simp [hval]
    · show s.gasAvailable - Gas.extcodesizeTotal s (conv a)
          ≥ s.gasAvailable - opBound .extcodesize [a]
      have h3 : opBound Op.extcodesize [a] = 40000 := rfl
      rw [h3]
      exact Nat.sub_le_sub_left htotal s.gasAvailable
  case extcodecopy =>
    rcases args with _ | ⟨a, _ | ⟨d, _ | ⟨s0, _ | ⟨nn, _ | ⟨e, args⟩⟩⟩⟩⟩ <;>
      simp [stepOp] at hyul
    subst hyul
    show OkStep code s (opBound .extcodecopy [a, d, s0, nn]) []
      { YulSemantics.EVM.touchMemory yst d.toNat nn.toNat with memory :=
          (YulSemantics.EVM.copyInto yst.memory d.toNat s0.toNat nn.toNat
            (yst.env.extCodeOf a)) }
      pre.length 1 σ
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .extcodecopy) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain
      (opTable_available (yop := .extcodecopy) rfl)
    have hstk' : s.stack = conv a :: conv d :: conv s0 :: conv nn :: σ := by
      simpa using hstk
    have h3 : opBound Op.extcodecopy [a, d, s0, nn]
        = 40000 + (memBound d.toNat nn.toNat + 3 * ((nn.toNat + 31) / 32)) := rfl
    have h4 : Gas.copyWordCost (conv nn) = 3 * ((nn.toNat + 31) / 32) := by
      unfold Gas.copyWordCost
      rw [conv_toNat]
    have hbase : Gas.baseCost s.executionEnv.fork Operation.EXTCODECOPY ≤ 100 := by
      rw [hf.fork]
      decide
    have hmem := memExpansionDelta_le_memBound s.activeWords.toNat
      (conv d).toNat (conv nn).toNat
    rw [conv_toNat d, conv_toNat nn] at hmem
    have hcold := accountCold_le s (AccountAddress.ofUInt256 (conv a))
    have hgas' : Gas.extcodecopyTotal s (conv a) (conv d) (conv nn)
        ≤ s.gasAvailable := by
      unfold Gas.extcodecopyTotal
      rw [conv_toNat d, conv_toNat nn, h4]
      omega
    refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
      (StepRunning.extcodecopy s (conv a) (conv d) (conv s0) (conv nn) σ
        hdec hstk' hgas'),
      ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
        hf.running⟩,
      ⟨?_, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, ?_, hm.retData, hm.retDataLen,
        hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, rfl, ?_⟩
    · show MemMatch
        (YulSemantics.EVM.copyInto yst.memory d.toNat s0.toNat nn.toNat
          (yst.env.extCodeOf a))
        (MachineState.writeBytes s.memory
          (MachineState.readPadded
            (s.accountMap (AccountAddress.ofUInt256 (conv a))).code
            (conv s0).toNat (conv nn).toNat) (conv d).toNat)
      rw [conv_toNat d, conv_toNat s0, conv_toNat nn]
      exact hm.mem.copyFromBytes (hm.externalCode.bytes a) d.toNat s0.toNat nn.toNat
    · simpa only [conv_toNat] using activeWordsAfter_eq hm.activeWords d.toNat nn.toNat
    · show s.pc.succ = _
      rw [hpc]
      apply succ_ofNat
      have hsz : code.size = pre.length + 1 + post.length := by
        subst hcode
        simp [Instr.bytes]
        omega
      have := hf.codeSmall
      omega
    · show s.gasAvailable - Gas.extcodecopyTotal s (conv a) (conv d) (conv nn)
          ≥ s.gasAvailable - opBound .extcodecopy [a, d, s0, nn]
      unfold Gas.extcodecopyTotal
      rw [conv_toNat d, conv_toNat nn, h4, h3]
      omega
  case extcodehash =>
    rcases args with _ | ⟨a, _ | ⟨b, args⟩⟩ <;>
      simp [stepOp, YulSemantics.EVM.rd1] at hyul
    subst hyul
    show OkStep code s (opBound .extcodehash [a])
      [YulSemantics.EVM.projectedCodeHash yst.env yst.env.balanceOf a]
      yst pre.length 1 σ
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .extcodehash) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain
      (opTable_available (yop := .extcodehash) rfl)
    have hstk' : s.stack = conv a :: σ := by simpa using hstk
    have htotal : Gas.extcodehashTotal s (conv a) ≤ 40000 := by
      unfold Gas.extcodehashTotal
      have hbase : Gas.baseCost s.executionEnv.fork Operation.EXTCODEHASH ≤ 100 := by
        rw [hf.fork]
        decide
      have hcold := accountCold_le s (AccountAddress.ofUInt256 (conv a))
      omega
    have hgas' : Gas.extcodehashTotal s (conv a) ≤ s.gasAvailable :=
      le_trans htotal hgas40
    refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
      (StepRunning.extcodehash s (conv a) σ hdec hgas' hstk'),
      ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
        hf.running⟩,
      ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen,
        hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, ?_, ?_⟩
    · show s.pc.succ = _
      rw [hpc]
      apply succ_ofNat
      have hsz : code.size = pre.length + 1 + post.length := by
        subst hcode
        simp [Instr.bytes]
        omega
      have := hf.codeSmall
      omega
    · show (s.accountMap (AccountAddress.ofUInt256 (conv a))).codeHash :: σ = _
      simp [hm.externalCode.hash a]
    · show s.gasAvailable - Gas.extcodehashTotal s (conv a)
          ≥ s.gasAvailable - opBound .extcodehash [a]
      have h3 : opBound Op.extcodehash [a] = 40000 := rfl
      rw [h3]
      exact Nat.sub_le_sub_left htotal s.gasAvailable
  case blockhash =>
    rcases args with _ | ⟨n, _ | ⟨b, args⟩⟩ <;>
      simp [stepOp, YulSemantics.EVM.rd1] at hyul
    subst hyul
    show OkStep code s (opBound .blockhash [n]) [yst.env.blockHashOf n]
      yst pre.length 1 σ
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .blockhash) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain
      (opTable_available (yop := .blockhash) rfl)
    have hstk' : s.stack = conv n :: σ := by simpa using hstk
    have hgas' : Gas.baseCost s.fork .BLOCKHASH ≤ s.gasAvailable := by
      rw [hfork]
      have : Gas.baseCost .Osaka Operation.BLOCKHASH ≤ 40000 := by decide
      omega
    refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
      (StepRunning.blockhash s (conv n) σ hdec hgas' hstk'),
      ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
        hf.running⟩,
      ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen,
        hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, ?_, ?_⟩
    · show s.pc.succ = _
      rw [hpc]
      apply succ_ofNat
      have hsz : code.size = pre.length + 1 + post.length := by
        subst hcode
        simp [Instr.bytes]
        omega
      have := hf.codeSmall
      omega
    · show s.executionEnv.header.blockHash (conv n) :: σ = _
      simp [hm.env.blockHash n]
    · show s.gasAvailable - Gas.baseCost s.fork .BLOCKHASH
          ≥ s.gasAvailable - opBound .blockhash [n]
      have h3 : opBound Op.blockhash [n] = 40000 := rfl
      rw [h3]
      apply Nat.sub_le_sub_left
      rw [hfork]
      decide
  case blobhash =>
    rcases args with _ | ⟨i, _ | ⟨b, args⟩⟩ <;>
      simp [stepOp, YulSemantics.EVM.rd1] at hyul
    subst hyul
    show OkStep code s (opBound .blobhash [i]) [yst.env.blobHashOf i]
      yst pre.length 1 σ
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .blobhash) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain
      (opTable_available (yop := .blobhash) rfl)
    have hstk' : s.stack = conv i :: σ := by simpa using hstk
    have hgas' : Gas.baseCost s.fork .BLOBHASH ≤ s.gasAvailable := by
      rw [hfork]
      have : Gas.baseCost .Osaka Operation.BLOBHASH ≤ 40000 := by decide
      omega
    cases hlookup : s.executionEnv.blobVersionedHashes[(conv i).toNat]? with
    | none =>
      have hval := hm.env.blobHash i
      rw [hlookup] at hval
      refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
        (StepRunning.blobhash_oob s (conv i) σ hdec hgas' hstk' hlookup),
        ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
          hf.running⟩,
        ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
          hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, ?_, ?_⟩
      · show s.pc.succ = _
        rw [hpc]; apply succ_ofNat
        have hsz : code.size = pre.length + 1 + post.length := by
          subst hcode; simp [Instr.bytes]; omega
        have := hf.codeSmall; omega
      · show (0 : UInt256) :: σ = _
        simp [hval]
      · show s.gasAvailable - Gas.baseCost s.fork .BLOBHASH
          ≥ s.gasAvailable - opBound .blobhash [i]
        have h3 : opBound Op.blobhash [i] = 40000 := rfl
        have : Gas.baseCost s.fork .BLOBHASH ≤ 40000 := by rw [hfork]; decide
        omega
    | some h =>
      have hval := hm.env.blobHash i
      rw [hlookup] at hval
      refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
        (StepRunning.blobhash s (conv i) σ h hdec hgas' hstk' hlookup),
        ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
          hf.running⟩,
        ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
          hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, ?_, ?_⟩
      · show s.pc.succ = _
        rw [hpc]; apply succ_ofNat
        have hsz : code.size = pre.length + 1 + post.length := by
          subst hcode; simp [Instr.bytes]; omega
        have := hf.codeSmall; omega
      · show h :: σ = _
        simp [hval]
      · show s.gasAvailable - Gas.baseCost s.fork .BLOBHASH
          ≥ s.gasAvailable - opBound .blobhash [i]
        have h3 : opBound Op.blobhash [i] = 40000 := rfl
        have : Gas.baseCost s.fork .BLOBHASH ≤ 40000 := by rw [hfork]; decide
        omega
  case log0 =>
    cases hst : yst.env.static with
    | false =>
      have hperm : s.executionEnv.permitStateMutation = true :=
        hm.perm_of_static_false hst
      have hguard (act : YulSemantics.BuiltinResult U256 EvmState) :
          YulSemantics.EVM.guardStatic yst act = some act := by
        simp [YulSemantics.EVM.guardStatic, hst]
      rcases args with _ | ⟨p, _ | ⟨n, _ | ⟨extra, args⟩⟩⟩ <;>
        simp [stepOp, hguard] at hyul
      subst hyul
      exact logStep (yop := .log0) (topicCount := 0) rfl rfl rfl
        hcode hf hm hperm hpc hstk hgas
    | true =>
      have hperm : s.executionEnv.permitStateMutation = false :=
        hm.perm_of_static_true hst
      rcases args with _ | ⟨p, _ | ⟨n, _ | ⟨extra, args⟩⟩⟩ <;>
        simp [stepOp, YulSemantics.EVM.guardStatic, hst] at hyul
      subst hyul
      exact staticViolationStep (yop := .log0) rfl hcode hf hm hpc (by decide) hperm
  case log1 =>
    cases hst : yst.env.static with
    | false =>
      have hperm : s.executionEnv.permitStateMutation = true :=
        hm.perm_of_static_false hst
      have hguard (act : YulSemantics.BuiltinResult U256 EvmState) :
          YulSemantics.EVM.guardStatic yst act = some act := by
        simp [YulSemantics.EVM.guardStatic, hst]
      rcases args with _ | ⟨p, _ | ⟨n, _ | ⟨t1, _ | ⟨extra, args⟩⟩⟩⟩ <;>
        simp [stepOp, hguard] at hyul
      subst hyul
      exact logStep (yop := .log1) (topicCount := 1) rfl rfl rfl
        hcode hf hm hperm hpc hstk hgas
    | true =>
      have hperm : s.executionEnv.permitStateMutation = false :=
        hm.perm_of_static_true hst
      rcases args with _ | ⟨p, _ | ⟨n, _ | ⟨t1, _ | ⟨extra, args⟩⟩⟩⟩ <;>
        simp [stepOp, YulSemantics.EVM.guardStatic, hst] at hyul
      subst hyul
      exact staticViolationStep (yop := .log1) rfl hcode hf hm hpc (by decide) hperm
  case log2 =>
    cases hst : yst.env.static with
    | false =>
      have hperm : s.executionEnv.permitStateMutation = true :=
        hm.perm_of_static_false hst
      have hguard (act : YulSemantics.BuiltinResult U256 EvmState) :
          YulSemantics.EVM.guardStatic yst act = some act := by
        simp [YulSemantics.EVM.guardStatic, hst]
      rcases args with _ | ⟨p, _ | ⟨n, _ | ⟨t1, _ | ⟨t2, _ | ⟨extra, args⟩⟩⟩⟩⟩ <;>
        simp [stepOp, hguard] at hyul
      subst hyul
      exact logStep (yop := .log2) (topicCount := 2) rfl rfl rfl
        hcode hf hm hperm hpc hstk hgas
    | true =>
      have hperm : s.executionEnv.permitStateMutation = false :=
        hm.perm_of_static_true hst
      rcases args with _ | ⟨p, _ | ⟨n, _ | ⟨t1, _ | ⟨t2, _ | ⟨extra, args⟩⟩⟩⟩⟩ <;>
        simp [stepOp, YulSemantics.EVM.guardStatic, hst] at hyul
      subst hyul
      exact staticViolationStep (yop := .log2) rfl hcode hf hm hpc (by decide) hperm
  case log3 =>
    cases hst : yst.env.static with
    | false =>
      have hperm : s.executionEnv.permitStateMutation = true :=
        hm.perm_of_static_false hst
      have hguard (act : YulSemantics.BuiltinResult U256 EvmState) :
          YulSemantics.EVM.guardStatic yst act = some act := by
        simp [YulSemantics.EVM.guardStatic, hst]
      rcases args with _ | ⟨p, _ | ⟨n, _ | ⟨t1, _ | ⟨t2, _ | ⟨t3,
        _ | ⟨extra, args⟩⟩⟩⟩⟩⟩ <;>
        simp [stepOp, hguard] at hyul
      subst hyul
      exact logStep (yop := .log3) (topicCount := 3) rfl rfl rfl
        hcode hf hm hperm hpc hstk hgas
    | true =>
      have hperm : s.executionEnv.permitStateMutation = false :=
        hm.perm_of_static_true hst
      rcases args with _ | ⟨p, _ | ⟨n, _ | ⟨t1, _ | ⟨t2, _ | ⟨t3,
        _ | ⟨extra, args⟩⟩⟩⟩⟩⟩ <;>
        simp [stepOp, YulSemantics.EVM.guardStatic, hst] at hyul
      subst hyul
      exact staticViolationStep (yop := .log3) rfl hcode hf hm hpc (by decide) hperm
  case log4 =>
    cases hst : yst.env.static with
    | false =>
      have hperm : s.executionEnv.permitStateMutation = true :=
        hm.perm_of_static_false hst
      have hguard (act : YulSemantics.BuiltinResult U256 EvmState) :
          YulSemantics.EVM.guardStatic yst act = some act := by
        simp [YulSemantics.EVM.guardStatic, hst]
      rcases args with _ | ⟨p, _ | ⟨n, _ | ⟨t1, _ | ⟨t2, _ | ⟨t3,
        _ | ⟨t4, _ | ⟨extra, args⟩⟩⟩⟩⟩⟩⟩ <;>
        simp [stepOp, hguard] at hyul
      subst hyul
      exact logStep (yop := .log4) (topicCount := 4) rfl rfl rfl
        hcode hf hm hperm hpc hstk hgas
    | true =>
      have hperm : s.executionEnv.permitStateMutation = false :=
        hm.perm_of_static_true hst
      rcases args with _ | ⟨p, _ | ⟨n, _ | ⟨t1, _ | ⟨t2, _ | ⟨t3,
        _ | ⟨t4, _ | ⟨extra, args⟩⟩⟩⟩⟩⟩⟩ <;>
        simp [stepOp, YulSemantics.EVM.guardStatic, hst] at hyul
      subst hyul
      exact staticViolationStep (yop := .log4) rfl hcode hf hm hpc (by decide) hperm
  case sload =>
    rcases args with _ | ⟨k, _ | ⟨b, args⟩⟩ <;> simp [stepOp] at hyul
    subst hyul
    show OkStep code s (opBound .sload [k]) [yst.storage k] yst pre.length 1 σ
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .sload) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain
      (opTable_available (yop := .sload) rfl)
    have hstk' : s.stack = conv k :: σ := by simpa using hstk
    have hgas' : Gas.sloadTotal s (conv k) ≤ s.gasAvailable := by
      unfold Gas.sloadTotal
      have h1 : Gas.baseCost s.executionEnv.fork Operation.SLOAD ≤ 100 := by
        rw [hf.fork]; decide
      have h2 := sloadCold_le s (conv k)
      omega
    refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
      (StepRunning.sload s (conv k) σ hdec hgas' hstk'),
      ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
        hf.running⟩,
      ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, ?_, ?_⟩
    · show s.pc.succ = _
      rw [hpc]; apply succ_ofNat
      have hsz : code.size = pre.length + 1 + post.length := by
        subst hcode; simp [Instr.bytes]; omega
      have := hf.codeSmall; omega
    · show (s.accountMap s.executionEnv.address).storage.get (conv k) :: σ = _
      simp [← hm.stor k]
    · show s.gasAvailable - Gas.sloadTotal s (conv k)
        ≥ s.gasAvailable - opBound .sload [k]
      have h1 : Gas.baseCost s.executionEnv.fork Operation.SLOAD ≤ 100 := by
        rw [hf.fork]; decide
      have h2 := sloadCold_le s (conv k)
      have h3 : opBound Op.sload [k] = 40000 := rfl
      unfold Gas.sloadTotal
      omega
  case sstore =>
    cases hst : yst.env.static with
    | true =>
      have hperm : s.executionEnv.permitStateMutation = false :=
        hm.perm_of_static_true hst
      rcases args with _ | ⟨k, _ | ⟨v, _ | ⟨c, args⟩⟩⟩ <;>
        simp [stepOp, YulSemantics.EVM.guardStatic, hst] at hyul
      subst hyul
      exact staticViolationStep (yop := .sstore) rfl hcode hf hm hpc (by decide) hperm
    | false =>
      have hperm : s.executionEnv.permitStateMutation = true :=
        hm.perm_of_static_false hst
      have hguard (act : YulSemantics.BuiltinResult U256 EvmState) :
          YulSemantics.EVM.guardStatic yst act = some act := by
        simp [YulSemantics.EVM.guardStatic, hst]
      rcases args with _ | ⟨k, _ | ⟨v, _ | ⟨c, args⟩⟩⟩ <;>
        simp [stepOp, hguard] at hyul
      subst hyul
      show OkStep code s (opBound .sstore [k, v]) []
        { yst with
            storage := YulSemantics.EVM.upd yst.storage k v
            env := { yst.env with storageOf :=
              YulSemantics.EVM.updAccount yst.env.storageOf yst.env.address k v } }
        pre.length 1 σ
      obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .sstore) rfl
      have hdec := decoded_op hf hcode hpc hb' hplain
        (opTable_available (yop := .sstore) rfl)
      have hstk' : s.stack = conv k :: conv v :: σ := by simpa using hstk
      have hsent : Gas.sstoreSentry s.fork
          (s.gasAvailable - Gas.baseCost s.fork .SSTORE) = false := by
        show Gas.sstoreSentry s.executionEnv.fork
          (s.gasAvailable - Gas.baseCost s.executionEnv.fork Operation.SSTORE) = false
        rw [hf.fork]
        unfold Gas.sstoreSentry
        rw [if_pos (by decide)]
        apply decide_eq_false
        have hb0 : Gas.baseCost Fork.Osaka Operation.SSTORE = 0 := by decide
        omega
      have hgas' : Gas.sstoreTotal s (conv k) (conv v) ≤ s.gasAvailable := by
        unfold Gas.sstoreTotal
        have h1 := sstoreCost_le s.executionEnv.fork
          (s.substate.originalStorage s.executionEnv.address (conv k))
          ((s.accountMap s.executionEnv.address).storage (conv k)) (conv v)
        have h2 := sstoreCold_le s (conv k)
        have hb0 : Gas.baseCost s.executionEnv.fork Operation.SSTORE = 0 := by
          rw [hf.fork]; decide
        omega
      refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
        (StepRunning.sstore s (conv k) (conv v) σ hdec hperm hstk' hsent hgas'),
        ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
          hf.running⟩,
        ?_, ?_, rfl, ?_⟩
      · constructor
        · exact hm.mem
        · intro k'
          show conv (YulSemantics.EVM.upd yst.storage k v k') = _
          unfold YulSemantics.EVM.upd
          rw [AccountMap.get_set_same]
          by_cases hk : k' = k
          · subst hk
            rw [if_pos rfl]
            exact (Storage.get_set_same _ _ _).symm
          · rw [if_neg hk]
            rw [Storage.get_set_other _ _ _ _ (by simpa [conv_inj] using hk)]
            exact hm.stor k'
        · intro k'
          rw [AccountMap.get_set_same]
          exact hm.tstor k'
        · exact hm.cd
        · exact hm.env.setStorageOf _
        · exact hm.codeBytes
        · exact hm.codeLen
        · rw [AccountMap.get_set_same]
          exact hm.selfBalance
        · intro a
          by_cases ha : AccountAddress.ofUInt256 (conv a) = s.executionEnv.address
          · rw [ha, AccountMap.get_set_same]
            have hba := hm.balanceOf a
            rw [ha] at hba
            simpa using hba
          · rw [AccountMap.get_set_other _ _ _ _ ha]
            exact hm.balanceOf a
        · exact hm.activeWords
        · exact hm.retData
        · exact hm.retDataLen
        · apply hm.externalCode.setStorage yst.env.address s.executionEnv.address k v
          rw [hm.env.address]
          exact accountAddress_ofUInt256_toUInt256 _
        · exact hm.logs
        · exact hm.selfdestructs
        · exact hm.createdThisTx
      · show s.pc.succ = _
        rw [hpc]; apply succ_ofNat
        have hsz : code.size = pre.length + 1 + post.length := by
          subst hcode; simp [Instr.bytes]; omega
        have := hf.codeSmall; omega
      · show s.gasAvailable - Gas.sstoreTotal s (conv k) (conv v)
          ≥ s.gasAvailable - opBound .sstore [k, v]
        have h1 := sstoreCost_le s.executionEnv.fork
          (s.substate.originalStorage s.executionEnv.address (conv k))
          ((s.accountMap s.executionEnv.address).storage (conv k)) (conv v)
        have h2 := sstoreCold_le s (conv k)
        have h3 : opBound Op.sstore [k, v] = 40000 := rfl
        have hb0 : Gas.baseCost s.executionEnv.fork Operation.SSTORE = 0 := by
          rw [hf.fork]; decide
        unfold Gas.sstoreTotal
        omega
  case tload =>
    rcases args with _ | ⟨k, _ | ⟨b, args⟩⟩ <;> simp [stepOp] at hyul
    subst hyul
    show OkStep code s (opBound .tload [k]) [yst.transient k] yst pre.length 1 σ
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .tload) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain
      (opTable_available (yop := .tload) rfl)
    have hstk' : s.stack = conv k :: σ := by simpa using hstk
    have hgas' : Gas.baseCost s.fork .TLOAD ≤ s.gasAvailable := by
      rw [hfork]
      have : Gas.baseCost .Osaka Operation.TLOAD ≤ 40000 := by decide
      omega
    refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
      (StepRunning.tload s (conv k) σ hdec hgas' hstk'),
      ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
        hf.running⟩,
      ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, ?_, ?_⟩
    · show s.pc.succ = _
      rw [hpc]; apply succ_ofNat
      have hsz : code.size = pre.length + 1 + post.length := by
        subst hcode; simp [Instr.bytes]; omega
      have := hf.codeSmall; omega
    · show (s.accountMap s.executionEnv.address).tstorage.get (conv k) :: σ = _
      simp [← hm.tstor k]
    · show s.gasAvailable - Gas.baseCost s.fork .TLOAD
        ≥ s.gasAvailable - opBound .tload [k]
      have h1 : Gas.baseCost s.fork .TLOAD ≤ 100 := by rw [hfork]; decide -- ok
      have h3 : opBound Op.tload [k] = 40000 := rfl
      omega
  case tstore =>
    cases hst : yst.env.static with
    | true =>
      have hperm : s.executionEnv.permitStateMutation = false :=
        hm.perm_of_static_true hst
      rcases args with _ | ⟨k, _ | ⟨v, _ | ⟨c, args⟩⟩⟩ <;>
        simp [stepOp, YulSemantics.EVM.guardStatic, hst] at hyul
      subst hyul
      exact staticViolationStep (yop := .tstore) rfl hcode hf hm hpc (by decide) hperm
    | false =>
      have hperm : s.executionEnv.permitStateMutation = true :=
        hm.perm_of_static_false hst
      have hguard (act : YulSemantics.BuiltinResult U256 EvmState) :
          YulSemantics.EVM.guardStatic yst act = some act := by
        simp [YulSemantics.EVM.guardStatic, hst]
      rcases args with _ | ⟨k, _ | ⟨v, _ | ⟨c, args⟩⟩⟩ <;>
        simp [stepOp, hguard] at hyul
      subst hyul
      show OkStep code s (opBound .tstore [k, v]) []
        { yst with
            transient := YulSemantics.EVM.upd yst.transient k v
            env := { yst.env with transientOf :=
              YulSemantics.EVM.updAccount yst.env.transientOf yst.env.address k v } }
        pre.length 1 σ
      obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .tstore) rfl
      have hdec := decoded_op hf hcode hpc hb' hplain
        (opTable_available (yop := .tstore) rfl)
      have hstk' : s.stack = conv k :: conv v :: σ := by simpa using hstk
      have hgas' : Gas.baseCost s.fork .TSTORE ≤ s.gasAvailable := by
        rw [hfork]
        have : Gas.baseCost .Osaka Operation.TSTORE ≤ 40000 := by decide
        omega
      refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
        (StepRunning.tstore s (conv k) (conv v) σ hdec hperm hgas' hstk'),
        ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
          hf.running⟩,
        ?_, ?_, rfl, ?_⟩
      · constructor
        · exact hm.mem
        · intro k'
          rw [AccountMap.get_set_same]
          exact hm.stor k'
        · intro k'
          show conv (YulSemantics.EVM.upd yst.transient k v k') = _
          unfold YulSemantics.EVM.upd
          rw [AccountMap.get_set_same]
          by_cases hk : k' = k
          · subst hk
            rw [if_pos rfl]
            exact (Storage.get_set_same _ _ _).symm
          · rw [if_neg hk]
            rw [Storage.get_set_other _ _ _ _ (by simpa [conv_inj] using hk)]
            exact hm.tstor k'
        · exact hm.cd
        · exact hm.env.setTransientOf _
        · exact hm.codeBytes
        · exact hm.codeLen
        · rw [AccountMap.get_set_same]
          exact hm.selfBalance
        · intro a
          by_cases ha : AccountAddress.ofUInt256 (conv a) = s.executionEnv.address
          · rw [ha, AccountMap.get_set_same]
            have hba := hm.balanceOf a
            rw [ha] at hba
            simpa using hba
          · rw [AccountMap.get_set_other _ _ _ _ ha]
            exact hm.balanceOf a
        · exact hm.activeWords
        · exact hm.retData
        · exact hm.retDataLen
        · apply hm.externalCode.setTransient yst.env.address s.executionEnv.address k v
          rw [hm.env.address]
          exact accountAddress_ofUInt256_toUInt256 _
        · exact hm.logs
        · exact hm.selfdestructs
        · exact hm.createdThisTx
      · show s.pc.succ = _
        rw [hpc]; apply succ_ofNat
        have hsz : code.size = pre.length + 1 + post.length := by
          subst hcode; simp [Instr.bytes]; omega
        have := hf.codeSmall; omega
      · show s.gasAvailable - Gas.baseCost s.fork .TSTORE
          ≥ s.gasAvailable - opBound .tstore [k, v]
        have h1 : Gas.baseCost s.fork .TSTORE ≤ 100 := by rw [hfork]; decide
        have h3 : opBound Op.tstore [k, v] = 40000 := rfl
        omega
  case call => simp [stepOp] at hyul
  case callcode => simp [stepOp] at hyul
  case delegatecall => simp [stepOp] at hyul
  case staticcall => simp [stepOp] at hyul
  case create => simp [stepOp] at hyul
  case create2 => simp [stepOp] at hyul
  case selfdestruct =>
    cases hst : yst.env.static with
    | true =>
      have hperm : s.executionEnv.permitStateMutation = false :=
        hm.perm_of_static_true hst
      rcases args with _ | ⟨beneficiary, _ | ⟨extra, args⟩⟩ <;>
        simp [stepOp, YulSemantics.EVM.guardStatic, hst] at hyul
      subst hyul
      exact staticViolationStep (yop := .selfdestruct) rfl hcode hf hm hpc
        (by decide) hperm
    | false =>
      have hperm : s.executionEnv.permitStateMutation = true :=
        hm.perm_of_static_false hst
      have hguard (act : YulSemantics.BuiltinResult U256 EvmState) :
          YulSemantics.EVM.guardStatic yst act = some act := by
        simp [YulSemantics.EVM.guardStatic, hst]
      rcases args with _ | ⟨beneficiary, _ | ⟨extra, args⟩⟩ <;>
        simp [stepOp, hguard] at hyul
      subst hyul
      exact selfdestructStep hcode hf hm hperm hpc hstk hgas40
  case stop =>
    rcases args with _ | ⟨a, args⟩ <;> simp [stepOp] at hyul
    subst hyul
    show HaltStep s { yst with halted := some (.stop, []) }
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .stop) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain
      (opTable_available (yop := .stop) rfl)
    exact ⟨_, EVM.Step.running hf.running hf.noPrecompile (StepRunning.stop s hdec),
      ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, hf.callStack, (.stop, []), rfl, rfl⟩
  case invalid =>
    rcases args with _ | ⟨a, args⟩ <;> simp [stepOp] at hyul
    subst hyul
    show HaltStep s { yst with halted := some (.invalid, []) }
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .invalid) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain
      (opTable_available (yop := .invalid) rfl)
    exact ⟨_, EVM.Step.running hf.running hf.noPrecompile
      (StepRunning.invalidOpcode s hdec),
      ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, hf.callStack, (.invalid, []), rfl, rfl⟩
  case ret =>
    rcases args with _ | ⟨p, _ | ⟨n, _ | ⟨c, args⟩⟩⟩ <;> simp [stepOp] at hyul
    subst hyul
    show HaltStep s { YulSemantics.EVM.touchMemory yst p.toNat n.toNat with
      halted := some (.ret, YulSemantics.EVM.readBytes yst.memory p.toNat n.toNat) }
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .ret) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain
      (opTable_available (yop := .ret) rfl)
    have hstk' : s.stack = conv p :: conv n :: σ := by simpa using hstk
    have hgas' : Gas.returnTotal s (conv p) (conv n) ≤ s.gasAvailable := by
      unfold Gas.returnTotal
      have h1 : Gas.baseCost s.executionEnv.fork Operation.RETURN ≤ 3 := by rw [hf.fork]; decide
      have h2 := memExpansionDelta_le_memBound s.activeWords.toNat (conv p).toNat (conv n).toNat
      have h3 : opBound Op.ret [p, n] = 40000 + memBound (conv p).toNat (conv n).toNat := rfl
      omega
    exact ⟨_, EVM.Step.running hf.running hf.noPrecompile
      (StepRunning.return_ s (conv p) (conv n) σ hdec hstk' hgas'),
      ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf,
        by simpa only [conv_toNat] using activeWordsAfter_eq hm.activeWords p.toNat n.toNat,
        hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩,
      hf.callStack,
      (.ret, YulSemantics.EVM.readBytes yst.memory p.toNat n.toNat), rfl,
      rfl, (hm.mem.readBytes p.toNat n.toNat).symm⟩
  case revert =>
    rcases args with _ | ⟨p, _ | ⟨n, _ | ⟨c, args⟩⟩⟩ <;> simp [stepOp] at hyul
    subst hyul
    show HaltStep s { YulSemantics.EVM.touchMemory yst p.toNat n.toNat with
      halted := some (.revert, YulSemantics.EVM.readBytes yst.memory p.toNat n.toNat) }
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .revert) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain
      (opTable_available (yop := .revert) rfl)
    have hstk' : s.stack = conv p :: conv n :: σ := by simpa using hstk
    have hgas' : Gas.revertTotal s (conv p) (conv n) ≤ s.gasAvailable := by
      unfold Gas.revertTotal
      have h1 : Gas.baseCost s.executionEnv.fork Operation.REVERT ≤ 3 := by rw [hf.fork]; decide
      have h2 := memExpansionDelta_le_memBound s.activeWords.toNat (conv p).toNat (conv n).toNat
      have h3 : opBound Op.revert [p, n] = 40000 + memBound (conv p).toNat (conv n).toNat := rfl
      omega
    exact ⟨_, EVM.Step.running hf.running hf.noPrecompile
      (StepRunning.revert s (conv p) (conv n) σ hdec hstk' hgas'),
      ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf,
        by simpa only [conv_toNat] using activeWordsAfter_eq hm.activeWords p.toNat n.toNat,
        hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩,
      hf.callStack,
      (.revert, YulSemantics.EVM.readBytes yst.memory p.toNat n.toNat), rfl,
      rfl, (hm.mem.readBytes p.toNat n.toNat).symm⟩

/-! ### Control-flow steps: `JUMPDEST`, `JUMPI` -/

/-- Executing an embedded `JUMPDEST`: a no-op that advances the pc. -/
theorem jumpdestStep {code : ByteArray} {pre post : List UInt8}
    {yst : EvmState} {s : State}
    (hcode : code = mkCode (pre ++ (Instr.op .JUMPDEST).bytes ++ post))
    (hf : FrameOK code s) (hm : StateMatch yst s)
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hgas : 40000 ≤ s.gasAvailable) :
    ∃ s', EVM.Step s s' ∧ FrameOK code s' ∧ StateMatch yst s'
      ∧ s'.pc = UInt256.ofNat (pre.length + 1)
      ∧ s'.stack = s.stack
      ∧ s.gasAvailable - 40000 ≤ s'.gasAvailable := by
  have hdec := decoded_op hf hcode hpc (by decide) trivial (by decide)
  have hfork : s.fork = .Osaka := hf.fork
  have hgas' : Gas.baseCost s.fork .JUMPDEST ≤ s.gasAvailable := by
    rw [hfork]
    have : Gas.baseCost .Osaka Operation.JUMPDEST ≤ 40000 := by decide
    omega
  refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
    (StepRunning.jumpdest s hdec hgas'),
    ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
      hf.running⟩,
    ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, rfl, ?_⟩
  · show s.pc.succ = _
    rw [hpc]; apply succ_ofNat
    have hsz : code.size = pre.length + 1 + post.length := by
      subst hcode; simp [Instr.bytes]; omega
    have := hf.codeSmall; omega
  · show s.gasAvailable - Gas.baseCost s.fork .JUMPDEST ≥ s.gasAvailable - 40000
    apply Nat.sub_le_sub_left
    rw [hfork]
    decide

/-- Executing an embedded `JUMP`: jump to `dest` (which must pass the
jumpdest analysis). -/
theorem jumpStep {code : ByteArray} {pre post : List UInt8}
    {dest : UInt256} {rest : List UInt256} {yst : EvmState} {s : State}
    (hcode : code = mkCode (pre ++ (Instr.op .JUMP).bytes ++ post))
    (hf : FrameOK code s) (hm : StateMatch yst s)
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hstk : s.stack = dest :: rest)
    (hvalid : Decode.isValidJumpDest code dest.toNat = true)
    (hgas : 40000 ≤ s.gasAvailable) :
    ∃ s', EVM.Step s s' ∧ FrameOK code s' ∧ StateMatch yst s'
      ∧ s'.pc = dest
      ∧ s'.stack = rest
      ∧ s.gasAvailable - 40000 ≤ s'.gasAvailable := by
  have hdec := decoded_op hf hcode hpc (by decide) trivial (by decide)
  have hfork : s.fork = .Osaka := hf.fork
  have hgas' : Gas.baseCost s.fork .JUMP ≤ s.gasAvailable := by
    rw [hfork]
    have : Gas.baseCost .Osaka Operation.JUMP ≤ 40000 := by decide
    omega
  refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
    (StepRunning.jump s dest rest hdec hgas' hstk
      (by rw [hf.hcode]; exact hvalid)),
    ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
      hf.running⟩,
    ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, rfl, rfl, ?_⟩
  · show s.gasAvailable - Gas.baseCost s.fork .JUMP ≥ s.gasAvailable - 40000
    apply Nat.sub_le_sub_left
    rw [hfork]
    decide

/-- Executing an embedded `JUMPI` whose condition is zero: fall through. -/
theorem jumpiNotTakenStep {code : ByteArray} {pre post : List UInt8}
    {dest cond : UInt256} {rest : List UInt256} {yst : EvmState} {s : State}
    (hcode : code = mkCode (pre ++ (Instr.op .JUMPI).bytes ++ post))
    (hf : FrameOK code s) (hm : StateMatch yst s)
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hstk : s.stack = dest :: cond :: rest)
    (hcond : cond.toNat = 0)
    (hgas : 40000 ≤ s.gasAvailable) :
    ∃ s', EVM.Step s s' ∧ FrameOK code s' ∧ StateMatch yst s'
      ∧ s'.pc = UInt256.ofNat (pre.length + 1)
      ∧ s'.stack = rest
      ∧ s.gasAvailable - 40000 ≤ s'.gasAvailable := by
  have hdec := decoded_op hf hcode hpc (by decide) trivial (by decide)
  have hfork : s.fork = .Osaka := hf.fork
  have hgas' : Gas.baseCost s.fork .JUMPI ≤ s.gasAvailable := by
    rw [hfork]
    have : Gas.baseCost .Osaka Operation.JUMPI ≤ 40000 := by decide
    omega
  refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
    (StepRunning.jumpi_notTaken s dest cond rest hdec hgas' hstk
      (by simp [UInt256.isTrue, hcond])),
    ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
      hf.running⟩,
    ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, ?_, rfl, ?_⟩
  · show s.pc.succ = _
    rw [hpc]; apply succ_ofNat
    have hsz : code.size = pre.length + 1 + post.length := by
      subst hcode; simp [Instr.bytes]; omega
    have := hf.codeSmall; omega
  · show s.gasAvailable - Gas.baseCost s.fork .JUMPI ≥ s.gasAvailable - 40000
    apply Nat.sub_le_sub_left
    rw [hfork]
    decide

/-- Executing an embedded `JUMPI` with a nonzero condition: jump to `dest`
(which must pass the jumpdest analysis). -/
theorem jumpiTakenStep {code : ByteArray} {pre post : List UInt8}
    {dest cond : UInt256} {rest : List UInt256} {yst : EvmState} {s : State}
    (hcode : code = mkCode (pre ++ (Instr.op .JUMPI).bytes ++ post))
    (hf : FrameOK code s) (hm : StateMatch yst s)
    (hpc : s.pc = UInt256.ofNat pre.length)
    (hstk : s.stack = dest :: cond :: rest)
    (hcond : cond.toNat ≠ 0)
    (hvalid : Decode.isValidJumpDest code dest.toNat = true)
    (hgas : 40000 ≤ s.gasAvailable) :
    ∃ s', EVM.Step s s' ∧ FrameOK code s' ∧ StateMatch yst s'
      ∧ s'.pc = dest
      ∧ s'.stack = rest
      ∧ s.gasAvailable - 40000 ≤ s'.gasAvailable := by
  have hdec := decoded_op hf hcode hpc (by decide) trivial (by decide)
  have hfork : s.fork = .Osaka := hf.fork
  have hgas' : Gas.baseCost s.fork .JUMPI ≤ s.gasAvailable := by
    rw [hfork]
    have : Gas.baseCost .Osaka Operation.JUMPI ≤ 40000 := by decide
    omega
  refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
    (StepRunning.jumpi_taken s dest cond rest hdec hgas' hstk hcond
      (by rw [hf.hcode]; exact hvalid)),
    ⟨hf.hcode, hf.codeSmall, hf.fork, hf.perm, hf.noPrecompile, hf.callStack,
      hf.running⟩,
    ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen, hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩, rfl, rfl, ?_⟩
  · show s.gasAvailable - Gas.baseCost s.fork .JUMPI ≥ s.gasAvailable - 40000
    apply Nat.sub_le_sub_left
    rw [hfork]
    decide

end YulEvmCompiler
