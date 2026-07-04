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

/-- Worst-case gas consumed by the single instruction compiled for `op` on
argument values `args`. -/
def opBound (op : Op) (args : List U256) : Nat :=
  40000 +
    match op, args with
    | .mload, [p] => memBound p.toNat 32
    | .ret, [p, n] => memBound p.toNat n.toNat
    | .revert, [p, n] => memBound p.toNat n.toNat
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
    ⟨hm.mem, hm.stor, hm.tstor⟩, ?_, ?_, ?_⟩
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
    ⟨hm.mem, hm.stor, hm.tstor⟩, hf.callStack, rfl, rfl⟩

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
    ⟨hm.mem, hm.stor, hm.tstor⟩, ?_, rfl, ?_⟩
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
    ⟨hm.mem, hm.stor, hm.tstor⟩, ?_, rfl, ?_⟩
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
    ⟨hm.mem, hm.stor, hm.tstor⟩, ?_, rfl, ?_⟩
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
    ⟨hm.mem, hm.stor, hm.tstor⟩, ?_, ?_, ?_⟩
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
    ⟨hm.mem, hm.stor, hm.tstor⟩, ?_, ?_, ?_⟩
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
    ⟨hm.mem, hm.stor, hm.tstor⟩, ?_, ?_, ?_⟩
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

/-! ### The per-built-in step -/

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
      ⟨hm.mem, hm.stor, hm.tstor⟩, ?_, ?_, ?_⟩
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
      ⟨hm.mem, hm.stor, hm.tstor⟩, ?_, rfl, ?_⟩
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
      [YulSemantics.EVM.loadWord yst.memory p.toNat] yst pre.length 1 σ
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
      ⟨hm.mem, hm.stor, hm.tstor⟩, ?_, ?_, ?_⟩
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
      ⟨hm.mem, hm.stor, hm.tstor⟩, ?_, ?_, ?_⟩
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
    rcases args with _ | ⟨k, _ | ⟨v, _ | ⟨c, args⟩⟩⟩ <;> simp [stepOp] at hyul
    subst hyul
    show OkStep code s (opBound .sstore [k, v]) []
      { yst with storage := YulSemantics.EVM.upd yst.storage k v } pre.length 1 σ
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
      (StepRunning.sstore s (conv k) (conv v) σ hdec hf.perm hstk' hsent hgas'),
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
      ⟨hm.mem, hm.stor, hm.tstor⟩, ?_, ?_, ?_⟩
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
    rcases args with _ | ⟨k, _ | ⟨v, _ | ⟨c, args⟩⟩⟩ <;> simp [stepOp] at hyul
    subst hyul
    show OkStep code s (opBound .tstore [k, v]) []
      { yst with transient := YulSemantics.EVM.upd yst.transient k v } pre.length 1 σ
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .tstore) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain
      (opTable_available (yop := .tstore) rfl)
    have hstk' : s.stack = conv k :: conv v :: σ := by simpa using hstk
    have hgas' : Gas.baseCost s.fork .TSTORE ≤ s.gasAvailable := by
      rw [hfork]
      have : Gas.baseCost .Osaka Operation.TSTORE ≤ 40000 := by decide
      omega
    refine ⟨_, EVM.Step.running hf.running hf.noPrecompile
      (StepRunning.tstore s (conv k) (conv v) σ hdec hf.perm hgas' hstk'),
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
  case stop =>
    rcases args with _ | ⟨a, args⟩ <;> simp [stepOp] at hyul
    subst hyul
    show HaltStep s { yst with halted := some (.stop, []) }
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .stop) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain
      (opTable_available (yop := .stop) rfl)
    exact ⟨_, EVM.Step.running hf.running hf.noPrecompile (StepRunning.stop s hdec),
      ⟨hm.mem, hm.stor, hm.tstor⟩, hf.callStack, (.stop, []), rfl, rfl⟩
  case invalid =>
    rcases args with _ | ⟨a, args⟩ <;> simp [stepOp] at hyul
    subst hyul
    show HaltStep s { yst with halted := some (.invalid, []) }
    obtain ⟨hb', hplain⟩ := opTable_roundtrip (yop := .invalid) rfl
    have hdec := decoded_op hf hcode hpc hb' hplain
      (opTable_available (yop := .invalid) rfl)
    exact ⟨_, EVM.Step.running hf.running hf.noPrecompile
      (StepRunning.invalidOpcode s hdec),
      ⟨hm.mem, hm.stor, hm.tstor⟩, hf.callStack, (.invalid, []), rfl, rfl⟩
  case ret =>
    rcases args with _ | ⟨p, _ | ⟨n, _ | ⟨c, args⟩⟩⟩ <;> simp [stepOp] at hyul
    subst hyul
    show HaltStep s { yst with
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
      ⟨hm.mem, hm.stor, hm.tstor⟩, hf.callStack,
      (.ret, YulSemantics.EVM.readBytes yst.memory p.toNat n.toNat), rfl,
      rfl, (hm.mem.readBytes p.toNat n.toNat).symm⟩
  case revert =>
    rcases args with _ | ⟨p, _ | ⟨n, _ | ⟨c, args⟩⟩⟩ <;> simp [stepOp] at hyul
    subst hyul
    show HaltStep s { yst with
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
      ⟨hm.mem, hm.stor, hm.tstor⟩, hf.callStack,
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
    ⟨hm.mem, hm.stor, hm.tstor⟩, ?_, rfl, ?_⟩
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
    ⟨hm.mem, hm.stor, hm.tstor⟩, rfl, rfl, ?_⟩
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
    ⟨hm.mem, hm.stor, hm.tstor⟩, ?_, rfl, ?_⟩
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
    ⟨hm.mem, hm.stor, hm.tstor⟩, rfl, rfl, ?_⟩
  · show s.gasAvailable - Gas.baseCost s.fork .JUMPI ≥ s.gasAvailable - 40000
    apply Nat.sub_le_sub_left
    rw [hfork]
    decide

end YulEvmCompiler
