import YulEvmCompiler.AsmSem
import YulEvmCompiler.OpStep

/-!
# YulEvmCompiler.LowerDefs

**Phase B**: the generic simulation from the Asm semantics down to the EVM
semantics of the lowered bytecode.

Fixing a program `prog` with `lowerProg prog = some is`, every reachable
Asm configuration `⟨c, σ, yst⟩` (its code a suffix of `prog`) corresponds
to EVM states `s` with

* `s.pc` at the byte position of the suffix (`codeSize prog - codeSize c` —
  well-defined because a suffix is determined by its length),
* `s.stack` the pointwise image of `σ` (`conv` on words, the *resolved
  label address* on code addresses),
* `FrameOK`/`StateMatch` as in the milestone-1/2 proof.

Each local `AStep` then maps to 1–3 EVM `Step`s (label pushes and jumps
expand to `PUSH32 addr`, `JUMP`/`JUMPI`, and the landing `JUMPDEST`). An
external call/create step instead maps to an arbitrary finite `Steps` trace
through `ExternalsRealized`. Only its endpoints are constrained, so the trace
may enter arbitrary init or runtime code, nest calls/creations, and reenter
the caller or creator.
Both cases have an existential gas bound; bounds add along `ASteps`. All gas
accounting and byte/decode arithmetic lives in this phase.
-/

namespace YulEvmCompiler

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM (U256 EvmState Op stepOp)

/-! ### The stack image -/

/-- The word a stack value lowers to: `conv` on words, the resolved byte
address on code addresses (total via `getD`; meaningful whenever the label
is defined, which `StkOK` guarantees for reachable stacks). -/
def mapAVal (prog : List Asm) : AVal → UInt256
  | .word v => conv v
  | .code l => UInt256.ofNat ((resolve l prog).getD 0)

/-- Pointwise image of an Asm stack. -/
def mapStk (prog : List Asm) (σ : List AVal) : List UInt256 :=
  σ.map (mapAVal prog)

@[simp] theorem mapStk_nil (prog : List Asm) : mapStk prog [] = [] := rfl
@[simp] theorem mapStk_cons (prog : List Asm) (v : AVal) (σ : List AVal) :
    mapStk prog (v :: σ) = mapAVal prog v :: mapStk prog σ := rfl
theorem mapStk_append (prog : List Asm) (σ τ : List AVal) :
    mapStk prog (σ ++ τ) = mapStk prog σ ++ mapStk prog τ := by
  simp [mapStk]

/-- Word blocks map to their `conv` images. -/
theorem mapStk_words (prog : List Asm) (vs : List U256) (σ : List AVal) :
    mapStk prog (words vs ++ σ) = vs.map conv ++ mapStk prog σ := by
  rw [mapStk_append]
  congr 1
  simp [mapStk, words, mapAVal]

/-- Every code address on the stack is a defined label (so `mapAVal` is
faithful). Preserved by every step; established at the empty stack. -/
def StkOK (prog : List Asm) (σ : List AVal) : Prop :=
  ∀ l, AVal.code l ∈ σ → l ∈ labelDefs prog

theorem StkOK.nil {prog : List Asm} : StkOK prog [] := by
  intro l h
  simp at h

theorem StkOK.tail {prog : List Asm} {v : AVal} {σ : List AVal}
    (h : StkOK prog (v :: σ)) : StkOK prog σ :=
  fun l hl => h l (List.mem_cons_of_mem v hl)

theorem StkOK.cons_word {prog : List Asm} {v : U256} {σ : List AVal}
    (h : StkOK prog σ) : StkOK prog (.word v :: σ) := by
  intro l hl
  rcases List.mem_cons.mp hl with hc | hc
  · exact absurd hc (by simp)
  · exact h l hc

theorem StkOK.cons_code {prog : List Asm} {l₀ : Label} {σ : List AVal}
    (h : StkOK prog σ) (hdef : l₀ ∈ labelDefs prog) :
    StkOK prog (.code l₀ :: σ) := by
  intro l hl
  rcases List.mem_cons.mp hl with hc | hc
  · obtain rfl : l₀ = l := by simpa using hc.symm
    exact hdef
  · exact h l hc

theorem StkOK.words_append {prog : List Asm} (vs : List U256) {σ : List AVal}
    (h : StkOK prog σ) : StkOK prog (words vs ++ σ) := by
  intro l hl
  rcases List.mem_append.mp hl with hc | hc
  · exact absurd hc (by simp [words])
  · exact h l hc

theorem StkOK.append_right {prog : List Asm} {τ σ : List AVal}
    (h : StkOK prog (τ ++ σ)) : StkOK prog σ :=
  fun l hl => h l (List.mem_append_right τ hl)

/-- Every step preserves the code-addresses-defined invariant (purely
Asm-side; no EVM state involved). -/
theorem AStep.stkOK [model : ExternalModel] {prog : List Asm} {a b : AConf}
    (h : AStep prog a b) (ha : StkOK prog a.stk) : StkOK prog b.stk := by
  cases h with
  | push => exact ha.cons_word
  | op _ => exact (ha.append_right).words_append _
  | @dup n v τ ρ c yst _ =>
    intro l hl
    rcases List.mem_cons.mp hl with hc | hc
    · exact ha l (by rw [hc]; exact List.mem_append_right τ (List.mem_cons_self ..))
    · exact ha l hc
  | @swap n a' b' τ ρ c yst _ =>
    intro l hl
    have hmem : ∀ v, v ∈ b' :: (τ ++ a' :: ρ) → v ∈ a' :: (τ ++ b' :: ρ) := by
      intro v hv
      rcases List.mem_cons.mp hv with h1 | h1
      · exact h1 ▸ List.mem_cons_of_mem _ (List.mem_append_right τ (List.mem_cons_self ..))
      · rcases List.mem_append.mp h1 with h2 | h2
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ h2)
        · rcases List.mem_cons.mp h2 with h3 | h3
          · exact h3 ▸ List.mem_cons_self ..
          · exact List.mem_cons_of_mem _
              (List.mem_append_right τ (List.mem_cons_of_mem _ h3))
    exact ha l (hmem _ hl)
  | pop => exact ha.tail
  | label => exact ha
  | jump _ => exact ha
  | jumpiTaken _ _ => exact ha.tail
  | jumpiFall _ => exact ha.tail
  | pushLabel hdef => exact ha.cons_code hdef
  | dynJump _ => exact ha.tail

/-! ### Locating a suffix in the lowered bytecode -/

/-- `assemble` agrees with `mkCode` on the flat byte list. -/
theorem assemble_eq_mkCode (is : List Instr) :
    assemble is = mkCode (assembleBytes is) := rfl

/-- A lowered executable prefix followed by bytes that are not part of the
symbolic program.  Yul objects use the payload for their explicit `STOP`
seam, recursively compiled children, and data segments. -/
def assembleWithPayload (is : List Instr) (payload : List UInt8) : ByteArray :=
  mkCode (assembleBytes is ++ payload)

@[simp] theorem assembleWithPayload_nil (is : List Instr) :
    assembleWithPayload is [] = assemble is := by
  rw [assemble_eq_mkCode]
  simp [assembleWithPayload]

/-- Splitting the lowered program at a code suffix `i :: c`: the bytes
decompose around `i`'s lowering, with the prefix's byte length equal to the
suffix's byte position. -/
theorem locate {prog : List Asm} {is : List Instr}
    (hlow : lowerProg prog = some is) {i : Asm} {c : List Asm}
    (hsuf : (i :: c) <:+ prog) :
    ∃ (pre : List Asm) (isPre isI isC : List Instr),
      prog = pre ++ i :: c
      ∧ lowerInstr prog i = some isI
      ∧ lowerFrag prog c = some isC
      ∧ assembleBytes is
        = assembleBytes isPre ++ assembleBytes isI ++ assembleBytes isC
      ∧ (assembleBytes isPre).length = codeSize pre
      ∧ codeSize prog = codeSize pre + i.size + codeSize c := by
  obtain ⟨pre, hpre⟩ := hsuf
  have hlow' : lowerFrag prog (pre ++ i :: c) = some is := by
    rw [hpre]; exact hlow
  obtain ⟨isPre, isRest, h1, h2, rfl⟩ := lowerFrag_append hlow'
  obtain ⟨isI, isC, hI, hC, rfl⟩ := lowerFrag_cons h2
  refine ⟨pre, isPre, isI, isC, hpre.symm, hI, hC, ?_, lowerFrag_length h1, ?_⟩
  · rw [assembleBytes_append, assembleBytes_append, List.append_assoc]
  · rw [← hpre, codeSize_append, codeSize_cons]
    omega

/-- The byte position of the label found by `findLabel`: `resolve` agrees,
the position accounts for the suffix, the lowered bytes decompose at the
label's `JUMPDEST`, and that `JUMPDEST` passes the jumpdest analysis. -/
theorem locate_label {prog : List Asm} {is : List Instr}
    (hlow : lowerProg prog = some is) {l : Label} {c' : List Asm}
    (hfind : findLabel l prog = some c') :
    ∃ (a : Nat) (isPreL isC' : List Instr),
      resolve l prog = some a
      ∧ a + 1 + codeSize c' = codeSize prog
      ∧ assembleBytes is
        = assembleBytes isPreL ++ (Instr.op .JUMPDEST).bytes
          ++ assembleBytes isC'
      ∧ (assembleBytes isPreL).length = a
      ∧ Decode.isValidJumpDest (assemble is) a = true := by
  obtain ⟨preL, hsplit, -, hres⟩ := findLabel_eq_some hfind
  have hsuf : (Asm.label l :: c') <:+ prog := ⟨preL, hsplit.symm⟩
  obtain ⟨pre, isPre, isI, isC, hsplit', hI, hC, hbytes, hlenPre, -⟩ :=
    locate hlow hsuf
  obtain rfl : [Instr.op .JUMPDEST] = isI := by
    simpa [lowerInstr] using hI
  have hpre_eq : pre = preL := by
    have heq : pre ++ Asm.label l :: c' = preL ++ Asm.label l :: c' := by
      rw [← hsplit', ← hsplit]
    have hlen : pre.length = preL.length := by
      have := congrArg List.length heq
      simpa using this
    exact List.append_inj_left heq (by simpa using hlen)
  subst hpre_eq
  have hJ : assembleBytes [Instr.op .JUMPDEST] = (Instr.op .JUMPDEST).bytes := by
    simp
  refine ⟨codeSize pre, isPre, isC, hres, ?_, by rw [hbytes, hJ], hlenPre, ?_⟩
  · rw [hsplit, codeSize_append, codeSize_cons]
    simp [Asm.size]
    omega
  · have hvalid := isValidJumpDest_boundary isPre (assembleBytes isC)
    rw [assemble_eq_mkCode, hbytes, hJ, ← hlenPre]
    exact hvalid

/-- `locate_label`, with the valid-jump-destination fact checked in a full
object bytecode image. Appending a payload cannot change decoding at a label
inside the lowered executable prefix. -/
theorem locate_label_withPayload {prog : List Asm} {is : List Instr}
    (hlow : lowerProg prog = some is) {l : Label} {c' : List Asm}
    (hfind : findLabel l prog = some c') (payload : List UInt8) :
    ∃ (a : Nat) (isPreL isC' : List Instr),
      resolve l prog = some a
      ∧ a + 1 + codeSize c' = codeSize prog
      ∧ assembleBytes is
        = assembleBytes isPreL ++ (Instr.op .JUMPDEST).bytes
          ++ assembleBytes isC'
      ∧ (assembleBytes isPreL).length = a
      ∧ Decode.isValidJumpDest (assembleWithPayload is payload) a = true := by
  obtain ⟨a, isPreL, isC', hres, hpos, hbytes, hlen, -⟩ :=
    locate_label hlow hfind
  refine ⟨a, isPreL, isC', hres, hpos, hbytes, hlen, ?_⟩
  have hvalid := isValidJumpDest_boundary isPreL (assembleBytes isC' ++ payload)
  rw [assembleWithPayload, hbytes, ← hlen]
  simpa only [List.append_assoc] using hvalid

/-! ### Small arithmetic helpers (local copies; the originals live in the
milestone-2 `Correctness.lean`, which this pipeline replaces) -/

theorem conv_ofNat' (n : Nat) :
    conv (BitVec.ofNat 256 n) = UInt256.ofNat n := by
  apply u256ext
  rw [conv_toNat, toNat_u256_ofNat]
  simp

private theorem le_of_add_le' {x y z : Nat} (h : x + y ≤ z) : x ≤ z :=
  Nat.le_trans (Nat.le_add_right x y) h

/-- Chain two "consumed at most `k` gas" bounds. Pure-term chaining lemmas
are used instead of `omega` at the multi-step use sites — `omega` is
unreliable in those large contexts. -/
theorem gasChain₂' {a b c k₁ k₂ : Nat}
    (h₁ : a - k₁ ≤ b) (h₂ : b - k₂ ≤ c) : a - (k₁ + k₂) ≤ c := by
  omega

/-- Chain three "consumed at most `k` gas" bounds. -/
theorem gasChain₃' {a b c d k₁ k₂ k₃ : Nat}
    (h₁ : a - k₁ ≤ b) (h₂ : b - k₂ ≤ c) (h₃ : c - k₃ ≤ d) :
    a - (k₁ + k₂ + k₃) ≤ d := by
  omega

/-- Setting at the seam of an append replaces the head of the right part. -/
theorem set_at_append {α : Type} (τ : List α) (y x : α) (ρ : List α) :
    (τ ++ y :: ρ).set τ.length x = τ ++ x :: ρ := by
  induction τ with
  | nil => rfl
  | cons t τ ih =>
    show t :: (τ ++ y :: ρ).set τ.length x = _
    rw [ih]
    rfl

/-- The `SWAP` list surgery, in the shape the Asm `swap` rule uses. -/
theorem exchange_swap {α : Type} (x y : α) (τ ρ : List α) :
    List.exchange (x :: (τ ++ y :: ρ)) 0 (τ.length + 1)
      = some (y :: (τ ++ x :: ρ)) := by
  have h1 : (x :: (τ ++ y :: ρ))[τ.length + 1]? = some y := by
    show (τ ++ y :: ρ)[τ.length]? = some y
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  unfold List.exchange
  rw [show (x :: (τ ++ y :: ρ))[0]? = some x from rfl, h1]
  show some (((x :: (τ ++ y :: ρ)).set 0 y).set (τ.length + 1) x) = _
  congr 1
  show y :: ((τ ++ y :: ρ).set τ.length x) = _
  rw [set_at_append]

/-! ### The configuration correspondence -/

/-- The phase-B invariant between an Asm configuration and an EVM state
running the lowered bytecode. -/
structure ConfMatch (prog : List Asm) (is : List Instr) (a : AConf)
    (s : State) (payload : List UInt8 := []) : Prop where
  frame : FrameOK (assembleWithPayload is payload) s
  smatch : StateMatch a.yst s
  pc : s.pc = UInt256.ofNat (codeSize prog - codeSize a.code)
  stack : s.stack = mapStk prog a.stk

/-! ### Open-world call and creation realization

The source semantics deliberately does not choose a callee implementation.
Instead, `CallsRealized external` says that every response admitted by the
source relation is realized by a *complete* target call-and-return execution.
Only the two endpoints are constrained.  In particular, the `Steps` witness
has no invariant requiring an empty call stack between them: it may enter
arbitrary contracts, make nested calls, and re-enter this caller any number of
times before the original call returns. `CreatesRealized` below imposes the
same endpoint-only discipline on arbitrary init-code executions. -/

/-- Target realization of an open-world source call relation.  The restored
endpoint is again the original running frame with an empty call stack, the
source-selected response installed, and its success flag on the stack. -/
structure CallsRealized (external : YulSemantics.EVM.ExternalCalls) : Prop where
  call {yop : Op} (hcall : IsCallOp yop) {o : Operation}
      (hop : opTable yop = some o) {args rets : List U256}
      {yst yst' : EvmState}
      (hsource : YulSemantics.EVM.builtin external yop args yst (.ok rets yst')) :
      ∃ bnd : Nat, ∀ {code : ByteArray} {s : State} {σ : List UInt256},
        FrameOK code s → StateMatch yst s →
        s.decodedOp = some o → s.stack = args.map conv ++ σ →
        bnd ≤ s.gasAvailable →
        ∃ s', Steps s s' ∧ FrameOK code s' ∧ StateMatch yst' s' ∧
          s'.pc = s.pc.succ ∧ s'.stack = rets.map conv ++ σ ∧
          s.gasAvailable - bnd ≤ s'.gasAvailable

/-- The theorem-facing form of call realization.  Its trace is deliberately
unrestricted at intermediate states, which is the formal reason reentrant
executions are included in compiler correctness. -/
theorem CallsRealized.complete_allows_reentrancy
    {external : YulSemantics.EVM.ExternalCalls} (h : CallsRealized external)
    {yop : Op} (hcall : IsCallOp yop) {o : Operation}
    (hop : opTable yop = some o) {args rets : List U256} {yst yst' : EvmState}
    (hsource : YulSemantics.EVM.builtin external yop args yst (.ok rets yst')) :
    ∃ bnd : Nat, ∀ {code : ByteArray} {s : State} {σ : List UInt256},
      FrameOK code s → StateMatch yst s →
      s.decodedOp = some o → s.stack = args.map conv ++ σ →
      bnd ≤ s.gasAvailable →
      ∃ s', Steps s s' ∧ FrameOK code s' ∧ StateMatch yst' s' ∧
        s'.pc = s.pc.succ ∧ s'.stack = rets.map conv ++ σ ∧
        s.gasAvailable - bnd ≤ s'.gasAvailable :=
  h.call hcall hop hsource

/-- The empty external relation is realized vacuously: no source call can
choose a response. This recovers the pre-call executable-dialect theorems. -/
theorem CallsRealized.none :
    CallsRealized YulSemantics.EVM.ExternalCalls.none := by
  constructor
  intro yop hcall o hop args rets yst yst' hsource
  cases yop <;>
    simp [IsCallOp, YulSemantics.EVM.builtin,
      YulSemantics.EVM.builtinWithExternal, YulSemantics.EVM.externalCall,
      YulSemantics.EVM.ExternalCalls.none] at hcall hsource
  all_goals split at hsource <;> contradiction

/-- Target realization of an open-world source CREATE/CREATE2 relation. The
finite target trace is intentionally unrestricted between its endpoints: it
may execute arbitrary init code, call arbitrary contracts, and re-enter the
creator before returning to the instruction after CREATE. -/
structure CreatesRealized (external : YulSemantics.EVM.ExternalCreates) : Prop where
  create {yop : Op} (hcreate : IsCreateOp yop) {o : Operation}
      (hop : opTable yop = some o) {args rets : List U256}
      {yst yst' : EvmState}
      (hsource : YulSemantics.EVM.builtinWithExternal
        YulSemantics.EVM.ExternalCalls.none external yop args yst (.ok rets yst')) :
      ∃ bnd : Nat, ∀ {code : ByteArray} {s : State} {σ : List UInt256},
        FrameOK code s → StateMatch yst s →
        s.decodedOp = some o → s.stack = args.map conv ++ σ →
        bnd ≤ s.gasAvailable →
        ∃ s', Steps s s' ∧ FrameOK code s' ∧ StateMatch yst' s' ∧
          s'.pc = s.pc.succ ∧ s'.stack = rets.map conv ++ σ ∧
          s.gasAvailable - bnd ≤ s'.gasAvailable

/-- The unrestricted realization premise is the formal coverage point for
arbitrary init-code behavior, including nested calls and reentrancy. -/
theorem CreatesRealized.complete_allows_initcode_reentrancy
    {external : YulSemantics.EVM.ExternalCreates} (h : CreatesRealized external)
    {yop : Op} (hcreate : IsCreateOp yop) {o : Operation}
    (hop : opTable yop = some o) {args rets : List U256} {yst yst' : EvmState}
    (hsource : YulSemantics.EVM.builtinWithExternal
      YulSemantics.EVM.ExternalCalls.none external yop args yst (.ok rets yst')) :
    ∃ bnd : Nat, ∀ {code : ByteArray} {s : State} {σ : List UInt256},
      FrameOK code s → StateMatch yst s →
      s.decodedOp = some o → s.stack = args.map conv ++ σ →
      bnd ≤ s.gasAvailable →
      ∃ s', Steps s s' ∧ FrameOK code s' ∧ StateMatch yst' s' ∧
        s'.pc = s.pc.succ ∧ s'.stack = rets.map conv ++ σ ∧
        s.gasAvailable - bnd ≤ s'.gasAvailable :=
  h.create hcreate hop hsource

/-- No CREATE response can be selected from the empty relation. -/
theorem CreatesRealized.none :
    CreatesRealized YulSemantics.EVM.ExternalCreates.none := by
  constructor
  intro yop hcreate o hop args rets yst yst' hsource
  cases yop <;>
    simp [IsCreateOp, YulSemantics.EVM.builtinWithExternal,
      YulSemantics.EVM.externalCreate,
      YulSemantics.EVM.ExternalCreates.none] at hcreate hsource
  all_goals split at hsource <;> contradiction

/-- The complete open-world obligations used by compiler correctness. Calls
and creations are separated so clients can instantiate either relation
independently while the compiler theorem quantifies over both. -/
structure ExternalsRealized (model : ExternalModel) : Prop where
  calls : CallsRealized model.calls
  creates : CreatesRealized model.creates

/-- The fully closed executable model has no external transitions. -/
theorem ExternalsRealized.none :
    ExternalsRealized
      { calls := YulSemantics.EVM.ExternalCalls.none
        creates := YulSemantics.EVM.ExternalCreates.none } :=
  ⟨CallsRealized.none, CreatesRealized.none⟩

/-! ### A non-trivial realized model: the insufficient-balance CALL failure

`ExternalsRealized.none` satisfies the open-world interface only *vacuously*
(its source relation admits no response). The model below is genuinely
non-empty: it admits, for a value-bearing `call` whose caller cannot afford the
transferred value, exactly the immediate-fail response the EVM performs — push
`0`, expose no return data, leave the world unchanged. This is realized by a
single real evm-semantics `StepRunning.callFail` step (no callee frame, no
`StepReturn`), so the interface is demonstrably inhabited by a real EVM
behavior.

Fully general realization (arbitrary callee execution and reentrancy) remains
the client's responsibility, as documented; this witness discharges the
insufficient-balance `.call` failure class only. -/

/-- `activeWordsAfter` factors through the empty high-water mark: touching a
range from `curr` is `curr` joined with touching it from `0`. -/
private theorem activeWordsAfter_split (curr offset size : Nat) :
    MachineState.activeWordsAfter curr offset size
      = Nat.max curr (MachineState.activeWordsAfter 0 offset size) := by
  unfold MachineState.activeWordsAfter
  by_cases h : size = 0 <;> simp [h]

/-- The two-range high-water mark factors the same way. -/
private theorem activeWordsAfter2_split (curr o1 s1 o2 s2 : Nat) :
    MachineState.activeWordsAfter (MachineState.activeWordsAfter curr o1 s1) o2 s2
      = Nat.max curr
          (MachineState.activeWordsAfter (MachineState.activeWordsAfter 0 o1 s1) o2 s2) := by
  rw [activeWordsAfter_split (MachineState.activeWordsAfter curr o1 s1) o2 s2,
      activeWordsAfter_split curr o1 s1,
      activeWordsAfter_split (MachineState.activeWordsAfter 0 o1 s1) o2 s2]
  exact Nat.max_assoc _ _ _

/-- Memory-expansion gas for a fixed range is bounded independently of the
current high-water mark: expanding *from* `curr` never costs more than
building the range *from* `0`. -/
private theorem memExpansionDelta2_le (curr o1 s1 o2 s2 : Nat) :
    MachineState.memExpansionDelta2 curr o1 s1 o2 s2
      ≤ MachineState.memCost
          (MachineState.activeWordsAfter (MachineState.activeWordsAfter 0 o1 s1) o2 s2) := by
  unfold MachineState.memExpansionDelta2
  rw [activeWordsAfter2_split]
  set M := MachineState.activeWordsAfter (MachineState.activeWordsAfter 0 o1 s1) o2 s2 with hM
  rcases Nat.le_total curr M with h | h
  · simp only [Nat.max_eq_right h]; exact Nat.sub_le _ _
  · simp only [Nat.max_eq_left h, Nat.sub_self]; exact Nat.zero_le _

/-- Every additive component of `Gas.callCommitted` is bounded by a fixed
constant plus the (state-independent) memory-expansion ceiling. On the pinned
Osaka fork the base fee is `100`; the value/new-account surcharge is at most
`9000 + 25000`, the cold-account surcharge at most `2500`, and the EIP-7702
delegate-access cost at most `2600`. -/
private theorem callCommitted_le (s : State) (hfork : s.executionEnv.fork = .Osaka)
    (value argsOff argsLen retOff retLen toArg : EvmSemantics.UInt256) :
    Gas.callCommitted s value argsOff argsLen retOff retLen toArg
      ≤ 39200 + MachineState.memCost
          (MachineState.activeWordsAfter
            (MachineState.activeWordsAfter 0 argsOff.toNat argsLen.toNat)
            retOff.toNat retLen.toNat) := by
  have hbase : Gas.baseCost s.executionEnv.fork .CALL ≤ 100 := by rw [hfork]; decide
  have hmem := memExpansionDelta2_le s.activeWords.toNat argsOff.toNat argsLen.toNat
    retOff.toNat retLen.toNat
  have hsur : Gas.callSurcharge s.executionEnv.fork (value.toNat != 0)
      (Gas.callTargetIsNew s.executionEnv.fork s.accountMap
        (AccountAddress.ofUInt256 toArg)) ≤ 34000 := by
    simp only [Gas.callSurcharge]; split_ifs <;> omega
  have hcold : Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg) ≤ 2500 := by
    unfold Gas.accountColdSurcharge; split_ifs <;> omega
  have hdel : Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg) ≤ 2600 := by
    unfold Gas.delegationAccessCost
    split <;> first | (split_ifs <;> omega) | omega
  rw [show Gas.callCommitted s value argsOff argsLen retOff retLen toArg
      = Gas.baseCost s.executionEnv.fork .CALL
        + MachineState.memExpansionDelta2 s.activeWords.toNat
            argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
        + (Gas.callSurcharge s.executionEnv.fork (value.toNat != 0)
              (Gas.callTargetIsNew s.executionEnv.fork s.accountMap
                (AccountAddress.ofUInt256 toArg))
            + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
            + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)) from rfl]
  omega

/-- The non-empty call relation: a value-bearing `call` that the caller cannot
afford fails immediately (`success = false`, empty return data, world equal to
the pre-call world projection). Restricting to the insufficient-balance case is
what lets the failure be observed from the *source* state (the EVM's other
silent-fail trigger, the 1024-frame depth limit, is invisible to this
relation). -/
def insufficientBalanceCalls : YulSemantics.EVM.ExternalCalls where
  Call := fun req st resp =>
    req.kind = YulSemantics.EVM.CallKind.call ∧
    st.env.selfBalance.toNat < req.value.toNat ∧
    resp.success = false ∧
    resp.returndata = [] ∧
    resp.world = YulSemantics.EVM.CallWorld.ofState st

/-- The non-trivial model: the insufficient-balance CALL failure relation for
calls, and no creations. -/
@[reducible] def insufficientBalanceModel : ExternalModel where
  calls := insufficientBalanceCalls
  creates := YulSemantics.EVM.ExternalCreates.none

/-- `conv` is strictly monotone (it preserves `toNat`). -/
private theorem conv_lt_of_toNat {a b : U256} (h : a.toNat < b.toNat) :
    conv a < conv b := h

/-- The insufficient-balance CALL relation is realized by a single real
evm-semantics `StepRunning.callFail` step. This is the first genuinely
non-vacuous instance of `CallsRealized` proved in-repo. -/
theorem CallsRealized.insufficientBalance :
    CallsRealized insufficientBalanceCalls := by
  constructor
  intro yop hcall o hop args rets yst yst' hsource
  -- The relation only fires on `.call`; narrow `yop` to the four call ops.
  have hkinds : yop = .call ∨ yop = .callcode ∨ yop = .delegatecall ∨ yop = .staticcall := by
    cases yop <;> simp_all [IsCallOp]
  rcases hkinds with rfl | rfl | rfl | rfl
  · -- `.call`: the genuine witness.
    have hoCALL : o = .CALL := by
      have h : opTable Op.call = some Operation.CALL := rfl
      rw [h] at hop; exact (Option.some.inj hop).symm
    subst hoCALL
    -- Reduce to the exactly-seven-argument shape; every other shape is `False`.
    rcases args with _ | ⟨gas, _ | ⟨target, _ | ⟨value, _ | ⟨inOff, _ | ⟨inSize,
      _ | ⟨outOff, _ | ⟨outSize, _ | ⟨x, xs⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      simp only [YulSemantics.EVM.builtin, YulSemantics.EVM.builtinWithExternal] at hsource
    -- One goal remains: `if static ∧ value ≠ 0 then _ = .halt else externalCall …`.
    split at hsource
    · exact absurd hsource (by simp)
    · unfold YulSemantics.EVM.externalCall at hsource
      obtain ⟨response, hCall, heq⟩ := hsource
      injection heq with hrets hyst'
      obtain ⟨-, hbal, hsucc, hrdata, -⟩ := hCall
      subst hyst'
      subst hrets
      refine ⟨39200 + MachineState.memCost
        (MachineState.activeWordsAfter
          (MachineState.activeWordsAfter 0 inOff.toNat inSize.toNat)
          outOff.toNat outSize.toNat), ?_⟩
      intro code s σ hf hm hdec hstk hbnd
      simp only [List.map_cons, List.map_nil, List.cons_append,
        List.nil_append] at hstk
      have hccbound : Gas.callCommitted s (conv value) (conv inOff) (conv inSize)
          (conv outOff) (conv outSize) (conv target)
          ≤ 39200 + MachineState.memCost
              (MachineState.activeWordsAfter
                (MachineState.activeWordsAfter 0 inOff.toNat inSize.toNat)
                outOff.toNat outSize.toNat) := by
        have := callCommitted_le s hf.fork (conv value) (conv inOff) (conv inSize)
          (conv outOff) (conv outSize) (conv target)
        simpa only [conv_toNat] using this
      have hgas : Gas.callCommitted s (conv value) (conv inOff) (conv inSize)
          (conv outOff) (conv outSize) (conv target) ≤ s.gasAvailable :=
        le_trans hccbound hbnd
      have h_afford : Gas.forwardGas s.executionEnv.fork
          (s.gasAvailable - Gas.callCommitted s (conv value) (conv inOff) (conv inSize)
            (conv outOff) (conv outSize) (conv target)) (conv gas).toNat
          ≤ s.gasAvailable - Gas.callCommitted s (conv value) (conv inOff) (conv inSize)
            (conv outOff) (conv outSize) (conv target) := by
        rw [hf.fork]
        unfold Gas.forwardGas
        rw [if_pos (by decide)]
        exact le_trans (Nat.min_le_right _ _) (Nat.sub_le _ _)
      have h_fail : s.executionEnv.depth ≥ 1024 ∨
          (s.accountMap s.executionEnv.address).balance < conv value :=
        Or.inr (by rw [← hm.selfBalance]; exact conv_lt_of_toNat hbal)
      have hstep := StepRunning.callFail s (conv gas) (conv target) (conv value)
        (conv inOff) (conv inSize) (conv outOff) (conv outSize) σ hdec hstk hgas
        h_afford h_fail
      refine ⟨_, Steps.trans (Step.running hf.running hf.noPrecompile hstep)
        (Steps.refl _), ?_, ?_, ?_, ?_, ?_⟩
      · -- FrameOK
        exact ⟨hf.hcode, hf.codeSmall, hf.fork, hf.noPrecompile, hf.callStack, hf.running⟩
      · -- StateMatch
        have hcopy : YulSemantics.EVM.copyReturn yst.memory outOff.toNat outSize.toNat []
            = yst.memory := by
          funext a
          show (if outOff.toNat ≤ a ∧ a < outOff.toNat + min outSize.toNat [].length
            then _ else yst.memory a) = yst.memory a
          rw [if_neg (by rintro ⟨h1, h2⟩; simp only [List.length_nil, Nat.min_zero,
            Nat.add_zero] at h2; omega)]
        have hwarm : ∀ {α : Type} (f : Substate → α),
            (∀ A a, f (Substate.addAccessedAccount A a) = f A) →
            f (State.warmCallTarget s s.substate (AccountAddress.ofUInt256 (conv target)))
              = f s.substate := by
          intro α f hf'
          unfold State.warmCallTarget Substate.addAccessedAccountOpt
          cases s.delegateOf (AccountAddress.ofUInt256 (conv target)) <;>
            simp only [hf']
        refine {
          mem := ?_, stor := ?_, tstor := ?_, cd := ?_, env := ?_, codeBytes := ?_,
          codeLen := ?_, selfBalance := ?_, balanceOf := ?_, activeWords := ?_,
          retData := ?_, retDataLen := ?_, externalCode := ?_, logs := ?_,
          selfdestructs := ?_, createdThisTx := ?_ }
        · simp only [YulSemantics.EVM.finishCall, hsucc, hrdata, Bool.false_eq_true,
            false_and, if_false]
          rw [hcopy]; exact hm.mem
        · simp only [YulSemantics.EVM.finishCall, YulSemantics.EVM.touchMemory2,
            YulSemantics.EVM.touchMemory, hsucc, hrdata, Bool.false_eq_true,
            false_and, if_false]
          exact hm.stor
        · simp only [YulSemantics.EVM.finishCall, YulSemantics.EVM.touchMemory2,
            YulSemantics.EVM.touchMemory, hsucc, hrdata, Bool.false_eq_true,
            false_and, if_false]
          exact hm.tstor
        · simp only [YulSemantics.EVM.finishCall, YulSemantics.EVM.touchMemory2,
            YulSemantics.EVM.touchMemory, hsucc, hrdata, Bool.false_eq_true,
            false_and, if_false]
          exact hm.cd
        · simp only [YulSemantics.EVM.finishCall, YulSemantics.EVM.touchMemory2,
            YulSemantics.EVM.touchMemory, hsucc, hrdata, Bool.false_eq_true,
            false_and, if_false]
          exact hm.env
        · simp only [YulSemantics.EVM.finishCall, YulSemantics.EVM.touchMemory2,
            YulSemantics.EVM.touchMemory, hsucc, hrdata, Bool.false_eq_true,
            false_and, if_false]
          exact hm.codeBytes
        · simp only [YulSemantics.EVM.finishCall, YulSemantics.EVM.touchMemory2,
            YulSemantics.EVM.touchMemory, hsucc, hrdata, Bool.false_eq_true,
            false_and, if_false]
          exact hm.codeLen
        · simp only [YulSemantics.EVM.finishCall, YulSemantics.EVM.touchMemory2,
            YulSemantics.EVM.touchMemory, hsucc, hrdata, Bool.false_eq_true,
            false_and, if_false]
          exact hm.selfBalance
        · simp only [YulSemantics.EVM.finishCall, YulSemantics.EVM.touchMemory2,
            YulSemantics.EVM.touchMemory, hsucc, hrdata, Bool.false_eq_true,
            false_and, if_false]
          exact hm.balanceOf
        · simp only [YulSemantics.EVM.finishCall, hsucc, hrdata, Bool.false_eq_true,
            false_and, if_false]
          show conv (YulSemantics.EVM.touchMemory2 yst inOff.toNat inSize.toNat
            outOff.toNat outSize.toNat).activeWords = _
          simp only [conv_toNat]
          exact activeWordsAfter2_eq hm.activeWords inOff.toNat inSize.toNat
            outOff.toNat outSize.toNat inOff.isLt inSize.isLt
        · simp only [YulSemantics.EVM.finishCall, hsucc, hrdata, Bool.false_eq_true,
            false_and, if_false]
          have hbf : YulSemantics.EVM.byteFrom ([] : List UInt8) = fun _ => (0 : UInt8) := by
            funext a; simp [YulSemantics.EVM.byteFrom]
          rw [hbf]; exact MemMatch.init
        · simp only [YulSemantics.EVM.finishCall, hsucc, hrdata, Bool.false_eq_true,
            false_and, if_false, List.length_nil, ByteArray.size_empty]
        · simp only [YulSemantics.EVM.finishCall, YulSemantics.EVM.touchMemory2,
            YulSemantics.EVM.touchMemory, hsucc, hrdata, Bool.false_eq_true,
            false_and, if_false]
          exact hm.externalCode
        · simp only [YulSemantics.EVM.finishCall, YulSemantics.EVM.touchMemory2,
            YulSemantics.EVM.touchMemory, hsucc, hrdata, Bool.false_eq_true,
            false_and, if_false]
          rw [hwarm (fun A => A.logSeries) (fun _ _ => rfl)]
          exact hm.logs
        · simp only [YulSemantics.EVM.finishCall, YulSemantics.EVM.touchMemory2,
            YulSemantics.EVM.touchMemory, hsucc, hrdata, Bool.false_eq_true,
            false_and, if_false]
          rw [hwarm (fun A => A.selfDestructList) (fun _ _ => rfl),
            hwarm (fun A => A.originalAccountMap) (fun _ _ => rfl)]
          exact hm.selfdestructs
        · simp only [YulSemantics.EVM.finishCall, YulSemantics.EVM.touchMemory2,
            YulSemantics.EVM.touchMemory, hsucc, hrdata, Bool.false_eq_true,
            false_and, if_false]
          rw [hwarm (fun A => A.originalAccountMap) (fun _ _ => rfl)]
          exact hm.createdThisTx
      · rfl
      · -- stack
        show UInt256.ofNat 0 :: σ = List.map conv [response.flag] ++ σ
        have hf0 : response.flag = (0 : U256) := by
          simp [YulSemantics.EVM.CallResponse.flag, hsucc]
        rw [hf0]; rfl
      · -- gas bound
        show s.gasAvailable - (39200 + MachineState.memCost
            (MachineState.activeWordsAfter
              (MachineState.activeWordsAfter 0 inOff.toNat inSize.toNat)
              outOff.toNat outSize.toNat))
          ≤ s.gasAvailable - Gas.callCommitted s (conv value) (conv inOff) (conv inSize)
              (conv outOff) (conv outSize) (conv target)
            + (bif (conv value).toNat != 0 then Gas.callStipend else 0)
        have hb0 : 0 ≤ (bif (conv value).toNat != 0 then Gas.callStipend else 0) :=
          Nat.zero_le _
        omega
  · -- `.callcode`: `req.kind = .callcode ≠ .call`, contradiction.
    exfalso
    rcases args with _ | ⟨gas, _ | ⟨target, _ | ⟨value, _ | ⟨inOff, _ | ⟨inSize,
      _ | ⟨outOff, _ | ⟨outSize, _ | ⟨x, xs⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      simp only [YulSemantics.EVM.builtin, YulSemantics.EVM.builtinWithExternal,
        YulSemantics.EVM.externalCall, insufficientBalanceCalls] at hsource
    obtain ⟨response, hCall, -⟩ := hsource
    exact absurd hCall.1 (by decide)
  · -- `.delegatecall`
    exfalso
    rcases args with _ | ⟨gas, _ | ⟨target, _ | ⟨inOff, _ | ⟨inSize,
      _ | ⟨outOff, _ | ⟨outSize, _ | ⟨x, xs⟩⟩⟩⟩⟩⟩⟩ <;>
      simp only [YulSemantics.EVM.builtin, YulSemantics.EVM.builtinWithExternal,
        YulSemantics.EVM.externalCall, insufficientBalanceCalls] at hsource
    obtain ⟨response, hCall, -⟩ := hsource
    exact absurd hCall.1 (by decide)
  · -- `.staticcall`
    exfalso
    rcases args with _ | ⟨gas, _ | ⟨target, _ | ⟨inOff, _ | ⟨inSize,
      _ | ⟨outOff, _ | ⟨outSize, _ | ⟨x, xs⟩⟩⟩⟩⟩⟩⟩ <;>
      simp only [YulSemantics.EVM.builtin, YulSemantics.EVM.builtinWithExternal,
        YulSemantics.EVM.externalCall, insufficientBalanceCalls] at hsource
    obtain ⟨response, hCall, -⟩ := hsource
    exact absurd hCall.1 (by decide)

/-- The non-trivial model satisfies the full open-world obligations: its call
relation is realized by a real EVM `callFail` trace, and it has no creations.
This exhibits a demonstrably inhabited (non-vacuous) `ExternalsRealized`. -/
theorem ExternalsRealized.insufficientBalanceCall :
    ExternalsRealized insufficientBalanceModel :=
  ⟨CallsRealized.insufficientBalance, CreatesRealized.none⟩

/-- The lowered program's byte size is `codeSize prog` (bounded by the
frame invariant). -/
theorem codeSize_lt {prog : List Asm} {is : List Instr} {payload : List UInt8}
    (hlow : lowerProg prog = some is) {s : State}
    (hf : FrameOK (assembleWithPayload is payload) s) : codeSize prog < 2 ^ 256 := by
  have h := hf.codeSmall
  rw [assembleWithPayload, size_mkCode, List.length_append,
    lowerFrag_length hlow] at h
  omega

/-- Falling through the executable prefix of an object executes its explicit
`STOP` seam. Bytes after that seam are unreachable on normal fall-through. -/
theorem stopSeamStep {is : List Instr} {payload : List UInt8}
    {yst : EvmState} {s : State}
    (hf : FrameOK (assembleWithPayload is (0 :: payload)) s)
    (hm : StateMatch yst s)
    (hpc : s.pc = UInt256.ofNat (assembleBytes is).length) :
    ∃ s', EVM.Step s s' ∧ StateMatch yst s' ∧ s'.callStack = []
      ∧ s'.halt = .Success ∧ s'.hReturn = .empty := by
  have hcode : assembleWithPayload is (0 :: payload) =
      mkCode (assembleBytes is ++ (Instr.op .STOP).bytes ++ payload) := by
    simp [assembleWithPayload, Instr.bytes, Instr.opByte, List.append_assoc]
  have hdec : s.decodedOp = some .STOP := by
    exact decoded_op hf hcode hpc (by decide) trivial (by decide)
  exact ⟨_, EVM.Step.running hf.running hf.noPrecompile (StepRunning.stop s hdec),
    ⟨hm.mem, hm.stor, hm.tstor, hm.cd, hm.env, hm.codeBytes, hm.codeLen,
        hm.selfBalance, hm.balanceOf, hm.activeWords, hm.retData, hm.retDataLen,
        hm.externalCode, hm.logs, hm.selfdestructs, hm.createdThisTx⟩,
    hf.callStack, rfl, rfl⟩

/-! ### Reshaping the located bytes for the per-instruction step lemmas

`congr` is avoided on purpose: its up-front definitional-equality check
diverges on `PUSH32` byte terms (`natToBE` unfolding); `congrArg` plus a
targeted `simp only` never looks inside the bytes. -/

/-- A one-instruction fragment, in the `pre ++ instr ++ post` shape the
`OpStep` lemmas consume. -/
theorem assemble_at₁ {is isPre isC : List Instr} {i : Instr}
    (hbytes : assembleBytes is
      = assembleBytes isPre ++ assembleBytes [i] ++ assembleBytes isC) :
    assemble is = mkCode (assembleBytes isPre ++ i.bytes ++ assembleBytes isC) := by
  rw [assemble_eq_mkCode, hbytes]
  refine congrArg mkCode ?_
  simp only [assembleBytes_cons, assembleBytes_nil, List.append_nil]

/-- A two-instruction fragment, shaped around its *first* instruction. -/
theorem assemble_at₂ {is isPre isC : List Instr} {i j : Instr}
    (hbytes : assembleBytes is
      = assembleBytes isPre ++ assembleBytes [i, j] ++ assembleBytes isC) :
    assemble is
      = mkCode (assembleBytes isPre ++ i.bytes ++ (j.bytes ++ assembleBytes isC)) := by
  rw [assemble_eq_mkCode, hbytes]
  refine congrArg mkCode ?_
  simp only [assembleBytes_cons, assembleBytes_nil, List.append_nil,
    List.append_assoc]

/-- A two-instruction fragment, shaped around its *second* instruction. -/
theorem assemble_at₂' {is isPre isC : List Instr} {i j : Instr}
    (hbytes : assembleBytes is
      = assembleBytes isPre ++ assembleBytes [i, j] ++ assembleBytes isC) :
    assemble is
      = mkCode ((assembleBytes isPre ++ i.bytes) ++ j.bytes ++ assembleBytes isC) := by
  rw [assemble_eq_mkCode, hbytes]
  refine congrArg mkCode ?_
  simp only [assembleBytes_cons, assembleBytes_nil, List.append_nil,
    List.append_assoc]

/-- A one-instruction location inside an executable prefix with trailing
payload. -/
theorem assembleWithPayload_at₁ {is isPre isC : List Instr} {i : Instr}
    (hbytes : assembleBytes is
      = assembleBytes isPre ++ assembleBytes [i] ++ assembleBytes isC)
    (payload : List UInt8) :
    assembleWithPayload is payload =
      mkCode (assembleBytes isPre ++ i.bytes ++ (assembleBytes isC ++ payload)) := by
  unfold assembleWithPayload
  rw [hbytes]
  refine congrArg mkCode ?_
  simp only [assembleBytes_cons, assembleBytes_nil, List.append_nil,
    List.append_assoc]

/-- A two-instruction location, shaped around the first instruction, inside
an executable prefix with trailing payload. -/
theorem assembleWithPayload_at₂ {is isPre isC : List Instr} {i j : Instr}
    (hbytes : assembleBytes is
      = assembleBytes isPre ++ assembleBytes [i, j] ++ assembleBytes isC)
    (payload : List UInt8) :
    assembleWithPayload is payload =
      mkCode (assembleBytes isPre ++ i.bytes ++
        (j.bytes ++ assembleBytes isC ++ payload)) := by
  unfold assembleWithPayload
  rw [hbytes]
  refine congrArg mkCode ?_
  simp only [assembleBytes_cons, assembleBytes_nil, List.append_nil,
    List.append_assoc]

/-- A two-instruction location, shaped around the second instruction, inside
an executable prefix with trailing payload. -/
theorem assembleWithPayload_at₂' {is isPre isC : List Instr} {i j : Instr}
    (hbytes : assembleBytes is
      = assembleBytes isPre ++ assembleBytes [i, j] ++ assembleBytes isC)
    (payload : List UInt8) :
    assembleWithPayload is payload =
      mkCode ((assembleBytes isPre ++ i.bytes) ++ j.bytes ++
        (assembleBytes isC ++ payload)) := by
  unfold assembleWithPayload
  rw [hbytes]
  refine congrArg mkCode ?_
  simp only [assembleBytes_cons, assembleBytes_nil, List.append_nil,
    List.append_assoc]

end YulEvmCompiler
