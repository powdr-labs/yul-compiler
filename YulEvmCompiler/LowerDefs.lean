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

Each `AStep` then maps to 1–3 EVM `Step`s (label pushes and jumps expand to
`PUSH32 addr`, `JUMP`/`JUMPI`, and the landing `JUMPDEST`), with an
existential gas bound; bounds add along `ASteps`. All gas accounting and
all byte/decode arithmetic of the compiler correctness proof lives in this
file — phase A never sees it.
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
theorem AStep.stkOK {prog : List Asm} {a b : AConf}
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
        hm.selfBalance, hm.balanceOf⟩,
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
