import YulEvmCompiler.Asm

/-!
# YulEvmCompiler.AsmSem

The small-step semantics of the labeled assembly layer.

A configuration holds the **remaining code** (always a suffix of the whole
program `prog`, which parameterizes the step relation), an operand stack of
`AVal`s, and the *Yul-side* machine state (`YulSemantics.EVM.EvmState`).
Built-ins step by the Yul dialect's `stepOp`, so the Yul→Asm simulation
(phase A) needs no per-op value agreements, no gas, and no byte positions —
jumps resolve labels to code suffixes via `findLabel`.

Stack values are either words or **opaque code addresses** (`AVal.code l`,
pushed by `pushLabel`, consumed by `dynJump` — the function-call return
convention). Compiled code never feeds a code address to an ordinary op;
keeping them a separate constructor makes that a type-level fact in phase A
and lets phase B map them to concrete byte positions via `resolve`.

The `pushLabel`/`jump`/`jumpi` rules carry their label-resolution premises
(`l ∈ labelDefs prog` / `findLabel … = some _`), so a derivation is
self-contained: phase B never needs global label well-formedness beyond
what each step records, and phase A discharges the premises once via
`findLabel_boundary` from the compile-time `Nodup` check.
-/

namespace YulEvmCompiler

open YulSemantics.EVM (U256 EvmState Op stepOp)

/-- An Asm-level stack value: a word, or the code address of label `l`. -/
inductive AVal
  | word (v : U256)
  | code (l : Label)
  deriving Repr, DecidableEq

/-- Lift a list of words onto the Asm stack. -/
def words (vs : List U256) : List AVal := vs.map .word

@[simp] theorem words_nil : words [] = [] := rfl
@[simp] theorem words_cons (v : U256) (vs : List U256) :
    words (v :: vs) = .word v :: words vs := rfl
@[simp] theorem words_length (vs : List U256) : (words vs).length = vs.length := by
  simp [words]
theorem words_append (vs ws : List U256) :
    words (vs ++ ws) = words vs ++ words ws := by
  simp [words]

/-- An Asm machine configuration: remaining code (a suffix of the program),
operand stack, machine state. -/
structure AConf where
  code : List Asm
  stk : List AVal
  yst : EvmState

/-- One step of the Asm machine, relative to the whole program `prog`
(which jumps search for labels). -/
inductive AStep (prog : List Asm) : AConf → AConf → Prop
  /-- Push a word. -/
  | push {v : U256} {c : List Asm} {σ : List AVal} {yst : EvmState} :
      AStep prog ⟨.push v :: c, σ, yst⟩ ⟨c, .word v :: σ, yst⟩
  /-- A non-halting built-in: consume the argument words, push the results,
  step the machine state — all by the Yul dialect's own `stepOp`. -/
  | op {yop : Op} {args rets : List U256} {c : List Asm} {σ : List AVal}
      {yst yst' : EvmState} :
      stepOp yop args yst = some (.ok rets yst') →
      AStep prog ⟨.op yop :: c, words args ++ σ, yst⟩
        ⟨c, words rets ++ σ, yst'⟩
  /-- `DUP(n+1)`: copy the value `n` deep onto the top. -/
  | dup {n : Fin 16} {v : AVal} {τ ρ : List AVal} {c : List Asm}
      {yst : EvmState} :
      τ.length = n.val →
      AStep prog ⟨.dup n :: c, τ ++ v :: ρ, yst⟩ ⟨c, v :: (τ ++ v :: ρ), yst⟩
  /-- `SWAP(n+1)`: exchange the top with the value `n+1` deep. -/
  | swap {n : Fin 16} {a b : AVal} {τ ρ : List AVal} {c : List Asm}
      {yst : EvmState} :
      τ.length = n.val →
      AStep prog ⟨.swap n :: c, a :: (τ ++ b :: ρ), yst⟩
        ⟨c, b :: (τ ++ a :: ρ), yst⟩
  /-- Discard the top of the stack. -/
  | pop {v : AVal} {σ : List AVal} {c : List Asm} {yst : EvmState} :
      AStep prog ⟨.pop :: c, v :: σ, yst⟩ ⟨c, σ, yst⟩
  /-- A label definition is a no-op (its lowering, `JUMPDEST`, only costs
  gas — phase B's concern). -/
  | label {l : Label} {c : List Asm} {σ : List AVal} {yst : EvmState} :
      AStep prog ⟨.label l :: c, σ, yst⟩ ⟨c, σ, yst⟩
  /-- Unconditional jump: continue right after the (unique) `.label l`. -/
  | jump {l : Label} {c c' : List Asm} {σ : List AVal} {yst : EvmState} :
      findLabel l prog = some c' →
      AStep prog ⟨.jump l :: c, σ, yst⟩ ⟨c', σ, yst⟩
  /-- Conditional jump, taken (the popped word is nonzero). -/
  | jumpiTaken {l : Label} {v : U256} {c c' : List Asm} {σ : List AVal}
      {yst : EvmState} :
      v ≠ 0 →
      findLabel l prog = some c' →
      AStep prog ⟨.jumpi l :: c, .word v :: σ, yst⟩ ⟨c', σ, yst⟩
  /-- Conditional jump, not taken (the popped word is zero). -/
  | jumpiFall {l : Label} {v : U256} {c : List Asm} {σ : List AVal}
      {yst : EvmState} :
      v = 0 →
      AStep prog ⟨.jumpi l :: c, .word v :: σ, yst⟩ ⟨c, σ, yst⟩
  /-- Push a (defined) label's code address. -/
  | pushLabel {l : Label} {c : List Asm} {σ : List AVal} {yst : EvmState} :
      l ∈ labelDefs prog →
      AStep prog ⟨.pushLabel l :: c, σ, yst⟩ ⟨c, .code l :: σ, yst⟩
  /-- Jump to the code address on top of the stack (function return). -/
  | dynJump {l : Label} {c c' : List Asm} {σ : List AVal} {yst : EvmState} :
      findLabel l prog = some c' →
      AStep prog ⟨.dynJump :: c, .code l :: σ, yst⟩ ⟨c', σ, yst⟩

/-- A halting step: a built-in whose `stepOp` halts (`stop`, `return`,
`revert`, `invalid`). The final Yul-side state carries the payload. -/
inductive AHalt (prog : List Asm) : AConf → EvmState → Prop
  | op {yop : Op} {args : List U256} {c : List Asm} {σ : List AVal}
      {yst yst' : EvmState} :
      stepOp yop args yst = some (.halt yst') →
      AHalt prog ⟨.op yop :: c, words args ++ σ, yst⟩ yst'

/-- Finitely many Asm steps (reflexive-transitive closure of `AStep`). -/
inductive ASteps (prog : List Asm) : AConf → AConf → Prop
  | refl (a : AConf) : ASteps prog a a
  | head {a b c : AConf} : AStep prog a b → ASteps prog b c → ASteps prog a c

namespace ASteps

theorem single {prog : List Asm} {a b : AConf} (h : AStep prog a b) :
    ASteps prog a b :=
  .head h (.refl b)

theorem trans {prog : List Asm} {a b c : AConf}
    (h₁ : ASteps prog a b) (h₂ : ASteps prog b c) : ASteps prog a c := by
  induction h₁ with
  | refl => exact h₂
  | head s _ ih => exact .head s (ih h₂)

theorem snoc {prog : List Asm} {a b c : AConf}
    (h₁ : ASteps prog a b) (h₂ : AStep prog b c) : ASteps prog a c :=
  h₁.trans (single h₂)

end ASteps

/-- The step relation only ever moves to suffixes of the program: ordinary
instructions consume the head of the current suffix, jumps land right after
a label found in `prog`. This is what lets phase B recover a byte position
(`codeSize prog - codeSize c`) for every reachable configuration. -/
theorem AStep.suffix {prog : List Asm} {a b : AConf}
    (h : AStep prog a b) (ha : a.code <:+ prog) : b.code <:+ prog := by
  have tail_suffix : ∀ {i : Asm} {c : List Asm}, (i :: c) <:+ prog → c <:+ prog := by
    intro i c ⟨pre, hpre⟩
    exact ⟨pre ++ [i], by simpa using hpre⟩
  cases h with
  | push => exact tail_suffix ha
  | op _ => exact tail_suffix ha
  | dup _ => exact tail_suffix ha
  | swap _ => exact tail_suffix ha
  | pop => exact tail_suffix ha
  | label => exact tail_suffix ha
  | jump hfind => exact findLabel_suffix hfind
  | jumpiTaken _ hfind => exact findLabel_suffix hfind
  | jumpiFall _ => exact tail_suffix ha
  | pushLabel _ => exact tail_suffix ha
  | dynJump hfind => exact findLabel_suffix hfind

theorem ASteps.suffix {prog : List Asm} {a b : AConf}
    (h : ASteps prog a b) (ha : a.code <:+ prog) : b.code <:+ prog := by
  induction h with
  | refl => exact ha
  | head s _ ih => exact ih (s.suffix ha)

end YulEvmCompiler
