import YulEvmCompiler.OpTable

/-!
# YulEvmCompiler.Asm

The **labeled assembly layer**: the compiler's control-flow IR.

`Asm` sits between Yul and the byte-level `Instr` IR. Jumps target symbolic
*labels*, so compilation is position-independent (no byte positions are
threaded through the compiler), and the simulation proof against the Asm
semantics (`YulEvmCompiler.AsmSem`) never mentions a program counter. A
separate, generic lowering pass (`lowerProg`) resolves labels to byte
positions and produces `Instr`s; its correctness proof
(`YulEvmCompiler.LowerCorrect`) is the only place byte positions, decode
lemmas, and gas appear.

Design points (see `DESIGN.md`):

* Every constructor lowers to a **fixed byte width** (`Asm.size`), so the
  byte position of a suffix `c` of the program is
  `codeSize prog - codeSize c` — independent of label resolution.
* `.op` carries the *Yul* operation; the EVM opcode is chosen at lowering
  via `opTable`. The Asm semantics runs Yul-side `stepOp`, so phase A needs
  no per-op agreements at all.
* Label well-formedness (`WFProg`) is **checked, not proved**: the compiler
  runs the decidable `wfCheck` on its output and rejects on failure, so the
  correctness proof gets uniqueness/definedness of labels for free from
  `compile = some _`, with no freshness bookkeeping.
-/

namespace YulEvmCompiler

open EvmSemantics
open YulSemantics.EVM (U256 Op)

/-- A symbolic code label. Generated from a counter during compilation;
uniqueness is *checked* at the end (`wfCheck`), not tracked by proofs. -/
abbrev Label := Nat

/-- The labeled assembly IR. -/
inductive Asm
  /-- Push a (Yul-side) word: lowers to `PUSH32 (conv v)`. -/
  | push (v : U256)
  /-- A verified Yul built-in (must be in `opTable`'s domain to lower);
  includes the halting ops. -/
  | op (yop : Op)
  /-- `DUP(n+1)` — variable reads. -/
  | dup (n : Fin 16)
  /-- `SWAP(n+1)` — assignments, return-value shuffling. -/
  | swap (n : Fin 16)
  /-- `POP` — block exits, statically-resolved control-flow pops. -/
  | pop
  /-- Definition site of label `l`: lowers to `JUMPDEST`. -/
  | label (l : Label)
  /-- Unconditional jump to `l`: lowers to `PUSH32 addr(l); JUMP`. -/
  | jump (l : Label)
  /-- Conditional jump to `l`, consuming the condition on top of the stack:
  lowers to `PUSH32 addr(l); JUMPI`. -/
  | jumpi (l : Label)
  /-- Push `l`'s code address (function return addresses):
  lowers to `PUSH32 addr(l)`. -/
  | pushLabel (l : Label)
  /-- Jump to the code address on top of the stack (function returns):
  lowers to `JUMP`. -/
  | dynJump
  deriving Repr, DecidableEq

namespace Asm

/-- The byte width an instruction lowers to. Fixed per constructor — this is
what makes suffix positions independent of label resolution. -/
def size : Asm → Nat
  | push _ => 33
  | op _ => 1
  | dup _ => 1
  | swap _ => 1
  | pop => 1
  | label _ => 1
  | jump _ => 34
  | jumpi _ => 34
  | pushLabel _ => 33
  | dynJump => 1

theorem size_pos (i : Asm) : 1 ≤ i.size := by cases i <;> simp [size]

/-- The label an instruction defines (only `.label`). -/
def defines : Asm → Option Label
  | label l => some l
  | _ => none

/-- The label an instruction references (jumps and address pushes). -/
def references : Asm → Option Label
  | jump l | jumpi l | pushLabel l => some l
  | _ => none

end Asm

/-- Total byte size of a fragment once lowered. -/
def codeSize (p : List Asm) : Nat := (p.map Asm.size).sum

@[simp] theorem codeSize_nil : codeSize [] = 0 := rfl
@[simp] theorem codeSize_cons (i : Asm) (p : List Asm) :
    codeSize (i :: p) = i.size + codeSize p := by
  simp [codeSize]
theorem codeSize_append (p q : List Asm) :
    codeSize (p ++ q) = codeSize p + codeSize q := by
  simp [codeSize]

theorem codeSize_suffix_le {c p : List Asm} (h : c <:+ p) :
    codeSize c ≤ codeSize p := by
  obtain ⟨pre, rfl⟩ := h
  rw [codeSize_append]
  omega

/-- The labels a fragment defines, in order. -/
def labelDefs (p : List Asm) : List Label := p.filterMap Asm.defines

/-- The labels a fragment references. -/
def labelRefs (p : List Asm) : List Label := p.filterMap Asm.references

@[simp] theorem labelDefs_nil : labelDefs [] = [] := rfl
@[simp] theorem labelRefs_nil : labelRefs [] = [] := rfl

theorem labelDefs_cons (i : Asm) (p : List Asm) :
    labelDefs (i :: p) = i.defines.toList ++ labelDefs p := by
  unfold labelDefs
  rw [List.filterMap_cons]
  cases i.defines <;> simp

theorem labelRefs_cons (i : Asm) (p : List Asm) :
    labelRefs (i :: p) = i.references.toList ++ labelRefs p := by
  unfold labelRefs
  rw [List.filterMap_cons]
  cases i.references <;> simp

theorem labelDefs_append (p q : List Asm) :
    labelDefs (p ++ q) = labelDefs p ++ labelDefs q := by
  simp [labelDefs]

theorem labelRefs_append (p q : List Asm) :
    labelRefs (p ++ q) = labelRefs p ++ labelRefs q := by
  simp [labelRefs]

@[simp] theorem labelDefs_label (l : Label) (p : List Asm) :
    labelDefs (.label l :: p) = l :: labelDefs p := by
  rw [labelDefs_cons]; rfl

/-- Membership in the defined labels of a cons, by cases on the head. -/
theorem mem_labelDefs_cons {l : Label} {i : Asm} {p : List Asm} :
    l ∈ labelDefs (i :: p) ↔ i = .label l ∨ l ∈ labelDefs p := by
  cases i <;>
    simp [labelDefs, Asm.defines, eq_comm]

/-- Byte position of (the `JUMPDEST` of) the first `.label l`. -/
def resolve (l : Label) : List Asm → Option Nat
  | [] => none
  | i :: rest =>
    if i = .label l then some 0
    else (resolve l rest).map (i.size + ·)

/-- The code suffix immediately *after* the first `.label l` (the Asm-level
jump target; the lowered `JUMP` lands on the `JUMPDEST` just before it). -/
def findLabel (l : Label) : List Asm → Option (List Asm)
  | [] => none
  | i :: rest => if i = .label l then some rest else findLabel l rest

/-- Inverting a successful `findLabel`: the program splits at the label's
first occurrence, and `resolve` agrees on the byte position. -/
theorem findLabel_eq_some {l : Label} :
    ∀ {p c : List Asm}, findLabel l p = some c →
      ∃ pre, p = pre ++ .label l :: c ∧ l ∉ labelDefs pre
        ∧ resolve l p = some (codeSize pre) := by
  intro p
  induction p with
  | nil => intro c h; simp [findLabel] at h
  | cons i rest ih =>
    intro c h
    rw [findLabel] at h
    by_cases hi : i = Asm.label l
    · subst hi
      rw [if_pos rfl] at h
      obtain rfl : rest = c := by simpa using h
      exact ⟨[], rfl, by simp, by simp [resolve]⟩
    · rw [if_neg hi] at h
      obtain ⟨pre, rfl, hnot, hres⟩ := ih h
      refine ⟨i :: pre, rfl, ?_, ?_⟩
      · intro hmem
        rcases mem_labelDefs_cons.mp hmem with hl | hl
        · exact hi hl
        · exact hnot hl
      · rw [resolve, if_neg hi, hres]
        simp

/-- A found suffix is a suffix of the program. -/
theorem findLabel_suffix {l : Label} {p c : List Asm}
    (h : findLabel l p = some c) : c <:+ p := by
  obtain ⟨pre, rfl, -, -⟩ := findLabel_eq_some h
  exact ⟨pre ++ [.label l], by simp⟩

/-- A label not defined in the prefix is found exactly where it is placed. -/
theorem findLabel_of_not_mem {l : Label} :
    ∀ {pre : List Asm}, l ∉ labelDefs pre → ∀ c : List Asm,
      findLabel l (pre ++ .label l :: c) = some c := by
  intro pre
  induction pre with
  | nil => intro _ c; rw [List.nil_append, findLabel, if_pos rfl]
  | cons i pre ih =>
    intro hnot c
    have hi : i ≠ Asm.label l :=
      fun hEq => hnot (mem_labelDefs_cons.mpr (Or.inl hEq))
    rw [List.cons_append, findLabel, if_neg hi]
    exact ih (fun hmem => hnot (mem_labelDefs_cons.mpr (Or.inr hmem))) c

/-- `resolve` counterpart of `findLabel_of_not_mem`. -/
theorem resolve_of_not_mem {l : Label} :
    ∀ {pre : List Asm}, l ∉ labelDefs pre → ∀ c : List Asm,
      resolve l (pre ++ .label l :: c) = some (codeSize pre) := by
  intro pre
  induction pre with
  | nil => intro _ c; rw [List.nil_append, resolve, if_pos rfl]; rfl
  | cons i pre ih =>
    intro hnot c
    have hi : i ≠ Asm.label l :=
      fun hEq => hnot (mem_labelDefs_cons.mpr (Or.inl hEq))
    rw [List.cons_append, resolve, if_neg hi,
      ih (fun hmem => hnot (mem_labelDefs_cons.mpr (Or.inr hmem))) c]
    simp

/-- Under unique label definitions, the prefix before a placed label cannot
define it. -/
theorem not_mem_labelDefs_left {l : Label} {pre c : List Asm}
    (hnodup : (labelDefs (pre ++ .label l :: c)).Nodup) :
    l ∉ labelDefs pre := by
  rw [labelDefs_append] at hnodup
  intro hmem
  exact List.disjoint_of_nodup_append hnodup hmem
    (mem_labelDefs_cons.mpr (Or.inl rfl))

/-- With unique label definitions, a label placed by the compiler is found
exactly where it was placed. This is how phase A turns "I emitted `.label l`
here" into "jumps to `l` arrive here". -/
theorem findLabel_boundary {l : Label} {pre c : List Asm}
    (hnodup : (labelDefs (pre ++ .label l :: c)).Nodup) :
    findLabel l (pre ++ .label l :: c) = some c :=
  findLabel_of_not_mem (not_mem_labelDefs_left hnodup) c

/-- `resolve` counterpart of `findLabel_boundary`. -/
theorem resolve_boundary {l : Label} {pre c : List Asm}
    (hnodup : (labelDefs (pre ++ .label l :: c)).Nodup) :
    resolve l (pre ++ .label l :: c) = some (codeSize pre) :=
  resolve_of_not_mem (not_mem_labelDefs_left hnodup) c

/-- A resolved position points strictly inside the code (at a 1-byte
`JUMPDEST`). -/
theorem resolve_lt {l : Label} :
    ∀ {p : List Asm} {a : Nat}, resolve l p = some a → a + 1 ≤ codeSize p := by
  intro p
  induction p with
  | nil => intro a h; simp [resolve] at h
  | cons i rest ih =>
    intro a h
    rw [resolve] at h
    by_cases hi : i = Asm.label l
    · subst hi
      rw [if_pos rfl] at h
      obtain rfl : (0 : Nat) = a := by simpa using h
      simp [Asm.size]
    · rw [if_neg hi] at h
      obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.mp h
      have := ih ha'
      have := i.size_pos
      rw [codeSize_cons]
      omega

/-- A label is defined iff `findLabel` finds it. -/
theorem mem_labelDefs_iff_findLabel {l : Label} :
    ∀ {p : List Asm}, l ∈ labelDefs p ↔ (findLabel l p).isSome := by
  intro p
  induction p with
  | nil => simp [findLabel]
  | cons i rest ih =>
    rw [findLabel]
    by_cases hi : i = Asm.label l
    · subst hi
      simp
    · rw [if_neg hi, ← ih, mem_labelDefs_cons]
      exact ⟨fun h => h.resolve_left hi, Or.inr⟩

/-! ### Whole-program well-formedness (checked at compile time) -/

/-- The label well-formedness the correctness proof relies on. The compiler
*checks* this (decidably, `wfCheck`) on its final output, so downstream
proofs get it from `compile = some _` without any freshness
reasoning. -/
structure WFProg (p : List Asm) : Prop where
  /-- Each label is defined at most once (jump targets are unambiguous). -/
  nodup : (labelDefs p).Nodup
  /-- Every referenced label is defined (lowering and `dynJump` are total). -/
  refsDefined : ∀ l ∈ labelRefs p, l ∈ labelDefs p
  /-- Byte positions fit in a word (pc arithmetic never wraps). -/
  small : codeSize p < 2 ^ 256

/-- The decidable well-formedness check the compiler runs. -/
def wfCheck (p : List Asm) : Bool :=
  decide (labelDefs p).Nodup
    && (labelRefs p).all (fun l => decide (l ∈ labelDefs p))
    && decide (codeSize p < 2 ^ 256)

theorem wfCheck_iff {p : List Asm} : wfCheck p = true ↔ WFProg p := by
  unfold wfCheck
  rw [Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨of_decide_eq_true h1,
      fun l hl => of_decide_eq_true (h2 l hl),
      of_decide_eq_true h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨decide_eq_true h1, fun l hl => decide_eq_true (h2 l hl)⟩,
      decide_eq_true h3⟩

/-! ### Lowering to the byte-level IR -/

/-- Lower one instruction, resolving labels against the whole program
`prog`. `none` when a referenced label is undefined (excluded by `wfCheck`)
or the Yul op is outside `opTable`'s verified domain. -/
def lowerInstr (prog : List Asm) : Asm → Option (List Instr)
  | .push v      => some [.push (conv v)]
  | .op yop      => (opTable yop).map (fun o => [.op o])
  | .dup n       => some [.op (.Dup ⟨n⟩)]
  | .swap n      => some [.op (.Swap ⟨n⟩)]
  | .pop         => some [.op .POP]
  | .label _     => some [.op .JUMPDEST]
  | .jump l      => (resolve l prog).map
      (fun a => [.push (UInt256.ofNat a), .op .JUMP])
  | .jumpi l     => (resolve l prog).map
      (fun a => [.push (UInt256.ofNat a), .op .JUMPI])
  | .pushLabel l => (resolve l prog).map
      (fun a => [.push (UInt256.ofNat a)])
  | .dynJump     => some [.op .JUMP]

/-- Lower a fragment (against the whole program `prog`). -/
def lowerFrag (prog : List Asm) : List Asm → Option (List Instr)
  | [] => some []
  | i :: rest => do
      let is1 ← lowerInstr prog i
      let is2 ← lowerFrag prog rest
      return is1 ++ is2

/-- Lower a whole program. -/
def lowerProg (p : List Asm) : Option (List Instr) := lowerFrag p p

/-- Lowered width is `Asm.size`, for every constructor. -/
theorem lowerInstr_length {prog : List Asm} {i : Asm} {is : List Instr}
    (h : lowerInstr prog i = some is) :
    (assembleBytes is).length = i.size := by
  cases i <;> simp only [lowerInstr] at h
  case push v =>
    obtain rfl : [Instr.push (conv v)] = is := by simpa using h
    simp [Asm.size]
  case op yop =>
    obtain ⟨o, -, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [Asm.size]
  case dup n =>
    obtain rfl : [Instr.op (.Dup ⟨n⟩)] = is := by simpa using h
    simp [Asm.size]
  case swap n =>
    obtain rfl : [Instr.op (.Swap ⟨n⟩)] = is := by simpa using h
    simp [Asm.size]
  case pop =>
    obtain rfl : [Instr.op .POP] = is := by simpa using h
    simp [Asm.size]
  case label l =>
    obtain rfl : [Instr.op .JUMPDEST] = is := by simpa using h
    simp [Asm.size]
  case jump l =>
    obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [Asm.size]
  case jumpi l =>
    obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [Asm.size]
  case pushLabel l =>
    obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [Asm.size]
  case dynJump =>
    obtain rfl : [Instr.op .JUMP] = is := by simpa using h
    simp [Asm.size]

@[simp] theorem lowerFrag_nil (prog : List Asm) : lowerFrag prog [] = some [] := rfl

theorem lowerFrag_cons {prog : List Asm} {i : Asm} {p : List Asm} {is : List Instr}
    (h : lowerFrag prog (i :: p) = some is) :
    ∃ is1 is2, lowerInstr prog i = some is1 ∧ lowerFrag prog p = some is2
      ∧ is = is1 ++ is2 := by
  rw [lowerFrag, Option.bind_eq_bind] at h
  obtain ⟨is1, h1, h'⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨is2, h2, h''⟩ := Option.bind_eq_some_iff.mp h'
  exact ⟨is1, is2, h1, h2, by simpa using h''.symm⟩

theorem lowerFrag_cons' {prog : List Asm} {i : Asm} {p : List Asm}
    {is1 is2 : List Instr}
    (h1 : lowerInstr prog i = some is1) (h2 : lowerFrag prog p = some is2) :
    lowerFrag prog (i :: p) = some (is1 ++ is2) := by
  rw [lowerFrag, Option.bind_eq_bind, h1, Option.bind_some, h2]
  rfl

/-- Splitting a successful fragment lowering at an append. -/
theorem lowerFrag_append {prog : List Asm} :
    ∀ {p q : List Asm} {is : List Instr},
      lowerFrag prog (p ++ q) = some is →
      ∃ is1 is2, lowerFrag prog p = some is1 ∧ lowerFrag prog q = some is2
        ∧ is = is1 ++ is2 := by
  intro p
  induction p with
  | nil => intro q is h; exact ⟨[], is, rfl, h, rfl⟩
  | cons i p ih =>
    intro q is h
    rw [List.cons_append] at h
    obtain ⟨is1, is2, h1, h2, rfl⟩ := lowerFrag_cons h
    obtain ⟨is21, is22, h21, h22, rfl⟩ := ih h2
    exact ⟨is1 ++ is21, is22, lowerFrag_cons' h1 h21, h22, by simp⟩

/-- Joining fragment lowerings across an append. -/
theorem lowerFrag_append' {prog : List Asm} :
    ∀ {p q : List Asm} {is1 is2 : List Instr},
      lowerFrag prog p = some is1 → lowerFrag prog q = some is2 →
      lowerFrag prog (p ++ q) = some (is1 ++ is2) := by
  intro p
  induction p with
  | nil =>
    intro q is1 is2 h1 h2
    obtain rfl : ([] : List Instr) = is1 := by simpa using h1
    simpa using h2
  | cons i p ih =>
    intro q is1 is2 h1 h2
    obtain ⟨js1, js2, hj1, hj2, rfl⟩ := lowerFrag_cons h1
    rw [List.cons_append]
    have := lowerFrag_cons' hj1 (ih hj2 h2)
    simpa using this

/-- Lowered fragment byte length is its `codeSize`. -/
theorem lowerFrag_length {prog : List Asm} :
    ∀ {p : List Asm} {is : List Instr},
      lowerFrag prog p = some is →
      (assembleBytes is).length = codeSize p := by
  intro p
  induction p with
  | nil =>
    intro is h
    obtain rfl : ([] : List Instr) = is := by simpa using h
    rfl
  | cons i p ih =>
    intro is h
    obtain ⟨is1, is2, h1, h2, rfl⟩ := lowerFrag_cons h
    rw [assembleBytes_append, List.length_append, lowerInstr_length h1, ih h2,
      codeSize_cons]

end YulEvmCompiler
