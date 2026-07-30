import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Basic
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas
import YulEvmCompiler.OpTable
set_option warningAsError true
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

* Every constructor lowers to a **label-resolution-independent byte width**
  (`Asm.size`), so the byte position of a suffix `c` of the program is
  `codeSize prog - codeSize c`. Constant pushes use the *minimal* `PUSHk`
  encoding (`Instr.pushMin`), so their width depends on the constant's value
  — but never on where labels resolve. Label pushes (`jump`/`jumpi`/
  `pushLabel`) use a **uniform** width `labelWidth` bytes for the address, so
  their size is fixed regardless of the resolved target; `wfCheck` bounds
  `codeSize` by `256 ^ labelWidth`, guaranteeing every resolved address fits.
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
  /-- Push a (Yul-side) word: lowers to the minimal-width `PUSHk (conv v)`
  (`Instr.pushMin`). -/
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
  /-- Unconditional jump to `l`: lowers to `PUSH{labelWidth} addr(l); JUMP`. -/
  | jump (l : Label)
  /-- Conditional jump to `l`, consuming the condition on top of the stack:
  lowers to `PUSH{labelWidth} addr(l); JUMPI`. -/
  | jumpi (l : Label)
  /-- Push `l`'s code address (function return addresses):
  lowers to `PUSH{labelWidth} addr(l)`. -/
  | pushLabel (l : Label)
  /-- Jump to the code address on top of the stack (function returns):
  lowers to `JUMP`. -/
  | dynJump
  /-- An **immutable** read: pushes `v`, the value `key`'s immutable holds in the
  deployed code, always as a full-width `PUSH32`.

  The fixed width is the whole point. Ordinary `push` takes the minimal `PUSHk`
  encoding, so its byte length varies with the value; an immutable's 32 immediate
  bytes must sit at an offset the *constructor* can compute and patch, which
  requires that offset to be independent of the value stored there. `key` carries
  no runtime meaning — it exists so the object layer can report where each
  placeholder landed. -/
  | pushImmutable (key : String) (v : U256)
  deriving Repr, DecidableEq

/-- The uniform number of address bytes emitted for a label push (`jump`,
`jumpi`, `pushLabel`). Used symbolically throughout; widening it later (e.g.
to `3`) is a one-line change here plus re-pinning `wfCheck`'s codeSize bound.
`labelWidth = 2` covers every deployable program: EIP-170 caps runtime code
at 24576 bytes and EIP-3860 caps initcode at 49152 — both `< 256 ^ 2`. -/
def labelWidth : Nat := 2

/-- `labelWidth` as the `Fin 33` width of the emitted `PUSHk`. -/
def labelWidthFin : Fin 33 := ⟨labelWidth, by norm_num [labelWidth]⟩

@[simp] theorem labelWidthFin_val : labelWidthFin.val = labelWidth := rfl

namespace Asm

/-- The byte width an instruction lowers to. Independent of label resolution
(constant pushes use the minimal `PUSHk` encoding, which depends on the value
but not on the layout; label pushes use the uniform `labelWidth`-byte
address). This is what makes suffix positions
`codeSize prog - codeSize c`. -/
def size : Asm → Nat
  | push v => 1 + Instr.byteWidth (conv v).toNat
  | op _ => 1
  | dup _ => 1
  | swap _ => 1
  | pop => 1
  | label _ => 1
  | jump _ => labelWidth + 2
  | jumpi _ => labelWidth + 2
  | pushLabel _ => labelWidth + 1
  | dynJump => 1
  -- `PUSH32` opcode byte plus 32 immediate bytes, independent of `v`.
  | pushImmutable _ _ => 33

theorem size_pos (i : Asm) : 1 ≤ i.size := by
  cases i <;> simp only [size] <;> omega

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
  /-- Every resolved label address fits in `labelWidth` bytes: `codeSize`
  bounds every byte position, so a `labelWidth`-byte immediate never truncates
  a jump target. Strictly stronger than the old word bound
  (`256 ^ labelWidth < 2 ^ 256`). -/
  small : codeSize p < 256 ^ labelWidth

/-- The old word bound, recovered from `small` (`256 ^ labelWidth < 2 ^ 256`):
pc arithmetic never wraps. -/
theorem WFProg.small' {p : List Asm} (hw : WFProg p) : codeSize p < 2 ^ 256 := by
  have h := hw.small
  have hlt : (256 : Nat) ^ labelWidth ≤ 2 ^ 256 := by
    calc (256 : Nat) ^ labelWidth = 2 ^ 16 := by norm_num [labelWidth]
      _ ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  omega

/-- The decidable well-formedness check the compiler runs. -/
def wfCheck (p : List Asm) : Bool :=
  decide (labelDefs p).Nodup
    && (labelRefs p).all (fun l => decide (l ∈ labelDefs p))
    && decide (codeSize p < 256 ^ labelWidth)

/-! ### Verified fast well-formedness check

`wfCheck` as written recomputes `labelDefs p` — a full traversal that allocates a
fresh labels list — *inside* the `labelRefs` loop, and then scans it; and
`List.Nodup`'s default decision procedure is a quadratic sequence of equality
tests. With thousands of labels and references over tens of thousands of
instructions that dominated compilation. `wfCheckFast` traverses once and answers
both questions from a `Std.HashSet`; `@[csimp]` installs it in compiled code
while `wfCheck` remains the specification `wfCheck_iff` is stated about. -/

/-- Hash-based `Nodup` for label lists. (`Optimizer.nodupFast` is the same check
for the optimizer's string-keyed lists; this copy keeps the assembly layer
independent of the optimizer's module tree.) -/
def nodupLabels (xs : List Label) : Bool :=
  (Std.HashSet.ofList xs).size == xs.length

private theorem hashSet_ofList_cons_size {α : Type} [BEq α] [Hashable α]
    [LawfulBEq α] [LawfulHashable α] (a : α) (xs : List α) :
    (Std.HashSet.ofList (a :: xs)).size =
      ((Std.HashSet.ofList xs).insert a).size := by
  apply Std.HashSet.Equiv.size_eq
  apply Std.HashSet.Equiv.of_forall_contains_eq
  intro x
  simp
  rw [BEq.comm]

private theorem hashSet_ofList_size_eq_length_iff {α : Type}
    [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] [DecidableEq α]
    (xs : List α) :
    (Std.HashSet.ofList xs).size = xs.length ↔ xs.Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      rw [hashSet_ofList_cons_size, Std.HashSet.size_insert]
      by_cases ha : a ∈ Std.HashSet.ofList xs
      · have hmem : a ∈ xs := by
          simpa [Std.HashSet.mem_iff_contains] using ha
        have hle := Std.HashSet.size_ofList_le (l := xs)
        simp [ha, hmem]
        omega
      · have hmem : a ∉ xs := by
          simpa [Std.HashSet.mem_iff_contains] using ha
        simp [ha, hmem, ih]

@[simp] theorem nodupLabels_eq_decide (xs : List Label) :
    nodupLabels xs = decide xs.Nodup := by
  rw [Bool.eq_iff_iff]
  simpa [nodupLabels] using hashSet_ofList_size_eq_length_iff xs

/-- One-pass well-formedness check: `labelDefs` is built once, and both the
uniqueness and the definedness questions are answered from one hash set. -/
def wfCheckFast (p : List Asm) : Bool :=
  let defs := labelDefs p
  let defSet := Std.HashSet.ofList defs
  (defSet.size == defs.length)
    && (labelRefs p).all (fun l => defSet.contains l)
    && decide (codeSize p < 256 ^ labelWidth)

@[csimp] theorem wfCheck_eq_wfCheckFast : @wfCheck = @wfCheckFast := by
  funext p
  have hnodup : ((Std.HashSet.ofList (labelDefs p)).size == (labelDefs p).length)
      = decide (labelDefs p).Nodup := nodupLabels_eq_decide (labelDefs p)
  have hmem : ∀ l, (Std.HashSet.ofList (labelDefs p)).contains l
      = decide (l ∈ labelDefs p) := by
    intro l
    rw [Std.HashSet.contains_ofList]
    simp
  simp only [wfCheck, wfCheckFast, hnodup, hmem]

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
  | .push v      => some [Instr.pushMin (conv v)]
  | .op yop      => (opTable yop).map (fun o => [.op o])
  | .dup n       => some [.op (.Dup ⟨n⟩)]
  | .swap n      => some [.op (.Swap ⟨n⟩)]
  | .pop         => some [.op .POP]
  | .label _     => some [.op .JUMPDEST]
  | .jump l      => (resolve l prog).map
      (fun a => [.push labelWidthFin (UInt256.ofNat a), .op .JUMP])
  | .jumpi l     => (resolve l prog).map
      (fun a => [.push labelWidthFin (UInt256.ofNat a), .op .JUMPI])
  | .pushLabel l => (resolve l prog).map
      (fun a => [.push labelWidthFin (UInt256.ofNat a)])
  | .dynJump     => some [.op .JUMP]
  -- Always the full 32-byte immediate, so the value's byte position is fixed.
  | .pushImmutable _ v => some [.push ⟨32, by norm_num⟩ (conv v)]

/-- Lower a fragment (against the whole program `prog`). -/
def lowerFrag (prog : List Asm) : List Asm → Option (List Instr)
  | [] => some []
  | i :: rest => do
      let is1 ← lowerInstr prog i
      let is2 ← lowerFrag prog rest
      return is1 ++ is2

/-- Lower a whole program. -/
def lowerProg (p : List Asm) : Option (List Instr) := lowerFrag p p

/-! ### Verified fast lowering

`resolve l prog` walks the program from the start for **one** label, so
`lowerFrag` — which calls it once per `jump`/`jumpi`/`pushLabel` — is
`O(references × program)`, with an `Asm.label` allocation and an `Asm.size`
computation (a bignum width loop for `push`) at every visited instruction.
Real fixtures have thousands of references over tens of thousands of
instructions, which made lowering quadratic.

The fix computes every label's address in **one** pass and looks them up in a
`Std.HashMap`. `lowerProg` stays the proof-facing specification: the fast
version is proved *equal* to it and installed with `@[csimp]`, so compiled
code runs the fast one while every theorem downstream still talks about
`lowerProg`. No new axiom, no `implemented_by` trust step. -/

/-- Record `i`'s label at byte position `off`, keeping any address already
recorded (so the *first* definition wins, as `resolve` does). -/
def noteLabel (i : Asm) (off : Nat) (m : Std.HashMap Label Nat) :
    Std.HashMap Label Nat :=
  match i with
  | .label l => if m.contains l then m else m.insert l off
  | _ => m

/-- Address of the first definition of every label, accumulated left to right.
`off` is the byte position of the head of `p`. -/
def labelAddrsGo : List Asm → Nat → Std.HashMap Label Nat → Std.HashMap Label Nat
  | [], _, m => m
  | i :: rest, off, m => labelAddrsGo rest (off + i.size) (noteLabel i off m)

/-- An instruction that is not `.label l` leaves `l`'s recorded address alone. -/
theorem noteLabel_ne (i : Asm) (off : Nat) (m : Std.HashMap Label Nat)
    (l : Label) (hi : i ≠ .label l) :
    (noteLabel i off m).contains l = m.contains l ∧
      (noteLabel i off m)[l]? = m[l]? := by
  cases i with
  | label l' =>
      have hne : ¬ l' = l := fun h => hi (by rw [h])
      by_cases hm : m.contains l'
      · simp [noteLabel, hm]
      · refine ⟨?_, ?_⟩
        · simp [noteLabel, hm, Std.HashMap.contains_insert, beq_iff_eq, hne]
        · simp [noteLabel, hm, Std.HashMap.getElem?_insert, beq_iff_eq, hne]
  | _ => exact ⟨rfl, rfl⟩

/-- Byte address of every label defined in `p`, in one pass. -/
def labelAddrs (p : List Asm) : Std.HashMap Label Nat := labelAddrsGo p 0 ∅

/-- The accumulator characterisation: a label already recorded keeps its
address, and any other label resolves within the remaining fragment, shifted by
the fragment's own offset. -/
theorem labelAddrsGo_getElem? (p : List Asm) :
    ∀ (off : Nat) (m : Std.HashMap Label Nat) (l : Label),
      (labelAddrsGo p off m)[l]? =
        if m.contains l then m[l]? else (resolve l p).map (off + ·) := by
  induction p with
  | nil =>
      intro off m l
      simp only [labelAddrsGo, resolve, Option.map_none]
      by_cases h : m.contains l
      · simp [h]
      · simp [h, Std.HashMap.getElem?_eq_none_of_contains_eq_false
          (by simpa using h)]
  | cons i rest ih =>
      intro off m l
      rw [labelAddrsGo, ih]
      by_cases hi : i = .label l
      · subst hi
        by_cases hm : m.contains l
        · simp [noteLabel, hm]
        · simp [noteLabel, hm, resolve]
      · obtain ⟨hc, hg⟩ := noteLabel_ne i off m l hi
        rw [hc, hg]
        by_cases hm : m.contains l
        · simp [hm]
        · simp only [hm, if_false, Bool.false_eq_true, resolve, hi, if_false]
          cases hr : resolve l rest with
          | none => simp
          | some a => simp [Nat.add_assoc]

/-- `labelAddrs` agrees with `resolve` on every label. -/
theorem labelAddrs_getElem? (p : List Asm) (l : Label) :
    (labelAddrs p)[l]? = resolve l p := by
  rw [labelAddrs, labelAddrsGo_getElem?]
  simp

/-- Record `i`'s label as targeting `rest`, keeping any target already recorded
(so the *first* definition wins, as `findLabel` does). -/
def noteTarget (i : Asm) (rest : List Asm) (m : Std.HashMap Label (List Asm)) :
    Std.HashMap Label (List Asm) :=
  match i with
  | .label l => if m.contains l then m else m.insert l rest
  | _ => m

/-- `findLabel`'s answer for every label, accumulated left to right. -/
def findLabelMapGo : List Asm → Std.HashMap Label (List Asm) →
    Std.HashMap Label (List Asm)
  | [], m => m
  | i :: rest, m => findLabelMapGo rest (noteTarget i rest m)

/-- Jump-target table: the code suffix after each label's first definition,
computed in one pass. `findLabel l p` scans the whole program for one label, and
the stack-certificate verifier resolves one per jump. -/
def findLabelMap (p : List Asm) : Std.HashMap Label (List Asm) :=
  findLabelMapGo p ∅

/-- An instruction that is not `.label l` leaves `l`'s recorded target alone. -/
private theorem noteTarget_ne (i : Asm) (rest : List Asm)
    (m : Std.HashMap Label (List Asm)) (l : Label) (hi : i ≠ .label l) :
    (noteTarget i rest m).contains l = m.contains l ∧
      (noteTarget i rest m)[l]? = m[l]? := by
  cases i with
  | label l' =>
      have hne : ¬ l' = l := fun h => hi (by rw [h])
      by_cases hm : m.contains l'
      · simp [noteTarget, hm]
      · refine ⟨?_, ?_⟩
        · simp [noteTarget, hm, Std.HashMap.contains_insert, beq_iff_eq, hne]
        · simp [noteTarget, hm, Std.HashMap.getElem?_insert, beq_iff_eq, hne]
  | _ => exact ⟨rfl, rfl⟩

theorem findLabelMapGo_getElem? (p : List Asm) :
    ∀ (m : Std.HashMap Label (List Asm)) (l : Label),
      (findLabelMapGo p m)[l]? =
        if m.contains l then m[l]? else findLabel l p := by
  induction p with
  | nil =>
      intro m l
      simp only [findLabelMapGo, findLabel]
      by_cases h : m.contains l
      · simp [h]
      · simp [h, Std.HashMap.getElem?_eq_none_of_contains_eq_false
          (by simpa using h)]
  | cons i rest ih =>
      intro m l
      rw [findLabelMapGo, ih]
      by_cases hi : i = .label l
      · subst hi
        by_cases hm : m.contains l
        · simp [noteTarget, hm]
        · simp [noteTarget, hm, findLabel]
      · obtain ⟨hc, hg⟩ := noteTarget_ne i rest m l hi
        rw [hc, hg]
        by_cases hm : m.contains l
        · simp [hm]
        · simp [hm, findLabel, hi]

/-- `findLabelMap` agrees with `findLabel` on every label. -/
theorem findLabelMap_getElem? (p : List Asm) (l : Label) :
    (findLabelMap p)[l]? = findLabel l p := by
  rw [findLabelMap, findLabelMapGo_getElem?]
  simp

/-- `lowerInstr` against a precomputed address table. -/
def lowerInstrWith (addrs : Std.HashMap Label Nat) : Asm → Option (List Instr)
  | .push v      => some [Instr.pushMin (conv v)]
  | .op yop      => (opTable yop).map (fun o => [.op o])
  | .dup n       => some [.op (.Dup ⟨n⟩)]
  | .swap n      => some [.op (.Swap ⟨n⟩)]
  | .pop         => some [.op .POP]
  | .label _     => some [.op .JUMPDEST]
  | .jump l      => addrs[l]?.map
      (fun a => [.push labelWidthFin (UInt256.ofNat a), .op .JUMP])
  | .jumpi l     => addrs[l]?.map
      (fun a => [.push labelWidthFin (UInt256.ofNat a), .op .JUMPI])
  | .pushLabel l => addrs[l]?.map
      (fun a => [.push labelWidthFin (UInt256.ofNat a)])
  | .dynJump     => some [.op .JUMP]

theorem lowerInstrWith_eq (p : List Asm) (i : Asm) :
    lowerInstrWith (labelAddrs p) i = lowerInstr p i := by
  cases i <;> simp [lowerInstrWith, lowerInstr, labelAddrs_getElem?]

/-- `lowerFrag` against a precomputed address table. -/
def lowerFragWith (addrs : Std.HashMap Label Nat) :
    List Asm → Option (List Instr)
  | [] => some []
  | i :: rest => do
      let is1 ← lowerInstrWith addrs i
      let is2 ← lowerFragWith addrs rest
      return is1 ++ is2

theorem lowerFragWith_eq (p : List Asm) :
    ∀ c : List Asm, lowerFragWith (labelAddrs p) c = lowerFrag p c := by
  intro c
  induction c with
  | nil => rfl
  | cons i rest ih => simp [lowerFragWith, lowerFrag, lowerInstrWith_eq, ih]

/-- One-pass lowering: build the address table once, then lower. -/
def lowerProgFast (p : List Asm) : Option (List Instr) :=
  lowerFragWith (labelAddrs p) p

@[csimp] theorem lowerProg_eq_lowerProgFast : @lowerProg = @lowerProgFast := by
  funext p
  rw [lowerProgFast, lowerProg, lowerFragWith_eq]

/-- Lowered width is `Asm.size`, for every constructor. -/
theorem lowerInstr_length {prog : List Asm} {i : Asm} {is : List Instr}
    (h : lowerInstr prog i = some is) :
    (assembleBytes is).length = i.size := by
  cases i <;> simp only [lowerInstr] at h
  case push v =>
    obtain rfl : [Instr.pushMin (conv v)] = is := by simpa using h
    simp [Asm.size]
  case pushImmutable key v =>
    obtain rfl : [Instr.push ⟨32, by norm_num⟩ (conv v)] = is := by simpa using h
    simp [Asm.size, assembleBytes, Instr.bytes]
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
    simp only [assembleBytes_cons, assembleBytes_nil, List.append_nil,
      List.length_append, Instr.length_bytes_push, Instr.length_bytes_op,
      labelWidthFin_val, Asm.size]
    omega
  case jumpi l =>
    obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [assembleBytes_cons, assembleBytes_nil, List.append_nil,
      List.length_append, Instr.length_bytes_push, Instr.length_bytes_op,
      labelWidthFin_val, Asm.size]
    omega
  case pushLabel l =>
    obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [assembleBytes_cons, assembleBytes_nil, List.append_nil,
      Instr.length_bytes_push, labelWidthFin_val, Asm.size]
    omega
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
