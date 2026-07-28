import YulEvmCompiler.Asm
set_option warningAsError true
/-!
# YulEvmCompiler.AsmPeephole

An **assembly-level (Asm → Asm) peephole optimizer**: the transform and its
label-structure preservation. This is the "separate, Asm→Asm soundness
contract" layer: unlike the source (Yul→Yul) optimizer, it rewrites the
compiler's labelled control-flow IR directly, so it can exploit patterns the
source optimizer cannot express — the backend's calling convention, its
branch layout, and its label placement.

## The rewrites

Six rewrites, each mined from actually-emitted code (the classic
`dup;pop` / `push;pop` / `swap n;swap n` peepholes never fire on this
backend's output):

1. **Return-slot assignment** — `push v ; swap1 ; pop ⟶ pop ; push v`.
   Identical net effect ("replace the top of the stack with the literal
   `v`"), one `SWAP1` (3 gas, 1 byte) cheaper. Emitted whenever a function
   body writes a constant into its top return slot.
2. **Branch inversion** — `jumpi l ; jump m ; label l ⟶
   op iszero ; jumpi m ; label l`. The `if cond {break/continue/leave}`
   shape: enter the guarded body via fall-through instead of a jump. Saves
   33 bytes, and 8 gas whenever the condition is false (the common path for
   guard-style `if`s) at the cost of 3 gas when it is true. The label stays
   (other references may exist); only the local entry becomes fall-through.
3. **Double-`iszero` elimination** — `op iszero ; op iszero ; jumpi l ⟶
   jumpi l`. A branch only tests truthiness, which `iszero ∘ iszero`
   preserves; 2 bytes and 6 gas per condition evaluation. Only sound in the
   `jumpi` context (elsewhere the normalized 0/1 value is observable).
   Branch inversion produces these whenever the source condition already
   ended in `iszero`, so iteration matters (below).
4. **Jump to next** — `jump l ; label l ⟶ label l` and `jumpi l ; label l
   ⟶ pop ; label l`: both branches land at the fall-through anyway.
5. **Dead label elimination** — drop `label l` when `l` is referenced
   nowhere in the program (about a quarter of emitted labels: loop-exit and
   return labels nothing jumps to). Saves the 1-byte `JUMPDEST` and 1 gas
   per pass-through.
6. **Iteration** — `optimizeAsm` runs up to four rounds (`optimizeAsmN`,
   early-stopping at a fixpoint): removing a double `iszero` uncovers a
   branch-inversion window, and an inverted branch orphans its `jumpi`'s
   label for dead-label elimination.

## Structure

* `peepRun R` — the concrete linear scan (`R` = labels that may be
  referenced; `optimizeAsm` instantiates `R := labelRefs p`).
* `CodeRel R` — a **spec** relation between a source suffix and an optimized
  suffix. `optimizeAsm` is one *implementation*; `codeRel_optimize` proves
  its output is always `CodeRel`-related. `CodeRel` keeps `labelDefs` a
  sublist (retaining every label in `R`), keeps `labelRefs` a subset,
  preserves `findLabel` for labels in `R` (`codeRel_findLabel`), and does
  not grow `codeSize`; hence it preserves `WFProg` (`codeRel_wf`).

The forward simulation against the phase-A step relation lives in
`YulEvmCompiler.AsmPeepholeSound` (this module stays byte- and
semantics-free); `YulEvmCompiler.Compile.compile` inserts `optimizeAsm`
between `compileProgram` and `lowerProg`.
-/

namespace YulEvmCompiler

open YulSemantics.EVM (U256 Op)

/-! ### The concrete transform -/

/-- The Asm-level peephole scan, relative to the set `R` of labels that may
be referenced. Rewrites every `push v ; swap1 ; pop` window to `pop ; push
v`, every `jumpi l ; jump m ; label l` window to `op iszero ; jumpi m ;
label l`, and drops `label l` when `l ∉ R`. Other instructions pass
through. -/
def peepRun (R : List Label) : List Asm → List Asm
  | .push v :: .swap ⟨0, _⟩ :: .pop :: rest =>
      .pop :: .push v :: peepRun R rest
  | .op .iszero :: .op .iszero :: .jumpi l :: rest =>
      .jumpi l :: peepRun R rest
  | .jumpi l :: .jump m :: .label l' :: rest =>
      if l = l' then .op .iszero :: .jumpi m :: .label l' :: peepRun R rest
      else .jumpi l :: peepRun R (.jump m :: .label l' :: rest)
  | .jumpi l :: .label l' :: rest =>
      if l = l' then .pop :: .label l' :: peepRun R rest
      else .jumpi l :: peepRun R (.label l' :: rest)
  | .jump l :: .label l' :: rest =>
      if l = l' then .label l' :: peepRun R rest
      else .jump l :: peepRun R (.label l' :: rest)
  | .label l :: rest =>
      if l ∈ R then .label l :: peepRun R rest else peepRun R rest
  | i :: rest => i :: peepRun R rest
  | [] => []
  termination_by p => p.length

/-- One round of the Asm-level peephole pass: scan with the program's own
reference set, so exactly the unreferenced labels are dropped. -/
def optimizeAsmRound (p : List Asm) : List Asm := peepRun (labelRefs p) p

/-- Iterate rounds up to a small fixed bound, stopping early at a fixpoint.
Later rounds catch windows the previous round exposes: removing a double
`iszero` uncovers a branch-inversion window, and an inverted branch orphans
its `jumpi`'s label for dead-label elimination. -/
def optimizeAsmN : Nat → List Asm → List Asm
  | 0, p => p
  | k + 1, p =>
      let q := optimizeAsmRound p
      if q = p then p else optimizeAsmN k q

/-- The Asm-level peephole pass run by `compile`: four rounds (empirically
past the fixpoint of the whole corpus). -/
def optimizeAsm (p : List Asm) : List Asm := optimizeAsmN 4 p

/-! ### The spec relation on code suffixes -/

namespace Peephole

/-- Relates a source program suffix to a valid optimized suffix, relative to
the set `R` of labels that may be referenced anywhere in the program.
`optimizeAsm` is a particular strategy; `codeRel_optimize` shows its output
is always `CodeRel`-related to its input. Keeping the relation separate from
the concrete function makes the simulation and the label-structure lemmas
independent of the scan order. -/
inductive CodeRel (R : List Label) : List Asm → List Asm → Prop
  /-- Empty programs are related. -/
  | nil : CodeRel R [] []
  /-- Keep an instruction verbatim. -/
  | keep (i : Asm) {c c' : List Asm} : CodeRel R c c' → CodeRel R (i :: c) (i :: c')
  /-- Rewrite a return-slot window. `n` is `swap1` (`n.val = 0`). -/
  | window {v : U256} {n : Fin 16} (hn : n.val = 0) {c c' : List Asm} :
      CodeRel R c c' →
      CodeRel R (.push v :: .swap n :: .pop :: c) (.pop :: .push v :: c')
  /-- Invert a `jumpi`-over-`jump` branch whose target is the very next
  label. The label stays in place (other references may exist). -/
  | brInv {l m : Label} {c c' : List Asm} :
      CodeRel R c c' →
      CodeRel R (.jumpi l :: .jump m :: .label l :: c)
                (.op .iszero :: .jumpi m :: .label l :: c')
  /-- Drop a double `iszero` feeding a `jumpi`: the branch only tests
  truthiness, which `iszero ∘ iszero` preserves. Only sound in this
  context — anywhere else the normalized 0/1 value is observable. -/
  | dblIszero {l : Label} {c c' : List Asm} :
      CodeRel R c c' →
      CodeRel R (.op .iszero :: .op .iszero :: .jumpi l :: c) (.jumpi l :: c')
  /-- Drop a `jump` to the immediately following label. -/
  | jumpNext {l : Label} {c c' : List Asm} :
      CodeRel R c c' →
      CodeRel R (.jump l :: .label l :: c) (.label l :: c')
  /-- A `jumpi` to the immediately following label lands there either way:
  only the condition pop remains. -/
  | jumpiNext {l : Label} {c c' : List Asm} :
      CodeRel R c c' →
      CodeRel R (.jumpi l :: .label l :: c) (.pop :: .label l :: c')
  /-- Drop a label no instruction may reference. -/
  | dropLabel {l : Label} (hl : l ∉ R) {c c' : List Asm} :
      CodeRel R c c' → CodeRel R (.label l :: c) c'

/-- `peepRun` always produces a `CodeRel`-related program. -/
theorem codeRel_peepRun (R : List Label) (p : List Asm) : CodeRel R p (peepRun R p) := by
  fun_induction peepRun R p with
  | case1 v isLt rest ih => exact CodeRel.window (n := ⟨0, isLt⟩) rfl ih
  | case2 l rest ih => exact CodeRel.dblIszero ih
  | case3 m l' rest ih => exact CodeRel.brInv ih
  | case4 l m l' rest hne ih => exact CodeRel.keep _ ih
  | case5 l' rest ih => exact CodeRel.jumpiNext ih
  | case6 l l' rest hne ih => exact CodeRel.keep _ ih
  | case7 l' rest ih => exact CodeRel.jumpNext ih
  | case8 l l' rest hne ih => exact CodeRel.keep _ ih
  | case9 l rest hmem ih => exact CodeRel.keep _ ih
  | case10 l rest hmem ih => exact CodeRel.dropLabel hmem ih
  | case11 i rest _ _ _ _ _ _ ih => exact CodeRel.keep i ih
  | case12 => exact CodeRel.nil

/-- One `optimizeAsmRound` is `CodeRel`-related to its input, relative to the
program's own reference set. -/
theorem codeRel_optimizeRound (p : List Asm) :
    CodeRel (labelRefs p) p (optimizeAsmRound p) :=
  codeRel_peepRun (labelRefs p) p

/-! ### `CodeRel` preserves label structure -/

/-- Optimization only ever *removes* label definitions (and preserves their
order). -/
theorem codeRel_labelDefs_sublist {R : List Label} {P Q : List Asm}
    (h : CodeRel R P Q) : List.Sublist (labelDefs Q) (labelDefs P) := by
  induction h with
  | nil => exact .refl _
  | keep i _ ih =>
      rw [labelDefs_cons, labelDefs_cons]
      exact ih.append_left i.defines.toList
  | window _ _ ih =>
      simpa only [labelDefs_cons, Asm.defines, Option.toList_none,
        List.nil_append] using ih
  | brInv _ ih =>
      simp only [labelDefs_cons, Asm.defines, Option.toList_none,
        Option.toList_some, List.nil_append, List.singleton_append]
      exact ih.cons_cons _
  | dblIszero _ ih =>
      simpa only [labelDefs_cons, Asm.defines, Option.toList_none,
        List.nil_append] using ih
  | jumpNext _ ih =>
      simp only [labelDefs_cons, Asm.defines, Option.toList_none,
        Option.toList_some, List.nil_append, List.singleton_append]
      exact ih.cons_cons _
  | jumpiNext _ ih =>
      simp only [labelDefs_cons, Asm.defines, Option.toList_none,
        Option.toList_some, List.nil_append, List.singleton_append]
      exact ih.cons_cons _
  | dropLabel _ _ ih =>
      simp only [labelDefs_cons, Asm.defines, Option.toList_some,
        List.singleton_append]
      exact ih.cons _

/-- A label in `R` is never dropped. -/
theorem codeRel_labelDefs_mem {R : List Label} {P Q : List Asm}
    (h : CodeRel R P Q) {l : Label} (hR : l ∈ R) (hl : l ∈ labelDefs P) :
    l ∈ labelDefs Q := by
  induction h with
  | nil => exact hl
  | keep i _ ih =>
      rcases mem_labelDefs_cons.mp hl with h' | h'
      · exact mem_labelDefs_cons.mpr (Or.inl h')
      · exact mem_labelDefs_cons.mpr (Or.inr (ih h'))
  | window _ _ ih =>
      rcases mem_labelDefs_cons.mp hl with h' | h'
      · exact absurd h' (by simp)
      · rcases mem_labelDefs_cons.mp h' with h'' | h''
        · exact absurd h'' (by simp)
        · rcases mem_labelDefs_cons.mp h'' with h3 | h3
          · exact absurd h3 (by simp)
          · exact mem_labelDefs_cons.mpr (Or.inr
              (mem_labelDefs_cons.mpr (Or.inr (ih h3))))
  | brInv _ ih =>
      rcases mem_labelDefs_cons.mp hl with h' | h'
      · exact absurd h' (by simp)
      · rcases mem_labelDefs_cons.mp h' with h'' | h''
        · exact absurd h'' (by simp)
        · rcases mem_labelDefs_cons.mp h'' with h3 | h3
          · exact mem_labelDefs_cons.mpr (Or.inr
              (mem_labelDefs_cons.mpr (Or.inr (mem_labelDefs_cons.mpr (Or.inl h3)))))
          · exact mem_labelDefs_cons.mpr (Or.inr
              (mem_labelDefs_cons.mpr (Or.inr (mem_labelDefs_cons.mpr (Or.inr (ih h3))))))
  | dblIszero _ ih =>
      rcases mem_labelDefs_cons.mp hl with h' | h'
      · exact absurd h' (by simp)
      · rcases mem_labelDefs_cons.mp h' with h'' | h''
        · exact absurd h'' (by simp)
        · rcases mem_labelDefs_cons.mp h'' with h3 | h3
          · exact absurd h3 (by simp)
          · exact mem_labelDefs_cons.mpr (Or.inr (ih h3))
  | jumpNext _ ih =>
      rcases mem_labelDefs_cons.mp hl with h' | h'
      · exact absurd h' (by simp)
      · rcases mem_labelDefs_cons.mp h' with h'' | h''
        · exact mem_labelDefs_cons.mpr (Or.inl h'')
        · exact mem_labelDefs_cons.mpr (Or.inr (ih h''))
  | jumpiNext _ ih =>
      rcases mem_labelDefs_cons.mp hl with h' | h'
      · exact absurd h' (by simp)
      · rcases mem_labelDefs_cons.mp h' with h'' | h''
        · exact mem_labelDefs_cons.mpr (Or.inr (mem_labelDefs_cons.mpr (Or.inl h'')))
        · exact mem_labelDefs_cons.mpr (Or.inr (mem_labelDefs_cons.mpr (Or.inr (ih h''))))
  | dropLabel hdrop _ ih =>
      rcases mem_labelDefs_cons.mp hl with h' | h'
      · cases h'; exact absurd hR hdrop
      · exact ih h'

/-- Membership in the referenced labels of a cons, by cases on the head. -/
theorem mem_labelRefs_cons {l : Label} {i : Asm} {p : List Asm} :
    l ∈ labelRefs (i :: p) ↔ i.references = some l ∨ l ∈ labelRefs p := by
  rw [labelRefs_cons, List.mem_append]
  cases h : i.references <;> simp [eq_comm]

/-- Optimization never introduces a label reference. -/
theorem codeRel_labelRefs_subset {R : List Label} {P Q : List Asm}
    (h : CodeRel R P Q) : ∀ l ∈ labelRefs Q, l ∈ labelRefs P := by
  induction h with
  | nil => exact fun l hl => hl
  | keep i _ ih =>
      intro l hl
      rcases mem_labelRefs_cons.mp hl with h' | h'
      · exact mem_labelRefs_cons.mpr (Or.inl h')
      · exact mem_labelRefs_cons.mpr (Or.inr (ih l h'))
  | window _ _ ih =>
      intro l hl
      rcases mem_labelRefs_cons.mp hl with h' | h'
      · exact absurd h' (by simp [Asm.references])
      · rcases mem_labelRefs_cons.mp h' with h'' | h''
        · exact absurd h'' (by simp [Asm.references])
        · exact mem_labelRefs_cons.mpr (Or.inr (mem_labelRefs_cons.mpr (Or.inr
            (mem_labelRefs_cons.mpr (Or.inr (ih l h''))))))
  | brInv _ ih =>
      intro l' hl'
      rcases mem_labelRefs_cons.mp hl' with h' | h'
      · exact absurd h' (by simp [Asm.references])
      · rcases mem_labelRefs_cons.mp h' with h'' | h''
        · -- the optimized `jumpi m` reference maps to the source `jump m`
          exact mem_labelRefs_cons.mpr (Or.inr (mem_labelRefs_cons.mpr
            (Or.inl (by simpa [Asm.references] using h''))))
        · rcases mem_labelRefs_cons.mp h'' with h3 | h3
          · exact absurd h3 (by simp [Asm.references])
          · exact mem_labelRefs_cons.mpr (Or.inr (mem_labelRefs_cons.mpr (Or.inr
              (mem_labelRefs_cons.mpr (Or.inr (ih l' h3))))))
  | dblIszero _ ih =>
      intro l' hl'
      rcases mem_labelRefs_cons.mp hl' with h' | h'
      · -- the kept `jumpi l` reference maps to the source `jumpi l`
        exact mem_labelRefs_cons.mpr (Or.inr (mem_labelRefs_cons.mpr (Or.inr
          (mem_labelRefs_cons.mpr (Or.inl h')))))
      · exact mem_labelRefs_cons.mpr (Or.inr (mem_labelRefs_cons.mpr (Or.inr
          (mem_labelRefs_cons.mpr (Or.inr (ih l' h'))))))
  | jumpNext _ ih =>
      intro l' hl'
      rcases mem_labelRefs_cons.mp hl' with h' | h'
      · exact absurd h' (by simp [Asm.references])
      · exact mem_labelRefs_cons.mpr (Or.inr (mem_labelRefs_cons.mpr (Or.inr (ih l' h'))))
  | jumpiNext _ ih =>
      intro l' hl'
      rcases mem_labelRefs_cons.mp hl' with h' | h'
      · exact absurd h' (by simp [Asm.references])
      · rcases mem_labelRefs_cons.mp h' with h'' | h''
        · exact absurd h'' (by simp [Asm.references])
        · exact mem_labelRefs_cons.mpr (Or.inr (mem_labelRefs_cons.mpr (Or.inr (ih l' h''))))
  | dropLabel _ _ ih =>
      intro l' hl'
      exact mem_labelRefs_cons.mpr (Or.inr (ih l' hl'))

/-- Optimization never grows the lowered byte size. -/
theorem codeRel_codeSize_le {R : List Label} {P Q : List Asm}
    (h : CodeRel R P Q) : codeSize Q ≤ codeSize P := by
  induction h with
  | nil => simp
  | keep i _ ih => rw [codeSize_cons, codeSize_cons]; omega
  | window _ _ ih => simp only [codeSize_cons, Asm.size]; omega
  | brInv _ ih => simp only [codeSize_cons, Asm.size]; omega
  | dblIszero _ ih => simp only [codeSize_cons, Asm.size]; omega
  | jumpNext _ ih => simp only [codeSize_cons, Asm.size]; omega
  | jumpiNext _ ih => simp only [codeSize_cons, Asm.size]; omega
  | dropLabel _ _ ih => simp only [codeSize_cons, Asm.size]; omega

/-- `findLabel` is preserved for every label that may be referenced, and the
found suffixes are again related. -/
theorem codeRel_findLabel {R : List Label} {P Q : List Asm} (h : CodeRel R P Q)
    {l : Label} (hR : l ∈ R) :
    ∀ {tgt : List Asm}, findLabel l P = some tgt →
      ∃ otgt, findLabel l Q = some otgt ∧ CodeRel R tgt otgt := by
  induction h with
  | nil => intro tgt hf; simp [findLabel] at hf
  | keep i hc ih =>
      intro tgt hf
      rw [findLabel] at hf
      by_cases hi : i = .label l
      · subst hi; rw [if_pos rfl] at hf
        obtain rfl := Option.some.inj hf
        exact ⟨_, by rw [findLabel, if_pos rfl], hc⟩
      · rw [if_neg hi] at hf
        obtain ⟨otgt, ho, hr⟩ := ih hf
        exact ⟨otgt, by rw [findLabel, if_neg hi]; exact ho, hr⟩
  | @brInv l0 m c c' hc ih =>
      intro tgt hf
      rw [findLabel, if_neg (by simp), findLabel, if_neg (by simp), findLabel] at hf
      by_cases hi : (Asm.label l0 : Asm) = .label l
      · rw [if_pos hi] at hf
        obtain rfl := Option.some.inj hf
        exact ⟨_, by
          rw [findLabel, if_neg (by simp), findLabel, if_neg (by simp),
            findLabel, if_pos hi], hc⟩
      · rw [if_neg hi] at hf
        obtain ⟨otgt, ho, hr⟩ := ih hf
        exact ⟨otgt, by
          rw [findLabel, if_neg (by simp), findLabel, if_neg (by simp),
            findLabel, if_neg hi]; exact ho, hr⟩
  | window hn hc ih =>
      intro tgt hf
      rw [findLabel, if_neg (by simp), findLabel, if_neg (by simp),
        findLabel, if_neg (by simp)] at hf
      obtain ⟨otgt, ho, hr⟩ := ih hf
      exact ⟨otgt, by
        rw [findLabel, if_neg (by simp), findLabel, if_neg (by simp)]
        exact ho, hr⟩
  | dblIszero hc ih =>
      intro tgt hf
      rw [findLabel, if_neg (by simp), findLabel, if_neg (by simp),
        findLabel, if_neg (by simp)] at hf
      obtain ⟨otgt, ho, hr⟩ := ih hf
      exact ⟨otgt, by rw [findLabel, if_neg (by simp)]; exact ho, hr⟩
  | @jumpNext l0 c c' hc ih =>
      intro tgt hf
      rw [findLabel, if_neg (by simp), findLabel] at hf
      by_cases hi : (Asm.label l0 : Asm) = .label l
      · rw [if_pos hi] at hf
        obtain rfl := Option.some.inj hf
        exact ⟨_, by rw [findLabel, if_pos hi], hc⟩
      · rw [if_neg hi] at hf
        obtain ⟨otgt, ho, hr⟩ := ih hf
        exact ⟨otgt, by rw [findLabel, if_neg hi]; exact ho, hr⟩
  | @jumpiNext l0 c c' hc ih =>
      intro tgt hf
      rw [findLabel, if_neg (by simp), findLabel] at hf
      by_cases hi : (Asm.label l0 : Asm) = .label l
      · rw [if_pos hi] at hf
        obtain rfl := Option.some.inj hf
        exact ⟨_, by rw [findLabel, if_neg (by simp), findLabel, if_pos hi], hc⟩
      · rw [if_neg hi] at hf
        obtain ⟨otgt, ho, hr⟩ := ih hf
        exact ⟨otgt, by rw [findLabel, if_neg (by simp), findLabel, if_neg hi]; exact ho, hr⟩
  | @dropLabel l0 hdrop c c' hc ih =>
      intro tgt hf
      have hne : (Asm.label l0 : Asm) ≠ .label l := by
        intro hEq
        exact hdrop (by cases hEq; exact hR)
      rw [findLabel, if_neg hne] at hf
      exact ih hf

/-- `CodeRel` preserves whole-program well-formedness (when `R` covers the
program's references), so lowering the optimized program still succeeds. -/
theorem codeRel_wf {R : List Label} {P Q : List Asm} (h : CodeRel R P Q)
    (hRefs : ∀ l ∈ labelRefs P, l ∈ R) (hw : WFProg P) : WFProg Q where
  nodup := hw.nodup.sublist (codeRel_labelDefs_sublist h)
  refsDefined := by
    intro l hl
    have hlP := codeRel_labelRefs_subset h l hl
    exact codeRel_labelDefs_mem h (hRefs l hlP) (hw.refsDefined l hlP)
  small := by have := codeRel_codeSize_le h; have := hw.small; omega

/-- `CodeRel R [] Q` forces `Q = []`. -/
theorem codeRel_nil_left {R : List Label} {Q : List Asm}
    (h : CodeRel R [] Q) : Q = [] := by
  cases h; rfl

end Peephole

end YulEvmCompiler
