import YulEvmCompiler.Asm
set_option warningAsError true
/-!
# YulEvmCompiler.AsmPeephole

An **assembly-level (Asm → Asm) peephole optimizer**: the transform and its
label-structure preservation. This is the "separate, Asm→Asm soundness
contract" layer: unlike the source (Yul→Yul) optimizer, it rewrites the
compiler's labelled control-flow IR directly, so it can exploit patterns the
source optimizer cannot express — in particular the **calling convention**
the backend emits for return-value slots.

## The rewrite

The single rewrite realized here is the return-slot assignment idiom

```text
  push v ; swap1 ; pop   ⟶   pop ; push v
```

Both sequences have the identical net effect "replace the top of the stack
with the literal `v`", but the right-hand side is one `SWAP1` (3 gas, 1 byte)
cheaper. The backend emits the left-hand form whenever a function body writes
a constant into its (top) return slot (e.g. `multiRet`, `multiAssign`,
`multiRet3`); the source optimizer never sees it because return slots are a
backend calling-convention artifact.

## Structure

* `optimizeAsm` — the concrete linear scan.
* `CodeRel` — a **spec** relation between a source suffix and an optimized
  suffix. `optimizeAsm` is one *implementation*; `codeRel_optimize` proves it
  always produces a `CodeRel`-related program. `CodeRel` preserves `labelDefs`,
  `labelRefs`, `findLabel` (`codeRel_findLabel`) and does not grow `codeSize`,
  hence preserves `WFProg` (`codeRel_wf`).

The forward simulation against the phase-A step relation lives in
`YulEvmCompiler.AsmPeepholeSound` (this module stays byte- and
semantics-free); `YulEvmCompiler.Compile.compile` inserts `optimizeAsm`
between `compileProgram` and `lowerProg`.
-/

namespace YulEvmCompiler

open YulSemantics.EVM (U256 EvmState Op)

/-! ### The concrete transform -/

/-- The Asm-level peephole pass: rewrite every `push v ; swap1 ; pop` window to
the equivalent, cheaper `pop ; push v`. All other instructions pass through. -/
def optimizeAsm : List Asm → List Asm
  | .push v :: .swap ⟨0, _⟩ :: .pop :: rest => .pop :: .push v :: optimizeAsm rest
  | i :: rest => i :: optimizeAsm rest
  | [] => []

/-! ### The spec relation on code suffixes -/

namespace Peephole

/-- Relates a source program suffix to a valid optimized suffix. `optimizeAsm`
is a particular strategy; `codeRel_optimize` shows its output is always
`CodeRel`-related to its input. Keeping the relation separate from the concrete
function makes the simulation and the label-structure lemmas independent of the
scan order. -/
inductive CodeRel : List Asm → List Asm → Prop
  /-- Empty programs are related. -/
  | nil : CodeRel [] []
  /-- Keep an instruction verbatim. -/
  | keep (i : Asm) {c c' : List Asm} : CodeRel c c' → CodeRel (i :: c) (i :: c')
  /-- Rewrite a return-slot window. `n` is `swap1` (`n.val = 0`). -/
  | window {v : U256} {n : Fin 16} (hn : n.val = 0) {c c' : List Asm} :
      CodeRel c c' →
      CodeRel (.push v :: .swap n :: .pop :: c) (.pop :: .push v :: c')

/-- `optimizeAsm` always produces a `CodeRel`-related program. -/
theorem codeRel_optimize (p : List Asm) : CodeRel p (optimizeAsm p) := by
  fun_induction optimizeAsm p with
  | case1 v n rest ih => exact CodeRel.window (n := ⟨0, n⟩) rfl ih
  | case2 i rest _ ih => exact CodeRel.keep i ih
  | case3 => exact CodeRel.nil

/-! ### `CodeRel` preserves label structure -/

theorem codeRel_labelDefs {P Q : List Asm} (h : CodeRel P Q) :
    labelDefs P = labelDefs Q := by
  induction h with
  | nil => rfl
  | keep i _ ih => rw [labelDefs_cons, labelDefs_cons, ih]
  | window _ _ ih => simp only [labelDefs, List.filterMap_cons, Asm.defines]; exact ih

theorem codeRel_labelRefs {P Q : List Asm} (h : CodeRel P Q) :
    labelRefs P = labelRefs Q := by
  induction h with
  | nil => rfl
  | keep i _ ih => rw [labelRefs_cons, labelRefs_cons, ih]
  | window _ _ ih => simp only [labelRefs, List.filterMap_cons, Asm.references]; exact ih

theorem codeRel_codeSize_le {P Q : List Asm} (h : CodeRel P Q) :
    codeSize Q ≤ codeSize P := by
  induction h with
  | nil => simp
  | keep i _ ih => rw [codeSize_cons, codeSize_cons]; omega
  | window _ _ ih => simp only [codeSize_cons, Asm.size]; omega

theorem codeRel_findLabel {P Q : List Asm} (h : CodeRel P Q) :
    ∀ {l : Label} {tgt : List Asm}, findLabel l P = some tgt →
      ∃ otgt, findLabel l Q = some otgt ∧ CodeRel tgt otgt := by
  induction h with
  | nil => intro l tgt hf; simp [findLabel] at hf
  | keep i hc ih =>
      intro l tgt hf
      rw [findLabel] at hf
      by_cases hi : i = .label l
      · subst hi; rw [if_pos rfl] at hf
        obtain rfl := Option.some.inj hf
        exact ⟨_, by rw [findLabel, if_pos rfl], hc⟩
      · rw [if_neg hi] at hf
        obtain ⟨otgt, ho, hr⟩ := ih hf
        exact ⟨otgt, by rw [findLabel, if_neg hi]; exact ho, hr⟩
  | window hn hc ih =>
      intro l tgt hf
      rw [findLabel, if_neg (by simp), findLabel, if_neg (by simp),
        findLabel, if_neg (by simp)] at hf
      obtain ⟨otgt, ho, hr⟩ := ih hf
      exact ⟨otgt, by rw [findLabel, if_neg (by simp), findLabel, if_neg (by simp)]; exact ho, hr⟩

/-- `CodeRel` preserves whole-program well-formedness, so lowering the optimized
program still succeeds. -/
theorem codeRel_wf {P Q : List Asm} (h : CodeRel P Q) (hw : WFProg P) : WFProg Q where
  nodup := codeRel_labelDefs h ▸ hw.nodup
  refsDefined := by
    intro l hl
    rw [← codeRel_labelDefs h]
    exact hw.refsDefined l (by rw [codeRel_labelRefs h]; exact hl)
  small := by have := codeRel_codeSize_le h; have := hw.small; omega

/-- `CodeRel [] Q` forces `Q = []`. -/
theorem codeRel_nil_left {Q : List Asm} (h : CodeRel [] Q) : Q = [] := by
  cases h; rfl

end Peephole

end YulEvmCompiler
