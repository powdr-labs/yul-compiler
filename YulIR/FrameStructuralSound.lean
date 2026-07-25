import YulIR.FrameOptimize
import YulIR.FrameCongr
import YulIR.FrameSound
import YulIR.FrameFunCongr

set_option warningAsError true
/-!
# YulIR.FrameStructuralSound — whole-pass soundness of `structuralBlock`

Composes the local rewrite lemmas (`YulIR.FrameSound`) with the congruences
(`YulIR.FrameCongr`) over the *actual* `structuralBlock` pass, via its functional-induction
principle `structuralBlock.induct`. The headline result is

  `structuralBlock_equiv : EquivBlock funs (structuralBlock b) b`

— i.e. structural simplification (dead `if 0`, `if 1`/nonzero-`if` splice, empty-`if` removal,
constant-`switch` selection, recursing through every nested block) preserves the frame big-step
semantics at a fixed function table, for *every* block. This is the first whole-pass soundness
theorem on the frame IR (the earlier `FrameSound` lemmas covered hand-written single statements).
Dropping unreachable code (`dropUnreachableBlock`, the other half of `structural`) is separate.
-/

namespace YulIR.FinFrame.Sem

open YulSemantics (Outcome Literal)
open YulSemantics.EVM (litValue)

/-! ### Literal-condition evaluation for the pass's `isZeroLit`/`isNonzeroLit` tests -/

/-- A zero literal evaluates to `0` under any store. -/
theorem evalAtom_isZeroLit {c : Atom n} (σ : Store n) (h : c.isZeroLit = true) :
    evalAtom σ c = 0 := by
  cases c with
  | slot i => simp [Atom.isZeroLit] at h
  | lit l  => simpa only [evalAtom] using beq_iff_eq.mp (by simpa [Atom.isZeroLit] using h)

/-- A nonzero literal evaluates to something `≠ 0` under any store. -/
theorem evalAtom_isNonzeroLit {c : Atom n} (σ : Store n) (h : c.isNonzeroLit = true) :
    evalAtom σ c ≠ 0 := by
  cases c with
  | slot i => simp [Atom.isNonzeroLit] at h
  | lit l  => simpa only [evalAtom] using bne_iff_ne.mp (by simpa [Atom.isNonzeroLit] using h)

/-! ### Generalized single-`cond` rewrites (any zero/nonzero literal, empty body) -/

/-- `if <zero-lit> { body }` ≡ nothing. -/
theorem cond_isZero (funs : Funs) {c : Atom n} (body : Block n) (hc : c.isZeroLit = true) :
    EquivBlock funs [Stmt.cond c body] [] := by
  intro σ st σ' st' o
  constructor
  · intro h
    cases block_singleton_inv h with
    | condFalse _    => exact .nil
    | condTrue hc' _ => exact absurd (evalAtom_isZeroLit σ hc) hc'
  · intro h; cases h with
    | nil => exact block_singleton (.condFalse (evalAtom_isZeroLit σ hc))

/-- `if c { }` (empty body) ≡ nothing, for *any* condition. -/
theorem cond_empty (funs : Funs) {c : Atom n} : EquivBlock funs [Stmt.cond c []] [] := by
  intro σ st σ' st' o
  constructor
  · intro h
    cases block_singleton_inv h with
    | condFalse _       => exact .nil
    | condTrue _ hbody  => cases hbody with | nil => exact .nil
  · intro h; cases h with
    | nil =>
        by_cases hc : evalAtom σ c = 0
        · exact block_singleton (.condFalse hc)
        · exact block_singleton (.condTrue hc .nil)

/-- `if <nonzero-lit> { body }` ≡ `body` (spliced). -/
theorem cond_isNonzero (funs : Funs) {c : Atom n} (body : Block n) (hc : c.isNonzeroLit = true) :
    EquivBlock funs [Stmt.cond c body] body := by
  intro σ st σ' st' o
  constructor
  · intro h
    cases block_singleton_inv h with
    | condFalse hc'    => exact absurd hc' (evalAtom_isNonzeroLit σ hc)
    | condTrue _ hbody => exact hbody
  · intro h; exact block_singleton (.condTrue (evalAtom_isNonzeroLit σ hc) h)

/-! ### Singleton congruences -/

/-- Lift a statement equivalence to the one-element blocks. -/
theorem EquivStmt.toSingleton {funs : Funs} {s₁ s₂ : Stmt n} (hs : EquivStmt funs s₁ s₂) :
    EquivBlock funs [s₁] [s₂] :=
  EquivBlock.consStmt hs (EquivBlock.refl funs [])

/-! ### `selectLit` is `selectCase` at the literal's value -/

theorem selectLit_eq_selectCase (k : Literal) (cs : List (Literal × Block n))
    (df : Option (Block n)) : selectLit k cs df = selectCase (litValue k) cs df := rfl

/-! ### Whole-pass soundness of `structuralBlock` -/

/-- **Structural simplification preserves semantics**, for every block. Proved by functional
induction on the pass itself, discharging each rewrite with the corresponding `FrameSound` lemma and
each recursive/structural case with the matching congruence from `FrameCongr`. -/
theorem structuralBlock_equiv (funs : Funs) (b : Block n) :
    EquivBlock funs (structuralBlock b) b := by
  refine structuralBlock.induct
    (motive_1 := fun s => EquivBlock funs (structuralStmt s) [s])
    (motive_2 := fun df => EquivBlock funs ((structuralDflt df).getD []) (df.getD []))
    (motive_3 := fun b => EquivBlock funs (structuralBlock b) b)
    (motive_4 := fun cs =>
      List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock funs p.2 q.2) (structuralCases cs) cs)
    ?cond0 ?cond1 ?condE ?swLit ?swVar ?loop ?stmt ?bnil ?bcons ?cnil ?ccons ?dnone ?dsome b
  -- cond, dead (zero condition or empty body): structuralStmt = []
  case cond0 =>
    intro c body hcz ih
    rw [structuralStmt.eq_1, if_pos hcz]
    -- [] ≡ [cond c body], via [cond c body] ≡ [cond c (structuralBlock body)] ≡ []
    have step2 : EquivBlock funs [Stmt.cond c (structuralBlock body)] [] := by
      simp only [Bool.or_eq_true] at hcz
      rcases hcz with hz | he
      · exact cond_isZero funs (structuralBlock body) hz
      · have hb : structuralBlock body = [] := by simpa using he
        rw [hb]; exact cond_empty funs
    exact (EquivBlock.trans (EquivStmt.toSingleton (EquivStmt.cond_congr ih.symm)) step2).symm
  -- cond, always taken (nonzero literal, nonempty body): structuralStmt = structuralBlock body
  case cond1 =>
    intro c body hcz hnz ih
    rw [structuralStmt.eq_1, if_neg hcz, if_pos hnz]
    exact (EquivBlock.trans (EquivStmt.toSingleton (EquivStmt.cond_congr ih.symm))
      (cond_isNonzero funs (structuralBlock body) hnz)).symm
  -- cond, kept: structuralStmt = [cond c (structuralBlock body)]
  case condE =>
    intro c body hcz hnz ih
    rw [structuralStmt.eq_1, if_neg hcz, if_neg hnz]
    exact EquivStmt.toSingleton (EquivStmt.cond_congr ih)
  -- switch with literal scrutinee: structuralStmt = selectLit k cs' df'
  case swLit =>
    intro cs df k ihcs ihdf
    rw [structuralStmt.eq_2]
    exact EquivBlock.trans (selectCase_congr ihcs ihdf) (structural_switch funs k cs df).symm
  -- switch with non-literal scrutinee: structuralStmt = [switch c cs' df']
  case swVar =>
    intro c cs df hne ihcs ihdf
    rw [structuralStmt.eq_3 c cs df hne]
    exact EquivStmt.toSingleton (EquivStmt.switch_congr ihcs ihdf)
  -- loop
  case loop =>
    intro post body ihp ihb
    rw [structuralStmt.eq_4]
    exact EquivStmt.toSingleton (EquivStmt.loop_congr ihp ihb)
  -- other statements (write/writeMany/effect/break/continue/leave): structuralStmt s = [s]
  case stmt =>
    intro s hnc hns hnl
    rw [structuralStmt.eq_5 s hnc hns hnl]
    exact EquivBlock.refl funs [s]
  -- block nil
  case bnil => exact EquivBlock.refl funs []
  -- block cons
  case bcons =>
    intro s ss ihs ihss
    rw [structuralBlock.eq_2]
    exact EquivBlock.append_congr ihs ihss
  -- cases nil
  case cnil => exact .nil
  -- cases cons
  case ccons =>
    intro l b rest ihb ihrest
    rw [structuralCases.eq_2]
    exact List.Forall₂.cons ⟨rfl, ihb⟩ ihrest
  -- default none
  case dnone => exact EquivBlock.refl funs []
  -- default some
  case dsome =>
    intro b ihb
    rw [structuralDflt.eq_2]; exact ihb

/-! ### Whole-program lifting -/

/-- **Whole-program soundness of structural simplification**: applying `structuralBlock` to every
function body in the table (the entry point `none` included) yields a program with identical runs —
one `run_mapBodies` over the unified function table. -/
theorem structural_program_run (p : Program) {st st' o} :
    Run p st st' o ↔ Run ⟨mapBodiesFuns (fun _ b => structuralBlock b) p.functions⟩ st st' o :=
  run_mapBodies _ (fun F fd => structuralBlock_equiv F fd.body)

end YulIR.FinFrame.Sem
