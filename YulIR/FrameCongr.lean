import YulIR.FrameBigStep

set_option warningAsError true
/-!
# YulIR.FrameCongr — congruence lemmas for frame-IR equivalence

The reusable infrastructure for lifting a local rewrite to a whole pass: equivalence is a congruence
for each block-forming operation. `EquivBlock.consStmt` (in `FrameBigStep`) already handles `::`;
here are the `if`-body congruence and block **append** congruence (via an execution-decomposition
lemma for `++`), which is what `structural`'s statement-splicing needs. `switch`/`loop` body
congruences are future work (the loop one needs induction over iterations).
-/

namespace YulIR.FinFrame.Sem

open YulSemantics (Outcome)

/-- `if`-body congruence: equivalent bodies give equivalent conditionals. -/
theorem EquivStmt.cond_congr {funs : Funs} {c : Atom n} {b₁ b₂ : Block n}
    (hb : EquivBlock funs b₁ b₂) : EquivStmt funs (.cond c b₁) (.cond c b₂) := by
  intro σ st σ' st' o
  constructor
  · intro h; cases h with
    | condFalse hc  => exact .condFalse hc
    | condTrue hc h => exact .condTrue hc ((hb _ _ _ _ _).mp h)
  · intro h; cases h with
    | condFalse hc  => exact .condFalse hc
    | condTrue hc h => exact .condTrue hc ((hb _ _ _ _ _).mpr h)

/-- Execution of a block append decomposes: either the prefix finishes `normal` and the suffix runs,
or the prefix ends with a non-`normal` outcome (short-circuit). -/
theorem execBlock_append {funs : Funs} {a b : Block n} {σ st σ' st' o} :
    ExecBlock funs σ st (a ++ b) σ' st' o ↔
      (∃ σm stm, ExecBlock funs σ st a σm stm .normal ∧ ExecBlock funs σm stm b σ' st' o)
      ∨ (ExecBlock funs σ st a σ' st' o ∧ o ≠ .normal) := by
  induction a generalizing σ st with
  | nil =>
      simp only [List.nil_append]
      constructor
      · intro h; exact Or.inl ⟨σ, st, .nil, h⟩
      · rintro (⟨_, _, hnil, hb⟩ | ⟨hnil, hne⟩)
        · cases hnil; exact hb
        · cases hnil; exact absurd rfl hne
  | cons s rest ih =>
      simp only [List.cons_append]
      constructor
      · intro h; cases h with
        | consNormal hs hrest =>
            rcases ih.mp hrest with ⟨σm, stm, ha, hb⟩ | ⟨ha, hne⟩
            · exact Or.inl ⟨σm, stm, .consNormal hs ha, hb⟩
            · exact Or.inr ⟨.consNormal hs ha, hne⟩
        | consStop hs hne => exact Or.inr ⟨.consStop hs hne, hne⟩
      · rintro (⟨σm, stm, ha, hb⟩ | ⟨ha, hne⟩)
        · cases ha with
          | consNormal hs ha' => exact .consNormal hs (ih.mpr (Or.inl ⟨σm, stm, ha', hb⟩))
          | consStop _ hne    => exact absurd rfl hne
        · cases ha with
          | consNormal hs ha' => exact .consNormal hs (ih.mpr (Or.inr ⟨ha', hne⟩))
          | consStop hs hne'  => exact .consStop hs hne'

/-- Block **append** congruence. -/
theorem EquivBlock.append_congr {funs : Funs} {a₁ a₂ b₁ b₂ : Block n}
    (ha : EquivBlock funs a₁ a₂) (hb : EquivBlock funs b₁ b₂) :
    EquivBlock funs (a₁ ++ b₁) (a₂ ++ b₂) := by
  intro σ st σ' st' o
  rw [execBlock_append, execBlock_append]
  constructor
  · rintro (⟨σm, stm, haa, hbb⟩ | ⟨haa, hne⟩)
    · exact Or.inl ⟨σm, stm, (ha _ _ _ _ _).mp haa, (hb _ _ _ _ _).mp hbb⟩
    · exact Or.inr ⟨(ha _ _ _ _ _).mp haa, hne⟩
  · rintro (⟨σm, stm, haa, hbb⟩ | ⟨haa, hne⟩)
    · exact Or.inl ⟨σm, stm, (ha _ _ _ _ _).mpr haa, (hb _ _ _ _ _).mpr hbb⟩
    · exact Or.inr ⟨(ha _ _ _ _ _).mpr haa, hne⟩

end YulIR.FinFrame.Sem
