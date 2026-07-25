import YulIR.FrameBigStep

set_option warningAsError true
/-!
# YulIR.FrameCongr — congruence lemmas for frame-IR equivalence

The reusable infrastructure for lifting a local rewrite to a whole pass: equivalence is a congruence
for each block-forming operation. `EquivBlock.consStmt` (in `FrameBigStep`) already handles `::`;
here are the `if`-body congruence, block **append** congruence (via an execution-decomposition lemma
for `++`, what `structural`'s statement-splicing needs), and the `loop`/`switch` body congruences.
The loop one goes through `loopImp`, an induction over the loop-unrolling derivation (the standard
"generalize the code, induct, discharge the non-loop constructors with `nofun`" pattern); the switch
one factors through `selectCase_congr`, congruence of the branch a constant scrutinee selects.
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

/-! ### Loop congruence -/

private theorem loopImp {funs : Funs} {post₁ post₂ body₁ body₂ : Block n}
    (hpost : EquivBlock funs post₁ post₂) (hbody : EquivBlock funs body₁ body₂) :
    ∀ {σ : Store n} {st code res}, Step funs σ st code res → code = .loop post₁ body₁ →
      Step funs σ st (.loop post₂ body₂) res := by
  intro σ st code res h
  induction h with
  | loopBrk hb ihb =>
      intro hcode; injection hcode with h1 h2; subst h1; subst h2
      exact Step.loopBrk ((hbody _ _ _ _ _).mp hb)
  | loopLeave hb ihb =>
      intro hcode; injection hcode with h1 h2; subst h1; subst h2
      exact Step.loopLeave ((hbody _ _ _ _ _).mp hb)
  | loopHalt hb ihb =>
      intro hcode; injection hcode with h1 h2; subst h1; subst h2
      exact Step.loopHalt ((hbody _ _ _ _ _).mp hb)
  | loopStep hb hob hp hl ihb ihp ihl =>
      intro hcode; injection hcode with h1 h2; subst h1; subst h2
      exact Step.loopStep ((hbody _ _ _ _ _).mp hb) hob ((hpost _ _ _ _ _).mp hp)
        (ihl hpost hbody rfl)
  | loopPostStop hb hob hp hne ihb ihp =>
      intro hcode; injection hcode with h1 h2; subst h1; subst h2
      exact Step.loopPostStop ((hbody _ _ _ _ _).mp hb) hob ((hpost _ _ _ _ _).mp hp) hne
  | _ => exact nofun

/-- **Loop congruence**: equivalent post/body blocks give equivalent loops. -/
theorem EquivStmt.loop_congr {funs : Funs} {post₁ post₂ body₁ body₂ : Block n}
    (hpost : EquivBlock funs post₁ post₂) (hbody : EquivBlock funs body₁ body₂) :
    EquivStmt funs (.loop post₁ body₁) (.loop post₂ body₂) := by
  intro σ st σ' st' o
  constructor
  · intro h; cases h with
    | loopS h' => exact .loopS (loopImp hpost hbody h' rfl)
  · intro h; cases h with
    | loopS h' => exact .loopS (loopImp hpost.symm hbody.symm h' rfl)

/-! ### Switch congruence -/

open YulSemantics (Literal)
open YulSemantics.EVM (litValue)

/-- Congruence of the block a constant `switch` selects, under case-wise equivalence. -/
theorem selectCase_congr {funs : Funs} {cv : U256} {cs₁ cs₂ : List (Literal × Block n)}
    {df₁ df₂ : Option (Block n)}
    (hcs : List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock funs p.2 q.2) cs₁ cs₂)
    (hdf : EquivBlock funs (df₁.getD []) (df₂.getD [])) :
    EquivBlock funs (selectCase cv cs₁ df₁) (selectCase cv cs₂ df₂) := by
  induction hcs with
  | nil => simpa only [selectCase, List.find?_nil] using hdf
  | @cons p q cs₁' cs₂' hpq _ ih =>
      obtain ⟨hlabel, hblk⟩ := hpq
      unfold selectCase
      by_cases hm : (litValue p.1 == cv) = true
      · have hmq : (litValue q.1 == cv) = true := by rw [← hlabel]; exact hm
        rw [List.find?_cons_of_pos (by simpa using hm), List.find?_cons_of_pos (by simpa using hmq)]
        exact hblk
      · have hmq : ¬ (litValue q.1 == cv) = true := by rw [← hlabel]; exact hm
        rw [List.find?_cons_of_neg (by simpa using hm), List.find?_cons_of_neg (by simpa using hmq)]
        exact ih

/-- **Switch congruence**: a common scrutinee with case-wise / default equivalent bodies gives
equivalent `switch`es. -/
theorem EquivStmt.switch_congr {funs : Funs} {c : Atom n} {cs₁ cs₂ : List (Literal × Block n)}
    {df₁ df₂ : Option (Block n)}
    (hcs : List.Forall₂ (fun p q => p.1 = q.1 ∧ EquivBlock funs p.2 q.2) cs₁ cs₂)
    (hdf : EquivBlock funs (df₁.getD []) (df₂.getD [])) :
    EquivStmt funs (.switch c cs₁ df₁) (.switch c cs₂ df₂) := by
  intro σ st σ' st' o
  constructor
  · intro h; cases h with
    | switch h' => exact .switch ((selectCase_congr hcs hdf _ _ _ _ _).mp h')
  · intro h; cases h with
    | switch h' => exact .switch ((selectCase_congr hcs hdf _ _ _ _ _).mpr h')

end YulIR.FinFrame.Sem
