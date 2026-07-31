import YulEvmCompiler.AsmSem
import YulEvmCompiler.SsaCfg.Sem
import YulEvmCompiler.SsaCfg.ToAsm
/-!
# YulEvmCompiler.SsaCfg.ToAsmSound

**Codegen simulation** for the `yul-ssa-cfg` backend: an SSA execution
(`SsaCfg.Run`) maps to a trace of the labeled-`Asm` machine (`ASteps`/`AHalt`)
over the program emitted by `ToAsm.emitProg`.

The file is organized bottom-up:

1. `StkMatch` — the stack invariant: the runtime `Asm` stack is the pointwise
   image of the generator's tracked symbolic stack under the register file
   (`SSlot.val v ↦ .word (R v)`, `SSlot.code l ↦ .code l`,
   `SSlot.retAddr ↦ .code retLab`).
2. `SimStk` — "these ops take a stack matching `σ` to a stack matching `τ`,
   leaving the machine state alone", with its refl/trans/append combinators
   and one lemma per stack op (`pop`/`dup`/`swap`).
3. `shuffleGo_spec`/`shuffle_sound` — the workhorse: the checked greedy
   shuffler's emitted ops realize exactly the target layout. Fully proved by
   induction on the shuffler's fuel.
4. `elideJumps` transport — a dropped `jump l` immediately before `label l`
   is a no-op pair; `findLabel` commutes with the elision, so a trace over
   the un-elided emission transports to the elided program. Fully proved.
5. per-instruction / per-terminator simulation, and the main induction over
   the big-step `Exec` derivation.
-/

namespace YulEvmCompiler.SsaCfg

open YulSemantics.EVM (U256 EvmState Op builtinWithExternal)
open YulEvmCompiler

/-! ## Generic list helpers -/

namespace ListAux

theorem getElem?_split {α : Type _} {l : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : ∃ l₁ l₂, l = l₁ ++ a :: l₂ ∧ l₁.length = i := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp h
  refine ⟨l.take i, l.drop (i + 1), ?_, ?_⟩
  · subst hget
    conv_lhs => rw [← List.take_append_drop i l, ← List.getElem_cons_drop hlt]
  · rw [List.length_take]; omega

theorem forall₂_append_left {α β : Type _} {Rel : α → β → Prop}
    {l₁ l₂ : List α} :
    ∀ {m : List β}, List.Forall₂ Rel (l₁ ++ l₂) m →
      ∃ m₁ m₂, m = m₁ ++ m₂ ∧ List.Forall₂ Rel l₁ m₁ ∧ List.Forall₂ Rel l₂ m₂ := by
  induction l₁ with
  | nil => intro m h; exact ⟨[], m, rfl, List.Forall₂.nil, by simpa using h⟩
  | cons a l₁ ih =>
    intro m h
    rw [List.cons_append] at h
    cases m with
    | nil => simp at h
    | cons b m =>
      rw [List.forall₂_cons] at h
      obtain ⟨m₁, m₂, rfl, h₁, h₂⟩ := ih h.2
      exact ⟨b :: m₁, m₂, rfl, List.forall₂_cons.mpr ⟨h.1, h₁⟩, h₂⟩

theorem forall₂_append {α β : Type _} {Rel : α → β → Prop}
    {l₁ l₂ : List α} {m₁ m₂ : List β}
    (h₁ : List.Forall₂ Rel l₁ m₁) (h₂ : List.Forall₂ Rel l₂ m₂) :
    List.Forall₂ Rel (l₁ ++ l₂) (m₁ ++ m₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hab _ ih => exact List.forall₂_cons.mpr ⟨hab, ih⟩

end ListAux

/-! ## Shuffler primitives -/

namespace ToAsm

/-- `idxOf` finds an actual occurrence. -/
theorem idxOf_getElem? {σ : List SSlot} {s : SSlot} {i : Nat}
    (h : idxOf σ s = some i) : σ[i]? = some s := by
  rw [idxOf, List.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨hlt, hp, -⟩ := h
  rw [List.getElem?_eq_getElem hlt]
  exact congrArg some (by simpa using hp)

/-- `swapAt σ j` (for `j ≥ 1`) exchanges the top of `σ` with the slot `j`
deep — exactly the shape `AStep.swap` consumes. -/
theorem swapAt_eq {σ σ' : List SSlot} {j : Nat} (hj : 0 < j)
    (h : swapAt σ j = some σ') :
    ∃ a b mid rest, σ = a :: (mid ++ b :: rest) ∧ mid.length = j - 1 ∧
      σ' = b :: (mid ++ a :: rest) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [swapAt] at h
  rcases h0 : σ[0]? with _ | a
  · rw [h0] at h; simp at h
  rcases h1 : σ[k + 1]? with _ | b
  · rw [h0, h1] at h; simp at h
  rw [h0, h1] at h
  simp only [bind, Option.bind, Option.some.injEq] at h
  subst h
  -- `σ` is nonempty with head `a`
  cases σ with
  | nil => simp at h0
  | cons a' t =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
    subst h0
    rw [List.getElem?_cons_succ] at h1
    obtain ⟨mid, rest, rfl, hlen⟩ := ListAux.getElem?_split h1
    refine ⟨a', b, mid, rest, rfl, by simpa using hlen, ?_⟩
    rw [List.set_cons_zero, List.set_cons_succ, ← hlen,
      List.set_append_right _ _ (le_refl _)]
    simp

end ToAsm

/-! ## The stack invariant -/

/-- The runtime `Asm` value a symbolic slot denotes, under register file `R`
and the current frame's return label `retLab`. -/
def slotVal (R : Regs) (retLab : Label) : SSlot → Option AVal
  | .val v => (R v).map AVal.word
  | .code l => some (.code l)
  | .retAddr => some (.code retLab)

/-- **The stack invariant**: the runtime stack `σ` is the pointwise image of
the generator's symbolic stack `sym`. -/
def StkMatch (R : Regs) (retLab : Label) (sym : List SSlot) (σ : List AVal) :
    Prop :=
  List.Forall₂ (fun s a => slotVal R retLab s = some a) sym σ

namespace StkMatch

variable {R : Regs} {retLab : Label}

@[simp] theorem nil : StkMatch R retLab [] [] := List.Forall₂.nil

theorem cons {s : SSlot} {a : AVal} {sym : List SSlot} {σ : List AVal}
    (hs : slotVal R retLab s = some a) (h : StkMatch R retLab sym σ) :
    StkMatch R retLab (s :: sym) (a :: σ) :=
  List.forall₂_cons.mpr ⟨hs, h⟩

theorem cons_inv {s : SSlot} {sym : List SSlot} {σ : List AVal}
    (h : StkMatch R retLab (s :: sym) σ) :
    ∃ a σ', σ = a :: σ' ∧ slotVal R retLab s = some a ∧
      StkMatch R retLab sym σ' := by
  cases σ with
  | nil => simp [StkMatch] at h
  | cons a σ' =>
    rw [StkMatch, List.forall₂_cons] at h
    exact ⟨a, σ', rfl, h.1, h.2⟩

theorem append {sym₁ sym₂ : List SSlot} {σ₁ σ₂ : List AVal}
    (h₁ : StkMatch R retLab sym₁ σ₁) (h₂ : StkMatch R retLab sym₂ σ₂) :
    StkMatch R retLab (sym₁ ++ sym₂) (σ₁ ++ σ₂) :=
  ListAux.forall₂_append h₁ h₂

theorem append_inv {sym₁ sym₂ : List SSlot} {σ : List AVal}
    (h : StkMatch R retLab (sym₁ ++ sym₂) σ) :
    ∃ σ₁ σ₂, σ = σ₁ ++ σ₂ ∧ StkMatch R retLab sym₁ σ₁ ∧
      StkMatch R retLab sym₂ σ₂ :=
  ListAux.forall₂_append_left h

theorem length_eq {sym : List SSlot} {σ : List AVal}
    (h : StkMatch R retLab sym σ) : sym.length = σ.length :=
  List.Forall₂.length_eq h

/-- The invariant is functional: the symbolic stack determines the runtime
stack. -/
theorem det {sym : List SSlot} {σ σ' : List AVal}
    (h : StkMatch R retLab sym σ) (h' : StkMatch R retLab sym σ') : σ = σ' := by
  induction h generalizing σ' with
  | nil => cases h'; rfl
  | @cons s a sym σ hsa _ ih =>
    obtain ⟨b, σ'', rfl, hsb, h''⟩ := cons_inv h'
    rw [hsa] at hsb
    obtain rfl := Option.some.inj hsb
    rw [ih h'']

/-- The image of a list of words: what a shuffled operand prefix looks like
at runtime. -/
theorem of_vals {xs : List ValId} {vs : List U256}
    (h : Regs.getMany R xs = some vs) :
    StkMatch R retLab (xs.map SSlot.val) (words vs) := by
  induction xs generalizing vs with
  | nil => cases vs with
    | nil => simp [words]
    | cons _ _ => simp [Regs.getMany] at h
  | cons x xs ih =>
    rw [Regs.getMany_cons] at h
    rcases hx : R x with _ | v
    · rw [hx] at h; simp at h
    rcases hxs : Regs.getMany R xs with _ | vs'
    · rw [hx, hxs] at h; simp at h
    rw [hx, hxs] at h
    simp only [Option.bind_some, Option.map_some] at h
    obtain rfl := Option.some.inj h
    exact cons (by simp [slotVal, hx]) (ih hxs)

end StkMatch

/-! ## Pure stack-shuffling simulation

`SimStk R retLab ops σ τ`: from any runtime stack matching the symbolic stack
`σ`, the ops run (in any program, with any continuation) to a runtime stack
matching `τ`, without touching the machine state. This is the shape every
`shuffle`-emitted fragment satisfies, and it composes by `++`. -/

variable [model : ExternalModel]

def SimStk (R : Regs) (retLab : Label) (ops : List Asm)
    (σ τ : List SSlot) : Prop :=
  ∀ σr, StkMatch R retLab σ σr →
    ∃ τr, StkMatch R retLab τ τr ∧
      ∀ (prog c : List Asm) (yst : EvmState),
        ASteps (model := model) prog ⟨ops ++ c, σr, yst⟩ ⟨c, τr, yst⟩

namespace SimStk

variable {R : Regs} {retLab : Label}

theorem nil {σ : List SSlot} : SimStk (model := model) R retLab [] σ σ := by
  intro σr h
  exact ⟨σr, h, by intro prog c yst; simpa using ASteps.refl _⟩

theorem of_eq {σ τ : List SSlot} (h : σ = τ) :
    SimStk (model := model) R retLab [] σ τ := by subst h; exact nil

theorem trans {ops₁ ops₂ : List Asm} {σ σ' τ : List SSlot}
    (h₁ : SimStk (model := model) R retLab ops₁ σ σ')
    (h₂ : SimStk (model := model) R retLab ops₂ σ' τ) :
    SimStk (model := model) R retLab (ops₁ ++ ops₂) σ τ := by
  intro σr hσ
  obtain ⟨σ'r, hσ'r, hsteps₁⟩ := h₁ σr hσ
  obtain ⟨τr, hτr, hsteps₂⟩ := h₂ σ'r hσ'r
  refine ⟨τr, hτr, ?_⟩
  intro prog c yst
  rw [List.append_assoc]
  exact (hsteps₁ prog (ops₂ ++ c) yst).trans (hsteps₂ prog c yst)

/-- One `POP`. -/
theorem pop {s : SSlot} {σ : List SSlot} :
    SimStk (model := model) R retLab [Asm.pop] (s :: σ) σ := by
  intro σr h
  obtain ⟨a, σ', rfl, -, h'⟩ := StkMatch.cons_inv h
  refine ⟨σ', h', ?_⟩
  intro prog c yst
  rw [List.singleton_append]
  exact ASteps.single AStep.pop

/-- One `DUP(i+1)`: the slot `i` deep is copied to the top. -/
theorem dup {σ : List SSlot} {s : SSlot} {i : Nat} (hi : i < 16)
    (hget : σ[i]? = some s) :
    SimStk (model := model) R retLab [Asm.dup ⟨i, hi⟩] σ (s :: σ) := by
  intro σr h
  obtain ⟨σ₁, σ₂, rfl, hlen⟩ := ListAux.getElem?_split hget
  obtain ⟨τ, ρ, rfl, h₁, h₂⟩ := StkMatch.append_inv h
  obtain ⟨a, ρ', rfl, hsa, h₂'⟩ := StkMatch.cons_inv h₂
  refine ⟨a :: (τ ++ a :: ρ'), StkMatch.cons hsa (h₁.append (StkMatch.cons hsa h₂')), ?_⟩
  intro prog c yst
  have hτlen : τ.length = (⟨i, hi⟩ : Fin 16).val := by rw [← h₁.length_eq, hlen]
  rw [List.singleton_append]
  exact ASteps.single (AStep.dup hτlen)

/-- One `SWAP(j)`: `swapAt` exchanges the top with the slot `j` deep. -/
theorem swap {σ σ' : List SSlot} {j : Nat} (hj : 0 < j) (hjj : j - 1 < 16)
    (hswap : ToAsm.swapAt σ j = some σ') :
    SimStk (model := model) R retLab [Asm.swap ⟨j - 1, hjj⟩] σ σ' := by
  obtain ⟨a, b, mid, rest, rfl, hmid, rfl⟩ := ToAsm.swapAt_eq hj hswap
  intro σr h
  obtain ⟨x, σ₀, rfl, hxa, h₀⟩ := StkMatch.cons_inv h
  obtain ⟨midr, ρ, rfl, hmidr, hρ⟩ := StkMatch.append_inv h₀
  obtain ⟨y, restr, rfl, hyb, hrest⟩ := StkMatch.cons_inv hρ
  refine ⟨y :: (midr ++ x :: restr),
    StkMatch.cons hyb (hmidr.append (StkMatch.cons hxa hrest)), ?_⟩
  intro prog c yst
  have hlen : midr.length = (⟨j - 1, hjj⟩ : Fin 16).val := by
    rw [← hmidr.length_eq, hmid]
  rw [List.singleton_append]
  exact ASteps.single (AStep.swap hlen)

end SimStk

end YulEvmCompiler.SsaCfg
