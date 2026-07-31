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

## Status

Fully proved (no `sorry`, no new axioms): the `StkMatch` machinery, the
shuffler (`shuffleGo_spec`, `shuffle_sound`), the whole `elideJumps` transport
(`findLabel_elideJumps`, `astep_elideJumps`, `asteps_elideJumps`,
`ahalt_elideJumps`), the register-file bookkeeping, `emitInstr_const_sim`,
`emitInstr_op_sim` and `emitTerm_halt_sim`. `emitProg_asteps'` and
`emitProg_ahalt'` are *derived* — their proofs are complete modulo the three
outstanding lemmas `emitBlock_emitRest`, `exec_sim` and `emitProg_placement`.

Both target statements need two hypotheses beyond the ones in
`SsaCfg/Correctness.lean`; `P.wfCheck = true` is not optional — without it the
statements are false, see the counterexample documented at
`emitProg_asteps'`. -/

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

/-! ## The checked shuffler is correct

`shuffleGo` only ever returns at its `σ = τ` base case, so a successful run
both certifies the final symbolic stack *is* the target and hands back a
trace realizing it. -/

omit model in
private theorem cons_rev_append (op : Asm) (acc ops : List Asm) :
    (op :: acc).reverse ++ ops = acc.reverse ++ (op :: ops) := by simp

theorem shuffleGo_spec (R : Regs) (retLab : Label) (τ : List SSlot) :
    ∀ (fuel : Nat) (σ : List SSlot) (acc ops : List Asm) (final : List SSlot),
      ToAsm.shuffleGo τ fuel σ acc = some (ops, final) →
      final = τ ∧ ∃ ops', ops = acc.reverse ++ ops' ∧
        SimStk (model := model) R retLab ops' σ τ := by
  intro fuel
  induction fuel with
  | zero => intro σ acc ops final h; simp [ToAsm.shuffleGo] at h
  | succ fuel ih =>
    intro σ acc ops final h
    rw [ToAsm.shuffleGo.eq_def] at h
    dsimp only at h
    split at h
    · -- base case: the symbolic stack already *is* the target
      rename_i hστ
      obtain ⟨rfl, rfl⟩ : ops = acc.reverse ∧ final = σ := by
        simpa [Prod.ext_iff, eq_comm] using h
      exact ⟨hστ, [], by simp, SimStk.of_eq hστ⟩
    · rename_i hστ
      cases σ with
      | nil => dsimp only at h; exact absurd h (by simp)
      | cons top rest =>
        dsimp only at h
        split at h
        · -- surplus top: `POP`
          obtain ⟨rfl, ops', rfl, hsim⟩ := ih _ _ _ _ h
          exact ⟨rfl, Asm.pop :: ops', cons_rev_append _ _ _,
            SimStk.trans SimStk.pop hsim⟩
        · split at h
          · -- deficit slot: `DUP` it up
            rename_i need hneed
            split at h
            · rename_i i hidx
              split at h
              · rename_i hi
                obtain ⟨rfl, ops', rfl, hsim⟩ := ih _ _ _ _ h
                exact ⟨rfl, Asm.dup ⟨i, hi⟩ :: ops', cons_rev_append _ _ _,
                  SimStk.trans
                    (SimStk.dup hi (ToAsm.idxOf_getElem? hidx)) hsim⟩
              · exact absurd h (by simp)
            · exact absurd h (by simp)
          · split at h
            · -- a place where the top belongs: `SWAP`
              rename_i j hfix
              have hj0 : 0 < j := by
                have hp := List.find?_some hfix
                simp only [decide_eq_true_eq] at hp
                exact hp.1
              split at h
              · rename_i σ' hswap
                split at h
                · rename_i hjj
                  obtain ⟨rfl, ops', rfl, hsim⟩ := ih _ _ _ _ h
                  exact ⟨rfl, Asm.swap ⟨j - 1, hjj⟩ :: ops',
                    cons_rev_append _ _ _,
                    SimStk.trans (SimStk.swap hj0 hjj hswap) hsim⟩
                · exact absurd h (by simp)
              · exact absurd h (by simp)
            · split at h
              · -- shallowest mismatch to the top: `SWAP`
                rename_i j hmis
                have hj0 : 0 < j := by
                  have hp := List.find?_some hmis
                  simp only [decide_eq_true_eq] at hp
                  exact hp.1
                split at h
                · rename_i σ' hswap
                  split at h
                  · rename_i hjj
                    obtain ⟨rfl, ops', rfl, hsim⟩ := ih _ _ _ _ h
                    exact ⟨rfl, Asm.swap ⟨j - 1, hjj⟩ :: ops',
                      cons_rev_append _ _ _,
                      SimStk.trans (SimStk.swap hj0 hjj hswap) hsim⟩
                  · exact absurd h (by simp)
                · exact absurd h (by simp)
              · exact absurd h (by simp)

/-- **The shuffle lemma**: a successful `shuffle σ τ` emits ops that take any
runtime stack matching `σ` to one matching `τ`, leaving the machine state
untouched. -/
theorem shuffle_sound {R : Regs} {retLab : Label} {σ τ : List SSlot}
    {ops : List Asm} (h : ToAsm.shuffle σ τ = some ops) :
    SimStk (model := model) R retLab ops σ τ := by
  rw [ToAsm.shuffle] at h
  rcases hgo : ToAsm.shuffleGo τ
      ((σ.length + τ.length + 2) * (σ.length + τ.length + 2)) σ [] with
    _ | ⟨ops', final⟩
  · rw [hgo] at h; simp at h
  rw [hgo] at h
  simp only [bind, Option.bind] at h
  obtain ⟨-, ops'', hops, hsim⟩ := shuffleGo_spec (model := model) R retLab τ _ _ _ _ _ hgo
  split at h
  · obtain rfl := Option.some.inj h
    rw [hops]; simpa using hsim
  · exact absurd h (by simp)

/-! ## `elideJumps` transport

`emitProg` post-processes the emission by dropping every `jump l` that sits
immediately before `label l` (the block-order fall-through). This is a no-op
pair — the jump lands exactly where the fall-through would — so an `Asm`
trace over the un-elided emission transports to the elided program. -/

namespace ToAsm

omit model in
theorem elideJumps_jump_ne {l : Label} {c : List Asm}
    (h : ∀ rest, c ≠ Asm.label l :: rest) :
    elideJumps (Asm.jump l :: c) = Asm.jump l :: elideJumps c := by
  cases c with
  | nil => simp [elideJumps]
  | cons i rest =>
    cases i
    case label l' =>
      have hne : ¬ l = l' := fun hl => h rest (by rw [hl])
      simp [elideJumps, hne]
    all_goals simp [elideJumps]

omit model in
theorem elideJumps_jump_eq (l : Label) (rest : List Asm) :
    elideJumps (Asm.jump l :: Asm.label l :: rest) = Asm.label l :: elideJumps rest := by
  simp [elideJumps]

omit model in
/-- The elision removes no label definition (it only drops `jump`s). -/
@[simp] theorem labelDefs_elideJumps (p : List Asm) :
    labelDefs (elideJumps p) = labelDefs p := by
  fun_induction elideJumps p with
  | case1 lj rest ih => simp [labelDefs_cons, Asm.defines, ih]
  | case2 lj lj' rest hne ih => simp [labelDefs_cons, Asm.defines, ih]
  | case3 a rest _ ih => simp [labelDefs_cons, ih]
  | case4 => simp

omit model in
/-- `findLabel` commutes with the elision. -/
theorem findLabel_elideJumps (l : Label) (p : List Asm) :
    findLabel l (elideJumps p) = (findLabel l p).map elideJumps := by
  fun_induction elideJumps p with
  | case1 lj rest ih =>
    by_cases hlj : lj = l
    · subst hlj; simp [findLabel]
    · simp [findLabel, hlj, ih]
  | case2 lj lj' rest hne ih =>
    by_cases hlj : lj' = l
    · subst hlj; simp [findLabel]
    · simp [findLabel, hlj, ih]
  | case3 a rest _ ih =>
    by_cases ha : a = Asm.label l
    · subst ha; simp [findLabel]
    · rw [findLabel, findLabel, if_neg ha, if_neg ha, ih]
  | case4 => simp [findLabel]

omit model in
/-- Elision consumes the head instruction either as itself (the usual case)
or not at all (the dropped `jump`). -/
theorem elideJumps_cons_cases (i : Asm) (q : List Asm) :
    elideJumps (i :: q) = i :: elideJumps q ∨ elideJumps (i :: q) = elideJumps q := by
  cases i
  case jump l =>
    cases q
    case nil => left; simp [elideJumps]
    case cons a rest =>
      cases a
      case label l' =>
        by_cases hl : l = l'
        · subst hl; right; simp [elideJumps]
        · left; simp [elideJumps, hl]
      all_goals (left; simp [elideJumps])
  all_goals (left; simp [elideJumps])

omit model in
theorem elideJumps_cons_suffix (i : Asm) (q : List Asm) :
    elideJumps q <:+ elideJumps (i :: q) := by
  rcases elideJumps_cons_cases i q with h | h
  · exact ⟨[i], by rw [h]; simp⟩
  · exact ⟨[], by rw [h]; simp⟩

omit model in
/-- Every suffix of the un-elided program elides to a suffix of the elided
program — the fragment-placement fact the transport needs. -/
theorem elideJumps_suffix {c p : List Asm} (h : c <:+ p) :
    elideJumps c <:+ elideJumps p := by
  obtain ⟨pre, rfl⟩ := h
  induction pre with
  | nil => simp
  | cons i pre ih =>
    rw [List.cons_append]
    exact ih.trans (elideJumps_cons_suffix i (pre ++ c))

omit model in @[simp] theorem elideJumps_push (v : U256) (c : List Asm) :
    elideJumps (Asm.push v :: c) = Asm.push v :: elideJumps c := by simp [elideJumps]
omit model in @[simp] theorem elideJumps_op (yop : Op) (c : List Asm) :
    elideJumps (Asm.op yop :: c) = Asm.op yop :: elideJumps c := by simp [elideJumps]
omit model in @[simp] theorem elideJumps_dup (n : Fin 16) (c : List Asm) :
    elideJumps (Asm.dup n :: c) = Asm.dup n :: elideJumps c := by simp [elideJumps]
omit model in @[simp] theorem elideJumps_swapOp (n : Fin 16) (c : List Asm) :
    elideJumps (Asm.swap n :: c) = Asm.swap n :: elideJumps c := by simp [elideJumps]
omit model in @[simp] theorem elideJumps_pop (c : List Asm) :
    elideJumps (Asm.pop :: c) = Asm.pop :: elideJumps c := by simp [elideJumps]
omit model in @[simp] theorem elideJumps_label (l : Label) (c : List Asm) :
    elideJumps (Asm.label l :: c) = Asm.label l :: elideJumps c := by simp [elideJumps]
omit model in @[simp] theorem elideJumps_jumpi (l : Label) (c : List Asm) :
    elideJumps (Asm.jumpi l :: c) = Asm.jumpi l :: elideJumps c := by simp [elideJumps]
omit model in @[simp] theorem elideJumps_pushLabel (l : Label) (c : List Asm) :
    elideJumps (Asm.pushLabel l :: c) = Asm.pushLabel l :: elideJumps c := by
  simp [elideJumps]
omit model in @[simp] theorem elideJumps_dynJump (c : List Asm) :
    elideJumps (Asm.dynJump :: c) = Asm.dynJump :: elideJumps c := by simp [elideJumps]

end ToAsm

/-- The elision's action on an `Asm` configuration. -/
def elideConf (a : AConf) : AConf := ⟨ToAsm.elideJumps a.code, a.stk, a.yst⟩

/-- **One step transports across the elision.** The only interesting case is
`jump l` immediately before `label l`: the elided program falls through the
label instead, which is a single `AStep.label` landing in the same place (by
`findLabel_boundary`, using label uniqueness). -/
theorem astep_elideJumps {prog : List Asm} (hnodup : (labelDefs prog).Nodup)
    {a b : AConf} (ha : a.code <:+ prog)
    (h : AStep (model := model) prog a b) :
    ASteps (model := model) (ToAsm.elideJumps prog) (elideConf a) (elideConf b) := by
  cases h with
  | @push v c σ yst =>
    simp only [elideConf, ToAsm.elideJumps_push]; exact ASteps.single AStep.push
  | @op yop args rets c σ yst yst' hb =>
    simp only [elideConf, ToAsm.elideJumps_op]; exact ASteps.single (AStep.op hb)
  | @dup n v τ ρ c yst hlen =>
    simp only [elideConf, ToAsm.elideJumps_dup]
    exact ASteps.single (AStep.dup hlen)
  | @swap n x y τ ρ c yst hlen =>
    simp only [elideConf, ToAsm.elideJumps_swapOp]
    exact ASteps.single (AStep.swap hlen)
  | @pop v σ c yst =>
    simp only [elideConf, ToAsm.elideJumps_pop]; exact ASteps.single AStep.pop
  | @label l c σ yst =>
    simp only [elideConf, ToAsm.elideJumps_label]; exact ASteps.single AStep.label
  | @jump l c c' σ yst hfind =>
    by_cases hc : ∃ rest, c = Asm.label l :: rest
    · obtain ⟨rest, rfl⟩ := hc
      obtain ⟨pre, hpre⟩ := ha
      have hsplit : prog = (pre ++ [Asm.jump l]) ++ Asm.label l :: rest := by
        rw [← hpre]; simp
      have hfl : findLabel l prog = some rest := by
        rw [hsplit]; exact findLabel_boundary (by rw [← hsplit]; exact hnodup)
      rw [hfl] at hfind
      obtain rfl := Option.some.inj hfind
      simp only [elideConf, ToAsm.elideJumps_jump_eq]
      exact ASteps.single AStep.label
    · have hne : ∀ rest, c ≠ Asm.label l :: rest := fun rest heq => hc ⟨rest, heq⟩
      simp only [elideConf, ToAsm.elideJumps_jump_ne hne]
      refine ASteps.single (AStep.jump ?_)
      rw [ToAsm.findLabel_elideJumps, hfind]; rfl
  | @jumpiTaken l v c c' σ yst hv hfind =>
    simp only [elideConf, ToAsm.elideJumps_jumpi]
    refine ASteps.single (AStep.jumpiTaken hv ?_)
    rw [ToAsm.findLabel_elideJumps, hfind]; rfl
  | @jumpiFall l v c σ yst hv =>
    simp only [elideConf, ToAsm.elideJumps_jumpi]
    exact ASteps.single (AStep.jumpiFall hv)
  | @pushLabel l c σ yst hmem =>
    simp only [elideConf, ToAsm.elideJumps_pushLabel]
    refine ASteps.single (AStep.pushLabel ?_)
    rw [ToAsm.labelDefs_elideJumps]; exact hmem
  | @dynJump l c c' σ yst hfind =>
    simp only [elideConf, ToAsm.elideJumps_dynJump]
    refine ASteps.single (AStep.dynJump ?_)
    rw [ToAsm.findLabel_elideJumps, hfind]; rfl

/-- **Whole traces transport across the elision.** -/
theorem asteps_elideJumps {prog : List Asm} (hnodup : (labelDefs prog).Nodup)
    {a b : AConf} (h : ASteps (model := model) prog a b) :
    a.code <:+ prog →
      ASteps (model := model) (ToAsm.elideJumps prog) (elideConf a) (elideConf b) := by
  induction h with
  | refl => intro _; exact ASteps.refl _
  | head hstep hsteps ih =>
    intro ha
    exact (astep_elideJumps hnodup ha hstep).trans (ih (hstep.suffix ha))

/-- **Halting configurations transport across the elision.** -/
theorem ahalt_elideJumps {prog : List Asm} {a : AConf} {yst' : EvmState}
    (h : AHalt (model := model) prog a yst') :
    AHalt (model := model) (ToAsm.elideJumps prog) (elideConf a) yst' := by
  cases h with
  | @op yop args c σ yst _ hb =>
    simp only [elideConf, ToAsm.elideJumps_op]; exact AHalt.op hb

/-! ## Register-file bookkeeping

An instruction's *definitions* must be fresh with respect to whatever is
still on the symbolic stack — otherwise `R.setMany ds …` would silently
overwrite a value the stack still refers to. That is exactly single
assignment, which `Prog.wfCheck` decides (see the discussion at
`emitProg_asteps'`); the codegen lemmas take it as the `AgreeOn` hypothesis
below so the obligation is isolated in one place. -/

namespace Regs

omit model in
@[simp] theorem setMany_nil (R : Regs) (vs : List U256) : R.setMany [] vs = R := rfl

omit model in
@[simp] theorem setMany_nil_vals (R : Regs) (xs : List ValId) : R.setMany xs [] = R := by
  cases xs <;> rfl

omit model in
theorem setMany_cons (R : Regs) (x : ValId) (xs : List ValId) (v : U256)
    (vs : List U256) : R.setMany (x :: xs) (v :: vs) = (R.set x v).setMany xs vs := rfl

omit model in
theorem setMany_not_mem {xs : List ValId} :
    ∀ {R : Regs} {vs : List U256} {y : ValId}, y ∉ xs → (R.setMany xs vs) y = R y := by
  induction xs with
  | nil => intro R vs y _; rfl
  | cons x xs ih =>
    intro R vs y hy
    cases vs with
    | nil => rfl
    | cons v vs =>
      have hne : y ≠ x := fun he => hy (by simp [he])
      rw [setMany_cons, ih (fun hm => hy (List.mem_cons_of_mem _ hm)),
        Regs.set_other _ _ hne]

omit model in
theorem getMany_setMany {xs : List ValId} :
    ∀ {R : Regs} {vs : List U256}, xs.Nodup → xs.length = vs.length →
      (R.setMany xs vs).getMany xs = some vs := by
  induction xs with
  | nil => intro R vs _ hlen; cases vs with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    intro R vs hnd hlen
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      have hx : x ∉ xs := (List.nodup_cons.mp hnd).1
      rw [setMany_cons, Regs.getMany_cons, setMany_not_mem hx, Regs.set_same,
        ih (List.nodup_cons.mp hnd).2 (by simpa using hlen)]
      rfl

end Regs

/-- `R'` agrees with `R` on every value the symbolic stack `sym` mentions. -/
def AgreeOn (R R' : Regs) (sym : List SSlot) : Prop :=
  ∀ v, SSlot.val v ∈ sym → R' v = R v

omit model in
theorem StkMatch.mono {R R' : Regs} {retLab : Label} :
    ∀ {sym : List SSlot} {σ : List AVal}, StkMatch R retLab sym σ →
      AgreeOn R R' sym → StkMatch R' retLab sym σ := by
  intro sym
  induction sym with
  | nil => intro σ h _; cases σ with
    | nil => exact StkMatch.nil
    | cons _ _ => simp [StkMatch] at h
  | cons s sym ih =>
    intro σ h hag
    obtain ⟨a, σ', rfl, hsa, h'⟩ := StkMatch.cons_inv h
    refine StkMatch.cons ?_ (ih h' (fun v hv => hag v (List.mem_cons_of_mem _ hv)))
    cases s with
    | val v =>
      rw [slotVal, hag v List.mem_cons_self]; exact hsa
    | code l => exact hsa
    | retAddr => exact hsa

/-! ## Per-instruction simulation -/

/-- Instruction-level simulation: `asmf` takes a runtime stack matching `sym`
under `R` in machine state `st` to one matching `sym'` under `R'` in `st'`. -/
def SimInstr (R R' : Regs) (retLab : Label) (asmf : List Asm)
    (sym sym' : List SSlot) (st st' : EvmState) : Prop :=
  ∀ σr, StkMatch R retLab sym σr →
    ∃ σr', StkMatch R' retLab sym' σr' ∧
      ∀ (prog c : List Asm),
        ASteps (model := model) prog ⟨asmf ++ c, σr, st⟩ ⟨c, σr', st'⟩

omit model in
theorem liftE_bind_inv {α β : Type} {o : Option α} {f : α → ToAsm.E β} {n : Nat}
    {r : β} {n' : Nat} (h : (ToAsm.liftE o >>= f) n = some (r, n')) :
    ∃ a, o = some a ∧ f a n = some (r, n') := by
  cases o with
  | none => simp [ToAsm.liftE, StateT.bind, bind] at h
  | some a =>
    exact ⟨a, rfl, by simpa [ToAsm.liftE, StateT.bind, bind, pure, StateT.pure] using h⟩

/-- `const`: a single `PUSH`. -/
theorem emitInstr_const_sim {P : Prog} {L : ToAsm.LabelMap} {sym : List SSlot}
    {needed : List ValId} {d : ValId} {v : U256} {n n' : Nat}
    {asmf : List Asm} {sym' : List SSlot} {R : Regs} {retLab : Label}
    {st : EvmState}
    (hemit : ToAsm.emitInstr P L sym needed (.const d v) n = some ((asmf, sym'), n'))
    (hfresh : AgreeOn R (R.set d v) sym) :
    SimInstr (model := model) R (R.set d v) retLab asmf sym sym' st st := by
  have h : (([Asm.push v], SSlot.val d :: sym), n) = ((asmf, sym'), n') :=
    Option.some.inj (by rw [← hemit]; rfl)
  obtain ⟨⟨rfl, rfl⟩, -⟩ := Prod.mk.injEq .. ▸ h
  intro σr hm
  refine ⟨AVal.word v :: σr, StkMatch.cons (by simp [slotVal]) (hm.mono hfresh), ?_⟩
  intro prog c
  rw [List.singleton_append]
  exact ASteps.single AStep.push

/-- A built-in that returns: the checked shuffle brings the operands to the
top in order, then `AStep.op` consumes exactly the `builtinWithExternal`
premise the SSA rule provides. -/
theorem emitInstr_op_sim {P : Prog} {L : ToAsm.LabelMap} {sym : List SSlot}
    {needed : List ValId} {ds : List ValId} {yop : Op} {as : List ValId}
    {n n' : Nat} {asmf : List Asm} {sym' : List SSlot} {R : Regs}
    {retLab : Label} {args rets : List U256} {st st' : EvmState}
    (hemit : ToAsm.emitInstr P L sym needed (.op ds yop as) n = some ((asmf, sym'), n'))
    (hget : R.getMany as = some args)
    (hb : builtinWithExternal model.calls model.creates yop args st (.ok rets st'))
    (hlen : ds.length = rets.length) (hnd : ds.Nodup)
    (hfresh : AgreeOn R (R.setMany ds rets) (ToAsm.keepOf sym needed)) :
    SimInstr (model := model) R (R.setMany ds rets) retLab asmf sym sym' st st' := by
  rw [ToAsm.emitInstr] at hemit
  obtain ⟨ops, hsh, heq⟩ := liftE_bind_inv hemit
  obtain ⟨⟨rfl, rfl⟩, -⟩ := Prod.mk.injEq .. ▸
    (Option.some.inj (by rw [← heq]; rfl) :
      ((ops ++ [Asm.op yop], List.map SSlot.val ds ++ ToAsm.keepOf sym needed), n)
        = ((asmf, sym'), n'))
  intro σr hm
  obtain ⟨τr, hτr, hsteps⟩ := shuffle_sound (model := model) (R := R) (retLab := retLab) hsh σr hm
  obtain ⟨σa, σk, rfl, hσa, hσk⟩ := StkMatch.append_inv hτr
  obtain rfl : σa = words args := hσa.det (StkMatch.of_vals hget)
  refine ⟨words rets ++ σk,
    (StkMatch.of_vals (Regs.getMany_setMany hnd hlen)).append (hσk.mono hfresh), ?_⟩
  intro prog c
  rw [List.append_assoc]
  refine (hsteps prog ([Asm.op yop] ++ c) st).trans (ASteps.single ?_)
  rw [List.singleton_append]
  exact AStep.op hb

/-! ## Halting terminators

`emitTerm` for `.halt yop as` shuffles the operands to the top and emits
`op yop`; whatever follows (the dead barrier that keeps the linear
stack-certificate walk honest) is never executed, so the trace simply stops
at the halting op. -/

omit model in
/-- Inverting a `pure` in the emission monad. -/
theorem E_pure_inv {α : Type} {X r : α} {n n' : Nat}
    (h : (pure X : ToAsm.E α) n = some (r, n')) : X = r := by
  have h' : some ((X, n) : α × Nat) = some (r, n') := h
  exact ((Prod.mk.injEq ..).mp (Option.some.inj h')).1

omit model in
/-- Both branches of the halting terminator emit
`shuffle … ++ op yop ++ dead barrier`. -/
theorem emitTerm_halt_shape {isFunc : Bool} {f : Func} {L : ToAsm.LabelMap}
    {fidx : Option Nat} {liveIn : Array (List ValId)} {sym : List SSlot}
    {yop : Op} {as : List ValId} {n n' : Nat} {asmf : List Asm}
    (hemit : ToAsm.emitTerm isFunc f L fidx liveIn sym (.halt yop as) n
      = some (asmf, n')) :
    ∃ ops barrier,
      ToAsm.shuffle sym
          (as.map SSlot.val ++ ToAsm.removeOnce sym (as.map SSlot.val)) = some ops
        ∧ asmf = ops ++ Asm.op yop :: barrier := by
  rw [ToAsm.emitTerm] at hemit
  obtain ⟨ops, hsh, heq⟩ := liftE_bind_inv hemit
  refine ⟨ops, ?_⟩
  dsimp only at heq
  split at heq
  · split at heq
    · exact absurd heq (by simp [ToAsm.liftE])
    · have hA := E_pure_inv heq
      simp only [List.append_assoc, List.singleton_append] at hA
      exact ⟨_, hsh, hA.symm⟩
  · have hA := E_pure_inv heq
    simp only [List.append_assoc, List.singleton_append] at hA
    exact ⟨_, hsh, hA.symm⟩

/-- **A halting terminator simulates**: the shuffle brings the operands to the
top, then the emitted `op yop` halts with the source's final state. The dead
barrier the generator appends after it is never walked. -/
theorem emitTerm_halt_sim {isFunc : Bool} {f : Func} {L : ToAsm.LabelMap}
    {fidx : Option Nat} {liveIn : Array (List ValId)} {sym : List SSlot}
    {yop : Op} {as : List ValId} {n n' : Nat} {asmf : List Asm}
    {R : Regs} {retLab : Label} {args : List U256} {st st' : EvmState}
    {σr : List AVal}
    (hemit : ToAsm.emitTerm isFunc f L fidx liveIn sym (.halt yop as) n
      = some (asmf, n'))
    (hget : R.getMany as = some args)
    (hb : builtinWithExternal model.calls model.creates yop args st (.halt st'))
    (hmatch : StkMatch R retLab sym σr) :
    ∀ (prog c : List Asm), ∃ conf,
      ASteps (model := model) prog ⟨asmf ++ c, σr, st⟩ conf ∧
      AHalt (model := model) prog conf st' := by
  obtain ⟨ops, barrier, hsh, rfl⟩ := emitTerm_halt_shape hemit
  intro prog c
  obtain ⟨τr, hτr, hsteps⟩ :=
    shuffle_sound (model := model) (R := R) (retLab := retLab) hsh σr hmatch
  obtain ⟨σa, σk, rfl, hσa, hσk⟩ := StkMatch.append_inv hτr
  obtain rfl : σa = words args := hσa.det (StkMatch.of_vals hget)
  refine ⟨⟨Asm.op yop :: (barrier ++ c), words args ++ σk, st⟩, ?_, AHalt.op hb⟩
  rw [List.append_assoc, List.cons_append]
  exact hsteps prog (Asm.op yop :: (barrier ++ c)) st

/-! ## The rest of a block, as the big-step relation walks it

`emitBlock` folds `emitInstr` over the block's instructions (paired with their
needed-after sets) and finishes with `emitTerm`. The big-step `Exec` relation
consumes exactly a *suffix* of that, so the simulation induction is stated
over `emitRest`, which is the same fold written as a recursion. -/

def emitRest (P : Prog) (L : ToAsm.LabelMap) (isFunc : Bool) (f : Func)
    (fidx : Option Nat) (liveIn : Array (List ValId)) (t : Term) :
    List (Instr × List ValId) → List SSlot → ToAsm.E (List Asm)
  | [], sym => ToAsm.emitTerm isFunc f L fidx liveIn sym t
  | (i, need) :: rest, sym => do
      let (asm, sym') ← ToAsm.emitInstr P L sym need i
      let tl ← emitRest P L isFunc f fidx liveIn t rest sym'
      pure (asm ++ tl)

omit model in
/-- **Bridge from `emitBlock`'s fold to `emitRest`** (proof outstanding): a
successful block emission is the block's label followed by `emitRest` over the
whole instruction list from the block's entry layout. Purely a `foldlM`
rearrangement in `StateT Nat Option`; no semantic content. -/
theorem emitBlock_emitRest {P : Prog} {L : ToAsm.LabelMap} {fidx : Option Nat}
    {f : Func} {liveIn : Array (List ValId)} {bid : BlockId} {b : Block}
    {n n' : Nat} {frag : List Asm}
    (h : ToAsm.emitBlock P L fidx f liveIn bid b n
      = some (Asm.label (ToAsm.blkLabel L fidx bid) :: frag, n')) :
    ∃ (paired : List (Instr × List ValId)) (sym0 : List SSlot),
      paired.map Prod.fst = b.instrs
      ∧ sym0 = (if bid = f.entry then
            f.params.map SSlot.val ++ (if fidx.isSome then [SSlot.retAddr] else [])
          else ToAsm.layoutOf fidx.isSome (liveIn[bid]?.getD []) b)
      ∧ emitRest P L fidx.isSome f fidx liveIn b.term paired sym0 n = some (frag, n') := by
  sorry

/-! ## Fragment placement

The classic Phase A (`SimAsm.lean`) locates each fragment inside the whole
program by list appends and resolves labels with `findLabel_boundary` from the
compile-time `Nodup` fact. The same holds here, one fragment per basic block;
`Placement` packages it. -/

/-- Block `bid` of function `fidx` has its emitted body sitting in `asm`
right after its label. -/
def BlockPlaced (P : Prog) (asm : List Asm) (fidx : Option Nat) (f : Func)
    (liveIn : Array (List ValId)) (bid : BlockId) (b : Block) : Prop :=
  ∃ (n n' : Nat) (frag tail : List Asm),
    ToAsm.emitBlock P (ToAsm.mkLabelMap P) fidx f liveIn bid b n
      = some (Asm.label (ToAsm.blkLabel (ToAsm.mkLabelMap P) fidx bid) :: frag, n')
    ∧ findLabel (ToAsm.blkLabel (ToAsm.mkLabelMap P) fidx bid) asm
      = some (frag ++ tail)

/-- Every block of every function is placed; the terminal label is last (so
`main`'s `ret []` runs off the end of the code with an empty stack); and
`main`'s entry label heads the program. -/
def Placement (P : Prog) (asm : List Asm) : Prop :=
  (∃ liveIn, ToAsm.liveInSets P.main = some liveIn ∧
      ∀ bid b, P.main.blocks[bid]? = some b →
        BlockPlaced P asm none P.main liveIn bid b)
  ∧ (∀ i g, P.funcs[i]? = some g → ∃ liveIn, ToAsm.liveInSets g = some liveIn ∧
      ∀ bid b, g.blocks[bid]? = some b → BlockPlaced P asm (some i) g liveIn bid b)
  ∧ findLabel (ToAsm.mkLabelMap P).endLabel asm = some []
  ∧ (∃ c, asm = Asm.label (ToAsm.blkLabel (ToAsm.mkLabelMap P) none P.main.entry) :: c)

/-! ## The frame-level simulation goal -/

/-- What one SSA frame owes the `Asm` machine: a `ret` returns to the frame's
return label with the return values on top of the caller's untouched stack; a
halt reaches a configuration whose head instruction halts with the same final
state. For `main` the "return label" is the terminal label, whose continuation
is the empty code — which is how a `.normal` outcome lands in `⟨[], [], yst'⟩`. -/
def SimFRes (asm : List Asm) (retLab : Label) (below : List AVal)
    (a : AConf) : FRes → Prop
  | .ret vals st' =>
      ∃ cret, findLabel retLab asm = some cret ∧
        ASteps (model := model) asm a ⟨cret, words vals ++ below, st'⟩
  | .halt st' =>
      ∃ conf, ASteps (model := model) asm a conf ∧
        AHalt (model := model) asm conf st'

/-! ## The main induction

Every `Exec` constructor maps to a bounded `Asm` trace segment:

* `const` — `AStep.push` (`emitInstr_const_sim`), then the IH;
* `op`/`opHalt` — the checked shuffle (`shuffle_sound`) plus `AStep.op` /
  `AHalt.op`, whose `builtinWithExternal` premise is literally the SSA rule's
  (`emitInstr_op_sim`);
* `call`/`callHalt` — `pushLabel`, the argument `DUP`s, `jump` to the callee's
  entry (placed by `Placement`), the callee's IH with the fresh register file,
  and `dynJump` back through the `.code retLab` still on the stack;
* `jump`/`branchTrue`/`branchFalse` — the edge shuffle onto the target's entry
  layout (`edgeLayout`), then `AStep.jump`/`jumpi` resolved by
  `findLabel_boundary`, then the IH at the target block;
* `ret` — the epilogue rotation lifting the return address, then `dynJump`
  (in `main`: pop everything and `jump` the terminal label);
* `halt` — `emitTerm_halt_sim`.

The freshness side conditions (`AgreeOn`) come from single assignment, i.e.
from `P.wfCheck`; see the discussion at `emitProg_asteps'`. -/
theorem exec_sim {P : Prog} {asm : List Asm}
    (hnodup : (labelDefs asm).Nodup) (hwf : P.wfCheck = true)
    (hplace : Placement P asm)
    {f : Func} {R : Regs} {st : EvmState} {rest : Rest} {res : FRes}
    (hexec : Exec (model := model) P f R st rest res) :
    ∀ (fidx : Option Nat) (liveIn : Array (List ValId))
      (paired : List (Instr × List ValId)) (sym : List SSlot)
      (n n' : Nat) (frag tail : List Asm) (retLab : Label)
      (below σr : List AVal),
      paired.map Prod.fst = rest.instrs →
      emitRest P (ToAsm.mkLabelMap P) fidx.isSome f fidx liveIn rest.term paired sym n
        = some (frag, n') →
      StkMatch R retLab sym σr →
      (findLabel retLab asm).isSome →
      SimFRes (model := model) asm retLab below
        ⟨frag ++ tail, σr ++ below, st⟩ res := by
  induction hexec
  case const =>
    -- `AStep.push` (`emitInstr_const_sim`) then the IH on the shortened rest
    intro fidx liveIn paired sym n n' frag tail retLab below σr hpair hemit hm hret
    sorry
  case op =>
    -- `emitInstr_op_sim` (fully proved above) then the IH
    intro fidx liveIn paired sym n n' frag tail retLab below σr hpair hemit hm hret
    sorry
  case opHalt =>
    -- the shuffle, then `AHalt.op` on the emitted `op yop`
    intro fidx liveIn paired sym n n' frag tail retLab below σr hpair hemit hm hret
    sorry
  case call =>
    -- pushLabel / arg DUPs / jump entry / callee IH / dynJump back
    intro fidx liveIn paired sym n n' frag tail retLab below σr hpair hemit hm hret
    sorry
  case callHalt =>
    -- as `call`, but the callee's IH already produces the halting configuration
    intro fidx liveIn paired sym n n' frag tail retLab below σr hpair hemit hm hret
    sorry
  case jump =>
    -- edge shuffle onto the target's entry layout, `AStep.jump`, target IH
    intro fidx liveIn paired sym n n' frag tail retLab below σr hpair hemit hm hret
    sorry
  case branchTrue =>
    -- shuffle to `cond :: layout(true)`, `AStep.jumpiTaken`, target IH
    intro fidx liveIn paired sym n n' frag tail retLab below σr hpair hemit hm hret
    sorry
  case branchFalse =>
    -- `AStep.jumpiFall`, the fall-through shuffle, target IH
    intro fidx liveIn paired sym n n' frag tail retLab below σr hpair hemit hm hret
    sorry
  case ret =>
    -- function: epilogue rotation + `dynJump`; main: pops + `jump endLabel`
    intro fidx liveIn paired sym n n' frag tail retLab below σr hpair hemit hm hret
    sorry
  case halt =>
    -- `emitTerm_halt_sim`
    intro fidx liveIn paired sym n n' frag tail retLab below σr hpair hemit hm hret
    sorry

/-! ## Placement of `emitProg`'s output -/

omit model in
/-- **`emitProg` places its fragments** (proof outstanding): the accepted
program is the elision of a raw emission in which every block's body sits
right after its label, the terminal label is last, and `main`'s entry label is
first. This is the `SimAsm.lean` Phase-A bookkeeping (fragment concatenation
plus `findLabel_boundary` from `Nodup`), specialized to one fragment per basic
block. -/
theorem emitProg_placement {P : Prog} {asm : List Asm}
    (hwf : P.wfCheck = true) (hemit : ToAsm.emitProg P = some asm) :
    ∃ asm₀ : List Asm, asm = ToAsm.elideJumps asm₀ ∧ Placement P asm₀ := by
  sorry

/-- Entering `main`'s entry block: one `AStep.label` off the head of the
program lands in the entry fragment with an empty stack, which matches the
entry layout (`main` has no parameters), so the frame-level simulation applies
with the terminal label as the frame's "return" label. -/
private theorem raw_entry_sim {P : Prog} {asm₀ : List Asm}
    (hnodup₀ : (labelDefs asm₀).Nodup) (hwf : P.wfCheck = true)
    (hpl : Placement P asm₀) {yst0 : EvmState} {res : FRes} {eb : Block}
    (heb : P.main.blocks[P.main.entry]? = some eb)
    (hexec : Exec (model := model) P P.main Regs.empty yst0
      ⟨eb.instrs, eb.term⟩ res) :
    ∃ a : AConf, ASteps (model := model) asm₀ ⟨asm₀, [], yst0⟩ a ∧
      SimFRes (model := model) asm₀ (ToAsm.mkLabelMap P).endLabel [] a res := by
  have hpl' := hpl
  obtain ⟨⟨liveIn, -, hblocks⟩, -, hend, c, hhead⟩ := hpl'
  obtain ⟨n, n', frag, tail, hblk, hfind⟩ := hblocks _ _ heb
  -- the entry fragment heads the program
  have hc : c = frag ++ tail := by
    rw [hhead, findLabel, if_pos rfl] at hfind
    exact Option.some.inj hfind
  have hasm : asm₀ = Asm.label (ToAsm.blkLabel (ToAsm.mkLabelMap P) none P.main.entry)
      :: (frag ++ tail) := by rw [hhead, hc]
  obtain ⟨paired, sym0, hpair, hsym0, hrest⟩ := emitBlock_emitRest hblk
  -- `main` takes no parameters, so its entry layout is empty
  have hp : P.main.params = [] := by
    have hwf' := hwf
    rw [Prog.wfCheck] at hwf'
    simp only [Bool.and_eq_true] at hwf'
    simpa using hwf'.1.1.1
  have hsym : sym0 = [] := by rw [hsym0]; simp [hp]
  refine ⟨⟨frag ++ tail, [] ++ [], yst0⟩, ?_, ?_⟩
  · refine ASteps.single ?_
    rw [hasm]; exact AStep.label
  · refine exec_sim hnodup₀ hwf hpl hexec none liveIn paired sym0 n n' frag tail
      (ToAsm.mkLabelMap P).endLabel [] [] hpair hrest ?_ ?_
    · rw [hsym]; exact StkMatch.nil
    · rw [hend]; rfl

/-! ## The codegen simulation

Both statements need two hypotheses beyond the ones in
`SsaCfg/Correctness.lean`'s `emitProg_asteps`/`emitProg_ahalt`:

* `(labelDefs asm).Nodup` — `AStep.jump`/`jumpiTaken`/`dynJump` resolve labels
  with `findLabel`, and identifying the fragment a jump lands in needs label
  uniqueness. `finishProg` already establishes it (`wfCheck asm`), so the
  integration in `finishProg_correct` can thread it (it in fact already
  computes `hnodup`).

* `P.wfCheck = true` — **single assignment**. Without it the statements are
  *false*: the generator pushes a `const`'s destination onto its symbolic
  stack without checking whether that `ValId` is already there, so a program
  that defines the same id twice makes the symbolic stack claim two slots hold
  the same value while the runtime stack holds two *different* words. The
  concrete counterexample (checked by `#eval`):

  ```
  main.blocks = #[ ⟨[], [const 0 0, const 0 7], branch 0 ⟨1,[]⟩ ⟨2,[]⟩⟩,
                   ⟨[], [], halt stop []⟩,
                   ⟨[], [], ret []⟩ ]
  ```

  The SSA semantics binds `0 ↦ 7` (the second `const` overwrites) and takes
  the *true* edge, so `Run P yst yst .halt`. `emitProg` accepts and emits
  `label 0; push 0; push 7; pop; jumpi 1; jump 2; label 1; op stop; jump 3;
  label 2; label 3` — the surplus-top `POP` from the shuffler discards the
  `7`, `jumpi` then sees `0` and falls through to block 2, which returns
  normally. `Asm.wfCheck` on that output is `true`, so `finishProg` accepts
  it; only `P.wfCheck` (which is `false` here — `allDefs = [0, 0]`) rules it
  out. `ofBlock_wfCheck` supplies it for the unoptimized candidate, and
  `optimizeProg` re-checks `Prog.wfCheck` on its own output
  (`SsaCfg/Passes.lean`), so `P.wfCheck → (optimizeProg P).wfCheck` is a
  one-line lemma the integration can add. -/
theorem emitProg_asteps' {P : Prog} {asm : List Asm} {yst0 yst' : EvmState}
    (hnodup : (labelDefs asm).Nodup) (hwf : P.wfCheck = true)
    (hemit : ToAsm.emitProg P = some asm)
    (hrun : Run (model := model) P yst0 yst' .normal) :
    ASteps (model := model) asm ⟨asm, [], yst0⟩ ⟨[], [], yst'⟩ := by
  obtain ⟨asm₀, rfl, hpl⟩ := emitProg_placement hwf hemit
  have hnodup₀ : (labelDefs asm₀).Nodup := by
    rwa [ToAsm.labelDefs_elideJumps] at hnodup
  cases hrun with
  | normal heb hexec =>
    obtain ⟨a, hsteps, hsim⟩ := raw_entry_sim hnodup₀ hwf hpl heb hexec
    obtain ⟨cret, hcret, hsteps2⟩ := hsim
    obtain rfl : cret = [] := Option.some.inj (hcret.symm.trans hpl.2.2.1)
    have hraw : ASteps (model := model) asm₀ ⟨asm₀, [], yst0⟩ ⟨[], [], yst'⟩ := by
      refine hsteps.trans ?_
      simpa using hsteps2
    have := asteps_elideJumps hnodup₀ hraw (List.suffix_refl _)
    simpa [elideConf, ToAsm.elideJumps] using this

theorem emitProg_ahalt' {P : Prog} {asm : List Asm} {yst0 yst' : EvmState}
    (hnodup : (labelDefs asm).Nodup) (hwf : P.wfCheck = true)
    (hemit : ToAsm.emitProg P = some asm)
    (hrun : Run (model := model) P yst0 yst' .halt) :
    ∃ conf, ASteps (model := model) asm ⟨asm, [], yst0⟩ conf ∧
      AHalt (model := model) asm conf yst' := by
  obtain ⟨asm₀, rfl, hpl⟩ := emitProg_placement hwf hemit
  have hnodup₀ : (labelDefs asm₀).Nodup := by
    rwa [ToAsm.labelDefs_elideJumps] at hnodup
  cases hrun with
  | halt heb hexec =>
    obtain ⟨a, hsteps, hsim⟩ := raw_entry_sim hnodup₀ hwf hpl heb hexec
    obtain ⟨conf, hsteps2, hhalt⟩ := hsim
    refine ⟨elideConf conf, ?_, ahalt_elideJumps hhalt⟩
    have := asteps_elideJumps hnodup₀ (hsteps.trans hsteps2) (List.suffix_refl _)
    simpa [elideConf] using this

end YulEvmCompiler.SsaCfg
