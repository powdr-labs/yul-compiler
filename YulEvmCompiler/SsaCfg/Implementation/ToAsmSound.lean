-- Not imported from the root yet: the emission-shape layer is mid-realignment
-- against the `EmitSt` emitter (layout inheritance + commutative operand
-- ordering). The emission-independent machinery below is fully proved.
import YulEvmCompiler.AsmSem
import YulEvmCompiler.SsaCfg.Spec.Sem
import YulEvmCompiler.SsaCfg.Implementation.ToAsm
/-!
# YulEvmCompiler.SsaCfg.Implementation.ToAsmSound

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
`ahalt_elideJumps`), stack extension (`AStep.extend`/`ASteps.extend`/
`AHalt.extend`), the register-file bookkeeping, `emitInstr_const_sim`,
`emitInstr_op_sim`, `emitTerm_halt_sim`, the emission-monad inversions, the
`foldlM`↔`emitRest` bridge (`emitBlock_emitRest`) and fragment placement
(`emitProg_placement`). `emitProg_asteps'` and `emitProg_ahalt'` are
*derived*.

**Status.** Everything in this file is proved except the six open cases of
`exec_sim`. In particular the entire emission-shape layer is closed:
`emitInstr_const_shape`/`emitInstr_op_shape` (including the commutative
operand-order choice, via `foldl_best` and `builtin_comm`), `emitBlock_head`,
`emitBlock_emitRest`, `emitFunc_inv`, `emitProg_inv`, `emitProg_placement` and
`raw_entry_sim`.

`exec_sim`: `const`, `op`, `opHalt`, `halt` and `ret` are proved — every case
that does not cross a control-flow edge. `ret` uses the epilogue-rotation
lemma `rot_steps`/`rots_steps` (`SWAP1 … SWAPk` lifts the return address from
under the `k` results to the top) and, in `main`, the internal side condition
`fidx = none → retLab = endLabel`, which `raw_entry_sim` discharges by `rfl`.

Still open: `jump`, `branchTrue`, `branchFalse` and the `call` pair. The
edge cases need one invariant this file does not yet carry: with entry-layout
inheritance, `edgeTargetLayout` reads/records the emission state's layout
table while `emitBlock` pins its own `sym0` from the same table, so
`Placement` must additionally record that *the layout an incoming edge
shuffles onto is the target block's pinned layout with its parameters
substituted by the edge arguments*. Everything downstream of that
(re-establishing freshness at the target entry from the liveness fixed point
and `domCheck_entry`, and the `AStep.jump`/`jumpi` resolution) is already in
place.

`exec_sim` carries two side conditions beyond the emission itself — that no
value on the symbolic stack is defined again by the rest of the block, and
that the rest of the block's definitions are distinct. Both are single
assignment (`Prog.wfCheck`), re-established at a block entry from the liveness
fixed-point equation (`liveIn` subtracts `blockDefs`);
`instrDefs_nodup` discharges them for `main`'s entry block.

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

/-! ## Stack extension

Every `Asm` step only touches the top of the stack, so a trace over a frame's
own stack lifts verbatim to that stack sitting on top of a caller's. This is
what lets the frame-local `SimStk`/`SimInstr` lemmas be used inside a callee. -/

theorem AStep.extend {prog : List Asm} {a b : AConf} (below : List AVal)
    (h : AStep (model := model) prog a b) :
    AStep (model := model) prog ⟨a.code, a.stk ++ below, a.yst⟩
      ⟨b.code, b.stk ++ below, b.yst⟩ := by
  cases h with
  | push => simpa using AStep.push
  | op hb => simpa [List.append_assoc] using AStep.op hb
  | @dup n v τ ρ c yst hlen =>
    have := AStep.dup (model := model) (prog := prog) (n := n) (v := v) (τ := τ)
      (ρ := ρ ++ below) (c := c) (yst := yst) hlen
    simpa [List.append_assoc] using this
  | @swap n x y τ ρ c yst hlen =>
    have := AStep.swap (model := model) (prog := prog) (n := n) (a := x) (b := y)
      (τ := τ) (ρ := ρ ++ below) (c := c) (yst := yst) hlen
    simpa [List.append_assoc] using this
  | pop => simpa using AStep.pop
  | label => simpa using AStep.label
  | jump hf => simpa using AStep.jump hf
  | jumpiTaken hv hf => simpa using AStep.jumpiTaken hv hf
  | jumpiFall hv => simpa using AStep.jumpiFall hv
  | pushLabel hm => simpa using AStep.pushLabel hm
  | dynJump hf => simpa using AStep.dynJump hf

theorem ASteps.extend {prog : List Asm} {a b : AConf} (below : List AVal)
    (h : ASteps (model := model) prog a b) :
    ASteps (model := model) prog ⟨a.code, a.stk ++ below, a.yst⟩
      ⟨b.code, b.stk ++ below, b.yst⟩ := by
  induction h with
  | refl => exact ASteps.refl _
  | head hstep _ ih => exact ASteps.head (AStep.extend below hstep) ih

theorem AHalt.extend {prog : List Asm} {a : AConf} {yst' : EvmState}
    (below : List AVal) (h : AHalt (model := model) prog a yst') :
    AHalt (model := model) prog ⟨a.code, a.stk ++ below, a.yst⟩ yst' := by
  cases h with
  | op hb => simpa [List.append_assoc] using AHalt.op hb

/-- The epilogue rotation `SWAP(m+1) … SWAP(m+r+1)`. -/
def rotOps (m r : Nat) : List Asm :=
  (List.range' m (r + 1)).filterMap fun j =>
    if h : j < 16 then some (Asm.swap ⟨j, h⟩) else none

theorem rotOps_succ (m r : Nat) (hm : m < 16) :
    rotOps m (r + 1) = Asm.swap ⟨m, hm⟩ :: rotOps (m + 1) r := by
  show (List.range' m (r + 2)).filterMap _ = _
  rw [show List.range' m (r + 2) = m :: List.range' (m + 1) (r + 1) from rfl,
    List.filterMap_cons]
  simp [rotOps, hm]

theorem rotOps_zero (m : Nat) (hm : m < 16) :
    rotOps m 0 = [Asm.swap ⟨m, hm⟩] := by
  show (List.range' m 1).filterMap _ = _
  rw [show List.range' m 1 = [m] from rfl]
  simp [hm]

/-- **The epilogue rotation**: `SWAP1 … SWAPk` lifts the return address from
under `k` result words to the top, leaving the results in order. -/
theorem rot_steps {prog c : List Asm} {yst : EvmState} :
    ∀ (back front : List AVal) (x ra : AVal) (below : List AVal),
      front.length + back.length + 1 ≤ 16 →
      ASteps (model := model) prog
        ⟨rotOps front.length back.length ++ c, x :: (front ++ back ++ ra :: below), yst⟩
        ⟨c, ra :: (front ++ x :: back ++ below), yst⟩ := by
  intro back
  induction back with
  | nil =>
    intro front x ra below hlen
    have hm : front.length < 16 := by simp at hlen; omega
    simp only [List.length_nil, List.append_nil]
    rw [rotOps_zero front.length hm, List.singleton_append]
    refine ASteps.single ?_
    have := AStep.swap (model := model) (prog := prog) (n := ⟨front.length, hm⟩)
      (a := x) (b := ra) (τ := front) (ρ := below) (c := c) (yst := yst) rfl
    simpa using this
  | cons y back ih =>
    intro front x ra below hlen
    have hm : front.length < 16 := by simp at hlen; omega
    simp only [List.length_cons, List.append_assoc, List.cons_append]
    rw [rotOps_succ front.length back.length hm, List.cons_append]
    refine ASteps.head (b := ⟨rotOps (front.length + 1) back.length ++ c,
        y :: (front ++ x :: (back ++ ra :: below)), yst⟩) ?_ ?_
    · exact AStep.swap (model := model) (prog := prog) (n := ⟨front.length, hm⟩)
        (a := x) (b := y) (τ := front) (ρ := back ++ ra :: below)
        (c := rotOps (front.length + 1) back.length ++ c) (yst := yst) rfl
    · have hnext := ih (front ++ [x]) y ra below (by simp at hlen ⊢; omega)
      rw [List.length_append] at hnext
      simpa [List.append_assoc] using hnext



theorem rots_steps {prog c : List Asm} {yst : EvmState} {vs : List AVal} {ra : AVal}
    {below : List AVal} (hk : vs.length ≤ 16) :
    ASteps (model := model) prog
      ⟨((List.range vs.length).filterMap
          (fun j => if h : j < 16 then some (Asm.swap ⟨j, h⟩) else none)) ++ c,
        vs ++ ra :: below, yst⟩
      ⟨c, ra :: (vs ++ below), yst⟩ := by
  cases vs with
  | nil => simpa using ASteps.refl (model := model) (prog := prog) ⟨c, ra :: below, yst⟩
  | cons v vs =>
    have hh := rot_steps (model := model) (prog := prog) (c := c) (yst := yst) vs [] v ra below
      (by simp at hk ⊢; omega)
    rw [List.range_eq_range']
    simpa [rotOps] using hh


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
theorem liftE_bind_inv {α β : Type} {o : Option α} {f : α → ToAsm.E β}
    {n : ToAsm.EmitSt} {r : β} {n' : ToAsm.EmitSt}
    (h : (ToAsm.liftE o >>= f) n = some (r, n')) :
    ∃ a, o = some a ∧ f a n = some (r, n') := by
  cases o with
  | none => simp [ToAsm.liftE, StateT.bind, bind] at h
  | some a =>
    exact ⟨a, rfl, by simpa [ToAsm.liftE, StateT.bind, bind, pure, StateT.pure] using h⟩

omit model in
/-- Inverting a `bind` in the emission monad. -/
theorem E_bind_inv {σ α β : Type} {x : StateT σ Option α} {g : α → StateT σ Option β}
    {n : σ} {r : β} {n' : σ} (h : (x >>= g) n = some (r, n')) :
    ∃ a m, x n = some (a, m) ∧ g a m = some (r, n') := by
  have hb : (x n).bind (fun p => g p.1 p.2) = some (r, n') := h
  obtain ⟨p, hp, hg⟩ := Option.bind_eq_some_iff.mp hb
  exact ⟨p.1, p.2, hp, hg⟩

omit model in
/-- Composing a `bind` in the emission monad. -/
theorem E_bind_eq {σ α β : Type} {x : StateT σ Option α} {g : α → StateT σ Option β}
    {n : σ} {a : α} {m : σ} (hx : x n = some (a, m)) {r : β} {n' : σ}
    (hg : g a m = some (r, n')) : (x >>= g) n = some (r, n') := by
  show (x n).bind (fun p => g p.1 p.2) = some (r, n')
  rw [hx]; exact hg

omit model in
/-- Inverting a `pure` in the emission monad, value *and* counter. -/
theorem E_pure_inv2 {σ α : Type} {X r : α} {n n' : σ}
    (h : (pure X : StateT σ Option α) n = some (r, n')) : X = r ∧ n = n' := by
  have h' : some ((X, n) : α × σ) = some (r, n') := h
  exact (Prod.mk.injEq ..).mp (Option.some.inj h')

/-- `const`: a single `PUSH`. -/
theorem emitInstr_const_sim {P : Prog} {L : ToAsm.LabelMap} {ord : Bool}
    {sym : List SSlot} {needed future : List ValId} {d : ValId} {v : U256}
    {n n' : ToAsm.EmitSt}
    {asmf : List Asm} {sym' : List SSlot} {R : Regs} {retLab : Label}
    {st : EvmState}
    (hemit : ToAsm.emitInstr P L ord sym needed future (.const d v) n
      = some ((asmf, sym'), n'))
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
theorem shuffle_op_sim {sym keep : List SSlot} {args ds : List ValId} {yop : Op}
    {ops : List Asm} {R : Regs} {retLab : Label} {vals rets : List U256}
    {st st' : EvmState}
    (hsh : ToAsm.shuffle sym (args.map SSlot.val ++ keep) = some ops)
    (hget : R.getMany args = some vals)
    (hb : builtinWithExternal model.calls model.creates yop vals st (.ok rets st'))
    (hlen : ds.length = rets.length) (hnd : ds.Nodup)
    (hfresh : AgreeOn R (R.setMany ds rets) keep) :
    SimInstr (model := model) R (R.setMany ds rets) retLab (ops ++ [Asm.op yop])
      sym (ds.map SSlot.val ++ keep) st st' := by
  intro σr hm
  obtain ⟨τr, hτr, hsteps⟩ :=
    shuffle_sound (model := model) (R := R) (retLab := retLab) hsh σr hm
  obtain ⟨σa, σk, rfl, hσa, hσk⟩ := StkMatch.append_inv hτr
  obtain rfl : σa = words vals := hσa.det (StkMatch.of_vals hget)
  refine ⟨words rets ++ σk,
    (StkMatch.of_vals (Regs.getMany_setMany hnd hlen)).append (hσk.mono hfresh), ?_⟩
  intro prog c
  rw [List.append_assoc]
  refine (hsteps prog ([Asm.op yop] ++ c) st).trans (ASteps.single ?_)
  rw [List.singleton_append]
  exact AStep.op hb

/-- The five (six, counting `eq`) built-ins whose operand order the generator
is allowed to swap. -/
def CommOp (yop : Op) : Prop :=
  yop = .add ∨ yop = .mul ∨ yop = .and ∨ yop = .or ∨ yop = .xor ∨ yop = .eq

/-- The operand list the generator actually shuffled to the top: either the
source order, or — for a commutative built-in — the two operands swapped. -/
def ArgsOK (yop : Op) (as args : List ValId) : Prop :=
  args = as ∨ (CommOp yop ∧ ∃ a b, as = [a, b] ∧ args = [b, a])

omit model in
theorem bin_comm {f : U256 → U256 → U256} (hf : ∀ x y, f x y = f y x)
    (a b : U256) (st : EvmState) :
    YulSemantics.EVM.bin f [b, a] st = YulSemantics.EVM.bin f [a, b] st := by
  simp [YulSemantics.EVM.bin, hf a b]

/-- **The dialect fact that licenses the reordering**: the six built-ins
`emitInstr` is allowed to feed in either operand order really are commutative
in the combined local/external relation (they are pure `stepOp` binaries, and
`BitVec` `+`/`*`/`&&&`/`|||`/`^^^` commute, `eq` is symmetric). -/
theorem builtin_comm {yop : Op} (hc : CommOp yop) {a b : U256} {st : EvmState}
    {res : YulSemantics.BuiltinResult U256 YulSemantics.EVM.EvmState}
    (h : builtinWithExternal model.calls model.creates yop [a, b] st res) :
    builtinWithExternal model.calls model.creates yop [b, a] st res := by
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [builtinWithExternal, YulSemantics.EVM.stepOp] at h ⊢
  · rw [bin_comm (fun x y => BitVec.add_comm x y)]; exact h
  · rw [bin_comm (fun x y => BitVec.mul_comm x y)]; exact h
  · rw [bin_comm (fun x y => BitVec.and_comm x y)]; exact h
  · rw [bin_comm (fun x y => BitVec.or_comm x y)]; exact h
  · rw [bin_comm (fun x y => BitVec.xor_comm x y)]; exact h
  · rw [bin_comm (fun x y => by congr 1; exact decide_eq_decide.mpr eq_comm)]; exact h

omit model in
/-- Inverting `emitInstr`'s final `match best with | some p => pure … | none =>
liftE none`. -/
theorem E_match_inv {α₁ α₂ β : Type} {X : Option (α₁ × α₂)} {f : α₁ → α₂ → β}
    {n n' : ToAsm.EmitSt} {r : β}
    (h : (match X with
          | some (a, b) => (pure (f a b) : ToAsm.E β)
          | none => ToAsm.liftE none) n = some (r, n')) :
    ∃ a b, X = some (a, b) ∧ f a b = r ∧ n = n' := by
  cases X with
  | none => exact absurd h (by simp [ToAsm.liftE])
  | some p =>
    obtain ⟨a, b⟩ := p
    obtain ⟨h1, h2⟩ := E_pure_inv2 h
    exact ⟨a, b, rfl, h1, h2⟩

omit model in
/-- The accumulator of `emitInstr`'s cheapest-order fold always records a
successful shuffle for one of the candidate orders. -/
theorem foldl_best {sym keep : List SSlot} {Q : List Asm × List ValId → Prop} :
    ∀ (l : List (List ValId)) (acc : Option (List Asm × List ValId)),
      (∀ args ∈ l, ∀ ops,
        ToAsm.shuffle sym (args.map SSlot.val ++ keep) = some ops → Q (ops, args)) →
      (∀ p, acc = some p → Q p) →
      ∀ r, (l.foldl (init := acc) fun acc args =>
              match ToAsm.shuffle sym (args.map SSlot.val ++ keep) with
              | some ops =>
                match acc with
                | some (prev, _) =>
                  if ops.length < (prev : List Asm).length then some (ops, args) else acc
                | none => some (ops, args)
              | none => acc) = some r → Q r := by
  intro l
  induction l with
  | nil => intro acc _ hacc r hr; exact hacc r hr
  | cons a l ih =>
    intro acc hl hacc r hr
    rw [List.foldl_cons] at hr
    refine ih _ (fun args ha => hl args (List.mem_cons_of_mem _ ha)) ?_ r hr
    intro p hp
    rcases hsh : ToAsm.shuffle sym (a.map SSlot.val ++ keep) with _ | ops
    · rw [hsh] at hp; exact hacc p hp
    · rw [hsh] at hp
      rcases acc with _ | ⟨prev, prevArgs⟩
      · obtain rfl := Option.some.inj hp
        exact hl a List.mem_cons_self ops hsh
      · dsimp only at hp
        split at hp
        · obtain rfl := Option.some.inj hp
          exact hl a List.mem_cons_self ops hsh
        · exact hacc p hp

omit model in
/-- **The shape `emitInstr` gives a built-in application**: the checked shuffle
onto *one of the candidate operand orders*, then the op. -/
theorem emitInstr_op_shape {P : Prog} {L : ToAsm.LabelMap} {ord : Bool}
    {sym : List SSlot} {needed future : List ValId} {ds : List ValId} {yop : Op}
    {as : List ValId} {n n' : ToAsm.EmitSt} {asmf : List Asm} {sym' : List SSlot}
    (hemit : ToAsm.emitInstr P L ord sym needed future (.op ds yop as) n
      = some ((asmf, sym'), n')) :
    ∃ (args : List ValId) (ops : List Asm) (keep : List SSlot),
      keep = (if ord then ToAsm.orderByFuture (ToAsm.keepOf sym needed) future
              else ToAsm.keepOf sym needed)
      ∧ ArgsOK yop as args
      ∧ ToAsm.shuffle sym (args.map SSlot.val ++ keep) = some ops
      ∧ asmf = ops ++ [Asm.op yop]
      ∧ sym' = ds.map SSlot.val ++ keep := by
  suffices h : ∀ i : Instr, i = Instr.op ds yop as →
      ToAsm.emitInstr P L ord sym needed future i n = some ((asmf, sym'), n') →
      ∃ (args : List ValId) (ops : List Asm) (keep : List SSlot),
        keep = (if ord then ToAsm.orderByFuture (ToAsm.keepOf sym needed) future
                else ToAsm.keepOf sym needed)
        ∧ ArgsOK yop as args
        ∧ ToAsm.shuffle sym (args.map SSlot.val ++ keep) = some ops
        ∧ asmf = ops ++ [Asm.op yop]
        ∧ sym' = ds.map SSlot.val ++ keep by
    exact h _ rfl hemit
  intro i hi hem
  fun_cases ToAsm.emitInstr P L ord sym needed future i
  case case2 keep argOrders best prev args hbest =>
    rename_i ds2 yop2 as2
    injection hi with h1 h2 h3
    subst h1; subst h2; subst h3
    have hem' : (match best with
        | some (ops, _) =>
          (pure (ops ++ [Asm.op yop2], List.map SSlot.val ds2 ++ keep) :
            ToAsm.E (List Asm × List SSlot))
        | none => ToAsm.liftE none) n = some ((asmf, sym'), n') := hem
    rw [hbest] at hem'
    obtain ⟨heq, -⟩ := E_pure_inv2 hem'
    obtain ⟨e1, e2⟩ := (Prod.mk.injEq ..).mp heq
    have hQ : ArgsOK yop2 as2 args ∧
        ToAsm.shuffle sym (args.map SSlot.val ++ keep) = some prev := by
      refine foldl_best
        (Q := fun p => ArgsOK yop2 as2 p.2 ∧
          ToAsm.shuffle sym (p.2.map SSlot.val ++ keep) = some p.1)
        argOrders none ?_ (by simp) (prev, args) hbest
      intro a ha opsx hsh
      refine ⟨?_, hsh⟩
      simp only [argOrders] at ha
      split at ha
      all_goals
        first
        | (rename_i x y
           split at ha
           · simp only [List.mem_singleton] at ha
             exact Or.inl (by rw [ha])
           · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
             rcases ha with rfl | rfl
             · exact Or.inl rfl
             · exact Or.inr ⟨by simp [CommOp], x, y, rfl, rfl⟩)
        | (simp only [List.mem_singleton] at ha; exact Or.inl ha)
    exact ⟨args, prev, keep, rfl, hQ.1, hQ.2, e1.symm, e2.symm⟩
  case case3 keep argOrders best hbest =>
    rename_i ds2 yop2 as2
    injection hi with h1 h2 h3
    subst h1; subst h2; subst h3
    have hem' : (match best with
        | some (ops, _) =>
          (pure (ops ++ [Asm.op yop2], List.map SSlot.val ds2 ++ keep) :
            ToAsm.E (List Asm × List SSlot))
        | none => ToAsm.liftE none) n = some ((asmf, sym'), n') := hem
    rw [hbest] at hem'
    exact absurd hem' (by simp [ToAsm.liftE])
  all_goals exact absurd hi (by simp)


/-! ## Halting terminators

`emitTerm` for `.halt yop as` shuffles the operands to the top and emits
`op yop`; whatever follows (the dead barrier that keeps the linear
stack-certificate walk honest) is never executed, so the trace simply stops
at the halting op. -/

omit model in
/-- Inverting a `pure` in the emission monad. -/
theorem E_pure_inv {α : Type} {X r : α} {n n' : ToAsm.EmitSt}
    (h : (pure X : ToAsm.E α) n = some (r, n')) : X = r := by
  have h' : some ((X, n) : α × ToAsm.EmitSt) = some (r, n') := h
  exact ((Prod.mk.injEq ..).mp (Option.some.inj h')).1

omit model in
/-- Both branches of the halting terminator emit
`shuffle … ++ op yop ++ dead barrier`. -/
theorem emitTerm_halt_shape {isFunc : Bool} {f : Func} {L : ToAsm.LabelMap}
    {fidx : Option Nat} {liveIn : Array (List ValId)} {sym : List SSlot}
    {yop : Op} {as : List ValId} {n n' : ToAsm.EmitSt} {asmf : List Asm}
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
    {yop : Op} {as : List ValId} {n n' : ToAsm.EmitSt} {asmf : List Asm}
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

/-! ## Single assignment, as the induction needs it

`emitInstr` extends the symbolic stack with an instruction's destinations
without checking that they are not already there, so the simulation needs
"every value still on the symbolic stack is distinct from every value the
remaining instructions define". That is single assignment (`P.wfCheck`),
packaged here as two side conditions on the rest-of-block being emitted. -/

/-- The values the remaining instructions of a block define. -/
def restDefs {β : Type} (paired : List (Instr × β)) : List ValId :=
  (paired.map Prod.fst).flatMap Instr.defs

omit model in
@[simp] theorem restDefs_nil {β : Type} : restDefs ([] : List (Instr × β)) = [] := rfl

omit model in
theorem restDefs_cons {β : Type} (i : Instr) (need : β)
    (paired : List (Instr × β)) :
    restDefs ((i, need) :: paired) = i.defs ++ restDefs paired := by
  simp [restDefs]

omit model in
theorem restDefs_eq {β : Type} {paired : List (Instr × β)} {is : List Instr}
    (h : paired.map Prod.fst = is) : restDefs paired = is.flatMap Instr.defs := by
  rw [restDefs, h]

omit model in
theorem agreeOn_set {R : Regs} {d : ValId} {v : U256} {sym : List SSlot}
    (h : ∀ x, SSlot.val x ∈ sym → x ≠ d) : AgreeOn R (R.set d v) sym :=
  fun x hx => Regs.set_other _ _ (h x hx)

omit model in
theorem agreeOn_setMany {R : Regs} {ds : List ValId} {rets : List U256}
    {sym : List SSlot} (h : ∀ x, SSlot.val x ∈ sym → x ∉ ds) :
    AgreeOn R (R.setMany ds rets) sym :=
  fun x hx => Regs.setMany_not_mem (h x hx)

omit model in
/-- The keep-list only ever retains slots that were already on the stack. -/
theorem keepOf_go_mem {needed : List ValId} {s : SSlot} :
    ∀ {σ seen : List SSlot}, s ∈ ToAsm.keepOf.go needed σ seen → s ∈ σ := by
  intro σ
  induction σ with
  | nil => intro seen h; simp [ToAsm.keepOf.go] at h
  | cons a rest ih =>
    intro seen h
    cases a with
    | val w =>
      rw [ToAsm.keepOf.go] at h
      split at h
      · rcases List.mem_cons.mp h with rfl | h' 
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih h')
      · exact List.mem_cons_of_mem _ (ih h)
    | code l => exact List.mem_cons_of_mem _ (ih (by rw [ToAsm.keepOf.go] at h; exact h))
    | retAddr =>
      rw [ToAsm.keepOf.go] at h
      split at h
      · exact List.mem_cons_of_mem _ (ih h)
      · rcases List.mem_cons.mp h with rfl | h'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih h')

omit model in
theorem keepOf_mem {σ : List SSlot} {needed : List ValId} {s : SSlot}
    (h : s ∈ ToAsm.keepOf σ needed) : s ∈ σ := keepOf_go_mem h

omit model in
theorem dedup_mem {s : SSlot} :
    ∀ {l seen : List SSlot}, s ∈ ToAsm.orderByFuture.dedup l seen → s ∈ l ∨ s ∈ seen := by
  intro l
  induction l with
  | nil =>
    intro seen h
    rw [ToAsm.orderByFuture.dedup] at h
    exact Or.inr (by simpa using h)
  | cons x rest ih =>
    intro seen h
    rw [ToAsm.orderByFuture.dedup] at h
    split at h
    · rcases ih h with h' | h'
      · exact Or.inl (List.mem_cons_of_mem _ h')
      · exact Or.inr h'
    · rcases ih h with h' | h'
      · exact Or.inl (List.mem_cons_of_mem _ h')
      · rcases List.mem_cons.mp h' with rfl | h''
        · exact Or.inl List.mem_cons_self
        · exact Or.inr h''

omit model in
/-- The next-use reordering is a permutation-with-filter of its input: it never
invents a slot. -/
theorem orderByFuture_mem {s : SSlot} {kept : List SSlot} {future : List ValId}
    (h : s ∈ ToAsm.orderByFuture kept future) : s ∈ kept := by
  rw [ToAsm.orderByFuture] at h
  simp only [List.mem_append] at h
  rcases h with (h | h) | h
  · rcases dedup_mem h with h' | h'
    · obtain ⟨v, -, hv⟩ := List.mem_filterMap.mp h'
      split at hv
      · rename_i hk
        obtain rfl := Option.some.inj hv
        simpa using hk
      · exact absurd hv (by simp)
    · simp at h'
  · exact (List.mem_filter.mp h).1
  · split at h
    · rename_i hk
      rw [List.mem_singleton] at h
      subst h
      simpa using hk
    · simp at h

omit model in
theorem keep_mem {ord : Bool} {sym : List SSlot} {needed future : List ValId}
    {s : SSlot}
    (h : s ∈ (if ord then ToAsm.orderByFuture (ToAsm.keepOf sym needed) future
              else ToAsm.keepOf sym needed)) : s ∈ sym := by
  split at h
  · exact keepOf_mem (orderByFuture_mem h)
  · exact keepOf_mem h

omit model in
/-- Reading a two-element operand list, and its swap. -/
theorem getMany_pair {R : Regs} {a b : ValId} {vs : List U256}
    (h : R.getMany [a, b] = some vs) :
    ∃ va vb, vs = [va, vb] ∧ R.getMany [b, a] = some [vb, va] := by
  rw [Regs.getMany_cons] at h
  rcases ha : R a with _ | va
  · rw [ha] at h; simp at h
  rw [ha, Regs.getMany_cons] at h
  rcases hb : R b with _ | vb
  · rw [hb] at h; simp at h
  rw [hb] at h
  simp only [Regs.getMany_nil, Option.bind_some, Option.map_some] at h
  obtain rfl := Option.some.inj h
  refine ⟨va, vb, rfl, ?_⟩
  rw [Regs.getMany_cons, hb, Regs.getMany_cons, ha]
  simp

omit model in
/-- One instruction's destinations, from `Prog.wfCheck`'s single-assignment
clause: a block's instruction defs are a sublist of the function's `allDefs`. -/
theorem sublist_flatMap_of_mem {α β : Type} {l : List α} {a : α} (g : α → List β)
    (ha : a ∈ l) : List.Sublist (g a) (l.flatMap g) := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with rfl | h
    · simp
    · have hh := (ih h).trans (List.sublist_append_right (g x) (xs.flatMap g))
      simpa using hh

omit model in
theorem instrDefs_nodup {f : Func} {k : Nat} (hwf : f.wfCheck k = true)
    {bid : BlockId} {b : Block} (hb : f.blocks[bid]? = some b) :
    (b.instrs.flatMap Instr.defs).Nodup := by
  have hnd : f.allDefs.Nodup := by
    simp only [Func.wfCheck, Bool.and_eq_true, decide_eq_true_eq] at hwf
    exact hwf.1.1.1
  have hmem : b ∈ f.blocks.toList := by
    have := Array.getElem?_toList (xs := f.blocks) (i := bid)
    exact List.mem_of_getElem? (this.trans hb)
  have hsub : List.Sublist (b.instrs.flatMap Instr.defs) f.allDefs := by
    refine List.Sublist.trans ?_ (List.sublist_append_right f.params _)
    refine List.Sublist.trans ?_
      (sublist_flatMap_of_mem (fun b => b.params ++ b.instrs.flatMap Instr.defs) hmem)
    exact List.sublist_append_right _ _
  exact hnd.sublist hsub

omit model in
theorem emitTerm_ret_shape {isFunc : Bool} {f : Func} {L : ToAsm.LabelMap}
    {fidx : Option Nat} {liveIn : Array (List ValId)} {sym : List SSlot}
    {xs : List ValId} {n n' : ToAsm.EmitSt} {asmf : List Asm}
    (hemit : ToAsm.emitTerm isFunc f L fidx liveIn sym (.ret xs) n = some (asmf, n')) :
    (isFunc = true ∧ xs.length ≤ 16 ∧ ∃ ops,
        ToAsm.shuffle sym (xs.map SSlot.val ++ [SSlot.retAddr]) = some ops ∧
        asmf = ops ++ ((List.range xs.length).filterMap
          (fun j => if h : j < 16 then some (Asm.swap ⟨j, h⟩) else none)) ++ [Asm.dynJump])
    ∨ (isFunc = false ∧ xs = [] ∧ ∃ ops, ToAsm.shuffle sym [] = some ops
        ∧ asmf = ops ++ [Asm.jump L.endLabel]) := by
  rw [ToAsm.emitTerm] at hemit
  split at hemit
  · rename_i hf
    obtain ⟨ops, hsh, heq⟩ := liftE_bind_inv hemit
    dsimp only at heq
    split at heq
    · rename_i hk
      exact Or.inl ⟨hf, hk, ops, hsh, (E_pure_inv2 heq).1.symm⟩
    · exact absurd heq (by simp [ToAsm.liftE])
  · rename_i hf
    split at hemit
    · exact absurd hemit (by simp [ToAsm.liftE])
    · rename_i hxs
      obtain ⟨ops, hsh, heq⟩ := liftE_bind_inv hemit
      exact Or.inr ⟨by simpa using hf, by simpa using hxs, ops, hsh,
        (E_pure_inv2 heq).1.symm⟩

/-! ## The rest of a block, as the big-step relation walks it

`emitBlock` folds `emitInstr` over the block's instructions (paired with their
needed-after sets) and finishes with `emitTerm`. The big-step `Exec` relation
consumes exactly a *suffix* of that, so the simulation induction is stated
over `emitRest`, which is the same fold written as a recursion. -/

def emitRest (P : Prog) (L : ToAsm.LabelMap) (ord : Bool) (isFunc : Bool)
    (f : Func) (fidx : Option Nat) (liveIn : Array (List ValId)) (t : Term) :
    List (Instr × List ValId × List ValId) → List SSlot → ToAsm.E (List Asm)
  | [], sym => ToAsm.emitTerm isFunc f L fidx liveIn sym t
  | (i, need, future) :: rest, sym => do
      let (asm, sym') ← ToAsm.emitInstr P L ord sym need future i
      let tl ← emitRest P L ord isFunc f fidx liveIn t rest sym'
      pure (asm ++ tl)

omit model in
@[simp] theorem emitRest_nil (P : Prog) (L : ToAsm.LabelMap) (ord isFunc : Bool)
    (f : Func) (fidx : Option Nat) (liveIn : Array (List ValId)) (t : Term)
    (sym : List SSlot) :
    emitRest P L ord isFunc f fidx liveIn t [] sym
      = ToAsm.emitTerm isFunc f L fidx liveIn sym t := rfl

omit model in
theorem emitRest_cons (P : Prog) (L : ToAsm.LabelMap) (ord isFunc : Bool) (f : Func)
    (fidx : Option Nat) (liveIn : Array (List ValId)) (t : Term)
    (i : Instr) (need future : List ValId)
    (rest : List (Instr × List ValId × List ValId)) (sym : List SSlot) :
    emitRest P L ord isFunc f fidx liveIn t ((i, need, future) :: rest) sym
      = (do
          let (asm, sym') ← ToAsm.emitInstr P L ord sym need future i
          let tl ← emitRest P L ord isFunc f fidx liveIn t rest sym'
          pure (asm ++ tl)) := rfl

omit model in
/-- `emitBlock`'s instruction `foldlM` *is* `emitRest`, modulo the accumulator
prefix: the fold's output is `acc0 ++ (the ops `emitRest` emits)`. -/
private theorem foldlM_emitRest (P : Prog) (L : ToAsm.LabelMap) (ord isFunc : Bool)
    (f : Func) (fidx : Option Nat) (liveIn : Array (List ValId)) (t : Term) :
    ∀ (paired : List (Instr × List ValId × List ValId)) (sym0 : List SSlot)
      (acc0 : List Asm) (n : ToAsm.EmitSt) (body : List Asm)
      (symEnd : List SSlot) (n₁ : ToAsm.EmitSt),
      (paired.foldlM (init := (acc0, sym0))
        (fun (acc, sym) (p : Instr × List ValId × List ValId) => do
          let (asm, sym') ← ToAsm.emitInstr P L ord sym p.2.1 p.2.2 p.1
          pure (acc ++ asm, sym'))) n = some ((body, symEnd), n₁) →
      ∀ (tasm : List Asm) (n' : ToAsm.EmitSt),
        ToAsm.emitTerm isFunc f L fidx liveIn symEnd t n₁ = some (tasm, n') →
        ∃ body', body = acc0 ++ body' ∧
          emitRest P L ord isFunc f fidx liveIn t paired sym0 n
            = some (body' ++ tasm, n') := by
  intro paired
  induction paired with
  | nil =>
    intro sym0 acc0 n body symEnd n₁ hfold tasm n' hterm
    rw [List.foldlM_nil] at hfold
    obtain ⟨heq, rfl⟩ := E_pure_inv2 hfold
    obtain ⟨rfl, rfl⟩ := (Prod.mk.injEq ..).mp heq
    exact ⟨[], by simp, by rw [emitRest_nil]; exact hterm⟩
  | cons q rest ih =>
    obtain ⟨i, need, future⟩ := q
    intro sym0 acc0 n body symEnd n₁ hfold tasm n' hterm
    rw [List.foldlM_cons] at hfold
    obtain ⟨⟨acc1, sym1⟩, m, hstep, hrest⟩ := E_bind_inv hfold
    obtain ⟨⟨asm, sym'⟩, m', hei, hpure⟩ := E_bind_inv hstep
    obtain ⟨heq2, rfl⟩ := E_pure_inv2 hpure
    obtain ⟨rfl, rfl⟩ := (Prod.mk.injEq ..).mp heq2
    obtain ⟨body', rfl, hemitrest⟩ :=
      ih sym' (acc0 ++ asm) m' body symEnd n₁ hrest tasm n' hterm
    refine ⟨asm ++ body', by simp, ?_⟩
    rw [emitRest_cons]
    refine E_bind_eq hei ?_
    dsimp only
    refine E_bind_eq hemitrest ?_
    show some (asm ++ (body' ++ tasm), n') = _
    simp

omit model in
theorem neededAfter_go_eq (base : List ValId) (instrs : List Instr) :
    ToAsm.neededAfter instrs base = (ToAsm.neededAfter.go base instrs).1 := rfl

omit model in
theorem futures_length (instrs : List Instr) (uses : List ValId) :
    instrs.length ≤ (instrs.foldr (init := ([([] : List ValId)], uses))
      fun i (acc : List (List ValId) × List ValId) =>
        (acc.2 :: acc.1, i.uses ++ acc.2)).1.length := by
  induction instrs with
  | nil => simp
  | cons i rest ih => simp only [List.foldr_cons, List.length_cons]; omega

omit model in
theorem neededAfter_length (instrs : List Instr) (base : List ValId) :
    (ToAsm.neededAfter instrs base).length = instrs.length := by
  rw [neededAfter_go_eq]
  induction instrs with
  | nil => rfl
  | cons i rest ih => simp [ToAsm.neededAfter.go]; simpa using ih

omit model in
/-- **Bridge from `emitBlock`'s fold to `emitRest`**: a successful block
emission is the block's label followed by `emitRest` over the whole instruction
list, starting from *whatever layout the block pinned* (`sym0`); for the entry
block that layout is the pure parameter frame. -/
theorem emitBlock_emitRest {P : Prog} {L : ToAsm.LabelMap} {ord : Bool}
    {fidx : Option Nat} {f : Func} {liveIn : Array (List ValId)} {bid : BlockId}
    {b : Block} {n n' : ToAsm.EmitSt} {frag : List Asm}
    (h : ToAsm.emitBlock P L ord fidx f liveIn bid b n
      = some (Asm.label (ToAsm.blkLabel L fidx bid) :: frag, n')) :
    ∃ (paired : List (Instr × List ValId × List ValId)) (sym0 : List SSlot)
      (m : ToAsm.EmitSt),
      paired.map Prod.fst = b.instrs
      ∧ (bid = f.entry → sym0 = f.params.map SSlot.val
            ++ (if fidx.isSome then [SSlot.retAddr] else []))
      ∧ emitRest P L ord fidx.isSome f fidx liveIn b.term paired sym0 m
        = some (frag, n') := by
  have tail : ∀ (sym0 : List SSlot) (s1 : ToAsm.EmitSt),
      (ToAsm.setLayout bid sym0 >>= fun _ =>
        ((b.instrs.zip ((ToAsm.neededAfter b.instrs
            (ToAsm.unionS (ToAsm.unionS b.term.uses [])
              (List.foldl (fun acc e => ToAsm.unionS (liveIn[e.target]?.getD []) acc)
                [] b.term.edges))).zip
          (if ord then
            (b.instrs.foldr (init := ([([] : List ValId)], b.term.uses))
              fun i (acc : List (List ValId) × List ValId) =>
                (acc.2 :: acc.1, i.uses ++ acc.2)).1
           else List.replicate b.instrs.length []))).foldlM
          (init := (([] : List Asm), sym0))
          (fun (acc, sym) (p : Instr × List ValId × List ValId) => do
            let (asm, sym') ← ToAsm.emitInstr P L ord sym p.2.1 p.2.2 p.1
            pure (acc ++ asm, sym')) >>= fun r =>
        ToAsm.emitTerm fidx.isSome f L fidx liveIn r.2 b.term >>= fun tasm =>
        pure (Asm.label (ToAsm.blkLabel L fidx bid) :: r.1 ++ tasm))) s1
        = some (Asm.label (ToAsm.blkLabel L fidx bid) :: frag, n') →
      ∃ (paired : List (Instr × List ValId × List ValId)) (m : ToAsm.EmitSt),
        paired.map Prod.fst = b.instrs ∧
        emitRest P L ord fidx.isSome f fidx liveIn b.term paired sym0 m
          = some (frag, n') := by
    intro sym0 s1 h1
    obtain ⟨-, s2, -, h2⟩ := E_bind_inv h1
    obtain ⟨⟨body, symEnd⟩, s3, hfold, h3⟩ := E_bind_inv h2
    obtain ⟨tasm, s4, hterm, h4⟩ := E_bind_inv h3
    obtain ⟨heq, rfl⟩ := E_pure_inv2 h4
    obtain ⟨body', hbody, hrest⟩ :=
      foldlM_emitRest P L ord fidx.isSome f fidx liveIn b.term _ _ [] s2 body symEnd s3
        hfold tasm s4 hterm
    rw [List.nil_append] at hbody
    subst hbody
    rw [List.cons_append] at heq
    obtain rfl := ((List.cons.injEq ..).mp heq).2
    refine ⟨_, s2, List.map_fst_zip ?_, hrest⟩
    rw [List.length_zip, neededAfter_length]
    split
    · have := futures_length b.instrs b.term.uses
      omega
    · simp
  simp only [ToAsm.emitBlock] at h
  split at h
  · rename_i hentry
    obtain ⟨sym0, s1, h0, h1⟩ := E_bind_inv h
    obtain ⟨hsym0, -⟩ := E_pure_inv2 h0
    obtain ⟨paired, m, hpair, hrest⟩ := tail sym0 s1 h1
    exact ⟨paired, sym0, m, hpair, fun _ => hsym0.symm, hrest⟩
  · rename_i hne
    obtain ⟨rec?, s0, -, h0⟩ := E_bind_inv h
    obtain ⟨sym0, s1, -, h1⟩ := E_bind_inv h0
    obtain ⟨paired, m, hpair, hrest⟩ := tail sym0 s1 h1
    exact ⟨paired, sym0, m, hpair, fun he => absurd he hne, hrest⟩

omit model in
theorem map_fst_eq_cons {β : Type} {paired : List (Instr × β)} {i : Instr}
    {is : List Instr} (h : paired.map Prod.fst = i :: is) :
    ∃ (need : β) (paired' : List (Instr × β)),
      paired = (i, need) :: paired' ∧ paired'.map Prod.fst = is := by
  cases paired with
  | nil => simp at h
  | cons q p' =>
    obtain ⟨i', need⟩ := q
    simp only [List.map_cons, List.cons.injEq] at h
    exact ⟨need, p', by rw [h.1], h.2⟩

omit model in
theorem map_fst_eq_nil {β : Type} {paired : List (Instr × β)}
    (h : paired.map Prod.fst = []) : paired = [] := by
  cases paired with
  | nil => rfl
  | cons q p' => simp at h

/-! ## Fragment placement

The classic Phase A (`SimAsm.lean`) locates each fragment inside the whole
program by list appends and resolves labels with `findLabel_boundary` from the
compile-time `Nodup` fact. The same holds here, one fragment per basic block;
`Placement` packages it. -/

/-- Block `bid` of function `fidx` has its emitted body sitting in `asm`
right after its label. -/
def BlockPlaced (P : Prog) (ord : Bool) (asm : List Asm) (fidx : Option Nat)
    (f : Func) (liveIn : Array (List ValId)) (bid : BlockId) (b : Block) : Prop :=
  ∃ (n n' : ToAsm.EmitSt) (frag tail : List Asm),
    ToAsm.emitBlock P (ToAsm.mkLabelMap P) ord fidx f liveIn bid b n
      = some (Asm.label (ToAsm.blkLabel (ToAsm.mkLabelMap P) fidx bid) :: frag, n')
    ∧ findLabel (ToAsm.blkLabel (ToAsm.mkLabelMap P) fidx bid) asm
      = some (frag ++ tail)

/-- Every block of every function is placed; the terminal label is last (so
`main`'s `ret []` runs off the end of the code with an empty stack); and
`main`'s entry label heads the program. -/
def Placement (P : Prog) (ord : Bool) (asm : List Asm) : Prop :=
  (∃ liveIn, ToAsm.liveInSets P.main = some liveIn ∧
      ∀ bid b, P.main.blocks[bid]? = some b →
        BlockPlaced P ord asm none P.main liveIn bid b)
  ∧ (∀ i g, P.funcs[i]? = some g → ∃ liveIn, ToAsm.liveInSets g = some liveIn ∧
      ∀ bid b, g.blocks[bid]? = some b → BlockPlaced P ord asm (some i) g liveIn bid b)
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

theorem SimFRes.prepend {asm : List Asm} {retLab : Label} {below : List AVal}
    {a a' : AConf} {res : FRes} (h : ASteps (model := model) asm a a')
    (hs : SimFRes (model := model) asm retLab below a' res) :
    SimFRes (model := model) asm retLab below a res := by
  cases res with
  | ret vals st' => obtain ⟨cret, hc, hst⟩ := hs; exact ⟨cret, hc, h.trans hst⟩
  | halt st' => obtain ⟨conf, hst, hh⟩ := hs; exact ⟨conf, h.trans hst, hh⟩

omit model in
theorem emitInstr_const_shape {P : Prog} {L : ToAsm.LabelMap} {ord : Bool}
    {sym : List SSlot} {needed future : List ValId} {d : ValId} {v : U256}
    {n n' : ToAsm.EmitSt} {asmf : List Asm} {sym' : List SSlot}
    (hei : ToAsm.emitInstr P L ord sym needed future (.const d v) n
      = some ((asmf, sym'), n')) :
    asmf = [Asm.push v] ∧ sym' = SSlot.val d :: sym ∧ n' = n := by
  obtain ⟨heq, rfl⟩ := E_pure_inv2
    (show (pure ([Asm.push v], SSlot.val d :: sym) : ToAsm.E (List Asm × List SSlot)) n
      = some ((asmf, sym'), n') from hei)
  obtain ⟨h1, h2⟩ := (Prod.mk.injEq ..).mp heq
  exact ⟨h1.symm, h2.symm, rfl⟩

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
theorem exec_sim {P : Prog} {ord : Bool} {asm : List Asm}
    (hnodup : (labelDefs asm).Nodup) (hwf : P.wfCheck = true)
    (hdom : ToAsm.Prog.domCheck P = true)
    (hplace : Placement P ord asm)
    {f : Func} {R : Regs} {st : EvmState} {rest : Rest} {res : FRes}
    (hexec : Exec (model := model) P f R st rest res) :
    ∀ (fidx : Option Nat) (liveIn : Array (List ValId))
      (paired : List (Instr × List ValId × List ValId)) (sym : List SSlot)
      (n n' : ToAsm.EmitSt) (frag tail : List Asm) (retLab : Label)
      (below σr : List AVal),
      paired.map Prod.fst = rest.instrs →
      emitRest P (ToAsm.mkLabelMap P) ord fidx.isSome f fidx liveIn rest.term
          paired sym n = some (frag, n') →
      (∀ v, SSlot.val v ∈ sym → v ∉ restDefs paired) →
      (restDefs paired).Nodup →
      StkMatch R retLab sym σr →
      (findLabel retLab asm).isSome →
      (fidx = none → retLab = (ToAsm.mkLabelMap P).endLabel) →
      SimFRes (model := model) asm retLab below
        ⟨frag ++ tail, σr ++ below, st⟩ res := by
  induction hexec
  case const f₀ R₀ st₀ d v is t res₀ hsub ih =>
    -- `AStep.push` (`emitInstr_const_sim`) then the IH on the shortened rest
    intro fidx liveIn paired sym n n' frag tail retLab below σr hpair hemit hfresh hndefs hm hret hmainRet
    obtain ⟨needF, paired', rfl, hpair'⟩ := map_fst_eq_cons hpair
    obtain ⟨need, future⟩ := needF
    dsimp only at hemit
    rw [emitRest_cons] at hemit
    obtain ⟨⟨asm1, sym1⟩, m, hei, h2⟩ := E_bind_inv hemit
    obtain ⟨tl, n'', htl, h3⟩ := E_bind_inv h2
    obtain ⟨heq, rfl⟩ := E_pure_inv2 h3
    obtain ⟨ha1, hs1, -⟩ := emitInstr_const_shape hei
    subst ha1; subst hs1
    rw [restDefs_cons] at hfresh hndefs
    have hdefs : (Instr.const d v).defs = [d] := rfl
    rw [hdefs] at hfresh hndefs
    have hne : ∀ x, SSlot.val x ∈ sym → x ≠ d := fun x hx hxd =>
      hfresh x hx (by simp [hxd])
    have hdnot : d ∉ restDefs paired' :=
      fun hc => (List.nodup_append.mp hndefs).2.2 d (by simp) d hc rfl
    obtain ⟨σr', hm', hsteps⟩ :=
      emitInstr_const_sim (st := st₀) hei (agreeOn_set hne) σr hm
    refine SimFRes.prepend ?_ (ih fidx liveIn paired' (SSlot.val d :: sym) _ _ tl tail
      retLab below σr' hpair' htl ?_ (List.nodup_append.mp hndefs).2.1 hm' hret hmainRet)
    · rw [← heq]
      have hst := ASteps.extend below (hsteps asm (tl ++ tail))
      simpa [List.append_assoc] using hst
    · intro x hx hc
      rcases List.mem_cons.mp hx with hxd | hxs
      · have : x = d := by injection hxd
        subst this; exact hdnot hc
      · exact hfresh x hxs (by simp [hc])
  case op f₀ R₀ st₀ st₁ ds yop as args rets is t res₀ hget hb hlen hsub ih =>
    -- `emitInstr_op_shape` + `shuffle_op_sim`; the chosen operand order is
    -- transported across `builtin_comm` for the commutative built-ins
    intro fidx liveIn paired sym n n' frag tail retLab below σr hpair hemit hfresh hndefs hm hret hmainRet
    obtain ⟨needF, paired', rfl, hpair'⟩ := map_fst_eq_cons hpair
    obtain ⟨need, future⟩ := needF
    dsimp only at hemit
    rw [emitRest_cons] at hemit
    obtain ⟨⟨asm1, sym1⟩, m, hei, h2⟩ := E_bind_inv hemit
    obtain ⟨tl, n'', htl, h3⟩ := E_bind_inv h2
    obtain ⟨heq, rfl⟩ := E_pure_inv2 h3
    obtain ⟨args', ops, keep, hkeep, hargs, hsh, ha1, hs1⟩ := emitInstr_op_shape hei
    subst ha1; subst hs1
    rw [restDefs_cons] at hfresh hndefs
    have hdefs : (Instr.op ds yop as).defs = ds := rfl
    rw [hdefs] at hfresh hndefs
    obtain ⟨hndds, hndrest, hdisj⟩ := List.nodup_append.mp hndefs
    obtain ⟨vals, hget', hb'⟩ : ∃ vals, R₀.getMany args' = some vals ∧
        builtinWithExternal model.calls model.creates yop vals st₀ (.ok rets st₁) := by
      rcases hargs with rfl | ⟨hc, a, b, rfl, rfl⟩
      · exact ⟨args, hget, hb⟩
      · obtain ⟨va, vb, rfl, hswap⟩ := getMany_pair hget
        exact ⟨[vb, va], hswap, builtin_comm hc hb⟩
    have hagree : AgreeOn R₀ (R₀.setMany ds rets) keep :=
      agreeOn_setMany (fun x hx hxd =>
        hfresh x (by rw [hkeep] at hx; exact keep_mem hx) (List.mem_append_left _ hxd))
    obtain ⟨σr', hm', hsteps⟩ :=
      shuffle_op_sim (st := st₀) (st' := st₁) hsh hget' hb' hlen hndds hagree σr hm
    refine SimFRes.prepend ?_ (ih fidx liveIn paired' _ _ _ tl tail
      retLab below σr' hpair' htl ?_ hndrest hm' hret hmainRet)
    · rw [← heq]
      have hst := ASteps.extend below (hsteps asm (tl ++ tail))
      simpa [List.append_assoc] using hst
    · intro x hx hc
      rcases List.mem_append.mp hx with hx1 | hx2
      · obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hx1
        have hyx : y = x := by injection hxy
        exact hdisj y hy x hc hyx
      · exact hfresh x (by rw [hkeep] at hx2; exact keep_mem hx2)
          (List.mem_append_right _ hc)
  case opHalt f₀ R₀ st₀ st₁ ds yop as args is t hget hb =>
    -- the shuffle, then `AHalt.op`; same operand-order transport as `op`
    intro fidx liveIn paired sym n n' frag tail retLab below σr hpair hemit hfresh hndefs hm hret hmainRet
    obtain ⟨needF, paired', rfl, hpair'⟩ := map_fst_eq_cons hpair
    obtain ⟨need, future⟩ := needF
    dsimp only at hemit
    rw [emitRest_cons] at hemit
    obtain ⟨⟨asm1, sym1⟩, m, hei, h2⟩ := E_bind_inv hemit
    obtain ⟨tl, n'', htl, h3⟩ := E_bind_inv h2
    obtain ⟨heq, -⟩ := E_pure_inv2 h3
    obtain ⟨args', ops, keep, hkeep, hargs, hsh, ha1, -⟩ := emitInstr_op_shape hei
    subst ha1
    obtain ⟨vals, hget', hb'⟩ : ∃ vals, R₀.getMany args' = some vals ∧
        builtinWithExternal model.calls model.creates yop vals st₀ (.halt st₁) := by
      rcases hargs with rfl | ⟨hc, a, b, rfl, rfl⟩
      · exact ⟨args, hget, hb⟩
      · obtain ⟨va, vb, rfl, hswap⟩ := getMany_pair hget
        exact ⟨[vb, va], hswap, builtin_comm hc hb⟩
    obtain ⟨τr, hτr, hsteps⟩ :=
      shuffle_sound (model := model) (R := R₀) (retLab := retLab) hsh σr hm
    obtain ⟨σa, σk, rfl, hσa, hσk⟩ := StkMatch.append_inv hτr
    obtain rfl : σa = words vals := hσa.det (StkMatch.of_vals hget')
    refine ⟨⟨Asm.op yop :: (tl ++ tail), words vals ++ (σk ++ below), st₀⟩, ?_,
      AHalt.op hb'⟩
    have hst := ASteps.extend below (hsteps asm (Asm.op yop :: (tl ++ tail)) st₀)
    rw [← heq]
    simpa [List.append_assoc] using hst
  case call =>
    -- pushLabel / arg DUPs / jump entry / callee IH / dynJump back
    intro fidx liveIn paired sym n n' frag tail retLab below σr hpair hemit hfresh hndefs hm hret hmainRet
    sorry
  case callHalt =>
    -- as `call`, but the callee's IH already produces the halting configuration
    intro fidx liveIn paired sym n n' frag tail retLab below σr hpair hemit hfresh hndefs hm hret hmainRet
    sorry
  case jump =>
    -- edge shuffle onto the target's entry layout, `AStep.jump`, target IH
    intro fidx liveIn paired sym n n' frag tail retLab below σr hpair hemit hfresh hndefs hm hret hmainRet
    sorry
  case branchTrue =>
    -- shuffle to `cond :: layout(true)`, `AStep.jumpiTaken`, target IH
    intro fidx liveIn paired sym n n' frag tail retLab below σr hpair hemit hfresh hndefs hm hret hmainRet
    sorry
  case branchFalse =>
    -- `AStep.jumpiFall`, the fall-through shuffle, target IH
    intro fidx liveIn paired sym n n' frag tail retLab below σr hpair hemit hfresh hndefs hm hret hmainRet
    sorry
  case ret f₀ R₀ st₀ xs vals hget =>
    -- function: epilogue rotation + `dynJump`; main: pops + `jump endLabel`
    intro fidx liveIn paired sym n n' frag tail retLab below σr hpair hemit hfresh hndefs hm hret hmainRet
    obtain rfl := map_fst_eq_nil hpair
    dsimp only at hemit
    rw [emitRest_nil] at hemit
    obtain ⟨cret, hcret⟩ : ∃ c, findLabel retLab asm = some c := Option.isSome_iff_exists.mp hret
    refine ⟨cret, hcret, ?_⟩
    rcases emitTerm_ret_shape hemit with ⟨-, hk, ops, hsh, rfl⟩ | ⟨hf, rfl, ops, hsh, rfl⟩
    · -- the function epilogue: shuffle, `SWAP1 … SWAPk`, `dynJump`
      obtain ⟨τr, hτr, hsteps⟩ :=
        shuffle_sound (model := model) (R := R₀) (retLab := retLab) hsh σr hm
      have hxv : StkMatch R₀ retLab (xs.map SSlot.val) (words vals) := StkMatch.of_vals hget
      obtain ⟨σa, σb, rfl, hσa, hσb⟩ := StkMatch.append_inv hτr
      obtain rfl : σa = words vals := hσa.det hxv
      obtain ⟨rb, σc, rfl, hrb, hσc⟩ := StkMatch.cons_inv hσb
      obtain rfl : rb = AVal.code retLab := by
        simpa [slotVal] using hrb.symm
      obtain rfl : σc = [] := by
        cases σc with
        | nil => rfl
        | cons _ _ => simp [StkMatch] at hσc
      have hvlen : (words vals).length ≤ 16 := by
        have hlen := hxv.length_eq
        simp only [List.length_map, words_length] at hlen
        simp only [words_length]
        omega
      refine ASteps.trans (b := ⟨((List.range xs.length).filterMap
          (fun j => if h : j < 16 then some (Asm.swap ⟨j, h⟩) else none))
            ++ Asm.dynJump :: tail,
          words vals ++ (AVal.code retLab :: below), st₀⟩) ?_
        (ASteps.trans (b := ⟨Asm.dynJump :: tail,
          AVal.code retLab :: (words vals ++ below), st₀⟩) ?_
          (ASteps.single (AStep.dynJump hcret)))
      · have hst := ASteps.extend below
          (hsteps asm (((List.range xs.length).filterMap
            (fun j => if h : j < 16 then some (Asm.swap ⟨j, h⟩) else none))
              ++ Asm.dynJump :: tail) st₀)
        simpa [List.append_assoc] using hst
      · have hrot := rots_steps (model := model) (prog := asm)
          (c := Asm.dynJump :: tail) (yst := st₀) (vs := words vals)
          (ra := AVal.code retLab) (below := below) hvlen
        have hxl : xs.length = (words vals).length := by
          have hlen := hxv.length_eq
          simpa using hlen
        rw [hxl]
        simpa using hrot
    · -- `main`: the shuffle empties the frame, then `jump` the terminal label
      obtain rfl : vals = [] := by simpa [Regs.getMany] using hget.symm
      have hfn : fidx = none := by
        cases fidx with
        | none => rfl
        | some i => simp at hf
      have hcret' : findLabel (ToAsm.mkLabelMap P).endLabel asm = some cret := by
        rw [← hmainRet hfn]; exact hcret
      obtain ⟨τr, hτr, hsteps⟩ :=
        shuffle_sound (model := model) (R := R₀) (retLab := retLab) hsh σr hm
      obtain rfl : τr = [] := by
        cases τr with
        | nil => rfl
        | cons _ _ => simp [StkMatch] at hτr
      refine ASteps.trans (b := ⟨Asm.jump (ToAsm.mkLabelMap P).endLabel :: tail, below, st₀⟩) ?_
        (ASteps.single (AStep.jump hcret'))
      have hst := ASteps.extend below
        (hsteps asm (Asm.jump (ToAsm.mkLabelMap P).endLabel :: tail) st₀)
      simpa using hst
  case halt =>
    -- `emitTerm_halt_sim`: the shuffle brings the operands up, then the emitted
    -- `op yop` halts; the dead barrier after it is never walked
    intro fidx liveIn paired sym n n' frag tail retLab below σr hpair hemit hfresh hndefs hm hret hmainRet
    rename_i hget hb
    obtain rfl := map_fst_eq_nil hpair
    dsimp only at hemit
    rw [emitRest_nil] at hemit
    obtain ⟨conf, hsteps, hhalt⟩ := emitTerm_halt_sim hemit hget hb hm asm tail
    exact ⟨⟨conf.code, conf.stk ++ below, conf.yst⟩,
      by simpa using ASteps.extend below hsteps, AHalt.extend below hhalt⟩

/-! ## Placement of `emitProg`'s output -/

/-! ### Inverting the emission, and locating the fragments -/

omit model in
theorem emitBlock_head {P : Prog} {L : ToAsm.LabelMap} {ord : Bool}
    {fidx : Option Nat} {f : Func} {liveIn : Array (List ValId)} {bid : BlockId}
    {b : Block} {n n' : ToAsm.EmitSt} {fr : List Asm}
    (h : ToAsm.emitBlock P L ord fidx f liveIn bid b n = some (fr, n')) :
    ∃ frag, fr = Asm.label (ToAsm.blkLabel L fidx bid) :: frag := by
  simp only [ToAsm.emitBlock] at h
  split at h
  · obtain ⟨sym0, s1, -, h1⟩ := E_bind_inv h
    obtain ⟨-, s2, -, h2⟩ := E_bind_inv h1
    obtain ⟨⟨body, symEnd⟩, s3, hfold, h3⟩ := E_bind_inv h2
    obtain ⟨tasm, s4, hterm, h4⟩ := E_bind_inv h3
    obtain ⟨heq, -⟩ := E_pure_inv2 h4
    exact ⟨body ++ tasm, by rw [← heq]; simp⟩
  · obtain ⟨rec?, s0, -, h0⟩ := E_bind_inv h
    obtain ⟨sym0, s1, -, h1⟩ := E_bind_inv h0
    obtain ⟨-, s2, -, h2⟩ := E_bind_inv h1
    obtain ⟨⟨body, symEnd⟩, s3, hfold, h3⟩ := E_bind_inv h2
    obtain ⟨tasm, s4, hterm, h4⟩ := E_bind_inv h3
    obtain ⟨heq, -⟩ := E_pure_inv2 h4
    exact ⟨body ++ tasm, by rw [← heq]; simp⟩

omit model in
theorem emitFunc_inv {P : Prog} {L : ToAsm.LabelMap} {ord : Bool}
    {fidx : Option Nat} {f : Func} {n : ToAsm.EmitSt} {code : List Asm}
    {n' : ToAsm.EmitSt}
    (h : ToAsm.emitFunc P L ord fidx f n = some (code, n')) :
    f.entry = 0 ∧ ∃ (n₀ : ToAsm.EmitSt) (liveIn : Array (List ValId)),
      ToAsm.liveInSets f = some liveIn ∧
      (((List.range f.blocks.size).zip f.blocks.toList).foldlM (init := ([] : List Asm))
        (fun acc (p : Nat × Block) => do
          let a ← ToAsm.emitBlock P L ord fidx f liveIn p.1 p.2
          pure (acc ++ a))) n₀ = some (code, n') := by
  rw [ToAsm.emitFunc] at h
  dsimp only at h
  split at h
  · exact absurd h (by simp [ToAsm.liftE])
  · rename_i hne
    obtain ⟨-, n₀, -, h1⟩ := E_bind_inv h
    obtain ⟨liveIn, hlive, h2⟩ := liftE_bind_inv h1
    split at h2
    · exact absurd h2 (by simp [ToAsm.liftE])
    · exact ⟨not_ne_iff.mp hne, n₀, liveIn, hlive, h2⟩

omit model in
theorem emitProg_inv {P : Prog} {ord : Bool} {asm : List Asm}
    (h : ToAsm.emitProgOrd ord P = some asm) :
    ∃ (asmMain asmFns : List Asm) (n₁ n₂ : ToAsm.EmitSt),
      ToAsm.emitFunc P (ToAsm.mkLabelMap P) ord none P.main
          ⟨(ToAsm.mkLabelMap P).endLabel + 1, {}⟩ = some (asmMain, n₁)
      ∧ (((List.range P.funcs.size).zip P.funcs.toList).foldlM (init := ([] : List Asm))
          (fun acc (p : Nat × Func) => do
            let a ← ToAsm.emitFunc P (ToAsm.mkLabelMap P) ord (some p.1) p.2
            pure (acc ++ a))) n₁ = some (asmFns, n₂)
      ∧ asm = ToAsm.elideJumps
          (asmMain ++ asmFns ++ [Asm.label (ToAsm.mkLabelMap P).endLabel]) := by
  rw [ToAsm.emitProgOrd] at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  · obtain ⟨⟨asm₀, k⟩, hbuild, hsome⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨asmMain, n₁, hmain, hb2⟩ := E_bind_inv hbuild
    obtain ⟨asmFns, n₂, hfns, hb3⟩ := E_bind_inv hb2
    obtain ⟨heq, -⟩ := E_pure_inv2 hb3
    exact ⟨asmMain, asmFns, n₁, n₂, hmain, hfns, by
      rw [← Option.some.inj hsome, heq]⟩

omit model in
theorem zip_range_mem {α : Type} {l : List α} {i k : Nat} {x : α}
    (hx : l[i]? = some x) (hk : i < k) : (i, x) ∈ (List.range k).zip l := by
  refine List.mem_of_getElem? (i := i) ?_
  rw [List.getElem?_zip_eq_some]
  exact ⟨by simpa using List.getElem?_range hk, hx⟩

omit model in
private theorem foldlM_grow {α : Type} (emit : α → ToAsm.E (List Asm)) :
    ∀ (l : List α) (acc0 : List Asm) (n : ToAsm.EmitSt) (code : List Asm) (n' : ToAsm.EmitSt),
      (l.foldlM (init := acc0) (fun acc a => do let x ← emit a; pure (acc ++ x))) n
        = some (code, n') → ∃ ops, code = acc0 ++ ops := by
  intro l
  induction l with
  | nil =>
    intro acc0 n code n' h
    rw [List.foldlM_nil] at h
    obtain ⟨rfl, -⟩ := E_pure_inv2 h
    exact ⟨[], by simp⟩
  | cons a rest ih =>
    intro acc0 n code n' h
    rw [List.foldlM_cons] at h
    obtain ⟨acc1, m, hstep, htail⟩ := E_bind_inv h
    obtain ⟨fr, m', he, hp⟩ := E_bind_inv hstep
    obtain ⟨rfl, rfl⟩ := E_pure_inv2 hp
    obtain ⟨ops, rfl⟩ := ih _ _ _ _ htail
    exact ⟨fr ++ ops, by simp⟩

omit model in
private theorem foldlM_split {α : Type} (emit : α → ToAsm.E (List Asm)) :
    ∀ (l : List α) (acc0 : List Asm) (n : ToAsm.EmitSt) (code : List Asm) (n' : ToAsm.EmitSt),
      (l.foldlM (init := acc0) (fun acc a => do let x ← emit a; pure (acc ++ x))) n
        = some (code, n') →
      ∀ a ∈ l, ∃ (m m' : ToAsm.EmitSt) (fr pre post : List Asm),
        emit a m = some (fr, m') ∧ code = pre ++ (fr ++ post) := by
  intro l
  induction l with
  | nil => intro acc0 n code n' h a ha; simp at ha
  | cons a0 rest ih =>
    intro acc0 n code n' h a ha
    rw [List.foldlM_cons] at h
    obtain ⟨acc1, m, hstep, htail⟩ := E_bind_inv h
    obtain ⟨fr0, m', he0, hp⟩ := E_bind_inv hstep
    obtain ⟨rfl, rfl⟩ := E_pure_inv2 hp
    rcases List.mem_cons.mp ha with rfl | ha'
    · obtain ⟨ops, rfl⟩ := foldlM_grow emit rest _ _ _ _ htail
      exact ⟨_, _, fr0, acc0, ops, he0, by simp⟩
    · exact ih _ _ _ _ htail a ha'


omit model in
private theorem foldlM_head {α : Type} (emit : α → ToAsm.E (List Asm))
    (a0 : α) (rest : List α) (n : ToAsm.EmitSt) (code : List Asm) (n' : ToAsm.EmitSt)
    (h : ((a0 :: rest).foldlM (init := ([] : List Asm))
      (fun acc a => do let x ← emit a; pure (acc ++ x))) n = some (code, n')) :
    ∃ (m' : ToAsm.EmitSt) (fr post : List Asm), emit a0 n = some (fr, m') ∧ code = fr ++ post := by
  rw [List.foldlM_cons] at h
  obtain ⟨acc1, m, hstep, htail⟩ := E_bind_inv h
  obtain ⟨fr, m', he, hp⟩ := E_bind_inv hstep
  obtain ⟨rfl, rfl⟩ := E_pure_inv2 hp
  obtain ⟨ops, hcode⟩ := foldlM_grow emit rest _ _ _ _ htail
  exact ⟨_, fr, ops, he, by rw [hcode]; simp⟩

omit model in
private theorem placed_of_split (pre : List Asm) {lbl : Label}
    {asm₀ frag post : List Asm} (hnd : (labelDefs asm₀).Nodup)
    (hsplit : asm₀ = pre ++ (Asm.label lbl :: frag) ++ post) :
    findLabel lbl asm₀ = some (frag ++ post) := by
  have h2 : asm₀ = pre ++ Asm.label lbl :: (frag ++ post) := by rw [hsplit]; simp
  rw [h2]; exact findLabel_boundary (by rw [← h2]; exact hnd)

omit model in
/-- **`emitProg` places its fragments**: the accepted program is the elision of
a raw emission in which every block's body sits right after its label, the
terminal label is last, and `main`'s entry label is first — the `SimAsm.lean`
Phase-A bookkeeping (fragment concatenation plus `findLabel_boundary` from
`Nodup`), specialized to one fragment per basic block. -/
theorem emitProg_placement {P : Prog} {ord : Bool} {asm : List Asm}
    (hnodup : (labelDefs asm).Nodup) (hwf : P.wfCheck = true)
    (hemit : ToAsm.emitProgOrd ord P = some asm) :
    ∃ asm₀ : List Asm, asm = ToAsm.elideJumps asm₀ ∧ Placement P ord asm₀ := by
  obtain ⟨asmMain, asmFns, n₁, n₂, hmain, hfns, rfl⟩ := emitProg_inv hemit
  have hnd0 : (labelDefs (asmMain ++ asmFns
      ++ [Asm.label (ToAsm.mkLabelMap P).endLabel])).Nodup := by
    rwa [ToAsm.labelDefs_elideJumps] at hnodup
  obtain ⟨hentry, n₀, liveIn, hlive, hfoldB⟩ := emitFunc_inv hmain
  have hmainwf : P.main.wfCheck P.funcs.size = true := by
    simp only [Prog.wfCheck, Bool.and_eq_true] at hwf
    exact hwf.1.2
  have hsize : 0 < P.main.blocks.size := by
    simp only [Func.wfCheck, Bool.and_eq_true, decide_eq_true_eq] at hmainwf
    have h1 : P.main.entry < P.main.blocks.size := hmainwf.1.1.2
    rw [hentry] at h1
    exact h1
  refine ⟨_, rfl, ⟨liveIn, hlive, ?_⟩, ?_, ?_, ?_⟩
  · intro bid b hb
    have htl : P.main.blocks.toList[bid]? = some b := Array.getElem?_toList.trans hb
    have hbid : bid < P.main.blocks.size := by
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp htl
      simpa using hlt
    obtain ⟨m, m', fr, pre, post, hblk, hcode⟩ :=
      foldlM_split _ _ _ _ _ _ hfoldB _ (zip_range_mem htl hbid)
    obtain ⟨frag, rfl⟩ := emitBlock_head hblk
    exact ⟨m, m', frag, post ++ asmFns ++ [Asm.label (ToAsm.mkLabelMap P).endLabel],
      hblk, placed_of_split pre hnd0 (by rw [hcode]; simp)⟩
  · intro i g hg
    have htlF : P.funcs.toList[i]? = some g := Array.getElem?_toList.trans hg
    have hi : i < P.funcs.size := by
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp htlF
      simpa using hlt
    obtain ⟨mf, mf', frg, preF, postF, hfn, hcodeF⟩ :=
      foldlM_split _ _ _ _ _ _ hfns _ (zip_range_mem htlF hi)
    obtain ⟨hentryg, n₀g, liveIng, hliveg, hfoldBg⟩ := emitFunc_inv hfn
    refine ⟨liveIng, hliveg, ?_⟩
    intro bid b hb
    have htl : g.blocks.toList[bid]? = some b := Array.getElem?_toList.trans hb
    have hbid : bid < g.blocks.size := by
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp htl
      simpa using hlt
    obtain ⟨m, m', fr, pre, post, hblk, hcode⟩ :=
      foldlM_split _ _ _ _ _ _ hfoldBg _ (zip_range_mem htl hbid)
    obtain ⟨frag, rfl⟩ := emitBlock_head hblk
    exact ⟨m, m', frag, post ++ postF ++ [Asm.label (ToAsm.mkLabelMap P).endLabel],
      hblk, placed_of_split (asmMain ++ preF ++ pre) hnd0 (by rw [hcodeF, hcode]; simp)⟩
  · exact placed_of_split (asmMain ++ asmFns) (frag := []) (post := []) hnd0 (by simp)
  · obtain ⟨s, hs⟩ : ∃ s, P.main.blocks.size = s + 1 := ⟨P.main.blocks.size - 1, by omega⟩
    obtain ⟨b₀, restB, htlm⟩ := List.exists_cons_of_ne_nil
      (l := P.main.blocks.toList) (by
        have hlen : P.main.blocks.toList.length = P.main.blocks.size := by simp
        intro hnil; rw [hnil] at hlen; simp at hlen; omega)
    rw [hs, List.range_succ_eq_map, htlm, List.zip_cons_cons] at hfoldB
    obtain ⟨m', fr, post, hblk0, hcode0⟩ := foldlM_head _ _ _ _ _ _ hfoldB
    obtain ⟨frag0, rfl⟩ := emitBlock_head hblk0
    exact ⟨frag0 ++ post ++ asmFns ++ [Asm.label (ToAsm.mkLabelMap P).endLabel],
      by rw [hcode0, hentry]; simp⟩

/-- Entering `main`'s entry block: one `AStep.label` off the head of the
program lands in the entry fragment with an empty stack, which matches the
entry layout (`main` has no parameters), so the frame-level simulation applies
with the terminal label as the frame's "return" label. -/
private theorem raw_entry_sim {P : Prog} {ord : Bool} {asm₀ : List Asm}
    (hnodup₀ : (labelDefs asm₀).Nodup) (hwf : P.wfCheck = true)
    (hdom : ToAsm.Prog.domCheck P = true)
    (hpl : Placement P ord asm₀) {yst0 : EvmState} {res : FRes} {eb : Block}
    (heb : P.main.blocks[P.main.entry]? = some eb)
    (hexec : Exec (model := model) P P.main Regs.empty yst0
      ⟨eb.instrs, eb.term⟩ res) :
    ∃ a : AConf, ASteps (model := model) asm₀ ⟨asm₀, [], yst0⟩ a ∧
      SimFRes (model := model) asm₀ (ToAsm.mkLabelMap P).endLabel [] a res := by
  have hpl' := hpl
  obtain ⟨⟨liveIn, -, hblocks⟩, -, hend, c, hhead⟩ := hpl'
  obtain ⟨n, n', frag, tail, hblk, hfind⟩ := hblocks _ _ heb
  have hc : c = frag ++ tail := by
    rw [hhead, findLabel, if_pos rfl] at hfind
    exact Option.some.inj hfind
  have hasm : asm₀ = Asm.label (ToAsm.blkLabel (ToAsm.mkLabelMap P) none P.main.entry)
      :: (frag ++ tail) := by rw [hhead, hc]
  obtain ⟨paired, sym0, m, hpair, hsym0, hrest⟩ := emitBlock_emitRest hblk
  have hp : P.main.params = [] := by
    have hwf' := hwf
    rw [Prog.wfCheck] at hwf'
    simp only [Bool.and_eq_true] at hwf'
    simpa using hwf'.1.1.1
  have hsym : sym0 = [] := by rw [hsym0 rfl]; simp [hp]
  have hmainwf : P.main.wfCheck P.funcs.size = true := by
    have hwf2 := hwf
    simp only [Prog.wfCheck, Bool.and_eq_true] at hwf2
    exact hwf2.1.2
  refine ⟨⟨frag ++ tail, [] ++ [], yst0⟩, ?_, ?_⟩
  · refine ASteps.single ?_
    rw [hasm]; exact AStep.label
  · refine exec_sim hnodup₀ hwf hdom hpl hexec none liveIn paired sym0 m n' frag tail
      (ToAsm.mkLabelMap P).endLabel [] [] hpair hrest ?_ ?_ ?_ ?_ (fun _ => rfl)
    · rw [hsym]; simp
    · rw [restDefs_eq hpair]; exact instrDefs_nodup hmainwf heb
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
theorem emitProg_asteps' {P : Prog} {ord : Bool} {asm : List Asm} {yst0 yst' : EvmState}
    (hnodup : (labelDefs asm).Nodup) (hwf : P.wfCheck = true)
    (hdom : ToAsm.Prog.domCheck P = true)
    (hemit : ToAsm.emitProgOrd ord P = some asm)
    (hrun : Run (model := model) P yst0 yst' .normal) :
    ASteps (model := model) asm ⟨asm, [], yst0⟩ ⟨[], [], yst'⟩ := by
  obtain ⟨asm₀, rfl, hpl⟩ := emitProg_placement hnodup hwf hemit
  have hnodup₀ : (labelDefs asm₀).Nodup := by
    rwa [ToAsm.labelDefs_elideJumps] at hnodup
  cases hrun with
  | normal heb hexec =>
    obtain ⟨a, hsteps, hsim⟩ := raw_entry_sim hnodup₀ hwf hdom hpl heb hexec
    obtain ⟨cret, hcret, hsteps2⟩ := hsim
    obtain rfl : cret = [] := Option.some.inj (hcret.symm.trans hpl.2.2.1)
    have hraw : ASteps (model := model) asm₀ ⟨asm₀, [], yst0⟩ ⟨[], [], yst'⟩ := by
      refine hsteps.trans ?_
      simpa using hsteps2
    have := asteps_elideJumps hnodup₀ hraw (List.suffix_refl _)
    simpa [elideConf, ToAsm.elideJumps] using this

theorem emitProg_ahalt' {P : Prog} {ord : Bool} {asm : List Asm} {yst0 yst' : EvmState}
    (hnodup : (labelDefs asm).Nodup) (hwf : P.wfCheck = true)
    (hdom : ToAsm.Prog.domCheck P = true)
    (hemit : ToAsm.emitProgOrd ord P = some asm)
    (hrun : Run (model := model) P yst0 yst' .halt) :
    ∃ conf, ASteps (model := model) asm ⟨asm, [], yst0⟩ conf ∧
      AHalt (model := model) asm conf yst' := by
  obtain ⟨asm₀, rfl, hpl⟩ := emitProg_placement hnodup hwf hemit
  have hnodup₀ : (labelDefs asm₀).Nodup := by
    rwa [ToAsm.labelDefs_elideJumps] at hnodup
  cases hrun with
  | halt heb hexec =>
    obtain ⟨a, hsteps, hsim⟩ := raw_entry_sim hnodup₀ hwf hdom hpl heb hexec
    obtain ⟨conf, hsteps2, hhalt⟩ := hsim
    refine ⟨elideConf conf, ?_, ahalt_elideJumps hhalt⟩
    have := asteps_elideJumps hnodup₀ (hsteps.trans hsteps2) (List.suffix_refl _)
    simpa [elideConf] using this

end YulEvmCompiler.SsaCfg
