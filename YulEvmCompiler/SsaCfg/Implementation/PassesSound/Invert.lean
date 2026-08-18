import YulEvmCompiler.SsaCfg.Implementation.PassesSound.Wf
set_option warningAsError true

/-!
# YulEvmCompiler.SsaCfg.Implementation.PassesSound.Invert

Soundness of **branch-sense normalization** (`Passes.invertBranches`).

`JUMPI` and the `branch` rule both select on "condition nonzero", so an
`iszero` in condition position is a pure negation of a choice the terminator
already makes: `branch (iszero x) t f` and `branch x f t` take the same
edge in every state.

The whole proof rests on one equation — `R c = iszero (R x)` at the moment
the branch is evaluated — and the pass is restricted precisely so that this
equation is *local*: the `iszero` is the block's **last** instruction, so it
has just executed and nothing has run since. No dominance argument, no
provenance history, no single-assignment reasoning beyond the `c ≠ x` the
table already guarantees.
-/

namespace YulEvmCompiler.SsaCfg

open YulSemantics.EVM (U256 EvmState Op builtinWithExternal stepOp ExternalCalls
  ExternalCreates b2w)
open YulSemantics (Outcome)
variable [model : ExternalModel]

namespace Passes

/-! ### The equation the rewrite needs -/

/-- Every entry of the block's `iszero` table is *realized* in `R`: the
condition holds the negation of its argument. -/
def IszeroEq (m : Std.HashMap ValId ValId) (R : Regs) : Prop :=
  ∀ c x : ValId, m[c]? = some x → ∃ v, R x = some v ∧ R c = some (b2w (v = 0))

/-- Carried through a block: the equation is owed only once the block's
instructions have all run (the `iszero` is the last of them). -/
def IszeroPending (m : Std.HashMap ValId ValId) (R : Regs) (is : List Instr) : Prop :=
  is = [] → IszeroEq m R

/-- Inverting the `iszero` built-in: it consumes one word and produces its
zero-test. -/
theorem iszero_ok {args rets : List U256} {st st' : EvmState}
    (h : builtinWithExternal model.calls model.creates model.gas .iszero args st (.ok rets st')) :
    ∃ v, args = [v] ∧ rets = [b2w (v = 0)] := by
  rw [builtin_of_pure (by decide)] at h
  match args with
  | [a] =>
      simp [stepOp, YulSemantics.EVM.un] at h
      exact ⟨a, rfl, by simp [h.1]⟩
  | [] => simp [stepOp, YulSemantics.EVM.un] at h
  | _ :: _ :: _ => simp [stepOp, YulSemantics.EVM.un] at h

/-- The edge a branch terminator selects in `R`. -/
def selEdge (R : Regs) : Term → Option Edge
  | .branch c t fe =>
      match R c with
      | some v => some (if v ≠ 0 then t else fe)
      | none => none
  | _ => none

omit model in
theorem invertTerm_go_isBranch (m : Std.HashMap ValId ValId) :
    ∀ (n : Nat) (c : ValId) (t fe : Edge),
      ∃ c' t' fe', invertTerm.go m c t fe n = .branch c' t' fe'
  | 0, c, t, fe => ⟨c, t, fe, rfl⟩
  | n + 1, c, t, fe => by
      unfold invertTerm.go
      split
      case _ x _ => exact invertTerm_go_isBranch m n x fe t
      case _ => exact ⟨c, t, fe, rfl⟩

omit model in
/-- **The semantic core.** Under the equation, rewriting the branch does not
change which edge is taken. -/
theorem invertTerm_go_sel {m : Std.HashMap ValId ValId} {R : Regs}
    (hInv : IszeroEq m R) :
    ∀ (n : Nat) (c : ValId) (t fe : Edge),
      selEdge R (invertTerm.go m c t fe n) = selEdge R (.branch c t fe)
  | 0, _, _, _ => rfl
  | n + 1, c, t, fe => by
      unfold invertTerm.go
      split
      case _ x hm =>
          rw [invertTerm_go_sel hInv n x fe t]
          obtain ⟨v, hx, hc⟩ := hInv c x hm
          simp only [selEdge, hx, hc]
          by_cases hv : v = 0
          · subst hv
            simp [b2w]
          · simp [b2w]
      case _ => rfl

/-- Build the `Exec` step for a branch terminator from the edge it selects. -/
theorem exec_branch_of_sel {P : Prog} {f' : Func} {R : Regs} {st : EvmState}
    {T : Term} {e : Edge} {tb : Block} {args : List U256} {res : FRes}
    (hT : ∃ c' t' fe', T = .branch c' t' fe')
    (hsel : selEdge R T = some e)
    (htb : f'.blocks[e.target]? = some tb)
    (hargs : R.getMany e.args = some args)
    (hlen : tb.params.length = args.length)
    (htail : Exec (model := model) P f' (R.setMany tb.params args) st
      ⟨tb.instrs, tb.term⟩ res) :
    Exec (model := model) P f' R st ⟨[], T⟩ res := by
  obtain ⟨c', t', fe', rfl⟩ := hT
  simp only [selEdge] at hsel
  rcases hc : R c' with _ | v
  · rw [hc] at hsel; simp at hsel
  · rw [hc] at hsel
    simp only [Option.some.injEq] at hsel
    by_cases hv : v ≠ 0
    · rw [if_pos hv] at hsel
      subst hsel
      exact Exec.branchTrue hc hv htb hargs hlen htail
    · rw [if_neg hv] at hsel
      subst hsel
      exact Exec.branchFalse (by simpa [not_not.mp hv] using hc) htb hargs hlen htail

/-! ### Discharging the pending equation

A block's table is nonempty only when its *last* instruction is the
`iszero`, so whenever the remaining instruction list becomes empty we know
exactly which instruction just ran. -/

omit model in
/-- If a suffix runs out after `i`, then `i` was the block's last
instruction. -/
theorem getLast_of_suffix_singleton {b : Block} {i : Instr}
    (hsuf : (i :: []) <:+ b.instrs) : b.instrs.getLast? = some i := by
  obtain ⟨pre, hpre⟩ := hsuf
  rw [← hpre]
  simp

omit model in
/-- A non-`iszero` last instruction leaves the table empty. -/
theorem table_empty_of_last {uses : Std.HashMap ValId Nat} {b : Block} {i : Instr}
    (hlast : b.instrs.getLast? = some i) (hnp : iszeroPair i = none) :
    blockIszeroSources uses b = ∅ := by
  unfold blockIszeroSources
  rw [hlast]
  dsimp only
  rw [hnp]

omit model in
theorem iszeroEq_of_empty {R : Regs} : IszeroEq ∅ R := by
  intro c x h; simp at h

omit model in
/-- Entering a fresh block, nothing is owed: either it has instructions
still to run, or it has none and hence an empty table. -/
theorem pending_entry (uses : Std.HashMap ValId Nat) (b : Block) (R : Regs) :
    IszeroPending (blockIszeroSources uses b) R b.instrs := by
  intro hnil
  have : blockIszeroSources uses b = ∅ := by
    unfold blockIszeroSources
    rw [hnil]
    rfl
  rw [this]
  exact iszeroEq_of_empty

omit model in
/-- A step that is not the `iszero` leaves nothing owed after it. -/
theorem pending_of_nonIszero {uses : Std.HashMap ValId Nat} {b : Block}
    {i : Instr} {is : List Instr} {R : Regs}
    (hsuf : (i :: is) <:+ b.instrs) (hnp : iszeroPair i = none) :
    IszeroPending (blockIszeroSources uses b) R is := by
  intro hnil
  subst hnil
  rw [table_empty_of_last (getLast_of_suffix_singleton hsuf) hnp]
  exact iszeroEq_of_empty

end Passes

/-! ### The simulation -/

open Passes in
/-- Lockstep simulation of an arbitrary suffix of a block. The instruction
list is untouched by the pass, so every instruction step is a congruence;
all the content is in the terminator, and `IszeroPending` is what carries
the `iszero`'s equation to it. -/
theorem invertBranches_exec_aux {P : Prog} {f : Func} {R : Regs} {st : EvmState}
    {rest : Rest} {res : FRes} (h : Exec (model := model) P f R st rest res) :
    ∀ {b : Block}, rest.instrs <:+ b.instrs → rest.term = b.term →
      IszeroPending (blockIszeroSources (useCounts f) b) R rest.instrs →
      Exec (model := model) P (Passes.invertBranches f) R st
        ⟨rest.instrs, Passes.invertTerm (blockIszeroSources (useCounts f) b) b.term⟩
        res := by
  induction h with
  | @const f R st d v is t res htail ih =>
    intro b hsuf hterm hpend
    refine Exec.const (ih (b := b) ((List.suffix_cons _ _).trans hsuf) hterm ?_)
    exact pending_of_nonIszero hsuf (by simp [Passes.iszeroPair])
  | @op f R st st' ds yop as args rets is t res hg hbi hlen htail ih =>
    intro b hsuf hterm hpend
    refine Exec.op hg hbi hlen (ih (b := b) ((List.suffix_cons _ _).trans hsuf) hterm ?_)
    -- either this instruction is the `iszero` (and its equation is now
    -- realized) or the table is empty
    intro hnil
    subst hnil
    have hlast := getLast_of_suffix_singleton hsuf
    rcases hnp : Passes.iszeroPair (Instr.op ds yop as) with _ | ⟨d, a⟩
    · rw [table_empty_of_last hlast hnp]; exact iszeroEq_of_empty
    · intro c x hcx
      obtain ⟨hlast', hne⟩ := Passes.blockIszeroSources_spec hcx
      rw [hlast] at hlast'
      have heq : Instr.op ds yop as = Instr.op [c] .iszero [x] := Option.some.inj hlast'
      injection heq with hds hyop has
      subst hds; subst hyop; subst has
      obtain ⟨w, hargs, hrets⟩ := iszero_ok hbi
      subst hargs; subst hrets
      have hw : R x = some w := by
        rcases hrx : R x with _ | u
        · rw [Regs.getMany_cons, hrx] at hg; simp at hg
        · rw [Regs.getMany_cons, hrx] at hg
          simp only [Option.bind_some, Regs.getMany_nil, Option.map_some,
            Option.some.injEq, List.cons.injEq, and_true] at hg
          subst hg
          rfl
      refine ⟨w, ?_, ?_⟩
      · rw [Regs.setMany_of_not_mem _ [c] _ (by simp [Ne.symm hne])]; exact hw
      · simp [Regs.setMany, Regs.set]
  | @opHalt f R st st' ds yop as args is t hg hbi =>
    intro b hsuf hterm hpend
    exact Exec.opHalt hg hbi
  | @call f g R st st' ds as fid args rvals eb is t res hfid hg hplen heb hbody hlen htail
      ihbody ih =>
    intro b hsuf hterm hpend
    refine Exec.call hfid hg hplen heb hbody hlen
      (ih (b := b) ((List.suffix_cons _ _).trans hsuf) hterm ?_)
    exact pending_of_nonIszero hsuf (by simp [Passes.iszeroPair])
  | @callHalt f g R st st' ds as fid args eb is t hfid hg hplen heb hbody ihbody =>
    intro b hsuf hterm hpend
    exact Exec.callHalt hfid hg hplen heb hbody
  | @jump f R st e tb args res htb hga hlen htail ih =>
    intro b hsuf hterm hpend
    rw [← hterm]
    refine Exec.jump (Passes.invertBranches_get htb) hga (by simpa using hlen) ?_
    exact ih (b := tb) (List.suffix_refl _) rfl (pending_entry _ _ _)
  | @branchTrue f R st c v et ef tb args res hc hv htb hga hlen htail ih =>
    intro b hsuf hterm hpend
    rw [← hterm]
    have hInv := hpend rfl
    have hsel : selEdge R (Passes.invertTerm
        (blockIszeroSources (useCounts f) b) (Term.branch c et ef)) = some et := by
      rw [show Passes.invertTerm (blockIszeroSources (useCounts f) b)
          (Term.branch c et ef)
        = Passes.invertTerm.go (blockIszeroSources (useCounts f) b) c et ef 8 from rfl,
        invertTerm_go_sel hInv]
      simp only [selEdge, hc]
      rw [if_pos hv]
    exact exec_branch_of_sel (invertTerm_go_isBranch _ 8 c et ef) hsel
      (Passes.invertBranches_get htb) hga (by simpa using hlen)
      (ih (b := tb) (List.suffix_refl _) rfl (pending_entry _ _ _))
  | @branchFalse f R st c et ef tb args res hc htb hga hlen htail ih =>
    intro b hsuf hterm hpend
    rw [← hterm]
    have hInv := hpend rfl
    have hsel : selEdge R (Passes.invertTerm
        (blockIszeroSources (useCounts f) b) (Term.branch c et ef)) = some ef := by
      rw [show Passes.invertTerm (blockIszeroSources (useCounts f) b)
          (Term.branch c et ef)
        = Passes.invertTerm.go (blockIszeroSources (useCounts f) b) c et ef 8 from rfl,
        invertTerm_go_sel hInv]
      simp only [selEdge, hc]
      rw [if_neg (by simp)]
    exact exec_branch_of_sel (invertTerm_go_isBranch _ 8 c et ef) hsel
      (Passes.invertBranches_get htb) hga (by simpa using hlen)
      (ih (b := tb) (List.suffix_refl _) rfl (pending_entry _ _ _))
  | @ret f R st xs vals hv =>
    intro b hsuf hterm hpend
    rw [← hterm]
    exact Exec.ret hv
  | @halt f R st st' yop as args hga hbi =>
    intro b hsuf hterm hpend
    rw [← hterm]
    exact Exec.halt hga hbi

open Passes in
/-- **Soundness of branch-sense normalization.** -/
theorem invertBranches_sound {P : Prog} {f : Func} {args : List U256}
    {st : EvmState} {res : FRes} {eb eb' : Block}
    (heb : f.blocks[f.entry]? = some eb)
    (heb' : (Passes.invertBranches f).blocks[f.entry]? = some eb')
    (hexec : Exec (model := model) P f (Regs.empty.setMany f.params args) st
      ⟨eb.instrs, eb.term⟩ res) :
    Exec (model := model) P (Passes.invertBranches f)
      (Regs.empty.setMany f.params args) st ⟨eb'.instrs, eb'.term⟩ res := by
  have hget := Passes.invertBranches_get heb
  rw [heb'] at hget
  obtain rfl : eb' = { eb with
      term := Passes.invertTerm (blockIszeroSources (useCounts f) eb) eb.term } :=
    Option.some.inj hget
  exact invertBranches_exec_aux hexec (List.suffix_refl _) rfl
    (pending_entry _ _ _)

end YulEvmCompiler.SsaCfg
