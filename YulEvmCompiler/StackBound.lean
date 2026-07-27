import YulEvmCompiler.AsmSem

set_option warningAsError true
/-!
# YulEvmCompiler.StackBound — static stack-depth analysis for the Asm machine

The `evm-semantics` `Step` relation (since the determinism refactor, #140) carries a
stack-overflow guard on every rule: a success step fires only when the resulting operand stack
stays within the 1024-word EVM limit. The abstract Asm machine (`AStep`), by contrast, has an
**unbounded** operand stack (Yul has no such limit). So the Phase-B simulation
(`YulEvmCompiler.LowerCorrect`) is only valid for Asm runs whose stack stays within the limit —
formally, `astep_sim`/`asteps_sim` carry `a.stk.length ≤ 1023` (one slot of slack, because
`jump`/`jumpi`/`pushLabel` lower to `PUSH <addr>; JUMP`, transiently pushing the label address).

This file discharges that hypothesis by a **static stack-*layout* analysis**: a layout map
`H : List Asm → Option Layout` assigning each code position (a suffix of the program) the operand
stack *layout* reached there — a list of `Slot`s recording, per stack cell, whether it holds a plain
word or a code (return-address) value and its target label. A decidable well-formedness check
`ValidHeights` verifies the map. When it holds, every configuration reachable from the entry stays
within the limit — so the compiler can *reject* (return `none`) any program the check fails, exactly
the "prove no overflow" contract.

Tracking the full layout (not merely a height `Nat`) is what makes the analysis sound across `DUP`
and `SWAP`: duplicating or moving a return-address value would land it at a stack height its jump
target does not expect, breaking return-address consistency. The layout lets `stepConstraint`
*require* those instructions to touch only `word` slots — rejecting the (compiler-never-emitted)
programs that would dup/swap a return address.

The soundness core is the invariant `Inv` and its preservation. `Inv` tracks three things: the stack
fits (`≤ 1023`); the layout matches the map (`H code = some (layoutOf stk)`); and — the subtle part,
needed for `dynJump` (function return) — every `.code l` return-address value on the stack sits at a
position whose target label expects exactly the layout below it (`WF`).
-/

namespace YulEvmCompiler

open EvmSemantics EvmSemantics.EVM
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal)

/-! ### Slots and layouts -/

/-- A static abstraction of an operand-stack cell: either a plain word, or a code
(return-address) value tagged with its target label. -/
inductive Slot
  | word
  | code (l : Label)
  deriving DecidableEq

/-- A static operand-stack layout: top-of-stack first, mirroring `AConf.stk`. -/
abbrev Layout := List Slot

/-- The layout map assigns each analysed code position (a suffix of the program) the operand-stack
layout reached there. `none` = not analysed (unreachable / rejected). -/
abbrev LayoutMap := List Asm → Option Layout

/-- The static abstraction of a runtime stack value. -/
def slotOf : AVal → Slot
  | .word _ => .word
  | .code l => .code l

/-- The layout of a runtime stack. -/
def layoutOf (σ : List AVal) : Layout := σ.map slotOf

@[simp] theorem layoutOf_nil : layoutOf [] = [] := rfl
@[simp] theorem layoutOf_cons (v : AVal) (σ : List AVal) :
    layoutOf (v :: σ) = slotOf v :: layoutOf σ := rfl
@[simp] theorem layoutOf_length (σ : List AVal) : (layoutOf σ).length = σ.length := by
  simp [layoutOf]
theorem layoutOf_append (σ τ : List AVal) : layoutOf (σ ++ τ) = layoutOf σ ++ layoutOf τ := by
  simp [layoutOf]
@[simp] theorem slotOf_word (v : U256) : slotOf (.word v) = .word := rfl
@[simp] theorem slotOf_code (l : Label) : slotOf (.code l) = .code l := rfl

@[simp] theorem layoutOf_words (vs : List U256) :
    layoutOf (words vs) = List.replicate vs.length Slot.word := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [words_cons, layoutOf_cons, slotOf, ih, List.replicate_succ]

/-- `(replicate k x ++ L).drop k = L` — dropping a replicated prefix. -/
theorem drop_replicate_append {α} (k : Nat) (x : α) (L : List α) :
    (List.replicate k x ++ L).drop k = L := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.cons_append, List.drop_succ_cons]; exact ih

/-! ### The layout map and its well-formedness -/

/-- The well-formedness constraint one instruction `i` (with continuation `c`) imposes on the layout
map, given its entry layout `S`. Mirrors each `AStep` rule's effect on the stack and the EVM 1024
limit (with 1 slot of slack for the label-address push in the jump/`pushLabel` lowerings). `dup`/
`swap` additionally require the touched cells to be `word`s (rejecting programs that would dup/swap a
return address). -/
def stepConstraint (prog : List Asm) (H : LayoutMap) : Asm → List Asm → Layout → Prop
  | .push _,      c, S => H c = some (.word :: S) ∧ S.length + 1 ≤ 1023
  | .dup n,       c, S => S[n.val]? = some Slot.word ∧ H c = some (.word :: S) ∧ S.length + 1 ≤ 1023
  | .pushLabel l, c, S => H c = some (.code l :: S) ∧ S.length + 1 ≤ 1023 ∧
      ∃ c', findLabel l prog = some c' ∧ H c' = some S
  | .pop,         c, S => ∃ s S', S = s :: S' ∧ H c = some S'
  | .swap n,      c, S => S[0]? = some Slot.word ∧ S[n.val + 1]? = some Slot.word ∧ H c = some S
  | .label _,     c, S => H c = some S
  | .op yop,      c, S => ∃ o, opTable yop = some o ∧ Operation.popArity o ≤ S.length ∧
      (List.replicate (Operation.pushArity o) Slot.word ++ S.drop (Operation.popArity o)).length ≤ 1023 ∧
      H c = some (List.replicate (Operation.pushArity o) Slot.word ++ S.drop (Operation.popArity o))
  | .jump l,      _, S => ∃ c', findLabel l prog = some c' ∧ H c' = some S
  | .jumpi l,     c, S => ∃ S', S = .word :: S' ∧
      (∃ c', findLabel l prog = some c' ∧ H c' = some S') ∧ H c = some S'
  | .dynJump,     _, _ => True

/-- A layout map is **valid** for `prog` when every instruction position it analyses satisfies its
step constraint. Decidable-in-spirit: a checker computes `H` and verifies this. -/
def ValidHeights (prog : List Asm) (H : LayoutMap) : Prop :=
  ∀ i c, (i :: c) <:+ prog → ∀ S, H (i :: c) = some S → stepConstraint prog H i c S

/-! ### A decidable verifier for `ValidHeights` (the verified checker)

`stepConstraint` is stated with existentials (over the op-table entry and jump targets); the
computable `stepOK` mirrors it as a `Bool`, and `checkValid` folds it over every suffix position.
The layout table `H` itself is proposed by an *untrusted* solver — soundness rests only on the
verifier below, so a wrong proposal is simply rejected. -/

/-- Decidable mirror of `stepConstraint`. -/
def stepOK (prog : List Asm) (H : LayoutMap) : Asm → List Asm → Layout → Bool
  | .push _,      c, S => decide (H c = some (.word :: S)) && decide (S.length + 1 ≤ 1023)
  | .dup n,       c, S => decide (S[n.val]? = some Slot.word) && decide (H c = some (.word :: S))
      && decide (S.length + 1 ≤ 1023)
  | .pushLabel l, c, S => decide (H c = some (.code l :: S)) && decide (S.length + 1 ≤ 1023)
      && (match findLabel l prog with | some c' => decide (H c' = some S) | none => false)
  | .pop,         c, S => match S with | _ :: S' => decide (H c = some S') | [] => false
  | .swap n,      c, S => decide (S[0]? = some Slot.word) && decide (S[n.val + 1]? = some Slot.word)
      && decide (H c = some S)
  | .label _,     c, S => decide (H c = some S)
  | .op yop,      c, S => match opTable yop with
      | some o => decide (Operation.popArity o ≤ S.length)
          && decide ((List.replicate (Operation.pushArity o) Slot.word
              ++ S.drop (Operation.popArity o)).length ≤ 1023)
          && decide (H c = some (List.replicate (Operation.pushArity o) Slot.word
              ++ S.drop (Operation.popArity o)))
      | none => false
  | .jump l,      _, S => match findLabel l prog with | some c' => decide (H c' = some S) | none => false
  | .jumpi l,     c, S => match S with
      | .word :: S' => (match findLabel l prog with | some c' => decide (H c' = some S') | none => false)
          && decide (H c = some S')
      | _ => false
  | .dynJump,     _, _ => true

/-- `stepOK` soundly implies `stepConstraint`. -/
theorem stepOK_sound {prog : List Asm} {H : LayoutMap} {i : Asm} {c : List Asm} {S : Layout}
    (h : stepOK prog H i c S = true) : stepConstraint prog H i c S := by
  cases i with
  | push v =>
      simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at h; exact h
  | dup n =>
      simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at h; exact ⟨h.1.1, h.1.2, h.2⟩
  | pushLabel l =>
      simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hHc, hlen⟩, hf⟩ := h
      refine ⟨hHc, hlen, ?_⟩
      revert hf; split
      · next c' he => intro hf; exact ⟨c', he, by simpa using hf⟩
      · intro hf; simp at hf
  | pop =>
      revert h; simp only [stepOK]; split
      · next s S' => intro h; exact ⟨s, S', rfl, by simpa using h⟩
      · intro h; simp at h
  | swap n =>
      simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at h; exact ⟨h.1.1, h.1.2, h.2⟩
  | label l =>
      simp only [stepOK, decide_eq_true_eq] at h; exact h
  | op yop =>
      revert h; simp only [stepOK]; split
      · next o he =>
          intro h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          exact ⟨o, he, h.1.1, h.1.2, h.2⟩
      · intro h; simp at h
  | jump l =>
      revert h; simp only [stepOK]; split
      · next c' he => intro h; exact ⟨c', he, by simpa using h⟩
      · intro h; simp at h
  | jumpi l =>
      revert h; simp only [stepOK]; split
      · next S' =>
          intro h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          refine ⟨S', rfl, ?_, h.2⟩
          revert h; split
          · next c' he => intro h; exact ⟨c', he, by simpa using h.1⟩
          · intro h; simp at h
      · intro h; simp at h
  | dynJump => trivial

/-- The verifier: `H` satisfies every suffix position's step constraint. -/
def checkValid (prog : List Asm) (H : LayoutMap) : Bool :=
  prog.tails.all (fun s => match s, H s with
    | i :: c, some S => stepOK prog H i c S
    | _, _ => true)

/-- **Verifier soundness**: a passing `checkValid` yields `ValidHeights`. -/
theorem checkValid_sound {prog : List Asm} {H : LayoutMap} (h : checkValid prog H = true) :
    ValidHeights prog H := by
  intro i c hsuf S hHS
  rw [checkValid, List.all_eq_true] at h
  have hmem : (i :: c) ∈ prog.tails := (List.mem_tails _ _).mpr hsuf
  have hs := h (i :: c) hmem
  rw [hHS] at hs
  exact stepOK_sound hs

/-- **Well-formed layout**: every `.code l` return-address cell sits at a position whose target
label `l` expects exactly the layout `below` it. Splitting the layout as `above ++ .code l :: below`,
`below` is what remains after returning through it (`dynJump`), so its target's layout is `below`. -/
def WF (prog : List Asm) (H : LayoutMap) (S : Layout) : Prop :=
  ∀ above l below, S = above ++ .code l :: below →
    ∃ c', findLabel l prog = some c' ∧ H c' = some below

/-- Well-formedness is inherited by any suffix (the slots below a return address are unchanged). -/
theorem WF.of_suffix {prog H} {S S' : Layout} (h : WF prog H S) (hsuf : S' <:+ S) :
    WF prog H S' := by
  obtain ⟨t, rfl⟩ := hsuf
  intro above l below heq
  exact h (t ++ above) l below (by rw [List.append_assoc, ← heq])

/-- Popping the top preserves well-formedness for the tail. -/
theorem WF.tail {prog H} {s : Slot} {S : Layout} (h : WF prog H (s :: S)) : WF prog H S :=
  h.of_suffix (List.suffix_cons s S)

/-- Dropping any prefix preserves well-formedness. -/
theorem WF.drop {prog H} {S : Layout} (h : WF prog H S) (k : Nat) : WF prog H (S.drop k) :=
  h.of_suffix ⟨S.take k, List.take_append_drop k S⟩

/-- Pushing a plain word preserves well-formedness. -/
theorem WF.word_cons {prog H} {S : Layout} (h : WF prog H S) : WF prog H (.word :: S) := by
  intro above l below heq
  cases above with
  | nil => simp at heq
  | cons x above' =>
      rw [List.cons_append] at heq; injection heq with _ heq2; exact h above' l below heq2

/-- Pushing a code address at the layout its target expects preserves well-formedness. -/
theorem WF.code_cons {prog H} {S : Layout} {l0 : Label} (h : WF prog H S)
    (hc : ∃ c', findLabel l0 prog = some c' ∧ H c' = some S) : WF prog H (.code l0 :: S) := by
  intro above l below heq
  cases above with
  | nil => simp only [List.nil_append, List.cons.injEq, Slot.code.injEq] at heq
           obtain ⟨rfl, rfl⟩ := heq; exact hc
  | cons x above' =>
      rw [List.cons_append] at heq; injection heq with _ heq2; exact h above' l below heq2

/-- Prepending a block of plain words preserves well-formedness. -/
theorem WF.replicate_word {prog H} {S : Layout} (h : WF prog H S) (k : Nat) :
    WF prog H (List.replicate k Slot.word ++ S) := by
  induction k with
  | zero => simpa using h
  | succ k ih => rw [List.replicate_succ, List.cons_append]; exact ih.word_cons

/-! ### The invariant and its preservation -/

/-- The reachable-configuration invariant. -/
structure Inv (prog : List Asm) (H : LayoutMap) (conf : AConf) : Prop where
  fits   : conf.stk.length ≤ 1023
  height : H conf.code = some (layoutOf conf.stk)
  wf     : WF prog H (layoutOf conf.stk)

/-- **The bound falls straight out of the invariant.** -/
theorem Inv.bound {prog H} {conf : AConf} (h : Inv prog H conf) : conf.stk.length ≤ 1023 :=
  h.fits

variable [model : ExternalModel]

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option maxHeartbeats 2000000 in
/-- **Op-arity coupling**: whenever a builtin (local op or external call/create) executes
successfully to `.ok rets`, its actual argument and result counts match the `Operation`'s declared
`popArity`/`pushArity`. Ties the abstract `AStep.op` stack effect to the layout arithmetic. -/
theorem builtin_arity {yop : Op} {o : Operation} (hop : opTable yop = some o)
    {args rets : List U256} {yst yst' : EvmState}
    (h : builtinWithExternal model.calls model.creates yop args yst (.ok rets yst')) :
    args.length = Operation.popArity o ∧ rets.length = Operation.pushArity o := by
  cases yop <;>
    simp only [opTable, Option.some.injEq, reduceCtorEq] at hop <;>
    subst hop <;>
    rcases args with _|⟨a,_|⟨b,_|⟨c,_|⟨d,_|⟨e,_|⟨f,_|⟨g,_|⟨hh,_⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [builtinWithExternal, YulSemantics.EVM.externalCall, YulSemantics.EVM.externalCreate,
      YulSemantics.EVM.stepOp, YulSemantics.EVM.bin, YulSemantics.EVM.un, YulSemantics.EVM.ter,
      YulSemantics.EVM.rd0, YulSemantics.EVM.rd1, YulSemantics.EVM.guardStatic, reduceCtorEq] at h <;>
    (try split at h) <;>
    (try simp only [reduceCtorEq, Option.some.injEq, YulSemantics.BuiltinResult.ok.injEq] at h)
  all_goals (first
    | done
    | (refine ⟨by simp [Operation.popArity], ?_⟩; first
        | (obtain ⟨rfl, -⟩ := h; simp [Operation.pushArity])
        | (obtain ⟨_, -, rfl, -⟩ := h; simp [Operation.pushArity])))

set_option linter.unusedVariables false in
/-- **Preservation.** Given a valid layout map, `Inv` is preserved by every `AStep`. The `dup`/
`swap` cases are the payoff of tracking layouts: the constraint forces the touched cells to be
words, so no return address is ever duplicated or moved. -/
theorem Inv.step {prog : List Asm} {H : LayoutMap} (hV : ValidHeights prog H)
    {a b : AConf} (hstep : AStep (model := model) prog a b) (hsuf : a.code <:+ prog)
    (hinv : Inv prog H a) : Inv prog H b := by
  cases hstep with
  | @push v c σ yst =>
      obtain ⟨hHc, hlen⟩ := hV (.push v) c hsuf _ hinv.height
      refine ⟨?_, ?_, ?_⟩
      · show (AVal.word v :: σ).length ≤ 1023
        have h2 : (layoutOf σ).length + 1 ≤ 1023 := hlen
        simp only [layoutOf_length] at h2; simpa using h2
      · show H c = some (layoutOf (AVal.word v :: σ))
        simpa only [layoutOf_cons, slotOf_word] using hHc
      · show WF prog H (layoutOf (AVal.word v :: σ))
        simpa only [layoutOf_cons, slotOf_word] using hinv.wf.word_cons
  | @op yop args rets c σ yst yst' hstepOp =>
      obtain ⟨o, hop, _, hbnd, hHc⟩ := hV (.op yop) c hsuf _ hinv.height
      obtain ⟨hargs, hrets⟩ := builtin_arity hop hstepOp
      have hSdrop : (layoutOf (words args ++ σ)).drop (Operation.popArity o) = layoutOf σ := by
        rw [layoutOf_append, layoutOf_words, ← hargs]; exact drop_replicate_append _ _ _
      have hres : layoutOf (words rets ++ σ)
          = List.replicate (Operation.pushArity o) Slot.word ++
              (layoutOf (words args ++ σ)).drop (Operation.popArity o) := by
        rw [hSdrop, layoutOf_append, layoutOf_words, hrets]
      refine ⟨?_, ?_, ?_⟩
      · show (words rets ++ σ).length ≤ 1023
        have h2 := hbnd; rw [← hres, layoutOf_length] at h2; exact h2
      · show H c = some (layoutOf (words rets ++ σ)); rw [hres]; exact hHc
      · show WF prog H (layoutOf (words rets ++ σ))
        rw [hres, hSdrop]
        have hw := hinv.wf
        rw [layoutOf_append, layoutOf_words] at hw
        exact WF.replicate_word (hw.of_suffix ⟨List.replicate args.length Slot.word, rfl⟩) _
  | @dup n v τ ρ c yst hτ =>
      obtain ⟨hslot, hHc, hlen⟩ := hV (.dup n) c hsuf _ hinv.height
      have hv : slotOf v = .word := by
        have key : (layoutOf (τ ++ v :: ρ))[n.val]? = some (slotOf v) := by
          rw [layoutOf_append, layoutOf_cons, ← hτ, ← layoutOf_length τ,
              List.getElem?_append_right (Nat.le_refl _)]
          simp
        exact Option.some.inj (key.symm.trans hslot)
      refine ⟨?_, ?_, ?_⟩
      · show (v :: (τ ++ v :: ρ)).length ≤ 1023
        have h2 : (layoutOf (τ ++ v :: ρ)).length + 1 ≤ 1023 := hlen
        simp only [layoutOf_length] at h2; simpa using h2
      · show H c = some (layoutOf (v :: (τ ++ v :: ρ)))
        simpa only [layoutOf_cons, hv] using hHc
      · show WF prog H (layoutOf (v :: (τ ++ v :: ρ)))
        simpa only [layoutOf_cons, hv] using hinv.wf.word_cons
  | @swap n x y τ ρ c yst hτ =>
      obtain ⟨hx, hy, hHc⟩ := hV (.swap n) c hsuf _ hinv.height
      have hsx : slotOf x = .word := by
        have key : (layoutOf (x :: (τ ++ y :: ρ)))[0]? = some (slotOf x) := by simp [layoutOf_cons]
        exact Option.some.inj (key.symm.trans hx)
      have hsy : slotOf y = .word := by
        have key : (layoutOf (x :: (τ ++ y :: ρ)))[n.val + 1]? = some (slotOf y) := by
          simp only [layoutOf_cons, layoutOf_append, List.getElem?_cons_succ]
          rw [← hτ, ← layoutOf_length τ, List.getElem?_append_right (Nat.le_refl _)]
          simp
        exact Option.some.inj (key.symm.trans hy)
      have hlayeq : layoutOf (y :: (τ ++ x :: ρ)) = layoutOf (x :: (τ ++ y :: ρ)) := by
        simp only [layoutOf_cons, layoutOf_append, hsx, hsy]
      refine ⟨?_, ?_, ?_⟩
      · show (y :: (τ ++ x :: ρ)).length ≤ 1023
        have h2 : (x :: (τ ++ y :: ρ)).length ≤ 1023 := hinv.fits
        simp only [List.length_cons, List.length_append] at h2 ⊢; omega
      · show H c = some (layoutOf (y :: (τ ++ x :: ρ))); rw [hlayeq]; exact hHc
      · show WF prog H (layoutOf (y :: (τ ++ x :: ρ))); rw [hlayeq]; exact hinv.wf
  | @pop v σ c yst =>
      obtain ⟨_, S', hSeq, hHc⟩ := hV .pop c hsuf _ hinv.height
      rw [layoutOf_cons] at hSeq; injection hSeq with _ hS'
      refine ⟨?_, ?_, ?_⟩
      · show σ.length ≤ 1023
        have h2 : (v :: σ).length ≤ 1023 := hinv.fits
        simp only [List.length_cons] at h2; omega
      · show H c = some (layoutOf σ); rw [hS']; exact hHc
      · show WF prog H (layoutOf σ)
        have hw := hinv.wf; rw [layoutOf_cons] at hw; exact hw.tail
  | @label l c σ yst =>
      have hHc := hV (.label l) c hsuf _ hinv.height
      exact ⟨hinv.fits, hHc, hinv.wf⟩
  | @jump l c c' σ yst hfind =>
      obtain ⟨c'', hf'', hH''⟩ := hV (.jump l) c hsuf _ hinv.height
      rw [hfind] at hf''; obtain rfl := Option.some.inj hf''
      exact ⟨hinv.fits, hH'', hinv.wf⟩
  | @jumpiTaken l v c c' σ yst hv hfind =>
      obtain ⟨S', hSeq, ⟨c'', hf'', hH''⟩, _⟩ := hV (.jumpi l) c hsuf _ hinv.height
      rw [layoutOf_cons, slotOf_word] at hSeq; injection hSeq with _ hS'
      rw [hfind] at hf''; obtain rfl := Option.some.inj hf''
      refine ⟨?_, ?_, ?_⟩
      · show σ.length ≤ 1023
        have h2 : (AVal.word v :: σ).length ≤ 1023 := hinv.fits
        simp only [List.length_cons] at h2; omega
      · show H c' = some (layoutOf σ); rw [hS']; exact hH''
      · show WF prog H (layoutOf σ)
        have hw := hinv.wf; rw [layoutOf_cons, slotOf_word] at hw; exact hw.tail
  | @jumpiFall l v c σ yst hv =>
      obtain ⟨S', hSeq, _, hHc⟩ := hV (.jumpi l) c hsuf _ hinv.height
      rw [layoutOf_cons, slotOf_word] at hSeq; injection hSeq with _ hS'
      refine ⟨?_, ?_, ?_⟩
      · show σ.length ≤ 1023
        have h2 : (AVal.word v :: σ).length ≤ 1023 := hinv.fits
        simp only [List.length_cons] at h2; omega
      · show H c = some (layoutOf σ); rw [hS']; exact hHc
      · show WF prog H (layoutOf σ)
        have hw := hinv.wf; rw [layoutOf_cons, slotOf_word] at hw; exact hw.tail
  | @pushLabel l c σ yst hdef =>
      obtain ⟨hHc, hlen, hfind⟩ := hV (.pushLabel l) c hsuf _ hinv.height
      refine ⟨?_, ?_, ?_⟩
      · show (AVal.code l :: σ).length ≤ 1023
        have h2 : (layoutOf σ).length + 1 ≤ 1023 := hlen
        simp only [layoutOf_length] at h2; simpa using h2
      · show H c = some (layoutOf (AVal.code l :: σ))
        simpa only [layoutOf_cons, slotOf_code] using hHc
      · show WF prog H (layoutOf (AVal.code l :: σ))
        simpa only [layoutOf_cons, slotOf_code] using hinv.wf.code_cons hfind
  | @dynJump l c c' σ yst hfind =>
      have hw := hinv.wf
      rw [layoutOf_cons, slotOf_code] at hw
      obtain ⟨c'', hf'', hH''⟩ := hw [] l (layoutOf σ) (by simp)
      rw [hfind] at hf''; obtain rfl := Option.some.inj hf''
      refine ⟨?_, hH'', hw.tail⟩
      show σ.length ≤ 1023
      have h2 : (AVal.code l :: σ).length ≤ 1023 := hinv.fits
      simp only [List.length_cons] at h2; omega

/-- **The invariant holds at every reachable configuration**, hence the stack stays within the
EVM limit throughout any Asm run — the hypothesis `astep_sim`/`asteps_sim` require. -/
theorem Inv.reach {prog : List Asm} {H : LayoutMap} (hV : ValidHeights prog H)
    {a b : AConf} (hsteps : ASteps (model := model) prog a b) (hsuf : a.code <:+ prog)
    (hinv : Inv prog H a) : Inv prog H b := by
  induction hsteps with
  | refl => exact hinv
  | head hstep _ ih => exact ih ((hstep.suffix hsuf)) (hinv.step hV hstep hsuf)

omit model in
/-- The entry configuration `⟨prog, [], yst⟩` satisfies the invariant, provided the map assigns the
whole program the empty layout. -/
theorem Inv.entry {prog : List Asm} {H : LayoutMap} (h0 : H prog = some []) (yst : EvmState) :
    Inv prog H ⟨prog, [], yst⟩ where
  fits := by simp
  height := by simpa using h0
  wf := by intro above l below hi; simp at hi

/-- **The run stack-bound**, in the exact shape the Phase-B lemmas consume: every configuration
reachable from the entry keeps its stack within the EVM limit. -/
theorem run_stack_bound {prog : List Asm} {H : LayoutMap}
    (hV : ValidHeights prog H) (h0 : H prog = some []) (yst : EvmState) :
    ∀ mid, ASteps (model := model) prog ⟨prog, [], yst⟩ mid → mid.stk.length ≤ 1023 :=
  fun _ hsteps => (Inv.reach hV hsteps (List.suffix_refl _) (Inv.entry h0 yst)).bound

end YulEvmCompiler
