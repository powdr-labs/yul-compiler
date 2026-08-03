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
`H : List Asm → Option StkLayout` assigning each code position (a suffix of the program) the operand
stack *layout* reached there — a list of `Slot`s recording, per stack cell, whether it holds a plain
word or a *return-address* value, and in the latter case the **layout the target label expects on
return** (`Slot.code R`). A decidable check `checkValid` verifies the map; when it holds every
configuration reachable from the entry stays within the limit, so the compiler can *reject*
(return `none`) any program the check fails — exactly the "prove no overflow" contract.

## Why return layouts, not fixed heights

The compiler's function epilogue rotates the return address to the top with `retRot`
(`SWAP1…SWAPk`) — it **moves** a return-address value past the `k` result words. So a return
address's *current* below-stack changes over its lifetime (`C` at the `pushLabel`, then
`word×k ++ C` at the `dynJump`). A design that pinned each return address to a fixed below-layout
(or below-height) would reject every value-returning function.

Instead, each `Slot.code R` records the layout `R` the address's target label expects **on return**
(`R = H (target)`, `= word×k ++ C`, statically known from the callee's return arity). This tag
travels *with* the value under `dup`/`swap`, so those instructions may freely move return addresses.
The return-consistency check `R = below` is imposed **only at `dynJump` positions** (via
`stepConstraint`), where the rotation has completed and it genuinely holds. The correspondence
`StkMatch` between the runtime stack and the layout is then purely structural.
-/

namespace YulEvmCompiler

open EvmSemantics EvmSemantics.EVM
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal)

/-! ### Slots, layouts, and the runtime correspondence -/

/-- A static abstraction of an operand-stack cell: either a plain word, or a return-address value
tagged with its target **code position** (the suffix `findLabel` returns). The layout that position
expects on return is looked up via the map `H`, and checked for consistency only at `dynJump`. -/
inductive Slot
  | word
  | code (tgt : List Asm)
  deriving DecidableEq

/-- A static operand-stack layout: top-of-stack first, mirroring `AConf.stk`. -/
abbrev StkLayout := List Slot

/-- The layout map assigns each analysed code position (a suffix of the program) the **set** of
operand-stack layouts reachable there. A set (not a single layout) is essential: a function called
from several call sites is entered at different absolute stack depths, so its shared entry position
genuinely has one reaching layout per site. An empty list = not analysed (unreachable / rejected).
Recursion or a stack-growing loop yields infinitely many reaching layouts, so the solver rejects it. -/
abbrev LayoutMap := List Asm → List StkLayout

/-- The runtime stack ↔ layout correspondence: words match `word`; a runtime return address
`code l` matches `code tgt` exactly when `l` resolves to `tgt`. Purely structural, so `dup`/`swap`
transport it for free — the return-consistency check lives in `stepConstraint` at `dynJump`. -/
inductive StkMatch (prog : List Asm) (H : LayoutMap) : List AVal → StkLayout → Prop
  | nil : StkMatch prog H [] []
  | word {v : U256} {σ : List AVal} {S : StkLayout} :
      StkMatch prog H σ S → StkMatch prog H (.word v :: σ) (.word :: S)
  | code {l : Label} {c' : List Asm} {σ : List AVal} {S : StkLayout} :
      findLabel l prog = some c' → StkMatch prog H σ S →
      StkMatch prog H (.code l :: σ) (.code c' :: S)

/-- Matched stacks have equal length. -/
theorem StkMatch.length_eq {prog H} {σ : List AVal} {S : StkLayout}
    (h : StkMatch prog H σ S) : σ.length = S.length := by
  induction h with
  | nil => rfl
  | word _ ih => simp [ih]
  | code _ _ ih => simp [ih]

/-- Concatenation of matched stacks. -/
theorem StkMatch.append {prog H} {σ₁ σ₂ : List AVal} {S₁ S₂ : StkLayout}
    (h₁ : StkMatch prog H σ₁ S₁) (h₂ : StkMatch prog H σ₂ S₂) :
    StkMatch prog H (σ₁ ++ σ₂) (S₁ ++ S₂) := by
  induction h₁ with
  | nil => exact h₂
  | word _ ih => exact .word ih
  | code hf _ ih => exact .code hf ih

/-- Splitting a matched concatenation. -/
theorem StkMatch.append_inv {prog H} {σ₁ σ₂ : List AVal} {S : StkLayout}
    (h : StkMatch prog H (σ₁ ++ σ₂) S) :
    ∃ S₁ S₂, S = S₁ ++ S₂ ∧ StkMatch prog H σ₁ S₁ ∧ StkMatch prog H σ₂ S₂ := by
  induction σ₁ generalizing S with
  | nil => exact ⟨[], S, rfl, .nil, h⟩
  | cons v σ₁ ih =>
      rw [List.cons_append] at h
      cases h with
      | word htl =>
          obtain ⟨S₁, S₂, rfl, h1, h2⟩ := ih htl
          exact ⟨.word :: S₁, S₂, rfl, .word h1, h2⟩
      | code hf htl =>
          obtain ⟨S₁, S₂, rfl, h1, h2⟩ := ih htl
          exact ⟨.code _ :: S₁, S₂, rfl, .code hf h1, h2⟩

/-- `words vs` matches exactly the all-`word` layout. -/
theorem StkMatch.replicate_word {prog H} (vs : List U256) :
    StkMatch prog H (words vs) (List.replicate vs.length .word) := by
  induction vs with
  | nil => exact .nil
  | cons v vs ih =>
      rw [words_cons]; simp only [List.length_cons, List.replicate_succ]; exact .word ih

/-- Conversely, whatever `words vs` matches is the all-`word` layout. -/
theorem StkMatch.eq_replicate {prog H} {vs : List U256} {S : StkLayout}
    (h : StkMatch prog H (words vs) S) : S = List.replicate vs.length .word := by
  induction vs generalizing S with
  | nil => cases h; rfl
  | cons v vs ih =>
      rw [words_cons] at h
      cases h with
      | word htl => rw [List.length_cons, List.replicate_succ, ih htl]

/-- `(replicate k x ++ L).drop k = L` — dropping a replicated prefix. -/
theorem drop_replicate_append {α} (k : Nat) (x : α) (L : List α) :
    (List.replicate k x ++ L).drop k = L := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.cons_append, List.drop_succ_cons]; exact ih

/-! ### The step constraint and its validity -/

/-- The constraint one instruction `i` (with continuation `c`) imposes on the layout map, given its
entry layout `S`. Mirrors each `AStep` rule's stack effect and the EVM 1024 limit (1 slot of slack
for the label-address push). `dup`/`swap` transport whatever cells they touch — including return
addresses — while `dynJump` requires the top cell's return layout `R` to equal the layout below it. -/
def stepConstraint (prog : List Asm) (H : LayoutMap) : Asm → List Asm → StkLayout → Prop
  | .push _,      c, S => (.word :: S) ∈ H c ∧ S.length + 1 ≤ 1023
  -- Same stack effect as `push`; only the lowered width differs.
  | .pushImmutable _ _, c, S => (.word :: S) ∈ H c ∧ S.length + 1 ≤ 1023
  | .dup n,       c, S => ∃ sl, S[n.val]? = some sl ∧ (sl :: S) ∈ H c ∧ S.length + 1 ≤ 1023
  | .pushLabel l, c, S => (∃ c', findLabel l prog = some c' ∧ (.code c' :: S) ∈ H c)
      ∧ S.length + 1 ≤ 1023
  | .pop,         c, S => ∃ sl S', S = sl :: S' ∧ S' ∈ H c
  | .swap n,      c, S => ∃ a mid b rest, S = a :: (mid ++ b :: rest) ∧ mid.length = n.val
      ∧ (b :: (mid ++ a :: rest)) ∈ H c
  | .label _,     c, S => S ∈ H c
  | .op yop,      c, S => ∃ o, opTable yop = some o ∧ Operation.popArity o ≤ S.length ∧
      (List.replicate (Operation.pushArity o) Slot.word ++ S.drop (Operation.popArity o)).length ≤ 1023 ∧
      (List.replicate (Operation.pushArity o) Slot.word ++ S.drop (Operation.popArity o)) ∈ H c
  | .jump l,      _, S => ∃ c', findLabel l prog = some c' ∧ S ∈ H c'
  | .jumpi l,     c, S => ∃ S', S = .word :: S' ∧
      (∃ c', findLabel l prog = some c' ∧ S' ∈ H c') ∧ S' ∈ H c
  | .dynJump,     _, S => ∃ c' S', S = .code c' :: S' ∧ S' ∈ H c'

/-- A layout map is **valid** for `prog` when every reaching layout at every analysed position
satisfies its step constraint. -/
def ValidHeights (prog : List Asm) (H : LayoutMap) : Prop :=
  ∀ i c, (i :: c) <:+ prog → ∀ S, S ∈ H (i :: c) → stepConstraint prog H i c S

/-! ### The invariant and its preservation -/

/-- The reachable-configuration invariant: the stack fits the EVM limit, and matches the layout the
map assigns to the current code position. Return-address consistency is *not* a separate clause —
it is enforced position-locally by `stepConstraint` at `dynJump` and carried by `StkMatch`. -/
def Inv (prog : List Asm) (H : LayoutMap) (conf : AConf) : Prop :=
  conf.stk.length ≤ 1023 ∧ ∃ S, S ∈ H conf.code ∧ StkMatch prog H conf.stk S

/-- **The bound falls straight out of the invariant.** -/
theorem Inv.bound {prog H} {conf : AConf} (h : Inv prog H conf) : conf.stk.length ≤ 1023 :=
  h.1

/-- Two splittings of a list at equal-length prefixes agree. -/
theorem list_split_uniq {α} {l₁ l₂ : List α} {x y : α} {r₁ r₂ : List α}
    (h : l₁ ++ x :: r₁ = l₂ ++ y :: r₂) (hl : l₁.length = l₂.length) :
    l₁ = l₂ ∧ x = y ∧ r₁ = r₂ := by
  obtain ⟨h1, h2⟩ := List.append_inj h hl
  exact ⟨h1, (List.cons.injEq ..).mp h2⟩

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
/-- **Preservation.** Given a valid layout map, `Inv` is preserved by every `AStep`. `dup`/`swap`
transport whichever cells they touch (including return addresses — the `retRot` epilogue); `dynJump`
returns to exactly the layout its tagged return address demands. -/
theorem Inv.step {prog : List Asm} {H : LayoutMap} (hV : ValidHeights prog H)
    {a b : AConf} (hstep : AStep (model := model) prog a b) (hsuf : a.code <:+ prog)
    (hinv : Inv prog H a) : Inv prog H b := by
  obtain ⟨hfit, S, hHa, hm⟩ := hinv
  cases hstep with
  | @push v c σ yst =>
      obtain ⟨hHc, hlen⟩ := hV (.push v) c hsuf _ hHa
      have hL : σ.length = S.length := hm.length_eq
      refine ⟨?_, .word :: S, hHc, .word hm⟩
      show (AVal.word v :: σ).length ≤ 1023
      simp only [List.length_cons, hL]; omega
  | @pushImmutable key v c σ yst =>
      obtain ⟨hHc, hlen⟩ := hV (.pushImmutable key v) c hsuf _ hHa
      have hL : σ.length = S.length := hm.length_eq
      refine ⟨?_, .word :: S, hHc, .word hm⟩
      show (AVal.word v :: σ).length ≤ 1023
      simp only [List.length_cons, hL]; omega
  | @op yop args rets c σ yst yst' hstepOp =>
      obtain ⟨o, hop, _, hbnd, hHc⟩ := hV (.op yop) c hsuf _ hHa
      obtain ⟨hargs, hrets⟩ := builtin_arity hop hstepOp
      -- split S at the args, learn the args-prefix is all-word
      obtain ⟨Sargs, Sσ, rfl, hMargs, hMσ⟩ := hm.append_inv
      have hSargs : Sargs = List.replicate args.length .word := hMargs.eq_replicate
      have hdrop : (Sargs ++ Sσ).drop (Operation.popArity o) = Sσ := by
        rw [hSargs, ← hargs]; exact drop_replicate_append _ _ _
      have hL : σ.length = Sσ.length := hMσ.length_eq
      refine ⟨?_, _, hHc, ?_⟩
      · show (words rets ++ σ).length ≤ 1023
        rw [hdrop] at hbnd
        simp only [List.length_append, List.length_replicate, words_length] at hbnd ⊢; omega
      · rw [hdrop, ← hrets]
        exact (StkMatch.replicate_word rets).append hMσ
  | @dup n v τ ρ c yst hτ =>
      obtain ⟨sl, hidx, hHc, hlen⟩ := hV (.dup n) c hsuf _ hHa
      -- the cell at depth n is v's slot
      obtain ⟨Sτ, Sv, rfl, hMτ, hMv⟩ := hm.append_inv
      have hτlen : Sτ.length = n.val := by rw [← hMτ.length_eq, hτ]
      have hslv : (Sτ ++ Sv)[n.val]? = Sv[0]? := by
        rw [← hτlen, List.getElem?_append_right (Nat.le_refl _)]; simp
      rw [hslv] at hidx
      refine ⟨?_, ?_⟩
      · show (v :: (τ ++ v :: ρ)).length ≤ 1023
        have hL : (τ ++ v :: ρ).length = (Sτ ++ Sv).length := (hMτ.append hMv).length_eq
        simp only [List.length_cons, List.length_append] at hlen hL ⊢; omega
      · cases hMv with
        | @word vy _ Sρ hMρ =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hidx; subst hidx
            exact ⟨_, hHc, .word (hMτ.append (.word hMρ))⟩
        | @code ly c'y _ Sρ hfy hMρ =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hidx; subst hidx
            exact ⟨_, hHc, .code hfy (hMτ.append (.code hfy hMρ))⟩
  | @swap n x y τ ρ c yst hτ =>
      obtain ⟨sa, mid, sb, rest, hSeq, hmidlen, hHc⟩ := hV (.swap n) c hsuf _ hHa
      replace hfit : (x :: (τ ++ y :: ρ)).length ≤ 1023 := hfit
      refine ⟨?_, ?_⟩
      · show (y :: (τ ++ x :: ρ)).length ≤ 1023
        simp only [List.length_cons, List.length_append] at hfit ⊢; omega
      · cases hm with
        | @word vx _ Sinner hMtl =>
            obtain ⟨Sτ, Sy, rfl, hMτ, hMy⟩ := hMtl.append_inv
            rw [List.cons.injEq] at hSeq; obtain ⟨rfl, hrest⟩ := hSeq
            cases hMy with
            | @word vy _ Sρ hMρ =>
                obtain ⟨rfl, rfl, rfl⟩ := list_split_uniq hrest (by rw [hmidlen, ← hMτ.length_eq, hτ])
                exact ⟨_, hHc, StkMatch.word (hMτ.append (StkMatch.word hMρ))⟩
            | @code ly c'y _ Sρ hfy hMρ =>
                obtain ⟨rfl, rfl, rfl⟩ := list_split_uniq hrest (by rw [hmidlen, ← hMτ.length_eq, hτ])
                exact ⟨_, hHc, StkMatch.code hfy (hMτ.append (StkMatch.word hMρ))⟩
        | @code lx c'x _ Sinner hfx hMtl =>
            obtain ⟨Sτ, Sy, rfl, hMτ, hMy⟩ := hMtl.append_inv
            rw [List.cons.injEq] at hSeq; obtain ⟨rfl, hrest⟩ := hSeq
            cases hMy with
            | @word vy _ Sρ hMρ =>
                obtain ⟨rfl, rfl, rfl⟩ := list_split_uniq hrest (by rw [hmidlen, ← hMτ.length_eq, hτ])
                exact ⟨_, hHc, StkMatch.word (hMτ.append (StkMatch.code hfx hMρ))⟩
            | @code ly c'y _ Sρ hfy hMρ =>
                obtain ⟨rfl, rfl, rfl⟩ := list_split_uniq hrest (by rw [hmidlen, ← hMτ.length_eq, hτ])
                exact ⟨_, hHc, StkMatch.code hfy (hMτ.append (StkMatch.code hfx hMρ))⟩
  | @pop v σ c yst =>
      obtain ⟨sl, S', hSeq, hHc⟩ := hV .pop c hsuf _ hHa
      subst hSeq
      replace hfit : (v :: σ).length ≤ 1023 := hfit
      cases hm with
      | word hMtl =>
          refine ⟨?_, S', hHc, hMtl⟩
          show σ.length ≤ 1023
          simp only [List.length_cons] at hfit; omega
      | code hf hMtl =>
          refine ⟨?_, S', hHc, hMtl⟩
          show σ.length ≤ 1023
          simp only [List.length_cons] at hfit; omega
  | @label l c σ yst =>
      have hHc := hV (.label l) c hsuf _ hHa
      exact ⟨hfit, S, hHc, hm⟩
  | @jump l c c' σ yst hfind =>
      obtain ⟨c'', hf'', hH''⟩ := hV (.jump l) c hsuf _ hHa
      rw [hfind] at hf''; obtain rfl := Option.some.inj hf''
      exact ⟨hfit, S, hH'', hm⟩
  | @jumpiTaken l v c c' σ yst hv hfind =>
      obtain ⟨S', hSeq, ⟨c'', hf'', hH''⟩, _⟩ := hV (.jumpi l) c hsuf _ hHa
      subst hSeq
      replace hfit : (AVal.word v :: σ).length ≤ 1023 := hfit
      cases hm with
      | word hMtl =>
          rw [hfind] at hf''; obtain rfl := Option.some.inj hf''
          refine ⟨?_, S', hH'', hMtl⟩
          show σ.length ≤ 1023
          simp only [List.length_cons] at hfit; omega
  | @jumpiFall l v c σ yst hv =>
      obtain ⟨S', hSeq, _, hHc⟩ := hV (.jumpi l) c hsuf _ hHa
      subst hSeq
      replace hfit : (AVal.word v :: σ).length ≤ 1023 := hfit
      cases hm with
      | word hMtl =>
          refine ⟨?_, S', hHc, hMtl⟩
          show σ.length ≤ 1023
          simp only [List.length_cons] at hfit; omega
  | @pushLabel l c σ yst hdef =>
      obtain ⟨⟨c', hfind, hHc⟩, hlen⟩ := hV (.pushLabel l) c hsuf _ hHa
      have hL : σ.length = S.length := hm.length_eq
      refine ⟨?_, .code c' :: S, hHc, .code hfind hm⟩
      show (AVal.code l :: σ).length ≤ 1023
      simp only [List.length_cons, hL]; omega
  | @dynJump l c c' σ yst hfind =>
      obtain ⟨ct, S', hSeq, hHt⟩ := hV .dynJump c hsuf _ hHa
      -- S = .code ct :: S' with H ct = some S'; the match forces ct = findLabel l
      subst hSeq
      replace hfit : (AVal.code l :: σ).length ≤ 1023 := hfit
      cases hm with
      | code hf hMtl =>
          rw [hfind] at hf; obtain rfl := Option.some.inj hf
          refine ⟨?_, S', hHt, hMtl⟩
          show σ.length ≤ 1023
          simp only [List.length_cons] at hfit; omega

/-- **The invariant holds at every reachable configuration**, hence the stack stays within the
EVM limit throughout any Asm run — the hypothesis `astep_sim`/`asteps_sim` require. -/
theorem Inv.reach {prog : List Asm} {H : LayoutMap} (hV : ValidHeights prog H)
    {a b : AConf} (hsteps : ASteps (model := model) prog a b) (hsuf : a.code <:+ prog)
    (hinv : Inv prog H a) : Inv prog H b := by
  induction hsteps with
  | refl => exact hinv
  | head hstep _ ih => exact ih ((hstep.suffix hsuf)) (hinv.step hV hstep hsuf)

omit model in
/-- The entry configuration `⟨prog, [], yst⟩` satisfies the invariant, provided the empty layout is
among those the map assigns the whole program. -/
theorem Inv.entry {prog : List Asm} {H : LayoutMap} (h0 : [] ∈ H prog) (yst : EvmState) :
    Inv prog H ⟨prog, [], yst⟩ :=
  ⟨by simp, [], h0, .nil⟩

/-- **The run stack-bound**, in the exact shape the Phase-B lemmas consume: every configuration
reachable from the entry keeps its stack within the EVM limit. -/
theorem run_stack_bound {prog : List Asm} {H : LayoutMap}
    (hV : ValidHeights prog H) (h0 : [] ∈ H prog) (yst : EvmState) :
    ∀ mid, ASteps (model := model) prog ⟨prog, [], yst⟩ mid → mid.stk.length ≤ 1023 :=
  fun _ hsteps => (Inv.reach hV hsteps (List.suffix_refl _) (Inv.entry h0 yst)).bound

/-! ### A decidable verifier for `ValidHeights` (the verified checker)

The layout table `H` is proposed by an *untrusted* solver; soundness rests only on the verifier
below, so a wrong proposal is simply rejected. -/

/-- Decidable mirror of `stepConstraint`. -/
def stepOK (prog : List Asm) (H : LayoutMap) : Asm → List Asm → StkLayout → Bool
  | .push _,      c, S => decide ((.word :: S) ∈ H c) && decide (S.length + 1 ≤ 1023)
  | .pushImmutable _ _, c, S =>
      decide ((.word :: S) ∈ H c) && decide (S.length + 1 ≤ 1023)
  | .dup n,       c, S => match S[n.val]? with
      | some sl => decide ((sl :: S) ∈ H c) && decide (S.length + 1 ≤ 1023)
      | none => false
  | .pushLabel l, c, S =>
      (match findLabel l prog with
       | some c' => decide ((.code c' :: S) ∈ H c)
       | none => false) && decide (S.length + 1 ≤ 1023)
  | .pop,         c, S => match S with | _ :: S' => decide (S' ∈ H c) | [] => false
  | .swap n,      c, S => match S with
      | a :: t => match t.drop n.val with
                  | b :: rest => decide ((b :: (t.take n.val ++ a :: rest)) ∈ H c)
                  | [] => false
      | [] => false
  | .label _,     c, S => decide (S ∈ H c)
  | .op yop,      c, S => match opTable yop with
      | some o => decide (Operation.popArity o ≤ S.length)
          && decide ((List.replicate (Operation.pushArity o) Slot.word
              ++ S.drop (Operation.popArity o)).length ≤ 1023)
          && decide ((List.replicate (Operation.pushArity o) Slot.word
              ++ S.drop (Operation.popArity o)) ∈ H c)
      | none => false
  | .jump l,      _, S => match findLabel l prog with | some c' => decide (S ∈ H c') | none => false
  | .jumpi l,     c, S => match S with
      | .word :: S' => (match findLabel l prog with | some c' => decide (S' ∈ H c') | none => false)
          && decide (S' ∈ H c)
      | _ => false
  | .dynJump,     _, S => match S with | .code c' :: S' => decide (S' ∈ H c') | _ => false

omit model in
set_option linter.unusedTactic false in
/-- `stepOK` soundly implies `stepConstraint`. -/
theorem stepOK_sound {prog : List Asm} {H : LayoutMap} {i : Asm} {c : List Asm} {S : StkLayout}
    (h : stepOK prog H i c S = true) : stepConstraint prog H i c S := by
  cases i with
  | push v => simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at h; exact h
  | pushImmutable key v =>
      simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at h; exact h
  | dup n =>
      revert h; simp only [stepOK]; split
      · next sl he =>
          intro h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          exact ⟨sl, he, h.1, h.2⟩
      · intro h; simp at h
  | pushLabel l =>
      revert h; simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq]; split
      · next c' he =>
          intro h; exact ⟨⟨c', he, by simpa using h.1⟩, h.2⟩
      · intro h; simp at h
  | pop =>
      revert h; simp only [stepOK]; split
      · next s S' => intro h; exact ⟨s, S', rfl, by simpa using h⟩
      · intro h; simp at h
  | swap n =>
      revert h; simp only [stepOK]; split
      · next a t =>
          split
          · next b rest hd =>
              intro h
              refine ⟨a, t.take n.val, b, rest, ?_, ?_, by simpa using h⟩
              · rw [← hd, List.take_append_drop]
              · have : (t.drop n.val).length = t.length - n.val := by simp
                rw [hd] at this; simp only [List.length_cons] at this
                simp only [List.length_take]; omega
          · intro h; simp at h
      · intro h; simp at h
  | label l => simp only [stepOK, decide_eq_true_eq] at h; exact h
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
  | dynJump =>
      revert h; simp only [stepOK]; split
      · next c' S' => intro h; simp only [decide_eq_true_eq] at h; exact ⟨c', S', rfl, h⟩
      · intro h; simp at h

/-- The verifier: at every suffix position, *every* reaching layout satisfies the step constraint. -/
def checkValid (prog : List Asm) (H : LayoutMap) : Bool :=
  prog.tails.all (fun s => match s with
    | i :: c => (H (i :: c)).all (fun S => stepOK prog H i c S)
    | [] => true)

omit model in
/-- **Verifier soundness**: a passing `checkValid` yields `ValidHeights`. -/
theorem checkValid_sound {prog : List Asm} {H : LayoutMap} (h : checkValid prog H = true) :
    ValidHeights prog H := by
  intro i c hsuf S hHS
  rw [checkValid, List.all_eq_true] at h
  have hs := h (i :: c) ((List.mem_tails _ _).mpr hsuf)
  dsimp only at hs
  rw [List.all_eq_true] at hs
  exact stepOK_sound (hs S hHS)

/-! ### The untrusted layout solver + the `compile`-facing check

`infer` is a forward worklist that *proposes* a layout table (unverified — soundness rests only on
`checkValid`). At each analysed position it accumulates the *set* of reaching layouts and pushes
each new layout's successors. A recursion or stack-growing loop produces ever-deeper layouts, so the
worklist never drains within the fuel budget and the program is rejected — exactly the "no overflow"
contract. Positions are keyed by suffix length (unique among suffixes of a fixed program). -/

/-- Successor positions and their layouts for one instruction. `none` = malformed / reject. -/
def succsOf (prog : List Asm) : Asm → List Asm → StkLayout → Option (List (List Asm × StkLayout))
  | .push _,      c, S => some [(c, .word :: S)]
  | .pushImmutable _ _, c, S => some [(c, .word :: S)]
  | .dup n,       c, S => match S[n.val]? with | some sl => some [(c, sl :: S)] | none => none
  | .pushLabel l, c, S => match findLabel l prog with
                          | some tgt => some [(c, .code tgt :: S)] | none => none
  | .pop,         c, S => match S with | _ :: S' => some [(c, S')] | [] => none
  | .swap n,      c, S => match S with
      | a :: t => match t.drop n.val with
                  | b :: rest => some [(c, b :: (t.take n.val ++ a :: rest))]
                  | [] => none
      | [] => none
  | .label _,     c, S => some [(c, S)]
  | .op yop,      c, S => match opTable yop with
      | some o => if Operation.popArity o ≤ S.length then
            some [(c, List.replicate (Operation.pushArity o) Slot.word ++ S.drop (Operation.popArity o))]
          else none
      | none => none
  | .jump l,      _, S => match findLabel l prog with | some tgt => some [(tgt, S)] | none => none
  | .jumpi l,     c, S => match S with
      | .word :: S' => match findLabel l prog with
                       | some tgt => some [(tgt, S'), (c, S')] | none => none
      | _ => none
  | .dynJump,     _, S => match S with | .code tgt :: S' => some [(tgt, S')] | _ => none

/-- Forward worklist accumulating, per position, the *set* of reaching layouts. Fuel-bounded: a
program whose reachable layouts do not stabilise (recursion / stack-growing loop) exhausts the fuel
and is rejected (`none`). -/
partial def inferGo (prog : List Asm) :
    Nat → List (List Asm × StkLayout) → List (Nat × List StkLayout) →
      Option (List (Nat × List StkLayout))
  | 0, _, _ => none
  | _ + 1, [], acc => some acc
  | fuel + 1, (pos, S) :: wl, acc =>
    if 1023 < S.length then none else  -- a layout past the limit ⇒ overflow ⇒ reject (fast on recursion)
    let entry := acc.find? (fun p => p.1 == pos.length)
    let known := (entry.map (·.2)).getD []
    if known.contains S then inferGo prog fuel wl acc
    else
      let acc' := if entry.isSome
                  then acc.map (fun p => if p.1 == pos.length then (p.1, S :: p.2) else p)
                  else (pos.length, [S]) :: acc
      match pos with
      | [] => inferGo prog fuel wl acc'
      | i :: c => match succsOf prog i c S with
                  | some succs => inferGo prog fuel (succs ++ wl) acc'
                  | none => none

/-- Propose a layout table for `prog`, seeded with the empty entry layout. -/
def infer (prog : List Asm) : Option (List (Nat × List StkLayout)) :=
  inferGo prog 1000000 [(prog, [])] []

/-- Read a proposed table back as a layout map, keyed by suffix length. -/
def tableToMap (t : List (Nat × List StkLayout)) : LayoutMap :=
  fun s => ((t.find? (fun p => p.1 == s.length)).map (·.2)).getD []

/-- **The compile-facing stack-overflow check.** Propose a layout table and *verify* it. -/
def stackOK (prog : List Asm) : Bool :=
  match infer prog with
  | some t => checkValid prog (tableToMap t) && decide ([] ∈ tableToMap t prog)
  | none => false

omit model in
/-- **Soundness of the check**: passing `stackOK` exhibits a valid layout map whose whole-program
layout set contains the empty entry layout — the two facts `run_stack_bound` consumes. -/
theorem stackOK_sound {prog : List Asm} (h : stackOK prog = true) :
    ∃ H : LayoutMap, ValidHeights prog H ∧ [] ∈ H prog := by
  unfold stackOK at h
  cases he : infer prog with
  | none => rw [he] at h; simp at h
  | some t =>
      rw [he] at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨tableToMap t, checkValid_sound h.1, h.2⟩

end YulEvmCompiler
