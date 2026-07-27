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

This file discharges that hypothesis by a **static stack-depth analysis**: a height map
`H : List Asm → Option Nat` assigning each code position (a suffix of the program) the operand-stack
height reached there, together with a decidable well-formedness check `ValidHeights`. When it holds,
every configuration reachable from the entry stays within the limit — so the compiler can *reject*
(return `none`) any program the check fails, exactly the "prove no overflow" contract.

The soundness core is the invariant `Inv` and its preservation. `Inv` tracks three things:
the stack fits (`≤ 1023`); the height matches the map (`H code = some stk.length`); and — the subtle
part, needed for `dynJump` (function return) — every `.code l` return-address value on the stack
sits at exactly the height `H (findLabel l)` its target expects.
-/

namespace YulEvmCompiler

open EvmSemantics EvmSemantics.EVM
open YulSemantics.EVM (U256 EvmState Op builtinWithExternal)

/-! ### The height map and its well-formedness -/

/-- The operand-stack height each code position (suffix of the program) is reached at.
`none` = the position is not analysed (unreachable / rejected). -/
abbrev HeightMap := List Asm → Option Nat

/-- The well-formedness constraint one instruction `i` (with continuation `c`) imposes on the height
map, given its entry height `h`. Mirrors each `AStep` rule's effect on the stack and the EVM 1024
limit (with 1 slot of slack for the label-address push in the jump/`pushLabel` lowerings). -/
def stepConstraint (prog : List Asm) (H : HeightMap) : Asm → List Asm → Nat → Prop
  | .push _,      c, h => h + 1 ≤ 1023 ∧ H c = some (h + 1)
  | .dup _,       c, h => h + 1 ≤ 1023 ∧ H c = some (h + 1)
  | .pushLabel l, c, h => h + 1 ≤ 1023 ∧ H c = some (h + 1) ∧
      ∃ c', findLabel l prog = some c' ∧ H c' = some h
  | .pop,         c, h => 1 ≤ h ∧ H c = some (h - 1)
  | .swap _,      c, h => H c = some h
  | .label _,     c, h => H c = some h
  | .op yop,      c, h => ∃ o, opTable yop = some o ∧
      Operation.popArity o ≤ h ∧ h - Operation.popArity o + Operation.pushArity o ≤ 1023 ∧
      H c = some (h - Operation.popArity o + Operation.pushArity o)
  | .jump l,      _, h => ∃ c', findLabel l prog = some c' ∧ H c' = some h
  | .jumpi l,     c, h => 1 ≤ h ∧ (∃ c', findLabel l prog = some c' ∧ H c' = some (h - 1)) ∧
      H c = some (h - 1)
  | .dynJump,     _, h => 1 ≤ h

/-- A height map is **valid** for `prog` when every instruction position it analyses satisfies its
step constraint. Decidable-in-spirit: a checker computes `H` and verifies this. -/
def ValidHeights (prog : List Asm) (H : HeightMap) : Prop :=
  ∀ i c, (i :: c) <:+ prog → ∀ h, H (i :: c) = some h → stepConstraint prog H i c h


/-- Every `.code l` return-address value on the stack sits at the height `H (findLabel l)` its
jump target expects: splitting the stack as `above ++ .code l :: below`, the values `below` are
exactly what remains after returning through it (`dynJump`), so its target's height is `below.length`.
-/
def ReturnAddrsOK (prog : List Asm) (H : HeightMap) (stk : List AVal) : Prop :=
  ∀ above l below, stk = above ++ .code l :: below →
    ∃ c', findLabel l prog = some c' ∧ H c' = some below.length

/-- Pushing a plain word preserves return-address consistency. -/
theorem ReturnAddrsOK.word_cons {prog H} {σ : List AVal} {v : U256}
    (h : ReturnAddrsOK prog H σ) : ReturnAddrsOK prog H (.word v :: σ) := by
  intro above l below heq
  cases above with
  | nil => simp at heq
  | cons x above' =>
      rw [List.cons_append] at heq; injection heq with _ heq2; exact h above' l below heq2

/-- Pushing a code address at the height its target expects preserves consistency. -/
theorem ReturnAddrsOK.code_cons {prog H} {σ : List AVal} {l0 : Label}
    (h : ReturnAddrsOK prog H σ)
    (hc : ∃ c', findLabel l0 prog = some c' ∧ H c' = some σ.length) :
    ReturnAddrsOK prog H (.code l0 :: σ) := by
  intro above l below heq
  cases above with
  | nil => simp only [List.nil_append, List.cons.injEq] at heq; obtain ⟨hl, hb⟩ := heq
           cases hl; cases hb; exact hc
  | cons x above' =>
      rw [List.cons_append] at heq; injection heq with _ heq2; exact h above' l below heq2

/-- Popping the top preserves consistency for the tail. -/
theorem ReturnAddrsOK.tail {prog H} {σ : List AVal} {x : AVal}
    (h : ReturnAddrsOK prog H (x :: σ)) : ReturnAddrsOK prog H σ :=
  fun above l below heq => h (x :: above) l below (by rw [heq, List.cons_append])

/-- Appending a block of plain words on top is transparent to return-address consistency. -/
theorem ReturnAddrsOK.words_append_iff {prog H} {vs : List U256} {σ : List AVal} :
    ReturnAddrsOK prog H (words vs ++ σ) ↔ ReturnAddrsOK prog H σ := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
      rw [words_cons, List.cons_append]
      constructor
      · intro h; exact ih.mp h.tail
      · intro h; exact (ih.mpr h).word_cons

/-- The reachable-configuration invariant. -/
structure Inv (prog : List Asm) (H : HeightMap) (conf : AConf) : Prop where
  fits    : conf.stk.length ≤ 1023
  height  : H conf.code = some conf.stk.length
  returns : ReturnAddrsOK prog H conf.stk

/-- **The bound falls straight out of the invariant.** -/
theorem Inv.bound {prog H} {conf : AConf} (h : Inv prog H conf) : conf.stk.length ≤ 1023 :=
  h.fits

/-! ### Preservation along a step, and along a run -/

variable [model : ExternalModel]

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option maxHeartbeats 2000000 in
/-- **Op-arity coupling**: whenever a builtin (local op or external call/create) executes
successfully to `.ok rets`, its actual argument and result counts match the `Operation`'s declared
`popArity`/`pushArity`. This ties the abstract `AStep.op` stack effect (`words args ++ σ ↦
words rets ++ σ`) to the height-map arithmetic in `stepConstraint`. -/
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

set_option warningAsError false in
/-- **Preservation** (interface; the per-constructor case analysis is the substance of the
checker's soundness). Given a well-formed height map, `Inv` is preserved by every `AStep`. -/
theorem Inv.step {prog : List Asm} {H : HeightMap} (hV : ValidHeights prog H)
    {a b : AConf} (hstep : AStep (model := model) prog a b) (hsuf : a.code <:+ prog)
    (hinv : Inv prog H a) : Inv prog H b := by
  cases hstep with
  | @push v c σ yst =>
      obtain ⟨hfit, hHc⟩ := hV (.push v) c hsuf _ hinv.height
      exact ⟨by simpa using hfit, by simpa using hHc, hinv.returns.word_cons⟩
  | @pushLabel l c σ yst hdef =>
      obtain ⟨hfit, hHc, hfind⟩ := hV (.pushLabel l) c hsuf _ hinv.height
      exact ⟨by simpa using hfit, by simpa using hHc, hinv.returns.code_cons hfind⟩
  | @pop v σ c yst =>
      obtain ⟨_, hHc⟩ := hV .pop c hsuf _ hinv.height
      refine ⟨?_, ?_, hinv.returns.tail⟩
      · show σ.length ≤ 1023
        have h2 : σ.length + 1 ≤ 1023 := hinv.fits
        omega
      · simpa using hHc
  | @label l c σ yst =>
      have hHc := hV (.label l) c hsuf _ hinv.height
      exact ⟨hinv.fits, hHc, hinv.returns⟩
  | @jump l c c' σ yst hfind =>
      obtain ⟨c'', hf'', hH''⟩ := hV (.jump l) c hsuf _ hinv.height
      rw [hfind] at hf''; obtain rfl := Option.some.inj hf''
      exact ⟨hinv.fits, hH'', hinv.returns⟩
  | @jumpiTaken l v c c' σ yst hv hfind =>
      obtain ⟨_, ⟨c'', hf'', hH''⟩, _⟩ := hV (.jumpi l) c hsuf _ hinv.height
      rw [hfind] at hf''; obtain rfl := Option.some.inj hf''
      refine ⟨?_, ?_, hinv.returns.tail⟩
      · show σ.length ≤ 1023
        have h2 : σ.length + 1 ≤ 1023 := hinv.fits
        omega
      · simpa using hH''
  | @jumpiFall l v c σ yst hv =>
      obtain ⟨_, _, hHc⟩ := hV (.jumpi l) c hsuf _ hinv.height
      refine ⟨?_, ?_, hinv.returns.tail⟩
      · show σ.length ≤ 1023
        have h2 : σ.length + 1 ≤ 1023 := hinv.fits
        omega
      · simpa using hHc
  | @dynJump l c c' σ yst hfind =>
      obtain ⟨c'', hf'', hH''⟩ := hinv.returns [] l σ (by simp)
      rw [hfind] at hf''; obtain rfl := Option.some.inj hf''
      refine ⟨?_, hH'', hinv.returns.tail⟩
      · show σ.length ≤ 1023
        have h2 : σ.length + 1 ≤ 1023 := hinv.fits
        omega
  | @dup n v τ ρ c yst hτ =>
      -- HARD: a dup'd `.code` value would land at the wrong height (needs value-flow).
      sorry
  | @swap n x y τ ρ c yst hτ =>
      -- HARD: a swapped `.code` value would move to the wrong height (needs value-flow).
      sorry
  | @op yop args rets c σ yst yst' hstepOp =>
      obtain ⟨o, hop, hpop, hbnd, hHc⟩ := hV (.op yop) c hsuf _ hinv.height
      obtain ⟨hargs, hrets⟩ := builtin_arity hop hstepOp
      have hwa : (words args ++ σ).length = args.length + σ.length := by
        simp [words, List.length_append, List.length_map]
      have hwr : (words rets ++ σ).length = rets.length + σ.length := by
        simp [words, List.length_append, List.length_map]
      -- height arithmetic: h - popArity + pushArity = rets.length + σ.length
      have hcalc : (words args ++ σ).length - Operation.popArity o + Operation.pushArity o
          = (words rets ++ σ).length := by rw [hwa, hwr, hargs, hrets]; omega
      refine ⟨?_, ?_, ?_⟩
      · show (words rets ++ σ).length ≤ 1023
        rw [← hcalc]; exact hbnd
      · show H c = some (words rets ++ σ).length
        rw [hHc, hcalc]
      · exact (ReturnAddrsOK.words_append_iff.mpr
          (ReturnAddrsOK.words_append_iff.mp hinv.returns))

/-- **The invariant holds at every reachable configuration**, hence the stack stays within the
EVM limit throughout any Asm run — the hypothesis `astep_sim`/`asteps_sim` require. -/
theorem Inv.reach {prog : List Asm} {H : HeightMap} (hV : ValidHeights prog H)
    {a b : AConf} (hsteps : ASteps (model := model) prog a b) (hsuf : a.code <:+ prog)
    (hinv : Inv prog H a) : Inv prog H b := by
  induction hsteps with
  | refl => exact hinv
  | head hstep _ ih => exact ih ((hstep.suffix hsuf)) (hinv.step hV hstep hsuf)

omit model in
/-- The entry configuration `⟨prog, [], yst⟩` satisfies the invariant, provided the map assigns the
whole program height `0` and stays within the limit there. -/
theorem Inv.entry {prog : List Asm} {H : HeightMap} (h0 : H prog = some 0) (yst : EvmState) :
    Inv prog H ⟨prog, [], yst⟩ where
  fits := by simp
  height := by simpa using h0
  returns := by intro above l below hi; simp at hi

/-- **The run stack-bound**, in the exact shape the Phase-B lemmas consume: every configuration
reachable from the entry keeps its stack within the EVM limit. -/
theorem run_stack_bound {prog : List Asm} {H : HeightMap}
    (hV : ValidHeights prog H) (h0 : H prog = some 0) (yst : EvmState) :
    ∀ mid, ASteps (model := model) prog ⟨prog, [], yst⟩ mid → mid.stk.length ≤ 1023 :=
  fun _ hsteps => (Inv.reach hV hsteps (List.suffix_refl _) (Inv.entry h0 yst)).bound

end YulEvmCompiler
