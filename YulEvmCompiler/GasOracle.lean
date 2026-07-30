import YulEvmCompiler.AsmSem
import YulEvmCompiler.OpTable
set_option warningAsError true
/-!
# YulEvmCompiler.GasOracle

**Why `gas()` costs an assumption, and exactly which assumptions can pay.**

Supporting `call(gas(), …)` (see `Asm.gasCall`) needs phase B to answer a
source derivation that already read *some* word `g` from the open-world
`gas()` oracle with a target run whose `GAS` opcode produced its own word.
That is sound only if nothing observable distinguishes the two.

This module records what is and is not sufficient, as machine-checked facts
rather than prose.

## The natural side condition, and why it must live in the oracle

The honest side condition is not "the callee ignores gas" — every opcode
costs gas, so a callee handed too little always behaves differently. It is
the *threshold* form:

> the callee's behaviour is stable above some minimum `G`, **and** the amount
> forwarded to it is at least that `G`.

That is the same shape as the guarantee `compile_correct` already gives —
"nothing is claimed for runs that start with less than `b` gas" — applied one
level down, to the gas handed across a call boundary rather than the gas
handed to the whole program. `GasThreshold` below is the first half.

The second half has to be a constraint on what `gas()` may *report*, and it
cannot be bolted onto our own fused instruction:

* `AStep.gasCall` is ours, so its rule *could* quantify the allowance as
  "some `g ≥ G`". But the peephole must derive that fused step from the two
  genuine source steps `op gas ; op call`, and the pinned oracle
  (`builtinWithExternal … .gas [] st r ↔ ∃ g, r = .ok [g] st`) lets the first
  of those report **anything**, including `0`.
  `thresholdCalls_source_step` / `thresholdCalls_no_admissible_allowance`
  exhibit a threshold-respecting environment together with a real two-step
  source derivation that **no** at-or-above-threshold allowance reproduces:
  the fused rule would have no matching step and the peephole simulation
  would be false, not merely unproved.
* So the constraint has to sit in the source `gas()` itself — i.e. in
  yul-semantics (powdr-labs/yul-semantics#41's `ExternalGas`), where it
  removes those derivations from the dialect instead of leaving them
  unmatched.

## A second, independent obstacle

Phase B's gas bookkeeping is additive: `astep_sim` proves
`∃ bnd, ∀ s, bnd ≤ s.gasAvailable → … ∧ s.gasAvailable - bnd ≤ s'.gasAvailable`,
and `bnd` is committed before the machine state — hence before the forwarded
allowance — is known. Under EIP-150 a gas-forwarding call hands the callee
all but a 64th, so a callee that spends its allowance leaves the caller about
`s.gasAvailable / 64`, and `no_additive_bound_under_eip150` shows no fixed
`bnd` covers that loss. This is a limitation of the *shape* of the phase-B
statement, not of any environment hypothesis. The fix is to generalise the
bookkeeping from "subtract `bnd`" to a monotone, unbounded gas transformer
(`g ↦ (g - c) / 64` at a gas call, `g ↦ g - c` elsewhere) — a class closed
under composition, and one EIP-150 discharges directly.
-/

namespace YulEvmCompiler

open YulSemantics.EVM (U256 EvmState Op CallKind CallRequest CallResponse
  CallWorld ExternalCalls ExternalCreates builtinWithExternal)

/-! ### The two hypothesis shapes -/

/-- **Flat gas-insensitivity**: the environment's admitted responses do not
depend on the forwarded allowance at all.

This is what the fused gas-forwarding call would need, given the pinned,
totally unconstrained `gas()` oracle — the source may report `0`, so anything
sufficient must identify the response at allowance `0` with the response at a
large one. It is also **false of real callees**: every opcode costs gas, so a
callee handed too little always behaves differently. Recorded here only as the
reference point the threshold hypothesis below improves on. -/
def GasInsensitive (external : ExternalCalls) : Prop :=
  ∀ (req : CallRequest) (g : U256) (st : EvmState) (resp : CallResponse),
    external.Call req st resp → external.Call { req with gas := g } st resp


/-- For every call request there is a *threshold* above which the
environment's admitted responses no longer depend on the forwarded
allowance. Unlike flat `GasInsensitive` this is true of real contracts: once
a callee has enough gas to finish, the surplus is refunded and changes
nothing.

The threshold may depend on everything about the request *except* its gas
field — which is exactly the data phase B holds before it sees a machine
state, so this half has no ordering problem of its own. -/
def GasThreshold (external : ExternalCalls) : Prop :=
  ∀ (kind : CallKind) (target value : U256) (input : List UInt8) (st : EvmState),
    ∃ G : Nat, ∀ (g₁ g₂ : U256) (resp : CallResponse),
      G ≤ g₁.toNat → G ≤ g₂.toNat →
      external.Call ⟨kind, g₁, target, value, input⟩ st resp →
      external.Call ⟨kind, g₂, target, value, input⟩ st resp

/-- Flat gas-insensitivity is the `G = 0` case: strictly stronger, as
`thresholdCalls` witnesses. -/
theorem GasInsensitive.gasThreshold {external : ExternalCalls}
    (h : GasInsensitive external) : GasThreshold external :=
  fun _ _ _ _ _ => ⟨0, fun _ g₂ _ _ _ hc => h _ g₂ _ _ hc⟩

/-! ### Obstacle 1: a threshold cannot bridge an unconstrained oracle

The witness environment succeeds exactly when forwarded at least `1000` gas —
a caricature of a callee that runs out of gas, and about as well behaved as a
gas-dependent environment gets: constant above its threshold, and independent
of the caller's state. -/

/-- Succeeds iff forwarded at least `1000` gas; the post-world is the
pre-call world either way. -/
def thresholdCalls : ExternalCalls where
  Call := fun req st resp =>
    (1000 ≤ req.gas.toNat ↔ resp.success = true)
      ∧ resp.returndata = []
      ∧ resp.world = CallWorld.ofState st

theorem thresholdCalls_gasThreshold : GasThreshold thresholdCalls := by
  intro kind target value input st
  refine ⟨1000, ?_⟩
  rintro g₁ g₂ resp h₁ h₂ ⟨hiff, hr, hw⟩
  exact ⟨⟨fun _ => hiff.mp h₁, fun _ => h₂⟩, hr, hw⟩

/-- The six non-gas arguments of the witness `call`. A zero call value keeps
the static-context gate out of the picture. -/
def gasWitnessArgs : List U256 := [0, 0, 0, 0, 0, 0]

/-- The failure response the environment admits below its threshold. -/
def gasWitnessFail : CallResponse :=
  ⟨false, [], CallWorld.ofState EvmState.init⟩

/-- The source-side post-state of the failing call. -/
def gasWitnessPost : EvmState :=
  YulSemantics.EVM.finishCall .call EvmState.init gasWitnessFail 0 0 0 0

/-- **A real source derivation at a below-threshold allowance.** The pinned
`gas()` oracle may report `0`; the environment then reports failure and the
call pushes `0`. Nothing in yul-semantics rules this run out. -/
theorem thresholdCalls_source_step :
    builtinWithExternal thresholdCalls ExternalCreates.none .call
      ((0 : U256) :: gasWitnessArgs) EvmState.init
      (.ok [(0 : U256)] gasWitnessPost) := by
  refine ⟨gasWitnessFail, ⟨?_, rfl, rfl⟩, rfl⟩
  simp [gasWitnessFail]

/-- **…and no at-or-above-threshold allowance reproduces it.** Every
allowance the threshold hypothesis speaks about forces success, hence the
flag `1`, never the `0` the source derivation committed to.

This is the crux of design option (i): a fused `AStep.gasCall` rule that
quantified its allowance as "some `g ≥ G`" would have *no* step matching the
`op gas ; op call` pair above, so the peephole's forward simulation
(`Peephole.step_sim`) would be **false**. Constraining the allowance inside
our own instruction cannot work; the constraint has to remove the offending
`gas()` reading at its source. -/
theorem thresholdCalls_no_admissible_allowance :
    ¬ ∃ g : U256, 1000 ≤ g.toNat ∧
      builtinWithExternal thresholdCalls ExternalCreates.none .call
        (g :: gasWitnessArgs) EvmState.init (.ok [(0 : U256)] gasWitnessPost) := by
  rintro ⟨g, hg, resp, ⟨hiff, -, -⟩, heq⟩
  have hsucc : resp.success = true := hiff.mp hg
  have hflag : resp.flag = (1 : U256) := by
    simp [YulSemantics.EVM.CallResponse.flag, hsucc]
  injection heq with hlist hst
  rw [hflag] at hlist
  simp at hlist

/-- The two source `AStep`s the peephole must fuse, in the witness model:
`op gas` reads `0`, then `op call` consumes it and the environment reports
failure. Both are instances of `AStep.op`, i.e. of the pinned source
relation — the derivation the fused rule would have to match. -/
theorem thresholdCalls_source_asteps
    {prog c : List Asm} {σ : List AVal}
    [model : ExternalModel] (hcalls : model.calls = thresholdCalls)
    (hcreates : model.creates = ExternalCreates.none) :
    ASteps (model := model) prog
      ⟨.op .gas :: .op .call :: c, words gasWitnessArgs ++ σ, EvmState.init⟩
      ⟨c, words [(0 : U256)] ++ σ, gasWitnessPost⟩ := by
  refine .head (b := ⟨.op .call :: c, words ((0 : U256) :: gasWitnessArgs) ++ σ,
    EvmState.init⟩) ?_ (.single ?_)
  · have h : builtinWithExternal model.calls model.creates .gas [] EvmState.init
        (.ok [(0 : U256)] EvmState.init) := ⟨0, rfl⟩
    simpa using AStep.op (model := model) (prog := prog) (yop := .gas)
      (args := []) (rets := [(0 : U256)]) (c := .op .call :: c)
      (σ := words gasWitnessArgs ++ σ) h
  · have h : builtinWithExternal model.calls model.creates .call
        ((0 : U256) :: gasWitnessArgs) EvmState.init
        (.ok [(0 : U256)] gasWitnessPost) := by
      rw [hcalls, hcreates]; exact thresholdCalls_source_step
    simpa [words_append] using AStep.op (model := model) (prog := prog) (yop := .call)
      (args := (0 : U256) :: gasWitnessArgs) (rets := [(0 : U256)]) (c := c) (σ := σ) h

/-! ### Obstacle 2: EIP-150 defeats an additive gas bound -/

/-- **No fixed `bnd` bounds the loss across a gas-forwarding call.** Under
EIP-150 a call forwards all but a 64th of what the caller holds, so a callee
that spends its allowance leaves the caller with about `g / 64`. Phase B's
conclusion `s.gasAvailable - bnd ≤ s'.gasAvailable` demands a *fixed* `bnd`
covering that loss for every sufficiently funded `s`, and no such `bnd`
exists.

So even with obstacle 1 solved, the fused step cannot be stated in the
current additive phase-B shape without additionally assuming the realizing
trace's cost is independent of the allowance — which is false for a callee
that spends what it is given. Generalising the bookkeeping to a monotone
unbounded gas transformer removes the need for that assumption entirely:
`g ↦ (g - c) / 64` is discharged by EIP-150 itself. -/
theorem no_additive_bound_under_eip150 :
    ¬ ∃ bnd : Nat, ∀ g : Nat, bnd ≤ g → g - bnd ≤ g / 64 := by
  rintro ⟨bnd, h⟩
  have hg := h (64 * bnd + 64) (by omega)
  have hdiv : (64 * bnd + 64) / 64 = bnd + 1 := by omega
  omega

end YulEvmCompiler
