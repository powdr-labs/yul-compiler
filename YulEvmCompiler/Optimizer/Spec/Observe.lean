import YulEvmCompiler.Optimizer.Spec.Backend
set_option warningAsError true
/-!
# YulEvmCompiler.Optimizer.Spec.Observe

The **observational tier** of the optimizer specification: a second, weaker
pass contract phrased in terms of what an external caller or the enclosing
transaction can actually see.

## Why a second tier

`Optimizer.Pass` demands `EquivBlock`: pointwise big-step equivalence — the
*same* final variable environment and the *same* raw machine state, from every
configuration. That is the right contract for local rewrites, and it composes
with the backend for free, but it provably cannot express whole classes of
optimizations this project wants:

* **dead-binding removal** changes the final `VEnv`;
* **scratch-memory reuse** (CSE buffers, reordered `mstore`s to dead regions)
  changes raw memory that nothing ever reads again;
* **dead stores before a `revert`** change the raw halt state even though the
  EVM discards the frame's effects.

`ObsEquivBlock` keeps exactly what is observable at the frame boundary — the
halt/outcome discipline, returndata, storage, transient storage, logs,
self-destructs, and the world/environment projections — after applying the
frame-boundary commit/rollback (`committedState`), and quantifies away memory,
the `msize` word count, and the final variable environment.

Because both sides are still quantified over **every** external-call and
creation oracle, any divergence a pass introduces in the *inputs* of an
external call is caught: an adversarial oracle propagates it into storage and
the final observables. Event-trace equivalence therefore does not need to be
stated separately for the passes this contract is designed to admit.

## Relation to the audited surface

`Pass` (the `EquivBlock` tier) remains the production contract and the one
pinned by `SpecClosure`. This module is additive: it defines the weaker
contract, embeds the strong one into it (`ObsEquivBlock.ofEquiv` — so every
existing pass is also observationally sound), and restates the backend payoff
(`ObsPass.optimize_then_compile_correct`): compiled optimized code reaches a
final state that *matches a Yul state observationally equal* to the source
program's. Admitting an `ObsPass` in front of the backend is a deliberate,
human-reviewed weakening of the headline guarantee from state equality to
observable equality; the theorem below is stated so that a maintainer can move
it into the audited roots when the first observational pass lands.
-/

namespace YulEvmCompiler.Optimizer

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM
open YulSemantics (Outcome VEnv Run Block EquivBlock)

/-! ## Observables -/

/-- The caller/transaction-observable projection of a final machine state:
every `EvmState` field except byte memory and the active-word count (`msize`),
which are frame-local scratch. The final `VEnv` is likewise not recorded —
variable environments die with the frame. -/
structure Obs where
  /-- Persistent storage. -/
  storage : U256 → U256
  /-- Transient storage (survives to the end of the transaction). -/
  transient : U256 → U256
  /-- Frame context and global world projections (balances, code, nonces). -/
  env : ExecEnv
  /-- The return-data buffer. -/
  returndata : List UInt8
  /-- Emitted logs, in order. -/
  logs : List YulSemantics.EVM.LogEntry
  /-- The self-destruct schedule, in order. -/
  selfdestructs : List (U256 × Bool)
  /-- The halt marker and its payload. -/
  halted : Option (YulSemantics.EVM.HaltKind × List UInt8)

/-- Project a machine state onto its observables. -/
def observables (st : EvmState) : Obs :=
  { storage := st.storage, transient := st.transient, env := st.env,
    returndata := st.returndata, logs := st.logs,
    selfdestructs := st.selfdestructs, halted := st.halted }

/-- What a whole run shows the outside world: the observables of the final
state after the frame-boundary commit/rollback relative to the initial state.
A reverting run therefore observes the rolled-back state, exactly as the EVM
presents it to a caller. -/
def runObservables (st0 st' : EvmState) : Obs :=
  observables (committedState st0 st')

/-! ## Observational block equivalence -/

variable {calls : ExternalCalls} {creates : ExternalCreates}

/-- Every run of `b₁` is matched by a run of `b₂` from the same initial state,
with the same control outcome and the same run observables. The final variable
environment and the raw (memory-carrying) final state may differ. -/
def ObsRefines (calls : ExternalCalls) (creates : ExternalCreates)
    (b₁ b₂ : Block Op) : Prop :=
  ∀ st0 V' st' o, Run (evmWithExternal calls creates) b₁ st0 V' st' o →
    ∃ V'' st'', Run (evmWithExternal calls creates) b₂ st0 V'' st'' o ∧
      runObservables st0 st'' = runObservables st0 st'

/-- Observational equivalence of top-level blocks: mutual observational
refinement. Strictly weaker than `EquivBlock` (which also pins raw memory and
the final variable environment), yet strong enough that no external observer —
under any call/creation oracle — can distinguish the two programs. -/
def ObsEquivBlock (calls : ExternalCalls) (creates : ExternalCreates)
    (b₁ b₂ : Block Op) : Prop :=
  ObsRefines calls creates b₁ b₂ ∧ ObsRefines calls creates b₂ b₁

namespace ObsRefines

theorem refl (b : Block Op) : ObsRefines calls creates b b :=
  fun _ V' st' _ hrun => ⟨V', st', hrun, rfl⟩

theorem trans {b₁ b₂ b₃ : Block Op} (h₁ : ObsRefines calls creates b₁ b₂)
    (h₂ : ObsRefines calls creates b₂ b₃) : ObsRefines calls creates b₁ b₃ := by
  intro st0 V' st' o hrun
  obtain ⟨V₂, st₂, hrun₂, hobs₂⟩ := h₁ st0 V' st' o hrun
  obtain ⟨V₃, st₃, hrun₃, hobs₃⟩ := h₂ st0 V₂ st₂ o hrun₂
  exact ⟨V₃, st₃, hrun₃, hobs₃.trans hobs₂⟩

end ObsRefines

namespace ObsEquivBlock

theorem refl (b : Block Op) : ObsEquivBlock calls creates b b :=
  ⟨ObsRefines.refl b, ObsRefines.refl b⟩

theorem symm {b₁ b₂ : Block Op} (h : ObsEquivBlock calls creates b₁ b₂) :
    ObsEquivBlock calls creates b₂ b₁ := ⟨h.2, h.1⟩

theorem trans {b₁ b₂ b₃ : Block Op} (h₁ : ObsEquivBlock calls creates b₁ b₂)
    (h₂ : ObsEquivBlock calls creates b₂ b₃) : ObsEquivBlock calls creates b₁ b₃ :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

/-- **The strong tier embeds.** Pointwise equivalence transports the very same
run, so the observables agree definitionally. Every `Optimizer.Pass` is in
particular observationally sound. -/
theorem ofEquiv {b₁ b₂ : Block Op}
    (h : EquivBlock (evmWithExternal calls creates) b₁ b₂) :
    ObsEquivBlock calls creates b₁ b₂ :=
  ⟨fun _ V' st' _ hrun => ⟨V', st', h.run_iff.mp hrun, rfl⟩,
   fun _ V' st' _ hrun => ⟨V', st', h.run_iff.mpr hrun, rfl⟩⟩

end ObsEquivBlock

/-! ## The observational pass contract -/

/-- **Observational soundness** of a source-to-source transform: for every
external oracle, input and output are observationally equivalent. This is the
weaker of the two admissible contracts; prefer `Optimizer.Sound` when a pass
preserves raw state, and use this one only for passes that legitimately change
memory, dead bindings, or other unobservable data. -/
def ObsSound (run : Block Op → Block Op) : Prop :=
  ∀ (calls : ExternalCalls) (creates : ExternalCreates) (b : Block Op),
    ObsEquivBlock calls creates b (run b)

/-- A **verified observational pass**: a total Yul→Yul transformation bundled
with a proof of `ObsSound`. Note the transform is a single function, uniform in
the external oracles — only its soundness proof quantifies over them. -/
structure ObsPass where
  /-- The source-to-source transformation on top-level blocks. -/
  run : Block Op → Block Op
  /-- Proof obligation: the transformation is observationally sound. -/
  sound : ObsSound run

namespace ObsPass

/-- The do-nothing observational pass. -/
def id : ObsPass where
  run := fun b => b
  sound := fun _ _ b => ObsEquivBlock.refl b

@[simp] theorem id_run (b : Block Op) : (id).run b = b := rfl

/-- Composition (`Q` first, then `P`), sound by transitivity. -/
def comp (P Q : ObsPass) : ObsPass where
  run := fun b => P.run (Q.run b)
  sound := fun calls creates b =>
    (Q.sound calls creates b).trans (P.sound calls creates (Q.run b))

@[simp] theorem comp_run (P Q : ObsPass) (b : Block Op) :
    (comp P Q).run b = P.run (Q.run b) := rfl

/-- Downgrade a strong pass (given as an oracle-uniform transform with an
`EquivBlock` soundness family) to an observational pass. -/
def ofSound (run : Block Op → Block Op)
    (sound : ∀ (calls : ExternalCalls) (creates : ExternalCreates),
      Optimizer.Sound (evmWithExternal calls creates) run) : ObsPass where
  run := run
  sound := fun calls creates b => ObsEquivBlock.ofEquiv (sound calls creates b)

/-! ## The backend payoff, observationally -/

open YulEvmCompiler

/-- **An observationally sound pass composes with the verified backend.** If
the Yul semantics runs the *original* `prog` to `yst'` with outcome `o`, then
the optimized program has its own run to some `yst₂` with the **same run
observables**, and the bytecode compiled from the optimized program correctly
simulates *that* run: from every matching initial state with enough gas it
reaches a final EVM state matching `yst₂` with the usual halt discipline.

Chaining the two equalities: the deployed bytecode's visible behavior —
committed storage, transient storage, logs, self-destructs, returndata, halt
payload, and world projections — is exactly the source program's. Raw final
memory is *not* pinned to the source's; that is the deliberate weakening this
tier exists to express. -/
theorem optimize_then_compile_correct
    [model : ExternalModel] (hexternal : ExternalsRealized model)
    (P : ObsPass) {prog : Block Op} {is : List Instr}
    (hcomp : compile (P.run prog) = some is)
    {yst0 : EvmState} {V' : VEnv (evmWithExternal model.calls model.creates)}
    {yst' : EvmState} {o : Outcome}
    (hrun : Run (evmWithExternal model.calls model.creates) prog yst0 V' yst' o) :
    ∃ V₂ yst₂,
      Run (evmWithExternal model.calls model.creates) (P.run prog) yst0 V₂ yst₂ o ∧
      runObservables yst0 yst₂ = runObservables yst0 yst' ∧
      ∃ b : Nat, ∀ s0 : State,
        FrameOK (assemble is) s0 → StateMatch yst0 s0 →
        s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
        ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst₂ s' ∧
          ((o = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
           (o = .halt ∧ HaltedMatch yst₂ s')) := by
  obtain ⟨V₂, yst₂, hrun₂, hobs⟩ :=
    (P.sound model.calls model.creates prog).1 yst0 V' yst' o hrun
  exact ⟨V₂, yst₂, hrun₂, hobs, compile_correct hexternal hcomp hrun₂⟩

end ObsPass

end YulEvmCompiler.Optimizer
