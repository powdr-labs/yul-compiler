import YulEvmCompiler.Correctness
import EvmSemantics.Crypto.Sha256
set_option warningAsError true
/-!
# The SHA-256 challenge statement

One `Prop` that any candidate EVM bytecode — ours or a challenger's — must
satisfy to count as a verified replacement for the `0x02` precompile
(EIP-8200 / EIP-7666 "EVMification"): `Challenge.Sha256.Correct`.

## What the spec side is

Not ours. `EvmSemantics.Crypto.Sha256.hash` is the function the *precompile
itself* computes in the pinned `evm-semantics` dependency — see
`EvmSemantics.EVM.Precompile.runSha256`, which is literally
`.success (Crypto.Sha256.hash input) cost`. So "this bytecode is equivalent
to the SHA-256 precompile" is a statement *inside* the trusted semantics,
and the equality is against the same function the reference EVM already
uses. Nothing about the specification is this repository's to get wrong; it
is FIPS 180-4 as pinned and vector-checked by `evm-semantics`
(`tests/Sha256Test.lean` covers the published §B.1–B.3 vectors).

## What a submission must prove

`Correct code`: for every calldata, given enough gas, a frame executing
`code` halts by *returning* exactly the 32 digest bytes. Notably it does
**not** talk about our bytecode, our Yul, our memory layout, or our gas —
two implementations that both satisfy `Correct` are automatically
interchangeable on the interface a caller can observe. That is what makes
this a challenge statement rather than a description of one implementation:
equivalence to the spec, not equivalence to the incumbent's code.

`CorrectWithSchedule code schedule` strengthens it with a *proven* gas
bound — the thing an EIP actually needs, and the top tier of the challenge
leaderboard.

## Scope, stated honestly

* The frame is the canonical one (`frame` below): fresh memory, empty
  storage, zero balance, zero call value, depth 0, Osaka. A precompile call
  frame is always fresh-memory, and `0x02` has no storage of its own, so
  this is the situation that actually arises — but a submission that reads
  `SLOAD`/`CALLVALUE`/`CALLER` is only constrained here at those values.
  Generalizing the frame is `CorrectInAnyFrame` below.
* `deployAddress` is *not* `0x02`. In the pinned Osaka semantics `0x02` is
  still a precompile (`Precompile.isPrecompile … = true`), so a frame there
  never executes bytecode at all — flipping that bit is exactly what
  EIP-8200 activation does. Until the pinned semantics has a post-8200
  fork, the challenge runs the candidate at a non-precompile address, which
  is what the deployed code will be doing after activation.
-/

namespace Challenge.Sha256

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics (Block Run VEnv Outcome)
open YulSemantics.EVM (EvmState Op evmWithExternal)
open YulEvmCompiler

/-! ## The specification -/

/-- The canonical SHA-256: the function the `0x02` precompile computes in the
pinned semantics (`Precompile.runSha256`). -/
def spec (input : ByteArray) : ByteArray := Crypto.Sha256.hash input

/-- The spec at the byte-list view yul-semantics uses for calldata and
return data. -/
def digestOf (calldata : List UInt8) : List UInt8 :=
  (spec (mkCode calldata)).toList

/-! ## The frame a candidate is judged in -/

/-- Where the challenge deploys a candidate. Any non-precompile address will
do; `0x8200` names the EIP. -/
def deployAddress : AccountAddress := AccountAddress.ofNat 0x8200

/-- The canonical call frame: `code` deployed at `deployAddress`, `calldata`
as input, `gas` available, and everything else at its zero — fresh memory,
no storage, no transient storage, no balance, no call value, depth 0, Osaka.

Nothing here is a modeling choice about SHA-256; it is the frame a
`CALL` into a freshly deployed, storage-free account produces. -/
def frame (code calldata : ByteArray) (gas : Nat) : EVM.State :=
  let account : Account := { Account.empty with code }
  let accounts := AccountMap.empty.set deployAddress account
  let env : ExecutionEnv := {
    (default : ExecutionEnv) with
    address := deployAddress
    codeAddr := deployAddress
    origin := AccountAddress.ofNat 0
    caller := AccountAddress.ofNat 0
    weiValue := 0
    calldata
    code
    gasPrice := 0
    depth := 0
    permitStateMutation := true
    blobVersionedHashes := #[]
    fork := .Osaka
  }
  { (default : EVM.State) with
    pc := 0
    stack := []
    execLength := 0
    halt := .Running
    callStack := []
    gasAvailable := gas
    activeWords := 0
    memory := .empty
    returnData := .empty
    hReturn := .empty
    accountMap := accounts
    substate := { Substate.empty with originalAccountMap := accounts }
    executionEnv := env }

/-! ## The challenge -/

/-- **The challenge.** `code` computes SHA-256 the way the precompile does:
for every calldata there is a gas level above which the frame halts by
returning exactly the digest of that calldata.

The `∃ g₀, ∀ g ≥ g₀` shape is "given enough gas": gas *must* appear, since
below some level every implementation runs out, and no fixed constant can
be right for all input lengths. It carries real content — the conclusion
holds for every larger budget, so a candidate cannot pass by succeeding at
one lucky gas value. -/
def Correct (code : ByteArray) : Prop :=
  ∀ calldata : ByteArray, ∃ g₀ : Nat, ∀ g : Nat, g₀ ≤ g →
    Eval (frame code calldata g) (.returned (spec calldata))

/-- The efficiency-carrying strengthening: `schedule n` gas suffices for
every input of `n` bytes. This is what a gas schedule in an EIP would need,
and the top tier of the challenge. -/
def CorrectWithSchedule (code : ByteArray) (schedule : Nat → Nat) : Prop :=
  ∀ (calldata : ByteArray) (g : Nat), schedule calldata.size ≤ g →
    Eval (frame code calldata g) (.returned (spec calldata))

/-- A proven gas schedule implies correctness. -/
theorem correct_of_schedule {code : ByteArray} {schedule : Nat → Nat}
    (h : CorrectWithSchedule code schedule) : Correct code :=
  fun calldata => ⟨schedule calldata.size, fun g hg => h calldata g hg⟩

/-- The frame-generalized statement: the same conclusion from *any* machine
state that is a fresh frame executing `code` — arbitrary world, caller, call
value, and storage. `Correct` is this restricted to the canonical world; the
gap between them is the noninterference obligation `Obligation.W`. -/
def CorrectInAnyFrame (code : ByteArray) : Prop :=
  ∀ (s : EVM.State), s.executionEnv.code = code → s.pc = 0 → s.stack = [] →
    s.callStack = [] → s.halt = .Running → s.memory = .empty →
    s.activeWords = 0 → s.executionEnv.fork = .Osaka →
    Precompile.isPrecompile s.executionEnv.fork s.executionEnv.codeAddr = false →
    ∃ g₀ : Nat, ∀ g : Nat, g₀ ≤ g →
      Eval { s with gasAvailable := g } (.returned (spec s.executionEnv.calldata))

/-! ## Frame facts

The canonical frame satisfies the compiler correctness theorem's target-side
side conditions. These are what let a Yul-level proof land on `Correct`
without any bytecode-level reasoning. -/

theorem frame_pc (code calldata : ByteArray) (gas : Nat) :
    (frame code calldata gas).pc = UInt256.ofNat 0 := rfl

theorem frame_stack (code calldata : ByteArray) (gas : Nat) :
    (frame code calldata gas).stack = [] := rfl

theorem frame_gas (code calldata : ByteArray) (gas : Nat) :
    (frame code calldata gas).gasAvailable = gas := rfl

theorem frame_calldata (code calldata : ByteArray) (gas : Nat) :
    (frame code calldata gas).executionEnv.calldata = calldata := rfl

theorem deployAddress_not_precompile :
    Precompile.isPrecompile .Osaka deployAddress = false := by
  decide

theorem frame_frameOK {code calldata : ByteArray} {gas : Nat}
    (hsize : code.size < 2 ^ 256) : FrameOK code (frame code calldata gas) where
  hcode := rfl
  codeSmall := hsize
  fork := rfl
  noPrecompile := deployAddress_not_precompile
  callStack := rfl
  running := rfl

end Challenge.Sha256
