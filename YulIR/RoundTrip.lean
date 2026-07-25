import YulIR
import YulSemantics.Interp
import YulSemantics.PrettyPrint

set_option warningAsError true
/-!
# YulIR.RoundTrip — semantic round-trip check

Runs a Yul program and its `toYul ∘ ofYul` round-trip through the `yul-semantics`
executable interpreter (`Interp.run`, the derived view of the ground-truth big-step
judgment) from the same initial states, and checks they produce the **same observable
result**.

The final variable environment legitimately differs (the round-trip introduces `_ir_*`
temporaries), and the raw machine state has function-typed fields (storage/memory/…),
so we compare a *fingerprint*: the control outcome, halt payload, returndata, logs,
self-destructs, `msize`, and storage/transient/memory sampled at a range of probe keys.
For a translation that only renames/re-sequences bindings, the fingerprints must match.

Run with: `lake env lean YulIR/RoundTrip.lean`.
-/

namespace YulIR.RoundTrip

open YulSemantics EVM

/-- Storage/transient keys sampled by the fingerprint. -/
def probeKeys : List U256 := (List.range 32).map (fun i => BitVec.ofNat 256 i)

/-- Memory bytes sampled by the fingerprint. -/
def probeMemBytes : Nat := 512

/-- An observable fingerprint of a final machine state + control outcome. -/
structure FingerPrint where
  outcome       : Outcome
  halted        : Option (HaltKind × List UInt8)
  returndata    : List UInt8
  logs          : List LogEntry
  selfdestructs : List (U256 × Bool)
  activeWords   : U256
  storage       : List U256
  transient     : List U256
  memory        : List UInt8
  deriving DecidableEq, Repr

/-- Project a final `(state, outcome)` onto its fingerprint. -/
def fingerprint (st : EvmState) (o : Outcome) : FingerPrint :=
  { outcome := o
    halted := st.halted
    returndata := st.returndata
    logs := st.logs
    selfdestructs := st.selfdestructs
    activeWords := st.activeWords
    storage := probeKeys.map st.storage
    transient := probeKeys.map st.transient
    memory := (List.range probeMemBytes).map st.memory }

/-- Run a Yul program to a fingerprint (or a stuck/out-of-fuel status). -/
def runFP (fuel : Nat) (prog : YulSemantics.Block EVM.Op) (st0 : EvmState) : Result FingerPrint :=
  (Interp.run EVM.exec fuel prog st0).map (fun r => fingerprint r.2.1 r.2.2)

/-- Do a program and its IR round-trip agree from `st0`? Same interpreter status
(`ok`/`stuck`/`outOfFuel`) and, when `ok`, identical fingerprints. -/
def agreesOn (fuel : Nat) (prog : YulSemantics.Block EVM.Op) (st0 : EvmState) : Bool :=
  runFP fuel prog st0 == runFP fuel (YulIR.toYul (YulIR.ofYul prog)) st0

/-! ### Initial-state scenarios -/

/-- An initial state whose calldata is a deterministic byte pattern. -/
def withCalldata (bytes : List UInt8) : EvmState :=
  { EvmState.init with env := { EvmState.init.env with calldata := bytes } }

/-- A handful of initial states to probe under. -/
def scenarios : List (String × EvmState) :=
  [ ("init", EvmState.init)
  , ("calldata=0x00..3f", withCalldata ((List.range 64).map (fun i => UInt8.ofNat i)))
  , ("calldata=42*", withCalldata (List.replicate 64 (UInt8.ofNat 42))) ]

/-- Check a program across all scenarios, printing a per-scenario verdict. -/
def check (name : String) (prog : YulSemantics.Block EVM.Op) (fuel : Nat := 100000) : IO Unit := do
  IO.println s!"── {name} ──"
  for (sname, st0) in scenarios do
    let src := runFP fuel prog st0
    let rt  := runFP fuel (YulIR.toYul (YulIR.ofYul prog)) st0
    let ok := src == rt
    let status :=
      match src with
      | .ok _ => "ok"
      | .stuck => "STUCK"
      | .outOfFuel => "OUT-OF-FUEL"
    let verdict := if ok then "PASS" else "FAIL"
    IO.println s!"    [{verdict}] {sname}  (source status: {status})"
  IO.println ""

end YulIR.RoundTrip

section
open YulIR.RoundTrip
open YulSemantics EVM

/-- Same programs as `YulIR.Examples`, checked semantically. -/
private def loopProg := yul% {
  let x := 0
  let i := 0
  for { } lt(i, 10) { i := add(i, 1) } { x := add(x, i) }
  sstore(0, x)
}

private def nestedProg := yul% {
  let a := add(sload(0), sload(1))
  sstore(a, mul(add(1, 2), 3))
}

private def memProg := yul% {
  mstore(0, calldataload(0))
  mstore(32, add(calldataload(0), calldataload(32)))
  sstore(0, keccak256(0, 64))
}

private def mixedProg := yul% {
  function f(p, q) -> r { r := add(p, q) }
  let n := f(3, 4)
  if lt(n, 100) {
    switch n
    case 7 { sstore(0, 1) }
    default { sstore(0, 2) }
  }
}

private def haltProg := yul% {
  mstore(0, 123)
  if calldataload(0) { revert(0, 32) }
  return(0, 32)
}

#eval do
  check "loop" loopProg
  check "nested / ANF (right-to-left)" nestedProg
  check "memory + keccak" memProg
  check "function + switch + if" mixedProg
  check "halting (return/revert)" haltProg

end
