import YulEvmCompiler.Compile
import YulSemantics.Syntax
import YulSemantics.Interp
import YulSemantics.FibExample
import EvmSemantics.EVM.StepF

/-!
# YulEvmCompiler.Examples

Sanity checks for the labeled-assembly pipeline (`compileProgram` /
`compile`): loops, `break`/`continue`, user-defined functions (including
recursion), and `leave`.

Beyond "it compiles", the interesting checks here are **differential**: each
program is run through yul-semantics' fuel-indexed interpreter *and* the
compiled bytecode is run through evm-semantics' executable step function
(`stepF`), and the final storage values are compared. This exercises the
whole pipeline (labels, lowering, the calling convention) long before the
correctness proof covers it.
-/

namespace YulEvmCompiler.Examples

open YulSemantics
open YulSemantics.EVM (Op EvmState)
open YulEvmCompiler

/-! ### Test programs -/

/-- A counting loop: `1 + 2 + … + 5` into storage slot 0. -/
def sumLoop : Block Op := yul% {
  let sum := 0
  for { let i := 1 } lt(i, 6) { i := add(i, 1) } {
    sum := add(sum, i)
  }
  sstore(0, sum)
}

/-- `continue` skips 3, `break` stops at 6: `0+1+2+4+5 = 12` in slot 0. -/
def breakContinue : Block Op := yul% {
  let s := 0
  for { let i := 0 } lt(i, 10) { i := add(i, 1) } {
    if eq(i, 3) { continue }
    if eq(i, 6) { break }
    s := add(s, i)
  }
  sstore(0, s)
}

/-- `switch` dispatch: `x = 2` selects the matching case, `7*3 = 21` in slot 0. -/
def switchMatch : Block Op := yul% {
  let x := 2
  switch x
  case 1 { sstore(0, 10) }
  case 2 { sstore(0, mul(7, 3)) }
  case 3 { sstore(0, 30) }
  default { sstore(0, 99) }
}

/-- `switch` fall-through to `default` when no case matches: `99` in slot 0. -/
def switchDefault : Block Op := yul% {
  let x := 5
  switch x
  case 1 { sstore(0, 10) }
  case 2 { sstore(0, 20) }
  default { sstore(0, 99) }
}

/-- A multi-value-return function feeding a multi-value `let`:
`divmod(17, 5) = (3, 2)` into slots 0 and 1. -/
def multiRet : Block Op := yul% {
  function divmod(a, b) -> q, r {
    q := div(a, b)
    r := mod(a, b)
  }
  let x, y := divmod(17, 5)
  sstore(0, x)
  sstore(1, y)
}

/-- A multi-value-return function feeding a multi-value assignment (the
targets already exist): `x, y := swap2(x, y)` swaps `1, 2` to `2, 1`. -/
def multiAssign : Block Op := yul% {
  function swap2(a, b) -> c, d {
    c := b
    d := a
  }
  let x := 1
  let y := 2
  x, y := swap2(x, y)
  sstore(0, x)
  sstore(1, y)
}

/-- A three-value return, exercising the full `SWAP1;SWAP2;SWAP3` rotation:
`first3() = (7, 8, 9)` into slots 0, 1, 2. -/
def multiRet3 : Block Op := yul% {
  function first3() -> a, b, c {
    a := 7
    b := 8
    c := 9
  }
  let x, y, z := first3()
  sstore(0, x)
  sstore(1, y)
  sstore(2, z)
}

/-- A simple function: `double(21) = 42` in slot 0. -/
def funCall : Block Op := yul% {
  function double(x) -> y {
    y := add(x, x)
  }
  sstore(0, double(21))
}

/-- A *recursive* function: `fact(5) = 120` in slot 0. -/
def factorial : Block Op := yul% {
  function fact(n) -> f {
    f := 1
    if gt(n, 1) {
      f := mul(n, fact(sub(n, 1)))
    }
  }
  sstore(0, fact(5))
}

/-- `leave` returns early: `f(0) = 1` in slot 0, `f(7) = 2` in slot 1. -/
def leaveEarly : Block Op := yul% {
  function f(a) -> r {
    r := 1
    if eq(a, 0) { leave }
    r := 2
  }
  sstore(0, f(0))
  sstore(1, f(7))
}

/-- Functions calling functions, calls nested inside expressions and loop
conditions; a zero-return function used as a statement. -/
def nested : Block Op := yul% {
  function sq(x) -> y {
    y := mul(x, x)
  }
  function store(k, v) {
    sstore(k, v)
  }
  let acc := 0
  for { let i := 1 } lt(i, add(sq(2), 1)) { i := add(i, 1) } {
    acc := add(acc, sq(i))
  }
  store(0, acc)
}

/-- A `for` whose body declares locals and `break`s from inside a nested
block (the pops must unwind both the inner block and the body). -/
def breakNested : Block Op := yul% {
  let r := 0
  for { let i := 0 } lt(i, 100) { i := add(i, 1) } {
    let d := add(i, i)
    {
      let e := add(d, 1)
      if gt(e, 7) { r := e break }
    }
  }
  sstore(0, r)
}

/-- The `n`-th Fibonacci number into storage slot 0, iteratively — the same
loop as yul-semantics' `FibExample.fibContract`, but reading `n` and writing
the result through **storage** (`sload`/`sstore`) instead of calldata/memory,
so it lands inside the verified op set. Here `n = 10`, so slot 0 ends at
`fib 10 = 55`. -/
def fibStorage : Block Op := yul% {
  let n := 10
  let a := 0
  let b := 1
  for { let i := 0 } lt(i, n) { i := add(i, 1) } {
    let t := add(a, b)
    a := b
    b := t
  }
  sstore(0, a)
}

#guard (compileProgram sumLoop).isSome
#guard (compileProgram breakContinue).isSome
#guard (compileProgram funCall).isSome
#guard (compileProgram factorial).isSome
#guard (compileProgram leaveEarly).isSome
#guard (compileProgram nested).isSome
#guard (compileProgram breakNested).isSome
#guard (compileProgram fibStorage).isSome
#guard (compile sumLoop).isSome
#guard (compile factorial).isSome
#guard (compile fibStorage).isSome

/-! ### The upstream Fibonacci contract

`YulSemantics.FibExample.fibContract` (the `n`-th Fibonacci contract proved
correct in yul-semantics) reads `n` from **calldata** (`calldataload`),
computes `fib n` in a `for` loop, writes it to **memory** (`mstore`), and
`return`s it. With `calldataload` and `mstore` now in the verified op set
(`opTable`) it compiles all the way to bytecode. -/
#guard (compileProgram FibExample.fibContract).isSome
#guard (compile FibExample.fibContract).isSome

/-! ### Differential execution: Yul interpreter vs. compiled bytecode -/

/-- Run the Yul-side interpreter to a final machine state. -/
def runYul (fuel : Nat) (prog : Block Op) : Option EvmState :=
  match Interp.run YulSemantics.EVM.exec fuel prog EvmState.init with
  | .ok (_, st, _) => some st
  | _ => none

/-- A minimal EVM state executing `code` on Osaka with plenty of gas. -/
def evmInit (code : ByteArray) : EvmSemantics.EVM.State :=
  let env : EvmSemantics.ExecutionEnv := Inhabited.default
  let s : EvmSemantics.EVM.State := Inhabited.default
  { s with
      pc := 0
      stack := []
      execLength := 0
      halt := .Running
      callStack := []
      gasAvailable := 100000000
      executionEnv := { env with
          code := code
          fork := .Osaka
          permitStateMutation := true } }

/-- Drive `stepF` until done (fuel-bounded). -/
def runEvm : Nat → EvmSemantics.EVM.State → EvmSemantics.EVM.State
  | 0, s => s
  | fuel + 1, s =>
    if s.isDone then s else runEvm fuel (EvmSemantics.EVM.stepF s)

/-- Compile `prog`, run both sides, and compare the storage values at
`keys` (plus that the EVM run actually finished without an exception). -/
def agreeOn (prog : Block Op) (keys : List Nat) : Bool :=
  match compile prog, runYul 100000 prog with
  | some is, some yst =>
      let s := runEvm 100000 (evmInit (assemble is))
      s.isDone
        && (s.halt matches .Success)
        && keys.all (fun k =>
          (yst.storage (BitVec.ofNat 256 k)).toNat
            == ((s.accountMap s.executionEnv.address).storage.get
                  (EvmSemantics.UInt256.ofNat k)).toNat)
  | _, _ => false

#guard agreeOn sumLoop [0]
#guard agreeOn breakContinue [0]
#guard agreeOn switchMatch [0]
#guard agreeOn switchDefault [0]
#guard agreeOn multiRet [0, 1]
#guard agreeOn multiAssign [0, 1]
#guard agreeOn multiRet3 [0, 1, 2]
#guard agreeOn funCall [0]
#guard agreeOn factorial [0]
#guard agreeOn leaveEarly [0, 1]
#guard agreeOn nested [0]
#guard agreeOn breakNested [0]
#guard agreeOn fibStorage [0]

/-- Compile `prog`, run both sides with `cd` as calldata, and compare the
returned byte payload (for contracts that halt via `return`, like the
calldata/memory Fibonacci contract). -/
def agreeReturn (prog : Block Op) (cd : List UInt8) : Bool :=
  let yst0 : EvmState :=
    { EvmState.init with env := { EvmState.init.env with calldata := cd } }
  match compile prog, Interp.run YulSemantics.EVM.exec 100000 prog yst0 with
  | some is, .ok (_, yst, _) =>
      let s0 := evmInit (assemble is)
      let s := runEvm 100000
        { s0 with executionEnv := { s0.executionEnv with calldata := ⟨cd.toArray⟩ } }
      s.isDone
        && (match yst.halted, s.halt with
            | some (.ret, ybytes), .Returned => ybytes == s.hReturn.toList
            | _, _ => false)
  | _, _ => false

-- The compiled calldata/memory Fibonacci contract returns the same bytes as
-- the Yul interpreter, for several inputs (`fib 0/1/7/10`).
#guard agreeReturn FibExample.fibContract (List.replicate 31 0 ++ [0])
#guard agreeReturn FibExample.fibContract (List.replicate 31 0 ++ [1])
#guard agreeReturn FibExample.fibContract (List.replicate 31 0 ++ [7])
#guard agreeReturn FibExample.fibContract (List.replicate 31 0 ++ [10])

-- The Yul interpreter's view of the expected values (documentation).
#guard (runYul 100000 sumLoop).map (fun st => (st.storage 0).toNat) = some 15
#guard (runYul 100000 breakContinue).map (fun st => (st.storage 0).toNat) = some 12
#guard (runYul 100000 switchMatch).map (fun st => (st.storage 0).toNat) = some 21
#guard (runYul 100000 switchDefault).map (fun st => (st.storage 0).toNat) = some 99
#guard (runYul 100000 multiRet).map (fun st => (st.storage 0).toNat) = some 3
#guard (runYul 100000 multiRet).map (fun st => (st.storage 1).toNat) = some 2
#guard (runYul 100000 multiAssign).map (fun st => (st.storage 0).toNat) = some 2
#guard (runYul 100000 multiAssign).map (fun st => (st.storage 1).toNat) = some 1
#guard (runYul 100000 multiRet3).map (fun st => (st.storage 2).toNat) = some 9
#guard (runYul 100000 funCall).map (fun st => (st.storage 0).toNat) = some 42
#guard (runYul 100000 factorial).map (fun st => (st.storage 0).toNat) = some 120
#guard (runYul 100000 leaveEarly).map
    (fun st => ((st.storage 0).toNat, (st.storage 1).toNat)) = some (1, 2)
#guard (runYul 100000 nested).map (fun st => (st.storage 0).toNat) = some 30
#guard (runYul 100000 breakNested).map (fun st => (st.storage 0).toNat) = some 9
#guard (runYul 100000 fibStorage).map (fun st => (st.storage 0).toNat) = some 55

end YulEvmCompiler.Examples
