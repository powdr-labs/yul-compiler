import YulEvmCompiler.Functions
import YulSemantics.Syntax
import EvmSemantics

/-!
# YulEvmCompiler.FunctionsExamples

Worked examples for the user-defined-function codegen in
`YulEvmCompiler.Functions`, written in the yul-semantics concrete-syntax DSL.

* `#guard` checks assert what the compiler accepts / rejects (pure, kernel-checked).
* `#eval` demos run the compiled bytecode through the **evm-semantics** EVM
  (`stepF` fuel loop) and print the resulting storage — an end-to-end check that
  the calling convention actually executes to the right value. The expected
  results are noted inline; all were confirmed (fac(5)=120, sum(10)=55,
  bump×2 → 2, two()→(7,9), g(h(4))=50).

NOTE: this is the *executable* side. The machine-checked correctness proof of
the calling convention (against `YulSemantics.Run`) is layered on separately
and does not yet cover these programs — unlike `compileProgram`, which is
backed by `compile_correct`.
-/

namespace YulEvmCompiler.FunctionsExamples

open YulSemantics YulSemantics.EVM YulEvmCompiler
open EvmSemantics EvmSemantics.EVM

/-! ### A minimal EVM runner (mirrors evm-semantics' `Main.initState`/`run`) -/

private def initState (code : ByteArray) (gas : Nat) : EvmSemantics.EVM.State :=
  let env : ExecutionEnv :=
    { address := 0, origin := 0, caller := 0, weiValue := ⟨0⟩
      calldata := .empty, code := code, codeAddr := 0
      gasPrice := ⟨0⟩, header := Inhabited.default, depth := 0
      permitStateMutation := true, blobVersionedHashes := #[], fork := .Cancun }
  { toMachineState :=
      { gasAvailable := gas, activeWords := ⟨0⟩
        memory := .empty, returnData := .empty, hReturn := .empty }
    accountMap := AccountMap.empty, substate := Substate.empty
    executionEnv := env, pc := ⟨0⟩, stack := [], execLength := 0, halt := .Running }

private partial def run (s : EvmSemantics.EVM.State) (fuel : Nat) : EvmSemantics.EVM.State :=
  if fuel = 0 then s else if s.isDone then s else run (stepF s) (fuel - 1)

/-- Compile `prog`, execute it, and read storage slot `slot` of the executing
account. -/
private def runSlot (prog : Block Op) (slot : Nat) : Option Nat := do
  let is ← compileProgF prog
  let s := run (initState (assemble is) 100000000) 2000000
  return ((s.accountMap s.executionEnv.address).storage.get
    (EvmSemantics.UInt256.ofNat slot)).toNat

/-! ### Examples -/

/-- Recursive factorial. -/
def facProg : Block Op := yul% {
  function fac(n) -> r {
    r := 1
    if n { r := mul(n, fac(sub(n, 1))) }
  }
  sstore(0, fac(5))
}

/-- Recursive sum `0 + 1 + … + n`. -/
def sumProg : Block Op := yul% {
  function sum(n) -> r {
    r := 0
    if n { r := add(n, sum(sub(n, 1))) }
  }
  sstore(0, sum(10))
}

/-- A parameterless, return-less procedure with a side effect, called twice. -/
def procProg : Block Op := yul% {
  function bump() { sstore(0, add(sload(0), 1)) }
  bump()
  bump()
}

/-- A two-return function, consumed by a multi-`let`. -/
def pairProg : Block Op := yul% {
  function two() -> a, b { a := 7  b := 9 }
  let x, y := two()
  sstore(x, y)
}

/-- Nested calls in argument position: `g(h(4))`. -/
def nestProg : Block Op := yul% {
  function h(x) -> r { r := add(x, 1) }
  function g(x) -> r { r := mul(x, 10) }
  sstore(0, g(h(4)))
}

-- Compiler acceptance (pure, CI-checked):
#guard (compileProgF facProg).isSome
#guard (compileProgF sumProg).isSome
#guard (compileProgF procProg).isSome
#guard (compileProgF pairProg).isSome
#guard (compileProgF nestProg).isSome

-- End-to-end execution on the evm-semantics EVM (runs at build time):
#eval runSlot facProg 0      -- some 120   (5!)
#eval runSlot sumProg 0      -- some 55    (Σ 1..10)
#eval runSlot procProg 0     -- some 2     (bump twice)
#eval runSlot pairProg 7     -- some 9     (storage[7] := 9)
#eval runSlot nestProg 0     -- some 50    (g(h(4)) = (4+1)*10)

end YulEvmCompiler.FunctionsExamples
