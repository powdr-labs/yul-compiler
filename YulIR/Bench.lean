import YulIR
import YulEvmCompiler.Compile
import YulEvmCompiler.Optimizer.Implementation.Pipeline
import YulEvmCompiler.Optimizer.Implementation.StackLayout
import YulEvmCompilerTests.SolcDifferential
import YulSemantics.Syntax

/-!
# YulIR.Bench — gas / code-size comparison: IR pipeline vs. current pipeline

For a Yul top-level block, compile it three ways to EVM bytecode and compare:

* **raw**     — the backend only (`compile`, with the stack-layout fallback), no optimizer;
* **current** — today's production path (`Optimizer.optimizerPipeline`, then the backend);
* **IR**      — round-trip through this IR (`toYul ∘ ofYul`), then the backend — *no
  optimizations yet*, so this measures the cost of ANF flattening the backend must absorb.

We reuse the differential harness (`SolcDifferential.measureGas` / `compareBytecode`, which
execute the bytecodes under several deterministic scenarios) so gas is real EVM execution gas,
and it is only reported for scenarios where the two programs reach identical observable state.

As IR optimizations land, the IR column should move from "worse than current" toward
"better than current". Run with:
  `lake env lean YulIR/Bench.lean`
-/

namespace YulIR.Bench

open YulSemantics EVM
open YulEvmCompilerTests.SolcDifferential (measureGas compareBytecode)

/-- Today's production optimizer applied to a top-level block (the "current pipeline"). -/
def currentOpt (b : YulSemantics.Block EVM.Op) : YulSemantics.Block EVM.Op :=
  (YulEvmCompiler.Optimizer.optimizerPipeline
    (calls := YulSemantics.EVM.ExternalCalls.none)
    (creates := YulSemantics.EVM.ExternalCreates.none)).run b

/-- The IR round-trip (no optimizations yet). -/
def irRoundTrip (b : YulSemantics.Block EVM.Op) : YulSemantics.Block EVM.Op :=
  YulIR.toYul (YulIR.ofYul b)

/-- Backend: block → bytecode, using the same stack-layout fallback `compileSource` uses. -/
def blockBytecode (b : YulSemantics.Block EVM.Op) : Option ByteArray :=
  (YulEvmCompiler.compile b
    <|> YulEvmCompiler.compile (YulEvmCompiler.Optimizer.stackLayoutBlock b)).map
      YulEvmCompiler.assemble

def sizeStr : Option ByteArray → String
  | some ba => s!"{ba.size}B"
  | none    => "FAILED"

/-- Bench one program: sizes for raw/current/IR, then IR-vs-current behavior + gas. -/
def bench (name : String) (b : YulSemantics.Block EVM.Op) : IO Unit := do
  IO.println s!"══════════ {name} ══════════"
  let raw := blockBytecode b
  let cur := blockBytecode (currentOpt b)
  let ir  := blockBytecode (irRoundTrip b)
  IO.println s!"  code size:  raw={sizeStr raw}   current={sizeStr cur}   IR={sizeStr ir}"
  match ir, cur with
  | some irB, some curB =>
      match compareBytecode irB curB with
      | .error e => IO.println s!"  behaviour:  IR vs current DIVERGE — {e}"
      | .ok () =>
          IO.println "  behaviour:  IR ≡ current ✓   exec gas (IR vs current):"
          for (sname, res) in measureGas irB curB do
            match res with
            | some (gIr, gCur) =>
                let delta : Int := (Int.ofNat gIr) - (Int.ofNat gCur)
                let sign := if delta > 0 then "+" else ""
                IO.println s!"      {sname}: IR={gIr}  current={gCur}  Δ={sign}{delta}"
            | none => IO.println s!"      {sname}: (not gas-comparable)"
  | _, _ => IO.println "  (gas skipped: a bytecode did not compile)"
  IO.println ""

end YulIR.Bench

section
open YulIR.Bench
open YulSemantics EVM

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
  sstore(0, n)
}

#eval do
  bench "loop" loopProg
  bench "nested / ANF" nestedProg
  bench "memory + keccak" memProg
  bench "function call" mixedProg

end
