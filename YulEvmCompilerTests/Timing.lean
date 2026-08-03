set_option warningAsError true
/-! Per-fixture wall-clock accounting for the corpus runners.

The corpus runners already do all the work needed to say how long each compiler
takes on a suite — they just never looked at the clock. These helpers let a
runner attribute a fixture's time to *this* compiler, to the pinned `solc`, or
to solc's Solidity→Yul front-end, so the PR summary can report compiler runtime
next to gas.

The unit of measurement is one fixture's elapsed nanoseconds, summed over the
suite. Summing per-fixture spans (rather than timing the whole run) keeps the
figure independent of how many workers `parMap` uses and of how a suite is
sharded across CI legs: every shard reports the work it did, and the summary
adds them up. Under saturated parallelism each span is wall-clock on a busy
machine, so the total approximates CPU time and should be read as an indicator,
not a benchmark.
-/

namespace YulEvmCompilerTests.Timing

/-- Nanoseconds elapsed since the monotonic-clock reading `start`. -/
def since (start : Nat) : IO Nat := do
  return (← IO.monoNanosNow) - start

/-- Run `act`, returning its result together with how long it took, in ns.

Only for genuine `IO` work (a `solc` subprocess). Pure compilation must be timed
inline instead: passing `pure (f x)` here would evaluate `f x` while building the
argument, i.e. before the clock starts. -/
def timedIO {α : Type} (act : IO α) : IO (α × Nat) := do
  let start ← IO.monoNanosNow
  let value ← act
  return (value, ← since start)

/-- Whole milliseconds, rounded to nearest — the granularity the CI summary
reports. Sub-millisecond fixtures are common, which is exactly why the runners
accumulate nanoseconds and convert only the suite total. -/
def toMs (ns : Nat) : Nat := (ns + 500000) / 1000000

end YulEvmCompilerTests.Timing
