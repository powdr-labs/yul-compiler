# Gas benchmarks (Tier A)

Hand-written Yul programs used to compare the execution gas of this compiler's
bytecode against solc's. Unlike the upstream Solidity corpora, these are small,
in-repo, and version-controlled, so their gas figures are stable and their
baseline (`../gas-benchmarks.txt`) can be pinned exactly.

Each fixture is a strict-assembly Yul program that **both** this compiler and
the pinned solc accept, chosen to be gas-interesting in a way that surfaces the
non-optimizing compiler's overhead:

- `arithmetic_loop.yul` — a counted loop over pure word arithmetic.
- `storage_loop.yul` — SSTORE/SLOAD across many slots, plus clears (cold/warm
  pricing and refunds).
- `fib_recursive.yul` — doubly-recursive Fibonacci (calling convention).
- `keccak_memory.yul` — memory expansion and per-word `keccak256` cost.
- `switch_dispatch.yul` — calldata-driven `switch` dispatch (branchy control
  flow; the only benchmark whose gas varies across input scenarios).

Both bytecode sequences run under the same deterministic scenarios as the solc
behavioral differential. For each scenario where the two reach identical
observable behavior, the gas each spends is recorded. Behavior is compared
exactly; gas is not — a non-optimizing compiler is expected to spend strictly
more than solc, so the baseline is a measurement, never an equality target.

The baseline is pinned to solc 0.8.35 and EVM version Osaka. Any change to this
compiler's codegen, to these programs, to the scenarios, or a solc bump moves
the numbers and must be re-pinned:

```sh
scripts/update-gas.sh          # regenerates ../gas-benchmarks.txt; review the diff
```

CI checks the committed baseline against a fresh measurement and fails on drift.
