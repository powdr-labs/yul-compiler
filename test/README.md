# Upstream Yul tests

`solidity-yul-syntax-known-mismatches.txt` records expected differences between
this parser/validator and Solidity's complete Yul syntax corpus. It is currently
empty: every upstream success is accepted and every fixture containing an
`*Error` expectation is rejected.

`solidity-yul-interpreter-known-failures.txt` records the fixtures that do not
yet work from Solidity's `test/libyul/yulInterpreterTests` corpus. CI attempts
every fixture whose `EVMVersion` constraint includes the latest supported fork
(Osaka), compiles and executes its Yul program with `evm-semantics` in the
fixed environment used by Solidity's Yul interpreter tests, then compares the
complete nonzero memory, storage, and transient-storage post-state with the
dumps embedded in the `.yul` file. A new failure or a stale baseline entry
makes CI fail; malformed version metadata also fails the run.

The initial state has empty calldata, memory, storage, and transient storage.
It also reproduces Solidity's fixed address, caller, call value, balances,
versioned blob hashes, block number, timestamp, fees, chain ID, and other block
fields. The executing account's code is always the bytecode produced by this
compiler, including for object roots. Solidity's AST interpreter instead uses
synthetic hash-derived object offsets/sizes and a dummy
`codecodecodecodecode` buffer. Consequently, the three fixtures that assert
those synthetic values compile successfully but remain explicit post-state
mismatches in the baseline.

The three `solidity-yul-*-known-compile-failures.txt` files cover Solidity's
positive `yulOptimizerTests`, `objectCompiler`, and `evmCodeTransform`
corpora. CI extracts the source before the fixture settings or expectation
section and runs the production `compileSource` entry point on every fixture
whose `EVMVersion` range includes Osaka. These tests establish compilation
compatibility only: optimizer output, exact assembly, bytecode, opcodes, and
source mappings are solc-specific and are deliberately not compared. Every
fixture is attempted, and either a new failure or a stale baseline entry fails
the run.

The three `solidity-yul-*-known-solc-differential-failures.txt` files track
behavioral differences from pinned solc for the `yulOptimizerTests`,
`objectCompiler`, and `evmCodeTransform` suites. Each source is compiled
independently by solc and this compiler, then both bytecode sequences run
through the same `evm-semantics` interpreter under six deterministic initial
environments. These are the Solidity default, a fixed patterned state, and
four fixture-path-seeded states with calldata lengths 1, 31, 32, and 33 plus
varied call values, balances, persistent storage, and transient storage. The
comparison includes halt kind, output and returndata, nonzero memory, account
balances/nonces/storage, logs, self-destructs, and storage refunds. Exact
bytecode, current-account code presence, PCs, internal stacks, gas remaining,
and zero-only memory allocation are intentionally ignored because correct
compilers may differ there. Optimizer fixtures supply additional source
programs only: this check does not apply their configured optimization step or
compare their expected optimized Yul. CI partitions the expensive optimizer
run by a stable fixture-name hash; the same hash filters each shard's exact
baseline entries, so stale and unexpected failures remain enforced per shard.

## Gas comparison

Two runners compare the *execution gas* of this compiler's bytecode against
solc's. Both reuse the differential's deterministic scenarios and its exact
behavior gate: gas is only measured where both compilers reach identical
observable behavior, and a non-optimizing compiler is expected to spend more
gas, so gas is a measurement rather than an equality target.

`gas-benchmarks.txt` pins the exact per-scenario gas of the small, in-repo
benchmark suite in `test/gas/` (Tier A). `scripts/CheckGasBenchmarks.lean`
recompiles each benchmark with both toolchains, re-measures, and fails if the
result differs from the committed baseline; `scripts/update-gas.sh` re-pins it
after an intended codegen or solc change. See `test/gas/README.md`.

`scripts/ReportSolcGas.lean` is the non-gating Tier B report: it measures gas
overhead across a whole upstream corpus (skipping the differential's
known-failure entries) and prints the aggregate and worst-case ratios. It has
no baseline because the upstream corpora and solc numbers churn, and it is run
on demand rather than in CI — it is a measurement with no pass/fail meaning.

Remove a relative fixture path from any baseline as soon as it passes. A
local checkout can be checked with:

```sh
lake env lean --run scripts/CheckSoliditySyntaxTests.lean \
  /path/to/solidity/test/libyul/yulSyntaxTests \
  test/solidity-yul-syntax-known-mismatches.txt
```

Interpreter fixtures can be checked with:

```sh
lake env lean --run scripts/CheckSolidityInterpreterTests.lean \
  /path/to/solidity/test/libyul/yulInterpreterTests \
  test/solidity-yul-interpreter-known-failures.txt
```

One of the positive compiler corpora can be checked with:

```sh
lake env lean --run scripts/CheckSolidityCompileTests.lean \
  object-compiler \
  /path/to/solidity/test/libyul/objectCompiler \
  test/solidity-yul-object-compiler-known-compile-failures.txt
```

After installing solc 0.8.35 with `svm-rs`, its behavioral differential can be
run with:

```sh
lake env lean --run scripts/CheckSoliditySolcDifferential.lean \
  optimizer \
  /path/to/solidity/test/libyul/yulOptimizerTests \
  test/solidity-yul-optimizer-known-solc-differential-failures.txt \
  "$(svm which 0.8.35)" 0.8.35 \
  0 4
```

Omit the final shard index/count pair to run the complete suite locally; use
indices `0` through `3` with count `4` to reproduce the four CI shards.

The Tier A gas baseline can be checked (and the Tier B report produced) with:

```sh
lake env lean --run scripts/CheckGasBenchmarks.lean \
  test/gas test/gas-benchmarks.txt "$(svm which 0.8.35)" 0.8.35

lake env lean --run scripts/ReportSolcGas.lean \
  object-compiler \
  /path/to/solidity/test/libyul/objectCompiler \
  test/solidity-yul-object-compiler-known-solc-differential-failures.txt \
  "$(svm which 0.8.35)" 0.8.35
```

Pass `--update` to `CheckGasBenchmarks.lean` (or run `scripts/update-gas.sh`)
to re-pin the baseline after an intended change.
