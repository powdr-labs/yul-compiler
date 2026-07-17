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

The same differential run also compares *gas*. For every fixture whose two
bytecode sequences are behaviorally comparable, it sums the execution gas this
compiler and solc spend across the comparable scenarios and checks this
compiler's total against a per-suite baseline
(`solidity-yul-*-gas-baseline.txt`). CI **fails if this compiler's total rises
above the pinned figure**. Because the corpora track upstream `develop`, a
fixture's source can change and move our gas for reasons unrelated to codegen;
solc's pinned total is used as a content fingerprint, so a rise only counts as a
regression when solc's total is unchanged. A changed solc total, a new fixture,
or a removed one is a re-pin notice rather than a failure, and only genuine
regressions fail. The baselines are sharded by the same fixture-name hash as the
known-failure lists. Re-pin after an intended codegen or solc change with:

```sh
scripts/update-gas.sh          # regenerates test/solidity-yul-*-gas-baseline.txt
```

## Solidity gasTests

`scripts/CheckSolidityGas.lean` extends the comparison to Solidity's
`test/libsolidity/gasTests` — full contracts, not Yul. Since this compiler only
accepts Yul, each contract is lowered by solc through its `--via-ir` pipeline
**with the Yul optimizer off** (`--ir`), and this compiler compiles that fully
unoptimized Yul; compiling it is the correctness check. This deliberately uses
only solc's Solidity→Yul front-end and none of solc's Yul optimizer. For gas,
our runtime bytecode (obtained by deploying our creation bytecode in the
executable EVM and taking the returned code) is compared against solc's own
**fully optimized** runtime (`--bin-runtime --optimize --via-ir`) under the same
scenarios — our non-optimizing compiler versus solc's best. This compiler's
total is pinned in `solidity-gas-baseline.txt` with the same fail-if-worse rule.
It relies on two small additions that let this compiler accept solc's generated
Yul: the validator no longer mis-lexes digits inside identifiers (solc's hashed
helper names), and `memoryguard` is desugared to its argument before
compilation. Re-pin with `scripts/update-gas.sh`.

Both compilers' optimized creation bytecode is deployed (running the
constructor), and the contract's calls are replayed on each, summing the gas
over the calls that reach identical observable behavior. A successful empty
`RETURN` and a `STOP` are treated as the same outcome (our compiler emits the
former where solc's optimizer emits the latter). gasTests specify no call
arguments, so each external function is called once with synthetic argument
words.

The same runner also covers Solidity's much larger
`test/libsolidity/semanticTests` corpus — real contracts, not microbenchmarks —
in `--lenient` mode: contracts using features this compiler cannot yet handle
are skipped rather than failing, and only the compilable subset's gas is pinned
(`solidity-semantic-gas-baseline.txt`). These fixtures specify their own calls
in the `// ----` section (`f(uint256): 42 -> 42`), with arguments already in
flattened ABI form, so the runner replays the *real* calls the test intends
(state persisting across the sequence, outputs cross-checked) rather than
synthetic inputs. CI runs it sharded across the optimizer legs. This is where
the largest overheads surface — e.g. contracts solc constant-folds to almost
nothing that this non-optimizing compiler runs in full.

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

After installing solc 0.8.35 with `svm-rs`, its behavioral-plus-gas differential
can be run with:

```sh
lake env lean --run scripts/CheckSoliditySolcDifferential.lean \
  optimizer \
  /path/to/solidity/test/libyul/yulOptimizerTests \
  test/solidity-yul-optimizer-known-solc-differential-failures.txt \
  test/solidity-yul-optimizer-gas-baseline.txt \
  "$(svm which 0.8.35)" 0.8.35 \
  0 4
```

Omit the final shard index/count pair to run the complete suite locally; use
indices `0` through `3` with count `4` to reproduce the four CI shards. Re-pin
the gas baselines after an intended change with `scripts/update-gas.sh` (it
regenerates all three suites from `SOLIDITY_DIR`, default `/tmp/solidity`).
