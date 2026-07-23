# Working in `YulEvmCompilerTests/`

Shared harness code for the Solidity-corpus differential and gas checks. The CI
entry points themselves live in `scripts/` (see `scripts/AGENTS.md`); this library
holds the reusable machinery they call. Read the root `AGENTS.md` "Testing and
verification" section for how the corpora are run and what each baseline means.

Note: there is **no `lake test`**. Fast end-to-end regressions are the `#guard`s
in `YulEvmCompiler/Examples.lean`, executed by `lake build`. This library is the
heavier external-differential layer that needs a pinned solc and a Solidity
checkout.

## File map

- `Solc.lean` — drives the pinned solc 0.8.35 (via `svm`) as an external process.
- `SolidityCorpus.lean` — shared fixture / baseline / source-section / EVM-version
  helpers over the Solidity corpora.
- `SolTest.lean` — parses a fixture's `// ----` call specs into calldata + value
  (arguments already in flattened ABI form).
- `InterpreterFixture.lean` — runner for Solidity's Yul interpreter fixtures;
  `initialState` is the canonical environment defaults — **consult it before
  diagnosing any environment-reader difference**.
- `SolcDifferential.lean` — common-state behavioral comparison of this compiler's
  vs. solc's bytecode across the six seeded environments, plus `measureGas`.
- `CorpusGas.lean` — per-suite gas baseline model: total gas per fixture,
  regression classification (solc total as a source fingerprint), baseline
  parse/render.
- `Parallel.lean` — sharding/concurrency helpers.

## What differential tests may and may not compare

Compare **observable** results only: termination/output, returndata, nonzero
memory, account state, logs, self-destructs, storage refunds. **Never** compare
exact bytecode, PCs, internal stacks, remaining gas, or the executing account's
code representation — those legitimately depend on layout and encoding choices.

Every `test/…-known-*-failures.txt` and `…-gas-baseline.txt` is an **exact
baseline**, not a skip list: unexpected failures *and* stale entries both fail the
run. Never edit a baseline just to make CI green — explain the semantic or
unsupported-feature reason, and note that gas baselines are regenerated only via
`scripts/update-gas.sh`.
