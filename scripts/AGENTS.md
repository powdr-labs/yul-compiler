# Working in `scripts/`

CI drivers and maintenance tooling. The reusable harness code these call lives in
`YulEvmCompilerTests/` (see its `AGENTS.md`). Read the root `AGENTS.md` "Testing
and verification" section for the exact invocations and baseline semantics.

## ⚠️ Trust-boundary files here — do NOT edit or run as an agent

`update-spec.sh` re-pins the audited specification closure. It, together with
`Checks.lean`, `SpecClosure.lean`, and `SPEC.md`, is **human-approval-only**: an
agent must never modify, run, or regenerate them, because that would let a change
to the spec approve itself. If your work legitimately moves the specification
surface, stop and surface it for a human — see the root `AGENTS.md`
trust-boundary section.

## Corpus / CI drivers (safe to run for local checking)

- `CheckSoliditySyntaxTests.lean` — parse every `yulSyntaxTests` fixture; expected
  rejections detected from `// ----` `Error` diagnostics.
- `CheckSolidityInterpreterTests.lean` — compile + execute `yulInterpreterTests`
  fixtures and compare sorted nonzero state.
- `CheckSolidityCompileTests.lean` — positive-compile `yulOptimizerTests`,
  `objectCompiler`, `evmCodeTransform` sources.
- `CheckSoliditySolcDifferential.lean` — behavioral differential vs. pinned solc
  across six seeded environments; also gas-checks against the baselines.
- `CheckSolidityGas.lean` — the `--via-ir` gas comparison. Built as the **native**
  `checkSolidityGas` executable (declared in `lakefile.toml`), *not* via
  `lean --run`, because compiling large real-world contracts recurses past the
  interpreter stack; CI and `update-gas.sh` raise `ulimit -s`.
- `CheckSolidityCompileGate.lean` — **compile-only** corpus checker: reports which
  `.sol` fixtures the compiler *rejects* (`solc --ir` → `compileSource`, including
  the stack-overflow gate), with **no gas execution**. Native `checkCompileGate`
  exe (same stack-depth reason as `checkSolidityGas`). Use it — not a full
  `checkSolidityGas` run and never `lean --run` — to find the fixtures a gate
  change now rejects: `checkCompileGate <corpus-dir> <solc> --baseline=<gas-baseline>`
  prints exactly the stale gas rows to drop. Most contracts compile in <0.1 s;
  shard 8-way (`--shard=I/8`) and union the `REJECT` lines for all of
  semanticTests in a few minutes — vs. ~24 min/shard for the gas runner, and
  with no gas execution (which can hang) or interpreter stack overflow.
- `UpdateCorpusGas.lean` + `update-gas.sh` — regenerate the gas baselines. The
  gas baselines are *derived data*; regenerate them with these tools rather than
  hand-editing `test/…-gas-baseline.txt`.
- `ci_pr_summary.py` / `test_ci_pr_summary.py` — CI PR-summary generation (Python).

`lakefile.toml` and `lake-manifest.json` (which pin the upstream semantics
revisions) are also human-approval-only — bumping them can silently move the
external boundary the theorems are stated against.
