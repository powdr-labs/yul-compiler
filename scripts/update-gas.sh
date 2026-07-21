#!/usr/bin/env bash
#
# update-gas.sh — re-pin the per-suite gas baselines checked by the solc
# differential (test/solidity-yul-*-gas-baseline.txt).
#
# Run this ONLY after a *legitimate, intended* change that moves the numbers: a
# change to this compiler's codegen, to the execution scenarios, a bump of the
# pinned solc version, or an upstream fixture edit. For every latest-fork corpus
# fixture that is not a known differential failure and compiles on both
# toolchains, it re-measures the total gas this compiler and the pinned solc
# spend and rewrites the baseline.
#
# The resulting `git diff` is the review artifact: it shows how gas moved on
# each fixture. The differential then fails CI if this compiler's total later
# rises above the pinned figure while solc's is unchanged.
#
# Point it at a Solidity checkout with the Yul corpora (SOLIDITY_DIR, default
# /tmp/solidity — the same tree CI's differential fetches).
#
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

SOLC_VERSION="${SOLC_VERSION:-0.8.35}"
SOLIDITY_DIR="${SOLIDITY_DIR:-/tmp/solidity}"

if [[ -n "${SOLC_PATH:-}" ]]; then
  solc_path="$SOLC_PATH"
elif command -v svm >/dev/null 2>&1; then
  solc_path="$(svm which "$SOLC_VERSION")"
else
  echo "error: set SOLC_PATH, or install svm and 'svm install $SOLC_VERSION'" >&2
  exit 1
fi
test -x "$solc_path"

# suite-name  corpus-subdir  known-failures-file  gas-baseline-file
suites=(
  "optimizer yulOptimizerTests solidity-yul-optimizer-known-solc-differential-failures.txt solidity-yul-optimizer-gas-baseline.txt"
  "object-compiler objectCompiler solidity-yul-object-compiler-known-solc-differential-failures.txt solidity-yul-object-compiler-gas-baseline.txt"
  "EVM-code-transform evmCodeTransform solidity-yul-evm-code-transform-known-solc-differential-failures.txt solidity-yul-evm-code-transform-gas-baseline.txt"
)

for entry in "${suites[@]}"; do
  read -r suite subdir known baseline <<<"$entry"
  echo "==> Re-measuring $suite gas with solc $SOLC_VERSION"
  lake env lean --run scripts/UpdateCorpusGas.lean \
    "$suite" \
    "$SOLIDITY_DIR/test/libyul/$subdir" \
    "test/$known" \
    "test/$baseline" \
    "$solc_path" "$SOLC_VERSION"
done

# The Solidity gas runner is a native executable (large contracts recurse past
# the interpreter stack); raise the OS stack for the deepest ones.
lake build checkSolidityGas
ulimit -s unlimited || true

echo "==> Re-measuring Solidity gasTests (compile via --via-ir, optimized runtime)"
.lake/build/bin/checkSolidityGas \
  "$SOLIDITY_DIR/test/libsolidity/gasTests" \
  test/solidity-gas-baseline.txt \
  "$solc_path" "$SOLC_VERSION" --update

echo "==> Re-measuring Solidity semanticTests (compilable subset, lenient)"
.lake/build/bin/checkSolidityGas \
  "$SOLIDITY_DIR/test/libsolidity/semanticTests" \
  test/solidity-semantic-gas-baseline.txt \
  "$solc_path" "$SOLC_VERSION" --lenient --update

echo "==> Re-measuring Uniswap v4-core fixtures (in-repo, strict + known failures)"
.lake/build/bin/checkSolidityGas \
  test/uniswap-v4 \
  test/uniswap-v4-gas-baseline.txt \
  "$solc_path" "$SOLC_VERSION" \
  --known=test/uniswap-v4-known-compile-failures.txt --per-scenario --update

echo "==> Re-measuring Aave v4 fixtures (in-repo, strict + known failures)"
.lake/build/bin/checkSolidityGas \
  test/aave-v4 \
  test/aave-v4-gas-baseline.txt \
  "$solc_path" "$SOLC_VERSION" \
  --known=test/aave-v4-known-compile-failures.txt --per-scenario --update

echo
echo "==> Done. Review the diff — this is the review artifact:"
git --no-pager diff --stat -- 'test/solidity-yul-*-gas-baseline.txt' \
  test/solidity-gas-baseline.txt test/solidity-semantic-gas-baseline.txt \
  test/uniswap-v4-gas-baseline.txt test/aave-v4-gas-baseline.txt
