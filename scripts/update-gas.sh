#!/usr/bin/env bash
#
# update-gas.sh — re-pin the Tier A gas benchmark baseline (test/gas-benchmarks.txt).
#
# Run this ONLY after a *legitimate, intended* change that moves the numbers: a
# change to this compiler's codegen, to the benchmark programs in test/gas/, to
# the execution scenarios, or a bump of the pinned solc version. It recompiles
# every benchmark with both this compiler and the pinned solc, re-measures gas,
# and rewrites the baseline.
#
# The resulting `git diff` is the review artifact: it shows exactly how gas moved
# on each benchmark and scenario. Confirm the change is intended (our numbers
# should generally only move when codegen does), then commit the new baseline.
#
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

SOLC_VERSION="${SOLC_VERSION:-0.8.35}"

# Resolve solc: honor an explicit SOLC_PATH, else ask svm for the pinned build.
if [[ -n "${SOLC_PATH:-}" ]]; then
  solc_path="$SOLC_PATH"
elif command -v svm >/dev/null 2>&1; then
  solc_path="$(svm which "$SOLC_VERSION")"
else
  echo "error: set SOLC_PATH, or install svm and 'svm install $SOLC_VERSION'" >&2
  exit 1
fi
test -x "$solc_path"

echo "==> Re-measuring gas benchmarks with solc $SOLC_VERSION"
lake env lean --run scripts/CheckGasBenchmarks.lean \
  test/gas test/gas-benchmarks.txt "$solc_path" "$SOLC_VERSION" --update

echo
echo "==> Done. Review the diff — this is the review artifact:"
git --no-pager diff --stat -- test/gas-benchmarks.txt
