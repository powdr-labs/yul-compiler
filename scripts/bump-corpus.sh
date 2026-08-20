#!/usr/bin/env bash
#
# bump-corpus.sh — move the pinned Solidity corpus revision.
#
# CI fetches the argotorg/solidity test corpora at the commit recorded in
# test/solidity-corpus.pin, so upstream pushes can never change what a CI run
# tests. Bumping the pin therefore *must* land in the same commit as the
# refreshed gas baselines (scripts/update-gas.sh), or the corpus and the
# baselines describe different fixture sets.
#
# Usage: scripts/bump-corpus.sh [<sha>]
#   <sha> defaults to argotorg/solidity develop HEAD.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
sha="${1:-$(git ls-remote https://github.com/argotorg/solidity.git refs/heads/develop | cut -f1)}"
[[ "$sha" =~ ^[0-9a-f]{40}$ ]] || { echo "not a full sha: $sha" >&2; exit 1; }
echo "$sha" > test/solidity-corpus.pin
echo "Pinned Solidity corpus at $sha."
echo "Now refresh the gas baselines (scripts/update-gas.sh) and commit both together."
