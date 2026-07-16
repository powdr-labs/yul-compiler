#!/usr/bin/env bash
#
# update-spec.sh — re-pin the audited specification boundary.
#
# Run this ONLY after a *legitimate, human-intended* change to the audited spec
# surface (a match relation, a theorem statement, a data type, the external
# semantics pins, …). It regenerates SPEC.md and rewrites the `#guard_msgs`
# pin inside SpecClosure.lean so CI passes again.
#
# The resulting `git diff` is the audit artifact: it shows exactly which audited
# declarations changed. Review it, confirm the change is a strengthening/fix and
# not an accidental weakening, then commit SpecClosure.lean and SPEC.md together.
# A human code-owner must approve the change (see .github/CODEOWNERS); automated
# agents must not run this to self-approve a spec change (see AGENTS.md).
#
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

echo "==> Re-pinning SpecClosure.lean and regenerating SPEC.md"
# First pass rewrites the pinned block in place (SPEC_REPIN=1). The #guard_msgs
# check in the *same* elaboration still compares against the OLD pin and reports
# a mismatch — that is expected here, hence the '|| true'. The file on disk is
# updated as a side effect before the check runs.
SPEC_REPIN=1 lake env lean SpecClosure.lean || true

echo "==> Verifying the freshly pinned file elaborates cleanly"
lake env lean SpecClosure.lean

echo
echo "==> Done. Review the diff — this is the audit artifact:"
git --no-pager diff --stat -- SpecClosure.lean SPEC.md
echo
echo "Next: read the changed declarations, confirm the spec change is intended,"
echo "then commit SpecClosure.lean and SPEC.md together for human code-owner review."
