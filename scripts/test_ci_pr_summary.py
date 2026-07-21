#!/usr/bin/env python3
import unittest

import ci_pr_summary as summary


HEAD_LINES = [
    "Checked 10 Solidity Yul syntax tests: 7 expected successes, 3 expected failures, "
    "0 known parser mismatches (0 false accepts, 0 false rejects)",
    "Checked 5 latest-fork Solidity Yul interpreter tests: 4 passed, 1 failed "
    "(1 known); skipped 0",
    "Checked 6 latest-fork Solidity optimizer tests: 5 compiled, 1 failed (1 known); "
    "skipped 0",
    "Differentially checked 6 latest-fork Solidity optimizer tests against solc 0.8.35: "
    "5 matched, 1 failed (1 known); skipped 0",
    "Gas: 2 comparable, 0 regressions, 1 improved, 0 changed upstream, 0 unpinned, 0 stale",
    "Gas totals: suite=optimizer mode=codegen ours=260 solc=250 comparable=2",
    "Gas row:\toptimizer\tcodegen\tshared.yul\t100\t100",
    "Gas row:\toptimizer\tcodegen\tadded.yul\t160\t150",
    "sorry_scan=pass",
    "axioms=pass",
    "spec_closure=pass",
    "spec_md=uptodate",
]

MAIN_LINES = [
    "Checked 10 Solidity Yul syntax tests: 6 expected successes, 4 expected failures, "
    "0 known parser mismatches (0 false accepts, 0 false rejects)",
    "Checked 5 latest-fork Solidity Yul interpreter tests: 3 passed, 2 failed "
    "(2 known); skipped 0",
    "Checked 6 latest-fork Solidity optimizer tests: 4 compiled, 2 failed (2 known); "
    "skipped 0",
    "Differentially checked 6 latest-fork Solidity optimizer tests against solc 0.8.35: "
    "4 matched, 2 failed (2 known); skipped 0",
    "Gas: 2 comparable, 0 regressions, 0 improved, 0 changed upstream, 0 unpinned, 0 stale",
    "Gas totals: suite=optimizer mode=codegen ours=320 solc=300 comparable=2",
    "Gas row:\toptimizer\tcodegen\tshared.yul\t150\t100",
    "Gas row:\toptimizer\tcodegen\tdropped.yul\t170\t200",
]


class SummaryTest(unittest.TestCase):
    def test_parses_machine_readable_gas_rows(self):
        data = summary.parse(HEAD_LINES)
        self.assertEqual(data["gas_rows"]["optimizer"]["shared.yul"]["ours"], 100)
        self.assertEqual(data["gas"]["optimizer"]["ours"], 260)

    def test_renders_deltas_against_main(self):
        head = summary.parse(HEAD_LINES)
        main = summary.parse(MAIN_LINES)
        rendered = summary.build_comment(
            head, {}, "abcdef123456", main, "0123456789ab")

        self.assertIn("head `abcdef123` · main `012345678`", rendered)
        self.assertIn("Δ vs main: successes +1, expected failures −1, mismatches 0", rendered)
        self.assertIn("| optimizer | 5/6 | +1 | 1 | −1 | 1 |", rendered)
        self.assertIn("| optimizer | — | 2 | 260 | −50 | 250 | 104.0% | 0 | 1 |", rendered)
        self.assertIn("`optimizer`: +1/−1 comparable fixtures", rendered)
        self.assertIn("Gas deltas use only fixtures present in both runs", rendered)

    def test_aggregate_fallback_supports_old_main_output(self):
        head = summary.parse(HEAD_LINES)
        old_main = summary.parse([line for line in MAIN_LINES if not line.startswith("Gas row:")])
        rendered = summary.build_comment(head, {}, base=old_main, sha="")

        self.assertIn("| optimizer | — | 2 | 260 | −60 | 250 | 104.0% | 0 | 1 |", rendered)
        self.assertIn("main predates per-fixture CI rows", rendered)


if __name__ == "__main__":
    unittest.main()
