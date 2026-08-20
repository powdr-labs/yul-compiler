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
    # Two shards of one suite, to check they are summed rather than overwritten.
    "Compile time: suite=optimizer mode=codegen ours_ms=4000 solc_ms=8000 "
    "frontend_ms=0 fixtures=5 rejected_ms=0 rejected=0 unpaired_ms=0 unpaired=0",
    "Compile time: suite=optimizer mode=codegen ours_ms=2000 solc_ms=4000 "
    "frontend_ms=0 fixtures=3 rejected_ms=0 rejected=0 unpaired_ms=0 unpaired=0",
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
    "Compile time: suite=optimizer mode=codegen ours_ms=5000 solc_ms=11000 "
    "frontend_ms=0 fixtures=8 rejected_ms=0 rejected=0 unpaired_ms=0 unpaired=0",
]

AAVE_LINES = [
    "Compiled 1/4 latest-fork contracts via solc 0.8.35 --via-ir "
    "(skipped 0, unsupported 3).",
    "Gas: 10 comparable, 0 regressions, 0 improved, 0 changed, 0 unpinned, 0 stale.",
    "Gas totals: suite=aave-v4 mode=vs_solc_optimized ours=54544009 "
    "solc=18236226 comparable=10",
    "Gas row:\taave-v4\tvs_solc_optimized\tPositionStatusMap.sol:nextContinuousTenThousand()\t"
    "21450571\t5975804",
    "Compile time: suite=aave-v4 mode=vs_solc_optimized ours_ms=125000 solc_ms=60000 "
    "frontend_ms=30000 fixtures=4 rejected_ms=90000 rejected=3 unpaired_ms=0 unpaired=0",
]


class SummaryTest(unittest.TestCase):
    def test_renders_aave_gas_corpus_row(self):
        rendered = summary.build_comment(summary.parse(AAVE_LINES), {}, sha="")

        self.assertIn(
            "| aave-v4 | 1/4 | 10 | 54,544,009 | — | 18,236,226 | 299.1% | — | 0 | 0 |",
            rendered)
        self.assertIn("`uniswap-v4` and `aave-v4` corpora", rendered)

    def test_parses_machine_readable_gas_rows(self):
        data = summary.parse(HEAD_LINES)
        self.assertEqual(data["gas_rows"]["optimizer"]["shared.yul"]["ours"], 100)
        self.assertEqual(data["gas"]["optimizer"]["ours"], 260)

    def test_renders_corpus_pin_and_drift(self):
        rendered = summary.build_comment(
            summary.parse(HEAD_LINES), {}, sha="a" * 40,
            corpus={"pin": "f" * 40, "behind": 14, "base_pin": "f" * 40})
        self.assertIn("corpus `fffffffff`", rendered)
        self.assertIn("**14 commits behind** argotorg/solidity develop", rendered)
        self.assertNotIn("moves the corpus pin", rendered)

    def test_renders_up_to_date_corpus_pin(self):
        rendered = summary.build_comment(
            summary.parse(HEAD_LINES), {}, sha="a" * 40,
            corpus={"pin": "f" * 40, "behind": 0, "base_pin": ""})
        self.assertIn("up to date with argotorg/solidity develop", rendered)

    def test_warns_when_pr_moves_the_corpus_pin(self):
        rendered = summary.build_comment(
            summary.parse(HEAD_LINES), {}, sha="a" * 40,
            corpus={"pin": "f" * 40, "behind": None, "base_pin": "e" * 40})
        self.assertIn("moves the corpus pin (main: `eeeeeeeee`)", rendered)
        self.assertNotIn("behind** argotorg/solidity develop", rendered)

    def test_omits_corpus_line_without_a_pin(self):
        rendered = summary.build_comment(summary.parse(HEAD_LINES), {}, sha="a" * 40)
        self.assertNotIn("corpus", rendered.split("###")[0])

    def test_renders_deltas_against_main(self):
        head = summary.parse(HEAD_LINES)
        main = summary.parse(MAIN_LINES)
        rendered = summary.build_comment(
            head, {}, "abcdef123456", main, "0123456789ab")

        self.assertIn("head `abcdef123` · main `012345678`", rendered)
        self.assertIn("Δ vs main: successes +1, expected failures −1, mismatches 0", rendered)
        self.assertIn("| ours/solc | Δ ratio vs main |", rendered)
        self.assertIn("| optimizer | 5/6 | +1 | 1 | −1 | 1 |", rendered)
        self.assertIn(
            "| optimizer | — | 2 | 260 | −50 | 250 | 104.0% | −50.0 pp | 0 | 1 |",
            rendered)
        self.assertIn(
            "| **total** | | | **260** | **−50** | **250** | **104.0%** | "
            "**−50.0 pp** | 0 | 1 |",
            rendered)
        self.assertIn("`optimizer`: +1/−1 comparable fixtures", rendered)
        self.assertIn("Gas and ratio deltas use only fixtures present in both runs", rendered)

    def test_aggregate_fallback_supports_old_main_output(self):
        head = summary.parse(HEAD_LINES)
        old_main = summary.parse([line for line in MAIN_LINES if not line.startswith("Gas row:")])
        rendered = summary.build_comment(head, {}, base=old_main, sha="")

        self.assertIn(
            "| optimizer | — | 2 | 260 | −60 | 250 | 104.0% | −2.7 pp | 0 | 1 |",
            rendered)
        self.assertIn("main predates per-fixture CI rows", rendered)

    def test_sums_compiler_runtime_across_shards(self):
        t = summary.parse(HEAD_LINES)["runtime"]["optimizer"]
        self.assertEqual(t, dict(mode="codegen", ours_ms=6000, solc_ms=12000,
                                 frontend_ms=0, fixtures=8, rejected_ms=0,
                                 rejected=0, unpaired_ms=0, unpaired=0))

    def test_renders_compiler_runtime_against_main(self):
        rendered = summary.build_comment(
            summary.parse(HEAD_LINES), {}, "abcdef123456",
            summary.parse(MAIN_LINES), "0123456789ab")

        self.assertIn("### 4. Compiler runtime (informational)", rendered)
        # 6.0 s over 8 fixtures vs main's 5.0 s over 8: +20% both in total and
        # per fixture, and half of solc's 12.0 s.
        self.assertIn(
            "| optimizer | 8 | 6.0 s | +20.0% | 750 ms | +20.0% | 12.0 s | 50.0% |",
            rendered)
        self.assertIn(
            "| **total** | 8 | **6.0 s** | **+20.0%** | 750 ms | **+20.0%** | "
            "**12.0 s** | **50.0%** |",
            rendered)
        self.assertIn("Nothing here affects the verdict.", rendered)
        # The runtime section must not displace the sections after it.
        self.assertIn("### 5. Soundness (formal guarantee)", rendered)
        self.assertIn("### 6. Verdict", rendered)

    def test_compiler_runtime_per_fixture_mean_absorbs_corpus_drift(self):
        """Main ran the same suite twice as slowly per fixture on half as many."""
        head = summary.parse(HEAD_LINES)
        main = summary.parse([
            line if not line.startswith("Compile time:") else
            "Compile time: suite=optimizer mode=codegen ours_ms=6000 solc_ms=11000 "
            "frontend_ms=0 fixtures=4 rejected_ms=0 rejected=0 unpaired_ms=0 unpaired=0"
            for line in MAIN_LINES])
        rendered = summary.build_comment(head, {}, "", main, "")

        # The suite costs the same wall-clock as on main, so the total says
        # nothing — but it now covers twice the fixtures at half the cost each.
        # The mean is the figure that survives a corpus that changed size.
        self.assertIn("| optimizer | 8 | 6.0 s | ≈0% | 750 ms | −50.0% |", rendered)

    def test_renders_runtime_without_a_main_baseline(self):
        """Main predating this output must degrade to '—', not crash or mislead."""
        rendered = summary.build_comment(summary.parse(AAVE_LINES), {}, sha="")

        self.assertIn("| aave-v4 | 4 | 2.1 min | — | 31.2 s | — | 1.0 min | 208.3% |",
                      rendered)
        self.assertIn("30.0 s of solc `--ir` front-end lowering", rendered)
        # Time spent on rejected fixtures is surfaced, not folded into the total.
        self.assertIn("1.5 min this compiler spent on 3 fixture(s) it then rejected",
                      rendered)

    def test_excludes_fixtures_solc_would_not_compile_from_both_sides(self):
        """A fixture only one compiler finished is counted on neither side."""
        rendered = summary.build_comment(summary.parse([
            "Compile time: suite=aave-v4 mode=vs_solc_optimized ours_ms=100 solc_ms=40 "
            "frontend_ms=10 fixtures=4 rejected_ms=0 rejected=0 unpaired_ms=7000 unpaired=2",
        ]), {}, sha="")

        # Only the 4 paired fixtures reach the table; the 7 s spent on the two
        # solc would not compile is reported apart, not folded into our column.
        self.assertIn("| aave-v4 | 4 | 100 ms | — | 25 ms | — | 40 ms | 250.0% |", rendered)
        self.assertIn("7.0 s on 2 fixture(s) this compiler compiled but solc would not",
                      rendered)

    def test_reports_missing_compiler_runtime(self):
        rendered = summary.build_comment(
            summary.parse([line for line in HEAD_LINES
                           if not line.startswith("Compile time:")]), {}, sha="")

        self.assertIn("_No compiler runtime captured._", rendered)

    def test_formats_durations_at_a_readable_scale(self):
        self.assertEqual(summary.fmt_duration(0), "0 ms")
        self.assertEqual(summary.fmt_duration(999), "999 ms")
        self.assertEqual(summary.fmt_duration(1_500), "1.5 s")
        self.assertEqual(summary.fmt_duration(90_000), "1.5 min")

    def test_formats_runtime_deltas_as_signed_percentages(self):
        self.assertEqual(summary.fmt_pct_delta(110, 100), "+10.0%")
        self.assertEqual(summary.fmt_pct_delta(90, 100), "−10.0%")
        self.assertEqual(summary.fmt_pct_delta(100.2, 100), "≈0%")
        self.assertEqual(summary.fmt_pct_delta(100, None), "—")
        self.assertEqual(summary.fmt_pct_delta(100, 0), "—")

    def test_formats_ratio_delta_in_percentage_points(self):
        self.assertEqual(summary.fmt_ratio_delta(1.24), "+1.2 pp")
        self.assertEqual(summary.fmt_ratio_delta(-0.26), "−0.3 pp")
        self.assertEqual(summary.fmt_ratio_delta(0.01), "0.0 pp")
        self.assertEqual(summary.fmt_ratio_delta(None), "—")


if __name__ == "__main__":
    unittest.main()
