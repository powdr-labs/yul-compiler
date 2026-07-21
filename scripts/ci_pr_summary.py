#!/usr/bin/env python3
"""Aggregate the per-leg CI summary files into a single Markdown PR comment.

Each CI leg tees its runner output into a file under a summary directory (see
.github/workflows/ci.yml). This script parses those files — it does not run any
tests — and emits Markdown covering parsing, correctness, gas, soundness, and a
final verdict. Job conclusions are passed via *_RESULT env vars so the verdict
can flag a leg that failed before it printed anything.

Usage: ci_pr_summary.py <summary-dir> [--sha SHA]
       [--base-summary-dir DIR] [--base-sha SHA] > comment.md
"""
import argparse
import os
import re
import sys
import glob


def read_lines(summary_dir):
    lines = []
    for path in sorted(glob.glob(os.path.join(summary_dir, "**", "*.txt"), recursive=True)):
        with open(path, encoding="utf-8", errors="replace") as f:
            for line in f:
                lines.append(line.rstrip("\n"))
    return lines


def parse(lines):
    data = {
        "syntax": None,
        "interpreter": None,
        "compile": {},        # suite -> dict
        "differential": {},   # suite -> dict (behaviour, summed over shards)
        "gas": {},            # suite -> dict (summed over shards)
        "gas_rows": {},       # suite -> fixture -> dict
        "gas_compile": {},    # suite -> dict (compiled/unsupported, summed)
        "soundness": {},      # marker -> value
    }
    pending_gas = None        # most recent "Gas:" counts, attached to next totals
    pending_compiled = None   # most recent "Compiled .../..." for a gas suite

    for ln in lines:
        m = re.search(r"Checked (\d+) Solidity Yul syntax tests: (\d+) expected successes, "
                      r"(\d+) expected failures, (\d+) known parser mismatches "
                      r"\((\d+) false accepts, (\d+) false rejects\)", ln)
        if m:
            data["syntax"] = dict(zip(
                ["total", "ok", "expfail", "known", "false_accepts", "false_rejects"],
                map(int, m.groups())))
            continue

        m = re.search(r"Checked (\d+) latest-fork Solidity Yul interpreter tests: "
                      r"(\d+) passed, (\d+) failed \((\d+) known\); skipped (\d+)", ln)
        if m:
            data["interpreter"] = dict(zip(
                ["total", "passed", "failed", "known", "skipped"], map(int, m.groups())))
            continue

        m = re.search(r"Checked (\d+) latest-fork Solidity (.+?) tests: "
                      r"(\d+) compiled, (\d+) failed \((\d+) known\); skipped (\d+)", ln)
        if m:
            total, suite, comp, failed, known, skipped = m.groups()
            data["compile"][suite] = dict(total=int(total), compiled=int(comp),
                                          failed=int(failed), known=int(known),
                                          skipped=int(skipped))
            continue

        m = re.search(r"Differentially checked (\d+) latest-fork Solidity (.+?)"
                      r"(?: shard \d+/\d+)? tests against solc \S+: "
                      r"(\d+) matched, (\d+) failed \((\d+) known\); skipped (\d+)", ln)
        if m:
            total, suite, matched, failed, known, skipped = m.groups()
            d = data["differential"].setdefault(
                suite, dict(total=0, matched=0, failed=0, known=0, skipped=0))
            d["total"] += int(total); d["matched"] += int(matched)
            d["failed"] += int(failed); d["known"] += int(known); d["skipped"] += int(skipped)
            continue

        m = re.search(r"Compiled (\d+)/(\d+) latest-fork contracts via solc \S+ --via-ir "
                      r"\(skipped (\d+), unsupported (\d+)\)", ln)
        if m:
            pending_compiled = dict(zip(["compiled", "eligible", "skipped", "unsupported"],
                                        map(int, m.groups())))
            continue

        m = re.search(r"Gas: (\d+) comparable, (\d+) regressions, (\d+) improved, "
                      r"(\d+) changed(?: upstream)?, (\d+) unpinned, (\d+) stale", ln)
        if m:
            pending_gas = dict(zip(
                ["comparable", "regressions", "improved", "changed", "unpinned", "stale"],
                map(int, m.groups())))
            continue

        m = re.search(r"Gas totals: suite=(\S+) mode=(\S+) ours=(\d+) solc=(\d+) comparable=(\d+)", ln)
        if m:
            suite, mode = m.group(1), m.group(2)
            ours, solc, comparable = int(m.group(3)), int(m.group(4)), int(m.group(5))
            g = data["gas"].setdefault(
                suite, dict(mode=mode, ours=0, solc=0, comparable=0, regressions=0, improved=0))
            g["ours"] += ours; g["solc"] += solc; g["comparable"] += comparable
            if pending_gas:
                g["regressions"] += pending_gas["regressions"]
                g["improved"] += pending_gas["improved"]
            if pending_compiled:
                c = data["gas_compile"].setdefault(
                    suite, dict(compiled=0, eligible=0, unsupported=0))
                c["compiled"] += pending_compiled["compiled"]
                c["eligible"] += pending_compiled["eligible"]
                c["unsupported"] += pending_compiled["unsupported"]
            pending_gas = None
            pending_compiled = None
            continue

        fields = ln.split("\t")
        if len(fields) == 6 and fields[0] == "Gas row:":
            _, suite, mode, fixture, ours, solc = fields
            if ours.isdigit() and solc.isdigit():
                rows = data["gas_rows"].setdefault(suite, {})
                rows[fixture] = dict(mode=mode, ours=int(ours), solc=int(solc))
            continue

        m = re.match(r"(sorry_scan|axioms|spec_closure|spec_md)=(\S+)", ln)
        if m:
            data["soundness"][m.group(1)] = m.group(2)
            continue

    return data


def results_env(prefix=""):
    return {k: os.environ.get(f"{prefix}{k.upper().replace('-', '_')}_RESULT", "")
            for k in ["build", "gas_runner", "solc_differential", "solidity_gas"]}


def fmt_int(n):
    return f"{n:,}"


def fmt_delta(n):
    if n is None:
        return "—"
    if n == 0:
        return "0"
    sign = "+" if n > 0 else "−"
    return f"{sign}{fmt_int(abs(n))}"


def ratio_pct(ours, solc):
    if solc == 0:
        return "—"
    return f"{ours / solc * 100:.1f}%"


def gas_row_delta(suite, current, base, current_rows, base_rows):
    """Return (gas delta, added fixtures, dropped fixtures, exact comparison).

    New runner output supplies per-fixture rows, so totals are compared only on
    the intersection. The aggregate fallback keeps the first rollout useful
    while main still predates the row output.
    """
    if base is None:
        return None, 0, 0, False
    ours = current_rows.get(suite, {})
    theirs = base_rows.get(suite, {})
    if ours and theirs:
        shared = ours.keys() & theirs.keys()
        delta = sum(ours[name]["ours"] - theirs[name]["ours"] for name in shared)
        return delta, len(ours.keys() - theirs.keys()), len(theirs.keys() - ours.keys()), True
    return current["ours"] - base["ours"], 0, 0, False


def gas_table(out, suites, compile_stats=None, base_suites=None,
              current_rows=None, base_rows=None):
    """Render one gas table. `compile_stats` (suite -> compiled/eligible dict)
    adds a coverage column for pipelines where not every contract compiles."""
    coverage = compile_stats or {}
    base_suites = base_suites or {}
    current_rows = current_rows or {}
    base_rows = base_rows or {}
    out.append("| corpus | compiled | comparable | our gas | Δ vs main | solc gas | ours/solc | regr | impr |")
    out.append("|---|--:|--:|--:|--:|--:|--:|--:|--:|")
    tot_ours = tot_solc = tot_regr = tot_impr = 0
    tot_delta = 0
    have_delta = False
    coverage_changes = []
    used_fallback = False
    for suite, g in sorted(suites.items()):
        tot_ours += g["ours"]; tot_solc += g["solc"]
        tot_regr += g["regressions"]; tot_impr += g["improved"]
        c = coverage.get(suite)
        compiled = f"{c['compiled']}/{c['eligible']}" if c else "—"
        delta, added, dropped, exact = gas_row_delta(
            suite, g, base_suites.get(suite), current_rows, base_rows)
        if delta is not None:
            tot_delta += delta
            have_delta = True
            used_fallback = used_fallback or not exact
        if added or dropped:
            coverage_changes.append(f"`{suite}`: +{added}/−{dropped} comparable fixtures")
        out.append(f"| {suite} | {compiled} | {g['comparable']} | {fmt_int(g['ours'])} | "
                   f"{fmt_delta(delta)} | {fmt_int(g['solc'])} | {ratio_pct(g['ours'], g['solc'])} | "
                   f"{g['regressions']} | {g['improved']} |")
    out.append(f"| **total** | | | **{fmt_int(tot_ours)}** | **{fmt_delta(tot_delta) if have_delta else '—'}** | **{fmt_int(tot_solc)}** | "
               f"**{ratio_pct(tot_ours, tot_solc)}** | {tot_regr} | {tot_impr} |")
    if coverage_changes:
        out.append("")
        out.append("<sub>Coverage change vs main — " + "; ".join(coverage_changes) +
                   ". Gas deltas use only fixtures present in both runs.</sub>")
    elif used_fallback:
        out.append("")
        out.append("<sub>Gas delta uses aggregate totals because main predates per-fixture CI rows.</sub>")
    return tot_regr


def build_comment(data, results, sha, base=None, base_sha="", base_results=None):
    out = []
    problems = []

    # ---- verdict inputs ----
    snd = data["soundness"]
    soundness_broken = any(snd.get(k) == "fail" for k in ("sorry_scan", "axioms", "spec_closure")) \
        or snd.get("spec_md") == "stale"
    if not snd and results.get("build") == "failure":
        # build failed before/at the soundness step and produced no markers
        soundness_unknown = True
    else:
        soundness_unknown = False

    diff_unexpected = sum(max(0, d["failed"] - d["known"]) for d in data["differential"].values())
    compile_unexpected = sum(max(0, c["failed"] - c["known"]) for c in data["compile"].values())
    correctness_regressed = diff_unexpected > 0 or compile_unexpected > 0 \
        or results.get("solc_differential") == "failure"

    total_regressions = sum(g["regressions"] for g in data["gas"].values())
    benchmarks_worse = total_regressions > 0

    if soundness_broken:
        problems.append("🔴 **Soundness broken**")
    elif soundness_unknown:
        problems.append("🔴 **Soundness unverified** (build failed)")
    if correctness_regressed:
        problems.append("🔴 **Correctness regressions**")
    if benchmarks_worse:
        problems.append("🟠 **Gas regressions** (benchmarks worse)")
    # a leg that failed for some other reason
    for name, res in results.items():
        if res == "failure" and name not in ("solc_differential",) and not soundness_unknown:
            problems.append(f"🔴 **{name} job failed**")
            break

    verdict = "✅ **All good**" if not problems else " · ".join(dict.fromkeys(problems))

    out.append(f"## CI summary — {verdict}")
    if sha:
        revision = f"head `{sha[:9]}`"
        if base_sha:
            revision += f" · main `{base_sha[:9]}`"
        out.append(f"<sub>{revision}</sub>")
    if base and base_results:
        incomplete = [name.replace("_", " ") for name, result in base_results.items()
                      if result and result != "success"]
        if incomplete:
            out.append("")
            out.append("> ⚪ Main comparison is incomplete: " + ", ".join(incomplete) +
                       " did not succeed.")
    out.append("")

    # ---- 1. Parsing ----
    out.append("### 1. Parsing")
    s = data["syntax"]
    if s:
        out.append(f"- **Syntax corpus:** {fmt_int(s['ok'])} expected successes, "
                   f"{fmt_int(s['expfail'])} expected failures over {fmt_int(s['total'])} tests; "
                   f"{s['known']} known mismatches ({s['false_accepts']} false accepts, "
                   f"{s['false_rejects']} false rejects).")
        if base and base["syntax"]:
            b = base["syntax"]
            out.append(f"  - Δ vs main: successes {fmt_delta(s['ok'] - b['ok'])}, "
                       f"expected failures {fmt_delta(s['expfail'] - b['expfail'])}, "
                       f"mismatches {fmt_delta(s['known'] - b['known'])}.")
    else:
        out.append("- _Syntax corpus: no result captured._")
    i = data["interpreter"]
    if i:
        out.append(f"- **Interpreter corpus:** {fmt_int(i['passed'])}/{fmt_int(i['total'])} passed "
                   f"({i['failed']} failed, {i['known']} known; {i['skipped']} skipped).")
        if base and base["interpreter"]:
            b = base["interpreter"]
            out.append(f"  - Δ vs main: passed {fmt_delta(i['passed'] - b['passed'])}, "
                       f"failed {fmt_delta(i['failed'] - b['failed'])}, "
                       f"known {fmt_delta(i['known'] - b['known'])}.")
    else:
        out.append("- _Interpreter corpus: no result captured._")
    out.append("")

    # ---- 2. Correctness ----
    out.append("### 2. Correctness")
    if data["compile"]:
        out.append("**Compilation (positive corpora):**")
        out.append("")
        out.append("| corpus | compiled | Δ compiled | failed | Δ failed | known |")
        out.append("|---|--:|--:|--:|--:|--:|")
        for suite, c in sorted(data["compile"].items()):
            unexpected = max(0, c["failed"] - c["known"])
            mark = " ⚠️" if unexpected else ""
            b = base["compile"].get(suite) if base else None
            out.append(f"| {suite} | {c['compiled']}/{c['total']} | "
                       f"{fmt_delta(c['compiled'] - b['compiled']) if b else '—'} | "
                       f"{c['failed']}{mark} | "
                       f"{fmt_delta(c['failed'] - b['failed']) if b else '—'} | {c['known']} |")
        out.append("")
    if data["differential"]:
        out.append("**Behaviour differential vs solc:**")
        out.append("")
        out.append("| corpus | matched | Δ matched | failed | Δ failed | known |")
        out.append("|---|--:|--:|--:|--:|--:|")
        for suite, d in sorted(data["differential"].items()):
            unexpected = max(0, d["failed"] - d["known"])
            mark = " ⚠️" if unexpected else ""
            b = base["differential"].get(suite) if base else None
            out.append(f"| {suite} | {d['matched']}/{d['total']} | "
                       f"{fmt_delta(d['matched'] - b['matched']) if b else '—'} | "
                       f"{d['failed']}{mark} | "
                       f"{fmt_delta(d['failed'] - b['failed']) if b else '—'} | {d['known']} |")
        out.append("")
    if not data["compile"] and not data["differential"]:
        out.append("- _No correctness results captured._")
        out.append("")

    # ---- 3. Gas ----
    out.append("### 3. Gas")
    vs_opt = {s: g for s, g in data["gas"].items() if g.get("mode") == "vs_solc_optimized"}
    codegen = {s: g for s, g in data["gas"].items() if g.get("mode") == "codegen"}
    if vs_opt:
        out.append("")
        out.append("**a) This compiler vs solc's optimized output** — we compile solc's "
                   "*unoptimized* `--via-ir` Yul; solc is fully optimized (`--optimize --via-ir`). "
                   "The `uniswap-v4` corpus is real Uniswap v4-core library code "
                   "(see test/uniswap-v4).")
        out.append("")
        base_vs_opt = ({s: g for s, g in base["gas"].items()
                        if g.get("mode") == "vs_solc_optimized"} if base else {})
        gas_table(out, vs_opt, data["gas_compile"], base_vs_opt,
                  data["gas_rows"], base["gas_rows"] if base else {})
        out.append("")
        out.append("<sub>ours/solc **> 100% is expected**: this compiler has no Yul optimizer yet, "
                   "so it spends more gas than solc's optimized output. This number is the size of "
                   "that gap. It does not fail CI; only a regression above the pinned baseline does.</sub>")
        out.append("")
    if codegen:
        out.append("**b) Backend codegen parity** — both this compiler and solc assemble the "
                   "*same, unoptimized* Yul (solc `--strict-assembly`, no `--optimize`). This isolates "
                   "code generation from optimization.")
        out.append("")
        base_codegen = ({s: g for s, g in base["gas"].items()
                         if g.get("mode") == "codegen"} if base else {})
        gas_table(out, codegen, base_suites=base_codegen,
                  current_rows=data["gas_rows"], base_rows=base["gas_rows"] if base else {})
        out.append("")
        out.append("<sub>Here ours/solc near 100% is expected — neither side optimizes, so this "
                   "compares raw code generation on identical input, not optimizer quality.</sub>")
        out.append("")
    if not data["gas"]:
        out.append("- _No gas results captured._")
        out.append("")

    # ---- 4. Soundness ----
    out.append("### 4. Soundness (formal guarantee)")
    def mark(cond, ok_txt, bad_txt):
        return f"✅ {ok_txt}" if cond else f"🔴 {bad_txt}"
    if snd:
        out.append(f"- **No `sorry` in sources:** "
                   f"{mark(snd.get('sorry_scan') == 'pass', 'clean', 'a sorry is present')}")
        out.append(f"- **Axiom footprint:** "
                   f"{mark(snd.get('axioms') == 'pass', 'sorry-free, standard axioms only', 'axiom set changed / sorry present')}")
        out.append(f"- **Spec closure:** "
                   f"{mark(snd.get('spec_closure') == 'pass', 'audited spec surface pinned', 'audited spec surface changed')}")
        out.append(f"- **SPEC.md:** "
                   f"{mark(snd.get('spec_md') == 'uptodate', 'up to date', 'stale — re-run SpecClosure.lean')}")
    elif soundness_unknown:
        out.append("- 🔴 _Build failed before soundness checks ran — guarantee unverified._")
    else:
        out.append("- _No soundness result captured._")
    out.append("")

    # ---- 5. Verdict ----
    out.append("### 5. Verdict")
    out.append(verdict)
    if problems:
        out.append("")
        out.append("See the failing job logs above for details.")
    return "\n".join(out) + "\n"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("summary_dir", nargs="?", default="summaries")
    parser.add_argument("--sha", default="")
    parser.add_argument("--base-summary-dir")
    parser.add_argument("--base-sha", default="")
    args = parser.parse_args()
    data = parse(read_lines(args.summary_dir))
    base = parse(read_lines(args.base_summary_dir)) if args.base_summary_dir else None
    sys.stdout.write(build_comment(data, results_env(), args.sha, base, args.base_sha,
                                   results_env("MAIN_")))


if __name__ == "__main__":
    main()
