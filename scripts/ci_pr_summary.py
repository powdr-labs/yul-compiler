#!/usr/bin/env python3
"""Aggregate the per-leg CI summary files into a single Markdown PR comment.

Each CI leg tees its runner output into a file under a summary directory (see
.github/workflows/ci.yml). This script parses those files — it does not run any
tests — and emits Markdown covering parsing, correctness, gas, soundness, and a
final verdict. Job conclusions are passed via *_RESULT env vars so the verdict
can flag a leg that failed before it printed anything.

Usage: ci_pr_summary.py <summary-dir> [--sha SHA] > comment.md
"""
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

        m = re.match(r"(sorry_scan|axioms|spec_closure|spec_md)=(\S+)", ln)
        if m:
            data["soundness"][m.group(1)] = m.group(2)
            continue

    return data


def results_env():
    return {k: os.environ.get(f"{k.upper().replace('-', '_')}_RESULT", "")
            for k in ["build", "gas_runner", "solc_differential", "solidity_gas"]}


def fmt_int(n):
    return f"{n:,}"


def ratio_pct(ours, solc):
    if solc == 0:
        return "—"
    return f"{ours / solc * 100:.1f}%"


def gas_table(out, suites, compile_stats=None):
    """Render one gas table. `compile_stats` (suite -> compiled/eligible dict)
    adds a coverage column for pipelines where not every contract compiles."""
    coverage = compile_stats or {}
    out.append("| corpus | compiled | comparable | our gas | solc gas | ours/solc | regr | impr |")
    out.append("|---|--:|--:|--:|--:|--:|--:|--:|")
    tot_ours = tot_solc = tot_regr = tot_impr = 0
    for suite, g in sorted(suites.items()):
        tot_ours += g["ours"]; tot_solc += g["solc"]
        tot_regr += g["regressions"]; tot_impr += g["improved"]
        c = coverage.get(suite)
        compiled = f"{c['compiled']}/{c['eligible']}" if c else "—"
        out.append(f"| {suite} | {compiled} | {g['comparable']} | {fmt_int(g['ours'])} | "
                   f"{fmt_int(g['solc'])} | {ratio_pct(g['ours'], g['solc'])} | "
                   f"{g['regressions']} | {g['improved']} |")
    out.append(f"| **total** | | | **{fmt_int(tot_ours)}** | **{fmt_int(tot_solc)}** | "
               f"**{ratio_pct(tot_ours, tot_solc)}** | {tot_regr} | {tot_impr} |")
    return tot_regr


def build_comment(data, results, sha):
    out = []
    problems = []

    # ---- verdict inputs ----
    snd = data["soundness"]
    soundness_broken = any(snd.get(k) == "fail" for k in ("sorry_scan", "axioms", "spec_closure")) \
        or snd.get("spec_md") == "stale"
    if not snd and results["build"] == "failure":
        # build failed before/at the soundness step and produced no markers
        soundness_unknown = True
    else:
        soundness_unknown = False

    diff_unexpected = sum(max(0, d["failed"] - d["known"]) for d in data["differential"].values())
    compile_unexpected = sum(max(0, c["failed"] - c["known"]) for c in data["compile"].values())
    correctness_regressed = diff_unexpected > 0 or compile_unexpected > 0 \
        or results["solc_differential"] == "failure"

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
        out.append(f"<sub>commit `{sha[:9]}`</sub>")
    out.append("")

    # ---- 1. Parsing ----
    out.append("### 1. Parsing")
    s = data["syntax"]
    if s:
        out.append(f"- **Syntax corpus:** {fmt_int(s['ok'])} expected successes, "
                   f"{fmt_int(s['expfail'])} expected failures over {fmt_int(s['total'])} tests; "
                   f"{s['known']} known mismatches ({s['false_accepts']} false accepts, "
                   f"{s['false_rejects']} false rejects).")
    else:
        out.append("- _Syntax corpus: no result captured._")
    i = data["interpreter"]
    if i:
        out.append(f"- **Interpreter corpus:** {fmt_int(i['passed'])}/{fmt_int(i['total'])} passed "
                   f"({i['failed']} failed, {i['known']} known; {i['skipped']} skipped).")
    else:
        out.append("- _Interpreter corpus: no result captured._")
    out.append("")

    # ---- 2. Correctness ----
    out.append("### 2. Correctness")
    if data["compile"]:
        out.append("**Compilation (positive corpora):**")
        out.append("")
        out.append("| corpus | compiled | failed | known |")
        out.append("|---|--:|--:|--:|")
        for suite, c in sorted(data["compile"].items()):
            unexpected = max(0, c["failed"] - c["known"])
            mark = " ⚠️" if unexpected else ""
            out.append(f"| {suite} | {c['compiled']}/{c['total']} | {c['failed']}{mark} | {c['known']} |")
        out.append("")
    if data["differential"]:
        out.append("**Behaviour differential vs solc:**")
        out.append("")
        out.append("| corpus | matched | failed | known |")
        out.append("|---|--:|--:|--:|")
        for suite, d in sorted(data["differential"].items()):
            unexpected = max(0, d["failed"] - d["known"])
            mark = " ⚠️" if unexpected else ""
            out.append(f"| {suite} | {d['matched']}/{d['total']} | {d['failed']}{mark} | {d['known']} |")
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
        gas_table(out, vs_opt, data["gas_compile"])
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
        gas_table(out, codegen)
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
    args = [a for a in sys.argv[1:]]
    sha = ""
    if "--sha" in args:
        idx = args.index("--sha")
        sha = args[idx + 1]
        del args[idx:idx + 2]
    summary_dir = args[0] if args else "summaries"
    data = parse(read_lines(summary_dir))
    sys.stdout.write(build_comment(data, results_env(), sha))


if __name__ == "__main__":
    main()
