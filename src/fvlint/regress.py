# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Manifest-driven regression runner.

A manifest (TOML) lists cases: a design, a top module, fvlint arguments and
the expected status of each check.  Every case runs in its own fvlint
process (optionally once per proof engine), and is compared against its
expectations and a time budget.  The same runner serves fvlint's own test
suite and a user's IP library (point `files`/`filelist` at your cores).

    python -m fvlint.regress tests/regress/manifest.toml -j 4
    python -m fvlint.regress my_ip.toml --record      # print expectations for new cases

Manifest format:

    [defaults]
    budget_s = 120              # wall-clock budget per case run
    engines = ["auto"]          # or ["pdr", "smtbmc"] to run each case per engine

    [[case]]
    name = "counters/cnt_mod100"
    files = ["../fixtures/counters.sv"]     # relative to the manifest
    # filelist = "cores/foo.f"               # alternatively, a .f file list
    top = "cnt_mod100"
    args = ["--frontend", "slang"]           # extra fvlint arguments
    expect = { "counter_overflow:q" = "PROVEN" }
    strict = false              # true: checks not listed in `expect` fail the case
    exit = 0                    # expected exit code (default: derived from expect)
    expect_error = "..."        # the run must abort (exit 2) with this text on stderr
    expect_detail = { "id" = "text that must appear in the detail" }
    tags = ["counter"]
    budget_s = 60
"""

from __future__ import annotations

import argparse
import fnmatch
import json
import os
import subprocess
import sys
import time
import tomllib
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from xml.sax.saxutils import escape, quoteattr

BAD = {"FAIL", "ERROR", "VACUOUS"}


@dataclass
class Case:
    name: str
    top: str
    files: list
    filelist: str | None
    args: list
    expect: dict
    strict: bool
    exit: int | None
    expect_error: str | None
    expect_detail: dict
    tags: list
    budget_s: float
    engines: list
    base: str


@dataclass
class Outcome:
    case: Case
    engine: str
    ok: bool
    skipped: bool = False
    seconds: float = 0.0
    problems: list = field(default_factory=list)
    statuses: dict = field(default_factory=dict)
    out: str = ""


def load_manifest(path: str) -> list:
    with open(path, "rb") as f:
        data = tomllib.load(f)
    base = os.path.dirname(os.path.abspath(path))
    d = data.get("defaults", {})
    cases = []
    for c in data.get("case", []):
        cases.append(Case(
            name=c["name"], top=c["top"],
            files=[os.path.normpath(os.path.join(base, x)) for x in c.get("files", [])],
            filelist=os.path.normpath(os.path.join(base, c["filelist"])) if c.get("filelist") else None,
            args=[a.replace("{dir}", base) for a in c.get("args", [])],
            expect=c.get("expect", {}), strict=c.get("strict", d.get("strict", False)),
            exit=c.get("exit"), expect_error=c.get("expect_error"),
            expect_detail=c.get("expect_detail", {}), tags=c.get("tags", []),
            budget_s=float(c.get("budget_s", d.get("budget_s", 120))),
            engines=c.get("engines", d.get("engines", ["auto"])), base=base))
    return cases


def _env():
    env = dict(os.environ)
    pkg_parent = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    env["PYTHONPATH"] = pkg_parent + (os.pathsep + env["PYTHONPATH"] if env.get("PYTHONPATH") else "")
    return env


def run_case(case: Case, engine: str, outroot: str, budget_scale: float, abc: bool) -> Outcome:
    o = Outcome(case, engine, ok=False)
    if engine == "pdr" and not abc:
        o.ok, o.skipped = True, True
        o.problems.append("skipped: no yosys-abc for the PDR engine")
        return o
    out = os.path.join(outroot, case.name.replace("/", "__") + f"__{engine}")
    o.out = out
    cmd = [sys.executable, "-m", "fvlint", "--top", case.top, "-o", out, "-j", "1",
           "--engine", engine, *case.files, *case.args]
    if case.filelist:
        cmd += ["-f", case.filelist]
    t0 = time.time()
    budget = case.budget_s * budget_scale
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, env=_env(), timeout=budget * 3 + 60)
        rc, err = p.returncode, p.stderr
    except subprocess.TimeoutExpired:
        o.seconds = time.time() - t0
        o.problems.append(f"killed after {o.seconds:.0f}s (budget {budget:.0f}s)")
        return o
    o.seconds = time.time() - t0
    if case.expect_error is not None:
        if rc != 2:
            o.problems.append(f"expected an abort (exit 2), got exit {rc}")
        if case.expect_error not in err:
            o.problems.append(f"stderr lacks {case.expect_error!r}")
        o.ok = not o.problems
        return o
    res_path = os.path.join(out, "results.json")
    if rc == 2 or not os.path.exists(res_path):
        o.problems.append(f"fvlint aborted (exit {rc}): {err.strip().splitlines()[-1] if err.strip() else ''}")
        return o
    with open(res_path) as f:
        results = {r["id"]: r for r in json.load(f)["results"]}
    o.statuses = {k: v["status"] for k, v in results.items()}
    for cid, want in case.expect.items():
        got = o.statuses.get(cid, "missing")
        if got != want:
            o.problems.append(f"{cid}: expected {want}, got {got}"
                              + (f" ({results[cid]['detail'][:120]})" if cid in results else ""))
    for cid, text in case.expect_detail.items():
        if cid not in results or text not in results[cid]["detail"]:
            o.problems.append(f"{cid}: detail lacks {text!r}")
    for cid, st in o.statuses.items():
        if cid in case.expect:
            continue
        if case.strict:
            o.problems.append(f"{cid}: unexpected check ({st})")
        elif st in BAD:
            o.problems.append(f"{cid}: unexpected {st}")
    want_exit = case.exit
    if want_exit is None:
        want_exit = 1 if any(v in BAD for v in o.statuses.values()) else 0
    if rc != want_exit:
        o.problems.append(f"exit code {rc}, expected {want_exit}")
    if o.seconds > budget:
        o.problems.append(f"took {o.seconds:.1f}s, budget {budget:.0f}s")
    o.ok = not o.problems
    return o


def _select(cases, patterns):
    if not patterns:
        return cases
    return [c for c in cases if any(fnmatch.fnmatch(c.name, p) or p in c.tags or p in c.name
                                    for p in patterns)]


def write_junit(outcomes, path):
    lines = ['<?xml version="1.0" encoding="UTF-8"?>',
             f'<testsuite name="fvlint-regress" tests="{len(outcomes)}" '
             f'failures="{sum(not o.ok for o in outcomes)}" skipped="{sum(o.skipped for o in outcomes)}">']
    for o in outcomes:
        lines.append(f'  <testcase classname={quoteattr(o.case.name.split("/")[0])} '
                     f'name={quoteattr(o.case.name + " [" + o.engine + "]")} time="{o.seconds:.2f}">')
        if o.skipped:
            lines.append(f"    <skipped message={quoteattr('; '.join(o.problems))}/>")
        elif not o.ok:
            lines.append(f"    <failure message={quoteattr('regression')}>{escape(chr(10).join(o.problems))}</failure>")
        lines.append("  </testcase>")
    lines.append("</testsuite>")
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")


def record(outcomes) -> str:
    """TOML `expect` tables reflecting what actually happened."""
    out = []
    for o in outcomes:
        if o.skipped:
            continue
        body = ", ".join(f'"{k}" = "{v}"' for k, v in sorted(o.statuses.items()))
        out.append(f"# {o.case.name} [{o.engine}] ({o.seconds:.1f}s)\nexpect = {{ {body} }}\n")
    return "\n".join(out)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="fvlint-regress", description=__doc__.split("\n\n")[0])
    ap.add_argument("manifests", nargs="*", help="manifest TOML file(s); default: fvlint's own")
    ap.add_argument("-k", dest="patterns", action="append", default=[],
                    help="only cases whose name/tag matches (glob or substring); repeatable")
    ap.add_argument("--engines", help="override engines, e.g. pdr,smtbmc")
    ap.add_argument("-j", "--jobs", type=int, default=max(1, (os.cpu_count() or 2) // 2))
    ap.add_argument("-o", "--out", default="fvlint_regress")
    ap.add_argument("--junit", help="JUnit XML output")
    ap.add_argument("--budget-scale", type=float, default=float(os.environ.get("FVLINT_BUDGET_SCALE", 1)),
                    help="multiply time budgets (slow machines, WebAssembly toolchain)")
    ap.add_argument("--record", action="store_true", help="print observed expectations as TOML")
    ap.add_argument("--fuzz", type=int, default=0, help="also run N soundness-fuzzer seeds")
    ap.add_argument("--list", action="store_true", help="list selected cases and exit")
    args = ap.parse_args(argv)

    manifests = args.manifests or [os.path.join(os.path.dirname(__file__), "..", "..", "tests",
                                                "regress", "manifest.toml")]
    cases = []
    for m in manifests:
        cases += load_manifest(m)
    cases = _select(cases, args.patterns)
    runs = []
    for c in cases:
        for e in (args.engines.split(",") if args.engines else c.engines):
            runs.append((c, e))
    if args.list:
        for c, e in runs:
            print(f"{c.name} [{e}] tags={','.join(c.tags)} budget={c.budget_s:.0f}s")
        return 0

    from .tools import Toolchain, ToolError
    try:
        tools = Toolchain.discover()
    except ToolError as e:
        print(f"fvlint-regress: {e}", file=sys.stderr)
        return 2
    os.makedirs(args.out, exist_ok=True)
    t0 = time.time()
    with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as ex:
        outcomes = list(ex.map(lambda ce: run_case(ce[0], ce[1], args.out, args.budget_scale,
                                                   bool(tools.abc)), runs))
    for o in outcomes:
        mark = "SKIP" if o.skipped else ("PASS" if o.ok else "FAIL")
        print(f"{mark:4}  {o.case.name:<40} [{o.engine:6}] {o.seconds:6.1f}s")
        for p in ([] if o.ok else o.problems):
            print(f"        {p}")
    fuzz_ok = True
    if args.fuzz:
        from . import fuzz
        s = fuzz.run(range(1, args.fuzz + 1), os.path.join(args.out, "fuzz"))
        fuzz_ok = not s["problems"]
        print(f"{'PASS' if fuzz_ok else 'FAIL'}  soundness fuzzer: {s['seeds']} designs, {s['checks']} checks "
              f"{s['statuses']}, {len(s['inconclusive'])} beyond the oracle's reach, {s['seconds']}s")
        for p in s["problems"]:
            print(f"        {p}")
    failed = sum(not o.ok for o in outcomes)
    print(f"\n{len(outcomes) - failed}/{len(outcomes)} case runs passed "
          f"({sum(o.skipped for o in outcomes)} skipped) in {time.time() - t0:.0f}s")
    if args.junit:
        write_junit(outcomes, args.junit)
    with open(os.path.join(args.out, "summary.json"), "w") as f:
        json.dump([{"case": o.case.name, "engine": o.engine, "ok": o.ok, "skipped": o.skipped,
                    "seconds": round(o.seconds, 2), "problems": o.problems, "statuses": o.statuses}
                   for o in outcomes], f, indent=2)
    if args.record:
        print("\n" + record(outcomes))
    return 0 if failed == 0 and fuzz_ok else 1


if __name__ == "__main__":
    sys.exit(main())
