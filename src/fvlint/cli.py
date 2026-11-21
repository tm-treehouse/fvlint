# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""fvlint command line."""

from __future__ import annotations

import argparse
import os
import re
import sys
import time
from concurrent.futures import ThreadPoolExecutor

from . import __version__
from .checks import ERROR, FAIL, UNKNOWN, WAIVED, Result
from .detect import detect_all
from .elaborate import Sources, elaborate
from .fsm import analyse_fsms
from .netlist import Netlist, display_path
from .prove import Options, Prover, Reset
from .report import console, write_json, write_junit
from .tools import Toolchain, ToolError
from .waivers import Waivers

KINDS = ["counter_overflow", "counter_underflow", "parallel_case", "full_case", "index_range",
         "mem_addr", "fsm_unreachable", "fsm_trap", "fsm_reset", "fsm_summary"]

_RESET_RE = re.compile(r"(^|_)(a?rst|a?reset|rst_?sync)(_?n|_ni|_b|_i)?$", re.I)


def find_reset(nl: Netlist, spec: str | None):
    """Pick the reset port: explicit --reset NAME[:LEVEL] or a name heuristic."""
    if spec:
        name, _, lvl = spec.partition(":")
        if name not in nl.ports:
            raise SystemExit(f"fvlint: --reset port {name!r} not found on top module")
        bits = nl.ports[name]["bits"]
        active = int(lvl) if lvl else (0 if re.search(r"(n|_ni|_b)$", name, re.I) else 1)
        return Reset(name, bits[0], active)
    cands = [n for n, p in nl.ports.items()
             if p["direction"] == "input" and len(p["bits"]) == 1 and _RESET_RE.search(n)]
    if not cands:
        return None
    name = sorted(cands, key=len)[0]
    m = _RESET_RE.search(name)
    low = bool(m.group(3)) and m.group(3).lower() in ("n", "_n", "_ni", "_b")
    return Reset(name, nl.ports[name]["bits"][0], 0 if low else 1)


def build_parser():
    p = argparse.ArgumentParser(
        prog="fvlint",
        description="Lightweight formal lint: find counters, unique/parallel case statements, "
                    "variable part-selects, memories and FSMs in RTL and prove small, local "
                    "properties about each one on a sliced cone of logic.")
    p.add_argument("files", nargs="*", help="Verilog/SystemVerilog sources")
    p.add_argument("--top", required=True, help="top module")
    p.add_argument("-f", dest="filelists", action="append", default=[], help="file list (.f)")
    p.add_argument("-I", dest="incdirs", action="append", default=[], help="include directory")
    p.add_argument("-D", dest="defines", action="append", default=[], help="preprocessor define")
    p.add_argument("-P", dest="params", action="append", default=[], help="top parameter NAME=VALUE")
    p.add_argument("--lib", action="append", default=[], help="blackbox stub file (e.g. vendor primitives)")
    p.add_argument("--frontend", choices=["yosys", "slang"], default="yosys",
                   help="Yosys' built-in parser or the yosys-slang plugin (better SystemVerilog)")
    g = p.add_argument_group("environment")
    g.add_argument("--reset", help="reset port NAME[:ACTIVE_LEVEL]; default: guessed from port names")
    g.add_argument("--no-reset", action="store_true", help="do not assume a reset at time 0")
    g.add_argument("--uninit", choices=["zero", "free"], default="zero",
                   help="power-up value of registers without reset/init (default: zero, FPGA style)")
    g.add_argument("--assume", help="SV file with module fvlint_assumptions whose ports are top-level "
                                    "inputs (by name) and which contains assume statements")
    g = p.add_argument_group("proof")
    g.add_argument("--max-level", type=int, default=3,
                   help="register stages to pull in before the full design (default 3)")
    g.add_argument("--no-full", action="store_true", help="never fall back to the full design")
    g.add_argument("--depth", type=int, default=20, help="k-induction / BMC depth (default 20)")
    g.add_argument("--max-bmc-depth", type=int, default=200, help="cap for counter-derived BMC depth (default 200)")
    g.add_argument("--timeout", type=float, default=120, help="seconds per solver run (default 120)")
    g.add_argument("--engine", choices=["smtbmc", "pdr"], default="smtbmc",
                   help="smtbmc k-induction with helper lemmas (default) or ABC PDR (needs yosys-abc)")
    g.add_argument("--solver", help="SMT solver for smtbmc (yices, bitwuzla, boolector, z3)")
    g.add_argument("-j", "--jobs", type=int, default=os.cpu_count() or 2, help="parallel checks")
    g = p.add_argument_group("selection and output")
    g.add_argument("--checks", help="comma-separated check kinds to run: " + ",".join(KINDS))
    g.add_argument("--waivers", help="waiver file (check-id globs)")
    g.add_argument("--list", action="store_true", help="list detected checks without proving")
    g.add_argument("-o", "--out", default="fvlint_out", help="work/output directory")
    g.add_argument("--json", help="results JSON (default OUT/results.json)")
    g.add_argument("--junit", help="JUnit XML (default OUT/junit.xml)")
    g.add_argument("--fail-on", choices=["fail", "unknown"], default="fail",
                   help="exit non-zero on FAIL/ERROR (default) or also on UNKNOWN")
    g.add_argument("-v", "--verbose", action="store_true", help="show proven and waived checks too")
    p.add_argument("--version", action="version", version=f"fvlint {__version__}")
    return p


def _slug(s: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.=-]+", "_", s).strip("_")[:90]


def main(argv=None) -> int:
    args = build_parser().parse_args(argv)
    t0 = time.time()
    src = Sources(files=list(args.files), incdirs=list(args.incdirs), defines=list(args.defines),
                  libs=list(args.lib), params=list(args.params))
    for fl in args.filelists:
        src.add_filelist(fl)
    if not src.files:
        print("fvlint: no source files", file=sys.stderr)
        return 2
    out = os.path.abspath(args.out)
    os.makedirs(out, exist_ok=True)

    try:
        tools = Toolchain.discover(args.solver)
        if args.engine == "pdr" and not tools.abc:
            raise ToolError("--engine pdr needs yosys-abc on PATH")
        elab = elaborate(src, args.top, args.frontend, tools, out, args.assume)
    except ToolError as e:
        print(f"fvlint: {e}", file=sys.stderr)
        return 2

    nl = Netlist.load(elab["main"], args.top, elab["src_base"], elab["src_map"])
    checks, lemmas = detect_all(nl, args.max_level)
    if elab["fsm_warning"]:
        print(f"fvlint: warning: {elab['fsm_warning']}", file=sys.stderr)
    fsm_checks, fsm_lemmas = analyse_fsms(nl, elab["fsm"]) if elab["fsm"] else ([], {})
    checks += fsm_checks
    for k, v in fsm_lemmas.items():
        lemmas.setdefault(k, []).extend(v)
    if args.checks:
        want = {k.strip() for k in args.checks.split(",")}
        checks = [c for c in checks if c.kind in want]

    reset = None if args.no_reset else find_reset(nl, args.reset)
    print(f"fvlint {__version__}: top {args.top}, {len(nl.cells)} cells, {len(checks)} checks; "
          f"reset: {f'{reset.port} (active {reset.active})' if reset else 'none'}; {tools.describe()}",
          file=sys.stderr)

    if args.list:
        for c in checks:
            print(f"{c.id:<50} {c.src:<28} {c.desc}")
        return 0

    waivers = Waivers.load(args.waivers)
    results, todo = [], []
    for c in checks:
        w = waivers.match(c)
        if w:
            results.append(Result(check=c, status=WAIVED, detail=w, waiver=w))
        elif c.preset:
            results.append(Result(check=c, status=c.preset, detail=c.detail))
        else:
            todo.append(c)

    opts = Options(max_level=args.max_level, try_full=not args.no_full, depth=args.depth,
                   max_bmc_depth=args.max_bmc_depth, timeout=args.timeout, engine=args.engine,
                   uninit=args.uninit)
    prover = Prover(nl, tools, out, lemmas, reset, opts, elab["assume_ports"], elab["assume_file"])
    slugs, used = [], set()
    for c in todo:
        s = _slug(c.id)
        while s in used:
            s += "_"
        used.add(s)
        slugs.append(s)

    def work(item):
        c, s = item
        try:
            return prover.run_check(c, s)
        except Exception as e:  # keep going; report the check as an error
            return Result(check=c, status=ERROR, detail=f"internal error: {e!r}")

    with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as ex:
        for r in ex.map(work, zip(todo, slugs)):
            results.append(r)

    meta = {"version": __version__, "top": args.top, "elapsed_s": round(time.time() - t0, 2),
            "reset": reset.port if reset else None, "uninit": args.uninit,
            "engine": args.engine, "solver": tools.solver, "max_level": args.max_level}
    write_json(results, args.json or os.path.join(out, "results.json"), meta)
    write_junit(results, args.junit or os.path.join(out, "junit.xml"))
    print(console(results, args.verbose))
    print(f"\n{meta['elapsed_s']}s, results in {display_path(out)}/", file=sys.stderr)

    bad = {FAIL, ERROR} | ({UNKNOWN} if args.fail_on == "unknown" else set())
    return 1 if any(r.status in bad for r in results) else 0


if __name__ == "__main__":
    sys.exit(main())
