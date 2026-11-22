# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""fvlint command line."""

from __future__ import annotations

import argparse
import os
import sys
import time

from . import __version__
from .checks import ERROR, FAIL, UNKNOWN, VACUOUS, WAIVED, Result
from .detect import detect_all
from .elaborate import Sources, elaborate
from .engine import Engine, Options
from .fsm import analyse_fsms
from .netlist import Netlist, display_path
from .report import console, write_json, write_junit
from .resets import discover
from .tools import Toolchain, ToolError
from .waivers import Waivers

KINDS = ["counter_overflow", "counter_underflow", "parallel_case", "full_case", "index_range",
         "mem_addr", "fsm_unreachable", "fsm_trap", "fsm_reset", "fsm_summary"]


def build_parser():
    p = argparse.ArgumentParser(
        prog="fvlint",
        description="Lightweight formal lint: find counters, unique/parallel case statements, "
                    "variable part-selects, memories and FSMs in RTL and prove small, local "
                    "properties about each one on a sliced cone of logic.")
    p.add_argument("files", nargs="*", help="Verilog/SystemVerilog sources")
    p.add_argument("--top", required=True, help="top module")
    p.add_argument("-f", dest="filelists", action="append", default=[], type=lambda v: (v, False),
                   metavar="FILE", help="file list (.f); its relative paths are relative to the current directory")
    p.add_argument("-F", dest="filelists", action="append", type=lambda v: (v, True),
                   metavar="FILE", help="file list (.f) whose relative paths are relative to the list itself")
    p.add_argument("-I", dest="incdirs", action="append", default=[], help="include directory")
    p.add_argument("-D", dest="defines", action="append", default=[], help="preprocessor define")
    p.add_argument("-P", dest="params", action="append", default=[], help="top parameter NAME=VALUE")
    p.add_argument("--lib", action="append", default=[], help="blackbox stub file (e.g. vendor primitives)")
    p.add_argument("--frontend", choices=["yosys", "slang"], default="yosys",
                   help="Yosys' built-in parser or the yosys-slang plugin (better SystemVerilog)")
    g = p.add_argument_group("environment")
    g.add_argument("--reset", help="reset port NAME[:ACTIVE_LEVEL]; default: guessed from port names")
    g.add_argument("--no-reset", action="store_true", help="do not assume a reset at time 0")
    g.add_argument("--reset-anytime", action="store_true",
                   help="allow reset to be re-asserted after start-up (default: reset once)")
    g.add_argument("--reset-cycles", type=int,
                   help="cycles to hold reset at start (default: 1 + longest reset synchronizer)")
    g.add_argument("--uninit", choices=["zero", "free"], default="zero",
                   help="power-up value of registers without reset/init (default: zero, FPGA style)")
    g.add_argument("--assume", help="SV file with module fvlint_assumptions whose ports are top-level "
                                    "inputs (by name) and which contains assume statements")
    g = p.add_argument_group("proof")
    g.add_argument("--engine", choices=["auto", "pdr", "smtbmc"], default="auto",
                   help="auto: ABC PDR if yosys-abc is available, else k-induction (default)")
    g.add_argument("--solver", help="SMT solver for smtbmc (yices, bitwuzla, boolector, z3)")
    g.add_argument("--max-level", type=int, default=3,
                   help="register stages to pull in before the full cone (default 3)")
    g.add_argument("--no-full", action="store_true", help="never fall back to the full cone")
    g.add_argument("--no-cegar", action="store_true",
                   help="do not replay slice counterexamples on the full cone")
    g.add_argument("--no-vacuity", action="store_true", help="skip vacuity checks on proofs")
    g.add_argument("--depth", type=int, default=20, help="k-induction / BMC depth (default 20)")
    g.add_argument("--max-bmc-depth", type=int, default=200, help="cap for structure-derived BMC depth")
    g.add_argument("--timeout", type=float, default=120, help="seconds per solver job (default 120)")
    g.add_argument("--pdr-timeout", type=float, default=30,
                   help="seconds for PDR before undecided checks fall back to k-induction (default 30)")
    g.add_argument("--batch-cells", type=int, default=1500, help="max cells per batched proof job")
    g.add_argument("--batch-props", type=int, default=8, help="max checks per batched proof job")
    g.add_argument("-j", "--jobs", type=int, default=max(1, (os.cpu_count() or 2) // 2),
                   help="parallel solver jobs (default: half the CPUs; each job runs 2 processes)")
    g = p.add_argument_group("selection and output")
    g.add_argument("--checks", help="comma-separated check kinds to run: " + ",".join(KINDS))
    g.add_argument("--waivers", help="waiver file (check-id globs)")
    g.add_argument("--list", action="store_true", help="list detected checks without proving")
    g.add_argument("-o", "--out", default="fvlint_out", help="work/output directory")
    g.add_argument("--json", help="results JSON (default OUT/results.json)")
    g.add_argument("--junit", help="JUnit XML (default OUT/junit.xml)")
    g.add_argument("--fail-on", choices=["fail", "vacuous", "unknown"], default="vacuous",
                   help="exit non-zero on FAIL/ERROR, plus VACUOUS (default), plus UNKNOWN")
    g.add_argument("-v", "--verbose", action="store_true", help="show proven and waived checks too")
    p.add_argument("--version", action="version", version=f"fvlint {__version__}")
    return p


def _warn(msg: str):
    print(f"fvlint: warning: {msg}", file=sys.stderr)


def main(argv=None) -> int:
    args = build_parser().parse_args(argv)
    t0 = time.time()
    src = Sources(files=list(args.files), incdirs=list(args.incdirs), defines=list(args.defines),
                  libs=list(args.lib), params=list(args.params))
    for fl, relative_to_list in args.filelists:
        src.add_filelist(fl, relative_to_list)
    want = {k.strip() for k in args.checks.split(",") if k.strip()} if args.checks else None
    if want is not None and not want <= set(KINDS):
        print(f"fvlint: --checks: unknown check kind(s) {', '.join(sorted(want - set(KINDS)))}; "
              f"known: {', '.join(KINDS)}", file=sys.stderr)
        return 2
    if not src.files:
        print("fvlint: no source files", file=sys.stderr)
        return 2
    out = os.path.abspath(args.out)
    os.makedirs(out, exist_ok=True)

    try:
        tools = Toolchain.discover(args.solver)
        if args.engine == "pdr" and not tools.abc:
            raise ToolError("--engine pdr needs yosys-abc (on PATH, or `pip install pyosys`)")
        vw = tools.version_warning()
        if vw:
            _warn(vw)
        elab = elaborate(src, args.top, args.frontend, tools, out, args.assume)
    except ToolError as e:
        print(f"fvlint: {e}", file=sys.stderr)
        return 2

    nl = Netlist.load(elab["main"], args.top, elab["src_base"], elab["src_map"])
    if nl.unknown_types:
        _warn("cell types not modelled by fvlint are cut (treated as free): "
              + ", ".join(sorted(nl.unknown_types)))
    if elab["assume_ports"]:
        bad = [p for p, d in elab["assume_ports"].items()
               if p not in nl.ports or nl.ports[p]["direction"] != "input" or d != "input"]
        if bad:
            print(f"fvlint: --assume: fvlint_assumptions ports {', '.join(bad)} are not inputs of "
                  f"{args.top}; ports are matched to top-level inputs by name", file=sys.stderr)
            return 2
    try:
        resets = discover(nl, args.reset, args.no_reset, args.reset_cycles, args.reset_anytime)
    except ValueError as e:
        print(f"fvlint: {e}", file=sys.stderr)
        return 2

    checks, lemmas = detect_all(nl, args.max_level)
    if elab["fsm_warning"]:
        _warn(elab["fsm_warning"])
    fsm_checks, fsm_lemmas = (analyse_fsms(nl, elab["fsm"], resets.names()) if elab["fsm"] else ([], {}))
    checks += fsm_checks
    for k, v in fsm_lemmas.items():
        lemmas.setdefault(k, []).extend(v)
    if want is not None:
        checks = [c for c in checks if c.kind in want]

    rdesc = "none"
    if resets.primary:
        rdesc = f"{resets.primary.name} (active {resets.primary.active}, held {resets.cycles} cycle(s)"
        rdesc += f", {len(resets.derived)} synchronized)" if resets.derived else ")"
    print(f"fvlint {__version__}: top {args.top}, {len(nl.cells)} cells, {len(checks)} checks; "
          f"reset: {rdesc}; {tools.describe()}", file=sys.stderr)

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
                   pdr_timeout=args.pdr_timeout,
                   uninit=args.uninit, vacuity=not args.no_vacuity, cegar=not args.no_cegar,
                   batch_cells=args.batch_cells, batch_props=args.batch_props, jobs=args.jobs)
    engine = Engine(nl, tools, out, lemmas, resets, opts, elab["assume_ports"], elab["assume_file"])
    env_err = engine.environment_ok() if todo else None
    if env_err:
        results += [Result(check=c, status=ERROR, detail=env_err) for c in todo]
    elif todo:
        try:
            results += engine.prove_all(todo)
        except Exception as e:  # keep the report; mark what is left as errors
            done = {r.check.id for r in results}
            results += [Result(check=c, status=ERROR, detail=f"internal error: {e!r}")
                        for c in todo if c.id not in done]

    meta = {"version": __version__, "top": args.top, "elapsed_s": round(time.time() - t0, 2),
            "reset": resets.primary.name if resets.primary else None, "reset_cycles": resets.cycles,
            "derived_resets": [r.name for r in resets.derived], "uninit": args.uninit,
            "engine": opts.engine, "solver": tools.solver,
            "yosys": ".".join(map(str, tools.version)) if tools.version else None,
            "max_level": args.max_level, **engine.stats}
    write_json(results, args.json or os.path.join(out, "results.json"), meta)
    write_junit(results, args.junit or os.path.join(out, "junit.xml"))
    print(console(results, args.verbose))
    print(f"\n{meta['elapsed_s']}s, {engine.stats['jobs']} solver jobs, engine {opts.engine}; "
          f"results in {display_path(out)}/", file=sys.stderr)

    bad = {FAIL, ERROR}
    if args.fail_on in ("vacuous", "unknown"):
        bad.add(VACUOUS)
    if args.fail_on == "unknown":
        bad.add(UNKNOWN)
    return 1 if any(r.status in bad for r in results) else 0


if __name__ == "__main__":
    sys.exit(main())
