# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Soundness fuzzer.

Generates small random designs (counters, cross-register conditions, case
statements, part-selects, non-power-of-two memories, occasionally a second
clock or a falling-edge register), runs fvlint on each, and then checks every
verdict with an independent oracle that uses none of fvlint's cleverness: a
plain bounded model check on the *whole* design, without slicing, cut-points,
counterexample replay, helper lemmas or PDR.

* PROVEN / VACUOUS  -> the oracle must find no violation (no reachable
                       enabling condition, for VACUOUS) within the bound.
* FAIL              -> the oracle must find the violation.
* fsm_unreachable   -> the oracle must not reach the state.

The oracle is bounded, so a disagreement beyond its depth goes unnoticed;
designs are kept small (registers of 2-5 bits) so the bound covers them.

    python -m fvlint.fuzz --seeds 50 -o fuzz_out
"""

from __future__ import annotations

import argparse
import contextlib
import io
import json
import os
import random
import sys
import time

# ----------------------------------------------------------------- generator


def generate(seed: int) -> tuple[str, str]:
    r = random.Random(seed)
    top = f"fz{seed}"
    n = r.randint(2, 4)
    widths = [r.randint(2, 5) for _ in range(n)]
    two_clocks = r.random() < 0.15
    neg = r.randrange(n) if r.random() < 0.15 else None
    ins = [f"in{j}" for j in range(4)]

    def cond(i):
        k = r.randrange(n)
        c = r.randrange(1 << widths[k])
        return r.choice([
            r.choice(ins), "!" + r.choice(ins),
            f"(r{k} == {widths[k]}'d{c})", f"(r{k} < {widths[k]}'d{c})", f"(r{k} != {widths[k]}'d{c})",
            f"({r.choice(ins)} && r{k} != {widths[k]}'d{c})",
        ])

    def expr(i):
        w = widths[i]
        c = r.randint(1, 3)
        k = r.randrange(n)
        other = f"r{k}" if widths[k] >= w else f"{{{w - widths[k]}'d0, r{k}}}"
        if widths[k] > w:
            other = f"r{k}[{w - 1}:0]"
        return r.choice([f"r{i} + {w}'d{c}", f"r{i} + {w}'d{c}", f"r{i} - {w}'d{c}",
                         f"{w}'d{r.randrange(1 << w)}", other,
                         f"din[{min(w, 4) - 1}:0]" if w <= 4 else f"{{{w - 4}'d0, din}}"])

    lines = [f"module {top} (input clk, input clk2, input rst, input in0, input in1, input in2, "
             f"input in3, input [3:0] din, output [63:0] o);"]
    for i, w in enumerate(widths):
        lines.append(f"  reg [{w - 1}:0] r{i};")
    for i, w in enumerate(widths):
        edge = "negedge clk" if i == neg else ("posedge clk2" if two_clocks and i == n - 1 else "posedge clk")
        style = r.choice(["random", "bounded", "credit"])
        mx = (1 << w) - 1
        if style == "bounded":
            # Clears at a limit: overflow-safe unless the limit is the maximum.
            lim = r.choice([r.randrange(1, mx + 1), mx])
            lines.append(f"  always @({edge}) if (rst) r{i} <= {w}'d0; "
                         f"else if (r{i} == {w}'d{lim}) r{i} <= {w}'d0; "
                         f"else if ({cond(i)}) r{i} <= r{i} + {w}'d1;")
            continue
        if style == "credit":
            # Increment gated by a *registered* threshold flag: safe iff the
            # threshold leaves one count of slack (needs a larger cone).
            lim = r.choice([mx - 1, mx - 1, mx])
            lines.append(f"  reg ok{i};")
            lines.append(f"  always @({edge}) if (rst) ok{i} <= 1'b1; else ok{i} <= (r{i} < {w}'d{lim});")
            lines.append(f"  always @({edge}) if (rst) r{i} <= {w}'d0; "
                         f"else if ({r.choice(ins)} && ok{i}) r{i} <= r{i} + {w}'d1; "
                         f"else if ({r.choice(ins)} && r{i} != {w}'d0) r{i} <= r{i} - {w}'d1;")
            continue
        body = [f"if (rst) r{i} <= {w}'d{r.randrange(1 << w)};"]
        for b in range(r.randint(1, 3)):
            body.append(f"else if ({cond(i)}) r{i} <= {expr(i)};")
        lines.append(f"  always @({edge}) " + " ".join(body))
    extra = []
    if r.random() < 0.5:   # unique case, sometimes with overlapping casez items
        k = r.randrange(n)
        if r.random() < 0.5:
            lines.append("  reg [1:0] y;")
            lines.append("  always @* begin y = 2'd0; unique casez ({in0, in1}) "
                         "2'b1?: y = 2'd1; 2'b?1: y = 2'd2; default: y = 2'd3; endcase end")
        else:
            lines.append("  reg [1:0] y;")
            lines.append(f"  always @* begin y = 2'd0; unique case (1'b1) r{k}[0]: y = 2'd1; "
                         f"r{k}[1]: y = 2'd2; endcase end")
        extra.append("y")
    if r.random() < 0.5:   # variable part-select
        k = r.randrange(n)
        lanes = r.randint(2, 5)
        mask = r.randrange(1 << (lanes * 4))
        lines.append(f"  wire [{lanes * 4 - 1}:0] lanes = {{{lanes}{{din}}}} ^ {lanes * 4}'d{mask};")
        lines.append(f"  wire [3:0] sel = lanes[r{k}*4 +: 4];")
        extra.append("sel")
    if r.random() < 0.4:   # non-power-of-two memory
        k = r.randrange(n)
        depth = r.choice([3, 5, 6, 7, 10, 12])
        aw = max(1, (depth - 1).bit_length())
        addr = f"r{k}" if widths[k] == aw else (f"r{k}[{aw - 1}:0]" if widths[k] > aw
                                                 else f"{{{aw - widths[k]}'d0, r{k}}}")
        lines.append(f"  reg [3:0] mem [0:{depth - 1}];")
        lines.append(f"  always @(posedge clk) if (in3) mem[{addr}] <= din;")
        lines.append(f"  wire [3:0] rd = mem[{addr}];")
        extra.append("rd")
    outs = ", ".join([f"r{i}" for i in range(n)] + extra)
    lines.append(f"  assign o = {{{outs}}};")
    lines.append("endmodule")
    return "\n".join(lines) + "\n", top


# -------------------------------------------------------------------- oracle


def _quiet(fn, *a, **kw):
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
        return fn(*a, **kw)


def oracle(out: str, top: str, depth: int, engine_opts, max_depth: int = 80) -> tuple[list, list]:
    """Re-check fvlint's verdicts in `out` with plain BMC on the whole design."""
    from .cone import UNBOUNDED, merge_specs, needs_multiclock, slice_spec
    from .detect import detect_all
    from .engine import Engine, Options
    from .fsm import analyse_fsms
    from .netlist import Netlist
    from .resets import discover
    from .sby import Prop
    from .tools import Toolchain

    with open(os.path.join(out, "results.json")) as f:
        results = {r["id"]: r for r in json.load(f)["results"]}
    edir = os.path.join(out, "elab")
    nl = Netlist.load(os.path.join(edir, "main.json"), top, edir)
    checks, _ = detect_all(nl, 3)
    by_id = {c.id: c for c in checks}
    resets = discover(nl, None, False, None)
    fsm_json = os.path.join(edir, "fsm.json")
    if os.path.exists(fsm_json):
        analyse_fsms(nl, fsm_json, resets.names())
    tools = Toolchain.discover()
    eng = Engine(nl, tools, os.path.join(out, "oracle"), {}, resets,
                 Options(engine="smtbmc", timeout=engine_opts.get("timeout", 300)))

    props, expect, roots = [], {}, []
    for cid, res in results.items():
        st = res["status"]
        if cid in by_id and st in ("PROVEN", "VACUOUS", "FAIL"):
            c = by_id[cid]
            name = f"fvl_t{len(props)}"
            mode = 2 if st == "VACUOUS" else 0
            props.append(Prop(name, c.checker, c.params, c.ports,
                              c.conds + resets.inactive_conds(), mode))
            expect[name] = (cid, st)
            roots += c.roots()
        elif st == "FAIL" and res["kind"] == "fsm_unreachable":
            sig, _, code = res["target"].partition("=")
            net = nl.netnames.get(sig)
            if not net or "'b" not in code:
                continue
            bits, val = net["bits"], int(code.split("'b")[1], 2)
            w = len(bits)
            if w > 8:
                continue
            others = [v for v in range(1 << w) if v != val]
            setv = sum(v << (i * w) for i, v in enumerate(others))
            name = f"fvl_t{len(props)}"
            props.append(Prop(name, "fvl_member", {"W": w, "N": len(others), "SET": setv},
                              {"v": bits}, resets.inactive_conds(), 0))
            expect[name] = (cid, "UNREACHABLE")
            roots += bits
    if not props:
        return [], []
    spec = slice_spec(nl, roots + [r.bit for r in resets.all()], [], UNBOUNDED)
    spec = merge_specs(nl, [spec])
    steps = {cid: results[cid].get("cex_step") or 0 for cid, _ in expect.values() if cid in results}
    bound = min(max([depth] + [v + 4 for v in steps.values()]), max_depth)
    r = eng.run("oracle_bmc", spec, props, "bmc", bound, needs_multiclock(nl, spec),
                engine=eng.smtbmc_str())
    finished = r.status in ("PASS", "FAIL")
    problems, inconclusive = [], []
    for name, (cid, st) in expect.items():
        failed = r.get(name).status == "fail"
        # A violation the oracle finds is a definite witness, even if its job
        # then timed out; *not* finding one only counts if the search finished
        # deep enough.
        if st == "PROVEN" and failed:
            problems.append(f"{cid}: fvlint PROVEN, oracle found a violation")
        elif st == "VACUOUS" and failed:
            problems.append(f"{cid}: fvlint VACUOUS, oracle reached the check's condition")
        elif st == "UNREACHABLE" and failed:
            problems.append(f"{cid}: fvlint says unreachable, oracle reached it")
        elif st == "FAIL" and not failed:
            if finished and steps.get(cid, 0) + 4 <= bound:
                problems.append(f"{cid}: fvlint FAIL, oracle found no violation within {bound} steps")
            else:
                inconclusive.append(f"{cid}: FAIL at step {steps.get(cid)} beyond the oracle's reach "
                                    f"(bound {bound}, job {r.status})")
    return problems, inconclusive


# ------------------------------------------------------------------- driver


def run(seeds, outroot: str, depth: int = 24, extra_args=(), verbose=False) -> dict:
    from . import cli
    os.makedirs(outroot, exist_ok=True)
    summary = {"seeds": 0, "checks": 0, "problems": [], "inconclusive": [], "statuses": {}, "seconds": 0.0}
    t0 = time.time()
    for seed in seeds:
        text, top = generate(seed)
        d = os.path.join(outroot, f"seed{seed}")
        os.makedirs(d, exist_ok=True)
        src = os.path.join(d, f"{top}.v")
        with open(src, "w") as f:
            f.write(text)
        rc = _quiet(cli.main, ["--top", top, src, "-o", d, "-j", "1", *extra_args])
        summary["seeds"] += 1
        if rc == 2 or not os.path.exists(os.path.join(d, "results.json")):
            summary["problems"].append(f"seed {seed}: fvlint did not complete (rc={rc}), see {d}")
            continue
        with open(os.path.join(d, "results.json")) as f:
            res = json.load(f)["results"]
        for x in res:
            summary["statuses"][x["status"]] = summary["statuses"].get(x["status"], 0) + 1
        summary["checks"] += len(res)
        probs, inconc = oracle(d, top, depth, {})
        for p in probs:
            summary["problems"].append(f"seed {seed}: {p} (design: {src})")
        summary["inconclusive"] += [f"seed {seed}: {p}" for p in inconc]
        if verbose:
            print(f"seed {seed}: {len(res)} checks, {len(probs)} problem(s)", file=sys.stderr)
    summary["seconds"] = round(time.time() - t0, 1)
    return summary


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="fvlint-fuzz", description=__doc__.split("\n\n")[0])
    ap.add_argument("--seeds", type=int, default=20, help="number of random designs")
    ap.add_argument("--first-seed", type=int, default=1)
    ap.add_argument("--depth", type=int, default=24, help="oracle BMC depth")
    ap.add_argument("-o", "--out", default="fvlint_fuzz")
    ap.add_argument("--engine", choices=["auto", "pdr", "smtbmc"], default="auto")
    ap.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args(argv)
    s = run(range(args.first_seed, args.first_seed + args.seeds), args.out, args.depth,
            ["--engine", args.engine], args.verbose)
    print(f"fvlint-fuzz: {s['seeds']} designs, {s['checks']} checks {s['statuses']}, "
          f"{len(s['problems'])} problem(s), {len(s['inconclusive'])} beyond the oracle's reach, "
          f"{s['seconds']}s")
    for p in s["problems"]:
        print("  " + p)
    return 1 if s["problems"] else 0


if __name__ == "__main__":
    sys.exit(main())
