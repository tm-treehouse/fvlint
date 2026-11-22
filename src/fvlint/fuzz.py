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
    # Reset structure: the primary reset, a two-stage synchronized copy, and
    # sometimes a flop that copies the synchronizer but that a data input can
    # also set asynchronously (not a reset, though it looks like one).
    resets = ["rst"]
    if r.random() < 0.35:
        lines.append("  reg s1, s2;")
        lines.append("  always @(posedge clk) begin s1 <= rst; s2 <= s1; end")
        resets.append("s2")
        if r.random() < 0.5:
            trig = r.choice(ins)
            lines.append("  reg msk;")
            lines.append(f"  always @(posedge clk or posedge {trig}) if ({trig}) msk <= 1'b1; else msk <= s1;")
            resets.append("msk")
    for i, w in enumerate(widths):
        edge = "negedge clk" if i == neg else ("posedge clk2" if two_clocks and i == n - 1 else "posedge clk")
        style = r.choice(["random", "bounded", "credit"])
        rst = r.choice(resets)
        mx = (1 << w) - 1
        if style == "bounded":
            # Clears at a limit: overflow-safe unless the limit is the maximum.
            lim = r.choice([r.randrange(1, mx + 1), mx])
            lines.append(f"  always @({edge}) if ({rst}) r{i} <= {w}'d0; "
                         f"else if (r{i} == {w}'d{lim}) r{i} <= {w}'d0; "
                         f"else if ({cond(i)}) r{i} <= r{i} + {w}'d1;")
            continue
        if style == "credit":
            # Increment gated by a *registered* threshold flag: safe iff the
            # threshold leaves one count of slack (needs a larger cone).
            lim = r.choice([mx - 1, mx - 1, mx])
            lines.append(f"  reg ok{i};")
            lines.append(f"  always @({edge}) if ({rst}) ok{i} <= 1'b1; else ok{i} <= (r{i} < {w}'d{lim});")
            lines.append(f"  always @({edge}) if ({rst}) r{i} <= {w}'d0; "
                         f"else if ({r.choice(ins)} && ok{i}) r{i} <= r{i} + {w}'d1; "
                         f"else if ({r.choice(ins)} && r{i} != {w}'d0) r{i} <= r{i} - {w}'d1;")
            continue
        body = [f"if ({rst}) r{i} <= {w}'d{r.randrange(1 << w)};"]
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
    if r.random() < 0.3:   # bit-select with a narrow signed index (negative when its top bit is set)
        k = r.randrange(n)
        top_bit = r.choice(["1'b0", r.choice(ins)])
        lines.append(f"  wire [2:0] lo3 = r{k};")
        lines.append(f"  wire signed [3:0] sidx = {{{top_bit}, lo3}};")
        lines.append("  wire [11:0] vec12 = {3{din}};")
        lines.append("  wire sbit = vec12[sidx];")
        extra.append("sbit")
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


# Oracle-only checkers.  They deliberately do not reuse fvlint's checker
# library or its parameter encoding: the oracle exists to catch mistakes there.
ORACLE_V = """\
// Oracle: a variable select offset v lies in 0..MAXOFF, compared in
// (BW+1)-bit signed arithmetic, so nothing is truncated to the offset width.
module fvo_index #(parameter integer BW = 1, parameter integer SIGNED = 0, parameter integer MAXOFF = 0,
                   parameter integer NC = 1, parameter [NC-1:0] POL = 1, parameter integer MODE = 0)
                  (input [BW-1:0] v, input [NC-1:0] c);
  wire en = &(c ~^ POL);
  wire signed [BW:0] sv = SIGNED ? $signed({v[BW-1], v}) : $signed({1'b0, v});
  wire ok = (sv >= 0) && (sv <= MAXOFF);
  generate if (MODE == 2) begin : g_v
    always @* assert (!en);
  end else begin : g_a
    always @* if (en) assert (ok);
  end endgenerate
endmodule

// Oracle: high from global step N on.
module fvo_settled #(parameter integer N = 12) (output done);
  (* gclk *) wire gclk;
  reg [7:0] n = 8'd0;
  always @(posedge gclk) if (n != 8'hff) n <= n + 8'd1;
  assign done = (n >= N);
endmodule
"""

SETTLE = 10      # cycles after the primary reset that genuine synchronizers need


def _index_prop(nl, c, name, conds, mode):
    """The oracle's own encoding of an index_range check, from the $shiftx cell."""
    from .sby import Prop
    v = c.ports["v"]
    for cell, cc in nl.cells.items():
        if cc["type"] == "$shiftx" and cc["connections"].get("B") == v:
            maxoff = len(cc["connections"]["A"]) - len(cc["connections"]["Y"])
            return Prop(name, "fvo_index", {"BW": len(v), "SIGNED": nl.param(cell, "B_SIGNED", 0),
                                            "MAXOFF": maxoff}, {"v": v}, conds, mode)
    return None


def oracle(out: str, top: str, depth: int, engine_opts, max_depth: int = 80) -> tuple[list, list]:
    """Re-check fvlint's verdicts in `out` with plain BMC on the whole design.

    Each PROVEN / VACUOUS verdict is checked twice: under fvlint's own gating
    (path conditions, every reset inactive, from step 0) and under gating the
    oracle decides by itself (path conditions, the primary reset inactive,
    and SETTLE cycles after start), so a register wrongly taken for a reset
    shows up as a disagreement.  index_range checks use the oracle's own
    property (bounds from the $shiftx cell); the other kinds still use
    fvlint's checker parameters."""
    from .cone import UNBOUNDED, needs_multiclock, slice_spec
    from .detect import detect_all
    from .engine import Engine, Options
    from .netlist import Netlist, is_const
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
    tools = Toolchain.discover()
    eng = Engine(nl, tools, os.path.join(out, "oracle"), {}, resets,
                 Options(engine="smtbmc", timeout=engine_opts.get("timeout", 300)))

    # A fresh bit for the settle flag.
    bits = [b for n in nl.netnames.values() for b in n["bits"]]
    bits += [b for c in nl.cells.values() for v in c["connections"].values() for b in v]
    settled = max([b for b in bits if not is_const(b)], default=1) + 1
    primary = [(resets.primary.bit, 1 - resets.primary.active)] if resets.primary else []

    props, expect, roots = [], {}, []

    def add(prop, cid, st, gating):
        props.append(prop)
        expect[prop.name] = (cid, st, gating)

    for cid, res in results.items():
        st = res["status"]
        if cid in by_id and st in ("PROVEN", "VACUOUS", "FAIL"):
            c = by_id[cid]
            mode = 2 if st == "VACUOUS" else 0
            gatings = [("fvlint", c.conds + resets.inactive_conds())]
            if st != "FAIL" and resets.derived:
                gatings.append(("independent", c.conds + primary + [(settled, 1)]))
            for gating, conds in gatings:
                name = f"fvl_t{len(props)}"
                p = _index_prop(nl, c, name, conds, mode) if c.kind == "index_range" else None
                add(p or Prop(name, c.checker, c.params, c.ports, conds, mode), cid, st, gating)
            roots += c.roots()
        elif st == "FAIL" and res["kind"] == "fsm_unreachable":
            sig, _, code = res["target"].partition("=")
            net = nl.netnames.get(sig)
            if not net or "'b" not in code:
                continue
            fbits, val = net["bits"], int(code.split("'b")[1], 2)
            w = len(fbits)
            if w > 8:
                continue
            others = [v for v in range(1 << w) if v != val]
            setv = sum(v << (i * w) for i, v in enumerate(others))
            add(Prop(f"fvl_t{len(props)}", "fvl_member", {"W": w, "N": len(others), "SET": setv},
                     {"v": fbits}, resets.inactive_conds(), 0), cid, "UNREACHABLE", "fvlint")
            roots += fbits
    if not props:
        return [], []
    spec = slice_spec(nl, roots + [r.bit for r in resets.all()], [], UNBOUNDED)
    mc = needs_multiclock(nl, spec)
    settle = (resets.cycles + SETTLE) * (2 if mc else 1)        # in global steps
    cells = {"fvo_settle": {"hide_name": 0, "type": "fvo_settled", "parameters": {"N": settle},
                            "attributes": {}, "port_directions": {"done": "output"},
                            "connections": {"done": [settled]}}}
    steps = {cid: results[cid].get("cex_step") or 0 for cid, _, _ in expect.values() if cid in results}
    need = resets.cycles + SETTLE + 6 if any(g == "independent" for _, _, g in expect.values()) else 0
    bound = min(max([depth, need] + [v + 4 for v in steps.values()]), max_depth)
    r = eng.run("oracle_bmc", spec, props, "bmc", bound, mc, engine=eng.smtbmc_str(),
                extra_cells=cells, extra_files={"fvo_oracle.v": ORACLE_V})
    finished = r.status in ("PASS", "FAIL")
    problems, inconclusive = [], []
    for name, (cid, st, gating) in expect.items():
        failed = r.get(name).status == "fail"
        how = "" if gating == "fvlint" else " (with the oracle's own reset gating)"
        # A violation the oracle finds is a definite witness, even if its job
        # then timed out; *not* finding one only counts if the search finished
        # deep enough.
        if st == "PROVEN" and failed:
            problems.append(f"{cid}: fvlint PROVEN, oracle found a violation{how}")
        elif st == "VACUOUS" and failed:
            problems.append(f"{cid}: fvlint VACUOUS, oracle reached the check's condition{how}")
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
