# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Soundness fuzzer.

Generates small random designs (counters, cross-register conditions, case
statements, part-selects, non-power-of-two memories, occasionally a second
clock or a falling-edge register), runs fvlint on each, and then checks every
verdict with an independent oracle.  The generator knows what it built, so
for each construct it also writes down, as plain Verilog expressions, when
the construct is active and when it goes wrong (an increment that wraps, two
case items that match, an address past the end).  The oracle appends those
monitors to its own copy of the design and runs a plain bounded model check
on it with SymbiYosys: no fvlint netlist, slicing, cut-points, replay,
lemmas, PDR, check parameters, path conditions or reset discovery.  It
shares only the tools (Yosys, SymbiYosys) and the contract: registers start
at zero, the reset is held at start for one cycle plus one per synchronizer
stage, and checks apply while the primary reset and the synchronized resets
are inactive (a flop that data can set is not a reset).

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
import re
import sys
import time
from dataclasses import dataclass, field

# ----------------------------------------------------------------- generator


@dataclass
class Design:
    """A generated design and what the generator knows about it."""
    text: str
    top: str
    regs: list = field(default_factory=list)          # sequential registers (name, width)
    # Stages of the rst -> s1 -> s2 synchronizer that something uses (Yosys
    # removes the others): genuine synchronized resets, so checks are off
    # while they are active, and the reset is held one cycle per stage longer.
    stages: list = field(default_factory=list)
    # (kind, target[, step]) -> {"en": when the construct is active, "bad": when it goes wrong}
    monitors: dict = field(default_factory=dict)
    clock: dict = field(default_factory=dict)          # register or memory -> its clock edge
    reads: dict = field(default_factory=dict)          # register, memory or wire -> names it reads

    def monitor(self, key, en, bad):
        m = self.monitors.setdefault(key, {"en": [], "bad": []})
        m["en"].append(en)
        m["bad"].append(bad)

    @property
    def gate(self) -> str:
        """When checks apply: the primary reset and the last synchronizer stage inactive."""
        return "!rst" + (f" && !{self.stages[-1]}" if self.stages else "")

    def clocks_of(self, expr: str) -> set:
        """Clock edges of the registers an expression depends on, directly or
        through other registers and wires."""
        todo, seen = set(_IDENT.findall(expr)), set()
        while todo:
            name = todo.pop()
            if name not in seen:
                seen.add(name)
                todo |= self.reads.get(name, set())
        return {self.clock[n] for n in seen if n in self.clock}

    def record(self):
        """Fill clock and reads from the text: one definition per line."""
        for line in self.text.splitlines():
            line = line.strip()
            m = (re.match(r"always @(?:\((.*?)\)|\*) (.*)$", line)
                 or re.match(r"wire (?:signed )?(?:\[[^\]]*\] )?()(\w+ = .*)$", line))
            if not m:
                continue
            sens, body = m.groups()
            if sens:                                   # clocked; always @* and wires are not
                lhs = set(re.findall(r"(\w+)(?:\[[^\]]*\])? <=", body))
                for name in lhs:
                    self.clock[name] = sens.split(" or ")[0]
            else:
                lhs = set(re.findall(r"(\w+) =(?!=)", body))
            for name in lhs:
                self.reads.setdefault(name, set()).update(set(_IDENT.findall(line)) - {name})


_STEP = re.compile(r"^r(\d+) ([+-]) \d+'d(\d+)$")
_IDENT = re.compile(r"(?<!['\w])[A-Za-z_]\w*")


def generate(seed: int) -> Design:
    r = random.Random(seed)
    top = f"fz{seed}"
    n = r.randint(2, 4)
    widths = [r.randint(2, 5) for _ in range(n)]
    two_clocks = r.random() < 0.15
    neg = r.randrange(n) if r.random() < 0.15 else None
    ins = [f"in{j}" for j in range(4)]
    d = Design("", top)

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

    def chain(i, rst, branches):
        """An if/else-if chain on register i: record a monitor for every
        branch that adds or subtracts a constant (taken, and wraps)."""
        w, mx = widths[i], (1 << widths[i]) - 1
        before = [f"!({rst})"]
        for c, rhs in branches:
            m = _STEP.match(rhs)
            if m and int(m.group(1)) == i:
                k = int(m.group(3))
                taken = " && ".join(before + [f"({c})"])
                up = m.group(2) == "+"
                wraps = f"(r{i} > {w}'d{mx - k})" if up else f"(r{i} < {w}'d{k})"
                d.monitor(("counter_overflow" if up else "counter_underflow", f"r{i}", k),
                          f"({taken})", f"({taken} && {wraps})")
            before.append(f"!({c})")

    lines = [f"module {top} (input clk, input clk2, input rst, input in0, input in1, input in2, "
             f"input in3, input [3:0] din, output [63:0] o);"]
    for i, w in enumerate(widths):
        lines.append(f"  reg [{w - 1}:0] r{i};")
        d.regs.append((f"r{i}", w))
    # Reset structure: the primary reset, a two-stage synchronized copy, and
    # sometimes a flop that copies the synchronizer but that a data input can
    # also set asynchronously (not a reset, though it looks like one).
    resets = ["rst"]
    if r.random() < 0.35:
        lines.append("  reg s1, s2;")
        lines.append("  always @(posedge clk) begin s1 <= rst; s2 <= s1; end")
        resets.append("s2")
        d.regs += [("s1", 1), ("s2", 1)]
        if r.random() < 0.5:
            trig = r.choice(ins)
            lines.append("  reg msk;")
            lines.append(f"  always @(posedge clk or posedge {trig}) if ({trig}) msk <= 1'b1; else msk <= s1;")
            resets.append("msk")
            d.regs.append(("msk", 1))
    used = set()
    for i, w in enumerate(widths):
        edge = "negedge clk" if i == neg else ("posedge clk2" if two_clocks and i == n - 1 else "posedge clk")
        style = r.choice(["random", "bounded", "credit"])
        rst = r.choice(resets)
        used.add(rst)
        mx = (1 << w) - 1
        if style == "bounded":
            # Clears at a limit: overflow-safe unless the limit is the maximum.
            lim = r.choice([r.randrange(1, mx + 1), mx])
            c = cond(i)
            lines.append(f"  always @({edge}) if ({rst}) r{i} <= {w}'d0; "
                         f"else if (r{i} == {w}'d{lim}) r{i} <= {w}'d0; "
                         f"else if ({c}) r{i} <= r{i} + {w}'d1;")
            chain(i, rst, [(f"r{i} == {w}'d{lim}", f"{w}'d0"), (c, f"r{i} + {w}'d1")])
            continue
        if style == "credit":
            # Increment gated by a *registered* threshold flag: safe iff the
            # threshold leaves one count of slack (needs a larger cone).
            lim = r.choice([mx - 1, mx - 1, mx])
            lines.append(f"  reg ok{i};")
            lines.append(f"  always @({edge}) if ({rst}) ok{i} <= 1'b1; else ok{i} <= (r{i} < {w}'d{lim});")
            d.regs.append((f"ok{i}", 1))
            up, down = f"{r.choice(ins)} && ok{i}", f"{r.choice(ins)} && r{i} != {w}'d0"
            lines.append(f"  always @({edge}) if ({rst}) r{i} <= {w}'d0; "
                         f"else if ({up}) r{i} <= r{i} + {w}'d1; "
                         f"else if ({down}) r{i} <= r{i} - {w}'d1;")
            chain(i, rst, [(up, f"r{i} + {w}'d1"), (down, f"r{i} - {w}'d1")])
            continue
        body = [f"if ({rst}) r{i} <= {w}'d{r.randrange(1 << w)};"]
        branches = []
        for b in range(r.randint(1, 3)):
            c, e = cond(i), expr(i)
            body.append(f"else if ({c}) r{i} <= {e};")
            branches.append((c, e))
        lines.append(f"  always @({edge}) " + " ".join(body))
        chain(i, rst, branches)
    d.stages = ["s1", "s2"] if "s2" in used else ["s1"] if "msk" in used else []
    extra = []
    if r.random() < 0.5:   # unique case, sometimes with overlapping casez items
        k = r.randrange(n)
        if r.random() < 0.5:
            lines.append("  reg [1:0] y;")
            lines.append("  always @* begin y = 2'd0; unique casez ({in0, in1}) "
                         "2'b1?: y = 2'd1; 2'b?1: y = 2'd2; default: y = 2'd3; endcase end")
            d.monitor(("parallel_case", "y"), "1'b1", "(in0 && in1)")             # both items match
            d.monitor(("full_case", "y"), "1'b1", "1'b0")                         # the default always matches
        else:
            lines.append("  reg [1:0] y;")
            lines.append(f"  always @* begin y = 2'd0; unique case (1'b1) r{k}[0]: y = 2'd1; "
                         f"r{k}[1]: y = 2'd2; endcase end")
            d.monitor(("parallel_case", "y"), "1'b1", f"(r{k}[0] && r{k}[1])")
            d.monitor(("full_case", "y"), "1'b1", f"(!r{k}[0] && !r{k}[1])")
        extra.append("y")
    if r.random() < 0.5:   # variable part-select
        k = r.randrange(n)
        lanes = r.randint(2, 5)
        mask = r.randrange(1 << (lanes * 4))
        lines.append(f"  wire [{lanes * 4 - 1}:0] lanes = {{{lanes}{{din}}}} ^ {lanes * 4}'d{mask};")
        lines.append(f"  wire [3:0] sel = lanes[r{k}*4 +: 4];")
        d.monitor(("index_range", "sel"), "1'b1", f"(r{k} > {lanes - 1})")     # r*4 + 3 past the top bit
        extra.append("sel")
    if r.random() < 0.3:   # bit-select with a narrow signed index (negative when its top bit is set)
        k = r.randrange(n)
        top_bit = r.choice(["1'b0", r.choice(ins)])
        lines.append(f"  wire [2:0] lo3 = r{k};")
        lines.append(f"  wire signed [3:0] sidx = {{{top_bit}, lo3}};")
        lines.append("  wire [11:0] vec12 = {3{din}};")
        lines.append("  wire sbit = vec12[sidx];")
        d.monitor(("index_range", "sbit"), "1'b1", "((sidx < 0) || (sidx > 11))")
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
        d.monitor(("mem_addr", "mem.wr0"), "in3", f"(in3 && ({addr}) > {depth - 1})")
        d.monitor(("mem_addr", "mem.rd0"), "1'b1", f"(({addr}) > {depth - 1})")
        extra.append("rd")
    outs = ", ".join([f"r{i}" for i in range(n)] + extra)
    lines.append(f"  assign o = {{{outs}}};")
    lines.append("endmodule")
    d.text = "\n".join(lines) + "\n"
    d.record()
    return d


# -------------------------------------------------------------------- oracle


def _quiet(fn, *a, **kw):
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
        return fn(*a, **kw)


_PROPERTY_STEP = re.compile(r"^\S+ [+-] (\d+) never wraps")


def result_key(res: dict):
    """The generator monitor a result of fvlint's speaks about: its kind and
    target, plus the step for counters (a register can have several)."""
    target = re.sub(r"#\d+$", "", res["target"])          # fvlint numbers checks that share a name
    if res["kind"] in ("counter_overflow", "counter_underflow"):
        m = _PROPERTY_STEP.match(res.get("property") or "")
        return (res["kind"], target, int(m.group(1))) if m else None
    return (res["kind"], target)


def _any(exprs) -> str:
    return " || ".join(exprs) if len(exprs) > 1 else exprs[0]


def oracle_text(design: Design, asserts: list, hold: int, edge: str | None = None) -> tuple[str, int]:
    """The design with the oracle's monitors appended: registers start at
    zero, the reset is held for `hold` steps, and each (condition) in
    `asserts` must never hold while the resets are inactive.  One assertion
    per line, in order, from the line returned after the text.  With `edge`
    (a one-clock job), registers on other clocks or edges are left undriven:
    nothing the assertions depend on reads them, and SymbiYosys' one-clock
    model rejects mixed edges."""
    body = design.text.rstrip("\n").splitlines()
    assert body[-1] == "endmodule"
    if edge is not None:
        def other(line):
            m = re.match(r"\s*always @\((.*?)\)", line)       # clocked blocks only: always @* has no parentheses
            return bool(m) and m.group(1).split(" or ")[0] != edge
        body = ["  // (oracle: on another clock, not modelled here)" if other(ln) else ln for ln in body]
    lines = body[:-1] + [
        "  // ---- fvlint-fuzz oracle: not part of the design fvlint sees",
        "  initial begin " + " ".join(f"{name} = {w}'d0;" for name, w in design.regs) + " end",
        "  (* gclk *) wire fvo_gclk;",
        "  reg [7:0] fvo_n = 8'd0;",
        "  always @(posedge fvo_gclk) if (fvo_n != 8'hff) fvo_n <= fvo_n + 8'd1;",
        f"  always @* if (fvo_n < 8'd{hold}) assume (rst); else assume (!rst);",
        f"  wire fvo_gate = {design.gate};",
    ]
    first = len(lines) + 1
    lines += [f"  always @* if (fvo_gate) assert (!({a}));" for a in asserts]
    lines.append("endmodule")
    return "\n".join(lines) + "\n", first


_SUMMARY_FAIL = re.compile(r"summary:\s+failed assertion \S+ at (\S+?):(\d+)\.\S*(?: steps? (\d+))?")
_DONE = re.compile(r"DONE \((\w+)")


def read_oracle_log(log: str, source: str = "oracle.sv") -> tuple[str, dict]:
    """(status, {line of `source`: earliest failing step}) from a SymbiYosys BMC log."""
    status = "ERROR"
    fails = {}
    for line in log.splitlines():
        m = _SUMMARY_FAIL.search(line)
        if m and m.group(1) == source:
            ln, step = int(m.group(2)), int(m.group(3) or 0)
            fails[ln] = min(step, fails.get(ln, step))
        m = _DONE.search(line)
        if m:
            status = m.group(1)
    return status, fails


def oracle(out: str, design: Design, depth: int, engine_opts, max_depth: int = 80) -> tuple[list, list]:
    """Re-check fvlint's verdicts in `out` against the generator's monitors,
    with plain BMC on the oracle's own copy of the design (see the module
    docstring)."""
    from .tools import Toolchain

    with open(os.path.join(out, "results.json")) as f:
        results = json.load(f)["results"]
    monitors = dict(design.monitors)
    groups, problems, inconclusive = {}, [], []
    for res in results:
        st = res["status"]
        if res["kind"].startswith("fsm_"):
            # fsm_unreachable FAIL: fvlint says this state of the register is never reached.
            sig, _, code = res["target"].partition("=")
            if (res["kind"] == "fsm_unreachable" and st == "FAIL" and re.fullmatch(r"\w+", sig)
                    and re.fullmatch(r"\d+'b[01]+", code)):
                groups.setdefault(("state", res["target"]), []).append(("UNREACHABLE", res))
                monitors[("state", res["target"])] = {"bad": [f"({sig} == {code})"]}
            continue
        if st not in ("PROVEN", "VACUOUS", "FAIL"):
            continue
        key = result_key(res)
        if key not in monitors:
            inconclusive.append(f"{res['id']}: {st}, but the generator has no monitor for it")
            continue
        groups.setdefault(key, []).append((st, res))

    asserts, expect = [], []
    for key, verdicts in groups.items():
        m = monitors[key]
        statuses = {st for st, _ in verdicts}
        ids = ", ".join(sorted(res["id"] for _, res in verdicts))
        if "FAIL" in statuses:
            if statuses != {"FAIL"}:
                inconclusive.append(f"{ids}: FAIL and {'/'.join(sorted(statuses - {'FAIL'}))} for constructs "
                                    "the oracle watches together; only the FAIL is checked")
            step = min(res.get("cex_step") or 0 for st, res in verdicts if st == "FAIL")
            asserts.append(_any(m["bad"]))
            expect.append((ids, "FAIL", step))
            continue
        if statuses == {"VACUOUS"}:                # never even active
            asserts.append(_any(m["en"]))
            expect.append((ids, "VACUOUS", None))
            continue
        if "VACUOUS" in statuses:
            inconclusive.append(f"{ids}: VACUOUS and PROVEN for constructs the oracle watches together; "
                                "only the absence of a violation is checked")
        asserts.append(_any(m["bad"]))                # never goes wrong
        expect.append((ids, "UNREACHABLE" if statuses == {"UNREACHABLE"} else "PROVEN", None))
    if not asserts:
        return problems, inconclusive

    tools = Toolchain.discover()
    timeout = engine_opts.get("timeout", 300)
    d = os.path.join(out, "oracle")
    os.makedirs(d, exist_ok=True)
    # A check whose registers all run on one clock edge is modelled one step
    # per cycle, as fvlint models such a cone; one that spans clocks or edges
    # needs two global steps per cycle.  The generator knows which is which.
    jobs = {}
    for i, a in enumerate(asserts):
        edges = design.clocks_of(f"{a} {design.gate}")
        jobs.setdefault(None if len(edges) > 1 else min(edges, default="posedge clk"), []).append(i)
    for edge, idx in sorted(jobs.items(), key=lambda kv: (kv[0] is None, kv[0] or "")):
        mc = edge is None
        scale = 2 if mc else 1
        hold = (1 + len(design.stages)) * scale
        steps = [expect[i][2] for i in idx if expect[i][1] == "FAIL"]
        bound = min(max([depth] + [s + 4 for s in steps]), max_depth) * scale
        name = ("oracle_mc" if mc else "oracle" if edge == "posedge clk"
                else "oracle_" + edge.replace(" ", "_"))
        text, first = oracle_text(design, [asserts[i] for i in idx], hold, edge)
        with open(os.path.join(d, f"{name}.sv"), "w") as f:
            f.write(text)
        with open(os.path.join(d, f"{name}.sby"), "w") as f:
            f.write("[options]\nmode bmc\n" f"depth {bound}\n" f"timeout {int(timeout)}\n"
                    + ("multiclock on\n" if mc else "")
                    + f"\n[engines]\nsmtbmc --keep-going {tools.solver or ''}\n\n[script]\n"
                      f"read_verilog -formal -sv {name}.sv\nprep -top {design.top}\n\n[files]\n{name}.sv\n")
        tools.run_sby(os.path.join(d, f"{name}.sby"), d, timeout)
        log = ""
        log_path = os.path.join(d, name, "logfile.txt")
        if os.path.exists(log_path):
            with open(log_path, errors="replace") as f:
                log = f.read()
        status, fails = read_oracle_log(log, f"{name}.sv")
        finished = status in ("PASS", "FAIL")
        for n, i in enumerate(idx):
            ids, st, step = expect[i]
            failed = (first + n) in fails
            # A violation the oracle finds is a definite witness, even if its
            # job then timed out; *not* finding one only counts if the search
            # finished deep enough.  fvlint's step counts cycles when the
            # check's own cone has one clock: scale it like the oracle's.
            if st == "PROVEN" and failed:
                problems.append(f"{ids}: fvlint PROVEN, oracle found a violation at step {fails[first + n]}")
            elif st == "VACUOUS" and failed:
                problems.append(f"{ids}: fvlint VACUOUS, oracle reached the check's condition")
            elif st == "UNREACHABLE" and failed:
                problems.append(f"{ids}: fvlint says unreachable, oracle reached it")
            elif st == "FAIL" and not failed:
                if finished and (step + 4) * scale <= bound:
                    problems.append(f"{ids}: fvlint FAIL, oracle found no violation within {bound} steps")
                else:
                    inconclusive.append(f"{ids}: FAIL at step {step} beyond the oracle's reach "
                                        f"(bound {bound}, job {status})")
            elif not finished and not failed:
                inconclusive.append(f"{ids}: {st} not confirmed, oracle job {status}")
    return problems, inconclusive


# ------------------------------------------------------------------- driver


def run(seeds, outroot: str, depth: int = 24, extra_args=(), verbose=False) -> dict:
    from . import cli
    os.makedirs(outroot, exist_ok=True)
    summary = {"seeds": 0, "checks": 0, "problems": [], "inconclusive": [], "statuses": {}, "seconds": 0.0}
    t0 = time.time()
    for seed in seeds:
        design = generate(seed)
        d = os.path.join(outroot, f"seed{seed}")
        os.makedirs(d, exist_ok=True)
        src = os.path.join(d, f"{design.top}.v")
        with open(src, "w") as f:
            f.write(design.text)
        rc = _quiet(cli.main, ["--top", design.top, src, "-o", d, "-j", "1", *extra_args])
        summary["seeds"] += 1
        if rc == 2 or not os.path.exists(os.path.join(d, "results.json")):
            summary["problems"].append(f"seed {seed}: fvlint did not complete (rc={rc}), see {d}")
            continue
        with open(os.path.join(d, "results.json")) as f:
            res = json.load(f)["results"]
        for x in res:
            summary["statuses"][x["status"]] = summary["statuses"].get(x["status"], 0) + 1
        summary["checks"] += len(res)
        probs, inconc = oracle(d, design, depth, {})
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
