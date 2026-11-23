# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""fvlint.fuzz: the design generator, its monitors, and the oracle's judging
logic.  The oracle's SymbiYosys run is faked; everything around it is real."""

from __future__ import annotations

import json
import os
import re
import unittest
from unittest import mock

from fvlint import cli, fuzz
from fvlint.fuzz import Design
from fvlint.tools import Toolchain

from .support import TempDirCase, captured

IDENT = re.compile(r"(?<!')\b[A-Za-z_]\w*\b")


class Generator(unittest.TestCase):
    def test_deterministic_per_seed(self):
        self.assertEqual(fuzz.generate(7), fuzz.generate(7))
        self.assertNotEqual(fuzz.generate(7).text, fuzz.generate(8).text)
        d = fuzz.generate(42)
        self.assertEqual(d.top, "fz42")
        self.assertTrue(d.text.startswith("module fz42 (") and d.text.endswith("endmodule\n"))

    def test_shape(self):
        for seed in range(1, 60):
            text = fuzz.generate(seed).text
            with self.subTest(seed=seed):
                regs = re.findall(r"reg \[(\d+):0\] r(\d+);", text)
                self.assertTrue(2 <= len(regs) <= 4)
                self.assertTrue(all(1 <= int(w) <= 4 for w, _ in regs))           # 2..5-bit registers
                self.assertEqual([int(i) for _, i in regs], list(range(len(regs))))
                outs = re.search(r"assign o = \{(.*)\};", text).group(1).split(", ")
                self.assertEqual(outs[:len(regs)], [f"r{i}" for i in range(len(regs))])   # nothing optimised away
                declared = set(re.findall(r"(?:reg|wire)(?: signed)?(?: \[[^\]]*\])? (\w+)", text))
                self.assertLessEqual(set(outs), declared)
                self.assertEqual(text.count("module "), 1)
                self.assertEqual(text.splitlines()[-1], "endmodule")

    def test_every_feature_is_generated(self):
        texts = "\n".join(fuzz.generate(s).text for s in range(1, 120))
        for feature in ("posedge clk2", "negedge clk", "unique casez", "unique case (1'b1)", "*4 +: 4]",
                        "reg [3:0] mem [0:", "else if (r", "<= 1'b1; else ok", "r0 - ",
                        "s1 <= rst; s2 <= s1;", "if (s2) r", "msk <= 1'b1; else msk <= s1", "if (msk) r",
                        "wire signed [3:0] sidx = {in", "wire signed [3:0] sidx = {1'b0",
                        "else case (st) 2'd0: st <=", "endcase if (in", "endcase end", "if (s2) st <="):
            with self.subTest(feature=feature):
                self.assertIn(feature, texts)

    def test_a_monitor_for_every_counter_step(self):
        for seed in range(1, 80):
            d = fuzz.generate(seed)
            with self.subTest(seed=seed):
                sites = set()
                for reg, op, k in re.findall(r"(\w+) <= \1 ([+-]) \d+'d(\d+);", d.text):
                    sites.add(("counter_overflow" if op == "+" else "counter_underflow", reg, int(k)))
                self.assertEqual({k for k in d.monitors if k[0].startswith("counter")}, sites)

    def test_monitors_only_name_signals_of_the_design(self):
        for seed in range(1, 80):
            d = fuzz.generate(seed)
            declared = set(IDENT.findall(d.text))
            for key, m in d.monitors.items():
                with self.subTest(seed=seed, key=key):
                    self.assertEqual(len(m["en"]), len(m["bad"]))
                    self.assertLessEqual(set(IDENT.findall(" ".join(m["en"] + m["bad"]))), declared)

    def test_monitors_of_a_known_design(self):
        # Seed 10 (two credit counters, a bounded and a plain one, a signed
        # bit-select, a memory): the generator's own account of each construct.
        m = fuzz.generate(10).monitors
        self.assertEqual(m[("counter_overflow", "r0", 1)],
                         {"en": ["(!(rst) && (in3 && ok0))"], "bad": ["(!(rst) && (in3 && ok0) && (r0 > 2'd2))"]})
        self.assertEqual(m[("counter_underflow", "r0", 1)]["bad"],
                         ["(!(rst) && !(in3 && ok0) && (in2 && r0 != 2'd0) && (r0 < 2'd1))"])
        self.assertEqual(m[("counter_overflow", "r1", 3)]["bad"], ["(!(rst) && ((r3 == 2'd1)) && (r1 > 5'd28))"])
        self.assertEqual(m[("counter_overflow", "r3", 1)]["bad"],
                         ["(!(rst) && !(r3 == 2'd3) && ((r0 == 2'd0)) && (r3 > 2'd2))"])
        self.assertEqual(m[("index_range", "sbit")]["bad"], ["((sidx < 0) || (sidx > 11))"])
        self.assertEqual(m[("mem_addr", "mem.wr0")], {"en": ["in3"], "bad": ["(in3 && (r2[3:0]) > 9)"]})
        self.assertEqual(m[("mem_addr", "mem.rd0")], {"en": ["1'b1"], "bad": ["((r2[3:0]) > 9)"]})
        self.assertEqual(m[("index_range", "sbit")]["en"], ["1'b1"])               # always evaluated
        # Settled-without-proof constructs come on top (their own random stream).
        self.assertEqual(m[("full_case", "fx")], {"en": ["1'b1"], "bad": ["(!(in2) && !(!in2))"]})
        self.assertEqual(m[("parallel_case", "fx")]["bad"], ["((in2) && (!in2))"])
        self.assertEqual(len(m), 11)

    def test_case_and_part_select_monitors(self):
        seen = set()
        for seed in range(1, 80):
            d = fuzz.generate(seed)
            m = d.monitors
            if "unique casez" in d.text:
                self.assertEqual((m[("parallel_case", "y")]["bad"], m[("full_case", "y")]["bad"]),
                                 (["(in0 && in1)"], ["1'b0"]))                   # the default always matches
                self.assertEqual((m[("parallel_case", "y")]["en"], m[("full_case", "y")]["en"]), (["1'b1"], ["1'b1"]))
                self.assertNotIn("y", d.clock)                                    # combinational
                self.assertLessEqual({"in0", "in1"}, d.reads["y"])
                seen.add("casez")
            elif "unique case" in d.text:
                k = re.search(r"unique case \(1'b1\) r(\d+)\[0\]", d.text).group(1)
                self.assertEqual(m[("parallel_case", "y")]["bad"], [f"(r{k}[0] && r{k}[1])"])
                self.assertEqual(m[("full_case", "y")]["bad"], [f"(!r{k}[0] && !r{k}[1])"])
                self.assertEqual((m[("parallel_case", "y")]["en"], m[("full_case", "y")]["en"]), (["1'b1"], ["1'b1"]))
                seen.add("onehot")
            lanes = re.search(r"wire \[(\d+):0\] lanes = .*\n.*lanes\[r(\d+)\*4", d.text)
            if lanes:
                top, k = lanes.groups()
                self.assertEqual(m[("index_range", "sel")], {"en": ["1'b1"],
                                                             "bad": [f"(r{k} > {(int(top) + 1) // 4 - 1})"]})
                seen.add("lanes")
        self.assertEqual(seen, {"casez", "onehot", "lanes"})

    def test_settled_constructs(self):
        # Constructs fvlint can settle without a proof: drawn from their own
        # stream, so the rest of each design is what it was without them.
        seen = set()
        for seed in range(1, 80):
            d = fuzz.generate(seed)
            m, text = d.monitors, d.text
            with self.subTest(seed=seed):
                self.assertEqual("output [31:0] o2" in text, "assign o2 = {" in text)
                if "reg [1:0] pv;" in text:
                    k = re.search(r"else case \(st\) 2'd(\d): begin \(\* parallel_case \*\)", text).group(1)
                    self.assertEqual(m[("parallel_case", "pv")]["en"], [f"(st == 2'd{k})"])
                    self.assertTrue(m[("parallel_case", "pv")]["bad"][0].startswith(f"(st == 2'd{k} && ("))
                    self.assertIn("reg [1:0] st;", text)                     # only inside the FSM
                    seen.add("nested")
                if "ud <= ud - " in text:
                    self.assertIn(("counter_overflow", "ud", 1), m)
                    self.assertIn(("counter_underflow", "ud", 1), m)
                    self.assertEqual("initial ud = " in text, ("ud", int(re.search(r"reg \[(\d)", text[
                        text.index("ud;") - 12:]).group(1)) + 1) not in d.regs)
                    seen.add("updown-initial" if "initial ud = " in text else "updown")
                self.assertEqual(d.x_defaults, {"fx"} if "fx = 2'bx;" in text else set())
                if "fv = 2'd3;" in text:
                    self.assertIn(("full_case", "fv"), m)
                    seen.add("full_case-value")
                if d.x_defaults:
                    seen.add("full_case-x")
                pe = re.search(r"localparam PE = (\d);", text)
                if pe:
                    keys = {k for k in m if k[1] == "pq"}
                    self.assertEqual(len(keys), 1)
                    self.assertEqual(d.required, keys if pe.group(1) == "1" else set())
                    self.assertIn("PE && pq", " ".join(m[next(iter(keys))]["en"]))
                    seen.add(f"param{pe.group(1)}")
                else:
                    self.assertEqual(d.required, set())
                if d.args:
                    self.assertEqual(d.args[0], "--horizon")
                    self.assertIn(int(d.args[1]), (6, 8, 12, 16))
                    seen.add("horizon")
        self.assertEqual(seen, {"nested", "updown", "updown-initial", "full_case-x", "full_case-value", "param0",
                                "param1", "horizon"})

    def test_state_machines(self):
        # Pinned: a plain one, one overridden after the reset branch, one with an unconditional arm.
        lines = lambda seed: [x for x in fuzz.generate(seed).text.splitlines() if " st" in x or "busy" in x]
        self.assertEqual(lines(5), [
            "  reg [1:0] st;",
            "  always @(posedge clk) begin if (rst) st <= 2'd1; else case (st) 2'd0: st <= in0 ? 2'd3 : 2'd0; "
            "2'd1: st <= in3 ? 2'd1 : 2'd3; 2'd2: st <= in1 ? 2'd1 : 2'd0; 2'd3: st <= in2 ? 2'd3 : 2'd1; endcase end",
            "  wire busy = (st == 2'd1) || (st == 2'd2);",
            "  assign o = {r0, r1, r2, r3, busy, sel, rd};"])
        self.assertEqual(lines(8)[1],
                         "  always @(posedge clk) begin if (s2) st <= 2'd2; else case (st) "
                         "2'd0: st <= in2 ? 2'd1 : 2'd0; 2'd1: st <= in0 ? 2'd1 : 2'd3; "
                         "2'd2: st <= in0 ? 2'd0 : 2'd2; 2'd3: st <= in0 ? 2'd2 : 2'd3; "
                         "endcase if (in2 && in3) st <= 2'd0; end")
        self.assertEqual(lines(12)[1],
                         "  always @(posedge clk) begin if (rst) st <= 2'd0; else case (st) 2'd0: st <= 2'd3; "
                         "2'd1: st <= in0 ? 2'd2 : 2'd1; 2'd2: st <= in1 ? 2'd3 : 2'd2; 2'd3: st <= in0 ? 2'd0 : 2'd3; "
                         "endcase if (in3 && in2) st <= 2'd1; end")
        self.assertNotIn("reg [1:0] st;", fuzz.generate(7).text)

    def test_reset_stages(self):
        # Only the synchronizer stages something uses survive elaboration.
        self.assertEqual(fuzz.generate(4).stages, ["s1", "s2"])         # a register resets on s2
        self.assertEqual(fuzz.generate(9).stages, ["s1"])               # s2 unused; s1 feeds msk, which is used
        self.assertEqual(fuzz.generate(50).stages, [])                  # synchronizer present but unused
        self.assertEqual(fuzz.generate(31).stages, ["s1", "s2"])        # the state machine resets on s2
        self.assertIn(("st", 2), fuzz.generate(31).regs)
        self.assertEqual(fuzz.generate(10).stages, [])                  # no synchronizer
        self.assertEqual(fuzz.generate(9).regs, [("r0", 4), ("r1", 4), ("r2", 3), ("s1", 1), ("s2", 1), ("msk", 1)])
        self.assertEqual(fuzz.generate(10).regs, [("r0", 2), ("r1", 5), ("r2", 5), ("r3", 2), ("ok0", 1), ("ok2", 1)])

    def test_clocks_and_dependencies(self):
        # Seed 7: r2 runs on clk2 and the memory address is r2; r1's checks
        # depend on clk registers only.
        d = fuzz.generate(7)
        self.assertEqual(d.clock, {"r0": "posedge clk", "ok1": "posedge clk", "r1": "posedge clk",
                                   "r2": "posedge clk2", "mem": "posedge clk", "ud": "posedge clk"})
        self.assertEqual(d.reads["sel"], {"wire", "lanes", "r1"})
        self.assertEqual(d.clocks_of(" ".join(d.monitors[("counter_overflow", "r1", 1)]["bad"])), {"posedge clk"})
        self.assertEqual(d.clocks_of(" ".join(d.monitors[("mem_addr", "mem.rd0")]["bad"])),
                         {"posedge clk", "posedge clk2"})
        self.assertEqual(d.clocks_of("in0 && din"), set())
        neg = next(fuzz.generate(s) for s in range(1, 80) if "negedge clk" in fuzz.generate(s).text)
        self.assertIn("negedge clk", set(neg.clock.values()))
        sync = fuzz.generate(9)                                         # through wires and the synchronizer
        self.assertEqual(sync.clocks_of("msk"), {"posedge clk"})
        self.assertTrue({"rst", "s1"} <= sync.reads["s2"] and "rst" in sync.reads["s1"])


def design(**kw):
    text = "module t (input clk, input rst, input e, output [3:0] o);\n  reg [3:0] q;\nendmodule\n"
    return Design(**dict(dict(text=text, top="t", regs=[("q", 4)]), **kw))


def row(cid, status, prop="", step=None):
    kind, _, target = cid.partition(":")
    return {"id": cid, "kind": kind, "target": target, "property": prop, "status": status, "cex_step": step}


def info(cid, reason, prop=""):
    return dict(row(cid, "INFO", prop), reason=reason)


class OracleText(unittest.TestCase):
    def test_monitors_are_appended(self):
        d = design(stages=["s1", "s2"], regs=[("q", 4), ("s1", 1)])
        text, first = fuzz.oracle_text(d, ["(a)", "(b && c)"], 3)
        lines = text.splitlines()
        self.assertEqual(lines[:2], d.text.splitlines()[:2])           # the design itself, unchanged
        self.assertIn("  initial begin q = 4'd0; s1 = 1'd0; end", lines)
        self.assertIn("  always @* if (fvo_n < 8'd3) assume (rst); else assume (!rst);", lines)
        self.assertIn("  wire fvo_gate = !rst && !s2;", lines)
        self.assertEqual(lines[first - 1:], ["  always @* if (fvo_gate) assert (!((a)));",
                                             "  always @* if (fvo_gate) assert (!((b && c)));", "endmodule"])
        self.assertEqual(text.count("endmodule"), 1)
        self.assertIn("  wire fvo_gate = !rst;", fuzz.oracle_text(design(), ["x"], 1)[0])
        self.assertIn("  wire fvo_gate = !rst && !s1;", fuzz.oracle_text(design(stages=["s1"]), ["x"], 1)[0])

    def test_one_clock_jobs_leave_other_clocks_out(self):
        text = ("module t (input clk, input clk2, input rst, input e);\n  reg a, b, c;\n"
                "  always @(posedge clk or posedge e) if (e) a <= 1'b1; else a <= rst;\n"
                "  always @(negedge clk) b <= a;\n  always @(posedge clk2) c <= b;\n"
                "  always @* begin end\nendmodule\n")
        d = Design(text, "t", regs=[("a", 1), ("b", 1), ("c", 1)])
        lines = fuzz.oracle_text(d, ["(a)"], 1, "posedge clk")[0].splitlines()
        self.assertEqual(lines[2:6], ["  always @(posedge clk or posedge e) if (e) a <= 1'b1; else a <= rst;",
                                      "  // (oracle: on another clock, not modelled here)",
                                      "  // (oracle: on another clock, not modelled here)",
                                      "  always @* begin end"])
        lines = fuzz.oracle_text(d, ["(b)"], 1, "negedge clk")[0].splitlines()
        self.assertEqual(lines[2:4], ["  // (oracle: on another clock, not modelled here)",
                                      "  always @(negedge clk) b <= a;"])
        self.assertEqual(fuzz.oracle_text(d, ["(c)"], 1)[0].splitlines()[2:5], text.splitlines()[2:5])   # two clocks

    def test_log(self):
        log = ("SBY 1:00:00 [run] summary: counterexample trace: run/engine_0/trace0.vcd\n"
               "SBY 1:00:00 [run] summary:   failed assertion t._witness_.check_oracle_sv_12_assert_3 at "
               "oracle.sv:12.27-12.40\n"
               "SBY 1:00:00 [run] summary: counterexample trace: run/engine_0/trace1.vcd\n"
               "SBY 1:00:00 [run] summary:   failed assertion t._witness_.check_oracle_sv_14_assert_5 at "
               "oracle.sv:14.27-14.40 steps 7, 9\n"
               "SBY 1:00:00 [run] summary:   failed assertion t._witness_.check_oracle_sv_12_assert_3 at "
               "oracle.sv:12.27-12.40 step 9\n"
               "SBY 1:00:00 [run] DONE (FAIL, rc=2)\n")
        self.assertEqual(fuzz.read_oracle_log(log), ("FAIL", {12: 0, 14: 7}))
        self.assertEqual(fuzz.read_oracle_log(""), ("ERROR", {}))
        self.assertEqual(fuzz.read_oracle_log("SBY [run] DONE (TIMEOUT, rc=8)\n"), ("TIMEOUT", {}))

    def test_full_summary(self):
        # SBY's log lists five traces, then "and N further traces"; the rest
        # are only in the job's full summary file (here as yices reported
        # seed 13 of the fuzzer: one trace per assertion).
        traces = [(28, 1), (26, 2), (25, 2), (27, 2), (29, 5), (30, 5)]
        log = "".join(f"SBY 1:00:00 [oracle] summary: counterexample trace: oracle/engine_0/trace{i}.vcd\n"
                      f"SBY 1:00:00 [oracle] summary:   failed assertion fz13._witness_.check_oracle_sv_{ln}_assert_1 "
                      f"at oracle.sv:{ln}.27-{ln}.66 step {st}\n" for i, (ln, st) in enumerate(traces[:5]))
        log += ("SBY 1:00:00 [oracle] summary: and 1 further trace\n"
                "SBY 1:00:00 [oracle] summary: see oracle/FAIL for a complete summary\n"
                "SBY 1:00:00 [oracle] DONE (FAIL, rc=2)\n")
        summary = ("engine_0 (smtbmc --keep-going yices) returned FAIL\n"
                   + "".join(f"counterexample trace: engine_0/trace{i}.vcd\n"
                             f"  failed assertion fz13._witness_.check_oracle_sv_{ln}_assert_1 at "
                             f"oracle.sv:{ln}.27-{ln}.66 step {st}\n" for i, (ln, st) in enumerate(traces)))
        self.assertNotIn(30, fuzz.read_oracle_log(log)[1])
        self.assertEqual(fuzz.read_oracle_log(log, summary=summary), ("FAIL", dict(traces)))
        self.assertEqual(fuzz.read_oracle_log("", summary=summary)[0], "ERROR")    # the status comes from the log
        self.assertEqual(fuzz.read_oracle_log(log, "other.sv", summary), ("FAIL", {}))

    def test_result_key(self):
        self.assertEqual(fuzz.result_key(row("counter_overflow:r0#1", "FAIL", "r0 + 2 never wraps past 15 (4 bits)")),
                         ("counter_overflow", "r0", 2))
        self.assertEqual(fuzz.result_key(row("counter_underflow:r1", "PROVEN", "r1 - 3 never wraps below 0")),
                         ("counter_underflow", "r1", 3))
        self.assertIsNone(fuzz.result_key(row("counter_overflow:r1", "PROVEN", "something else")))
        self.assertEqual(fuzz.result_key(row("mem_addr:mem.wr0", "PROVEN")), ("mem_addr", "mem.wr0"))


class Oracle(TempDirCase):
    OVF = ("counter_overflow", "q", 1)

    def setUp(self):
        super().setUp()
        self.d = design(monitors={self.OVF: {"en": ["(e)"], "bad": ["(e && q > 4'd14)"]},
                                  ("counter_underflow", "q", 1): {"en": ["(!e)"], "bad": ["(!e && q < 4'd1)"]},
                                  ("mem_addr", "m.wr0"): {"en": ["e"], "bad": ["(e && q > 9)"]}})

    def outdir(self, rows, meta=None):
        d = os.path.join(self.tmp, "out")
        os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, "results.json"), "w") as f:
            json.dump({"meta": meta or {}, "results": rows}, f)
        return d

    def oracle(self, rows, fails=None, status="PASS", design=None, depth=24, max_depth=80, opts=None,
               log_limit=None, meta=None):
        """fails: {text of a condition: step}; the fake SymbiYosys reports
        every assertion whose line contains that text as failed at that step.
        It writes them all to the full summary file, and the first `log_limit`
        of them (all by default) to the log's short summary, as SBY does."""
        fails = fails or {}
        self.runs, self.texts = [], []

        class Tools:
            solver = "z3"

            def run_sby(tools, sby, cwd, timeout):
                with open(sby) as f:
                    text = f.read()
                self.runs.append((text, timeout))
                sv = text.rstrip().splitlines()[-1]
                with open(os.path.join(cwd, sv)) as f:
                    self.texts.append(f.read())
                found = []
                for n, line in enumerate(self.texts[-1].splitlines(), 1):
                    for cond, step in fails.items():
                        if "assert (" in line and cond in line:
                            found.append(f"  failed assertion t.x at {sv}:{n}.1-1.2 step {step}\n")
                shown = found if log_limit is None else found[:log_limit]
                log = "".join(f"SBY [run] summary: {ln}" for ln in shown)
                if len(shown) < len(found):
                    log += f"SBY [run] summary: and {len(found) - len(shown)} further traces\n"
                name = os.path.splitext(sv)[0]
                os.makedirs(os.path.join(cwd, name), exist_ok=True)
                with open(os.path.join(cwd, name, "logfile.txt"), "w") as f:
                    f.write(log + f"SBY [run] DONE ({status}, rc=0)\n")
                with open(os.path.join(cwd, name, status), "w") as f:
                    f.write("".join(found))
                return 0
        with mock.patch.object(Toolchain, "discover", staticmethod(lambda solver=None: Tools())):
            return fuzz.oracle(self.outdir(rows, meta), design or self.d, depth, opts or {}, max_depth)

    @property
    def text(self):
        return "\n".join(self.texts)

    def asserts(self):
        return [ln.strip() for ln in self.text.splitlines() if "assert (" in ln]

    def test_agreeing_verdicts(self):
        rows = [row("counter_overflow:q", "PROVEN", "q + 1 never wraps past 15 (4 bits)"),
                row("counter_underflow:q", "VACUOUS", "q - 1 never wraps below 0"),
                row("mem_addr:m.wr0", "FAIL", step=5), row("counter_overflow:other", "INFO")]
        self.assertEqual(self.oracle(rows, fails={"(e && q > 9)": 3}), ([], []))
        self.assertEqual(self.asserts(), ["always @* if (fvo_gate) assert (!((e && q > 4'd14)));",   # PROVEN: never bad
                                          "always @* if (fvo_gate) assert (!((!e)));",   # VACUOUS: never even active
                                          "always @* if (fvo_gate) assert (!((e && q > 9)));"])     # FAIL: must fail
        (sby, timeout), = self.runs
        self.assertEqual(sby, "[options]\nmode bmc\ndepth 24\ntimeout 300\n\n[engines]\nsmtbmc --keep-going z3\n\n"
                              "[script]\nread_verilog -formal -sv oracle.sv\nprep -top t\n\n[files]\noracle.sv\n")
        self.assertEqual(timeout, 300)
        self.assertIn("assume (rst); else assume (!rst);", self.text)
        self.assertIn("fvo_n < 8'd1)", self.text)                       # no synchronizer: one cycle of reset

    def test_disagreements(self):
        rows = [row("counter_overflow:q", "PROVEN", "q + 1 never wraps past 15 (4 bits)"),
                row("counter_underflow:q", "VACUOUS", "q - 1 never wraps below 0"),
                row("mem_addr:m.wr0", "FAIL", step=3)]
        problems, inconclusive = self.oracle(rows, fails={"q > 4'd14": 6, "(!e)": 2}, status="FAIL")
        self.assertEqual(problems, ["counter_overflow:q: fvlint PROVEN, oracle found a violation at step 6",
                                    "counter_underflow:q: fvlint VACUOUS, oracle reached the check's condition",
                                    "mem_addr:m.wr0: fvlint FAIL, oracle found no violation within 24 steps"])
        self.assertEqual(inconclusive, [])

    def test_failures_past_the_short_summary(self):
        # The log's summary stops after a few traces; the oracle must read the
        # job's full summary file for the rest (seed 13 in CI, with yices).
        rows = [row("counter_overflow:q", "FAIL", "q + 1 never wraps past 15 (4 bits)", step=4),
                row("counter_underflow:q", "FAIL", "q - 1 never wraps below 0", step=1),
                row("mem_addr:m.wr0", "FAIL", step=5)]
        fails = {"q > 4'd14": 4, "q < 4'd1": 1, "q > 9": 5}
        self.assertEqual(self.oracle(rows, fails=fails, status="FAIL", log_limit=1), ([], []))
        problems, _ = self.oracle(rows, fails={"q > 4'd14": 4, "q < 4'd1": 1}, status="FAIL", log_limit=1)
        self.assertEqual(problems, ["mem_addr:m.wr0: fvlint FAIL, oracle found no violation within 24 steps"])

    def test_fail_beyond_the_oracle(self):
        problems, inconclusive = self.oracle([row("mem_addr:m.wr0", "FAIL", step=90)])
        self.assertEqual(problems, [])
        self.assertIn("depth 80\n", self.runs[0][0])                     # capped at max_depth
        self.assertEqual(inconclusive,
                         ["mem_addr:m.wr0: FAIL at step 90 beyond the oracle's reach (bound 80, job PASS)"])
        self.oracle([row("mem_addr:m.wr0", "FAIL", step=30)])
        self.assertIn("depth 34\n", self.runs[0][0])                     # step + 4

    def test_unfinished_oracle_job(self):
        rows = [row("mem_addr:m.wr0", "FAIL", step=2), row("counter_overflow:q", "PROVEN", "q + 1 never wraps")]
        problems, inconclusive = self.oracle(rows, status="TIMEOUT")
        self.assertEqual(problems, [])
        self.assertEqual(inconclusive,
                         ["mem_addr:m.wr0: FAIL at step 2 beyond the oracle's reach (bound 24, job TIMEOUT)",
                          "counter_overflow:q: PROVEN not confirmed, oracle job TIMEOUT"])
        problems, _ = self.oracle(rows, fails={"q > 4'd14": 3}, status="TIMEOUT")    # a found violation counts
        self.assertEqual(problems, ["counter_overflow:q: fvlint PROVEN, oracle found a violation at step 3"])

    def test_grouping(self):
        two = {"en": ["(a)", "(b)"], "bad": ["(a && q > 4'd13)", "(b && q > 4'd13)"]}
        d = design(monitors={("counter_overflow", "q", 2): two})
        rows = [row("counter_overflow:q", "PROVEN", "q + 2 never wraps past 15 (4 bits)"),
                row("counter_overflow:q#1", "PROVEN", "q + 2 never wraps past 15 (4 bits)")]
        self.assertEqual(self.oracle(rows, design=d), ([], []))
        self.assertEqual(self.asserts(), ["always @* if (fvo_gate) assert (!((a && q > 4'd13) || (b && q > 4'd13)));"])
        rows[1]["status"] = "VACUOUS"
        problems, inconclusive = self.oracle(rows, design=d)
        self.assertEqual((problems, self.asserts()),
                         ([], ["always @* if (fvo_gate) assert (!((a && q > 4'd13) || (b && q > 4'd13)));"]))
        self.assertEqual(inconclusive, ["counter_overflow:q, counter_overflow:q#1: VACUOUS and PROVEN for constructs "
                                        "the oracle watches together; only the absence of a violation is checked"])
        rows[1]["status"], rows[1]["cex_step"] = "FAIL", 4
        problems, inconclusive = self.oracle(rows, design=d, fails={"q > 4'd13": 2})
        self.assertEqual(problems, [])
        self.assertEqual(inconclusive, ["counter_overflow:q, counter_overflow:q#1: FAIL and PROVEN for constructs "
                                        "the oracle watches together; only the FAIL is checked"])

    def test_checks_without_a_monitor(self):
        rows = [row("index_range:sel", "PROVEN"), row("counter_overflow:q", "FAIL", "q + 3 never wraps", 2),
                row("counter_overflow:q#1", "UNKNOWN", "q + 1 never wraps")]
        problems, inconclusive = self.oracle(rows)
        self.assertEqual(problems, [])
        self.assertEqual(inconclusive, ["index_range:sel: PROVEN, but the generator has no monitor for it",
                                        "counter_overflow:q: FAIL, but the generator has no monitor for it"])
        self.assertEqual(self.runs, [])                                 # nothing left to check: no job

    def test_unreachable_fsm_state(self):
        rows = [row("fsm_unreachable:q=4'b1010", "FAIL"), row("fsm_unreachable:q=4'd3", "FAIL"),
                row("fsm_unreachable:a.b=2'b01", "FAIL"), row("fsm_unreachable:q=4'b0001", "PROVEN")]
        self.assertEqual(self.oracle(rows), ([], []))
        self.assertEqual(self.asserts(), ["always @* if (fvo_gate) assert (!((q == 4'b1010)));"])
        problems, _ = self.oracle(rows[:1], fails={"q == 4'b1010": 1})
        self.assertEqual(problems, ["fsm_unreachable:q=4'b1010: fvlint says unreachable, oracle reached it"])
        self.assertNotIn(("state", "q=4'b1010"), self.d.monitors)      # the design's own monitors are untouched

    def test_clock_domains_get_their_own_jobs(self):
        # q and a run on clk, p on clk2, and q's increment depends on p: that
        # check spans two clocks; the memory address (a) check does not.
        mon = {("counter_overflow", "q", 1): {"en": ["(e && p)"], "bad": ["(e && p && q > 4'd14)"]},
               ("mem_addr", "m.wr0"): {"en": ["e"], "bad": ["(e && a > 9)"]}}
        d = design(monitors=mon, stages=["s1", "s2"],
                   clock={"q": "posedge clk", "a": "posedge clk", "p": "posedge clk2", "s1": "posedge clk",
                          "s2": "posedge clk"},
                   reads={"q": {"p"}, "a": {"e"}, "s2": {"s1"}, "s1": {"rst"}})
        rows = [row("mem_addr:m.wr0", "FAIL", step=25), row("counter_overflow:q", "PROVEN", "q + 1 never wraps")]
        problems, inconclusive = self.oracle(rows, design=d, depth=10, max_depth=30, fails={"a > 9": 20})
        self.assertEqual((problems, inconclusive), ([], []))
        (one, _), (two, _) = self.runs
        self.assertIn("[files]\noracle.sv\n", one)
        self.assertNotIn("multiclock", one)
        self.assertIn("depth 29\n", one)                                 # step + 4, one step per cycle
        self.assertIn("[files]\noracle_mc.sv\n", two)
        self.assertIn("multiclock on\n", two)
        self.assertIn("depth 20\n", two)                                 # two global steps per cycle
        self.assertIn("fvo_n < 8'd3)", self.texts[0])                    # (1 + 2 stages) cycles
        self.assertIn("fvo_n < 8'd6)", self.texts[1])                    # ... doubled
        self.assertIn("wire fvo_gate = !rst && !s2;", self.texts[1])
        self.assertEqual([[ln.strip() for ln in t.splitlines() if "assert (" in ln] for t in self.texts],
                         [["always @* if (fvo_gate) assert (!((e && a > 9)));"],
                          ["always @* if (fvo_gate) assert (!((e && p && q > 4'd14)));"]])
        # A step of fvlint's that counts cycles is scaled to global steps in a two-clock job.
        mon[("mem_addr", "m.wr0")] = {"en": ["e"], "bad": ["(e && p && a > 9)"]}
        problems, inconclusive = self.oracle(rows[:1], design=d, depth=10, max_depth=30)
        self.assertIn("depth 58\n", self.runs[0][0])
        self.assertEqual(problems, ["mem_addr:m.wr0: fvlint FAIL, oracle found no violation within 58 steps"])
        rows[0]["cex_step"] = 27
        problems, inconclusive = self.oracle(rows[:1], design=d, depth=10, max_depth=30)
        self.assertEqual((problems, inconclusive),
                         ([], ["mem_addr:m.wr0: FAIL at step 27 beyond the oracle's reach (bound 60, job PASS)"]))

    def test_a_job_per_clock_edge(self):
        mon = {("counter_overflow", "q", 1): {"en": ["(e)"], "bad": ["(e && q > 4'd14)"]},
               ("counter_overflow", "n", 1): {"en": ["(e)"], "bad": ["(e && n > 4'd14)"]},
               ("parallel_case", "y"): {"en": ["1'b1"], "bad": ["(e && f)"]}}
        d = design(monitors=mon, clock={"q": "posedge clk", "n": "negedge clk"})
        rows = [row("counter_overflow:q", "PROVEN", "q + 1 never wraps"),
                row("counter_overflow:n", "PROVEN", "n + 1 never wraps"), row("parallel_case:y", "PROVEN")]
        self.assertEqual(self.oracle(rows, design=d), ([], []))
        self.assertEqual([r[0].rstrip().splitlines()[-1] for r in self.runs],
                         ["oracle_negedge_clk.sv", "oracle.sv"])
        self.assertEqual([[ln.strip() for ln in t.splitlines() if "assert (" in ln] for t in self.texts],
                         [["always @* if (fvo_gate) assert (!((e && n > 4'd14)));"],
                          ["always @* if (fvo_gate) assert (!((e && q > 4'd14)));",
                           "always @* if (fvo_gate) assert (!((e && f)));"]])      # no registers: any one-clock job
        problems, _ = self.oracle(rows, design=d, fails={"n > 4'd14": 4})
        self.assertEqual(problems, ["counter_overflow:n: fvlint PROVEN, oracle found a violation at step 4"])

    def test_dead_logic(self):
        # INFO "dead logic": the check's condition never holds, as for VACUOUS.
        rows = [info("counter_overflow:q", "dead_state", "q + 1 never wraps past 15 (4 bits)"),
                info("mem_addr:m.wr0", "dead_state")]
        self.assertEqual(self.oracle(rows), ([], []))
        self.assertEqual(self.asserts(), ["always @* if (fvo_gate) assert (!((e)));",
                                          "always @* if (fvo_gate) assert (!(e));"])
        problems, _ = self.oracle(rows[:1], fails={"(e)": 3})
        self.assertEqual(problems, ["counter_overflow:q: fvlint INFO (dead logic in an unreachable state), oracle "
                                    "reached the check's condition"])

    def test_dead_logic_mixed_with_proofs(self):
        rows = [info("counter_overflow:q", "dead_state", "q + 1 never wraps past 15 (4 bits)"),
                row("counter_overflow:q#1", "PROVEN", "q + 1 never wraps past 15 (4 bits)")]
        problems, inconclusive = self.oracle(rows)
        self.assertEqual(problems, [])
        self.assertEqual(inconclusive, ["counter_overflow:q, counter_overflow:q#1: DEAD and PROVEN for constructs "
                                        "the oracle watches together; only the absence of a violation is checked"])
        self.assertEqual(self.asserts(), ["always @* if (fvo_gate) assert (!((e && q > 4'd14)));"])
        rows[1] = row("counter_overflow:q#1", "VACUOUS", "q + 1 never wraps past 15 (4 bits)")
        self.assertEqual(self.oracle(rows), ([], []))
        self.assertEqual(self.asserts(), ["always @* if (fvo_gate) assert (!((e)));"])

    def test_horizon(self):
        # INFO "can't wrap within --horizon N": no wrap in the first N - 1
        # cycles after the reset, checked by BMC to exactly that depth.
        rows = [info("counter_overflow:q", "horizon", "q + 1 never wraps past 15 (4 bits)"),
                row("counter_underflow:q", "PROVEN", "q - 1 never wraps below 0")]
        self.assertEqual(self.oracle(rows, meta={"horizon": 12}), ([], []))
        self.assertEqual(self.asserts(), ["always @* if (fvo_gate) assert (!((fvo_n < 8'd12) && (e && q > 4'd14)));",
                                          "always @* if (fvo_gate) assert (!((!e && q < 4'd1)));"])
        self.assertIn("depth 24\n", self.runs[0][0])
        problems, _ = self.oracle(rows, meta={"horizon": 12}, fails={"q > 4'd14": 5})
        self.assertEqual(problems, ["counter_overflow:q: fvlint INFO (can't wrap within --horizon 12 cycles), "
                                    "oracle found a wrap at step 5"])
        # Two synchronizer stages and a deep horizon: the reset is held 3 cycles; BMC goes deep enough.
        d = design(monitors=self.d.monitors, stages=["s1", "s2"])
        self.oracle(rows[:1], meta={"horizon": 40}, design=d)
        self.assertEqual(self.asserts(), ["always @* if (fvo_gate) assert (!((fvo_n < 8'd42) && (e && q > 4'd14)));"])
        self.assertIn("depth 42\n", self.runs[0][0])
        # A horizon and a proof of the same construct are checked apart.
        rows.append(row("counter_overflow:q#1", "PROVEN", "q + 1 never wraps past 15 (4 bits)"))
        self.assertEqual(self.oracle(rows, meta={"horizon": 12}), ([], []))
        self.assertEqual(len(self.asserts()), 3)
        # Without a horizon in the results (an older run), nothing is claimed.
        self.assertEqual(self.oracle(rows[:1]), ([], []))
        self.assertEqual(self.runs, [])

    def test_horizon_in_a_two_clock_job(self):
        mon = {("counter_overflow", "q", 1): {"en": ["(e && p)"], "bad": ["(e && p && q > 4'd14)"]}}
        d = design(monitors=mon, clock={"q": "posedge clk", "p": "posedge clk2"}, reads={"q": {"p"}})
        self.oracle([info("counter_overflow:q", "horizon", "q + 1 never wraps past 15 (4 bits)")], design=d,
                    meta={"horizon": 8})
        self.assertEqual(self.asserts(), ["always @* if (fvo_gate) assert (!((fvo_n < 8'd16) && (e && p && "
                                          "q > 4'd14)));"])                      # 2 + 2 * 7 global steps

    def test_harmless_full_case(self):
        # The oracle can't watch "set to 'x before the case"; the generator's record must agree.
        d = design(monitors=self.d.monitors, x_defaults={"fx"})
        rows = [info("full_case:fx", "full_case_x"), info("full_case:fv", "full_case_x"),
                info("counter_overflow:q", "free_running", "q + 1 never wraps past 15 (4 bits)"),
                info("fsm_summary:st", None)]
        problems, inconclusive = self.oracle(rows, design=d)
        self.assertEqual(problems, ["full_case:fv: fvlint INFO (the full_case pragma changes nothing), but the code "
                                    "sets fv to a value before the case"])
        self.assertEqual((inconclusive, self.runs), ([], []))             # free-running: nothing claimed

    def test_required_checks(self):
        d = design(monitors=self.d.monitors, required={self.OVF})
        problems, _ = self.oracle([row("mem_addr:m.wr0", "FAIL", step=1)], design=d, fails={"q > 9": 1})
        self.assertEqual(problems, ["counter_overflow/q/1: live logic (its guard's parameter is 1), but fvlint "
                                    "reported no check for it"])
        for status in ("UNKNOWN", "WAIVED", "PROVEN"):
            with self.subTest(status=status):
                rows = [row("counter_overflow:q", status, "q + 1 never wraps past 15 (4 bits)")]
                self.assertEqual(self.oracle(rows, design=d)[0], [])

    def test_timeout_option(self):
        self.oracle([row("mem_addr:m.wr0", "FAIL", step=1)], fails={"q > 9": 1}, opts={"timeout": 7})
        self.assertIn("timeout 7\n", self.runs[0][0])
        self.assertEqual(self.runs[0][1], 7)

    def test_missing_log(self):
        class Silent:
            solver = None

            def run_sby(self, sby, cwd, timeout):
                return -1
        with mock.patch.object(Toolchain, "discover", staticmethod(lambda solver=None: Silent())):
            problems, inconclusive = fuzz.oracle(self.outdir([row("mem_addr:m.wr0", "PROVEN")]), self.d, 24, {})
        self.assertEqual((problems, inconclusive), ([], ["mem_addr:m.wr0: PROVEN not confirmed, oracle job ERROR"]))


class Driver(TempDirCase):
    def test_run(self):
        argvs = []

        def fake_main(argv):
            argvs.append(argv)
            out = argv[argv.index("-o") + 1]
            if out.endswith("seed2"):
                with open(os.path.join(out, "results.json"), "w") as f:
                    json.dump({"results": []}, f)                       # stale or partial results
                return 2
            if out.endswith("seed4"):
                return 1                                                # crashed before writing results
            with open(os.path.join(out, "results.json"), "w") as f:
                json.dump({"results": [{"status": "PROVEN"}, {"status": "FAIL"}]}, f)
            return 1
        oracle_calls = []

        def fake_oracle(d, design, depth, opts):
            oracle_calls.append((os.path.basename(d), design.top, depth))
            return (["x: disagreement"], ["y: too deep"]) if design.top == "fz3" else ([], [])
        with mock.patch.object(cli, "main", fake_main), mock.patch.object(fuzz, "oracle", fake_oracle), \
                captured() as (_, err):
            s = fuzz.run([1, 2, 3, 4], self.tmp, depth=12, extra_args=["--engine", "pdr"], verbose=True)
            again = fuzz.run([1], self.tmp, depth=12)                    # same output tree again
        self.assertEqual((s["seeds"], s["checks"], s["statuses"]), (4, 4, {"PROVEN": 2, "FAIL": 2}))
        self.assertEqual((again["seeds"], again["problems"]), (1, []))
        d1 = os.path.join(self.tmp, "seed1")
        self.assertEqual(argvs[0], ["--top", "fz1", os.path.join(d1, "fz1.v"), "-o", d1, "-j", "1", "--engine", "pdr"])
        self.assertEqual(argvs[1][-4:], ["--engine", "pdr", "--horizon", "12"])     # the design's own options
        self.assertEqual(fuzz.generate(2).args, ["--horizon", "12"])
        self.assertTrue(0 <= s["seconds"] < 60)
        self.assertEqual(oracle_calls, [("seed1", "fz1", 12), ("seed3", "fz3", 12), ("seed1", "fz1", 12)])
        self.assertEqual(len(s["problems"]), 3)
        self.assertIn("seed 2: fvlint did not complete (rc=2)", s["problems"][0])
        self.assertTrue(s["problems"][1].startswith("seed 3: x: disagreement (design: "))
        self.assertIn("seed 4: fvlint did not complete (rc=1)", s["problems"][2])
        self.assertEqual(s["inconclusive"], ["seed 3: y: too deep"])
        self.assertIn("seed 3: 2 checks, 1 problem(s)", err.getvalue())
        with open(os.path.join(self.tmp, "seed1", "fz1.v")) as f:
            self.assertEqual(f.read(), fuzz.generate(1).text)

    def test_main(self):
        captured_args = []

        def fake_run(seeds, out, depth, extra, verbose):
            captured_args.append((list(seeds), out, depth, extra, verbose))
            return {"seeds": 2, "checks": 5, "statuses": {}, "problems": ["p"] if depth == 9 else [],
                    "inconclusive": [], "seconds": 0.1}
        with mock.patch.object(fuzz, "run", fake_run), captured() as (out, _):
            self.assertEqual(fuzz.main(["--seeds", "2", "--first-seed", "5", "-o", "x", "--engine", "smtbmc"]), 0)
            self.assertEqual(fuzz.main(["--depth", "9"]), 1)
            for engine in ("auto", "pdr"):
                self.assertEqual(fuzz.main(["--engine", engine]), 0)
        self.assertEqual(captured_args[0], ([5, 6], "x", 24, ["--engine", "smtbmc"], False))
        self.assertEqual(captured_args[1], (list(range(1, 21)), "fvlint_fuzz", 9, ["--engine", "auto"], False))
        self.assertEqual([a[3] for a in captured_args[2:]], [["--engine", "auto"], ["--engine", "pdr"]])
        self.assertIn("  p", out.getvalue().splitlines())


if __name__ == "__main__":
    unittest.main()
