# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""fvlint regression tests.

End-to-end tests run the real toolchain (Yosys + SymbiYosys + an SMT solver)
on the fixtures in tests/fixtures, each of which has known-clean structures
and planted bugs.  Run with:  python -m unittest -v tests.test_fvlint
"""

from __future__ import annotations

import contextlib
import io
import json
import os
import shutil
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, "src"))

from fvlint import cli                                   # noqa: E402
from fvlint.elaborate import Sources                     # noqa: E402
from fvlint.netlist import Netlist, const_value          # noqa: E402
from fvlint.prove import _instance                       # noqa: E402
from fvlint.waivers import Waivers                       # noqa: E402
from fvlint.checks import Check                          # noqa: E402

FIX = os.path.join(HERE, "fixtures")
OUT = os.path.join(HERE, "_out")
JOBS = os.environ.get("FVLINT_TEST_JOBS", str(os.cpu_count() or 2))

# (fixture file, top) -> {check id: expected status}
EXPECT = {
    ("counters.sv", "cnt_mod100"): {"counter_overflow:q": "PROVEN"},
    ("counters.sv", "cnt_badlimit"): {"counter_overflow:q": "FAIL"},
    ("counters.sv", "credit_ok"): {"counter_overflow:used": "PROVEN",
                                   "counter_underflow:used": "PROVEN"},
    ("counters.sv", "credit_bug"): {"counter_overflow:used": "FAIL",
                                    "counter_underflow:used": "PROVEN"},
    ("counters.sv", "timebase"): {"counter_overflow:div": "INFO"},
    ("counters.sv", "cnt_wide"): {"counter_overflow:cnt": "PROVEN"},
    ("memory.sv", "ring_ok"): {"mem_addr:mem.rd0": "PROVEN", "mem_addr:mem.wr0": "PROVEN",
                               "counter_overflow:wp": "PROVEN", "counter_overflow:rp": "PROVEN"},
    ("memory.sv", "ring_bug"): {"mem_addr:mem.wr0": "FAIL", "mem_addr:mem.rd0": "FAIL",
                                "counter_overflow:wp": "PROVEN"},
    ("cases.sv", "arb_unique"): {"parallel_case:cases.sv:14": "FAIL"},
    ("cases.sv", "dec_onehot"): {"parallel_case:cases.sv:31": "PROVEN"},
    ("cases.sv", "arb_guarded"): {"parallel_case:cases.sv:46": "PROVEN"},
    ("index.sv", "lane_sel_ok"): {"index_range:index.sv:8": "PROVEN"},
    ("index.sv", "lane_sel_bug"): {"index_range:index.sv:17": "FAIL",
                                   "counter_overflow:sel": "INFO"},
    ("index.sv", "lane_sel_fixed"): {"index_range:index.sv:26": "PROVEN",
                                     "counter_overflow:sel": "PROVEN"},
    ("fsm.sv", "fsm_issues"): {"fsm_unreachable:st=2'b11": "FAIL", "fsm_trap:st={2'b10}": "WARN"},
    ("fsm.sv", "fsm_clean"): {"fsm_summary:st": "INFO"},
}


def run_fvlint(name: str, *args) -> tuple[int, dict]:
    out = os.path.join(OUT, name)
    if os.path.isdir(out):
        shutil.rmtree(out)
    buf_out, buf_err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(buf_out), contextlib.redirect_stderr(buf_err):
        rc = cli.main(["-o", out, "-j", JOBS, *args])
    path = os.path.join(out, "results.json")
    if not os.path.exists(path):
        raise AssertionError(f"fvlint produced no results (rc={rc}):\n{buf_err.getvalue()}")
    with open(path) as f:
        data = json.load(f)
    return rc, {r["id"]: r for r in data["results"]}


class FixtureTests(unittest.TestCase):
    """One test per fixture top: every expected check has the expected status
    and nothing else fails."""


def _make(fname, top, expected):
    def test(self):
        rc, res = run_fvlint(top, "--top", top, os.path.join(FIX, fname))
        got = {cid: res[cid]["status"] if cid in res else "missing" for cid in expected}
        self.assertEqual(got, expected, msg=json.dumps(res, indent=1)[:3000])
        unexpected = [cid for cid, r in res.items()
                      if r["status"] in ("FAIL", "ERROR") and cid not in expected]
        self.assertEqual(unexpected, [])
        should_fail = any(v == "FAIL" for v in expected.values())
        self.assertEqual(rc, 1 if should_fail else 0)
    test.__name__ = f"test_{top}"
    return test


for (_f, _t), _e in EXPECT.items():
    setattr(FixtureTests, f"test_{_t}", _make(_f, _t, _e))


class BehaviourTests(unittest.TestCase):
    def test_cone_growth(self):
        """credit_ok needs the registered 'not full' flag: level 0 must not
        prove it, a larger cone must."""
        _, res = run_fvlint("growth", "--top", "credit_ok", os.path.join(FIX, "counters.sv"))
        r = res["counter_overflow:used"]
        self.assertEqual(r["status"], "PROVEN")
        self.assertNotEqual(r["history"][0][1], "PROVEN")
        self.assertEqual(r["history"][0][0], "0")

    def test_counterexample_trace_written(self):
        _, res = run_fvlint("trace", "--top", "credit_bug", os.path.join(FIX, "counters.sv"))
        r = res["counter_overflow:used"]
        self.assertEqual(r["status"], "FAIL")
        self.assertTrue(r["trace"] and os.path.exists(os.path.join(OUT, "trace", r["trace"])))
        self.assertTrue(r["full_design"])

    def test_assumption_file(self):
        rc, res = run_fvlint("assume", "--top", "ring_bug", os.path.join(FIX, "memory.sv"),
                             "--assume", os.path.join(FIX, "ring_bug_assume.sv"))
        self.assertEqual(res["mem_addr:mem.rd0"]["status"], "PROVEN")
        self.assertEqual(res["mem_addr:mem.wr0"]["status"], "FAIL")   # the real bug stays
        self.assertEqual(rc, 1)

    def test_waiver_file(self):
        wf = os.path.join(OUT, "waivers.txt")
        os.makedirs(OUT, exist_ok=True)
        with open(wf, "w") as f:
            f.write("# test\ncounter_overflow:used   # accepted for the test\n")
        rc, res = run_fvlint("waive", "--top", "credit_bug", os.path.join(FIX, "counters.sv"),
                             "--waivers", wf)
        self.assertEqual(res["counter_overflow:used"]["status"], "WAIVED")
        self.assertEqual(rc, 0)

    def test_check_selection(self):
        _, res = run_fvlint("select", "--top", "ring_bug", os.path.join(FIX, "memory.sv"),
                            "--checks", "counter_overflow")
        self.assertEqual(set(res), {"counter_overflow:wp"})

    def test_slang_demo(self):
        """Hierarchy, a package and SV syntax via the slang frontend; with the
        demo's assumptions and waivers nothing fails."""
        demo = os.path.join(ROOT, "examples", "demo")
        rc, res = run_fvlint("demo_slang", "--frontend", "slang", "--top", "demo_top",
                             os.path.join(demo, "demo_top.sv"),
                             "--assume", os.path.join(demo, "assumptions.sv"),
                             "--waivers", os.path.join(demo, "waivers.txt"))
        self.assertEqual(rc, 0)
        self.assertEqual(res["counter_overflow:u_framer.seq"]["status"], "WAIVED")  # RTL attribute
        self.assertEqual(res["fsm_unreachable:u_framer.st=3'b100"]["status"], "WAIVED")
        self.assertEqual(res["mem_addr:u_fifo.mem.wr0"]["status"], "PROVEN")
        self.assertEqual(res["index_range:demo_top.sv:88"]["status"], "PROVEN")


class UnitTests(unittest.TestCase):
    def test_filelist(self):
        os.makedirs(OUT, exist_ok=True)
        fl = os.path.join(OUT, "t.f")
        with open(fl, "w") as f:
            f.write("// comment\n+incdir+inc+inc2\n+define+A=1\n-D B\n-I other\nrtl/a.sv  # trailing\n")
        s = Sources()
        s.add_filelist(fl)
        self.assertEqual([os.path.basename(p) for p in s.files], ["a.sv"])
        self.assertEqual([os.path.basename(p) for p in s.incdirs], ["inc", "inc2", "other"])
        self.assertEqual(s.defines, ["A=1", "B"])

    def test_waiver_matching(self):
        w = Waivers()
        w.rules.append(("fsm_trap:*", "ok"))
        self.assertTrue(w.match(Check(kind="fsm_trap", target="st={2'b10}", src="", desc="")))
        self.assertIsNone(w.match(Check(kind="fsm_unreachable", target="st", src="", desc="")))
        c = Check(kind="counter_overflow", target="x", src="", desc="", waive_attr="mem_addr, counter_overflow")
        self.assertTrue(w.match(c))

    def test_checker_instance_encoding(self):
        inst = _instance("fvl_range", {"W": 4, "LO": 1, "HI": 9}, {"v": [5, 6, 7, 8]},
                         [(10, 0), (11, 1), ("1", 1)])
        p = inst["parameters"]
        self.assertEqual((p["LO"], p["HI"], p["NC"], p["POL"], p["NE"]), ("0001", "1001", 2, "10", 1))
        self.assertEqual(inst["connections"]["c"], [10, 11])
        self.assertEqual(inst["connections"]["e"], ["1"])

    def test_const_value(self):
        self.assertEqual(const_value(["1", "0", "1"]), 5)
        self.assertIsNone(const_value(["1", "x"]))
        self.assertIsNone(const_value([3, "1"]))

    def test_reset_heuristic(self):
        def nl(*ports):
            return Netlist({"modules": {"t": {"ports": {p: {"direction": "input", "bits": [i + 2]}
                                                         for i, p in enumerate(ports)},
                                              "cells": {}, "netnames": {}}}}, "t")
        self.assertEqual((cli.find_reset(nl("clk", "rst_n"), None).active), 0)
        self.assertEqual((cli.find_reset(nl("clk", "areset"), None).active), 1)
        self.assertEqual((cli.find_reset(nl("clk", "sys_rst_ni"), None).active), 0)
        self.assertIsNone(cli.find_reset(nl("clk", "first"), None))
        self.assertEqual(cli.find_reset(nl("clk", "x"), "x:0").active, 0)


if __name__ == "__main__":
    unittest.main()
