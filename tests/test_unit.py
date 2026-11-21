# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Unit tests for fvlint's pure-Python logic (no Yosys/solver needed).

    python -m unittest -v tests.test_unit
"""

from __future__ import annotations

import json
import os
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "src"))

from fvlint.checks import Check                                      # noqa: E402
from fvlint.cone import UNBOUNDED, merge_specs, needs_multiclock, slice_spec  # noqa: E402
from fvlint.detect import clean_conds, mux_sources                   # noqa: E402
from fvlint.elaborate import Sources                                 # noqa: E402
from fvlint.fsm import read_fsm_cells                                # noqa: E402
from fvlint.netlist import Netlist, const_value, parse_yosys_version  # noqa: E402
from fvlint.replay import divergent, read_vcd, read_yw, stim_module  # noqa: E402
from fvlint.resets import discover, find_primary                     # noqa: E402
from fvlint.sby import Prop, instance, parse_job, prop_key           # noqa: E402
from fvlint.tools import ToolError, yosys_arg                        # noqa: E402
from fvlint.waivers import Waivers                                   # noqa: E402


def cell(t, conns, dirs, params=None):
    return {"type": t, "parameters": params or {}, "attributes": {}, "port_directions": dirs,
            "connections": conns}


def dff(d, q, clk=2, pol=1):
    return cell("$dff", {"CLK": [clk], "D": d, "Q": q}, {"CLK": "input", "D": "input", "Q": "output"},
                {"CLK_POLARITY": pol, "WIDTH": len(q)})


def netlist(cells, ports=None, nets=None):
    ports = ports or {"clk": {"direction": "input", "bits": [2]}}
    return Netlist({"modules": {"t": {"ports": ports, "cells": cells, "netnames": nets or {}}}}, "t")


class ParsingTests(unittest.TestCase):
    def test_filelist(self):
        with tempfile.TemporaryDirectory() as d:
            fl = os.path.join(d, "t.f")
            with open(fl, "w") as f:
                f.write("// comment\n# full-line comment\n+incdir+inc+inc2\n+define+A=1\n-D B\n"
                        "-I other\nrtl/a.sv  // trailing\nrtl/b#1.sv\n")
            s = Sources()
            s.add_filelist(fl)
        self.assertEqual([os.path.basename(p) for p in s.files], ["a.sv", "b#1.sv"])
        self.assertEqual([os.path.basename(p) for p in s.incdirs], ["inc", "inc2", "other"])
        self.assertEqual(s.defines, ["A=1", "B"])

    def test_yosys_quoting(self):
        self.assertEqual(yosys_arg("rtl/a.sv"), "rtl/a.sv")
        self.assertEqual(yosys_arg("my dir/a.sv"), '"my dir/a.sv"')
        self.assertEqual(yosys_arg("a;b"), '"a;b"')
        self.assertEqual(yosys_arg("x#y"), '"x#y"')
        with self.assertRaises(ToolError):
            yosys_arg('bad"name')

    def test_version(self):
        self.assertEqual(parse_yosys_version("Yosys 0.71 (git sha1 b4c586fd3, Release)"), (0, 71))
        self.assertIsNone(parse_yosys_version("garbage"))

    def test_const_value(self):
        self.assertEqual(const_value(["1", "0", "1"]), 5)
        self.assertIsNone(const_value(["1", "x"]))
        self.assertIsNone(const_value([3, "1"]))

    def test_waivers(self):
        w = Waivers()
        w.rules.append(("fsm_trap:*", "ok"))
        self.assertTrue(w.match(Check(kind="fsm_trap", target="st={2'b10}", src="", desc="")))
        self.assertIsNone(w.match(Check(kind="fsm_unreachable", target="st", src="", desc="")))
        c = Check(kind="counter_overflow", target="x", src="", desc="", waive_attr="mem_addr, counter_overflow")
        self.assertTrue(w.match(c))


class ConditionTests(unittest.TestCase):
    def test_constant_conditions(self):
        self.assertEqual(clean_conds([(5, 1), ("1", 1), (5, 1)]), [(5, 1)])
        self.assertIsNone(clean_conds([("0", 1)]))          # dead: constant mismatch
        self.assertIsNone(clean_conds([(5, 1), (5, 0)]))     # contradiction
        self.assertEqual(clean_conds([("x", 1)]), [])        # unknown constant: no constraint

    def test_mux_paths_drop_dead_branches(self):
        # y = S ? B : A with S tied to 0: only A is reachable.
        nl = netlist({"m": cell("$mux", {"A": [10], "B": [11], "S": ["0"], "Y": [12]},
                                {"A": "input", "B": "input", "S": "input", "Y": "output"})})
        self.assertEqual([b for b, _ in mux_sources(nl, [12])], [[10]])


class ConeTests(unittest.TestCase):
    def test_unknown_cells_are_cut(self):
        nl = netlist({
            "u": cell("$frobnicate", {"A": [10], "Y": [11]}, {"A": "input", "Y": "output"}),
            "a": cell("$not", {"A": [11], "Y": [12]}, {"A": "input", "Y": "output"}),
        })
        self.assertIn("$frobnicate", nl.unknown_types)
        spec = slice_spec(nl, [12], [], UNBOUNDED)
        self.assertIn("a", spec.keep)
        self.assertIn("u", spec.cut)          # never modelled: always free
        self.assertFalse(spec.full)

    def test_levels_and_union(self):
        nl = netlist({"r1": dff([11], [10]), "r2": dff([12], [11]), "r3": dff([13], [12])})
        s0 = slice_spec(nl, [10], ["r1"], 0)
        self.assertEqual(s0.kept_state, {"r1"})
        self.assertEqual(s0.cut, {"r2"})
        s1 = slice_spec(nl, [10], ["r1"], 1)
        self.assertEqual(s1.kept_state, {"r1", "r2"})
        u = merge_specs(nl, [s0, s1])
        self.assertEqual(u.kept_state, {"r1", "r2"})
        self.assertEqual(u.cut, {"r3"})     # cut in s1, kept nowhere

    def test_multiclock_detection(self):
        nl = netlist({"a": dff([11], [10], clk=2), "b": dff([10], [11], clk=3)},
                     ports={"clk": {"direction": "input", "bits": [2]},
                            "clk2": {"direction": "input", "bits": [3]}})
        both = slice_spec(nl, [10], ["a", "b"], 3)
        self.assertTrue(needs_multiclock(nl, both))
        one = slice_spec(nl, [10], ["a"], 0)
        self.assertFalse(needs_multiclock(nl, one))
        nl2 = netlist({"a": dff([11], [10], pol=1), "b": dff([10], [11], pol=0)})
        self.assertTrue(needs_multiclock(nl2, slice_spec(nl2, [10], ["a", "b"], 3)))


class ResetTests(unittest.TestCase):
    def nl(self, *ports):
        return netlist({}, ports={p: {"direction": "input", "bits": [i + 2]} for i, p in enumerate(ports)})

    def test_primary_heuristic(self):
        self.assertEqual(find_primary(self.nl("clk", "rst_n"), None).active, 0)
        self.assertEqual(find_primary(self.nl("clk", "areset"), None).active, 1)
        self.assertEqual(find_primary(self.nl("clk", "sys_rst_ni"), None).active, 0)
        self.assertIsNone(find_primary(self.nl("clk", "first"), None))
        self.assertEqual(find_primary(self.nl("clk", "x"), "x:0").active, 0)

    def test_synchronizer_chain(self):
        # r1 <= rst; r2 <= r1  (active-high, 2 stages) -> hold reset 3 cycles
        nl = netlist({"s1": dff([3], [10]), "s2": dff([10], [11])},
                     ports={"clk": {"direction": "input", "bits": [2]},
                            "rst": {"direction": "input", "bits": [3]}})
        r = discover(nl, None, False, None)
        self.assertEqual(r.primary.name, "rst")
        self.assertEqual(sorted(x.depth for x in r.derived), [1, 2])
        self.assertEqual(r.cycles, 3)
        self.assertEqual(sorted(r.inactive_conds()), [(3, 0), (10, 0), (11, 0)])


class SbyTests(unittest.TestCase):
    def test_instance_encoding(self):
        inst = instance(Prop("fvl_t0", "fvl_range", {"W": 4, "LO": 1, "HI": 9, "SIGNED": 0},
                             {"v": [5, 6, 7, 8]}, [(10, 0), (11, 1), ("1", 1)], mode=2))
        p = inst["parameters"]
        self.assertEqual((p["LO"], p["HI"], p["NC"], p["POL"], p["NE"], p["MODE"]),
                         ("0001", "1001", 2, "10", 1, 2))
        self.assertEqual(inst["connections"]["c"], [10, 11])
        signed = instance(Prop("fvl_t1", "fvl_range", {"W": 8, "LO": -128, "HI": 117, "SIGNED": 1},
                               {"v": list(range(8))}, []))
        self.assertEqual(signed["parameters"]["LO"], "10000000")

    def test_prop_names(self):
        self.assertEqual(prop_key("_witness_.check_flatten_fvl_t12__fvl_checkers_v_25_assert_52"), "fvl_t12")
        self.assertEqual(prop_key("x.fvl_l3_g_assert.y"), "fvl_l3")
        self.assertIsNone(prop_key("user_assert"))

    def test_pdr_summary_parsing(self):
        with tempfile.TemporaryDirectory() as d:
            run = os.path.join(d, "job", "run")
            os.makedirs(os.path.join(run, "model"))
            with open(os.path.join(run, "model", "design_aiger.ywa"), "w") as f:
                json.dump({"asserts": [["\\_witness_", "\\check_flatten_fvl_t0__a"],
                                       ["\\_witness_", "\\check_flatten_fvl_t1__a"]]}, f)
            with open(os.path.join(run, "logfile.txt"), "w") as f:
                f.write("SBY [run] engine_0: Output 1 was asserted in frame 18 (18) (solved 1 out of 2).\n"
                        "SBY [run] engine_0: Proved output 0 in frame 4.\n"
                        "SBY [run] summary: counterexample trace: run/engine_0/trace_1.vcd\n"
                        "SBY [run] summary:   failed assertion t._witness_.check_flatten_fvl_t1__a at "
                        "fvl_checkers.v:44 step 46\nSBY [run] DONE (FAIL, rc=2)\n")
            r = parse_job(os.path.join(d, "job"), d, 2, "abc --keep-going pdr", "prove", ["fvl_t0", "fvl_t1"])
        self.assertEqual(r.get("fvl_t0").status, "pass")
        self.assertEqual((r.get("fvl_t1").status, r.get("fvl_t1").step), ("fail", 46))   # not frame 18
        self.assertTrue(r.get("fvl_t1").trace.endswith("trace_1.vcd"))


class ReplayTests(unittest.TestCase):
    def test_witness_and_vcd(self):
        with tempfile.TemporaryDirectory() as d:
            yw = os.path.join(d, "t.yw")
            with open(yw, "w") as f:
                json.dump({"signals": [{"path": ["\\clk"], "width": 1, "offset": 0, "init_only": False},
                                       {"path": ["\\req"], "width": 2, "offset": 0, "init_only": False}],
                           "steps": [{"bits": "101"}, {"bits": "010"}]}, f)
            sig = read_yw(yw)
            self.assertEqual(sig["clk"], ["1", "0"])
            self.assertEqual(sig["req"], ["10", "01"])
            vcd = os.path.join(d, "t.vcd")
            with open(vcd, "w") as f:
                f.write("$var integer 32 t smt_step $end\n$scope module top $end\n"
                        "$var wire 2 n0 req $end\n$scope module u $end\n$var wire 1 n1 q $end\n"
                        "$upscope $end\n$upscope $end\n$enddefinitions $end\n"
                        "#0\nb0 t\nb10 n0\n0n1\n#5\n#10\nb1 t\nb01 n0\n1n1\n#15\n")
            v = read_vcd(vcd)
        self.assertEqual(v["req"], ["10", "01"])
        self.assertEqual(v["u.q"], ["0", "1"])

    def test_divergence(self):
        slice_v = {"a": ["0", "1", "1"], "b": ["1", "1", "1"]}
        real_v = {"a": ["0", "0", "1"], "b": ["1", "1", "1"]}
        cut = {"A": [("a", 1)], "B": [("b", 1)], "C": [("missing", 1)]}
        self.assertEqual(divergent(slice_v, real_v, cut, 2), {"A", "C"})

    def test_stimulus(self):
        text = stim_module([("req", 2)], {"req": ["10", "x1"]}, 1)
        self.assertIn("16'd0: begin assume ((p0 & 2'b11) == 2'b10);", text)
        self.assertIn("(p0 & 2'b01) == 2'b01", text)       # x bits left free
        self.assertIn("cover (n == 16'd1)", text)


class FsmTests(unittest.TestCase):
    def test_reset_edges_dropped(self):
        # 2 states; ctrl_in = [rst]; transitions: S0 -rst=0-> S1, S1 -rst=1-> S0, S1 -rst=0-> S1
        def entry(si, ci, so):
            # LSB-first: ctrl_out(0 bits), state_out(1), ctrl_in(1), state_in(1)
            return f"{so}{ci}{si}"
        tt = "".join(entry(*t) for t in [("0", "0", "1"), ("1", "1", "0"), ("1", "0", "1")])
        mod = {"cells": {"$fsm": {"type": "$fsm", "parameters": {
            "STATE_BITS": 1, "STATE_NUM": 2, "STATE_NUM_LOG2": 1, "CTRL_IN_WIDTH": 1,
            "CTRL_OUT_WIDTH": 0, "TRANS_NUM": 3, "STATE_TABLE": "10", "STATE_RST": 0,
            "TRANS_TABLE": tt[::-1], "NAME": "\\st"}, "connections": {"CTRL_IN": [3]}}},
            "netnames": {"rst": {"bits": [3]}}, "ports": {}}
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, "fsm.json")
            with open(p, "w") as f:
                json.dump({"modules": {"t": mod}}, f)
            keep = read_fsm_cells(p, "t")[0]
            drop = read_fsm_cells(p, "t", {"rst": 1})[0]
        self.assertEqual(len(keep["trans"]), 3)
        self.assertEqual(len(drop["trans"]), 2)       # the reset edge S1 -> S0 is gone
        self.assertEqual(drop["reset_edges"], 1)


if __name__ == "__main__":
    unittest.main()
