# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""fvlint.cone: slicing with cut-points, unions, clocks, slice modules."""

from __future__ import annotations

import json
import unittest

from fvlint.cone import UNBOUNDED, ConeSpec, _stable, build_module, clocks, merge_specs, needs_multiclock, slice_spec
from fvlint.netlist import Netlist

from .support import NB, load_snapshot


def chain(n=3):
    """in -> r1 -> r2 -> ... -> rn, root = rn's Q.  Returns (builder, clk, in, [q1..qn])."""
    b = NB()
    clk = b.input("clk")[0]
    x = b.input("x")
    qs, cur = [], x
    for i in range(1, n + 1):
        cur = b.ff(cur, clk, q=b.net(f"q{i}", b.new(1)), name=f"r{i}")
        qs.append(cur)
    return b, clk, x, qs


class Slicing(unittest.TestCase):
    def test_levels(self):
        b, clk, x, (q1, q2, q3) = chain()
        nl = b.build()
        s = slice_spec(nl, q3, [], 0)
        self.assertEqual((s.keep, s.cut), (set(), {"r3"}))              # level 0: even the root register is cut
        s = slice_spec(nl, q3, ["r3"], 0)
        self.assertEqual((s.kept_state, s.cut), ({"r3"}, {"r2"}))
        s = slice_spec(nl, q3, ["r3"], 1)
        self.assertEqual((s.kept_state, s.cut), ({"r3", "r2"}, {"r1"}))
        b4, _, _, (p1, p2, p3, p4) = chain(4)
        s = slice_spec(b4.build(), p4, ["r4"], 2)                        # two stages beyond the anchor
        self.assertEqual((s.kept_state, s.cut), ({"r4", "r3", "r2"}, {"r1"}))
        s = slice_spec(nl, q3, [], UNBOUNDED)
        self.assertEqual((s.kept_state, s.cut, s.inputs), ({"r1", "r2", "r3"}, set(), set(x) | {clk}))
        self.assertTrue(s.full)

    def test_anchors_do_not_consume_levels(self):
        b, clk, x, (q1, q2, q3) = chain()
        s = slice_spec(b.build(), q3, ["r3", "r2"], 0)
        self.assertEqual((s.kept_state, s.cut), ({"r3", "r2"}, {"r1"}))
        s = slice_spec(b.build(), q3, ["r3", "r1"], 0)                  # r1 unreachable without r2
        self.assertEqual((s.kept_state, s.cut), ({"r3"}, {"r2"}))

    def test_combinational_logic_is_always_kept(self):
        b = NB()
        x = b.input("x", 2)
        y = b.op("$and", A=b.op("$not", A=x), B=x)
        s = slice_spec(b.build(), y, [], 0)
        self.assertEqual((len(s.keep), s.cut, s.inputs, s.full), (2, set(), set(x), True))
        self.assertEqual(s.size(), 2)

    def test_opaque_sink_and_undriven(self):
        b = NB()
        x = b.input("x")
        bb_out, floating = b.new(1), b.new(1)
        b.cell("bb", "vendor_pll", {"I": x, "O": bb_out}, dirs={"I": "input", "O": "output"})
        b.cell("chk", "$check", {"A": x, "EN": b.new(1), "Y": b.new(1)})  # a sink driving something
        y = b.op("$xor", A=bb_out, B=floating)
        z = b.op("$or", A=y, B=b.cells["chk"]["connections"]["Y"])
        s = slice_spec(b.build(), z, [], UNBOUNDED)
        self.assertEqual(s.cut, {"bb", "chk"})
        self.assertEqual((s.undriven, s.inputs), (set(floating), set()))
        self.assertFalse(s.full)                                       # cut opaque logic: never "full"

    def test_constant_roots(self):
        s = slice_spec(NB().build(), ["0", "1"], [], 3)
        self.assertEqual((s.keep, s.cut, s.inputs, s.undriven), (set(), set(), set(), set()))

    def test_registers_are_decided_at_their_shallowest_depth(self):
        # root = q1 & n2, n2 = ~~q3 and q1 = r1(q3):  r3 is the first register
        # stage through the inverters but the second through r1.  At level 1
        # r3 must be kept, whichever path the search reaches it by first (a
        # plain breadth-first search meets it through r1 first and cuts it).
        b = NB()
        clk = b.input("clk")[0]
        q3 = b.ff(b.input("x"), clk, name="r3")
        q1 = b.ff(q3, clk, name="r1")
        n2 = b.op("$not", A=b.op("$not", A=q3))
        root = b.op("$and", A=q1, B=n2)
        s = slice_spec(b.build(), root, [], 1)
        self.assertEqual((s.kept_state, s.cut), ({"r1", "r3"}, set()))

    def test_feedback_loops_terminate(self):
        b = NB()
        clk = b.input("clk")[0]
        q = b.new(2)
        b.ff(b.op("$add", A=q, B=["1", "0"]), clk, q=q, name="cnt")
        s = slice_spec(b.build(), q, ["cnt"], 0)
        self.assertEqual(s.kept_state, {"cnt"})
        self.assertEqual(s.cut, set())

    def test_merge(self):
        b, clk, x, (q1, q2, q3) = chain()
        nl = b.build()
        s0 = slice_spec(nl, q3, ["r3"], 0)
        s1 = slice_spec(nl, q3, ["r3"], 1)
        u = merge_specs(nl, [s0, s1])
        self.assertEqual((u.kept_state, u.cut), ({"r3", "r2"}, {"r1"}))  # r2: cut in s0, kept in s1
        m = merge_specs(nl, [ConeSpec(undriven={1}, inputs={5}), ConeSpec(undriven={2}, inputs={6})])
        self.assertEqual((m.undriven, m.inputs), ({1, 2}, {5, 6}))
        empty = merge_specs(nl, [])
        self.assertEqual((empty.keep, empty.kept_state, empty.full), (set(), set(), True))

    def test_finish_removes_kept_cells_from_cut(self):
        b, *_ = chain()
        spec = ConeSpec(keep={"r1"}, cut={"r1", "r2"}).finish(b.build())
        self.assertEqual((spec.cut, spec.kept_state), ({"r2"}, {"r1"}))


class ClockDomains(unittest.TestCase):
    def two(self, pol_b=1, clk_b=None):
        b = NB()
        c1 = b.input("clk")[0]
        c2 = b.input("clk2")[0] if clk_b else c1
        qa, qb = b.new(1), b.new(1)
        b.ff(qb, c1, q=qa, name="a")
        b.ff(qa, c2, q=qb, name="b", clk_pol=pol_b)
        return b.build(), qa, c1, c2

    def test_single_clock(self):
        nl, qa, c1, _ = self.two()
        s = slice_spec(nl, qa, ["a", "b"], 0)
        self.assertEqual(clocks(nl, s), {(c1, 1)})
        self.assertFalse(needs_multiclock(nl, s))

    def test_two_clocks_or_two_edges(self):
        nl, qa, c1, c2 = self.two(clk_b=True)
        self.assertEqual(clocks(nl, slice_spec(nl, qa, ["a", "b"], 0)), {(c1, 1), (c2, 1)})
        self.assertTrue(needs_multiclock(nl, slice_spec(nl, qa, ["a", "b"], 0)))
        self.assertFalse(needs_multiclock(nl, slice_spec(nl, qa, ["a"], 0)))   # other domain cut
        nl, qa, *_ = self.two(pol_b=0)
        self.assertTrue(needs_multiclock(nl, slice_spec(nl, qa, ["a", "b"], 0)))

    def test_latch_forces_multiclock(self):
        b = NB()
        q = b.new(1)
        b.cell("l", "$dlatch", {"EN": b.input("g"), "D": b.input("d"), "Q": q}, {"WIDTH": 1, "EN_POLARITY": 1})
        nl = b.build()
        self.assertTrue(needs_multiclock(nl, slice_spec(nl, q, ["l"], 0)))


class SliceModule(unittest.TestCase):
    def setUp(self):
        b = NB()
        self.clk = b.input("clk")[0]
        self.unused = b.input("unused", 2)
        self.x = b.input("x", 2)
        self.io = b.input("io", 1, direction="inout")
        self.q1 = b.ff(self.x, self.clk, q=b.net("q1", b.new(2)), name="$procdff$7")
        self.q2 = b.ff(self.q1, self.clk, q=b.net("q2", b.new(2), init="00"), name="r2")
        self.q3 = b.ff(b.op("$xor", A=self.q2, B=self.io + self.io), self.clk, q=b.net("q3", b.new(2)), name="r3")
        b.output("o", self.q3)
        self.b = b
        self.nl = b.build()

    def test_cut_registers_become_free_inputs(self):
        spec = slice_spec(self.nl, self.q3, ["r3"], 0)                  # r2 cut
        m = build_module(self.nl, spec)
        cut = [c for c in m["cells"].values() if c["type"] == "$anyseq"]
        self.assertEqual(len(cut), 1)
        self.assertEqual((cut[0]["connections"]["Y"], cut[0]["parameters"]["WIDTH"]), (self.q2, 2))
        self.assertEqual(cut[0]["attributes"], {"fvlint_cut": "r2"})
        self.assertIn("r3", m["cells"])
        self.assertNotIn("r2", m["cells"])

    def test_ports_netnames_and_renaming(self):
        spec = slice_spec(self.nl, self.q3, [], UNBOUNDED)
        m = build_module(self.nl, spec, keep_ports=["unused", "o"])
        self.assertEqual(set(m["ports"]), {"clk", "x", "io", "unused"})      # outputs dropped, even if asked
        self.assertTrue({"clk", "x", "io", "unused"} <= set(m["netnames"]))   # port nets are driven
        self.assertEqual(m["ports"]["io"]["direction"], "input")              # inout becomes input
        self.assertIn("$fvlprocdff$7", m["cells"])                           # generated names re-prefixed
        self.assertNotIn("$procdff$7", m["cells"])
        self.assertIn("o", m["netnames"])                                    # aliases of kept bits stay
        m2 = build_module(self.nl, slice_spec(self.nl, self.q3, ["r3"], 0))
        self.assertNotIn("q1", m2["netnames"])                                # q1 is outside the slice
        self.assertNotIn("x", m2["ports"])

    def test_zero_init(self):
        spec = slice_spec(self.nl, self.q3, [], UNBOUNDED)
        m = build_module(self.nl, spec)
        inits = {tuple(n["bits"]): n["attributes"]["init"] for n in m["netnames"].values()
                 if n.get("hide_name") and "init" in n.get("attributes", {})}
        self.assertEqual(inits, {tuple(self.q1): "00", tuple(self.q3): "00"})   # q2 has its own init
        m = build_module(self.nl, spec, uninit="free")
        self.assertFalse(any("$fvlinit" in n for n in m["netnames"]))

    def test_memory_init(self):
        b = NB()
        rd = b.new(1)
        b.cell("m", "$mem_v2", {"RD_ADDR": b.input("a"), "RD_DATA": rd, "RD_CLK": ["x"], "RD_EN": ["1"]},
               {"WIDTH": 1, "SIZE": 2, "ABITS": 1, "RD_PORTS": 1, "WR_PORTS": 0, "INIT": "xx",
                "RD_CLK_ENABLE": "0"})
        b.cell("m2", "$mem_v2", {"RD_ADDR": b.input("a2"), "RD_DATA": b.new(1), "RD_CLK": ["x"], "RD_EN": ["1"]},
               {"WIDTH": 1, "SIZE": 2, "ABITS": 1, "RD_PORTS": 1, "WR_PORTS": 0, "INIT": "1x",
                "RD_CLK_ENABLE": "0"})
        nl = b.build()
        spec = merge_specs(nl, [slice_spec(nl, rd, ["m"], 0),
                                slice_spec(nl, nl.cells["m2"]["connections"]["RD_DATA"], ["m2"], 0)])
        m = build_module(nl, spec)
        self.assertEqual(m["cells"]["m"]["parameters"]["INIT"], "00")
        self.assertEqual(m["cells"]["m2"]["parameters"]["INIT"], "1x")         # explicit init kept
        self.assertEqual(nl.cells["m"]["parameters"]["INIT"], "xx")            # original untouched

    def test_undriven_bits_get_a_free_driver(self):
        b = NB()
        floating = b.new(1)
        y = b.op("$not", A=floating)
        nl = b.build()
        m = build_module(nl, slice_spec(nl, y, [], 0))
        free = [c for n, c in m["cells"].items() if n.startswith("$fvlundriven$")]
        self.assertEqual(free, [{"hide_name": 1, "type": "$anyseq", "parameters": {"WIDTH": 1},
                                 "attributes": {}, "port_directions": {"Y": "output"},
                                 "connections": {"Y": floating}}])

    def test_module_is_a_valid_standalone_netlist(self):
        spec = slice_spec(self.nl, self.q3, ["r3"], 0)
        m = build_module(self.nl, spec)
        nl2 = Netlist({"modules": {"t": json.loads(json.dumps(m))}}, "t")
        for b in self.q2:                                               # cut bits have exactly one driver
            self.assertEqual(nl2.ctype(nl2.driver[b].cell), "$anyseq")
        # every bit a kept cell reads is driven or a port input
        for cname, c in nl2.cells.items():
            for _, bits in nl2.inputs(cname):
                for b in bits:
                    if not isinstance(b, str):
                        self.assertTrue(b in nl2.driver or b in nl2.port_in, (cname, b))

    def test_original_netlist_is_not_modified(self):
        before = json.dumps(self.nl.data, sort_keys=True)
        build_module(self.nl, slice_spec(self.nl, self.q3, ["r3"], 0))["cells"]["r3"]["parameters"]["X"] = 1
        self.assertEqual(json.dumps(self.nl.data, sort_keys=True), before)

    def test_generated_names_are_sanitized(self):
        # Escaped user names may contain brackets, dots and spaces; the cells
        # and nets fvlint adds for them get plain identifiers.
        b = NB()
        clk = b.input("clk")[0]
        q1 = b.ff(b.input("x"), clk, q=b.net("q1", b.new(1)), name="\\g[0].r x")
        q2 = b.ff(q1, clk, q=b.net("q2", b.new(1)), name="\\u/r+2")
        nl = b.build()
        m = build_module(nl, slice_spec(nl, q2, ["\\u/r+2"], 0))
        self.assertIn("$fvlcut$0$g_0_.r_x$Q", m["cells"])
        self.assertIn("$fvlinit$0$u_r_2", m["netnames"])

    def test_module_attributes_are_kept(self):
        self.nl.mod["attributes"] = {"top": "1", "src": "t.v:1.1-9.9"}
        m = build_module(self.nl, slice_spec(self.nl, self.q3, ["r3"], 0))
        self.assertEqual(m["attributes"], {"top": "1", "src": "t.v:1.1-9.9"})
        self.assertIsNot(m["attributes"], self.nl.mod["attributes"])

    def test_stable_names(self):
        self.assertEqual(_stable("$procmux$12"), "$fvlprocmux$12")
        self.assertEqual(_stable("\\u.q"), "\\u.q")
        self.assertEqual(_stable("plain"), "plain")


class RealNetlists(unittest.TestCase):
    def test_counter_slices(self):
        nl = load_snapshot("snap_counters")
        from fvlint.detect import detect_all
        checks, _ = detect_all(nl, 3)
        c = next(c for c in checks if c.id == "counter_overflow:rel_q")
        s0 = slice_spec(nl, c.roots(), c.anchors, 0)
        lim_ff = nl.whole_driver(nl.netnames["lim"]["bits"])[0]
        self.assertIn(lim_ff, s0.cut)                                   # the limit register is one stage away
        s1 = slice_spec(nl, c.roots(), c.anchors, 1)
        self.assertIn(lim_ff, s1.kept_state)
        self.assertTrue(s1.full)
        m = build_module(nl, s0)
        self.assertTrue(any(cell["type"] == "$anyseq" for cell in m["cells"].values()))


if __name__ == "__main__":
    unittest.main()
