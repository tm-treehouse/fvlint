# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""fvlint.resets: primary reset heuristics and derived-reset discovery."""

from __future__ import annotations

import unittest

from fvlint.resets import ResetBit, Resets, _as_reset, discover, find_derived, find_primary

from .support import NB, load_snapshot


def ports(*names, width=1, direction="input"):
    b = NB()
    for n in names:
        b.input(n, width, direction=direction)
    return b.build()


class PrimaryReset(unittest.TestCase):
    def test_name_heuristic(self):
        cases = {"rst": 1, "reset": 1, "areset": 1, "arst": 1, "rst_n": 0, "rstn": 0, "rst_ni": 0, "rst_b": 0,
                 "sys_rst_n": 0, "RST_N": 0, "reset_i": 1, "rst_sync": 1, "core_rst": 1}
        for name, active in cases.items():
            with self.subTest(name=name):
                r = find_primary(ports("clk", name), None)
                self.assertEqual((r.name, r.active, r.depth), (name, active, 0))

    def test_not_resets(self):
        for name in ("first", "burst", "reset_done", "rst_count", "xrst"):
            with self.subTest(name=name):
                self.assertIsNone(find_primary(ports("clk", name), None))
        self.assertIsNone(find_primary(ports("rst", width=2), None))                # vectors are not resets
        self.assertIsNone(find_primary(ports("rst", direction="output"), None))

    def test_shortest_candidate_wins(self):
        nl = ports("clk", "sys_rst_n", "rst")
        r = find_primary(nl, None)
        self.assertEqual((r.name, r.bit), ("rst", nl.ports["rst"]["bits"][0]))

    def test_explicit_spec(self):
        nl = ports("clk", "go", "init_n")
        self.assertEqual(find_primary(nl, "go:0").active, 0)
        self.assertEqual(find_primary(nl, "go:1").active, 1)
        self.assertEqual(find_primary(nl, "go").active, 1)                         # default active high...
        self.assertEqual(find_primary(nl, "init_n").active, 0)                     # ...unless named *n
        for bad in ("nope", "nope:1"):
            with self.subTest(bad=bad), self.assertRaisesRegex(ValueError, "not an input"):
                find_primary(nl, bad)
        with self.assertRaises(ValueError):
            find_primary(ports("o", direction="output"), "o")


class ResetModel(unittest.TestCase):
    def test_accessors(self):
        p, d = ResetBit("rst_n", 3, 0), ResetBit("r2", 9, 0, 2)
        r = Resets(p, [d], 3)
        self.assertEqual(r.all(), [p, d])
        self.assertEqual(r.inactive_conds(), [(3, 1), (9, 1)])
        self.assertEqual(r.names(), {"rst_n": 0, "r2": 0})
        self.assertEqual((Resets().all(), Resets().inactive_conds(), Resets().names()), ([], [], {}))

    def test_discover(self):
        nl = ports("clk", "rst")
        self.assertEqual(discover(nl, None, True, None), Resets(None, [], 0))
        self.assertEqual(discover(ports("clk"), None, False, None), Resets(None, [], 0))
        r = discover(nl, None, False, None)
        self.assertEqual((r.primary.name, r.cycles, r.anytime), ("rst", 1, False))
        r = discover(nl, "rst:0", False, 5, anytime=True)
        self.assertEqual((r.primary.active, r.cycles, r.anytime), (0, 5, True))


class DerivedResets(unittest.TestCase):
    def setUp(self):
        self.b = NB()
        self.clk = self.b.input("clk")[0]
        self.rst = self.b.input("rst")[0]
        self.primary = ResetBit("rst", self.rst, 1)

    def derived(self, primary=None, **kw):
        return {(r.name, r.active, r.depth) for r in find_derived(self.b.build(), primary or self.primary, **kw)}

    def test_synchronizer_chain_of_copies(self):
        b = self.b
        s1 = b.ff([self.rst], self.clk, q=b.net("s1", b.new(1)))
        b.ff(s1, self.clk, q=b.net("s2", b.new(1)))
        self.assertEqual(self.derived(), {("s1", 1, 1), ("s2", 1, 2)})

    def test_async_assert_sync_release(self):
        # s <= 0 while rst (asynchronously), then shifts in 1: active-low derived reset.
        b = self.b
        s1 = b.ff(["1"], self.clk, q=b.net("s1", b.new(1)), arst=self.rst, arst_pol=1, arst_val=0)
        b.ff(s1, self.clk, q=b.net("s2", b.new(1)), arst=self.rst, arst_pol=1, arst_val=0)
        self.assertEqual(self.derived(), {("s1", 0, 1), ("s2", 0, 2)})

    def test_async_reset_through_inverters(self):
        # Yosys turns `negedge rst_n` into ARST = ~rst_n with active-high polarity.
        b = NB()
        clk, rst_n = b.input("clk")[0], b.input("rst_n")[0]
        inv = b.op("$not", A=b.op("$reduce_or", w=1, A=[rst_n]))
        b.ff(["1"], clk, q=b.net("s1", b.new(1)), arst=inv[0], arst_pol=1, arst_val=0)
        got = {(r.name, r.active, r.depth) for r in find_derived(b.build(), ResetBit("rst_n", rst_n, 0))}
        self.assertEqual(got, {("s1", 0, 1)})

    def test_wrong_async_polarity_is_not_a_reset(self):
        b = self.b
        b.ff(["1"], self.clk, q=b.net("s1", b.new(1)), arst=self.rst, arst_pol=0, arst_val=0)
        self.assertEqual(self.derived(), set())

    def test_synchronous_reset_through_the_d_logic(self):
        b = self.b
        q = b.net("rdy_n", b.new(1))
        b.ff(b.mux(["0"], ["1"], self.rst), self.clk, q=q)           # rst ? 1 : 0
        self.assertEqual(self.derived(), {("rdy_n", 1, 1)})

    def test_registers_that_are_not_resets(self):
        b = self.b
        data = b.input("data")[0]
        b.ff(b.mux([data], ["1"], self.rst), self.clk, q=b.net("load", b.new(1)))        # loads data
        b.ff(b.mux(["1"], ["1"], self.rst), self.clk, q=b.net("stuck", b.new(1)))         # never inactive...
        b.ff(b.mux(["0"], [data], self.rst), self.clk, q=b.net("in_rst", b.new(1)))       # data during reset
        b.ff(b.mux(["1"], ["0"], self.rst), self.clk, q=b.net("conflict", b.new(1)),
             arst=self.rst, arst_val=1)                                                    # async 1, sync 0
        seen = b.net("seen", b.new(1))
        b.ff(b.mux(seen, ["1"], data), self.clk, q=seen, arst=self.rst, arst_val=0)       # set by data
        self.assertEqual(self.derived(), set())

    def test_sources_beyond_the_search_limit_are_not_ignored(self):
        # q <= rst ? 0 : (s1 ? 1 : (s2 ? 1 : ... (s30 ? 1 : q))).  Every visible
        # source is constant, but q can also hold its own (reset) value, so q
        # is not a reset that is guaranteed to release.
        b = self.b
        q = b.net("q", b.new(1))
        cur = q
        for i in range(30):
            cur = b.mux(cur, ["1"], b.input(f"s{i}")[0])
        b.ff(b.mux(cur, ["0"], self.rst), self.clk, q=q)
        self.assertEqual(self.derived(), set())

    def _with_control(self, ctype, ports, params, d=None):
        """A 1-bit register of type ctype whose D copies synchronizer stage r1."""
        b = self.b
        r1 = b.ff([self.rst], self.clk, q=b.net("r1", b.new(1)))
        conns = dict({"CLK": [self.clk], "D": d if d is not None else r1, "Q": b.net("q", b.new(1))}, **ports)
        b.cell("ctl", ctype, conns, dict({"WIDTH": 1, "CLK_POLARITY": 1}, **params))
        return self.derived()

    def test_controls_that_data_can_assert_disqualify(self):
        # A data input that can force the register would let the design go
        # back "into reset" at any time, switching checks off (a false PROVEN).
        cases = {   # "data" stands for a primary input that is not a reset
            "async reset": ("$adff", {"ARST": "data"}, {"ARST_POLARITY": 1, "ARST_VALUE": 1}),
            "async load": ("$aldff", {"ALOAD": "data", "AD": ["1"]}, {"ALOAD_POLARITY": 1}),
            "async set": ("$dffsr", {"SET": "data", "CLR": ["0"]}, {"SET_POLARITY": 1, "CLR_POLARITY": 1}),
            "async clear": ("$dffsr", {"SET": ["0"], "CLR": "data"}, {"SET_POLARITY": 1, "CLR_POLARITY": 1}),
            "sync reset": ("$sdff", {"SRST": "data"}, {"SRST_POLARITY": 1, "SRST_VALUE": 1}),
            "clock enable": ("$dffe", {"EN": "data"}, {"EN_POLARITY": 1}),
            "never enabled": ("$dffe", {"EN": ["0"]}, {"EN_POLARITY": 1}),
            "unknown constant": ("$adff", {"ARST": ["x"]}, {"ARST_POLARITY": 1, "ARST_VALUE": 1}),
            "always asserted": ("$adff", {"ARST": ["1"]}, {"ARST_POLARITY": 1, "ARST_VALUE": 1}),
        }
        cases.update({   # driven by the reset, but asserted at its inactive level
            "async load, wrong level": ("$aldff", {"ALOAD": "rst", "AD": ["1"]}, {"ALOAD_POLARITY": 0}),
            "async set, wrong level": ("$dffsr", {"SET": "rst", "CLR": ["0"]}, {"SET_POLARITY": 0, "CLR_POLARITY": 1}),
        })
        for name, (ctype, ports, params) in cases.items():
            with self.subTest(name):
                self.setUp()
                data = self.b.input("data")[0]
                ports = {k: [data] if v == "data" else [self.rst] if v == "rst" else v for k, v in ports.items()}
                self.assertEqual(self._with_control(ctype, ports, params), {("r1", 1, 1)})

    def test_controls_driven_by_the_reset_qualify(self):
        cases = {   # name: (type, ports, params, D, expected active value)
            "async clear": ("$dffsr", {"SET": ["0"], "CLR": "rst"}, {"SET_POLARITY": 1, "CLR_POLARITY": 1},
                            ["1"], 0),
            "async set": ("$dffsr", {"SET": "rst", "CLR": ["0"]}, {"SET_POLARITY": 1, "CLR_POLARITY": 1},
                          ["0"], 1),
            "async load": ("$aldff", {"ALOAD": "rst", "AD": ["1"]}, {"ALOAD_POLARITY": 1}, ["0"], 1),
            "async load of 0": ("$aldff", {"ALOAD": "rst", "AD": ["0"]}, {"ALOAD_POLARITY": 1}, ["1"], 0),
            "sync reset": ("$sdff", {"SRST": "rst"}, {"SRST_POLARITY": 1, "SRST_VALUE": 1}, ["0"], 1),
            "enable tied on": ("$dffe", {"EN": ["1"]}, {"EN_POLARITY": 1}, None, 1),
            "enable tied on, low": ("$dffe", {"EN": ["0"]}, {"EN_POLARITY": 0}, None, 1),
        }
        for name, (ctype, ports, params, d, active) in cases.items():
            with self.subTest(name):
                self.setUp()
                ports = {k: [self.rst] if v == "rst" else v for k, v in ports.items()}
                got = self._with_control(ctype, ports, params, d)
                depth = 2 if d is None else 1                           # a copy of r1 is one stage later
                self.assertIn(("q", active, depth), got)

    def test_conflicting_forced_values(self):
        b = self.b
        # Set and clear by the same reset: forced to 1 and to 0 (D = 1 would
        # otherwise fit the second).
        b.cell("x", "$dffsr", {"CLK": [self.clk], "SET": [self.rst], "CLR": [self.rst], "D": ["1"],
                               "Q": b.net("q", b.new(1))},
               {"WIDTH": 1, "CLK_POLARITY": 1, "SET_POLARITY": 1, "CLR_POLARITY": 1})
        self.assertEqual(self.derived(), set())

    def test_latches_are_not_resets(self):
        b = self.b
        b.cell("l", "$dlatch", {"EN": [self.clk], "D": [self.rst], "Q": b.net("q", b.new(1))},
               {"WIDTH": 1, "EN_POLARITY": 1})
        self.assertEqual(self.derived(), set())

    def test_per_bit_reset_values(self):
        # if (rst) s <= 2'b11; else s <= {s[0], 1'b0};  an active-high two-stage
        # synchronizer in one register (both bits reset to 1).
        b = self.b
        s = b.net("s", b.new(2))
        b.ff(["0", s[0]], self.clk, q=s, arst=self.rst, arst_val=0b11)
        self.assertEqual(self.derived(), {("s[0]", 1, 1), ("s[1]", 1, 2)})
        # ...and one whose bits reset to different values: bit 0 to 0 (D=1), bit 1 to 1 (D=0).
        self.setUp()
        b = self.b
        t = b.net("t", b.new(2))
        b.ff(["1", "0"], self.clk, q=t, arst=self.rst, arst_val=0b10)
        self.assertEqual(self.derived(), {("t[0]", 0, 1), ("t[1]", 1, 1)})

    def test_mixed_copies_of_opposite_resets(self):
        b = self.b
        hi = b.ff([self.rst], self.clk, q=b.net("hi", b.new(1)))                          # active 1
        lo = b.ff(["1"], self.clk, q=b.net("lo", b.new(1)), arst=self.rst, arst_val=0)    # active 0
        sel = b.input("sel")[0]
        b.ff(b.mux(hi, lo, sel), self.clk, q=b.net("mix", b.new(1)))
        self.assertEqual(self.derived(), {("hi", 1, 1), ("lo", 0, 1)})

    def test_bits_of_a_vector_register(self):
        b = self.b
        q = b.net("pipe", b.new(2))
        # pipe <= {1'b1, pipe[1]}: bit 1 is the first stage, bit 0 copies it.
        # Bit 0 is visited first, so this also needs a second pass.
        b.ff([q[1], "1"], self.clk, q=q, arst=self.rst, arst_val=0b00)
        self.assertEqual(self.derived(), {("pipe[1]", 0, 1), ("pipe[0]", 0, 2)})

    def test_depth_limit_is_independent_of_cell_order(self):
        for order in ("forward", "reverse"):
            with self.subTest(order=order):
                self.setUp()
                b = self.b
                qs = [b.net(f"s{i}", b.new(1)) for i in range(5)]
                ds = [[self.rst]] + qs[:-1]
                idx = range(5) if order == "forward" else reversed(range(5))
                for i in idx:
                    b.ff(ds[i], self.clk, q=qs[i], name=f"ff{i}")
                self.assertEqual(self.derived(max_depth=2), {("s0", 1, 1), ("s1", 1, 2)})
                self.assertEqual(len(self.derived()), 5)

    def test_buffers_and_inverters_of_a_reset(self):
        for t, inverting in (("$not", True), ("$logic_not", True), ("$pos", False), ("$buf", False),
                             ("$reduce_or", False), ("$reduce_and", False), ("$reduce_bool", False),
                             ("$reduce_xor", False)):
            with self.subTest(type=t):
                b = NB()
                r = b.input("r")[0]
                y = b.op(t, w=1, A=[r])
                self.assertEqual(_as_reset(b.build(), y[0], {r: ResetBit("r", r, 1)})[1], 0 if inverting else 1)

    def test_as_reset(self):
        b = NB()
        r = b.input("r")[0]
        inv = b.op("$not", A=[r])
        buf = b.op("$logic_not", A=inv)
        wide = b.op("$and", A=[r], B=[r])
        nl = b.build()
        known = {r: ResetBit("r", r, 1)}
        self.assertEqual(_as_reset(nl, r, known)[1], 1)
        self.assertEqual(_as_reset(nl, inv[0], known)[1], 0)
        self.assertEqual(_as_reset(nl, buf[0], known)[1], 1)
        self.assertIsNone(_as_reset(nl, wide[0], known))                # not an inverter or buffer
        self.assertIsNone(_as_reset(nl, b.input("other")[0], known))
        self.assertIsNone(_as_reset(nl, buf[0], known, hops=2))         # too far


class RealNetlists(unittest.TestCase):
    def test_two_stage_synchronizer(self):
        nl = load_snapshot("snap_reset")
        r = discover(nl, None, False, None)
        self.assertEqual((r.primary.name, r.primary.active), ("rst_n", 0))
        self.assertEqual(sorted((d.name, d.active, d.depth) for d in r.derived), [("r1", 0, 1), ("r2", 0, 2)])
        self.assertEqual(r.cycles, 3)                                   # held until r2 releases
        self.assertNotIn("seen", r.names())

    def test_plain_synchronous_reset(self):
        r = discover(load_snapshot("snap_counters"), None, False, None)
        self.assertEqual((r.primary.name, r.primary.active, r.derived, r.cycles), ("rst", 1, [], 1))


if __name__ == "__main__":
    unittest.main()
