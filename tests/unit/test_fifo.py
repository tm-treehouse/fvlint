# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""fvlint.fifo: recognising FIFOs by their pointers, and settling the
pointers' counter checks."""

from __future__ import annotations

import unittest

from fvlint.checks import FIFO_POINTER, INFO, Check
from fvlint.fifo import FIFO, detect_fifos, settle_pointers
from fvlint.sby import Prop, instance

from .support import NB, const


class Fifo:
    """A FIFO netlist: a memory of `size` entries written at wp and read at rp."""

    def __init__(self, size=4, abits=2, pw=2, rp_pw=None, reset="sync", wrap=False, flush=False, step=1,
                 rd_clk=None, rd_reset=True, wr_ports=1, offset=0, wr_clk_enable=1, clk_pol=1,
                 addr_from_input=False, same_pointer=False, two_resets=False, rd_ports=1, wr_clk_pol=1,
                 arst_pol=1, waive=None):
        b = self.b = NB()
        self.clk = b.input("clk")[0]
        self.clk2 = b.input("clk2")[0]
        self.rst = b.input("rst")[0]
        self.we, self.re = b.input("we")[0], b.input("re")[0]
        din = b.input("din", 8)
        self.arst_pol = arst_pol
        self.wp = self.pointer("wp", pw, self.we, reset, wrap, flush, step, size, self.clk, clk_pol, two_resets)
        if same_pointer:
            self.rp = self.wp
        else:
            self.rp = self.pointer("rp", rp_pw or pw, self.re, reset if rd_reset else None, wrap, False, 1, size,
                                   self.clk2 if rd_clk == "clk2" else self.clk, 1, two_resets)
        waddr = b.input("wa", abits) if addr_from_input else self.wp[0][:abits]
        waddr = b.mux(["x"] * abits, waddr, self.we)               # Yosys: the address only where it writes
        n, r = wr_ports, rd_ports
        raddr = (b.input("ra", abits) if r == 2 else []) + self.rp[0][:abits]   # a second port: rp's is the last
        attrs = {"src": "f.v:8.3-8.9"} if waive is None else {"src": "f.v:8.3-8.9", "fvlint_waive": waive}
        self.mem = b.cell("$mem_v2$m", "$mem_v2", {
            "WR_ADDR": waddr * n, "WR_EN": [self.we] * 8 * n, "WR_DATA": din * n, "WR_CLK": [self.clk] * n,
            "RD_ADDR": raddr, "RD_DATA": b.new(8 * r), "RD_EN": ["1"] * r, "RD_CLK": ["x"] * r,
            "RD_ARST": ["0"] * r, "RD_SRST": ["0"] * r},
            {"SIZE": size, "ABITS": abits, "WIDTH": 8, "OFFSET": offset, "MEMID": "\\mem", "WR_PORTS": n,
             "RD_PORTS": r, "WR_CLK_ENABLE": wr_clk_enable, "WR_CLK_POLARITY": wr_clk_pol, "RD_CLK_ENABLE": 0},
            attrs=attrs,
            dirs={"WR_ADDR": "input", "WR_EN": "input", "WR_DATA": "input", "WR_CLK": "input", "RD_ADDR": "input",
                  "RD_DATA": "output", "RD_EN": "input", "RD_CLK": "input", "RD_ARST": "input", "RD_SRST": "input"})
        self.nl = b.build()

    def pointer(self, name, w, move, reset, wrap, flush, step, size, clk, clk_pol, two_resets):
        b = self.b
        q = b.net(name, b.new(w))
        inc = b.op("$add", w=32, A=q + ["0"] * (32 - w), B=const(step, 32))[:w]
        if wrap:
            last = b.op("$eq", w=1, A=q, B=const(size - 1, w))[0]
            inc = b.mux(inc, const(0, w), last)
        d = b.mux(q, inc, move)
        if flush:
            d = b.mux(d, const(0, w), b.input(f"{name}_flush")[0])
        if reset in ("sync", "nested"):
            if reset == "nested":                             # if (rst) if (x) p <= 0;
                x = self.b.netnames["x"]["bits"][0] if "x" in self.b.netnames else b.input("x")[0]
                d = b.mux(d, b.mux(d, const(0, w), x), self.rst)
            else:
                d = b.mux(d, const(0, w), self.rst)
            if two_resets:
                r2 = self.b.netnames["rst2"]["bits"][0] if "rst2" in self.b.netnames else b.input("rst2")[0]
                d = b.mux(d, const(1, w), r2)
            cell = f"$dff${name}"
            b.ff(d, clk, q=q, name=cell, clk_pol=clk_pol)
        elif reset == "async":
            cell = f"$adff${name}"
            b.ff(d, clk, q=q, name=cell, arst=self.rst, arst_pol=self.arst_pol, clk_pol=clk_pol)
        elif reset in ("aload", "aload_data"):                # slang's asynchronous reset
            cell = f"$aldff${name}"
            ad = b.input(f"{name}_ad", w) if reset == "aload_data" else const(0, w)
            b.cell(cell, "$aldff", {"CLK": [clk], "ALOAD": [self.rst], "AD": ad, "D": d, "Q": q},
                   {"WIDTH": w, "CLK_POLARITY": clk_pol, "ALOAD_POLARITY": 0})
        else:
            cell = f"$dff${name}"
            b.ff(d, clk, q=q, name=cell, clk_pol=clk_pol)
        return q, d, cell


class Recognition(unittest.TestCase):
    def test_a_fifo(self):
        f = Fifo()
        checks, natural = detect_fifos(f.nl, {f.rst: 0})
        self.assertEqual([(c.id, c.src, c.checker) for c in checks],
                         [("fifo_overflow:mem", "f.v:8", FIFO), ("fifo_underflow:mem", "f.v:8", FIFO)])
        over, under = checks
        self.assertEqual(over.params, {"PW": 2, "RW": 2, "CW": 3, "DEPTH": 4, "NR": 1, "RPOL": 1, "OVER": 1})
        self.assertEqual(under.params["OVER"], 0)
        wq, wd, wcell = f.wp
        rq, rd, rcell = f.rp
        self.assertEqual(over.ports, {"clk": [f.clk], "wd": wd, "wq": wq, "rd": rd, "rq": rq, "r": [f.rst],
                                      "n": ["0"]})
        self.assertIsNone(over.fallback)                       # nothing to strengthen it with
        self.assertEqual((over.anchors, over.conds, over.depth_hint), ([wcell, rcell], [], 12))
        self.assertEqual(over.desc, "no write to the full FIFO mem (4 entries) without a read")
        self.assertEqual(under.desc, "no read from the empty FIFO mem")
        self.assertEqual(natural, {wcell, rcell})
        self.assertIs(over.ports, under.ports)

    def test_resets(self):
        f = Fifo(reset=None)                                  # no reset: never cleared
        (c, _), _ = detect_fifos(f.nl, {})
        self.assertEqual((c.ports["r"], c.params["NR"], c.params["RPOL"]), (["0"], 1, 1))
        f = Fifo(reset="async")                               # an asynchronous reset
        (c, _), _ = detect_fifos(f.nl, {f.rst: 0})
        self.assertEqual((c.ports["r"], c.params["RPOL"]), ([f.rst], 1))
        f = Fifo(reset="async", arst_pol=0)                   # active low
        (c, _), _ = detect_fifos(f.nl, {f.rst: 1})
        self.assertEqual((c.ports["r"], c.params["RPOL"]), ([f.rst], 0))
        f = Fifo(reset="nested")                              # if (rst) if (x): during reset it may also hold
        self.assertEqual(detect_fifos(f.nl, {f.rst: 0}), ([], set()))
        f = Fifo()                                            # rst not known as a reset: a load in mid-run
        self.assertEqual(detect_fifos(f.nl, {}), ([], set()))
        self.assertEqual(detect_fifos(Fifo(rd_reset=False).nl, {})[0], [])       # pointers reset differently
        f = Fifo(rd_reset=False)
        self.assertEqual(detect_fifos(f.nl, {f.rst: 0})[0], [])
        f = Fifo(reset="aload")                               # slang: an asynchronous load of 0, active low
        (c, _), natural = detect_fifos(f.nl, {f.rst: 1})
        self.assertEqual((c.ports["r"], c.params["RPOL"], len(natural)), ([f.rst], 0, 2))
        f = Fifo(reset="aload_data")                          # an asynchronous load of a value: no reset
        self.assertEqual(detect_fifos(f.nl, {f.rst: 1}), ([], set()))
        f = Fifo(two_resets=True)                             # reset in two ways (both pointers alike)
        self.assertEqual(detect_fifos(f.nl, {f.rst: 0, f.nl.ports["rst2"]["bits"][0]: 0})[0], [])

    def test_pointer_shapes(self):
        f = Fifo(size=3, wrap=True)                           # back to 0 from the last entry
        checks, natural = detect_fifos(f.nl, {f.rst: 0})
        self.assertEqual((len(checks), natural, checks[0].params["DEPTH"], checks[0].params["CW"]), (2, set(), 3, 2))
        f = Fifo(size=4, pw=3)                                # an extra wrap bit
        (c, _), natural = detect_fifos(f.nl, {f.rst: 0})
        self.assertEqual((c.params["PW"], c.params["RW"], len(natural)), (3, 3, 2))
        f = Fifo(size=5, abits=3, pw=3, wrap=True)            # a wrap at 4, the last of 5 entries
        self.assertEqual(len(detect_fifos(f.nl, {f.rst: 0})[0]), 2)
        f = Fifo(size=6, abits=3, pw=3)                       # wraps at 8 (mem_addr checks the range)
        self.assertEqual(len(detect_fifos(f.nl, {f.rst: 0})[0]), 2)

    def test_not_fifos(self):
        for kw in ({"flush": True}, {"step": 2}, {"rd_clk": "clk2"}, {"wr_ports": 2}, {"offset": 1},
                   {"wr_clk_enable": 0}, {"clk_pol": 0}, {"addr_from_input": True}, {"same_pointer": True}):
            with self.subTest(kw=kw):
                f = Fifo(**kw)
                self.assertEqual(detect_fifos(f.nl, {f.rst: 0}), ([], set()))

    def test_ports_and_attributes(self):
        f = Fifo(rd_ports=2)                                  # the pointer reads at the second port
        self.assertEqual(len(detect_fifos(f.nl, {f.rst: 0})[0]), 2)
        self.assertEqual(detect_fifos(Fifo(wr_clk_pol=0).nl, {})[0], [])
        f = Fifo(wr_clk_pol=0)
        self.assertEqual(detect_fifos(f.nl, {f.rst: 0})[0], [])                # written on the falling edge
        f = Fifo(waive="fifo_overflow")
        self.assertEqual({c.waive_attr for c in detect_fifos(f.nl, {f.rst: 0})[0]}, {"fifo_overflow"})

    def test_wrap_must_be_at_the_last_entry(self):
        f = Fifo(size=3, wrap=True)
        # Re-point the wrap compare of wp at entry 1 instead of 2.
        for cell in f.nl.cells.values():
            if cell["type"] == "$eq" and cell["connections"]["A"] == f.wp[0]:
                cell["connections"]["B"] = const(1, 2)
        f.nl = type(f.nl)(f.nl.data, f.nl.top)
        self.assertEqual(detect_fifos(f.nl, {f.rst: 0})[0], [])

    def test_no_read_port_or_memory(self):
        b = NB()
        b.input("clk")
        self.assertEqual(detect_fifos(b.build(), {}), ([], set()))
        f = Fifo()
        f.nl.cells["$mem_v2$m"]["parameters"]["RD_PORTS"] = 0
        self.assertEqual(detect_fifos(f.nl, {f.rst: 0}), ([], set()))


class Strengthening(unittest.TestCase):
    """A guess at the design's own count of the entries, with the plain
    check as the fallback."""

    def test_pointer_difference(self):
        f = Fifo(size=4, pw=3)                                # an extra wrap bit, both pointers
        over, under = detect_fifos(f.nl, {f.rst: 0})[0]
        self.assertEqual((over.params["CAND"], over.params["NW"]), (2, 1))
        self.assertEqual(over.fallback.params.get("CAND"), None)
        self.assertEqual(over.fallback.ports, {k: v for k, v in over.ports.items()})
        self.assertEqual((over.id, over.fallback.id, under.fallback.params["OVER"]), (under.id.replace("under", "over"),
                                                                                       over.id, 0))
        for kw in ({"size": 3, "abits": 2, "pw": 3}, {"size": 4, "pw": 3, "rp_pw": 2}):
            with self.subTest(kw=kw):
                f = Fifo(**kw)
                checks = detect_fifos(f.nl, {f.rst: 0})[0]
                self.assertTrue(checks)
                self.assertTrue(all(c.fallback is None for c in checks))

    def count(self, f, name="cnt", w=3, step="add_sub", reads=True):
        """Add a register that counts writes and reads; the write pointer reads it when `reads`."""
        b = f.b
        q = b.net(name, b.new(w))
        one = lambda bit: [bit] + ["0"] * (w - 1)  # noqa: E731
        if step == "add_sub":
            nxt = b.op("$sub", w=w, A=b.op("$add", w=w, A=q, B=one(f.we)), B=one(f.re))
        elif step == "add":
            nxt = b.op("$add", w=w, A=q, B=one(f.we))
        elif step == "add_b":                                 # we + cnt
            nxt = b.op("$add", w=w, A=one(f.we), B=q)
        elif step == "sub":                                   # cnt - re
            nxt = b.op("$sub", w=w, A=q, B=one(f.re))
        elif step == "sub_add":                               # (we + cnt) - re
            nxt = b.op("$sub", w=w, A=b.op("$add", w=w, A=one(f.we), B=q), B=one(f.re))
        elif step == "add_add":                               # (cnt + we) + re: an odd count, still a self step
            nxt = b.op("$add", w=w, A=b.op("$add", w=w, A=q, B=one(f.we)), B=one(f.re))
        elif step == "sub_inner":                             # (cnt - re) + we
            nxt = b.op("$add", w=w, A=b.op("$sub", w=w, A=q, B=one(f.re)), B=one(f.we))
        elif step == "other_add":                             # (x + y) - re: no self step
            nxt = b.op("$sub", w=w, A=b.op("$add", w=w, A=b.input(f"{name}_x", w), B=b.input(f"{name}_y", w)),
                       B=one(f.re))
        else:
            nxt = b.input(f"{name}_in", w)
        b.ff(b.mux(nxt, const(0, w), f.rst), f.clk, q=q, name=f"$dff${name}")
        if reads:
            # Gate the write pointer's move on cnt (a full check), through its select.
            wq = f.wp[0]
            full = b.op("$ne", w=1, A=q, B=const(4, w))[0]
            (c,) = [c for c in b.cells.values() if c["type"] == "$mux" and c["connections"]["A"] == wq]   # hold or move
            c["connections"]["S"] = [b.op("$logic_and", w=1, A=c["connections"]["S"], B=[full])[0]]
        f.nl = f.b.build()
        return q

    def test_count_register(self):
        f = Fifo()
        q = self.count(f)
        over, under = detect_fifos(f.nl, {f.rst: 0})[0]
        self.assertEqual((over.params["CAND"], over.params["NW"], over.ports["n"]), (1, 3, q))
        self.assertEqual((over.fallback.ports["n"], over.fallback.fallback), (["0"], None))
        self.assertEqual(under.params["CAND"], 1)
        f = Fifo()
        self.count(f, reads=False)                            # the pointers don't read it
        self.assertIsNone(detect_fifos(f.nl, {f.rst: 0})[0][0].fallback)
        f = Fifo()
        self.count(f, step="load")                            # no self step
        self.assertIsNone(detect_fifos(f.nl, {f.rst: 0})[0][0].fallback)
        f = Fifo()
        q = self.count(f, step="add")                         # cnt <= cnt + we: a self step too
        self.assertEqual(detect_fifos(f.nl, {f.rst: 0})[0][0].ports["n"], q)
        f = Fifo(size=16, abits=4, pw=4)
        self.count(f, w=3)                                    # too narrow for 16 entries
        self.assertIsNone(detect_fifos(f.nl, {f.rst: 0})[0][0].fallback)
        for step in ("add_b", "sub", "sub_add", "add_add", "sub_inner"):
            with self.subTest(step=step):
                f = Fifo()
                q = self.count(f, step=step)
                self.assertEqual(detect_fifos(f.nl, {f.rst: 0})[0][0].ports["n"], q)
        f = Fifo()
        self.count(f, step="other_add")
        self.assertIsNone(detect_fifos(f.nl, {f.rst: 0})[0][0].fallback)
        for w, found in ((32, True), (33, False)):            # at most 32 bits
            with self.subTest(w=w):
                f = Fifo()
                self.count(f, w=w)
                self.assertEqual(detect_fifos(f.nl, {f.rst: 0})[0][0].fallback is not None, found)

    def test_the_narrowest_count_wins(self):
        f = Fifo()
        self.count(f, name="c4", w=4)
        self.count(f, name="c3", w=3)
        self.assertEqual(detect_fifos(f.nl, {f.rst: 0})[0][0].ports["n"], f.nl.netnames["c3"]["bits"])


class Pointers(unittest.TestCase):
    def check(self, kind, cell, preset=None):
        return Check(kind, "x", "a.v:1", "d", anchors=[cell], preset=preset)

    def test_settle(self):
        checks = [self.check("counter_overflow", "wp"), self.check("counter_overflow", "other"),
                  self.check("counter_underflow", "wp"), self.check("counter_overflow", "rp", preset=INFO)]
        checks[3].reason = "free_running"
        self.assertEqual(settle_pointers(checks, {"wp", "rp"}), 1)
        c = checks[0]
        self.assertEqual((c.preset, c.reason), (INFO, FIFO_POINTER))
        self.assertEqual(c.detail, "a FIFO pointer: it wraps by design; fifo_overflow and fifo_underflow check "
                                   "the FIFO")
        self.assertEqual([x.preset for x in checks[1:3]], [None, None])
        self.assertEqual(checks[3].reason, "free_running")


class Checker(unittest.TestCase):
    def test_instance(self):
        p = Prop("fvl_t0", FIFO, {"PW": 2, "RW": 2, "CW": 3, "DEPTH": 4, "NR": 2, "RPOL": 2, "OVER": 1},
                 {"clk": [5], "wd": [1, 2], "wq": [3, 4], "rd": [6, 7], "rq": [8, 9], "r": [10, 11]}, [(12, 0)])
        cell = instance(p)
        self.assertEqual(cell["parameters"]["RPOL"], "10")
        self.assertEqual(cell["parameters"]["POL"], "0")
        self.assertEqual(cell["connections"]["r"], [10, 11])

    def test_the_checker_exists(self):
        from fvlint.sby import CHECKERS_V
        self.assertIn(f"module {FIFO} #(", CHECKERS_V)


if __name__ == "__main__":
    unittest.main()
