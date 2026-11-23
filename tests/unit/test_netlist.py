# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""fvlint.netlist: value decoding, indexing, naming, structure queries."""

from __future__ import annotations

import json
import os
import unittest

from fvlint.netlist import (Driver, Netlist, attr_true, const_value, display_path, is_const, param_int,
                            parse_yosys_version, src_short)

from .support import NB, TempDirCase, const, load_snapshot


class ValueDecoding(unittest.TestCase):
    def test_is_const(self):
        for b in ("0", "1", "x", "z"):
            self.assertTrue(is_const(b))
        self.assertFalse(is_const(7))

    def test_param_int(self):
        self.assertEqual(param_int(5), 5)
        self.assertEqual(param_int("101"), 5)                     # Yosys: MSB-first binary string
        self.assertEqual(param_int("00000000000000000000000000001100"), 12)
        for bad in ("", "1x0", "abc", None, 1.5):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                param_int(bad)

    def test_attr_true(self):
        self.assertFalse(attr_true(None))
        self.assertFalse(attr_true(0))
        self.assertTrue(attr_true(1))
        self.assertTrue(attr_true("00000000000000000000000000000001"))   # 32-bit binary attribute
        self.assertFalse(attr_true("00000000000000000000000000000000"))
        self.assertFalse(attr_true("x"))
        self.assertTrue(attr_true("yes"))                                  # free-form string attribute
        self.assertFalse(attr_true(""))

    def test_const_value(self):
        self.assertEqual(const_value([]), 0)
        self.assertEqual(const_value(["1", "0", "1"]), 5)                 # LSB first
        self.assertEqual(const_value(["0", "0", "0", "1"]), 8)
        self.assertEqual(const_value(const(0xA5, 8)), 0xA5)
        for bad in (["1", "x"], ["z"], [3, "1"]):
            with self.subTest(bad=bad):
                self.assertIsNone(const_value(bad))

    def test_parse_yosys_version(self):
        self.assertEqual(parse_yosys_version("Yosys 0.71 (git sha1 b4c586fd3, Release)"), (0, 71))
        self.assertEqual(parse_yosys_version("prefix\nYosys 12.3+45 (...)"), (12, 3))
        self.assertIsNone(parse_yosys_version("yosys version unknown"))


class SourceLocations(TempDirCase):
    def test_plain(self):
        self.assertEqual(src_short(None), "?")
        self.assertEqual(src_short(""), "?")
        self.assertEqual(src_short("rtl/a.v:12.3-14.8"), "rtl/a.v:12")
        self.assertEqual(src_short("a.v:7.1-7.9|b.v:9.2-9.3"), "a.v:7")    # first location wins
        self.assertEqual(src_short("nocolon"), "nocolon")
        self.assertEqual(src_short("c:/w/a.v:3.1-3.2"), "c:/w/a.v:3")      # only the last ':' splits

    def test_relative_to_yosys_dir_and_cwd(self):
        self.chdir(self.tmp)
        edir = os.path.join(self.tmp, "out", "elab")
        self.assertEqual(src_short("../../rtl/a.v:5.1-5.2", edir), os.path.join("rtl", "a.v") + ":5")

    def test_staged_copy_mapped_back(self):
        self.chdir(self.tmp)
        edir = os.path.join(self.tmp, "out", "elab")
        stage, orig = os.path.join(edir, "src"), os.path.join(self.tmp, "ip")
        self.assertEqual(src_short("src/core/a.v:9.1-9.2", edir, (stage, orig)),
                         os.path.join("ip", "core", "a.v") + ":9")
        # A sibling directory that merely shares the prefix is not remapped.
        self.assertEqual(src_short("srcx/a.v:9.1-9.2", edir, (stage, orig)),
                         os.path.join("out", "elab", "srcx", "a.v") + ":9")

    def test_display_path(self):
        self.chdir(self.tmp)
        self.assertEqual(display_path(os.path.join(self.tmp, "a", "b.v")), os.path.join("a", "b.v"))
        up = os.path.join(os.path.dirname(self.tmp), "x.v")
        self.assertEqual(display_path(up), os.path.join("..", "x.v"))        # just above the CWD: relative
        far = os.path.join(os.path.sep, "fvlint_far", "a", "b.v")
        os.makedirs(os.path.join(self.tmp, "d1", "d2", "d3"))
        self.chdir(os.path.join(self.tmp, "d1", "d2", "d3"))
        self.assertEqual(display_path(far), far)                             # far away: absolute
        self.assertEqual(display_path(os.path.join(self.tmp, "d1", "y.v")), os.path.join("..", "..", "y.v"))
        self.assertEqual(display_path(os.path.join(self.tmp, "z.v")), os.path.abspath(os.path.join(self.tmp, "z.v")))

    def test_display_path_through_a_symlink(self):
        # The CWD reached through a link (macOS: /var -> /private/var): still relative.
        real = os.path.join(self.tmp, "real")
        os.makedirs(os.path.join(real, "src"))
        link = os.path.join(self.tmp, "link")
        os.symlink(real, link)
        self.chdir(link)
        self.assertEqual(display_path(os.path.join(real, "src", "a.v")), os.path.join("src", "a.v"))
        self.assertEqual(display_path(os.path.join(link, "src", "a.v")), os.path.join("src", "a.v"))


class Indexing(TempDirCase):
    def test_missing_top(self):
        with self.assertRaisesRegex(KeyError, "other"):
            Netlist(NB().data("t"), "other")

    def test_load_from_file(self):
        b = NB()
        b.input("a")
        p = self.write("n.json", json.dumps(b.data("top")))
        nl = Netlist.load(p, "top", src_base="/x", src_map=("/s", "/o"))
        self.assertEqual(nl.top, "top")
        self.assertEqual((nl.src_base, nl.src_map), ("/x", ("/s", "/o")))

    def test_drivers_readers_and_port_inputs(self):
        b = NB()
        a = b.input("a", 2)
        io = b.input("io", 1, direction="inout")
        b.output("o", b.op("$not", A=a))
        nl = b.build()
        self.assertEqual(nl.port_in, set(a) | set(io))           # outputs are not inputs
        y = nl.ports["o"]["bits"]
        cell = next(iter(nl.cells))
        self.assertEqual(nl.driver[y[1]], Driver(cell, "Y", 1))
        self.assertEqual(nl.readers[a[0]], [(cell, "A", 0)])
        self.assertNotIn(y[0], nl.readers)
        self.assertEqual(list(nl.inputs(cell)), [("A", a)])
        self.assertEqual(list(nl.outputs(cell)), [("Y", y)])

    def test_inout_cell_port_is_driver_and_reader(self):
        b = NB()
        x = b.new(1)
        b.cell("bb", "my_pad", {"PAD": x}, dirs={"PAD": "inout"})
        nl = b.build()
        self.assertEqual(nl.driver[x[0]].cell, "bb")
        self.assertEqual(nl.readers[x[0]], [("bb", "PAD", 0)])
        self.assertEqual(list(nl.outputs("bb")), [("PAD", x)])
        self.assertEqual(list(nl.inputs("bb")), [("PAD", x)])

    def test_constant_bits_are_never_indexed(self):
        b = NB()
        b.cell("c", "$not", {"A": ["1"], "Y": ["0"]})
        nl = b.build()
        self.assertEqual((nl.driver, nl.readers), ({}, {}))

    def test_missing_port_direction_defaults_to_input(self):
        b = NB()
        x = b.new(1)
        b.cell("c", "$not", {"A": x, "Y": b.new(1)}, dirs={})
        nl = b.build()
        self.assertEqual(nl.readers[x[0]], [("c", "A", 0)])
        self.assertEqual(list(nl.outputs("c")), [])
        self.assertEqual([p for p, _ in nl.inputs("c")], ["A", "Y"])

    def test_cell_classification(self):
        b = NB()
        for name, t in [("ff", "$adffe"), ("mem", "$mem_v2"), ("rd", "$memrd_v2"), ("g", "$_DFF_PN0_"),
                        ("glatch", "$_DLATCH_P_"), ("and", "$and"), ("gate", "$_AND_"),
                        ("src", "$anyseq"), ("a", "$assert"), ("cov", "$cover"), ("pr", "$print"),
                        ("as", "$assume"), ("lv", "$live"), ("fr", "$fair"), ("ck", "$check"),
                        ("si", "$scopeinfo"), ("sp2", "$specify2"), ("sp3", "$specify3"), ("sr", "$specrule"),
                        ("eq", "$equiv"), ("new", "$frobnicate"), ("bb", "vendor_pll")]:
            b.cell(name, t, {})
        nl = b.build()
        kinds = {c: nl.kind(c) for c in nl.cells}
        self.assertEqual(kinds, {"ff": "state", "mem": "state", "rd": "state", "g": "state",
                                 "glatch": "state", "and": "comb", "gate": "comb", "src": "comb",
                                 "a": "sink", "cov": "sink", "pr": "sink", "as": "sink", "lv": "sink",
                                 "fr": "sink", "ck": "sink", "si": "sink", "sp2": "sink", "sp3": "sink",
                                 "sr": "sink", "eq": "sink", "new": "opaque", "bb": "opaque"})
        self.assertEqual(nl.unknown_types, {"$frobnicate"})      # user/vendor cells are not "unknown"
        self.assertTrue(nl.is_stateful("ff") and not nl.is_stateful("and"))
        self.assertTrue(nl.is_opaque("bb") and not nl.is_opaque("a"))

    def test_param_and_attr_accessors(self):
        b = NB()
        b.cell("c", "$x", {}, params={"W": "0101", "N": 3, "S": "\\name", "Z": "1x"},
               attrs={"src": "a.v:3.1-3.2"})
        nl = b.build()
        self.assertEqual(nl.param("c", "W"), 5)
        self.assertEqual(nl.param("c", "N"), 3)
        self.assertEqual(nl.param("c", "S"), "\\name")               # non-numeric returned as is
        self.assertEqual(nl.param("c", "Z"), "1x")
        self.assertEqual(nl.param("c", "missing", 9), 9)
        self.assertEqual(nl.cell_src("c"), "a.v:3")
        self.assertEqual(nl.conn("c", "nope"), [])
        self.assertEqual(nl.ctype("c"), "$x")


class Naming(unittest.TestCase):
    def setUp(self):
        b = NB()
        self.v = b.new(4)
        b.net("$auto$1", self.v, hidden=True)
        b.net("top_q", self.v)
        b.net("u.inner_q", self.v)
        b.net("u.v.deepest_q", self.v, src="d.v:4.1-4.2", fvlint_waive="counter_overflow")
        self.h = b.net("$hidden_only", b.new(2), hidden=True, src="gen.v:9.1-9.2")
        self.mixed_a = b.net("ma", b.new(2))
        self.mixed_b = b.net("mb", b.new(2))
        self.b = b
        self.nl = b.build()

    def test_visible_innermost_then_shortest(self):
        self.assertEqual(self.nl.name_of(self.v), "u.v.deepest_q")
        self.assertEqual([n for n, _ in self.nl.nets_for(self.v)],
                         ["u.v.deepest_q", "u.inner_q", "top_q", "$auto$1"])
        self.assertEqual(self.nl.bit_name[self.v[2]], "u.v.deepest_q[2]")

    def test_missing_hide_name_means_visible(self):
        b = NB()
        v = b.new(2)
        b.netnames["plain"] = {"bits": v, "attributes": {"src": "p.v:2.1-2.2"}}
        b.net("$a", v, hidden=True)                                     # sorts first by name, but hidden
        nl = b.build()
        self.assertEqual((nl.visible_name(v), nl.net_src(v), nl.name_of(v)), ("plain", "p.v:2", "plain"))
        self.assertEqual(nl.bit_name[v[0]], "plain[0]")

    def test_equal_depth_prefers_shorter_then_alphabetical(self):
        b = NB()
        v = b.new(1)
        b.net("bb", v)
        b.net("a_long", v)
        b.net("aa", v)
        self.assertEqual(b.build().bit_name[v[0]], "aa")

    def test_hidden_names_are_last_resort(self):
        self.assertEqual(self.nl.name_of(self.h), "$hidden_only")
        self.assertIsNone(self.nl.visible_name(self.h))
        self.assertEqual(self.nl.net_src(self.h), "?")
        self.assertEqual(self.nl.visible_name(self.v), "u.v.deepest_q")

    def test_partial_and_mixed_vectors(self):
        self.assertEqual(self.nl.name_of(self.v[1:3]), "u.v.deepest_q[2:1]")
        self.assertEqual(self.nl.name_of(self.v[2:4]), "u.v.deepest_q[3:2]")   # distinct from [2:1]
        self.assertEqual(self.nl.name_of([self.v[2]]), "u.v.deepest_q[2]")
        self.assertEqual(self.nl.name_of([self.v[3], self.v[0]]), "{u.v.deepest_q[0],u.v.deepest_q[3]}")
        self.assertEqual(self.nl.name_of([self.mixed_a[0], self.mixed_b[1]]), "{mb[1],ma[0]}")  # MSB first
        self.assertEqual(self.nl.name_of([999]), "999")                   # unnamed bit
        self.assertEqual(self.nl.name_of([self.mixed_a[1], "0"]), "{0,ma[1]}")

    def test_constants_and_empty(self):
        self.assertEqual(self.nl.name_of([]), "?")
        self.assertEqual(self.nl.name_of(["1", "0", "0"]), "'001")          # MSB first

    def test_attributes_from_any_alias(self):
        self.assertEqual(self.nl.net_attr(self.v, "fvlint_waive"), "counter_overflow")
        self.assertIsNone(self.nl.net_attr(self.v, "nope"))
        self.assertIsNone(self.nl.net_attr([12345], "src"))
        self.assertEqual(self.nl.net_src(self.v), "d.v:4")

    def test_instance_of_a_flattened_cell(self):
        b = NB()
        cells = {
            "$procmux$3": ({}, ""),                                              # top module
            "top_reg": ({}, ""),
            "$flatten\\u_a.$procmux$8": ({}, "u_a"),                           # as Yosys 0.71 names them
            "$flatten\\p0.\\u_a.$procmux$2": ({}, "p0.u_a"),                    # nested: escaped again
            "$flatten\\u_a.$auto$proc_rom.cc:155$3": ({}, "u_a"),              # dots in the cell's own name
            "$flatten\\gen[0].u$1.$procmux$4": ({}, "gen[0].u$1"),
            "$flatten\\u_a.odd": ({}, "u_a"),
            "u_b.named": ({}, "u_b"),                                            # public, no hdlname
            "u_c.named": ({"hdlname": "p1 u_c named"}, "p1.u_c"),
            "x": ({"hdlname": "x"}, ""),
            "$y": ({"hdlname": " "}, ""),
        }
        for name, (attrs, _) in cells.items():
            b.cell(name, "$and", {"A": b.new(), "B": b.new(), "Y": b.new()}, attrs=attrs)
        nl = b.build()
        for name, (_, want) in cells.items():
            with self.subTest(name=name):
                self.assertEqual(nl.instance(name), want)


class Structure(unittest.TestCase):
    def test_whole_driver(self):
        b = NB()
        a = b.input("a", 4)
        y = b.op("$not", A=a)
        z = b.op("$not", A=a)
        nl = b.build()
        cell = nl.driver[y[0]].cell
        self.assertEqual(nl.whole_driver(y), (cell, "Y", 0))
        self.assertEqual(nl.whole_driver(y[1:3]), (cell, "Y", 1))
        self.assertIsNone(nl.whole_driver([y[1], y[0]]))          # out of order
        self.assertIsNone(nl.whole_driver([y[0], y[2]]))          # gap
        self.assertIsNone(nl.whole_driver([y[0], z[1]]))          # two cells
        self.assertIsNone(nl.whole_driver([y[0], "0"]))           # constant
        self.assertIsNone(nl.whole_driver(a))                     # undriven (port)
        self.assertIsNone(nl.whole_driver([]))

    def test_compare_cells(self):
        b = NB()
        q = b.input("q", 3)
        b.op("$eq", w=1, name="eq", A=q, B=const(3, 3))
        b.op("$lt", w=1, name="lt", A=const(1, 3), B=q[:1] + ["0", "0"])
        b.op("$add", name="add", A=q, B=const(1, 3))
        nl = b.build()
        self.assertEqual(nl.compare_cells(q, {"$eq", "$lt"}), {"eq", "lt"})
        self.assertEqual(nl.compare_cells(q[1:], {"$eq", "$lt"}), {"eq"})

    def test_equality(self):
        b = NB()
        st, x = b.input("st", 2), b.input("x", 2)
        cases = [
            (b.op("$eq", w=1, A=st, B=const(1, 2)), 1, (st, 1)),
            (b.op("$eqx", w=1, A=const(3, 2), B=st), 1, (st, 3)),                   # constant first
            (b.op("$ne", w=1, A=st + ["0", "0"], B=const(9, 4)), 0, (st, 9)),      # zero-extended
            (b.op("$nex", w=1, A=st, B=const(2, 2)), 0, (st, 2)),
            (b.op("$eq", w=1, A=st, B=const(1, 2)), 0, None),                      # st != 1: no value
            (b.op("$ne", w=1, A=st, B=const(1, 2)), 1, None),
            (b.op("$eq", w=1, A=st, B=x), 1, None),                                # no constant
            (b.op("$eq", w=1, A=const(1, 2), B=const(1, 2)), 1, None),             # no signal
            (b.op("$eq", w=1, A=[st[0], "1", st[1]], B=const(1, 3)), 1, None),     # not one signal
            (b.op("$lt", w=1, A=st, B=const(1, 2)), 1, None),
            (b.op("$eq", w=2, A=st, B=const(1, 2))[1:], 1, None),                  # not the result bit
            (x[:1], 1, None),                                                      # no driver
        ]
        nl = b.build()
        for i, (y, value, want) in enumerate(cases):
            with self.subTest(i=i):
                got = nl.equality(y[0], value)
                self.assertEqual(got, None if want is None else (list(want[0]), want[1]))

    def test_depends_on_counts_register_stages(self):
        b = NB()
        clk = b.input("clk")
        x = b.input("x")
        s1 = b.ff(x, clk[0])
        s2 = b.ff(b.op("$not", A=s1), clk[0])
        nl = b.build()
        self.assertTrue(nl.depends_on(s1, x, 1))
        self.assertFalse(nl.depends_on(s1, x, 0))
        self.assertTrue(nl.depends_on(s2, x, 2))
        self.assertFalse(nl.depends_on(s2, x, 1))
        self.assertTrue(nl.depends_on(s2, s2, 0))                 # the bits themselves
        self.assertFalse(nl.depends_on(["1"], x, 5))

    def test_depends_on_stops_at_opaque_and_terminates_on_loops(self):
        b = NB()
        clk, x = b.input("clk"), b.input("x")
        y = b.new(1)
        b.cell("bb", "vendor_buf", {"I": x, "O": y}, dirs={"I": "input", "O": "output"})
        q = b.new(1)
        b.ff(b.op("$xor", A=q, B=y), clk[0], q=q)                 # q depends on itself
        nl = b.build()
        self.assertFalse(nl.depends_on(q, x, 10))                 # only through the blackbox
        self.assertTrue(nl.depends_on(q, y, 1))

    def test_depends_on_terminates_on_combinational_loops(self):
        b = NB()
        x, other = b.input("x"), b.input("other")
        loop = b.new(1)
        y = b.op("$and", A=loop, B=x)
        b.cell("inv", "$not", {"A": y, "Y": loop})                # y -> loop -> y, no register
        nl = b.build()
        self.assertFalse(nl.depends_on(y, other, 3))
        self.assertTrue(nl.depends_on(y, x, 0))

    def test_ff_info_conditions(self):
        b = NB()
        clk, en, ar, sr = (b.input(n)[0] for n in ("clk", "en", "ar", "sr"))
        d = b.input("d", 2)
        q1 = b.ff(d, clk, name="plain")
        b.ff(d, clk, name="en_lo", en=en, en_pol=0)
        b.ff(d, clk, name="ar", arst=ar, arst_pol=1, en=en)
        b.ff(d, clk, name="sr", srst=sr, srst_pol=0)
        b.cell("al", "$aldff", {"CLK": [clk], "ALOAD": [ar], "AD": d, "D": d, "Q": b.new(2)},
               {"WIDTH": 2, "CLK_POLARITY": 1, "ALOAD_POLARITY": 1})
        nl = b.build()
        info = nl.ff_info("plain")
        self.assertEqual((info["type"], info["D"], info["Q"], info["conds"]), ("$dff", d, q1, []))
        self.assertEqual(nl.ff_info("en_lo")["conds"], [(en, 0)])
        self.assertEqual(nl.ff_info("ar")["conds"], [(en, 1), (ar, 0)])
        self.assertEqual(nl.ff_info("sr")["conds"], [(sr, 1)])          # active-low reset: D wins at 1
        self.assertEqual(nl.ff_info("al")["conds"], [(ar, 0)])

    def test_ff_info_default_polarity_is_active_high(self):
        b = NB()
        clk, en = b.input("clk")[0], b.input("en")[0]
        b.cell("f", "$dffe", {"CLK": [clk], "EN": [en], "D": b.new(1), "Q": b.new(1)}, {"WIDTH": 1})
        self.assertEqual(b.build().ff_info("f")["conds"], [(en, 1)])


class Clocks(unittest.TestCase):
    def test_flip_flops_and_latches(self):
        b = NB()
        clk = b.input("clk")[0]
        d = b.new(1)
        b.ff(d, clk, name="pos")
        b.ff(d, clk, name="neg", clk_pol=0)
        b.ff(d, "1", name="tied")
        b.cell("lat", "$dlatch", {"EN": [clk], "D": d, "Q": b.new(1)}, {"WIDTH": 1, "EN_POLARITY": 1})
        b.cell("noclk", "$ff", {"D": d, "Q": b.new(1)}, {"WIDTH": 1})
        nl = b.build()
        self.assertEqual(nl.clocks("pos"), {(clk, 1)})
        self.assertEqual(nl.clocks("neg"), {(clk, 0)})
        self.assertEqual(nl.clocks("tied"), set())
        self.assertEqual(nl.clocks("lat"), {("latch", 0)})
        self.assertEqual(nl.clocks("noclk"), set())                    # $ff: global clock

    def _mem(self, rd_clk_en, wr_clk_en, rd_pol="11", wr_pol="1", wr_en_const=None):
        """Two read ports (clocks c1, c2), one write port (clock c2).
        Parameters are MSB-first binary strings, one bit per port."""
        b = NB()
        c1, c2 = b.input("c1")[0], b.input("c2")[0]
        wr_en = [wr_en_const] if wr_en_const else b.new(1)
        b.cell("m", "$mem_v2", {
            "RD_CLK": [c1, c2], "RD_EN": ["1", "1"], "RD_ADDR": b.new(2), "RD_DATA": b.new(2),
            "RD_ARST": ["0", "0"], "RD_SRST": ["0", "0"],
            "WR_CLK": [c2], "WR_EN": wr_en, "WR_ADDR": b.new(1), "WR_DATA": b.new(1)},
            {"WIDTH": 1, "SIZE": 2, "ABITS": 1, "RD_PORTS": 2, "WR_PORTS": 1,
             "RD_CLK_ENABLE": rd_clk_en, "RD_CLK_POLARITY": rd_pol, "WR_CLK_ENABLE": wr_clk_en,
             "WR_CLK_POLARITY": wr_pol})
        return b.build(), c1, c2

    def test_memory_ports(self):
        nl, c1, c2 = self._mem("11", "1")
        self.assertEqual(nl.clocks("m"), {(c1, 1), (c2, 1)})
        nl, c1, c2 = self._mem("10", "1", rd_pol="01")                 # only rd1 clocked, on c2 falling
        self.assertEqual(nl.clocks("m"), {(c2, 0), (c2, 1)})
        nl, c1, c2 = self._mem("01", "0", rd_pol="00", wr_en_const="0")  # only rd0, on c1 falling
        self.assertEqual(nl.clocks("m"), {(c1, 0)})
        nl, c1, c2 = self._mem("00", "1")
        self.assertEqual(nl.clocks("m"), {(c2, 1)})                     # async reads are combinational

    def test_unclocked_write_port_is_level_sensitive(self):
        nl, _, _ = self._mem("00", "0")
        self.assertEqual(nl.clocks("m"), {("latch", 0)})
        nl, _, _ = self._mem("00", "0", wr_en_const="0")               # never written
        self.assertEqual(nl.clocks("m"), set())

    def test_write_enables_are_sliced_per_port(self):
        b = NB()
        clk = b.input("clk")[0]
        live = b.new(2)
        b.cell("m", "$mem_v2", {"RD_CLK": [], "RD_EN": [], "RD_ADDR": [], "RD_DATA": [], "WR_CLK": [clk, "x"],
                                "WR_EN": ["0", "0"] + live, "WR_ADDR": b.new(2), "WR_DATA": b.new(4)},
               {"WIDTH": 2, "SIZE": 2, "ABITS": 1, "RD_PORTS": 0, "WR_PORTS": 2, "RD_CLK_ENABLE": "0",
                "RD_CLK_POLARITY": "0", "WR_CLK_ENABLE": "01", "WR_CLK_POLARITY": "01"})
        self.assertEqual(b.build().clocks("m"), {(clk, 1), ("latch", 0)})   # port 1: unclocked, enabled
        for clk_en, wen in (("10", ["0", "0"] + live), ("01", live + ["0", "0"])):
            with self.subTest(clocked=clk_en):                          # the unclocked port is never written
                b.cells["m"]["parameters"]["WR_CLK_ENABLE"] = clk_en
                b.cells["m"]["parameters"]["WR_CLK_POLARITY"] = clk_en
                b.cells["m"]["connections"]["WR_EN"] = wen
                b.cells["m"]["connections"]["WR_CLK"] = [clk, "x"] if clk_en == "01" else ["x", clk]
                self.assertEqual(b.build().clocks("m"), {(clk, 1)})

    def test_constant_memory_clock_ignored(self):
        b = NB()
        b.cell("m", "$mem_v2", {"RD_CLK": ["0"], "RD_EN": ["1"], "RD_ADDR": b.new(1), "RD_DATA": b.new(1),
                                "WR_CLK": [], "WR_EN": [], "WR_ADDR": [], "WR_DATA": []},
               {"WIDTH": 1, "SIZE": 2, "ABITS": 1, "RD_PORTS": 1, "WR_PORTS": 0, "RD_CLK_ENABLE": "1",
                "RD_CLK_POLARITY": "1", "WR_CLK_ENABLE": "0", "WR_CLK_POLARITY": "0"})
        self.assertEqual(b.build().clocks("m"), set())


class RealNetlists(unittest.TestCase):
    """Indexing invariants on netlists Yosys really produced."""

    def test_every_bit_has_at_most_one_driver(self):
        for top in ("snap_counters", "snap_mux", "snap_fsm", "snap_reset", "snap_index", "snap_ops"):
            nl = load_snapshot(top)
            with self.subTest(top=top):
                seen = {}
                for cname in nl.cells:
                    for _, bits in nl.outputs(cname):
                        for b in bits:
                            if not is_const(b):
                                self.assertNotIn(b, seen, f"{b} driven by {seen.get(b)} and {cname}")
                                seen[b] = cname
                self.assertEqual(set(seen), set(nl.driver))
                self.assertEqual(nl.unknown_types, set())

    def test_every_cell_type_of_the_flow_is_modelled(self):
        # An unknown type would be cut (treated as a free input): fine for
        # soundness, but every check through it would lose precision.
        nl = load_snapshot("snap_ops")
        self.assertEqual(nl.unknown_types, set())
        kinds = {}
        for name, c in nl.cells.items():
            kinds.setdefault(c["type"], set()).add(nl.kind(name))
        state = {"$dff", "$adff", "$dffsr", "$aldff", "$dlatch", "$adlatch", "$mem_v2"}
        self.assertEqual(kinds, {t: {"state"} if t in state else {"comb"} for t in kinds})
        self.assertGreaterEqual(len(kinds), 40)
        clk = nl.ports["clk"]["bits"][0]
        by_type = {c["type"]: n for n, c in nl.cells.items()}
        self.assertEqual(nl.clocks(by_type["$dlatch"]), {("latch", 0)})
        self.assertEqual(nl.clocks(by_type["$adlatch"]), {("latch", 0)})
        self.assertEqual(nl.clocks(by_type["$dffsr"]), {(clk, 1)})
        self.assertEqual(nl.clocks(by_type["$aldff"]), {(clk, 1)})

    def test_hierarchical_register_named_where_it_lives(self):
        nl = load_snapshot("snap_counters")
        q = nl.netnames["u_sub.q"]["bits"]
        self.assertEqual(nl.name_of(q), "u_sub.q")
        ff = nl.whole_driver(q)
        self.assertIsNotNone(ff)
        self.assertEqual(nl.ctype(ff[0]), "$dff")
        self.assertEqual(nl.clocks(ff[0]), {(nl.ports["clk"]["bits"][0], 1)})

    def test_snapshot_memory(self):
        nl = load_snapshot("snap_mux")
        mem = [c for c in nl.cells if nl.ctype(c) == "$mem_v2"]
        self.assertEqual(len(mem), 1)
        clk = nl.ports["clk"]["bits"][0]
        self.assertEqual(nl.clocks(mem[0]), {(clk, 1)})


if __name__ == "__main__":
    unittest.main()
