# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""fvlint.detect: path conditions, mux traversal and the structure detectors."""

from __future__ import annotations

import unittest

from fvlint.checks import INFO, Check
from fvlint.detect import (MAX_PATHS, _compares, _dedupe, _dest_name, _fit, _operand_is, _signed_val,
                           clean_conds, detect_all, detect_case, detect_counters, detect_index,
                           detect_memory, forward, mux_sources)

from .support import NB, const, load_snapshot

PAR = "00000000000000000000000000000001"     # how Yosys writes a true attribute


class Conditions(unittest.TestCase):
    def test_clean_conds(self):
        self.assertEqual(clean_conds([]), [])
        self.assertEqual(clean_conds([(5, 1), ("1", 1), (5, 1), (6, 0)]), [(5, 1), (6, 0)])
        self.assertEqual(clean_conds([("0", 0)]), [])                  # constant true
        self.assertIsNone(clean_conds([("0", 1)]))                      # constant false: dead logic
        self.assertIsNone(clean_conds([("1", 0)]))
        self.assertIsNone(clean_conds([(5, 1), (6, 1), (5, 0)]))        # contradiction
        self.assertEqual(clean_conds([("x", 1), ("z", 0)]), [])         # unknown constant: no constraint

    def test_small_helpers(self):
        q = [10, 11, 12]
        self.assertTrue(_operand_is(q, q))
        self.assertTrue(_operand_is(q + ["0", "0"], q))                 # zero-extended
        self.assertFalse(_operand_is(q + ["1"], q))
        self.assertFalse(_operand_is(q[:2], q))
        self.assertFalse(_operand_is([11, 10, 12], q))
        self.assertEqual(_fit([1, 2], 4), [1, 2, "0", "0"])
        self.assertEqual(_fit([1, 2, "0"], 2), [1, 2])
        self.assertIsNone(_fit([1, 2, 3], 2))                           # would lose a live bit
        self.assertEqual(_signed_val(0b1111, 4), -1)
        self.assertEqual(_signed_val(0b1000, 4), -8)
        self.assertEqual(_signed_val(0b0111, 4), 7)


class MuxSources(unittest.TestCase):
    def test_leaf(self):
        b = NB()
        a = b.input("a", 2)
        nl = b.build()
        self.assertEqual(mux_sources(nl, a), [(a, [])])
        self.assertEqual(mux_sources(nl, a, [(7, 1)]), [(a, [(7, 1)])])
        y = b.op("$not", A=a)
        self.assertEqual(mux_sources(b.build(), y), [(y, [])])         # non-mux driver is a source

    def test_nested_mux_tree(self):
        b = NB()
        a, c, d = b.input("a", 2), b.input("c", 2), b.input("d", 2)
        s, t = b.input("s")[0], b.input("t")[0]
        y = b.mux(a, b.mux(c, d, t), s)
        got = mux_sources(b.build(), y)
        self.assertEqual(got, [(a, [(s, 0)]), (c, [(s, 1), (t, 0)]), (d, [(s, 1), (t, 1)])])

    def test_slice_of_a_mux_output(self):
        b = NB()
        a, c = b.input("a", 4), b.input("c", 4)
        s = b.input("s")[0]
        y = b.mux(a, c, s)
        self.assertEqual(mux_sources(b.build(), y[1:3]), [(a[1:3], [(s, 0)]), (c[1:3], [(s, 1)])])

    def test_constant_and_contradictory_selects_are_pruned(self):
        b = NB()
        a, c, d = b.input("a"), b.input("c"), b.input("d")
        s = b.input("s")[0]
        y = b.mux(a, c, "0")                                            # select tied low
        z = b.mux(d, b.mux(a, c, s), s)                                 # inner A needs s=1 and s=0
        nl = b.build()
        # Paths come back with their raw conditions (constant-true ones included);
        # only the feasible ones are returned.
        self.assertEqual(mux_sources(nl, y), [(a, [("0", 0)])])
        self.assertEqual([(bits, clean_conds(cs)) for bits, cs in mux_sources(nl, z)],
                         [(d, [(s, 0)]), (c, [(s, 1)])])
        self.assertEqual(mux_sources(nl, a, [("0", 1)]), [])            # caller's own dead condition

    def test_pmux(self):
        b = NB()
        dflt, i0, i1 = b.input("dflt", 2), b.input("i0", 2), b.input("i1", 2)
        s0, s1 = b.input("s0")[0], b.input("s1")[0]
        y = b.pmux(dflt, [i0, i1], [s0, s1])
        got = mux_sources(b.build(), y)
        self.assertEqual(got, [(i0, [(s0, 1)]), (i1, [(s1, 1)]), (dflt, [(s0, 0), (s1, 0)])])
        y2 = b.pmux(dflt, [i0, i1], [s0, s1])
        self.assertEqual(mux_sources(b.build(), y2[1:]), [(i0[1:], [(s0, 1)]), (i1[1:], [(s1, 1)]),
                                                          (dflt[1:], [(s0, 0), (s1, 0)])])

    def test_bmux(self):
        b = NB()
        data = b.input("data", 8)                                       # four 2-bit words
        sel = b.input("sel", 2)
        y = b.new(2)
        b.cell("bm", "$bmux", {"A": data, "S": sel, "Y": y}, {"WIDTH": 2, "S_WIDTH": 2})
        got = mux_sources(b.build(), y)
        self.assertEqual(got, [(data[0:2], [(sel[0], 0), (sel[1], 0)]), (data[2:4], [(sel[0], 1), (sel[1], 0)]),
                               (data[4:6], [(sel[0], 0), (sel[1], 1)]), (data[6:8], [(sel[0], 1), (sel[1], 1)])])

    def test_bmux_part_of_the_output(self):
        # Only bits 2..3 of each 4-bit word reach the register.
        b = NB()
        data, sel = b.input("data", 8), b.input("sel", 1)               # two 4-bit words
        y = b.new(4)
        b.cell("bm", "$bmux", {"A": data, "S": sel, "Y": y}, {"WIDTH": 4, "S_WIDTH": 1})
        self.assertEqual(mux_sources(b.build(), y[2:4]), [(data[2:4], [(sel[0], 0)]), (data[6:8], [(sel[0], 1)])])

    def test_wide_bmux_is_a_leaf(self):
        b = NB()
        sel = b.input("sel", 7)                                         # 128 words: too many paths
        y = b.new(1)
        b.cell("bm", "$bmux", {"A": b.input("data", 128), "S": sel, "Y": y}, {"WIDTH": 1, "S_WIDTH": 7})
        self.assertEqual(mux_sources(b.build(), y), [(y, [])])

    def test_paths_beyond_the_cap_are_kept_unexpanded(self):
        # 128 leaves: the first MAX_PATHS are listed, the rest come back as
        # unexpanded mux outputs; nothing is dropped.
        b = NB()
        sels = b.input("s", 7)
        leaves = [b.input(f"i{n}") for n in range(128)]
        level = leaves
        for s in sels:                                                  # balanced tree, 128 leaves
            level = [b.mux(level[i], level[i + 1], s) for i in range(0, len(level), 2)]
        nl = b.build()
        got = mux_sources(nl, level[0])
        listed = [bits for bits, _ in got if bits in leaves]
        self.assertEqual(len(listed), MAX_PATHS)
        covered = set(map(tuple, listed))
        for bits, _ in got:
            if bits not in leaves:
                self.assertEqual(nl.ctype(nl.whole_driver(bits)[0]), "$mux")
                covered |= {tuple(x) for x in leaves if nl.depends_on(bits, set(x), 0)}
        self.assertEqual(covered, set(map(tuple, leaves)))
        self.assertLess(len(got), MAX_PATHS + 8)

    def test_deep_chains_are_kept_unexpanded(self):
        # A 30-deep chain through each kind of mux input: 25 side inputs are
        # listed, the rest of the chain comes back as one unexpanded source.
        def mux_a(b, cur, i):
            return b.mux(cur, b.input(f"i{i}"), b.input(f"s{i}")[0])

        def mux_b(b, cur, i):
            return b.mux(b.input(f"i{i}"), cur, b.input(f"s{i}")[0])

        def pmux_default(b, cur, i):
            return b.pmux(cur, [b.input(f"i{i}")], [b.input(f"s{i}")[0]])

        def pmux_case(b, cur, i):
            return b.pmux(b.input(f"i{i}"), [cur], [b.input(f"s{i}")[0]])

        def bmux(b, cur, i):
            y = b.new(1)
            b.cell(None, "$bmux", {"A": b.input(f"i{i}") + cur, "S": b.input(f"s{i}"), "Y": y},
                   {"WIDTH": 1, "S_WIDTH": 1})
            return y
        for step in (mux_a, mux_b, pmux_default, pmux_case, bmux):
            with self.subTest(step=step.__name__):
                b = NB()
                cur = b.input("bottom")
                for i in range(30):
                    cur = step(b, cur, i)
                got = mux_sources(b.build(), cur)
                self.assertEqual(len(got), 26)
                self.assertNotIn(b.ports["bottom"]["bits"], [bits for bits, _ in got])

    def test_bmux_size_limit(self):
        for sw, expanded in ((6, True), (7, False)):                    # 64 words are expanded, 128 are not
            with self.subTest(words=1 << sw):
                b = NB()
                y = b.new(1)
                b.cell("bm", "$bmux", {"A": b.input("data", 1 << sw), "S": b.input("sel", sw), "Y": y},
                       {"WIDTH": 1, "S_WIDTH": sw})
                got = mux_sources(b.build(), y)
                self.assertEqual(got != [(y, [])], expanded)


class Forward(unittest.TestCase):
    def test_through_muxes_into_a_register(self):
        b = NB()
        clk, en, s = b.input("clk")[0], b.input("en")[0], b.input("s")[0]
        v, other = b.input("v", 2), b.input("o", 2)
        q = b.net("gnt", b.new(2))
        b.ff(b.mux(other, v, s), clk, q=q, en=en)
        conds, dest = forward(b.build(), v)
        self.assertEqual((conds, dest), ([(s, 1), (en, 1)], q))

    def test_stops_where_the_value_fans_out(self):
        b = NB()
        v = b.input("v", 2)
        s = b.input("s")[0]
        y = b.mux(v, b.input("o", 2), s)
        b.op("$not", A=y)
        b.op("$not", A=y)
        conds, dest = forward(b.build(), v)
        self.assertEqual((conds, dest), ([(s, 0)], y))                 # y has two readers

    def test_stops_at_other_logic(self):
        b = NB()
        v = b.input("v", 2)
        s = b.input("s")[0]
        y = b.mux(v, b.input("o", 2), s)
        b.op("$not", A=y)                                               # single reader, but not a mux
        self.assertEqual(forward(b.build(), v), ([(s, 0)], y))

    def test_split_readers_stop(self):
        b = NB()
        v = b.input("v", 2)
        b.op("$not", A=v[:1])
        b.op("$not", A=v[1:])
        self.assertEqual(forward(b.build(), v), ([], v))

    def test_pmux_and_bmux_ports(self):
        b = NB()
        a, i0, i1 = b.input("a", 2), b.input("i0", 2), b.input("i1", 2)
        s0, s1 = b.input("s0")[0], b.input("s1")[0]
        y = b.pmux(a, [i0, i1], [s0, s1])
        nl = b.build()
        self.assertEqual(forward(nl, a), ([(s0, 0), (s1, 0)], y))
        self.assertEqual(forward(nl, i1), ([(s1, 1)], y))
        self.assertEqual(forward(nl, i1[1:]), ([(s1, 1)], y[1:]))

        b = NB()
        data, sel = b.input("data", 4), b.input("sel", 2)
        y = b.new(1)
        b.cell("bm", "$bmux", {"A": data, "S": sel, "Y": y}, {"WIDTH": 1, "S_WIDTH": 2})
        self.assertEqual(forward(b.build(), data[2:3]), ([(sel[0], 0), (sel[1], 1)], y))

    def test_value_spanning_two_pmux_inputs_stops(self):
        b = NB()
        a, i0, i1 = b.input("a", 2), b.input("i0", 2), b.input("i1", 2)
        s = b.input("s", 2)
        y = b.pmux(a, [i0, i1], s)
        nl = b.build()
        flat = nl.conn(nl.driver[y[0]].cell, "B")
        self.assertEqual(forward(nl, flat[1:3]), ([], flat[1:3]))

    def test_value_spanning_two_bmux_words_stops(self):
        b = NB()
        data, sel = b.input("data", 8), b.input("sel", 2)               # four 2-bit words
        b.cell("bm", "$bmux", {"A": data, "S": sel, "Y": b.new(2)}, {"WIDTH": 2, "S_WIDTH": 2})
        nl = b.build()
        self.assertEqual(forward(nl, data[3:5]), ([], data[3:5]))       # bit 1 of word 1, bit 0 of word 2

    def test_partial_fanout_stops(self):
        b = NB()
        v = b.input("v", 2)
        s = b.input("s")[0]
        b.mux(v, b.input("o", 2), s)
        b.op("$not", A=v[1:])                                           # v[1] also read elsewhere
        self.assertEqual(forward(b.build(), v), ([], v))

    def test_register_control_ports_are_not_data(self):
        b = NB()
        clk, v = b.input("clk")[0], b.input("v")
        b.ff(b.input("d"), clk, en=v[0], q=b.net("q", b.new(1)))
        self.assertEqual(forward(b.build(), v), ([], v))                # stops at EN: no FF conditions

    def test_bmux_select_and_wide_words(self):
        b = NB()
        data, sel = b.input("data", 8), b.input("sel", 2)                # four 2-bit words
        y = b.new(2)
        b.cell("bm", "$bmux", {"A": data, "S": sel, "Y": y}, {"WIDTH": 2, "S_WIDTH": 2})
        nl = b.build()
        self.assertEqual(forward(nl, data[4:6]), ([(sel[0], 0), (sel[1], 1)], y))     # word 2
        self.assertEqual(forward(nl, data[5:6]), ([(sel[0], 0), (sel[1], 1)], y[1:]))
        self.assertEqual(forward(nl, data[3:5]), ([], data[3:5]))       # spans words 1 and 2
        self.assertEqual(forward(nl, sel), ([], sel))                   # the select is not data

    def test_dead_path(self):
        b = NB()
        v = b.input("v")
        y = b.mux(b.input("o"), v, "0")                                 # v is never selected
        self.assertEqual(forward(b.build(), v), (None, y))

    def test_constant_and_depth_limit(self):
        b = NB()
        v = b.input("v")
        self.assertEqual(forward(b.build(), ["1"]), ([], ["1"]))
        cur = v
        s = b.input("s")[0]
        for _ in range(20):
            cur = b.mux(b.input(f"o{_}"), cur, s)
        conds, dest = forward(b.build(), v, max_depth=3)
        self.assertEqual(len(conds), 1)                                 # duplicates of (s, 1) merged
        self.assertNotEqual(dest, cur)


class DestName(unittest.TestCase):
    def test_preference_order(self):
        b = NB()
        named = b.net("result", b.new(2))
        bus = b.net("bus", b.new(4))
        anon = b.net("$auto$x", b.new(2), hidden=True)
        nl = b.build()
        self.assertEqual(_dest_name(nl, named, anon, "a/t.v:3"), "result")
        self.assertEqual(_dest_name(nl, bus[1:3], anon, "a/t.v:3"), "bus")      # bits of one wider net
        self.assertEqual(_dest_name(nl, anon, named, "a/t.v:3"), "result")      # falls back to the source bits
        self.assertEqual(_dest_name(nl, anon, anon, "a/t.v:3"), "t.v:3")        # then the source location
        self.assertEqual(_dest_name(nl, [], [], "a/t.v:3"), "t.v:3")

    def test_a_net_of_exactly_these_bits_wins(self):
        # The bits are part of a wider net that ranks first (shorter name),
        # but a net of exactly these bits names them better.
        b = NB()
        wide = b.net("b", b.new(4))
        b.net("lo_part", wide[:2])
        nl = b.build()
        self.assertEqual(nl.bit_name[wide[0]], "b[0]")
        self.assertEqual(_dest_name(nl, wide[:2], [], "a/t.v:3"), "lo_part")

    def test_part_of_a_net_with_brackets_in_its_name(self):
        b = NB()
        bus = b.net("g[0].bus", b.new(4))
        nl = b.build()
        self.assertEqual(_dest_name(nl, bus[1:3], [], "a/t.v:3"), "g[0].bus")


def _counter(b: NB, w=4, step=1, op="$add", en=None, signed=False, const_on_a=False, name="q", clk=None,
             src=None):
    """q <= en ? q op step : q.  Returns (q bits, adder output)."""
    clk = clk if clk is not None else b.input("clk")[0]
    q = b.net(name, b.new(w), **({"src": src} if src else {}))
    k = const(step & ((1 << w) - 1), w)
    sgn = {"A_SIGNED": int(signed), "B_SIGNED": int(signed)}
    nxt = b.op(op, params=sgn, A=k, B=q) if const_on_a else b.op(op, params=sgn, A=q, B=k)
    d = b.mux(q, nxt, en) if en is not None else nxt
    b.ff(d, clk, q=q, name=f"ff_{name}")
    return q, nxt


class Counters(unittest.TestCase):
    def detect(self, b, max_level=3):
        return detect_counters(b.build(), max_level)

    def test_bounded_up_counter(self):
        b = NB()
        q = b.new(4)
        cmp = b.op("$ne", w=1, A=q, B=const(15, 4))                    # q != 15 guards the increment
        clk = b.input("clk")[0]
        b.net("q", q, src="r.v:7.1-7.9")
        b.ff(b.mux(q, b.op("$add", A=q, B=const(1, 4)), cmp[0]), clk, q=q, name="ff_q")
        checks, lemmas = self.detect(b)
        self.assertEqual(len(checks), 1)
        c = checks[0]
        self.assertEqual((c.id, c.src, c.checker, c.preset), ("counter_overflow:q", "r.v:7", "fvl_range", None))
        self.assertEqual(c.params, {"W": 4, "LO": 0, "HI": 14, "SIGNED": 0})
        self.assertEqual((c.ports, c.conds, c.anchors), ({"v": q}, [(cmp[0], 1)], ["ff_q"]))
        self.assertEqual(c.depth_hint, 16 + 2)
        self.assertIn("never wraps past 15 (4 bits)", c.desc)
        self.assertEqual(lemmas, {})                                    # 15 is the maximum: no useful bound

    def test_free_running_counter_is_informational(self):
        b = NB()
        _counter(b, en=b.input("en")[0])
        (c,), _ = self.detect(b)
        self.assertEqual(c.preset, INFO)
        self.assertIn("free-running", c.detail)

    def test_dependence_is_limited_to_max_level(self):
        # en is q[3] delayed by two registers: bounded only if the analysis looks 2 stages deep.
        b = NB()
        clk = b.input("clk")[0]
        q = b.net("q", b.new(4))
        r1 = b.ff(q[3:], clk)
        r2 = b.ff(r1, clk)
        b.ff(b.mux(q, b.op("$add", A=q, B=const(1, 4)), r2[0]), clk, q=q)
        self.assertEqual(detect_counters(b.build(), 2)[0][0].preset, None)
        self.assertEqual(detect_counters(b.build(), 1)[0][0].preset, INFO)

    def test_down_counter_and_step_size(self):
        b = NB()
        _counter(b, op="$sub", step=3)
        (c,), _ = self.detect(b)
        self.assertEqual(c.kind, "counter_underflow")
        self.assertEqual(c.params, {"W": 4, "LO": 3, "HI": 15, "SIGNED": 0})
        self.assertEqual(c.depth_hint, 16 // 3 + 2)
        self.assertIn("q - 3 never wraps below 0", c.desc)

    def test_constant_on_either_side_of_add(self):
        b = NB()
        _counter(b, step=2, const_on_a=True)
        (c,), _ = self.detect(b)
        self.assertEqual((c.kind, c.params["HI"]), ("counter_overflow", 13))

    def test_constant_minus_counter_is_not_a_counter(self):
        b = NB()
        _counter(b, op="$sub", const_on_a=True)
        self.assertEqual(self.detect(b), ([], {}))

    def test_signed_negative_add_is_a_decrement(self):
        b = NB()
        _counter(b, step=-1, signed=True)
        (c,), _ = self.detect(b)
        self.assertEqual(c.kind, "counter_underflow")
        self.assertEqual(c.params, {"W": 4, "LO": -7, "HI": 7, "SIGNED": 1})
        self.assertIn("signed q - 1 stays within -8..7", c.desc)

    def test_signed_subtract_of_a_negative_constant_is_an_increment(self):
        b = NB()
        _counter(b, step=-1, op="$sub", signed=True)
        (c,), _ = self.detect(b)
        self.assertEqual((c.kind, c.params), ("counter_overflow", {"W": 4, "LO": -8, "HI": 6, "SIGNED": 1}))
        self.assertIn("signed q + 1 stays within -8..7", c.desc)

    def test_one_bit_registers_are_not_counters(self):
        b = NB()
        _counter(b, w=1)                                                # a toggle, not a counter
        self.assertEqual(self.detect(b), ([], {}))

    def test_signed_increment(self):
        b = NB()
        _counter(b, step=2, signed=True)
        (c,), _ = self.detect(b)
        self.assertEqual((c.kind, c.params), ("counter_overflow", {"W": 4, "LO": -8, "HI": 5, "SIGNED": 1}))

    def test_signedness_needs_both_operands(self):
        b = NB()
        q = b.net("q", b.new(4))
        nxt = b.op("$add", params={"A_SIGNED": 1, "B_SIGNED": 0}, A=q, B=const(15, 4))
        b.ff(nxt, b.input("clk")[0], q=q)
        (c,), _ = self.detect(b)
        self.assertEqual((c.kind, c.params["SIGNED"], c.params["HI"]), ("counter_overflow", 0, 0))

    def test_degenerate_steps_are_ignored(self):
        b = NB()
        _counter(b, step=0)
        self.assertEqual(self.detect(b)[0], [])
        b = NB()
        q = b.net("q", b.new(4))
        b.ff(b.op("$add", w=4, A=q, B=const(16, 5)), b.input("clk")[0], q=q)   # step wider than q
        self.assertEqual(self.detect(b)[0], [])

    def test_zero_extended_counter_operand(self):
        b = NB()
        q = b.net("q", b.new(4))
        y = b.op("$add", w=5, A=q + ["0"], B=const(1, 5))
        b.ff(y[:4], b.input("clk")[0], q=q)
        (c,), _ = self.detect(b)
        self.assertEqual(c.params["HI"], 14)

    def test_two_bit_counter(self):
        b = NB()
        _counter(b, w=2)
        (c,), _ = self.detect(b)
        self.assertEqual(c.params, {"W": 2, "LO": 0, "HI": 2, "SIGNED": 0})

    def test_other_arithmetic_is_not_counting(self):
        for op in ("$mul", "$and", "$or", "$shl"):
            with self.subTest(op=op):
                b = NB()
                _counter(b, op=op, step=2)
                self.assertEqual(self.detect(b), ([], {}))
        b = NB()
        q = b.net("q", b.new(4))
        b.ff(b.op("$add", A=q, B=b.input("r", 4)), b.input("clk")[0], q=q)     # accumulator, not a counter
        self.assertEqual(self.detect(b), ([], {}))
        b = NB()
        q = b.net("q", b.new(4))
        y = b.op("$add", w=5, A=["0"] + q, B=const(2, 5))                # q*2 + 2: the counter is y[1:5]...
        b.ff(y[1:5], b.input("clk")[0], q=q)                             # ...an adder slice at an offset
        self.assertEqual(self.detect(b), ([], {}))

    def test_shapes_that_are_not_counters(self):
        b = NB()
        clk = b.input("clk")[0]
        one = b.net("one", b.new(1))
        b.ff(b.op("$add", A=one, B=["1"]), clk, q=one)                 # 1-bit toggle
        q = b.net("q", b.new(2))
        b.cell("ai", "$anyinit", {"D": b.op("$add", A=q, B=const(1, 2)), "Q": q}, {"WIDTH": 2})
        c = b.net("c", b.new(2))
        b.ff(b.op("$add", A=["0", c[1]], B=const(1, 2)), clk, q=["0", c[1]])   # constant Q bit
        b.cell("sr", "$sr", {"SET": b.new(2), "CLR": b.new(2), "Q": b.new(2)}, {"WIDTH": 2})
        self.assertEqual(self.detect(b), ([], {}))

    def test_dead_increment_is_skipped(self):
        b = NB()
        _counter(b, en="0")                                             # mux select tied off
        self.assertEqual(self.detect(b), ([], {}))
        b = NB()
        q = b.net("q", b.new(4))
        b.ff(b.op("$add", A=q, B=const(1, 4)), b.input("clk")[0], q=q, en="0")
        self.assertEqual(self.detect(b)[0], [])                         # register enable tied off

    def test_up_down_counter_has_both_checks(self):
        b = NB()
        clk, inc, dec = b.input("clk")[0], b.input("inc")[0], b.input("dec")[0]
        q = b.net("q", b.new(3))
        up = b.op("$add", A=q, B=const(1, 3))
        dn = b.op("$sub", A=q, B=const(1, 3))
        b.ff(b.mux(b.mux(q, dn, dec), up, inc), clk, q=q)
        checks, _ = self.detect(b)
        got = {c.kind: c.conds for c in checks}
        self.assertEqual(got, {"counter_overflow": [(inc, 1)], "counter_underflow": [(inc, 0), (dec, 1)]})

    def test_register_controls_join_the_path_conditions(self):
        b = NB()
        clk, en, rst = b.input("clk")[0], b.input("en")[0], b.input("rst")[0]
        q = b.net("q", b.new(4))
        b.ff(b.op("$add", A=q, B=const(1, 4)), clk, q=q, en=en, arst=rst)
        (c,), _ = self.detect(b)
        self.assertEqual(c.conds, [(en, 1), (rst, 0)])

    def test_waiver_attribute_and_source_fallback(self):
        b = NB()
        q = b.net("q", b.new(4), fvlint_waive="counter_overflow")
        b.ff(b.op("$add", A=q, B=const(1, 4)), b.input("clk")[0], q=q, attrs={"src": "cell.v:4.1-4.2"})
        (c,), _ = self.detect(b)
        self.assertEqual((c.waive_attr, c.src), ("counter_overflow", "cell.v:4"))

    def test_lemma_candidates(self):
        b = NB()
        clk = b.input("clk")[0]
        limit = b.input("limit", 4)
        wide = b.input("wide", 6)
        q = b.net("q", b.new(4))
        for k in (0, 3, 5, 9, 12, 15):                                  # 0 and 15 say nothing
            b.op("$eq", w=1, A=q, B=const(k, 4))
        b.op("$lt", w=1, name="c3", A=q, B=limit)                       # relational candidates...
        b.op("$lt", w=1, name="c2", A=q + ["0", "0"], B=limit[:2] + ["0"] * 4)   # (zero-extended)
        b.op("$lt", w=1, name="c1", A=q, B=limit[1:] + ["0"])           # ...at most two of them
        b.op("$gt", w=1, A=wide, B=q + ["0", "0"])                      # a live 6-bit operand does not fit
        b.op("$lt", w=1, A=q, B=[q[0]] + limit[1:])                     # reads q itself: not a bound
        b.ff(b.op("$add", A=q, B=const(1, 4)), clk, q=q, name="ff_q")
        _, lemmas = self.detect(b)
        got = [(lm.checker, lm.desc, lm.params, lm.bound) for lm in lemmas["ff_q"]]
        self.assertEqual(got, [
            ("fvl_range", "q <= 12", {"W": 4, "LO": 0, "HI": 12, "SIGNED": 0}, 12),
            ("fvl_range", "q <= 9", {"W": 4, "LO": 0, "HI": 9, "SIGNED": 0}, 9),
            ("fvl_range", "q <= 5", {"W": 4, "LO": 0, "HI": 5, "SIGNED": 0}, 5),
            ("fvl_rel", "q <= limit", {"W": 4, "SIGNED": 0}, 0),                     # whole signals first
            ("fvl_rel", "q <= {0,limit[3],limit[2],limit[1]}", {"W": 4, "SIGNED": 0}, 0),
        ])
        self.assertEqual(lemmas["ff_q"][3].ports, {"a": q, "b": limit})
        self.assertEqual(lemmas["ff_q"][0].ports, {"v": q})
        self.assertTrue(all(lm.owner == "ff_q" for lm in lemmas["ff_q"]))

    def test_lemma_choice_does_not_depend_on_cell_order_or_names(self):
        def build(order, names):
            b = NB()
            q = b.net("q", b.new(4))
            sigs = {n: b.input(n, 4) for n in ("alpha", "beta", "gamma")}
            for sig, cname in zip(order, names):
                b.op("$lt", w=1, name=cname, A=q, B=sigs[sig])
            b.ff(b.op("$add", A=q, B=const(1, 4)), b.input("clk")[0], q=q, name="ff_q")
            return [lm.desc for lm in detect_counters(b.build(), 3)[1]["ff_q"]]
        want = ["q <= alpha", "q <= beta"]
        self.assertEqual(build(["alpha", "beta", "gamma"], ["c1", "c2", "c3"]), want)
        self.assertEqual(build(["gamma", "beta", "alpha"], ["c1", "c2", "c3"]), want)
        self.assertEqual(build(["beta", "alpha", "gamma"], ["z", "y", "x"]), want)

    def test_not_equal_and_greater_compares_give_bounds(self):
        for op, k in (("$ne", 9), ("$ge", 9), ("$gt", 9), ("$le", 9), ("$eqx", 9), ("$nex", 9)):
            with self.subTest(op=op):
                b = NB()
                q = b.net("q", b.new(4))
                b.op(op, w=1, A=q, B=const(k, 4))
                b.ff(b.op("$add", A=q, B=const(1, 4)), b.input("clk")[0], q=q, name="ff_q")
                self.assertEqual([lm.desc for lm in self.detect(b)[1]["ff_q"]], ["q <= 9"])

    def test_bounds_just_below_the_maximum_are_kept(self):
        for signed, k, top in ((False, 14, "q <= 14"), (True, 6, "q <= 6")):
            with self.subTest(signed=signed):
                b = NB()
                q = b.net("q", b.new(4))
                b.op("$eq", w=1, A=q, B=const(k, 4))
                sgn = {"A_SIGNED": int(signed), "B_SIGNED": int(signed)}
                b.ff(b.op("$add", params=sgn, A=q, B=const(1, 4)), b.input("clk")[0], q=q, name="ff_q")
                self.assertEqual([lm.desc for lm in self.detect(b)[1]["ff_q"]], [top])

    def test_load_value_bounds_only_down_counters(self):
        def build(op):
            b = NB()
            clk, load = b.input("clk")[0], b.input("load")[0]
            q = b.net("q", b.new(4))
            b.ff(b.mux(b.op(op, A=q, B=const(1, 4)), const(12, 4), load), clk, q=q, name="ff_q")
            return detect_counters(b.build(), 3)[1]
        self.assertEqual([lm.desc for lm in build("$sub")["ff_q"]], ["q <= 12"])
        self.assertEqual(build("$add"), {})                             # an up counter passes its load value

    def test_signed_lemma_candidates_use_signed_order(self):
        b = NB()
        q = b.net("q", b.new(4))
        for k in (-3, 5, 7, -8):                                        # 7 = max, -8 = min: useless
            b.op("$eq", w=1, A=q, B=const(k & 15, 4))
        b.ff(b.op("$add", params={"A_SIGNED": 1, "B_SIGNED": 1}, A=q, B=const(1, 4)),
             b.input("clk")[0], q=q, name="ff_q")
        _, lemmas = self.detect(b)
        got = [(lm.desc, lm.params) for lm in lemmas["ff_q"]]
        self.assertEqual(got, [("q <= 5", {"W": 4, "LO": -8, "HI": 5, "SIGNED": 1}),
                               ("q <= -3", {"W": 4, "LO": -8, "HI": -3, "SIGNED": 1})])

    def test_compares_helper(self):
        b = NB()
        q = b.input("q", 3)
        r = b.input("r", 3)
        b.op("$eq", w=1, A=q, B=const(2, 3))
        b.op("$le", w=1, A=const(6, 3), B=q)                            # constant on the left
        b.op("$lt", w=1, A=q, B=r)
        b.op("$lt", w=1, A=r, B=q)                                      # duplicate operand: listed once
        b.op("$add", A=q, B=const(4, 3))                                # not a compare
        ks, others = _compares(b.build(), q)
        self.assertEqual((ks, others), ({2, 6}, [r]))


class CaseStatements(unittest.TestCase):
    def build(self, attrs, a=None, sels=3, sel_bits=None, use=True):
        b = NB()
        clk = b.input("clk")[0]
        s = sel_bits if sel_bits is not None else b.input("s", sels)
        a = a if a is not None else b.input("dflt", 2)
        y = b.pmux(a, [b.input(f"i{n}", 2) for n in range(len(s))], s, name="pm",
                   attrs=dict(attrs, src="c.v:5.1-9.8"))
        if use:
            b.ff(y, clk, q=b.net("gnt", b.new(2)), en=b.input("en")[0])
        return b.build(), s

    def test_parallel_case(self):
        nl, s = self.build({"parallel_case": PAR})
        (c,) = detect_case(nl)
        en = nl.ports["en"]["bits"][0]
        self.assertEqual((c.id, c.src, c.checker), ("parallel_case:gnt", "c.v:5", "fvl_onehot0"))
        self.assertEqual((c.params, c.ports, c.conds), ({"W": 3}, {"s": s}, [(en, 1)]))

    def test_full_case_without_default(self):
        nl, s = self.build({"parallel_case": PAR, "full_case": PAR}, a=["x", "x"])
        got = [(c.kind, c.checker, c.params, c.ports) for c in detect_case(nl)]
        self.assertEqual(got, [("parallel_case", "fvl_onehot0", {"W": 3}, {"s": s}),
                               ("full_case", "fvl_nonzero", {"W": 3}, {"s": s})])
        nl, _ = self.build({"parallel_case": PAR, "full_case": PAR})            # has a default value
        self.assertEqual([c.kind for c in detect_case(nl)], ["parallel_case"])

    def test_skipped_shapes(self):
        self.assertEqual(detect_case(self.build({})[0]), [])                    # plain priority case
        self.assertEqual(detect_case(self.build({"parallel_case": PAR}, sels=1)[0]), [])
        self.assertEqual(detect_case(self.build({"parallel_case": PAR}, sel_bits=["0", "1"])[0]), [])
        b = NB()                                                        # only $pmux cells are case statements
        b.cell("bm", "$bmux", {"A": ["x"] * 4, "S": b.input("s", 2), "Y": b.new(1)}, {"WIDTH": 1, "S_WIDTH": 2},
               {"parallel_case": PAR, "full_case": PAR})
        self.assertEqual(detect_case(b.build()), [])

    def test_unused_result_has_no_destination_but_is_checked(self):
        nl, _ = self.build({"parallel_case": PAR}, use=False)
        (c,) = detect_case(nl)
        self.assertEqual((c.target, c.conds), ("c.v:5", []))

    def test_dead_case_is_skipped(self):
        b = NB()
        y = b.pmux(b.input("d", 1), [b.input("i0"), b.input("i1")], b.input("s", 2), attrs={"parallel_case": PAR})
        b.mux(b.input("o"), y, "0")                                     # result never selected
        self.assertEqual(detect_case(b.build()), [])

    def test_same_destination_is_numbered_in_source_order(self):
        b = NB()
        gnt = b.net("gnt", b.new(1))
        s = b.input("s", 2)
        ys = []
        for line in (12, 9):
            ys.append(b.pmux(b.input(f"d{line}"), [b.input(f"a{line}"), b.input(f"b{line}")], s,
                             attrs={"parallel_case": PAR, "src": f"c.v:{line}.1-{line}.2"}))
        b.cell("m", "$mux", {"A": ys[0], "B": ys[1], "S": b.input("pick"), "Y": gnt})
        checks = detect_case(b.build())
        self.assertEqual(sorted((c.src, c.target) for c in checks), [("c.v:12", "gnt#1"), ("c.v:9", "gnt")])


class PartSelects(unittest.TestCase):
    def build(self, aw, yw, bw, signed=0, const_b=False, dead=False):
        b = NB()
        a = b.input("vec", aw)
        off = const(1, bw) if const_b else b.input("off", bw)
        y = b.net("lane", b.new(yw))
        b.cell("sx", "$shiftx", {"A": a, "B": off, "Y": y},
               {"A_WIDTH": aw, "B_WIDTH": bw, "Y_WIDTH": yw, "A_SIGNED": 0, "B_SIGNED": signed},
               attrs={"src": "p.v:3.1-3.2"})
        if dead:
            b.mux(b.input("o", yw), y, "0")
        return b.build(), off

    def test_index_range(self):
        nl, off = self.build(12, 4, 4)
        (c,) = detect_index(nl)
        self.assertEqual((c.id, c.src, c.checker), ("index_range:lane", "p.v:3", "fvl_range"))
        self.assertEqual((c.params, c.ports, c.conds), ({"W": 4, "LO": 0, "HI": 8, "SIGNED": 0}, {"v": off}, []))
        self.assertIn("0..8 (12-bit vector, 4-bit slice)", c.desc)

    def test_offsets_that_cannot_leave_the_vector_are_skipped(self):
        self.assertEqual(detect_index(self.build(12, 4, 3)[0]), [])     # 3-bit offset <= 7 < 8
        self.assertEqual(detect_index(self.build(11, 4, 3)[0]), [])     # offset <= 7 = last valid
        self.assertEqual(len(detect_index(self.build(10, 4, 3)[0])), 1)  # 7 > 6: can leave the vector
        self.assertEqual(detect_index(self.build(12, 4, 4, const_b=True)[0]), [])
        self.assertEqual(detect_index(self.build(3, 4, 4)[0]), [])      # slice wider than the vector
        self.assertEqual(detect_index(self.build(12, 4, 4, dead=True)[0]), [])

    def test_slice_as_wide_as_the_vector(self):
        (c,) = detect_index(self.build(4, 4, 2)[0])                     # only offset 0 is valid
        self.assertEqual(c.params["HI"], 0)

    def test_signed_offset_bound_fits_the_offset_width(self):
        # A 4-bit signed offset reaches -8..7.  The check is an unsigned
        # compare, so HI must stay below the sign bit or negative offsets
        # (8..15 unsigned) would pass.
        nl, _ = self.build(12, 4, 4, signed=1)                          # valid 0..8, offset max 7
        (c,) = detect_index(nl)
        self.assertEqual(c.params["HI"], 7)
        nl, _ = self.build(8, 4, 4, signed=1)                           # valid 0..4
        self.assertEqual(detect_index(nl)[0].params["HI"], 4)


class Memories(unittest.TestCase):
    def build(self, size=6, abits=3, offset=0, rd_addr=None, rd_en=None, wr_en=None, memid="\\mem",
              rd_ports=1, waive=None):
        b = NB()
        clk = b.input("clk")[0]
        width = 2
        ra = rd_addr if rd_addr is not None else b.input("ra", abits * rd_ports)
        we = wr_en if wr_en is not None else [b.input("we")[0]] * width
        rd = b.net("rd", b.new(width * rd_ports))
        params = {"SIZE": size, "ABITS": abits, "OFFSET": offset, "WIDTH": width, "RD_PORTS": rd_ports,
                  "WR_PORTS": 1, "RD_CLK_ENABLE": "0" * rd_ports, "WR_CLK_ENABLE": "1",
                  "WR_CLK_POLARITY": "1", "RD_CLK_POLARITY": "0" * rd_ports}
        if memid is not None:
            params["MEMID"] = memid
        attrs = {"src": "m.v:2.1-2.2"}
        if waive:
            attrs["fvlint_waive"] = waive
        conns = {"RD_ADDR": ra, "RD_DATA": rd, "RD_CLK": ["x"] * rd_ports,
                 "WR_ADDR": b.input("wa", abits), "WR_DATA": b.input("wd", width), "WR_EN": we, "WR_CLK": [clk]}
        if rd_en is not None:
            conns["RD_EN"] = rd_en
        b.cell("mem_cell", "$mem_v2", conns, params, attrs)
        return b.build(), ra, we

    def test_read_and_write_ports(self):
        nl, ra, we = self.build(rd_en=["1"], waive="mem_addr")
        rd, wr = detect_memory(nl)
        self.assertEqual((rd.id, wr.id), ("mem_addr:mem.rd0", "mem_addr:mem.wr0"))
        self.assertEqual(rd.params, {"W": 3, "LO": 0, "HI": 5, "SIGNED": 0})
        self.assertEqual(rd.ports, {"v": ra, "e": ["1"]})
        self.assertEqual(wr.ports, {"v": nl.ports["wa"]["bits"], "e": we})
        self.assertEqual((rd.src, rd.waive_attr, wr.waive_attr), ("m.v:2", "mem_addr", "mem_addr"))
        self.assertIn("read address of mem[0:5]", rd.desc)

    def test_full_power_of_two_memory_needs_no_check(self):
        self.assertEqual(detect_memory(self.build(size=8)[0]), [])

    def test_offset_memory(self):
        nl, _, _ = self.build(size=8, offset=4, abits=4)
        self.assertEqual({c.params["LO"] for c in detect_memory(nl)}, {4})
        self.assertEqual({c.params["HI"] for c in detect_memory(nl)}, {11})

    def test_disabled_and_constant_ports(self):
        self.assertEqual([c.id for c in detect_memory(self.build(rd_addr=const(1, 3))[0])], ["mem_addr:mem.wr0"])
        self.assertEqual([c.id for c in detect_memory(self.build(rd_en=["0"])[0])], ["mem_addr:mem.wr0"])
        self.assertEqual([c.id for c in detect_memory(self.build(wr_en=["0", "0"])[0])], ["mem_addr:mem.rd0"])

    def test_ports_are_sliced_per_port(self):
        b = NB()
        clk = b.input("clk")[0]
        ra, re = b.input("ra", 6), b.input("re", 2)
        rd = b.new(4)
        wa, we = b.input("wa", 6), b.input("we", 4)
        b.cell("m", "$mem_v2", {"RD_ADDR": ra, "RD_EN": re, "RD_DATA": rd, "RD_CLK": [clk, clk],
                                "WR_ADDR": wa, "WR_EN": we, "WR_DATA": b.input("wd", 4), "WR_CLK": [clk, clk]},
               {"SIZE": 6, "ABITS": 3, "WIDTH": 2, "RD_PORTS": 2, "WR_PORTS": 2, "MEMID": "\\m"})
        e0, e1 = b.input("e0")[0], b.input("e1")[0]
        b.ff(rd[0:2], clk, en=e0)                                       # each read port has its own consumer
        b.ff(rd[2:4], clk, en=e1)
        nl = b.build()
        got = {c.target: (c.ports, c.conds) for c in detect_memory(nl)}
        self.assertEqual(got, {"m.rd0": ({"v": ra[0:3], "e": re[0:1]}, [(e0, 1)]),
                               "m.rd1": ({"v": ra[3:6], "e": re[1:2]}, [(e1, 1)]),
                               "m.wr0": ({"v": wa[0:3], "e": we[0:2]}, []),
                               "m.wr1": ({"v": wa[3:6], "e": we[2:4]}, [])})

    def test_offset_defaults_to_zero(self):
        nl, _, _ = self.build()
        del nl.cells["mem_cell"]["parameters"]["OFFSET"]
        self.assertEqual({c.params["LO"] for c in detect_memory(nl)}, {0})

    def test_several_read_ports_and_missing_memid(self):
        nl, ra, _ = self.build(rd_ports=2, memid=None)
        checks = detect_memory(nl)
        self.assertEqual([c.id for c in checks], ["mem_addr:mem_cell.rd0", "mem_addr:mem_cell.rd1",
                                                  "mem_addr:mem_cell.wr0"])
        self.assertEqual([c.ports for c in checks[:2]], [{"v": ra[:3], "e": ["1"]}, {"v": ra[3:], "e": ["1"]}])
        self.assertEqual({c.checker for c in checks}, {"fvl_range"})                # no RD_EN: always enabled


class Dedupe(unittest.TestCase):
    def test_numeric_line_order(self):
        cs = [Check("k", "t", "a.v:10", ""), Check("k", "t", "a.v:9", ""), Check("k", "u", "a.v:1", ""),
              Check("k", "t", "?", "")]
        _dedupe(cs)
        self.assertEqual([c.target for c in cs], ["t#2", "t#1", "u", "t"])


class RealNetlists(unittest.TestCase):
    """Detectors on netlists Yosys produced from tests/unit/data/rtl."""

    def test_counters(self):
        nl = load_snapshot("snap_counters")
        checks, lemmas = detect_all(nl, 3)
        got = {c.id: (c.params, c.preset) for c in checks}
        u = {"W": 4, "LO": 0, "HI": 14, "SIGNED": 0}
        self.assertEqual(got, {
            "counter_overflow:free_q": (u, INFO),
            "counter_overflow:mod_q": (u, None),
            "counter_underflow:down_q": ({"W": 4, "LO": 1, "HI": 15, "SIGNED": 0}, None),
            "counter_overflow:acc": ({"W": 6, "LO": -32, "HI": 30, "SIGNED": 1}, None),
            "counter_underflow:acc": ({"W": 6, "LO": -31, "HI": 31, "SIGNED": 1}, None),
            "counter_overflow:rel_q": (u, None),
            "counter_overflow:u_sub.q": (u, None),
        })
        by_name = {nl.name_of(nl.ff_info(cell)["Q"]): sorted(lm.desc for lm in lms) for cell, lms in lemmas.items()}
        self.assertEqual(by_name, {"mod_q": ["mod_q <= 9"], "down_q": ["down_q <= 12"], "rel_q": ["rel_q <= lim"]})
        rst = nl.ports["rst"]["bits"][0]
        for c in checks:
            self.assertEqual(c.conds[0], (rst, 0), c.id)                # every update is under !rst
            self.assertEqual(len(c.anchors), 1)
            self.assertTrue(c.src.startswith("snap_counters.sv:"))

    def test_narrow_signed_index(self):
        got = {c.id: c.params for c in detect_index(load_snapshot("snap_index"))}
        self.assertEqual(got, {"index_range:ys": {"W": 4, "LO": 0, "HI": 7, "SIGNED": 0},    # -8 must fail
                               "index_range:yu": {"W": 4, "LO": 0, "HI": 11, "SIGNED": 0}})

    def test_bounds_fit_the_checker_width(self):
        # instance() encodes LO/HI in W bits; a bound that does not fit would
        # silently change meaning.  (The 0.2.0 signed-index false proof had a
        # bound that fit but was wrong; test_narrow_signed_index covers it.)
        for top in ("snap_counters", "snap_mux", "snap_reset", "snap_index", "snap_ops"):
            checks, lemmas = detect_all(load_snapshot(top), 3)
            ranges = [c.params for c in checks if c.checker == "fvl_range"]
            ranges += [lm.params for lms in lemmas.values() for lm in lms if lm.checker == "fvl_range"]
            for p in ranges:
                with self.subTest(top=top, params=p):
                    w = p["W"]
                    lo, hi = (-(1 << (w - 1)), (1 << (w - 1)) - 1) if p["SIGNED"] else (0, (1 << w) - 1)
                    self.assertTrue(lo <= p["LO"] <= p["HI"] <= hi)

    def test_case_index_memory(self):
        checks, lemmas = detect_all(load_snapshot("snap_mux"), 3)
        got = {c.id: c.params for c in checks}
        self.assertEqual(got, {
            "parallel_case:gnt": {"W": 3}, "parallel_case:y": {"W": 2}, "full_case:y": {"W": 2},
            "index_range:lane": {"W": 32, "LO": 0, "HI": 8, "SIGNED": 0},
            "mem_addr:mem.rd0": {"W": 3, "LO": 0, "HI": 5, "SIGNED": 0},
            "mem_addr:mem.wr0": {"W": 3, "LO": 0, "HI": 5, "SIGNED": 0},
        })
        self.assertEqual(lemmas, {})


if __name__ == "__main__":
    unittest.main()
