# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""fvlint.branches: conditions as Verilog, dead-branch detection and the
mapping of reachability verdicts."""

from __future__ import annotations

import unittest

from fvlint import branches
from fvlint.branches import condition, detect_branches, reach_verdicts, render_bit, render_cond, render_vec
from fvlint.checks import ERROR, FAIL, INFO, PROVEN, REACH, UNKNOWN, WARN, Check, Result
from fvlint.resets import discover

from .support import NB, const, load_snapshot


class Vectors(unittest.TestCase):
    def setUp(self):
        b = NB()
        self.n = b.input("n", 3)
        self.st = b.net("u.st", b.new(2))
        self.r = b.net("r", b.new(2))
        b.output("o", self.r + self.n)                  # a port that concatenates r and n
        self.hid = b.net("$h", b.new(2), hidden=True)
        self.tmp = b.net("u.$0\\q", b.new(2))            # a name Yosys made up
        self.nl = b.build()

    def test_constants_and_names(self):
        nl, n = self.nl, self.n
        self.assertEqual(render_vec(nl, const(5, 3)), "3'd5")
        self.assertEqual(render_vec(nl, ["1"]), "1'd1")
        self.assertEqual(render_vec(nl, n), "n")
        self.assertEqual(render_vec(nl, self.st), "u.st")
        self.assertEqual(render_vec(nl, self.r + n), "o")              # exactly a net
        self.assertEqual(render_vec(nl, n[:2]), "n[1:0]")
        self.assertEqual(render_vec(nl, n[1:]), "n[2:1]")
        self.assertEqual(render_vec(nl, n[1:2]), "n[1]")
        self.assertEqual(render_vec(nl, self.st[1:]), "u.st[1]")
        self.assertEqual(render_vec(nl, self.r[:1]), "r[0]")           # not o[0]: ports come last

    def test_zero_extension(self):
        nl, n = self.nl, self.n
        self.assertEqual(render_vec(nl, n + ["0", "0"]), "n")
        self.assertEqual(render_vec(nl, n[:1] + ["0"]), "n[0]")
        self.assertIsNone(render_vec(nl, n + ["0"], signed=True))      # sign matters: no stripping
        self.assertEqual(render_vec(nl, ["0", "0"]), "2'd0")

    def test_which_name(self):
        b = NB()
        x = b.new(2)
        b.net("pb", x)
        b.net("pa", x)                                    # a tie on everything but the name
        b.net("u.longname", x)                            # innermost wins over shorter
        y = b.new(2)
        b.net("sec", y, hidden=True)                      # hidden, though it looks written
        z = b.new(2)
        b.netnames["nokey"] = {"bits": z, "attributes": {}}   # no hide_name: visible
        w = b.new(3)
        b.net("pb2", w)
        b.net("pa2", w)
        v = b.new(2)
        b.net("aaa", v)
        b.net("zz", v)                                    # shorter wins over first by name
        nl = b.build()
        self.assertEqual(render_vec(nl, v[:1]), "zz[0]")
        self.assertEqual(render_vec(nl, x[:1]), "u.longname[0]")
        self.assertIsNone(render_vec(nl, y))
        self.assertIsNone(render_vec(nl, y[:1]))
        self.assertEqual(render_vec(nl, z), "nokey")
        self.assertEqual(render_vec(nl, z[1:]), "nokey[1]")
        self.assertEqual(render_vec(nl, w[1:]), "pa2[2:1]")

    def test_no_rendering(self):
        nl, n = self.nl, self.n
        for bits in ([], ["x"], [n[0], "1"], [n[0], n[2]], [n[1], n[0]], self.hid, self.tmp, [n[2], self.r[0]],
                     ["0", n[0]]):
            with self.subTest(bits=bits):
                self.assertIsNone(render_vec(nl, bits))


class Conditions(unittest.TestCase):
    def setUp(self):
        b = NB()
        self.b = b
        self.a, self.c = b.input("a")[0], b.input("c")[0]
        self.n = b.input("n", 3)
        self.s = b.input("s", 4)

    def r(self, bit, value=1):
        return render_cond(self.b.build(), bit, value)

    def test_logic(self):
        b, a, c, n = self.b, self.a, self.c, self.n
        self.assertEqual(self.r("1"), "1'b1")
        self.assertEqual(self.r("0"), "1'b0")
        self.assertIsNone(self.r("x"))
        self.assertEqual(self.r(a), "a")
        self.assertEqual(self.r(a, 0), "!a")
        self.assertEqual(self.r(b.op("$logic_not", A=[a])[0]), "!a")
        self.assertEqual(self.r(b.op("$logic_not", A=[a])[0], 0), "a")            # no double negation
        self.assertEqual(self.r(b.op("$not", A=[a])[0]), "!a")
        self.assertEqual(self.r(b.op("$logic_and", w=1, A=[a], B=[c])[0]), "(a && c)")
        self.assertEqual(self.r(b.op("$logic_and", w=1, A=[a], B=[c])[0], 0), "!(a && c)")
        self.assertEqual(self.r(b.op("$logic_or", w=1, A=n, B=[c])[0]), "((|n) || c)")
        self.assertEqual(self.r(b.op("$and", A=[a], B=[c])[0]), "(a && c)")
        self.assertEqual(self.r(b.op("$or", A=[a], B=[c])[0]), "(a || c)")
        self.assertEqual(self.r(b.op("$xor", A=[a], B=[c])[0]), "(a ^ c)")
        # A parameter that changes nothing (`x && 1'b1`) is left out; one that decides is kept.
        self.assertEqual(self.r(b.op("$logic_and", w=1, A=const(1, 32), B=[c])[0]), "c")
        self.assertEqual(self.r(b.op("$logic_and", w=1, A=[c], B=["1"])[0]), "c")
        self.assertEqual(self.r(b.op("$logic_or", w=1, A=[c], B=["0"])[0]), "c")
        self.assertEqual(self.r(b.op("$logic_or", w=1, A=["0"], B=[c])[0]), "c")
        self.assertEqual(self.r(b.op("$logic_and", w=1, A=const(0, 2), B=[c])[0]), "(1'b0 && c)")
        self.assertEqual(self.r(b.op("$logic_or", w=1, A=["1"], B=[c])[0]), "(1'b1 || c)")
        self.assertEqual(self.r(b.op("$logic_and", w=1, A=["1"], B=["1"])[0]), "(1'b1 && 1'b1)")

    def test_reductions(self):
        b, a, n = self.b, self.a, self.n
        self.assertEqual(self.r(b.op("$reduce_or", w=1, A=n)[0]), "(|n)")
        self.assertEqual(self.r(b.op("$reduce_bool", w=1, A=[a])[0]), "a")
        self.assertEqual(self.r(b.op("$reduce_and", w=1, A=n)[0]), "(&n)")
        self.assertEqual(self.r(b.op("$reduce_and", w=1, A=[a])[0]), "a")
        eqs = [b.op("$eq", w=1, A=n, B=const(k, 3))[0] for k in (1, 2)]
        self.assertEqual(self.r(b.op("$reduce_or", w=1, A=eqs)[0]), "((n == 3'd1) || (n == 3'd2))")
        hidden = b.net("$h", b.new(9), hidden=True)
        self.assertIsNone(self.r(b.op("$reduce_or", w=1, A=hidden)[0]))
        self.assertIsNone(self.r(b.op("$reduce_and", w=1, A=hidden[:2])[0]))
        self.assertIsNone(self.r(b.op("$logic_not", A=hidden[:2])[0]))
        self.assertIsNone(self.r(b.op("$logic_not", A=hidden[:1])[0]))

    def test_compares(self):
        b, n, s = self.b, self.n, self.s
        self.assertEqual(self.r(b.op("$eq", w=1, A=n, B=const(5, 3))[0]), "(n == 3'd5)")
        self.assertEqual(self.r(b.op("$eq", w=1, A=n, B=const(5, 3))[0], 0), "(n != 3'd5)")
        self.assertEqual(self.r(b.op("$eqx", w=1, A=n, B=const(5, 3))[0]), "(n == 3'd5)")
        self.assertEqual(self.r(b.op("$nex", w=1, A=n, B=const(5, 3))[0], 0), "(n == 3'd5)")
        self.assertEqual(self.r(b.op("$ne", w=1, A=n + ["0"], B=const(9, 4))[0]), "(n != 4'd9)")
        self.assertEqual(self.r(b.op("$ne", w=1, A=n, B=const(0, 3))[0]), "(n != 3'd0)")   # not `n`
        for op, sym, neg in (("$lt", "<", ">="), ("$le", "<=", ">"), ("$gt", ">", "<="), ("$ge", ">=", "<")):
            with self.subTest(op=op):
                self.assertEqual(self.r(b.op(op, w=1, A=n, B=const(2, 3))[0]), f"(n {sym} 3'd2)")
                self.assertEqual(self.r(b.op(op, w=1, A=n, B=const(2, 3))[0], 0), f"(n {neg} 3'd2)")
        # The constant goes to the right.
        for op, sym in (("$lt", ">"), ("$le", ">="), ("$gt", "<"), ("$ge", "<="), ("$eq", "=="), ("$ne", "!=")):
            with self.subTest(op=op):
                self.assertEqual(self.r(b.op(op, w=1, A=const(2, 3), B=n)[0]), f"(n {sym} 3'd2)")
        self.assertEqual(self.r(b.op("$lt", w=1, A=const(2, 3), B=const(3, 3))[0]), "(3'd2 < 3'd3)")
        signed = {"A_SIGNED": 1, "B_SIGNED": 1}
        self.assertEqual(self.r(b.op("$lt", w=1, A=s, B=const(3, 4), params=signed)[0]),
                         "($signed(s) < $signed(4'd3))")
        self.assertEqual(self.r(b.op("$lt", w=1, A=s, B=const(3, 4), params={"A_SIGNED": 1})[0]), "(s < 4'd3)")
        self.assertIsNone(self.r(b.op("$lt", w=1, A=n + [n[2]], B=const(3, 4), params=signed)[0]))
        self.assertIsNone(self.r(b.op("$eq", w=1, A=n, B=["x", "0", "0"])[0]))
        hidden = b.net("$h", b.new(2), hidden=True)
        self.assertIsNone(self.r(b.op("$eq", w=1, A=hidden, B=const(1, 2))[0]))
        self.assertIsNone(self.r(b.op("$eq", w=1, A=const(1, 2), B=hidden)[0]))

    def test_case_on_one_bit(self):
        # case (1'b1): an item is a compare of the constant with a condition.
        b, a = self.b, self.a
        self.assertEqual(self.r(b.op("$eq", w=1, A=["1"], B=[a])[0]), "a")
        self.assertEqual(self.r(b.op("$eq", w=1, A=["1"], B=[a])[0], 0), "!a")
        self.assertEqual(self.r(b.op("$eq", w=1, A=["0"], B=[a])[0]), "!a")
        self.assertEqual(self.r(b.op("$ne", w=1, A=[a], B=["0"])[0]), "a")
        notc = b.op("$logic_not", A=[self.c])[0]
        self.assertEqual(self.r(b.op("$eq", w=1, A=["1"], B=[notc])[0]), "!c")
        self.assertEqual(self.r(b.op("$eq", w=1, A=["1"], B=[notc])[0], 0), "c")
        signed = {"A_SIGNED": 1, "B_SIGNED": 1}
        self.assertEqual(self.r(b.op("$eq", w=1, A=["1"], B=[a], params=signed)[0]), "($signed(a) == $signed(1'd1))")
        self.assertEqual(self.r(b.op("$eq", w=1, A=self.n, B=const(1, 3))[0]), "(n == 3'd1)")

    def test_vector_logic_not(self):
        b, n = self.b, self.n
        z = b.op("$logic_not", w=1, A=n)[0]                # slang's `n == 0`
        self.assertEqual(self.r(z), "(n == 3'd0)")
        self.assertEqual(self.r(z, 0), "(n != 3'd0)")
        z2 = b.op("$logic_not", w=1, A=n[:2])[0]
        self.assertEqual(self.r(z2), "(n[1:0] == 2'd0)")
        self.assertEqual(self.r(z2, 0), "(n[1:0] != 2'd0)")

    def test_zero_extended_one_bit_operand(self):
        b, a = self.b, self.a
        self.assertEqual(self.r(b.op("$eq", w=1, A=[a, "0"], B=const(1, 2))[0]), "a")
        self.assertEqual(self.r(b.op("$eq", w=1, A=[a, "0", "0"], B=const(0, 3))[0]), "!a")

    def test_signedness_defaults_to_unsigned(self):
        b, n = self.b, self.n
        y = b.new(1)
        b.cell(None, "$lt", {"A": n, "B": const(2, 3), "Y": y}, {"Y_WIDTH": 1})
        self.assertEqual(self.r(y[0]), "(n < 3'd2)")
        for one in ("A_SIGNED", "B_SIGNED"):                 # signed only when both operands are
            y = b.new(1)
            b.cell(None, "$lt", {"A": n, "B": const(2, 3), "Y": y}, {"Y_WIDTH": 1, one: 1})
            self.assertEqual(self.r(y[0]), "(n < 3'd2)")

    def test_items_for_up_to_eight_values(self):
        b, n, s = self.b, self.n, self.s
        eqs = [b.op("$eq", w=1, A=n, B=const(k, 3))[0] for k in range(8)]
        self.assertEqual(self.r(b.op("$reduce_or", w=1, A=eqs)[0]),
                         "(" + " || ".join(f"(n == 3'd{k})" for k in range(8)) + ")")
        eqs = [b.op("$eq", w=1, A=s, B=const(k, 4))[0] for k in range(9)]
        self.assertIsNone(self.r(b.op("$reduce_or", w=1, A=eqs)[0]))

    def test_depth_limit_through_every_operator(self):
        # Eight cells deep is rendered, nine is not, whichever cells they are.
        def chain(step, k):
            b = NB()
            a, c = b.input("a")[0], b.input("c")[0]
            x = a
            for _ in range(k):
                x = step(b, x, c)
            return render_cond(b.build(), x, 1)
        steps = {
            "not": lambda b, x, c: b.op("$not", A=[x])[0],
            "logic_not": lambda b, x, c: b.op("$logic_not", A=[x])[0],
            "and A": lambda b, x, c: b.op("$logic_and", w=1, A=[x], B=[c])[0],
            "and B": lambda b, x, c: b.op("$logic_and", w=1, A=[c], B=[x])[0],
            "reduce_or": lambda b, x, c: b.op("$reduce_or", w=1, A=[x])[0],
            "reduce_or parts": lambda b, x, c: b.op("$reduce_or", w=1, A=[x, c])[0],
            "reduce_and": lambda b, x, c: b.op("$reduce_and", w=1, A=[x])[0],
            "compare": lambda b, x, c: b.op("$eq", w=1, A=["1"], B=[x])[0],
        }
        for name, step in steps.items():
            with self.subTest(name):
                self.assertIsNotNone(chain(step, 8))
                self.assertIsNone(chain(step, 9))

    def test_unsupported(self):
        b, a, c, n = self.b, self.a, self.c, self.n
        q = b.ff([a], b.input("clk")[0])[0]                  # a register without a name
        self.assertIsNone(self.r(q))
        self.assertIsNone(self.r(b.op("$add", A=n, B=const(1, 3))[0]))
        self.assertIsNone(self.r(b.op("$and", A=n, B=n)[1]))                     # not bit 0
        self.assertIsNone(self.r(b.op("$and", A=n[:2], B=n[1:])[0]))             # a vector $and
        self.assertIsNone(self.r(b.op("$logic_and", w=1, A=[q], B=[c])[0]))
        self.assertIsNone(self.r(b.op("$logic_or", w=1, A=[c], B=[q])[0]))
        self.assertIsNone(self.r(b.op("$logic_not", A=[q])[0]))
        self.assertIsNone(self.r(b.op("$reduce_or", w=1, A=[q, q])[0]))
        self.assertIsNone(self.r(b.op("$reduce_or", w=1, A=[q] * 9)[0]))
        self.assertIsNone(render_bit(b.build(), n[0], depth=9))
        deep = [a]
        for _ in range(12):
            deep = b.op("$not", A=deep)
        self.assertIsNone(self.r(deep[0]))
        shallow = [a]
        for _ in range(7):
            shallow = b.op("$not", A=shallow)
        self.assertEqual(self.r(shallow[0]), "!" * 7 + "a")

    def test_whole_condition(self):
        b, a, c, n = self.b, self.a, self.c, self.n
        eq = b.op("$eq", w=1, A=n, B=const(5, 3))[0]
        eq2 = b.op("$eq", w=1, A=n, B=const(5, 3))[0]                         # the same compare twice
        both = b.op("$logic_and", w=1, A=[a], B=[c])[0]
        nl = b.build()
        self.assertEqual(condition(nl, [(eq, 1)]), "n == 3'd5")
        self.assertEqual(condition(nl, [(eq, 0)]), "n != 3'd5")
        self.assertEqual(condition(nl, [(a, 1)]), "a")
        self.assertEqual(condition(nl, [(both, 0)]), "!(a && c)")
        self.assertEqual(condition(nl, [(both, 1)]), "a && c")
        self.assertEqual(condition(nl, [(eq, 1), (a, 0)]), "(n == 3'd5) && !a")
        self.assertEqual(condition(nl, [(eq, 1), (eq2, 1), (a, 0)]), "(n == 3'd5) && !a")
        self.assertEqual(condition(nl, [(eq, 1), (eq2, 1)]), "n == 3'd5")
        self.assertIsNone(condition(nl, []))
        self.assertIsNone(condition(nl, [(eq, 1), ("x", 1)]))
        wide = b.net("w" * 200, b.new(1))
        wider = b.net("v" * 201, b.new(1))
        nl = b.build()
        self.assertIsNone(condition(nl, [(wide[0], 1), (eq, 1)]))                # too long
        self.assertEqual(condition(nl, [(wide[0], 1)]), "w" * 200)
        self.assertIsNone(condition(nl, [(wider[0], 1)]))
        self.assertEqual(branches.MAX_EXPR, 200)
        self.assertEqual(len(condition(nl, [(a, 1)] * 1)), 1)

    def test_targets(self):
        t = branches._target
        self.assertEqual(t("(n == 3'd5)"), "n==3'd5")
        self.assertEqual(t("(a && c) || (b)"), "(a&&c)||(b)")
        self.assertEqual(t("!(a && c)"), "!(a&&c)")
        self.assertEqual(t("a"), "a")
        self.assertIsNone(t(None))
        self.assertIsNone(t("x" * 61))
        self.assertEqual(t("x" * 60), "x" * 60)

    def test_atomic(self):
        at = branches._atomic
        for x in ("a", "u.st", "n[3]", "n[3:1]", "(a && c)", "((a) || (c))", "\\esc$x"):
            with self.subTest(x=x):
                self.assertTrue(at(x))
        for x in ("a && c", "(a) && (c)", "!a", "(a", "a)", "n[x]", "(a)b", "(a))"):
            with self.subTest(x=x):
                self.assertFalse(at(x))


class Checker(unittest.TestCase):
    def test_the_reachability_checker_exists(self):
        from fvlint.sby import CHECKERS_V
        self.assertIn(f"module {REACH} #(", CHECKERS_V)


class OnASnapshot(unittest.TestCase):
    """The detector on what Yosys makes of if/else, case and ?: (data/rtl/snap_branches.sv)."""

    def test_arms(self):
        nl = load_snapshot("snap_branches")
        resets = discover(nl, None, False, None, False)
        self.assertEqual(resets.primary.name, "rst_n")
        checks = detect_branches(nl, dict(resets.inactive_conds()))
        got = [(c.id, c.src, c.condition) for c in checks]
        self.assertEqual(got, [
            ("dead_branch:!go", "snap_branches.sv:13", "!go"),
            ("dead_branch:go", "snap_branches.sv:13", "go"),
            ("dead_branch:n!=3'd5", "snap_branches.sv:13", "(n != 3'd5) && go"),
            ("dead_branch:n==3'd5", "snap_branches.sv:13", "(n == 3'd5) && go"),
            ("dead_branch:n!=3'd7", "snap_branches.sv:18", "n != 3'd7"),
            ("dead_branch:n==3'd7", "snap_branches.sv:18", "n == 3'd7"),
            ("dead_branch:!(a&&b)", "snap_branches.sv:19", "!(a && b) && (n != 3'd7)"),
            ("dead_branch:a&&b", "snap_branches.sv:19", "(a && b) && (n != 3'd7)"),
            # The arm that contradicts its path: two separate cells, so it is
            # checked (and proven dead) rather than dropped.
            ("dead_branch:!(a&&b)#1", "snap_branches.sv:20", "!(a && b) && (a && b) && (n != 3'd7)"),
            ("dead_branch:a&&b#1", "snap_branches.sv:20", "(a && b) && (n != 3'd7)"),
            ("dead_branch:op==2'd0", "snap_branches.sv:25", "op == 2'd0"),
            ("dead_branch:(op==2'd1)||(op==2'd2)", "snap_branches.sv:26", "(op == 2'd1) || (op == 2'd2)"),
            ("dead_branch:!a", "snap_branches.sv:32", "!a"),
            ("dead_branch:a", "snap_branches.sv:32", "a"),
        ])
        for c in checks:
            self.assertEqual((c.kind, c.checker, c.desc, c.params, c.ports),
                             ("dead_branch", REACH, branches.DESC, {}, {}))
            self.assertTrue(c.reach)
            self.assertNotIn((resets.primary.bit, 0), c.conds)                    # never under reset
        # No reset: the reset muxes are branches too (rst_n is just an input then).
        ids = {c.id for c in detect_branches(nl, {})}
        self.assertIn("dead_branch:!rst_n", ids)
        self.assertIn("dead_branch:rst_n", ids)


class Shapes(unittest.TestCase):
    def setUp(self):
        b = NB()
        self.b = b
        self.clk, self.rst, self.a, self.c = (b.input(n)[0] for n in ("clk", "rst", "a", "c"))
        self.d = b.input("d", 2)
        self.st = b.net("st", b.new(2))

    def ff(self, d, name, **attrs):
        q = self.b.net(name, self.b.new(len(d)), **attrs)
        self.b.ff(d, self.clk, q=q)
        return q

    def ids(self, inactive=None, **kw):
        return [c.id for c in detect_branches(self.b.build(**kw), inactive if inactive is not None else {})]

    def test_if_else(self):
        b = self.b
        self.ff(b.mux(self.d, const(1, 2), self.a, attrs={"src": "t.v:7.3-7.9"}), "q")
        checks = detect_branches(b.build(), {})
        self.assertEqual([(c.id, c.conds, c.src) for c in checks],
                         [("dead_branch:!a", [(self.a, 0)], "t.v:7"), ("dead_branch:a", [(self.a, 1)], "t.v:7")])

    def test_reset_muxes_and_arms_under_reset(self):
        b, rst = self.b, self.rst
        inner = b.mux(self.d, const(3, 2), self.a)                 # inside the reset branch
        self.ff(b.mux(self.d, inner, rst), "q")
        nrst = b.op("$logic_not", A=[rst])[0]
        self.ff(b.mux(self.d, const(0, 2), nrst), "p")             # `if (!rst)`: constant once inactive
        self.assertEqual(self.ids({rst: 0}), [])
        # Without a reset (--no-reset) rst is an input like any other.
        # (`if (rst)` and `if (!rst)` read the same: one branch each way.)
        self.assertEqual(self.ids(), ["dead_branch:!a", "dead_branch:!rst", "dead_branch:a", "dead_branch:rst"])

    def test_left_out(self):
        b = self.b
        self.ff(b.mux(self.d, ["x", "x"], self.a), "q")            # a placeholder arm (slang)
        self.ff(b.mux(self.d, const(1, 2), "1"), "p")              # a constant select
        eq = b.op("$logic_and", w=1, A=const(0, 1), B=[self.c])[0]
        self.ff(b.mux(self.d, const(1, 2), eq), "r")               # a select that is constant (a parameter)
        self.assertEqual(self.ids(), ["dead_branch:!a"])
        never = b.mux(self.d, const(2, 2), self.c)
        self.ff(b.mux(never, self.d, "1"), "s")                    # its result is never selected
        self.assertEqual(self.ids(), ["dead_branch:!a"])
        b.mux(self.d, const(2, 2), self.c)          # nothing reads it: an output port's `assign y = c ? ...`
        self.assertEqual(self.ids(), ["dead_branch:!a", "dead_branch:!c", "dead_branch:c"])

    def test_arms_that_contradict_their_path(self):
        b, a = self.b, self.a
        inner = b.mux(self.d, const(1, 2), a)                      # if (a) if (a) ...: its else can't happen
        self.ff(b.mux(self.d, inner, a), "q")
        self.assertEqual([(c.id, c.conds) for c in detect_branches(b.build(), {})],
                         [("dead_branch:!a", [(a, 0)]), ("dead_branch:a", [(a, 1)])])

    def test_placeholder_items(self):
        b, st = self.b, self.st
        eqs = [b.op("$eq", w=1, A=st, B=const(k, 2))[0] for k in (0, 1, 2)]
        self.ff(b.pmux(self.d, [const(1, 2), ["x", "x"], const(3, 2)], eqs), "q")
        self.assertEqual(sorted(self.ids()), ["dead_branch:st==2'd0", "dead_branch:st==2'd2"])

    def test_pmux_items_and_default(self):
        b, st = self.b, self.st
        eqs = [b.op("$eq", w=1, A=st, B=const(k, 2))[0] for k in (0, 1)]
        y = b.pmux(self.d, [const(1, 2), const(2, 2)], eqs)
        self.ff(y, "q")
        self.assertEqual(sorted(self.ids()), ["dead_branch:st==2'd0", "dead_branch:st==2'd1"])

    def test_case_item_source_is_the_item(self):
        b, st = self.b, self.st
        eqs = [b.op("$eq", w=1, A=st, B=const(k, 2), name=f"$procmux$9_CMP{k}",
                    attrs={"src": f"t.v:{20 + k}.1-20.2"})[0] for k in (0, 1)]
        eqs.append(b.op("$eq", w=1, A=st, B=const(2, 2), attrs={"src": "t.v:30.1-30.2"})[0])
        self.ff(b.pmux(self.d, [const(1, 2), const(2, 2), const(3, 2)], eqs, attrs={"src": "t.v:9.1-9.2"}), "q")
        self.ff(b.mux(self.d, const(1, 2), eqs[0], attrs={"src": "t.v:40.1-40.2"}), "p")
        srcs = {c.id: c.src for c in detect_branches(b.build(), {})}
        # Item 0 is also the `then` arm of the mux at line 40: one check, at the earlier line.
        self.assertEqual(srcs, {"dead_branch:st==2'd0": "t.v:20", "dead_branch:st==2'd1": "t.v:21",
                                "dead_branch:st==2'd2": "t.v:9", "dead_branch:st!=2'd0": "t.v:40"})

    def test_identical_arms_are_one_check(self):
        # An if that assigns two registers: two muxes, one arm each way.  The
        # earliest source line names it; any destination's waiver counts.
        b, a = self.b, self.a
        self.ff(b.mux(self.d, const(1, 2), a, attrs={"src": "t.v:9.1-9.2"}), "q", fvlint_waive="dead_branch")
        self.ff(b.mux(self.d, const(2, 2), a, attrs={"src": "t.v:4.1-4.2"}), "p")
        self.ff(b.mux(self.d, const(3, 2), a, attrs={"src": "t.v:12.1-12.2"}), "r")
        checks = detect_branches(b.build(), {})
        self.assertEqual([(c.id, c.src, c.waive_attr) for c in checks],
                         [("dead_branch:!a", "t.v:4", "dead_branch"), ("dead_branch:a", "t.v:4", "dead_branch")])

    def test_a_branch_is_taken_if_any_of_its_muxes_takes_it(self):
        # One `if (a) ... else ...` assigns q (stored only while c) and the
        # output y (used always): the else is taken whenever !a, c or not.
        b, a, c = self.b, self.a, self.c
        src = {"src": "t.v:7.7-7.8|t.v:7.3-9.9"}
        q = self.b.net("q", b.new(2))
        b.ff(b.mux(q, b.mux(self.d, const(1, 2), a, attrs=src), c), self.clk, q=q)
        b.output("y", b.mux(self.d[::-1], const(2, 2), a, attrs=src))
        checks = [x for x in detect_branches(b.build(), {}) if x.id.endswith("a")]
        self.assertEqual([(x.id, x.conds) for x in checks], [("dead_branch:!a", [(a, 0)]), ("dead_branch:a", [(a, 1)])])
        # Without the output, the arm needs c.
        b2 = NB()
        a2, c2, clk = b2.input("a")[0], b2.input("c")[0], b2.input("clk")[0]
        q2 = b2.net("q", b2.new(1))
        b2.ff(b2.mux(q2, b2.mux([c2], ["1"], a2, attrs=src), c2), clk, q=q2)
        self.assertEqual([x.conds for x in detect_branches(b2.build(), {}) if x.id.endswith("a")],
                         [[(a2, 0), (c2, 1)], [(a2, 1), (c2, 1)]])

    def test_every_mux_of_a_case_statement_has_its_own_compares(self):
        # One item, two signals: two pmuxes, each with its own compare of st.
        b, st = self.b, self.st
        src = {"src": "t.v:12.7-12.10|t.v:10.3-20.10"}
        for name in ("p", "q"):
            eq = b.op("$eq", w=1, A=st, B=const(1, 2), name=f"$procmux${name}_CMP0", attrs=src)
            self.ff(b.pmux(self.d, [const(1, 2)], eq), name)
        checks = detect_branches(b.build(), {})
        self.assertEqual([(c.id, c.src) for c in checks], [("dead_branch:st==2'd1", "t.v:12")])

    def test_case_fallthrough(self):
        # Yosys turns the last item of a case on one bit into a mux: its
        # other input is "no item matches", the implicit default.
        b, a = self.b, self.a
        self.ff(b.mux(self.d, const(1, 2), a, attrs={"src": "t.v:14.8-14.8|t.v:9.4-20.11"}), "q")
        self.assertEqual(self.ids(), ["dead_branch:a"])
        for src in ("t.v:6.11-6.17|t.v:6.7-7.38", "t.v:6.11-6.17", "", "junk|more", "t.v:6.1-6.2|junk"):
            with self.subTest(src=src):
                self.assertFalse(_fallthrough(src))
        self.assertTrue(_fallthrough("t.v:14.8-14.8|t.v:9.4-20.11"))

    def test_waiver_attribute_of_the_destination(self):
        b = self.b
        self.ff(b.mux(self.d, const(1, 2), self.a), "q", fvlint_waive="all")
        self.assertEqual({c.waive_attr for c in detect_branches(b.build(), {})}, {"all"})
        self.ff(b.mux(self.d, const(1, 2), self.c), "p")
        self.assertEqual({c.id: c.waive_attr for c in detect_branches(b.build(), {})}["dead_branch:c"], None)

    def test_unnamed_conditions(self):
        b = self.b
        q = b.ff([self.a], self.clk)                                # a register without a name
        self.ff(b.mux(self.d, const(1, 2), q[0], attrs={"src": "t.v:3.1-3.2"}), "x")
        eqs = [b.op("$eq", w=1, A=[q[0], self.c], B=const(k, 2))[0] for k in (1, 2)]
        self.ff(b.pmux(self.d, [const(1, 2), const(2, 2)], eqs, attrs={"src": "t.v:5.1-5.2"}), "y")
        checks = detect_branches(b.build(), {})
        self.assertEqual(sorted((c.id, c.condition) for c in checks),
                         [("dead_branch:x:else", None), ("dead_branch:x:then", None),
                          ("dead_branch:y:item", None), ("dead_branch:y:item#1", None)])

    def test_same_condition_in_different_places(self):
        # Told apart by the FSM state they sit in, else by number.
        b, st, a = self.b, self.st, self.a
        for k, line in ((1, 30), (0, 20)):
            eq = b.op("$eq", w=1, A=st, B=const(k, 2))[0]
            inner = b.mux(self.d, const(1, 2), a, attrs={"src": f"t.v:{line}.1-{line}.2"})
            self.ff(b.mux(self.d, inner, eq), f"q{k}")
        ids = [c.id for c in detect_branches(b.build(), {}) if "@" in c.id]
        self.assertEqual(sorted(ids), ["dead_branch:!a@st=2'b00", "dead_branch:!a@st=2'b01",
                                       "dead_branch:a@st=2'b00", "dead_branch:a@st=2'b01"])
        # One of its name: no state in it.
        eq = b.op("$eq", w=1, A=st, B=const(2, 2))[0]
        self.ff(b.mux(self.d, b.mux(self.d, const(1, 2), self.c), eq), "q2")
        self.assertIn("dead_branch:c", self.ids())
        b2 = NB()
        a2, c2, clk = b2.input("a")[0], b2.input("c")[0], b2.input("clk")[0]
        d2 = b2.input("d", 2)
        for k, line in ((0, 30), (1, 20)):
            inner = b2.mux(d2, const(1, 2), a2, attrs={"src": f"t.v:{line}.1-{line}.2"})
            b2.ff(b2.mux(d2, inner, c2) if k else b2.mux(inner, d2, c2), clk, q=b2.net(f"q{k}", b2.new(2)))
        got = {c.id: c.src for c in detect_branches(b2.build(), {}) if c.id.startswith("dead_branch:a")}
        self.assertEqual(got, {"dead_branch:a": "t.v:20", "dead_branch:a#1": "t.v:30"})

    def test_pinned_path_conditions(self):
        # A path condition the inactive reset decides: dropped when it holds,
        # the arm left out when it can't.
        b, rst, a = self.b, self.rst, self.a
        nrst = b.op("$logic_not", A=[rst])[0]
        self.ff(b.mux(self.d, b.mux(self.d, const(1, 2), a), nrst), "q")      # if (!rst) if (a)
        checks = detect_branches(b.build(), {rst: 0})
        self.assertEqual([(c.id, c.conds) for c in checks],
                         [("dead_branch:!a", [(a, 0)]), ("dead_branch:a", [(a, 1)])])
        self.assertEqual(detect_branches(b.build(), {rst: 1}), [])


def _fallthrough(src):
    b = NB()
    b.mux([b.input("d")[0]], ["1"], b.input("a")[0], name="m", attrs={"src": src} if src else None)
    return branches._case_fallthrough(b.build(), "m")


class Verdicts(unittest.TestCase):
    def r(self, status, checker=REACH, condition="n == 3'd7", engine="PDR", detail="proven by PDR on cone 0"):
        c = Check("dead_branch", "n==3'd7", "a.v:3", branches.DESC, checker=checker, condition=condition)
        return Result(check=c, status=status, detail=detail, engine=engine, step=4)

    def test_mapping(self):
        live, replayed = self.r(FAIL, engine="BMC"), self.r(FAIL)
        dead, anon = self.r(PROVEN), self.r(PROVEN, condition=None)
        open_, err = self.r(UNKNOWN, detail="timeout on cone 1"), self.r(ERROR, detail="e")
        info = self.r(INFO, detail="i")
        other = self.r(FAIL, checker="fvl_range", detail="cex")
        reach_verdicts([live, replayed, dead, anon, open_, err, info, other])
        self.assertEqual((live.status, live.detail),
                         (PROVEN, "live: taken at step 4 (found by a bounded search on the full cone; the trace is "
                                  "the witness)"))
        self.assertEqual((replayed.status, replayed.detail),
                         (PROVEN, "live: taken at step 4 (confirmed on the full cone; the trace is the witness)"))
        self.assertEqual((dead.status, dead.detail),
                         (WARN, "dead: `n == 3'd7` never holds after reset; proven by PDR on cone 0"))
        self.assertEqual(anon.detail, "dead: the branch condition never holds after reset; proven by PDR on cone 0")
        self.assertEqual((open_.status, open_.detail), (UNKNOWN, "neither taken nor proven dead: timeout on cone 1"))
        self.assertEqual([(x.status, x.detail) for x in (err, info, other)],
                         [(ERROR, "e"), (INFO, "i"), (FAIL, "cex")])


if __name__ == "__main__":
    unittest.main()
