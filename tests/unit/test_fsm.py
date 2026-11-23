# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""fvlint.fsm: decoding Yosys $fsm cells and the reachability analysis."""

from __future__ import annotations

import json
import random
import unittest

from fvlint.checks import FAIL, INFO, WARN, Check
from fvlint.fsm import _bits_lsb, _Eval, _sccs, analyse_fsms, dead_in_unreachable_states, read_fsm_cells
from fvlint.resets import discover

from .support import NB, TempDirCase, load_snapshot, snapshot


def fsm_cell(states, trans, reset=0, ctrl_in=(), ctrl_out_w=0, name="\\st", state_bits=None, arst=None):
    """A $fsm cell as fsm_extract writes it.

    states: MSB-first codes, index = state number.  trans: (from, ctrl_in
    LSB-first string, to).  Parameters are MSB-first binary strings, like
    Yosys' JSON backend writes them."""
    sb = state_bits or len(states[0])
    lg = max(1, (len(states) - 1).bit_length())
    ci = len(ctrl_in)

    def lsb(v, w):
        return "".join("1" if (v >> i) & 1 else "0" for i in range(w))
    table = ""
    for frm, cin, to in trans:                       # LSB-first: ctrl_out, state_out, ctrl_in, state_in
        table += "0" * ctrl_out_w + lsb(to, lg) + cin + lsb(frm, lg)
    st_lsb = "".join(code[::-1] for code in states)
    p = {"STATE_BITS": sb, "STATE_NUM": len(states), "STATE_NUM_LOG2": lg, "CTRL_IN_WIDTH": ci,
         "CTRL_OUT_WIDTH": ctrl_out_w, "TRANS_NUM": len(trans), "STATE_TABLE": st_lsb[::-1],
         "TRANS_TABLE": table[::-1], "NAME": name}
    if reset is not None:
        p["STATE_RST"] = format(reset, "032b") if isinstance(reset, int) else reset
    conns = {"CTRL_IN": list(ctrl_in), "CTRL_OUT": []}
    if arst is not None:
        conns["ARST"] = list(arst)
    return {"type": "$fsm", "parameters": p, "attributes": {}, "port_directions": {}, "connections": conns}


class Decoding(TempDirCase):
    def write_fsm(self, *cells, nets=None):
        mod = {"ports": {}, "cells": {f"$fsm{i}": c for i, c in enumerate(cells)},
               "netnames": nets or {}}
        return self.write_json("fsm.json", {"modules": {"t": mod}})

    def test_bits_lsb(self):
        self.assertEqual(_bits_lsb("1100"), "0011")
        self.assertEqual(_bits_lsb(6)[:4], "0110")
        self.assertEqual(len(_bits_lsb(6)), 32)

    def test_states_transitions_and_reset(self):
        p = self.write_fsm(fsm_cell(["00", "01", "11"], [(0, "", 1), (1, "", 2), (2, "", 2)], reset=0))
        (f,) = read_fsm_cells(p, "t")
        self.assertEqual((f["name"], f["states"], f["state_rst"]), ("st", ["00", "01", "11"], 0))
        self.assertEqual((f["trans"], f["reset_edges"], f["reset_targets"]), ([(0, 1), (1, 2), (2, 2)], 0, set()))

    def test_control_outputs_are_skipped_over(self):
        p = self.write_fsm(fsm_cell(["0", "1"], [(0, "1", 1), (1, "0", 0)], ctrl_in=[7], ctrl_out_w=3))
        self.assertEqual(read_fsm_cells(p, "t")[0]["trans"], [(0, 1), (1, 0)])

    def test_reset_state_variants(self):
        for rst, want in ((1, 1), (2, None), (5, None), ("x" * 32, None), (None, None)):
            with self.subTest(rst=rst):
                p = self.write_fsm(fsm_cell(["0", "1"], [(0, "", 1)], reset=rst))
                self.assertEqual(read_fsm_cells(p, "t")[0]["state_rst"], want)

    def test_reset_edges_are_dropped_by_signal_name(self):
        nets = {"rst_n": {"bits": [3]}, "go": {"bits": [4]}, "bus": {"bits": [5, 3]}}
        trans = [(0, "11", 1), (1, "01", 0), (1, "10", 1), (1, "00", 0)]    # ctrl_in = [rst_n, go]
        p = self.write_fsm(fsm_cell(["0", "1"], trans, ctrl_in=[3, 4]), nets=nets)
        self.assertEqual(read_fsm_cells(p, "t")[0]["trans"], [(0, 1), (1, 0), (1, 1), (1, 0)])
        f = read_fsm_cells(p, "t", {"rst_n": 0})[0]
        self.assertEqual((f["trans"], f["reset_edges"], f["reset_targets"]), ([(0, 1), (1, 1)], 2, {0}))
        f = read_fsm_cells(p, "t", {"bus[1]": 1})[0]                    # matched through any alias
        self.assertEqual(f["trans"], [(1, 0), (1, 0)])                  # the rst_n=1 edges went
        self.assertEqual(read_fsm_cells(p, "t", {"unrelated": 1})[0]["reset_edges"], 0)

    def test_state_numbers_without_bits(self):
        # STATE_NUM_LOG2 = 0 leaves no state-number bits in a transition row:
        # every row then goes from state 0 to state 0.
        cell = fsm_cell(["0"], [(0, "1", 0)], ctrl_in=[7])
        cell["parameters"].update(STATE_NUM_LOG2=0, TRANS_TABLE="1")
        (f,) = read_fsm_cells(self.write_fsm(cell), "t")
        self.assertEqual((f["states"], f["trans"]), (["0"], [(0, 0)]))

    def test_only_fsm_cells(self):
        other = {"type": "$dff", "parameters": {}, "attributes": {}, "port_directions": {}, "connections": {}}
        self.assertEqual(read_fsm_cells(self.write_fsm(other), "t"), [])


    def test_inputs_derived_from_the_reset(self):
        # PicoRV32's mem_state: `if (!resetn || trap) begin if (!resetn) st <= 0; end else case (st) ...`.
        # ctrl_in = [resetn, !resetn || trap, go]; the case rows don't mention resetn but need the
        # OR low, which it cannot be while reset is held.
        cells = {"n": cell("$logic_not", A=[9], Y=[20]), "o": cell("$logic_or", A=[20], B=[11], Y=[21])}
        trans = [(s, "01-", 0) for s in range(4)] + [(s, "11-", s) for s in range(4)] + \
                [(s, "-01", (s + 1) % 4) for s in range(4)] + [(s, "-00", s) for s in range(4)]
        nets = {"resetn": {"bits": [9]}}
        p = self.write_fsm(fsm_cell(["00", "01", "10", "11"], trans, ctrl_in=[9, 21, 12]), nets=nets)
        with open(p) as f:
            d = json.load(f)
        d["modules"]["t"]["cells"].update(cells)
        p = self.write_json("fsm.json", d)
        self.assertEqual(read_fsm_cells(p, "t", {"resetn": 0})[0]["reset_targets"], {0})
        self.assertEqual(read_fsm_cells(p, "t", {"resetn": 1})[0]["reset_targets"], {0, 1, 2, 3})  # OR is unknown
        self.assertEqual(read_fsm_cells(p, "t")[0]["reset_targets"], set())                        # no reset
        # A reset row into a state number past STATE_NUM is ignored.
        p = self.write_fsm(fsm_cell(["00", "01", "10"], [(0, "0", 1), (1, "0", 3), (0, "1", 2)], ctrl_in=[9]),
                           nets={"rst_n": {"bits": [9]}})
        self.assertEqual(read_fsm_cells(p, "t", {"rst_n": 0})[0]["reset_targets"], {1})
        # Inputs that are constant regardless of the reset say nothing about it.
        p = self.write_fsm(fsm_cell(["0", "1"], [(0, "01", 1), (1, "0-", 0)], ctrl_in=["0", 12]))
        self.assertEqual(read_fsm_cells(p, "t", {"rst": 1})[0]["reset_targets"], set())


def cell(typ, signed=False, **conns):
    return {"type": typ, "parameters": {"A_SIGNED": int(signed), "B_SIGNED": int(signed)}, "connections": conns}


class ThreeValued(unittest.TestCase):
    """_Eval: what the control inputs of an FSM are while the reset is held."""

    def ev(self, cells, pinned):
        return _Eval({"cells": cells}, pinned)

    def test_gates(self):
        x, one, zero = 1, 2, 3                                      # x unknown; pinned 1 and 0
        cases = [("$not", [x], None), ("$not", [one], 0), ("$and", [x, zero], 0), ("$and", [x, one], None),
                 ("$or", [x, one], 1), ("$or", [x, zero], None), ("$xor", [one, one], 0), ("$xor", [x, one], None),
                 ("$xor", [one, zero], 1), ("$xnor", [one, zero], 0), ("$xnor", [one, one], 1),
                 ("$xnor", [x, zero], None),
                 ("$reduce_and", [one, zero], 0), ("$reduce_or", [x, one], 1), ("$reduce_bool", [zero, zero], 0),
                 ("$logic_not", [zero, x], None), ("$logic_not", [zero, zero], 1),
                 ("$logic_and", [one, x], None), ("$logic_and", [zero, x], 0), ("$logic_or", [x, one], 1)]
        for typ, ins, want in cases:
            with self.subTest(typ=typ, ins=ins):
                ab = {"A": ins[:1], "B": ins[1:]} if typ in ("$and", "$or", "$xor", "$xnor", "$logic_and",
                                                            "$logic_or") else {"A": ins}
                e = self.ev({"g": cell(typ, Y=[10], **ab)}, {one: 1, zero: 0})
                self.assertEqual(e.bit(10), want)

    def test_multi_bit_results_and_extension(self):
        e = self.ev({"g": cell("$logic_or", A=[1], B=["0"], Y=[10, 11]),
                     "u": cell("$not", A=[1], Y=[12, 13]),                       # zero-extended: ~0 = 1
                     "s": cell("$not", True, A=[2], Y=[14, 15])}, {1: 1, 2: 1})  # sign-extended: ~1 = 0
        self.assertEqual([e.bit(b) for b in (10, 11, 12, 13, 14, 15)], [1, 0, 0, 1, 0, 0])
        bare = {"type": "$not", "parameters": {}, "connections": {"A": [2], "Y": [10, 11]}}   # no A_SIGNED: unsigned
        self.assertEqual([self.ev({"g": bare}, {2: 1}).bit(b) for b in (10, 11)], [0, 1])

    def test_equality(self):
        e = self.ev({"eq": cell("$eq", A=[1, 2], B=["1", "0"], Y=[10]),
                     "ne": cell("$ne", A=[1, 2], B=["0", "0"], Y=[11]),
                     "ux": cell("$eq", A=[1, 3], B=["1", "0"], Y=[12]),
                     "wide": cell("$eq", A=[1], B=["1", "1"], Y=[13]),
                     "wide_a": cell("$eq", A=[1, 1], B=["1"], Y=[14])}, {1: 1, 2: 0})
        self.assertEqual([e.bit(b) for b in (10, 11, 12, 13, 14)], [1, 1, None, 0, 0])

    def test_mux_and_pmux(self):
        cells = {"m0": cell("$mux", A=[1, 2], B=["0", 2], S=[4], Y=[10, 11]),         # S unknown: bits that agree
                 "m1": cell("$mux", A=[1, 2], B=["0", 2], S=[1], Y=[12, 13]),
                 "m2": cell("$mux", A=[1, 2], B=["0", "1"], S=[2], Y=[24, 25]),
                 "m3": cell("$mux", A=[2, 2], B=["1", "1"], S=[1], Y=[26, 27]),
                 "p0": cell("$pmux", A=["0", "0"], B=["1", "1", "1", "0"], S=[5, 6], Y=[14, 15]),
                 "p1": cell("$pmux", A=["0", "0"], B=["1", "1", "1", "0"], S=[1, 5], Y=[16, 17]),
                 "p2": cell("$pmux", A=["0", "0"], B=["1", "1", "1", "0"], S=[1, 7], Y=[18, 19]),
                 "p3": cell("$pmux", A=["0", "1"], B=["1", "1", "1", "0"], S=[3, 3], Y=[20, 21]),
                 "p4": cell("$pmux", A=["0", "1"], B=["1", "1", "1", "0"], S=[3, 8], Y=[22, 23])}
        e = self.ev(cells, {1: 1, 2: 0, 3: 0, 6: 0, 7: 1, 8: 1})
        self.assertEqual([e.bit(b) for b in range(10, 28)],
                         [None, 0, 0, 0, None, None, 1, None, None, None, 0, 1, 1, 0, 1, 0, 1, 1])

    def test_registers_loops_and_depth(self):
        loop = {"a": cell("$not", A=[11], Y=[10]), "b": cell("$not", A=[10], Y=[11])}
        self.assertIsNone(self.ev(loop, {1: 1}).bit(10))
        ff = {"q": {"type": "$dff", "parameters": {}, "connections": {"D": [1], "Q": [10]}}}
        self.assertIsNone(self.ev(ff, {1: 1}).bit(10))
        chain = {f"n{i}": cell("$not", A=[100 + i], Y=[101 + i]) for i in range(_Eval.MAX_DEPTH + 5)}
        self.assertEqual(self.ev(chain, {100: 0}).bit(110), 0)
        n = _Eval.MAX_DEPTH + 1                                         # gates between the pinned bit and the query
        self.assertEqual(self.ev(chain, {100: 0}).bit(100 + n), n % 2)
        self.assertIsNone(self.ev(chain, {100: 0}).bit(100 + n + 1))    # one more: too deep, unknown
        e = self.ev(chain, {100: 0})
        self.assertEqual((e.bit("1"), e.bit("x"), self.ev(chain, {}).bit(110)), (1, None, None))


class StronglyConnected(unittest.TestCase):
    def comps(self, nodes, edges):
        return sorted(sorted(c) for c in _sccs(nodes, edges))

    def test_components(self):
        edges = {1: {2}, 2: {3}, 3: {1, 4}, 4: {5}, 5: {4}, 6: set()}
        self.assertEqual(self.comps({1, 2, 3, 4, 5, 6}, edges), [[1, 2, 3], [4, 5], [6]])
        self.assertEqual(self.comps({1}, {1: {1}}), [[1]])
        self.assertEqual(self.comps(set(), {}), [])

    def test_random_graphs_against_reachability(self):
        rnd = random.Random(5)
        for trial in range(300):
            n = rnd.randint(1, 9)
            edges = {v: {w for w in range(n) if rnd.random() < 0.25} for v in range(n)}
            reach = {}
            for v in range(n):                                           # brute force: mutual reachability
                seen, todo = {v}, [v]
                while todo:
                    for w in edges[todo.pop()]:
                        if w not in seen:
                            seen.add(w)
                            todo.append(w)
                reach[v] = seen
            want = {tuple(sorted(w for w in range(n) if w in reach[v] and v in reach[w])) for v in range(n)}
            with self.subTest(trial=trial):
                self.assertEqual(self.comps(set(range(n)), edges), sorted(map(list, want)))

    def test_long_chain_does_not_recurse(self):
        n = 20000
        edges = {i: {i + 1} for i in range(n)}
        self.assertEqual(len(_sccs(set(range(n + 1)), edges)), n + 1)
        edges[n] = {0}
        self.assertEqual(len(_sccs(set(range(n + 1)), edges)), 1)


class Analysis(TempDirCase):
    def build(self, states, trans, reset=0, decode=(), waive=None, ctrl_in=(), q_is_ff=True):
        b = NB()
        clk = b.input("clk")[0]
        attrs = {"src": "f.v:3.1-3.2"}
        if waive:
            attrs["fvlint_waive"] = waive
        st = b.net("st", b.new(len(states[0])), **attrs)
        arst = b.input("arst")[0] if reset is not None else None     # with a reset state: an asynchronous reset
        if q_is_ff:
            b.ff(b.input("nxt", len(st)), clk, q=st, name="st_ff", arst=arst)
        for k in decode:
            b.op("$eq", w=1, A=st, B=[("1" if (k >> i) & 1 else "0") for i in range(len(st))])
        nl = b.build()
        p = self.write_json("fsm.json", {"modules": {"t": {
            "ports": {}, "netnames": {"st": {"bits": st}},
            "cells": {"$fsm": fsm_cell(states, trans, reset, ctrl_in=ctrl_in, arst=[arst] if arst else None)}}}})
        return nl, p

    def test_clean_fsm(self):
        nl, p = self.build(["00", "01", "10"], [(0, "", 1), (1, "", 2), (2, "", 0)])
        checks, lemmas = analyse_fsms(nl, p)
        self.assertEqual([(c.id, c.preset) for c in checks], [("fsm_summary:st", INFO)])
        self.assertEqual(checks[0].detail, "3 reachable states from reset 2'b00")
        self.assertEqual(checks[0].src, "f.v:3")
        (lm,) = lemmas["st_ff"]
        self.assertEqual((lm.checker, lm.ports), ("fvl_member", {"v": nl.netnames["st"]["bits"]}))
        self.assertEqual(lm.params, {"W": 2, "N": 3, "SET": 0 | (1 << 2) | (2 << 4)})

    def test_unreachable_assigned_and_decoded_states(self):
        # 01 is assigned (has an outgoing edge) but never entered; 11 is only decoded.
        nl, p = self.build(["00", "10", "01"], [(0, "", 0), (0, "", 1), (1, "", 0), (2, "", 0)], decode=(3, 1, 0))
        checks, _ = analyse_fsms(nl, p)
        got = {c.id: (c.preset, c.detail) for c in checks if c.kind == "fsm_unreachable"}
        self.assertEqual(got, {
            "fsm_unreachable:st=2'b01": (FAIL, "unreachable: assigned somewhere but no transition path from "
                                               "reset reaches it"),
            "fsm_unreachable:st=2'b11": (FAIL, "unreachable: decoded by the logic (case item / compare) but "
                                               "never assigned"),
        })

    def test_decodes_of_other_signals_or_out_of_range_values_are_ignored(self):
        b = NB()
        st = b.net("st", b.new(2))
        b.ff(b.input("nxt", 2), b.input("clk")[0], q=st, arst=b.input("arst")[0])
        other = b.input("other", 2)
        b.op("$eq", w=1, A=other, B=["0", "1"])                          # not the state register: 10
        b.op("$eq", w=1, A=st + ["0"], B=["0", "0", "1"])                # 4 does not fit in 2 bits
        b.op("$eq", w=1, A=st + ["1"], B=["0", "1", "0"])                # {1, st} == 3'b010: never st == 10
        b.op("$eq", w=1, A=[st[0], "1"], B=["0", "1"])                   # not all of st: 10
        b.op("$add", A=st, B=["0", "1"])                                 # arithmetic, not a decode: 10
        b.op("$ne", w=1, A=["1", "1"], B=st)                             # constant on the left: 3 decoded
        b.cell("mem", "$mem_v2", {"RD_ADDR": st, "RD_DATA": b.new(1)}, {"WIDTH": 1})   # state without Q
        nl = b.build()
        fsm = fsm_cell(["00", "01"], [(0, "", 1), (1, "", 0)], arst=nl.ports["arst"]["bits"])
        p = self.write_json("fsm.json", {"modules": {"t": {"ports": {}, "netnames": {"st": {"bits": st}},
                                                          "cells": {"$fsm": fsm}}}})
        ids = [c.id for c in analyse_fsms(nl, p)[0]]
        self.assertEqual(ids, ["fsm_unreachable:st=2'b11", "fsm_summary:st"])

    def test_all_equality_compares_decode(self):
        for t in ("$eq", "$ne", "$eqx", "$nex"):
            with self.subTest(type=t):
                nl, p = self.build(["00", "01"], [(0, "", 1), (1, "", 0)])
                b = NB()
                b.cells, b.netnames, b.ports, b._next = nl.cells, nl.netnames, nl.ports, 100
                b.op(t, w=1, A=nl.netnames["st"]["bits"] + ["0"], B=["0", "1", "0"])   # {0, st} vs 3'b010
                ids = [c.id for c in analyse_fsms(b.build(), p)[0]]
                self.assertEqual(ids, ["fsm_unreachable:st=2'b10", "fsm_summary:st"])

    def test_trap_states(self):
        # 00 -> 01 -> 10 <-> 11 (no way back): {10, 11} is a trap; 01 alone is not.
        nl, p = self.build(["00", "01", "10", "11"], [(0, "", 1), (1, "", 2), (2, "", 3), (3, "", 2)])
        checks, _ = analyse_fsms(nl, p)
        traps = [(c.id, c.preset) for c in checks if c.kind == "fsm_trap"]
        self.assertEqual(traps, [("fsm_trap:st={2'b10, 2'b11}", WARN)])

    def test_reset_state_self_loop_is_not_a_trap(self):
        nl, p = self.build(["0", "1"], [(0, "", 0), (1, "", 1)])
        checks, _ = analyse_fsms(nl, p)
        self.assertEqual([c.kind for c in checks], ["fsm_unreachable", "fsm_summary"])

    def test_synchronous_reset_edges_would_hide_traps(self):
        # Every state has an edge back to reset when rst_n=0; dropping them reveals the trap.
        trans = [(0, "1", 1), (0, "0", 0), (1, "1", 1), (1, "0", 0)]
        nl, p = self.build(["0", "1"], trans, ctrl_in=[9])
        nl.netnames["rst_n"] = {"bits": [9]}
        self.write_json("fsm.json", {"modules": {"t": {
            "ports": {}, "netnames": {"st": {"bits": nl.netnames["st"]["bits"]}, "rst_n": {"bits": [9]}},
            "cells": {"$fsm": fsm_cell(["0", "1"], trans, ctrl_in=[9])}}}})
        self.assertEqual([c.kind for c in analyse_fsms(nl, p)[0]], ["fsm_reset"])         # reset unknown
        self.assertEqual([c.kind for c in analyse_fsms(nl, p, {"rst_n": 0})[0]], ["fsm_trap", "fsm_summary"])

    def test_late_override_after_the_reset_branch(self):
        # PicoRV32's shape: `if (!resetn) st <= FETCH; else case ...` and,
        # after it, `if (err) st <= TRAP;`.  fsm_extract guesses TRAP as the
        # reset state from the mux tree (STATE_RST = 0 here); the reset rows
        # say FETCH.  ctrl_in = [resetn, err]; states TRAP, FETCH, EXEC.
        trans = [(s, "00", 1) for s in range(3)] + [(s, "-1", 0) for s in range(3)] + \
                [(1, "10", 2), (2, "10", 1), (0, "10", 0)]
        nl, _ = self.build(["100", "010", "001"], trans, reset=None)
        p = self.write_json("fsm.json", {"modules": {"t": {
            "ports": {}, "netnames": {"st": {"bits": nl.netnames["st"]["bits"]}, "resetn": {"bits": [9]}},
            "cells": {"$fsm": fsm_cell(["100", "010", "001"], trans, reset=0, ctrl_in=[9, 10])}}}})
        checks, _ = analyse_fsms(nl, p, {"resetn": 0})
        self.assertEqual([c.id for c in checks if c.kind == "fsm_unreachable"], [])
        (summary,) = [c for c in checks if c.kind == "fsm_summary"]
        # err can also fire while reset is held (its rows don't care about resetn): TRAP is a start too.
        self.assertEqual(summary.detail, "3 reachable states from reset {3'b010, 3'b100}")
        self.assertEqual([c.id for c in checks if c.kind == "fsm_trap"], [])

    def test_state_rst_is_trusted_only_for_an_asynchronous_reset(self):
        # fsm_extract connects the $fsm cell's ARST when the state register
        # has an asynchronous reset (whatever cell type the frontend used).
        trans = [(0, "", 1), (1, "", 0)]
        nl, p = self.build(["0", "1"], trans)
        self.assertEqual([c.id for c in analyse_fsms(nl, p)[0]], ["fsm_summary:st"])
        st = {"st": {"bits": nl.netnames["st"]["bits"]}}
        for arst in (None, ["0"], ["x"]):                                     # STATE_RST was a guess
            p = self.write_json("fsm.json", {"modules": {"t": {"ports": {}, "netnames": st, "cells": {
                "$fsm": fsm_cell(["0", "1"], trans, reset=1, arst=arst)}}}})
            self.assertEqual([c.id for c in analyse_fsms(nl, p)[0]], ["fsm_reset:st"])

    def test_no_reset_state(self):
        nl, p = self.build(["0", "1"], [(0, "", 1)], reset=None, waive="all")
        checks, lemmas = analyse_fsms(nl, p)
        self.assertEqual([(c.id, c.preset, c.waive_attr) for c in checks], [("fsm_reset:st", INFO, "all")])
        self.assertEqual(lemmas, {})

    def test_state_signal_not_driven_by_one_register(self):
        # A synchronous reset row still says where the FSM starts; with no
        # single register to attach it to there is no lemma.
        trans = [(0, "1", 1), (1, "1", 0), (0, "0", 0), (1, "0", 0)]         # ctrl_in = [rst_n]
        nl, _ = self.build(["0", "1"], trans, ctrl_in=[9], q_is_ff=False)
        p = self.write_json("fsm.json", {"modules": {"t": {
            "ports": {}, "netnames": {"st": {"bits": nl.netnames["st"]["bits"]}, "rst_n": {"bits": [9]}},
            "cells": {"$fsm": fsm_cell(["0", "1"], trans, ctrl_in=[9])}}}})
        checks, lemmas = analyse_fsms(nl, p, {"rst_n": 0})
        self.assertEqual(([c.kind for c in checks], lemmas), (["fsm_summary"], {}))
        self.assertEqual(analyse_fsms(nl, p)[0][0].id, "fsm_reset:st")            # STATE_RST alone is not trusted

    def test_state_signal_missing_from_the_netlist(self):
        # The FSM names a signal the main netlist does not have (renamed by a
        # later pass): no decodes or lemmas can be tied to it.
        nl, _ = self.build(["00", "01"], [(0, "", 1), (1, "", 0)], decode=(2, 3))
        trans = [(0, "1", 1), (1, "1", 0), (0, "0", 0), (1, "0", 0)]
        p = self.write_json("fsm.json", {"modules": {"t": {"ports": {}, "netnames": {"rst_n": {"bits": [9]}},
                                                          "cells": {"$fsm": fsm_cell(["00", "01"], trans, ctrl_in=[9],
                                                                                     name="\\gone")}}}})
        checks, lemmas = analyse_fsms(nl, p, {"rst_n": 0})
        self.assertEqual(([(c.id, c.src) for c in checks], lemmas), ([("fsm_summary:gone", "?")], {}))

    def test_transitions_to_unknown_state_numbers_are_ignored(self):
        # Three states need 2-bit state numbers; number 3 names no state.
        nl, p = self.build(["00", "01", "10"], [(0, "", 1), (1, "", 3), (3, "", 0)])
        self.assertEqual([c.id for c in analyse_fsms(nl, p)[0]],
                         ["fsm_unreachable:st=2'b10", "fsm_trap:st={2'b01}", "fsm_summary:st"])


class DeadStates(TempDirCase):
    """Checks that apply only in an unreachable state (PicoRV32's LD_RS2 with
    the dual-port register file) are dead: INFO, pointing at the root finding."""

    def setUp(self):
        super().setUp()
        b = NB()
        clk = b.input("clk")[0]
        arst = b.input("arst")[0]
        self.st = st = b.net("st", b.new(2))
        b.ff(b.input("nxt", 2), clk, q=st, name="st_ff", arst=arst)
        k = lambda v, w=2: [("1" if (v >> i) & 1 else "0") for i in range(w)]   # noqa: E731
        self.eq3 = b.op("$eq", w=1, A=st, B=k(3))[0]                    # st == 2'b11: never reached
        self.eq1 = b.op("$eq", w=1, A=k(1), B=st)[0]                    # constant first, reachable state
        self.ne3 = b.op("$ne", w=1, A=st + ["0", "0"], B=k(3, 4))[0]    # zero-extended state, st != 3
        self.eq9 = b.op("$eq", w=1, A=st + ["0", "0"], B=k(9, 4))[0]    # a value st can't hold
        self.other = b.op("$eq", w=1, A=b.input("x", 2), B=k(3))[0]     # not the state register
        self.eqx3 = b.op("$eqx", w=1, A=st, B=k(3))[0]
        self.nex3 = b.op("$nex", w=1, A=st, B=k(3))[0]
        self.eqsig = b.op("$eq", w=1, A=st, B=b.input("y", 2))[0]       # compared with a signal
        self.eq4 = b.op("$eq", w=1, A=st + ["0"], B=k(4, 3))[0]          # just too wide for st
        self.nl = b.build()
        p = self.write_json("fsm.json", {"modules": {"t": {
            "ports": {}, "netnames": {"st": {"bits": st}},
            "cells": {"$fsm": fsm_cell(["00", "01"], [(0, "", 1), (1, "", 0)], 0, arst=[arst])}}}})
        self.fsms = {}
        self.fsm_checks, _ = analyse_fsms(self.nl, p, reach_out=self.fsms)

    def check(self, *conds):
        return Check(kind="parallel_case", target="y", src="f.v:9", desc="", conds=list(conds))

    def test_reachable_states_are_recorded(self):
        self.assertEqual(self.fsms, {tuple(self.st): ("st", frozenset({"00", "01"}))})
        self.assertIn("fsm_unreachable:st=2'b11", [c.id for c in self.fsm_checks])

    def test_dead_checks(self):
        dead = [self.check((self.eq3, 1)), self.check((5, 1), (self.ne3, 0)), self.check((self.eq9, 1))]
        live = [self.check((self.eq1, 1)), self.check((self.eq3, 0)), self.check((self.ne3, 1)),
                self.check((self.other, 1)), self.check()]
        waived = self.check((self.eq3, 1))
        waived.preset, waived.detail = INFO, "free-running"
        self.assertEqual(dead_in_unreachable_states(self.nl, dead + live + [waived], self.fsms), 3)
        self.assertEqual([(c.preset, c.reason) for c in dead], [(INFO, "dead_state")] * 3)
        self.assertEqual(dead[0].detail, "dead logic: applies only in state st=2'b11, which is unreachable "
                                         "(see fsm_unreachable:st=2'b11); not checked")
        self.assertEqual(dead[1].detail, dead[0].detail)
        self.assertEqual(dead[2].detail, "dead logic: applies only when st equals a value wider than the "
                                         "register; not checked")
        self.assertEqual([(c.preset, c.reason) for c in live], [(None, None)] * len(live))
        self.assertEqual((waived.detail, waived.reason), ("free-running", None))   # a preset is left alone

    def test_more_compare_shapes(self):
        dead = [self.check((self.eqx3, 1)), self.check((self.nex3, 0)), self.check((self.eq4, 1))]
        live = [self.check((self.eqsig, 1)), self.check((self.eqx3, 0)), self.check((self.nex3, 1))]
        self.assertEqual(dead_in_unreachable_states(self.nl, dead + live, self.fsms), 3)
        self.assertEqual([c.preset for c in live], [None] * 3)
        self.assertIn("wider than the register", dead[2].detail)

    def test_counted_once(self):
        c = self.check((self.eq3, 1), (self.eqx3, 1))
        self.assertEqual(dead_in_unreachable_states(self.nl, [c], self.fsms), 1)

    def test_without_fsms(self):
        c = self.check((self.eq3, 1))
        self.assertEqual(dead_in_unreachable_states(self.nl, [c], {}), 0)
        self.assertIsNone(c.preset)


class RealNetlists(unittest.TestCase):
    def test_snapshot_fsm(self):
        nl = load_snapshot("snap_fsm")
        resets = discover(nl, None, False, None)
        (f,) = read_fsm_cells(snapshot("snap_fsm", "fsm"), "snap_fsm", resets.names())
        self.assertEqual(f["name"], "st")
        self.assertEqual(sorted(f["states"]), ["00", "01", "10"])       # IDLE, RUN, DONE (ORPHAN never assigned)
        self.assertEqual([f["states"][i] for i in f["reset_targets"]], ["00"])   # from the reset rows
        self.assertEqual(f["reset_edges"], 3)                           # one per state, all dropped
        code = f["states"]
        self.assertEqual(sorted((code[a], code[b]) for a, b in f["trans"]),
                         [("00", "00"), ("00", "01"), ("01", "01"), ("01", "10"), ("10", "10")])

        checks, lemmas = analyse_fsms(nl, snapshot("snap_fsm", "fsm"), resets.names())
        self.assertEqual({c.id: c.preset for c in checks}, {
            "fsm_unreachable:st=2'b11": FAIL, "fsm_trap:st={2'b10}": WARN, "fsm_summary:st": INFO})
        self.assertTrue(all(c.src == "snap_fsm.sv:9" for c in checks))
        (lm,) = [lm for lms in lemmas.values() for lm in lms]
        self.assertEqual(lm.params, {"W": 2, "N": 3, "SET": 0 | (1 << 2) | (2 << 4)})

    def test_designs_without_fsms(self):
        nl = load_snapshot("snap_counters")
        self.assertEqual(analyse_fsms(nl, snapshot("snap_counters", "fsm")), ([], {}))


if __name__ == "__main__":
    unittest.main()
