# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""fvlint.fsm: decoding Yosys $fsm cells and the reachability analysis."""

from __future__ import annotations

import random
import unittest

from fvlint.checks import FAIL, INFO, WARN
from fvlint.fsm import _bits_lsb, _sccs, analyse_fsms, read_fsm_cells
from fvlint.resets import discover

from .support import NB, TempDirCase, load_snapshot, snapshot


def fsm_cell(states, trans, reset=0, ctrl_in=(), ctrl_out_w=0, name="\\st", state_bits=None):
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
    return {"type": "$fsm", "parameters": p, "attributes": {}, "port_directions": {},
            "connections": {"CTRL_IN": list(ctrl_in), "CTRL_OUT": []}}


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
        self.assertEqual((f["name"], f["states"], f["reset"]), ("st", ["00", "01", "11"], 0))
        self.assertEqual((f["trans"], f["reset_edges"]), ([(0, 1), (1, 2), (2, 2)], 0))

    def test_control_outputs_are_skipped_over(self):
        p = self.write_fsm(fsm_cell(["0", "1"], [(0, "1", 1), (1, "0", 0)], ctrl_in=[7], ctrl_out_w=3))
        self.assertEqual(read_fsm_cells(p, "t")[0]["trans"], [(0, 1), (1, 0)])

    def test_reset_state_variants(self):
        for rst, want in ((1, 1), (2, None), (5, None), ("x" * 32, None), (None, None)):
            with self.subTest(rst=rst):
                p = self.write_fsm(fsm_cell(["0", "1"], [(0, "", 1)], reset=rst))
                self.assertEqual(read_fsm_cells(p, "t")[0]["reset"], want)

    def test_reset_edges_are_dropped_by_signal_name(self):
        nets = {"rst_n": {"bits": [3]}, "go": {"bits": [4]}, "bus": {"bits": [5, 3]}}
        trans = [(0, "11", 1), (1, "01", 0), (1, "10", 1), (1, "00", 0)]    # ctrl_in = [rst_n, go]
        p = self.write_fsm(fsm_cell(["0", "1"], trans, ctrl_in=[3, 4]), nets=nets)
        self.assertEqual(read_fsm_cells(p, "t")[0]["trans"], [(0, 1), (1, 0), (1, 1), (1, 0)])
        f = read_fsm_cells(p, "t", {"rst_n": 0})[0]
        self.assertEqual((f["trans"], f["reset_edges"]), ([(0, 1), (1, 1)], 2))
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
        if q_is_ff:
            b.ff(b.input("nxt", len(st)), clk, q=st, name="st_ff")
        for k in decode:
            b.op("$eq", w=1, A=st, B=[("1" if (k >> i) & 1 else "0") for i in range(len(st))])
        nl = b.build()
        p = self.write_json("fsm.json", {"modules": {"t": {
            "ports": {}, "netnames": {"st": {"bits": st}},
            "cells": {"$fsm": fsm_cell(states, trans, reset, ctrl_in=ctrl_in)}}}})
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
        other = b.input("other", 2)
        b.op("$eq", w=1, A=other, B=["0", "1"])                          # not the state register: 10
        b.op("$eq", w=1, A=st + ["0"], B=["0", "0", "1"])                # 4 does not fit in 2 bits
        b.op("$eq", w=1, A=st + ["1"], B=["0", "1", "0"])                # {1, st} == 3'b010: never st == 10
        b.op("$eq", w=1, A=[st[0], "1"], B=["0", "1"])                   # not all of st: 10
        b.op("$add", A=st, B=["0", "1"])                                 # arithmetic, not a decode: 10
        b.op("$ne", w=1, A=["1", "1"], B=st)                             # constant on the left: 3 decoded
        b.cell("mem", "$mem_v2", {"RD_ADDR": st, "RD_DATA": b.new(1)}, {"WIDTH": 1})   # state without Q
        nl = b.build()
        fsm = fsm_cell(["00", "01"], [(0, "", 1), (1, "", 0)])
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
        self.assertEqual([c.kind for c in analyse_fsms(nl, p)[0]], ["fsm_summary"])
        self.assertEqual([c.kind for c in analyse_fsms(nl, p, {"rst_n": 0})[0]], ["fsm_trap", "fsm_summary"])

    def test_no_reset_state(self):
        nl, p = self.build(["0", "1"], [(0, "", 1)], reset=None, waive="all")
        checks, lemmas = analyse_fsms(nl, p)
        self.assertEqual([(c.id, c.preset, c.waive_attr) for c in checks], [("fsm_reset:st", INFO, "all")])
        self.assertEqual(lemmas, {})

    def test_state_signal_not_driven_by_one_register(self):
        nl, p = self.build(["0", "1"], [(0, "", 1), (1, "", 0)], q_is_ff=False)
        checks, lemmas = analyse_fsms(nl, p)
        self.assertEqual(([c.kind for c in checks], lemmas), (["fsm_summary"], {}))

    def test_state_signal_missing_from_the_netlist(self):
        # The FSM names a signal the main netlist does not have (renamed by a
        # later pass): no decodes or lemmas can be tied to it.
        nl, _ = self.build(["00", "01"], [(0, "", 1), (1, "", 0)], decode=(2, 3))
        p = self.write_json("fsm.json", {"modules": {"t": {"ports": {}, "netnames": {}, "cells": {
            "$fsm": fsm_cell(["00", "01"], [(0, "", 1), (1, "", 0)], name="\\gone")}}}})
        checks, lemmas = analyse_fsms(nl, p)
        self.assertEqual(([(c.id, c.src) for c in checks], lemmas), ([("fsm_summary:gone", "?")], {}))

    def test_transitions_to_unknown_state_numbers_are_ignored(self):
        # Three states need 2-bit state numbers; number 3 names no state.
        nl, p = self.build(["00", "01", "10"], [(0, "", 1), (1, "", 3), (3, "", 0)])
        self.assertEqual([c.id for c in analyse_fsms(nl, p)[0]],
                         ["fsm_unreachable:st=2'b10", "fsm_trap:st={2'b01}", "fsm_summary:st"])


class RealNetlists(unittest.TestCase):
    def test_snapshot_fsm(self):
        nl = load_snapshot("snap_fsm")
        resets = discover(nl, None, False, None)
        (f,) = read_fsm_cells(snapshot("snap_fsm", "fsm"), "snap_fsm", resets.names())
        self.assertEqual(f["name"], "st")
        self.assertEqual(sorted(f["states"]), ["00", "01", "10"])       # IDLE, RUN, DONE (ORPHAN never assigned)
        self.assertEqual(f["states"][f["reset"]], "00")
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
