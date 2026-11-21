# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""FSM checks from Yosys' FSM extraction.

Yosys' fsm_extract builds a transition table treating the FSM's control
inputs as independent free variables.  That over-approximates the real
behaviour, so a state that is unreachable in this graph is unreachable in the
design (given the reset state is the initial state).  No solver is needed.
"""

from __future__ import annotations

import json

from .checks import FAIL, INFO, WARN, Check, Lemma
from .netlist import Netlist, const_value, param_int


def _bits_lsb(v) -> str:
    """Yosys JSON constant (MSB-first string) -> LSB-first string."""
    return v[::-1] if isinstance(v, str) else format(v, "032b")[::-1]


def read_fsm_cells(fsm_json: str, top: str, reset_names: dict | None = None) -> list:
    """Decode the $fsm cells written by fsm_extract.

    Returns dicts with 'name', 'states' (MSB-first code strings, index =
    state number), 'reset' (state number or None) and 'trans' [(from, to)].
    Transitions that require a reset input to be asserted are dropped
    (`reset_names` maps signal names to their active level): with a
    synchronous reset every state has an edge back to the reset state, which
    would otherwise hide trap states.
    """
    with open(fsm_json) as f:
        mod = json.load(f)["modules"][top]
    bit_names = {}
    for name, n in mod["netnames"].items():
        for i, b in enumerate(n["bits"]):
            bit_names.setdefault(b, set()).add(name if len(n["bits"]) == 1 else f"{name}[{i}]")
    reset_names = reset_names or {}
    out = []
    for c in mod["cells"].values():
        if c["type"] != "$fsm":
            continue
        p = c["parameters"]
        num = lambda k: param_int(p[k])  # noqa: E731
        sb, sn, lg = num("STATE_BITS"), num("STATE_NUM"), num("STATE_NUM_LOG2")
        ci, co, tn = num("CTRL_IN_WIDTH"), num("CTRL_OUT_WIDTH"), num("TRANS_NUM")
        st = _bits_lsb(p["STATE_TABLE"])
        states = [st[i * sb:(i + 1) * sb][::-1] for i in range(sn)]
        ctrl_in = c["connections"].get("CTRL_IN", [])
        reset_inputs = {}
        for j, b in enumerate(ctrl_in):
            for nm in bit_names.get(b, ()):
                if nm in reset_names:
                    reset_inputs[j] = str(reset_names[nm])
        tt = _bits_lsb(p["TRANS_TABLE"])
        w = 2 * lg + ci + co
        trans, dropped = [], 0
        for i in range(tn):
            e = tt[i * w:(i + 1) * w]
            cin = e[co + lg:co + lg + ci]
            if any(cin[j] == lvl for j, lvl in reset_inputs.items() if j < len(cin)):
                dropped += 1
                continue
            s_out = int(e[co:co + lg][::-1] or "0", 2)
            s_in = int(e[co + lg + ci:][::-1] or "0", 2)
            trans.append((s_in, s_out))
        rst = p.get("STATE_RST")
        reset = None
        if isinstance(rst, (str, int)):
            try:
                r = param_int(rst)
                reset = r if r < sn else None
            except ValueError:
                reset = None
        name = str(p.get("NAME", "")).lstrip("\\")
        out.append({"name": name, "states": states, "reset": reset, "trans": trans,
                    "reset_edges": dropped})
    return out


def _sccs(nodes, edges):
    index, low, onstack, stack, out = {}, {}, set(), [], []
    counter = [0]

    def strong(v):
        work = [(v, iter(edges.get(v, ())))]
        index[v] = low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        onstack.add(v)
        while work:
            node, it = work[-1]
            advanced = False
            for w in it:
                if w not in index:
                    index[w] = low[w] = counter[0]
                    counter[0] += 1
                    stack.append(w)
                    onstack.add(w)
                    work.append((w, iter(edges.get(w, ()))))
                    advanced = True
                    break
                elif w in onstack:
                    low[node] = min(low[node], index[w])
            if advanced:
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[node])
            if low[node] == index[node]:
                comp = set()
                while True:
                    w = stack.pop()
                    onstack.discard(w)
                    comp.add(w)
                    if w == node:
                        break
                out.append(comp)

    for n in sorted(nodes):
        if n not in index:
            strong(n)
    return out


def _fmt(code: str) -> str:
    return f"{len(code)}'b{code}"


def analyse_fsms(nl: Netlist, fsm_json: str, reset_names: dict | None = None):
    checks, lemmas = [], {}
    q_to_ff = {}
    for cell, c in nl.cells.items():
        if "Q" in c["connections"] and nl.is_stateful(cell):
            q_to_ff[tuple(c["connections"]["Q"])] = cell

    for fsm in read_fsm_cells(fsm_json, nl.top, reset_names):
        sig = fsm["name"]
        codes = fsm["states"]
        net = nl.netnames.get(sig)
        bits = net["bits"] if net else None
        src = nl.net_src(bits) if bits else "?"
        waive = nl.net_attr(bits, "fvlint_waive") if bits else None
        width = len(codes[0]) if codes else 0

        def mk(kind, target, status, desc, detail):
            c = Check(kind=kind, target=target, src=src, desc=desc, waive_attr=waive)
            c.preset, c.detail = status, detail
            return c

        if fsm["reset"] is None:
            checks.append(mk("fsm_reset", sig, INFO, f"FSM {sig} has a reset state",
                             "no reset state found; reachability not analysed"))
            continue
        reset = codes[fsm["reset"]]
        edges = {}
        for a, b in fsm["trans"]:
            if a < len(codes) and b < len(codes):
                edges.setdefault(codes[a], set()).add(codes[b])
        reach, todo = {reset}, [reset]
        while todo:
            s = todo.pop()
            for t in edges.get(s, ()):
                if t not in reach:
                    reach.add(t)
                    todo.append(t)

        # Codes the logic compares the state against (case items, decodes).
        handled = set()
        if bits and width:
            for cell, c in nl.cells.items():
                if c["type"] not in ("$eq", "$ne", "$eqx", "$nex"):
                    continue
                a, b = nl.conn(cell, "A"), nl.conn(cell, "B")
                for x, y in ((a, b), (b, a)):
                    if x[:len(bits)] == bits and all(v == "0" for v in x[len(bits):]):
                        v = const_value(y)
                        if v is not None and v < (1 << width):
                            handled.add(format(v, f"0{width}b"))

        assigned = set(codes)
        for code in sorted((assigned | handled) - reach):
            why = ("assigned somewhere but no transition path from reset reaches it"
                   if code in assigned else
                   "decoded by the logic (case item / compare) but never assigned")
            checks.append(mk("fsm_unreachable", f"{sig}={_fmt(code)}", FAIL,
                             f"state {_fmt(code)} of {sig} is reachable from reset {_fmt(reset)}",
                             f"unreachable: {why}"))

        sub = {s: {t for t in edges.get(s, ()) if t in reach} for s in reach}
        for comp in _sccs(reach, sub):
            if reset in comp:
                continue
            leaves = any(t not in comp for s in comp for t in sub.get(s, ()))
            if not leaves:
                names = ", ".join(_fmt(s) for s in sorted(comp))
                checks.append(mk("fsm_trap", f"{sig}={{{names}}}", WARN,
                                 f"{sig} can always return to reset state {_fmt(reset)}",
                                 f"once in {{{names}}} the FSM never leaves (only reset exits); "
                                 "fine for terminal states like DONE/READY, otherwise a deadlock"))

        checks.append(mk("fsm_summary", sig, INFO, f"FSM {sig} extracted",
                         f"{len(reach)} reachable states from reset {_fmt(reset)}"))

        if bits and tuple(bits) in q_to_ff and reach:
            vals = sorted(int(s, 2) for s in reach)
            setv = 0
            for i, v in enumerate(vals):
                setv |= v << (i * len(bits))
            ff = q_to_ff[tuple(bits)]
            lemmas.setdefault(ff, []).append(Lemma(
                owner=ff, desc=f"{sig} holds a reachable state code", checker="fvl_member",
                params={"W": len(bits), "N": len(vals), "SET": setv}, ports={"v": bits}))
    return checks, lemmas
