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


def _and3(vs):
    return 0 if 0 in vs else (1 if all(v == 1 for v in vs) else None)


def _or3(vs):
    return 1 if 1 in vs else (0 if all(v == 0 for v in vs) else None)


def _not3(v):
    return None if v is None else 1 - v


def _agree(vs):
    return vs[0] if vs and all(v == vs[0] for v in vs) else None


class _Eval:
    """Three-valued (0, 1, None = unknown) evaluation of the word-level
    combinational cells of a Yosys JSON module with some bits pinned.
    Registers, unsupported cells and deep cones evaluate to unknown."""

    MAX_DEPTH = 64

    def __init__(self, mod: dict, pinned: dict):
        self.cells, self.pinned, self.memo, self.busy = mod["cells"], pinned, {}, set()
        self.driver = {}
        for name, c in self.cells.items():
            if c["type"] in _OPS:
                for i, b in enumerate(c["connections"].get("Y", [])):
                    self.driver[b] = (name, i)

    def bit(self, b, depth=0):
        if b in ("0", "1"):
            return int(b)
        if not isinstance(b, int):
            return None
        if b in self.pinned:
            return self.pinned[b]
        if b not in self.driver or depth > self.MAX_DEPTH:
            return None
        name, i = self.driver[b]
        if name not in self.memo:
            if name in self.busy:                    # combinational loop
                return None
            self.busy.add(name)
            self.memo[name] = _OPS[self.cells[name]["type"]](self, self.cells[name], depth + 1)
            self.busy.discard(name)
        y = self.memo[name]
        return y[i] if i < len(y) else None

    def port(self, c, name, depth, width=None):
        v = [self.bit(b, depth) for b in c["connections"].get(name, [])]
        if width is None:
            return v
        if len(v) < width:                           # Yosys extends operands to the result width
            signed = param_int(c["parameters"].get(name + "_SIGNED", 0))
            v += [v[-1] if signed and v else 0] * (width - len(v))
        return v[:width]


def _width(c):
    return len(c["connections"].get("Y", []))


def _one_bit(c, v):
    return [v] + [0] * (_width(c) - 1)


def _op_bitwise(f):
    return lambda ev, c, d: [f([a, b]) for a, b in zip(ev.port(c, "A", d, _width(c)), ev.port(c, "B", d, _width(c)))]


def _op_reduce(f, invert=False):
    return lambda ev, c, d: _one_bit(c, (_not3 if invert else (lambda v: v))(f(ev.port(c, "A", d))))


def _op_logic(f):
    return lambda ev, c, d: _one_bit(c, f([_or3(ev.port(c, "A", d)), _or3(ev.port(c, "B", d))]))


def _op_eq(invert):
    def op(ev, c, d):
        w = max(len(c["connections"].get("A", [])), len(c["connections"].get("B", [])))
        pairs = zip(ev.port(c, "A", d, w), ev.port(c, "B", d, w))
        v = _and3([None if x is None or y is None else int(x == y) for x, y in pairs])
        return _one_bit(c, _not3(v) if invert else v)
    return op


def _op_mux(ev, c, d):
    w = _width(c)
    a, b, (s,) = ev.port(c, "A", d, w), ev.port(c, "B", d, w), ev.port(c, "S", d)
    return b if s == 1 else a if s == 0 else [_agree([x, y]) for x, y in zip(a, b)]


def _op_pmux(ev, c, d):
    w = _width(c)
    a, b, s = ev.port(c, "A", d, w), ev.port(c, "B", d), ev.port(c, "S", d)
    if s.count(1) > 1:
        return [None] * w
    cands = [b[k * w:(k + 1) * w] for k, v in enumerate(s) if v != 0]
    if 1 not in s:
        cands.append(a)
    return [_agree([x[i] for x in cands]) for i in range(w)]


_OPS = {
    "$not": lambda ev, c, d: [_not3(v) for v in ev.port(c, "A", d, _width(c))],
    "$and": _op_bitwise(_and3), "$or": _op_bitwise(_or3),
    "$xor": _op_bitwise(lambda v: None if None in v else v[0] ^ v[1]),
    "$xnor": _op_bitwise(lambda v: None if None in v else 1 - (v[0] ^ v[1])),
    "$reduce_and": _op_reduce(_and3), "$reduce_or": _op_reduce(_or3), "$reduce_bool": _op_reduce(_or3),
    "$logic_not": _op_reduce(_or3, invert=True), "$logic_and": _op_logic(_and3), "$logic_or": _op_logic(_or3),
    "$eq": _op_eq(False), "$ne": _op_eq(True), "$mux": _op_mux, "$pmux": _op_pmux,
}


def read_fsm_cells(fsm_json: str, top: str, reset_names: dict | None = None) -> list:
    """Decode the $fsm cells written by fsm_extract.

    Returns dicts with 'name', 'states' (MSB-first code strings, index =
    state number), 'trans' [(from, to)], 'reset_targets' (the states a
    transition can enter while the reset is asserted), 'state_rst' (Yosys'
    STATE_RST, or None) and 'async_reset' (whether the state register has an
    asynchronous reset, which STATE_RST then comes from).  Transitions that require a reset input to
    be asserted are dropped from 'trans' (`reset_names` maps signal names to
    their active level): with a synchronous reset every state has an edge
    back to the reset state, which would otherwise hide trap states.

    fsm_extract treats its control inputs as independent, but some are
    functions of the reset (`!rst_n || err`).  Their values with the reset
    asserted come from evaluating the logic in front of them, so a row that
    needs `!rst_n || err` low is not taken to fire during reset.  Inputs
    whose value is unknown match any row: the start set errs large, which
    can only hide an unreachable state, never invent one.

    STATE_RST is only trustworthy for an asynchronous reset (the cell's ARST
    is connected): for anything else fsm_extract guesses it "from the mux
    tree" (the constant at the root), which a late overriding assignment,
    e.g. `if (err) st <= TRAP;` after the reset branch, makes wrong.
    """
    with open(fsm_json) as f:
        mod = json.load(f)["modules"][top]
    bit_names = {}
    for name, n in mod["netnames"].items():
        for i, b in enumerate(n["bits"]):
            bit_names.setdefault(b, set()).add(name if len(n["bits"]) == 1 else f"{name}[{i}]")
    reset_names = reset_names or {}
    ev = _Eval(mod, {b: int(lvl) for b, nms in bit_names.items() for nm in nms
                     if nm in reset_names and isinstance(b, int) for lvl in [reset_names[nm]]})
    ev_free = _Eval(mod, {})                      # what is known without the reset (constants)
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
        at_reset = [ev.bit(b) for b in ctrl_in]
        reset_known = any(v is not None and ev_free.bit(b) is None for b, v in zip(ctrl_in, at_reset))
        tt = _bits_lsb(p["TRANS_TABLE"])
        w = 2 * lg + ci + co
        trans, dropped, targets = [], 0, set()
        for i in range(tn):
            e = tt[i * w:(i + 1) * w]
            cin = e[co + lg:co + lg + ci]
            s_out = int(e[co:co + lg][::-1] or "0", 2)
            s_in = int(e[co + lg + ci:][::-1] or "0", 2)
            # A row whose inputs can all hold their values with the reset
            # asserted can set the state while the reset is held.
            if reset_known and s_out < sn and all(
                    v not in "01" or r is None or int(v) == r for v, r in zip(cin, at_reset)):
                targets.add(s_out)
            held = [cin[j] for j in reset_inputs if j < len(cin)]
            if any(v == reset_inputs[j] for j, v in zip(reset_inputs, held)):
                dropped += 1
                continue
            trans.append((s_in, s_out))
        rst = p.get("STATE_RST")
        state_rst = None
        if isinstance(rst, (str, int)):
            try:
                r = param_int(rst)
                state_rst = r if r < sn else None
            except ValueError:
                state_rst = None
        name = str(p.get("NAME", "")).lstrip("\\")
        out.append({"name": name, "states": states, "trans": trans, "reset_targets": targets,
                    "state_rst": state_rst, "reset_edges": dropped,
                    "async_reset": any(isinstance(b, int) for b in c["connections"].get("ARST", []))})
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


def _fmt_set(codes) -> str:
    """One state as 3'b010; several (a reset that can land in more than one) as {3'b000, 3'b111}."""
    codes = sorted(codes)
    return _fmt(codes[0]) if len(codes) == 1 else "{" + ", ".join(_fmt(c) for c in codes) + "}"


def analyse_fsms(nl: Netlist, fsm_json: str, reset_names: dict | None = None, reach_out: dict | None = None):
    """FSM checks and lemmas.  With `reach_out`, also records for each FSM
    the state register's bits -> (name, reachable state codes)."""
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

        start = {codes[i] for i in fsm["reset_targets"]}
        if fsm["async_reset"] and fsm["state_rst"] is not None:
            start.add(codes[fsm["state_rst"]])          # Yosys took it from the asynchronous reset
        if not start:
            checks.append(mk("fsm_reset", sig, INFO, f"FSM {sig} has a reset state",
                             "no reset state found; reachability not analysed"))
            continue
        reset = _fmt_set(start)
        edges = {}
        for a, b in fsm["trans"]:
            if a < len(codes) and b < len(codes):
                edges.setdefault(codes[a], set()).add(codes[b])
        reach, todo = set(start), sorted(start)
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

        if reach_out is not None and bits and width:
            reach_out[tuple(bits)] = (sig, frozenset(reach))
        assigned = set(codes)
        for code in sorted((assigned | handled) - reach):
            why = ("assigned somewhere but no transition path from reset reaches it"
                   if code in assigned else
                   "decoded by the logic (case item / compare) but never assigned")
            checks.append(mk("fsm_unreachable", f"{sig}={_fmt(code)}", FAIL,
                             f"state {_fmt(code)} of {sig} is reachable from reset {reset}",
                             f"unreachable: {why}"))

        sub = {s: {t for t in edges.get(s, ()) if t in reach} for s in reach}
        for comp in _sccs(reach, sub):
            if comp & start:
                continue
            leaves = any(t not in comp for s in comp for t in sub.get(s, ()))
            if not leaves:
                names = ", ".join(_fmt(s) for s in sorted(comp))
                checks.append(mk("fsm_trap", f"{sig}={{{names}}}", WARN,
                                 f"{sig} can always return to reset state {reset}",
                                 f"once in {{{names}}} the FSM never leaves (only reset exits); "
                                 "fine for terminal states like DONE/READY, otherwise a deadlock"))

        checks.append(mk("fsm_summary", sig, INFO, f"FSM {sig} extracted",
                         f"{len(reach)} reachable states from reset {reset}"))

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


def _state_compare(nl: Netlist, bit, value: int, fsms: dict):
    """(name, code, reachable codes) if the condition `bit == value` means
    `state == code` for the state register of an FSM in `fsms` (see
    Netlist.equality, which detect's statement names use too).  code is
    None for a constant the register is too narrow to hold.  Otherwise
    None."""
    hit = nl.equality(bit, value)
    if hit is None:
        return None
    x, k = hit
    for bits, (sig, reach) in fsms.items():
        n = len(bits)
        if x == list(bits):
            return sig, (format(k, f"0{n}b") if k < (1 << n) else None), reach
    return None


def dead_in_unreachable_states(nl: Netlist, checks: list, fsms: dict) -> int:
    """Mark checks that apply only in an unreachable FSM state as INFO: one
    of their path conditions is `state == code` for a code the FSM analysis
    found unreachable (its fsm_unreachable result is the finding to look
    at).  Their proofs would only come back VACUOUS.  Returns how many."""
    n = 0
    for c in checks:
        if c.preset is not None:
            continue
        for bit, value in c.conds:
            hit = _state_compare(nl, bit, value, fsms)
            if hit is None:
                continue
            sig, code, reach = hit
            if code is None:
                why = f"applies only when {sig} equals a value wider than the register"
            elif code not in reach:
                why = (f"applies only in state {sig}={_fmt(code)}, which is unreachable "
                       f"(see fsm_unreachable:{sig}={_fmt(code)})")
            else:
                continue
            c.preset, c.detail = INFO, f"dead logic: {why}; not checked"
            n += 1
            break
    return n
