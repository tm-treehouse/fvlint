# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Structure detectors: find counters, unique/parallel case muxes, variable
part-selects and memories in a flattened netlist and turn each into checks.

Check ids are structural (the register, memory or destination signal the
check is about), so waivers survive edits elsewhere in the source.
"""

from __future__ import annotations

import os
import re
from dataclasses import dataclass

from .checks import FREE_RUNNING, FULL_CASE_X, INFO, Check, Lemma, src_key
from .fsm import _Eval
from .netlist import FF_TYPES, Netlist, attr_true, const_value, is_const, param_int

COMPARE_TYPES = {"$eq", "$ne", "$eqx", "$nex", "$lt", "$le", "$gt", "$ge"}
MAX_PATHS = 64
MAX_BMUX = 64


def _mask(w: int) -> int:
    return (1 << w) - 1


def _const_eval(nl: Netlist) -> _Eval:
    """Constant evaluation of the netlist's combinational logic, kept with
    the netlist.  Elaboration runs no opt_expr (the structure is kept as
    written), so a select such as `ENABLE_IRQ && timer` with the parameter
    at 0 is a $logic_and with a constant input, not a constant bit."""
    ev = getattr(nl, "_const_eval", None)
    if ev is None:
        ev = nl._const_eval = _Eval(nl.mod, {})
    return ev


def clean_conds(conds, nl: Netlist | None = None):
    """Drop constant-true and duplicate conditions.  Returns None when the
    conditions can never hold (a constant mismatch or a contradiction): the
    logic is dead, so the check is skipped rather than reported.  With `nl`,
    a condition bit whose logic evaluates to a constant counts as that
    constant (parameter-disabled logic)."""
    out, seen = [], {}
    ev = _const_eval(nl) if nl is not None else None
    for b, v in conds:
        if ev is not None and not is_const(b):
            k = ev.bit(b)
            if k is not None:
                b = str(k)
        if is_const(b):
            if b in ("0", "1") and b != str(v):
                return None
            continue
        if b in seen:
            if seen[b] != v:
                return None
            continue
        seen[b] = v
        out.append((b, v))
    return out


def _bits_of(v: int, n: int):
    return [(v >> i) & 1 for i in range(n)]


# --------------------------------------------------------------- mux trees
def mux_sources(nl: Netlist, bits: list, conds=(), depth=0, out=None):
    """Enumerate the sources feeding `bits` through a $mux/$pmux/$bmux tree.

    Returns [(bits_of_source, conditions)], conditions being (select_bit,
    value) pairs that must hold for that source to be selected.  Infeasible
    paths (constant or contradictory selects) are dropped.  Beyond the path
    and depth limits a sub-tree is returned unexpanded, as one opaque source,
    so the result always accounts for every way a value can arrive (reset
    discovery relies on that).
    """
    if out is None:
        out = []
    if clean_conds(conds, nl) is None:
        return out
    if len(out) >= MAX_PATHS or depth > 24:
        out.append((bits, list(conds)))
        return out
    d = nl.whole_driver(bits)
    if d is None:
        out.append((bits, list(conds)))
        return out
    cell, port, off = d
    t = nl.ctype(cell)
    w = len(bits)
    if t == "$mux" and port == "Y":
        s = nl.conn(cell, "S")[0]
        mux_sources(nl, nl.conn(cell, "A")[off:off + w], list(conds) + [(s, 0)], depth + 1, out)
        mux_sources(nl, nl.conn(cell, "B")[off:off + w], list(conds) + [(s, 1)], depth + 1, out)
    elif t == "$pmux" and port == "Y":
        width = nl.param(cell, "WIDTH")
        sel = nl.conn(cell, "S")
        b = nl.conn(cell, "B")
        for i, sb in enumerate(sel):
            mux_sources(nl, b[i * width + off:i * width + off + w], list(conds) + [(sb, 1)], depth + 1, out)
        mux_sources(nl, nl.conn(cell, "A")[off:off + w], list(conds) + [(sb, 0) for sb in sel],
                    depth + 1, out)
    elif t == "$bmux" and port == "Y" and (1 << len(nl.conn(cell, "S"))) <= MAX_BMUX:
        width = nl.param(cell, "WIDTH")
        sel = nl.conn(cell, "S")
        a = nl.conn(cell, "A")
        for i in range(1 << len(sel)):
            c = list(conds) + list(zip(sel, _bits_of(i, len(sel))))
            mux_sources(nl, a[i * width + off:i * width + off + w], c, depth + 1, out)
    else:
        out.append((bits, list(conds)))
    return out


MAX_FORWARD = 256          # mux cells one forward() walk may visit across all branches


def _forward_step(nl: Netlist, cell: str, port: str, offs: list):
    """One step of forward(): ("ff", conditions, Q bits) into a register,
    ("mux", conditions, Y bits) through a mux data input, or None where the
    value meets other logic (or spans several inputs of one mux)."""
    t = nl.ctype(cell)
    if t in FF_TYPES and port == "D":
        q = nl.conn(cell, "Q")
        return "ff", list(nl.ff_info(cell)["conds"]), [q[o] for o in offs]
    if t == "$mux" and port in ("A", "B"):
        return "mux", [(nl.conn(cell, "S")[0], 0 if port == "A" else 1)], [nl.conn(cell, "Y")[o] for o in offs]
    if t == "$pmux" and port in ("A", "B"):
        width = nl.param(cell, "WIDTH")
        sel = nl.conn(cell, "S")
        if port == "A":
            return "mux", [(s, 0) for s in sel], [nl.conn(cell, "Y")[o] for o in offs]
        idx = {o // width for o in offs}
        if len(idx) != 1:
            return None
        i = idx.pop()
        return "mux", [(sel[i], 1)], [nl.conn(cell, "Y")[o - i * width] for o in offs]
    if t == "$bmux" and port == "A":
        width = nl.param(cell, "WIDTH")
        sel = nl.conn(cell, "S")
        idx = {o // width for o in offs}
        if len(idx) != 1:
            return None
        i = idx.pop()
        return "mux", list(zip(sel, _bits_of(i, len(sel)))), [nl.conn(cell, "Y")[o - i * width] for o in offs]
    return None


def _forward_walk(nl: Netlist, cur: list, conds: list, depth: int, budget: list):
    dest = None
    while depth > 0:
        depth -= 1
        if any(is_const(b) for b in cur):
            break
        used = [b for b in cur if nl.readers.get(b)]
        if not used:
            break                                        # nothing reads the value: stop here
        # Bits nothing reads (the top of a result stored in a narrower
        # register) don't matter: follow the others.
        cur = used
        readers, single = {}, True
        for b in cur:
            rs = nl.readers[b]
            if len(rs) != 1:
                single = False
            for cell, port, off in rs:
                readers.setdefault((cell, port), []).append(off)
        if single and len(readers) == 1:
            (cell, port), offs = next(iter(readers.items()))
            step = _forward_step(nl, cell, port, offs)
            if step is None:
                break
            kind, more, nxt = step
            conds = conds + more
            if kind == "ff":
                dest = nxt
                break
            cur = nxt
            continue
        # The value fans out: follow every branch, keep what all of them need.
        live = []
        for (cell, port), offs in readers.items():
            budget[0] -= 1
            step = _forward_step(nl, cell, port, offs) if budget[0] > 0 else None
            if step is None:
                live.append((clean_conds(conds, nl), cur))           # used by other logic as it is
            elif step[0] == "ff":
                live.append((clean_conds(conds + step[1], nl), step[2]))
            else:
                live.append(_forward_walk(nl, step[2], conds + step[1], depth, budget))
        live = [(c, d) for c, d in live if c is not None]
        if not live:
            return None, cur
        common = [cd for cd in live[0][0] if all(cd in c for c, _ in live[1:])]
        same = all(d == live[0][1] for _, d in live[1:])
        return common, (live[0][1] if same else cur)
    return clean_conds(conds, nl), (dest or cur)


def forward(nl: Netlist, bits: list, max_depth=16):
    """Follow `bits` through the mux trees that consume them.

    Returns (conditions, destination_bits): the conditions under which the
    value propagates, and where it ends up (a register's Q, or the net where
    the mux chain stops).  Where the value fans out into several mux trees,
    each branch is followed and only the conditions every branch needs are
    kept (a value written in one state of an FSM reaches the state register
    through several nested if/else muxes, all inside that state's case
    item).  conditions is None if the value can never propagate.
    """
    return _forward_walk(nl, list(bits), [], max_depth, [MAX_FORWARD])


# Yosys' names for a signal's intermediate values: `$0\q[3:0]` from proc (and
# `$flatten\u_x.$0\q`, `u_x.$0\q` once flattened), `$0$memwr$\mem$...` for
# the data a memory write port writes.
_PROC_TEMP = re.compile(r"^(?:\$flatten\\)?((?:[^$]*\.)?)\$\d+\\([^\[$]+)")
_MEMWR_TEMP = re.compile(r"^(?:\$flatten\\)?((?:[^$]*\.)?)\$\d+\$memwr\$\\([^$]+)\$")


def _written(name: str) -> bool:
    """A name as the user wrote it: not one Yosys made up ($procmux$7_Y), and
    not an intermediate value of a signal (u_x.$0\\q[3:0]), which is named
    in its last hierarchy component."""
    return bool(name) and not name.startswith("$") and "$" not in name.rsplit(".", 1)[-1]


def _label(name: str) -> str | None:
    """A net name as the user wrote it, or None for an anonymous net."""
    if not name:
        return None
    if _written(name):
        return name
    m = _MEMWR_TEMP.match(name) or _PROC_TEMP.match(name)
    return (m.group(1) + m.group(2)) if m else None


def _bits_label(nl: Netlist, bits: list) -> str | None:
    """The user's name for these bits: a visible net of exactly these bits,
    the one visible net they belong to, or the signal Yosys' intermediate
    names stand for."""
    if not bits:
        return None
    for name, n in nl.nets_for(bits):
        if not n.get("hide_name", 0) and _written(name):
            return name
    names = {nl.bit_name.get(b, "").rsplit("[", 1)[0] for b in bits if not is_const(b)}
    names.discard("")
    visible = {n for n in names if _written(n)}
    if len(visible) == 1:
        return visible.pop()
    labels = {_label(n) for n in names} - {None}
    if len(labels) == 1:
        return labels.pop()
    return None


def _dest_name(nl: Netlist, dest: list, fallback_bits: list, src: str) -> str:
    """Structural name for an anonymous object: the signal its value lands in."""
    for bits in (dest, fallback_bits):
        name = _bits_label(nl, bits)
        if name:
            return name
    return os.path.basename(src)


# ---------------------------------------------------------------- counters
def _operand_is(bits: list, q: list) -> bool:
    """bits == q, optionally zero-extended."""
    if len(bits) < len(q) or bits[:len(q)] != q:
        return False
    return all(b == "0" for b in bits[len(q):])


def _fit(bits: list, w: int):
    """Resize an operand to w bits if that loses nothing (zero-extension)."""
    if len(bits) >= w:
        return bits[:w] if all(b == "0" for b in bits[w:]) else None
    return bits + ["0"] * (w - len(bits))


def _signed_val(v: int, w: int) -> int:
    return v - (1 << w) if v >> (w - 1) & 1 else v


def _compares(nl: Netlist, q: list):
    """(constants, other-operand bit lists) that q is compared against."""
    ks, others = set(), []
    for cell in sorted(nl.compare_cells(q, COMPARE_TYPES)):
        a, b = nl.conn(cell, "A"), nl.conn(cell, "B")
        for x, y in ((a, b), (b, a)):
            if _operand_is(x, q):
                k = const_value(y)
                if k is not None:
                    ks.add(k)
                elif not any(b in q for b in y if not is_const(b)):
                    yy = _fit(y, len(q))
                    if yy is not None and yy not in others:
                        others.append(yy)
    return ks, others


# Flip-flop types whose value comes only from D, plus a constant reset value.
_PLAIN_FF = {"$dff": None, "$dffe": None, "$adff": "ARST_VALUE", "$adffe": "ARST_VALUE",
             "$sdff": "SRST_VALUE", "$sdffe": "SRST_VALUE", "$sdffce": "SRST_VALUE"}


def min_cycles_to_wrap(nl: Netlist, cell: str, q: list, paths, up: bool, step: int,
                       uninit: str = "zero") -> int | None:
    """A lower bound on the cycles before `q op step` can wrap, or None.

    Holds when every value the register can take next is itself (hold), a
    constant (a load or reset value), or itself plus or minus a constant,
    and its start value is known: then it moves at most the largest step per
    cycle away from the extreme load or start value.  A 64-bit instruction
    counter that only resets to 0 and adds 1 can't wrap in fewer than
    2^64 - 1 cycles.  Unsigned counters only; anything else gives None.

    A register that steps both ways can wrap the other way first (0 - 1 is
    all ones, one increment from overflowing), so then the bound is the
    cycles before the first wrap of any kind: until then the value stays
    within [lowest start - n * largest down step, highest start + n *
    largest up step].  None when that first wrap can come at once.  With
    steps in one direction only, wraps never help (an overflow only lowers
    the value), and the bound is for `q op step` itself."""
    t = nl.ctype(cell)
    if t not in _PLAIN_FF:
        return None
    w = len(q)
    mask = _mask(w)
    values, k_up, k_down = [], 0, 0
    if _PLAIN_FF[t]:
        values.append(nl.param(cell, _PLAIN_FF[t], 0))
    init = nl.net_attr(q, "init")
    if init is not None:
        try:
            values.append(param_int(init) & mask)
        except ValueError:
            return None                                  # an x in the initial value
    elif uninit == "zero":
        values.append(0)
    else:
        return None                                      # free power-up value
    for sbits, _ in paths:
        if sbits == q:
            continue                                     # hold
        k = const_value(sbits)
        if k is not None:
            values.append(k & mask)
            continue
        drv = nl.whole_driver(sbits)
        if drv is None:
            return None
        acell, aport, aoff = drv
        at = nl.ctype(acell)
        if aport != "Y" or aoff != 0 or at not in ("$add", "$sub"):
            return None
        if nl.param(acell, "A_SIGNED", 0) or nl.param(acell, "B_SIGNED", 0):
            return None
        a, b = nl.conn(acell, "A"), nl.conn(acell, "B")
        if _operand_is(a, q) and const_value(b) is not None:
            k = const_value(b)
        elif at == "$add" and _operand_is(b, q) and const_value(a) is not None:
            k = const_value(a)
        else:
            return None
        if k > mask:
            return None
        if at == "$add":
            k_up = max(k_up, k)
        else:
            k_down = max(k_down, k)
    if (k_up if up else k_down) <= 0:
        return None

    def cycles(gap, speed):                              # to get there, then the wrapping step
        return -(-gap // speed) + 1 if gap > 0 else None

    # q + k wraps when q > mask - k, and q grows by at most k_up a cycle;
    # q - k wraps when q < k, and q shrinks by at most k_down a cycle.
    if not k_down:
        return cycles((mask - step + 1) - max(values), k_up)
    if not k_up:
        return cycles(min(values) - (step - 1), k_down)
    bounds = [cycles((mask - k_up + 1) - max(values), k_up), cycles(min(values) - (k_down - 1), k_down)]
    return None if None in bounds else min(bounds)


def fmt_cycles(n: int) -> str:
    """A cycle count for messages: exact when small, else the power of two
    below it (still a true lower bound)."""
    if n < 1 << 20:
        return f"{n:,}"
    e = n.bit_length() - 1
    return f"2^{e}" if n == 1 << e else f"more than 2^{e}"


def detect_counters(nl: Netlist, max_level: int, uninit: str = "zero"):
    checks, lemmas = [], {}
    for cell, c in nl.cells.items():
        if c["type"] not in FF_TYPES or c["type"] == "$anyinit" or "D" not in c["connections"]:
            continue
        ff = nl.ff_info(cell)
        q, d = ff["Q"], ff["D"]
        w = len(q)
        if w < 2 or any(is_const(b) for b in q):
            continue
        paths = mux_sources(nl, d)
        steps = []      # (dir, step, signed, conds)
        loads = set()
        for sbits, conds in paths:
            k = const_value(sbits)
            if k is not None:
                loads.add(k)
                continue
            drv = nl.whole_driver(sbits)
            if drv is None:
                continue
            acell, aport, aoff = drv
            at = nl.ctype(acell)
            if aport != "Y" or aoff != 0 or at not in ("$add", "$sub"):
                continue
            a, b = nl.conn(acell, "A"), nl.conn(acell, "B")
            signed = bool(nl.param(acell, "A_SIGNED", 0)) and bool(nl.param(acell, "B_SIGNED", 0))
            if _operand_is(a, q) and const_value(b) is not None:
                steps.append(("up" if at == "$add" else "down", b, signed, conds))
            elif at == "$add" and _operand_is(b, q) and const_value(a) is not None:
                steps.append(("up", a, signed, conds))
        if not steps:
            continue

        name = nl.name_of(q)
        src = nl.net_src(q)
        if src == "?":
            src = nl.cell_src(cell)
        waive = nl.net_attr(q, "fvlint_waive")
        ks, others = _compares(nl, q)
        any_signed = False
        counts_up = False
        for direction, step_bits, signed, conds in steps:
            raw = const_value(step_bits)
            # A signed add of a negative constant is a decrement.
            if signed:
                step = _signed_val(raw & _mask(len(step_bits)), len(step_bits))
                if step < 0:
                    direction, step = ("down" if direction == "up" else "up"), -step
            else:
                step = raw
            if step <= 0 or step > _mask(w):
                continue
            all_conds = clean_conds(conds + ff["conds"], nl)
            if all_conds is None:
                continue
            any_signed |= signed
            counts_up |= direction == "up"
            # Free-running or not is judged on the conditions as written: a
            # compare that can never hold (q == 200 for a 7-bit q) still shows
            # the counter was meant to be bounded, so it is checked (and fails).
            raw = [b for b, _ in conds + ff["conds"] if not is_const(b)]
            bounded = nl.depends_on(raw, set(q), max_level)
            kind = "counter_overflow" if direction == "up" else "counter_underflow"
            if signed:
                smin, smax = -(1 << (w - 1)), (1 << (w - 1)) - 1
                lo, hi = (smin, smax - step) if direction == "up" else (smin + step, smax)
                desc = (f"signed {name} {'+' if direction == 'up' else '-'} {step} stays within "
                        f"{smin}..{smax}")
            else:
                lo, hi = (0, _mask(w) - step) if direction == "up" else (step, _mask(w))
                desc = (f"{name} + {step} never wraps past {_mask(w)} ({w} bits)" if direction == "up"
                        else f"{name} - {step} never wraps below 0")
            chk = Check(kind=kind, target=name, src=src, desc=desc, checker="fvl_range",
                        params={"W": w, "LO": lo, "HI": hi, "SIGNED": int(signed)},
                        ports={"v": q}, conds=all_conds, anchors=[cell], waive_attr=waive,
                        depth_hint=(1 << w) // step + 2,
                        min_cycles=None if signed else min_cycles_to_wrap(
                            nl, cell, q, paths, direction == "up", step, uninit))
            if not bounded:
                chk.preset, chk.reason = INFO, FREE_RUNNING
                chk.detail = ("free-running: the increment condition does not depend on the "
                              "counter, so wrap-around looks intentional; not checked")
            checks.append(chk)

        # Candidate invariants (Houdini-filtered later): q <= K for the
        # constants q is compared against (largest first: the clearing/limit
        # compare usually bounds the counter), the largest load value of a
        # counter that only counts down, and q <= r for signals q is compared
        # with.  Values are taken in the counter's own (signed or unsigned)
        # domain; q <= min and q <= max say nothing useful about a counter and
        # are skipped.  Kept small on purpose: each false candidate costs
        # solver queries.
        val = (lambda k: _signed_val(k, w)) if any_signed else (lambda k: k)
        lo_end, hi_end = ((-(1 << (w - 1)), (1 << (w - 1)) - 1) if any_signed else (0, _mask(w)))
        useful = lambda k: lo_end < val(k) < hi_end  # noqa: E731
        cands = sorted({k for k in ks if useful(k)}, key=val, reverse=True)[:3]
        top_load = max(loads, key=val) if loads else None
        if not counts_up and top_load is not None and useful(top_load) and top_load not in cands:
            cands.append(top_load)
        for k in cands:
            lemmas.setdefault(cell, []).append(Lemma(
                owner=cell, desc=f"{name} <= {val(k)}", checker="fvl_range",
                params={"W": w, "LO": lo_end, "HI": val(k), "SIGNED": int(any_signed)},
                ports={"v": q}, bound=k))
        # Whole signals first (a zero-extended slice is a weaker bound), then
        # by name: the choice must not depend on cell names or set order.
        ranked = sorted(others, key=lambda r: (sum(is_const(b) for b in r), nl.name_of(r)))
        for r in ranked[:2]:
            lemmas.setdefault(cell, []).append(Lemma(
                owner=cell, desc=f"{name} <= {nl.name_of(r)}", checker="fvl_rel",
                params={"W": w, "SIGNED": int(any_signed)}, ports={"a": q, "b": r}))
    return _dedupe(checks), lemmas


# ------------------------------------------------------------ case / pmux
def _guard(nl: Netlist, conds) -> str | None:
    """The innermost `signal == constant` among path conditions, as
    `@signal=W'bCODE`: where a case statement sits inside an FSM's case.
    The same reading of a condition as fsm.dead_in_unreachable_states
    (Netlist.equality), so a name and a dead state can't disagree."""
    for bit, value in conds:
        hit = nl.equality(bit, value)
        if hit is None:
            continue
        x, k = hit
        name = nl.visible_name(x)
        if name and k < (1 << len(x)):
            return f"@{name}={len(x)}'b{format(k, f'0{len(x)}b')}"
    return None


def _statement_name(names: list, src: str, instance: str = "") -> str:
    """Name of a case statement from the signals it assigns (sorted; past
    four, the first three and a count).  One that assigns no named signal
    is named after its source line, in its instance."""
    if not names:
        return f"{instance}.{os.path.basename(src)}" if instance else os.path.basename(src)
    if len(names) <= 4:
        return ",".join(names)
    return ",".join(names[:3]) + f",+{len(names) - 3}"


@dataclass
class _Part:
    """One $pmux of a case statement: Yosys makes one per signal assigned."""
    cell: str
    conds: list                   # path conditions from forward()
    signal: str | None            # the signal it assigns, None if it has no name


@dataclass
class _Statement:
    target: str                   # the check id's target
    src: str
    instance: str                 # hierarchy path of the instance it is in ('' at the top)
    parts: list                   # [_Part]


def _case_statements(nl: Netlist) -> list:
    """The parallel_case statements of the netlist, unnamed: their $pmux
    cells grouped by source location and instance (after flatten, every
    instance of a module has the same `src`)."""
    stmts = {}                                           # (src attribute, instance) -> [_Part]
    for cell, c in nl.cells.items():
        if c["type"] != "$pmux":
            continue
        attrs = c.get("attributes", {})
        if not attr_true(attrs.get("parallel_case")):
            continue
        sel = nl.conn(cell, "S")
        if len(sel) < 2 or all(is_const(b) for b in sel):
            continue
        y = nl.conn(cell, "Y")
        conds, dest = forward(nl, y)
        if conds is None:
            continue   # the case result is never used (constant-disabled logic)
        src = nl.cell_src(cell)
        name = _dest_name(nl, dest, y, src)
        stmts.setdefault((attrs.get("src") or cell, nl.instance(cell)), []).append(
            _Part(cell, conds, None if name == os.path.basename(src) else name))
    return [_Statement("", nl.cell_src(parts[0].cell), inst, parts) for (_, inst), parts in stmts.items()]


def _name_statements(nl: Netlist, stmts: list):
    """Set each statement's target: the signals it assigns; statements that
    would share a name are told apart by the FSM state they sit in, then by
    number in source order."""
    for st in stmts:
        st.target = _statement_name(sorted({p.signal for p in st.parts if p.signal}), st.src, st.instance)
    by_name = {}
    for st in stmts:
        by_name.setdefault(st.target, []).append(st)
    for group in by_name.values():
        if len(group) < 2:
            continue
        for st in group:
            # The parts sit in the same place in the source; take the guard
            # most of them see (ties: the first by name).
            guards = [g for g in (_guard(nl, p.conds) for p in st.parts) if g]
            if guards:
                st.target += min(set(guards), key=lambda g: (-guards.count(g), g))
    by_name = {}
    for st in stmts:
        by_name.setdefault(st.target, []).append(st)
    for group in by_name.values():
        for n, st in enumerate(sorted(group, key=lambda st: (src_key(st.src), st.instance))):
            if n:
                st.target = f"{st.target}#{n}"


def _statement_checks(nl: Netlist, st: _Statement, kind: str) -> list:
    """The part checks of one statement: one per $pmux, grouped under the
    statement's id when there are several."""
    mine = []
    for part in st.parts:
        sel = nl.conn(part.cell, "S")
        if kind == "parallel_case":
            chk = Check(kind=kind, target=st.target, src=st.src,
                        desc="at most one item of a unique/parallel_case statement matches",
                        checker="fvl_onehot0", params={"W": len(sel)}, ports={"s": sel}, conds=part.conds)
        else:
            # full_case from the source (renamed at elaboration; proc_rmdead
            # also marks every case that has a default item).  Yosys
            # implements it as an 'x default: when no item that assigns the
            # signal matches, the synthesized value is arbitrary, while
            # simulation keeps the value the code assigned before the case.
            a = nl.conn(part.cell, "A")
            attrs = nl.cells[part.cell].get("attributes", {})
            if not (attr_true(attrs.get("fvlint_full_case")) and a and all(b == "x" for b in a)):
                continue
            chk = Check(kind=kind, target=st.target, src=st.src,
                        desc="an item of a full_case/unique case statement (no default) assigns the signal",
                        checker="fvl_nonzero", params={"W": len(sel)}, ports={"s": sel}, conds=part.conds)
        chk.part = part.signal or part.cell
        mine.append(chk)
    if len(mine) > 1:
        for i, chk in enumerate(mine):
            chk.group = chk.id
            chk.target = f"{st.target}~{i}"
    return mine


def detect_case(nl: Netlist):
    """parallel_case and full_case checks, one per case statement.

    Yosys turns a case statement into one $pmux per signal it assigns, so
    the property is proven for each of them; a statement with several gets
    one part check per signal, all with the statement's id in `group` (the
    report merges them).  A statement is named after the signals it assigns;
    statements that would share a name are told apart by the FSM state they
    sit in (`@cpu_state=8'b00010000`), then by number in source order."""
    stmts = _case_statements(nl)
    _name_statements(nl, stmts)
    checks = []
    for st in sorted(stmts, key=lambda st: (src_key(st.src), st.instance)):
        for kind in ("parallel_case", "full_case"):
            checks += _statement_checks(nl, st, kind)
    return checks


def harmless_full_case(checks: list, nl_nofc: Netlist) -> int:
    """full_case checks whose pragma changes nothing: in `nl_nofc`, the same
    design elaborated without full_case pragmas, the signal's value when no
    item matches is 'x as well, because the code sets it to 'x before the
    case (PicoRV32's `alu_out_0 = 'bx; case ...`).  Simulation then gives 'x
    too, so synthesis's freedom costs nothing: INFO, not checked.  Matched
    by source line, signal and item count; anything ambiguous keeps its
    check.  Returns how many."""
    defaults = {}
    for cell, c in nl_nofc.cells.items():
        if c["type"] != "$pmux" or not attr_true(c.get("attributes", {}).get("parallel_case")):
            continue
        sel = nl_nofc.conn(cell, "S")
        y = nl_nofc.conn(cell, "Y")
        conds, dest = forward(nl_nofc, y)
        if conds is None:
            continue
        src = nl_nofc.cell_src(cell)
        name = _dest_name(nl_nofc, dest, y, src)
        a = nl_nofc.conn(cell, "A")
        defaults.setdefault((src, name, len(sel)), []).append(bool(a) and all(b == "x" for b in a))
    n = 0
    for c in checks:
        if c.kind != "full_case" or c.preset is not None:
            continue
        found = defaults.get((c.src, c.part, c.params.get("W")))
        if found == [True]:
            c.preset, c.reason = INFO, FULL_CASE_X
            c.detail = (f"the code sets {c.part} to 'x before the case, so when no item matches simulation "
                        "gives 'x just as synthesis may: the full_case pragma changes nothing; not checked")
            n += 1
    return n


# ------------------------------------------------------- part-select index
def detect_index(nl: Netlist):
    checks = []
    for cell, c in nl.cells.items():
        if c["type"] != "$shiftx":
            continue
        b = nl.conn(cell, "B")
        if all(is_const(x) for x in b):
            continue
        a, y = nl.conn(cell, "A"), nl.conn(cell, "Y")
        aw, yw = len(a), len(y)
        hi = aw - yw
        if hi < 0:
            continue
        bw = len(b)
        signed = nl.param(cell, "B_SIGNED", 0)
        # The offset is checked with an unsigned compare against 0..HI, which
        # also rejects negative signed offsets (MSB set) as long as HI is
        # below the sign bit; so HI is clamped to the largest offset B can
        # express.  An unsigned offset that can never exceed hi needs no check.
        top = (1 << (bw - 1)) - 1 if signed else _mask(bw)
        if not signed and hi >= top:
            continue
        conds, dest = forward(nl, y)
        if conds is None:
            continue
        src = nl.cell_src(cell)
        checks.append(Check(
            kind="index_range", target=_dest_name(nl, dest, y, src), src=src,
            desc=f"variable select offset stays within 0..{hi} ({aw}-bit vector, {yw}-bit slice)",
            checker="fvl_range", params={"W": bw, "LO": 0, "HI": min(hi, top), "SIGNED": 0},
            ports={"v": b}, conds=conds))
    return _dedupe(checks)


# ------------------------------------------------------ shifts and division
def _zero_top(bits: list) -> int:
    """How many of the top bits are constant 0."""
    n = 0
    for b in reversed(bits):
        if b != "0":
            break
        n += 1
    return n


def _max_value(bits: list) -> int:
    """The largest unsigned value bits can take: constant 0 bits stay 0."""
    return sum(1 << i for i, b in enumerate(bits) if b != "0")


SHIFT_TYPES = {"$shl": "left", "$sshl": "left", "$shr": "right", "$sshr": "right"}
DIV_TYPES = {"$div": "quotient", "$divfloor": "quotient", "$mod": "remainder", "$modfloor": "remainder"}


def detect_shift(nl: Netlist):
    """A shift by a variable amount that can move every bit out: past the
    result's width for a left shift, past the bits of the shifted value that
    can carry data for a right shift (the amount is unsigned, as Verilog and
    Yosys treat it)."""
    checks = []
    for cell, c in nl.cells.items():
        way = SHIFT_TYPES.get(c["type"])
        if not way:
            continue
        b = nl.conn(cell, "B")
        if all(is_const(x) for x in b):
            continue
        a, y = nl.conn(cell, "A"), nl.conn(cell, "Y")
        # A right shift loses the value once it is past the bits that can
        # carry data: constant 0 bits on top (`{24'b0, x} >> n`, or a value
        # Yosys widened to the result) don't count.
        width = len(y) if way == "left" else len(a) - _zero_top(a)
        if width == 0 or _max_value(b) < width:
            continue                                     # the amount can't reach the width
        conds, dest = forward(nl, y)
        if conds is None:
            continue
        src = nl.cell_src(cell)
        checks.append(Check(
            kind="shift_range", target=_dest_name(nl, dest, y, src), src=src,
            desc=f"{way} shift amount stays within 0..{width - 1} (a {width}-bit "
                 f"{'result' if way == 'left' else 'value'}: more shifts every bit out)",
            checker="fvl_range", params={"W": len(b), "LO": 0, "HI": width - 1, "SIGNED": 0},
            ports={"v": b}, conds=conds))
    return _dedupe(checks)


def detect_div(nl: Netlist):
    """Division or modulo by a variable that can be zero where the result is
    used (Verilog gives 'x; hardware gives whatever the divider does)."""
    checks = []
    for cell, c in nl.cells.items():
        what = DIV_TYPES.get(c["type"])
        if not what:
            continue
        b = nl.conn(cell, "B")
        if all(is_const(x) for x in b) or "1" in b:
            continue                                     # constant, or a bit that is always 1
        y = nl.conn(cell, "Y")
        conds, dest = forward(nl, y)
        if conds is None:
            continue
        src = nl.cell_src(cell)
        checks.append(Check(
            kind="div_zero", target=_dest_name(nl, dest, y, src), src=src,
            desc=f"divisor is never 0 where the {what} is used",
            checker="fvl_nonzero", params={"W": len(b)}, ports={"s": b}, conds=conds))
    return _dedupe(checks)


# ----------------------------------------------------------------- memory
def detect_memory(nl: Netlist):
    checks = []
    for cell, c in nl.cells.items():
        if c["type"] != "$mem_v2":
            continue
        size = nl.param(cell, "SIZE")
        offset = nl.param(cell, "OFFSET", 0)
        abits = nl.param(cell, "ABITS")
        width = nl.param(cell, "WIDTH")
        if offset == 0 and size >= (1 << abits):
            continue  # every address is valid
        lo, hi = offset, offset + size - 1
        memid = nl.param(cell, "MEMID", cell)
        if isinstance(memid, str):
            memid = memid.lstrip("\\")
        src = nl.cell_src(cell)
        waive = nl.attrs(cell).get("fvlint_waive")
        rd_addr, rd_en, rd_data = nl.conn(cell, "RD_ADDR"), nl.conn(cell, "RD_EN"), nl.conn(cell, "RD_DATA")
        for i in range(nl.param(cell, "RD_PORTS", 0)):
            addr = rd_addr[i * abits:(i + 1) * abits]
            if all(is_const(x) for x in addr):
                continue
            en = rd_en[i:i + 1] if rd_en else ["1"]
            conds, _ = forward(nl, rd_data[i * width:(i + 1) * width])
            if conds is None or en == ["0"]:
                continue
            checks.append(Check(
                kind="mem_addr", target=f"{memid}.rd{i}", src=src,
                desc=f"read address of {memid}[{lo}:{hi}] stays in range", checker="fvl_range",
                params={"W": abits, "LO": lo, "HI": hi, "SIGNED": 0}, ports={"v": addr, "e": en},
                conds=conds, waive_attr=waive))
        wr_addr, wr_en = nl.conn(cell, "WR_ADDR"), nl.conn(cell, "WR_EN")
        for i in range(nl.param(cell, "WR_PORTS", 0)):
            addr = wr_addr[i * abits:(i + 1) * abits]
            en = wr_en[i * width:(i + 1) * width]
            if all(is_const(x) for x in addr) or all(b == "0" for b in en):
                continue
            checks.append(Check(
                kind="mem_addr", target=f"{memid}.wr{i}", src=src,
                desc=f"write address of {memid}[{lo}:{hi}] stays in range", checker="fvl_range",
                params={"W": abits, "LO": lo, "HI": hi, "SIGNED": 0}, ports={"v": addr, "e": en},
                waive_attr=waive))
    return checks


def _dedupe(checks):
    """Several objects with the same structural name (e.g. two case statements
    assigning one register) get '#n' suffixes in source order."""
    groups = {}
    for chk in checks:
        groups.setdefault(chk.id, []).append(chk)
    for group in groups.values():
        if len(group) > 1:
            for n, chk in enumerate(sorted(group, key=lambda c: src_key(c.src))):
                if n:
                    chk.target = f"{chk.target}#{n}"
    return checks


def detect_all(nl: Netlist, max_level: int, uninit: str = "zero"):
    counters, lemmas = detect_counters(nl, max_level, uninit)
    checks = counters + detect_case(nl) + detect_index(nl) + detect_shift(nl) + detect_div(nl) + detect_memory(nl)
    return checks, lemmas
