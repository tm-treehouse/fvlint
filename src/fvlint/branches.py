# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Dead branches: if/else arms, case items and ?: choices whose condition
never holds after reset (--dead-branches).

Yosys turns each of them into an input of a $mux or $pmux.  An arm's
condition is its select value plus the path conditions under which the
mux's result is used at all (detect.forward: the enclosing ifs and case
items, a register's enable).  Those path conditions are necessary ones, so
the condition checked is never stronger than the real one: if it can't
hold, the arm is dead.

The proof runs the other way round from other checks: the engine tries to
prove that the condition never holds (checker fvl_reach).  A proof, on a
slice or not, means a dead branch (WARN); a counterexample on the full cone
is a trace that takes the branch (PROVEN: live).  Most branches are taken
within a few cycles, and the engine finds those first, with one bounded
search over many of them (Engine._reach_first).

Left out: the default item of a case statement (a defensive default is dead
on purpose), arms that only matter while a reset is active, selects that
are constant once the resets are inactive (`if (rst)` muxes), Yosys'
placeholder arms (all 'x), and arms whose select bit appears in their own
path with the other value (`if (a) if (a) ... else ...`: dead by
construction).  A contradiction through different cells (`if (a && b) if
(!(a && b))`) is checked, and proven dead, like any other branch.  A case
item that only matches when an earlier item matches too counts as taken:
Yosys gives every item its own compare.
"""

from __future__ import annotations

import re

from .checks import FAIL, PROVEN, REACH, UNKNOWN, WARN, Check, src_key
from .detect import _dedupe, _dest_name, _guard, _written, clean_conds, forward
from .fsm import _Eval
from .netlist import Netlist, const_value, is_const

MAX_EXPR = 200           # longest condition kept as Verilog (results.json "condition")
MAX_TARGET = 60          # longest condition used as a check's name

DESC = "the branch is taken in some state reachable from reset"

_COMPARE = {"$eq": "==", "$eqx": "==", "$ne": "!=", "$nex": "!=", "$lt": "<", "$le": "<=",
            "$gt": ">", "$ge": ">="}
_NEGATED = {"==": "!=", "!=": "==", "<": ">=", ">=": "<", "<=": ">", ">": "<="}
_MIRRORED = {"==": "==", "!=": "!=", "<": ">", ">": "<", "<=": ">=", ">=": "<="}
_LOGIC = {"$logic_and": "&&", "$logic_or": "||", "$and": "&&", "$or": "||", "$xor": "^"}


# ------------------------------------------------------------ conditions
def _named_bits(nl: Netlist) -> dict:
    """bit -> (net name, index, width) over the nets with a name as the user
    wrote it; the innermost, then shortest name wins (as Netlist ranks them),
    except that a top-level port comes last: an output that concatenates
    registers (`assign o = {a, b}`) is no name for them."""
    m = getattr(nl, "_fvl_named_bits", None)
    if m is None:
        m = {}
        nets = sorted(((n, x) for n, x in nl.netnames.items() if not x.get("hide_name", 0) and _written(n)),
                      key=lambda kv: (-kv[0].count("."), kv[0] in nl.ports, len(kv[0]), kv[0]))
        for name, x in nets:
            for i, b in enumerate(x["bits"]):
                if not is_const(b):
                    m.setdefault(b, (name, i, len(x["bits"])))
        nl._fvl_named_bits = m
    return m


def render_vec(nl: Netlist, bits: list, signed: bool = False) -> str | None:
    """A vector as Verilog: a sized constant, a named net, or a slice of one.
    Zero bits on top of an unsigned value (Yosys' extension to an operand's
    width) are dropped: Verilog extends it the same way."""
    bits = list(bits)
    if not bits:
        return None
    if all(b in ("0", "1") for b in bits):
        return f"{len(bits)}'d{const_value(bits)}"
    if not signed:
        while len(bits) > 1 and bits[-1] == "0":
            bits.pop()
    if any(is_const(b) for b in bits):
        return None
    for n, x in nl.nets_for(bits):                 # a net of exactly these bits
        if not x.get("hide_name", 0) and _written(n):
            return n
    named = _named_bits(nl)
    first = named.get(bits[0])
    if first is None:
        return None
    name, lo, width = first
    if any(named.get(b) != (name, lo + k, width) for k, b in enumerate(bits)):
        return None
    hi = lo + len(bits) - 1
    return f"{name}[{lo}]" if hi == lo else f"{name}[{hi}:{lo}]"


def _bool(nl: Netlist, bits: list, depth: int) -> str | None:
    """A vector used as a condition (nonzero)."""
    if all(b in ("0", "1") for b in bits):
        return "1'b1" if "1" in bits else "1'b0"            # a parameter: `P && x`
    if len(bits) == 1:
        return render_bit(nl, bits[0], depth)
    v = render_vec(nl, bits)
    return f"(|{v})" if v else None


def render_bit(nl: Netlist, b, depth: int = 0, negate: bool = False) -> str | None:
    """A 1-bit condition as a Verilog expression over named signals, or None.
    With negate, a compare comes back with the opposite operator."""
    if b in ("0", "1"):
        return f"1'b{b}"
    if is_const(b) or depth > 8:
        return None
    v = render_vec(nl, [b])
    if v is not None:
        return v
    d = nl.driver.get(b)
    if d is None or d.port != "Y":
        return None
    t = nl.ctype(d.cell)
    a, bb = nl.conn(d.cell, "A"), nl.conn(d.cell, "B")
    if t == "$logic_not" and len(a) > 1:                 # slang's `v == 0`
        v = render_vec(nl, a)
        return f"({v} {'!=' if negate else '=='} {len(a)}'d0)" if v else None
    if t == "$logic_not" or (t == "$not" and len(a) == 1 and d.offset == 0):
        x = _bool(nl, a, depth + 1)
        return f"!{x}" if x else None
    if d.offset != 0:
        return None
    if t in ("$logic_and", "$logic_or") or (t in _LOGIC and len(a) == len(bb) == 1):
        x, y = _bool(nl, a, depth + 1), _bool(nl, bb, depth + 1)
        if not (x and y):
            return None
        op = _LOGIC[t]
        unit = {"&&": "1'b1", "||": "1'b0"}.get(op)          # a parameter that changes nothing: `x && 1'b1`
        if unit in (x, y) and x != y:
            return y if x == unit else x
        return f"({x} {op} {y})"
    if t in ("$reduce_or", "$reduce_bool"):
        x = _bool(nl, a, depth + 1)
        if x is None and 1 < len(a) <= 8:                   # a case item for several values
            parts = [render_bit(nl, bit, depth + 1) for bit in a]
            x = f"({' || '.join(parts)})" if None not in parts else None
        return x
    if t == "$reduce_and":
        if len(a) == 1:
            return render_bit(nl, a[0], depth + 1)
        v = render_vec(nl, a)
        return f"(&{v})" if v else None
    if t in _COMPARE:
        return _compare(nl, d.cell, _NEGATED[_COMPARE[t]] if negate else _COMPARE[t], depth)
    return None


def _operand(nl: Netlist, bits: list, signed: bool, depth: int) -> tuple:
    """(Verilog, width) of a compare operand; a constant keeps its width."""
    bits = list(bits)
    if not signed and not all(b in ("0", "1") for b in bits):
        while len(bits) > 1 and bits[-1] == "0":
            bits.pop()
    if len(bits) == 1 and not is_const(bits[0]):
        return render_bit(nl, bits[0], depth + 1), 1        # a condition: (1'b1 == !in2)
    return render_vec(nl, bits, signed), len(bits)


def _compare(nl: Netlist, cell: str, op: str, depth: int) -> str | None:
    """A compare as Verilog, the constant on the right; a 1-bit operand
    compared with 0 or 1 (`case (1'b1)` items) is the bit itself."""
    signed = bool(nl.param(cell, "A_SIGNED", 0)) and bool(nl.param(cell, "B_SIGNED", 0))
    a, b = nl.conn(cell, "A"), nl.conn(cell, "B")
    (x, wx), (y, wy) = _operand(nl, a, signed, depth), _operand(nl, b, signed, depth)
    if not (x and y):
        return None
    if re.fullmatch(r"\d+'d\d+", x) and not re.fullmatch(r"\d+'d\d+", y):
        x, y, wx, op = y, x, wy, _MIRRORED[op]
    k = re.fullmatch(r"\d+'d([01])", y)
    if wx == 1 and k and op in ("==", "!=") and not signed:
        return x if (k.group(1) == "1") == (op == "==") else _not(x)
    if signed:
        x, y = f"$signed({x})", f"$signed({y})"
    return f"({x} {op} {y})"


def _not(x: str) -> str:
    """The negation of an expression render_bit made."""
    if x.startswith("!") and _atomic(x[1:]):
        return x[1:]
    return f"!{x}" if _atomic(x) else f"!({x})"


def render_cond(nl: Netlist, bit, value: int) -> str | None:
    """The condition `bit == value` as Verilog, or None."""
    if not value:
        d = nl.driver.get(bit)
        if d is not None and d.port == "Y" and d.offset == 0 and (
                nl.ctype(d.cell) in _COMPARE or (nl.ctype(d.cell) == "$logic_not" and len(nl.conn(d.cell, "A")) > 1)):
            return render_bit(nl, bit, negate=True)
    x = render_bit(nl, bit)
    return x if x is None or value else _not(x)


def _atomic(x: str) -> bool:
    """A name, a select of one or an expression in one pair of parentheses."""
    if re.fullmatch(r"[\w.$\\]+(\[[\d:]+\])?", x):
        return True
    if not (x.startswith("(") and x.endswith(")")):
        return False
    level = 0
    for i, ch in enumerate(x):
        level += {"(": 1, ")": -1}.get(ch, 0)
        if level == 0 and i < len(x) - 1:
            return False
    return True


def condition(nl: Netlist, conds: list) -> str | None:
    """All of `conds` as one Verilog expression, or None if one has no
    rendering or the whole is too long."""
    parts = [render_cond(nl, b, v) for b, v in conds]
    if not parts or None in parts:
        return None
    parts = list(dict.fromkeys(parts))           # two compare cells for one compare in the source
    text = parts[0][1:-1] if len(parts) == 1 and parts[0].startswith("(") and _atomic(parts[0]) else \
        " && ".join(parts)
    return text if len(text) <= MAX_EXPR else None


def _target(expr: str | None) -> str | None:
    """A check name from a condition: no spaces, no outer parentheses."""
    if expr is None:
        return None
    t = expr.replace(" ", "")
    if t.startswith("(") and _atomic(t):
        t = t[1:-1]
    return t if len(t) <= MAX_TARGET else None


# -------------------------------------------------------------- detection
def _pinned(conds: list, ev: _Eval) -> list | None:
    """Path conditions with the ones the inactive resets decide removed;
    None if one needs a reset active."""
    out = []
    for b, v in conds:
        k = ev.bit(b)
        if k is None:
            out.append((b, v))
        elif k != v:
            return None
    return out


def _arm_cell(nl: Netlist, cell: str, sel_bit) -> str:
    """The cell whose source location is where an arm is written: a case
    item's compare, else the mux (the if)."""
    d = nl.driver.get(sel_bit)
    if d is not None and nl.ctype(cell) == "$pmux" and "$procmux$" in d.cell:
        return d.cell
    return cell


def _cond_key(nl: Netlist, cond: tuple):
    """What tells conditions apart: their Verilog (Yosys gives every mux of a
    case statement its own compare cells, all reading the same), else the bit."""
    return render_cond(nl, *cond) or cond


_SRC_LINE = re.compile(r"^.*?:(\d+)\.\d+-")


def _case_fallthrough(nl: Netlist, cell: str) -> bool:
    """A $mux that Yosys made for the last item of a case statement (one that
    tests a single bit, `3'b??1:`): its other input is what happens when no
    item matches, the implicit default.  Its source location is the item's,
    then the statement's; a case item sits below the `case` line, where an
    if's condition is on the line its statement starts."""
    parts = str(nl.attrs(cell).get("src") or "").split("|")
    if len(parts) != 2:
        return False
    lines = [_SRC_LINE.match(p) for p in parts]
    return all(lines) and lines[0].group(1) != lines[1].group(1)


def detect_branches(nl: Netlist, inactive: dict) -> list:
    """dead_branch checks, one per distinct branch condition.  `inactive`:
    reset bit -> its inactive value (Resets.inactive_conds).

    Yosys makes one mux per signal a branch assigns, all with the same select
    and source location; the branch is taken when any of them takes that
    arm, so its condition is what all of their arms need (a register may
    store one of the signals only in some states, while an output uses
    another all the time)."""
    ev = _Eval(nl.mod, dict(inactive))
    groups = {}                                 # (select, value, src, instance) -> branch
    for cell in nl.cells:
        t = nl.ctype(cell)
        if t not in ("$mux", "$pmux"):
            continue
        sel, y = nl.conn(cell, "S"), nl.conn(cell, "Y")
        a, b, w = nl.conn(cell, "A"), nl.conn(cell, "B"), len(y)
        if t == "$mux":
            choices = [(sel[0], 0, a, "else"), (sel[0], 1, b, "then")]
        else:
            choices = [(s, 1, b[i * w:(i + 1) * w], "item") for i, s in enumerate(sel)]
        choices = [ch for ch in choices
                   if not is_const(ch[0]) and ev.bit(ch[0]) is None and not all(x == "x" for x in ch[2])]
        if not choices:
            continue
        path, dest = forward(nl, y)
        if path is None:
            continue
        path = _pinned(path, ev)
        if path is None:
            continue
        for s, v, _, arm in choices:
            if arm == "else" and _case_fallthrough(nl, cell):
                continue
            conds = clean_conds([(s, v)] + path, nl)
            if conds is None:                    # this mux never takes it: `if (a) if (!a)`
                continue
            where = _arm_cell(nl, cell, s)
            g = groups.setdefault((str(nl.attrs(where).get("src") or ""), _cond_key(nl, (s, v)), nl.instance(cell)),
                                  {"own": (s, v), "arm": arm, "src": nl.cell_src(where), "dest": dest,
                                   "y": y, "conds": conds, "dests": []})
            mine = {_cond_key(nl, c) for c in conds}
            g["conds"] = [c for c in g["conds"] if _cond_key(nl, c) in mine]
            g["dests"].append(dest)
    arms = {}                                   # frozenset(conditions) -> branch
    for g in groups.values():
        key = frozenset(g["conds"])
        ent = arms.get(key)
        if ent is None or src_key(g["src"]) < src_key(ent["src"]):
            if ent is not None:
                g["dests"] = ent["dests"] + g["dests"]
            arms[key] = g
        else:
            ent["dests"] += g["dests"]
    checks = []
    for ent in arms.values():
        s, v = ent["own"]
        own = render_cond(nl, s, v)
        path = [c for c in ent["conds"] if c != (s, v)]
        name = _target(own) or f"{_dest_name(nl, ent['dest'], ent['y'], ent['src'])}:{ent['arm']}"
        waive = next((w for w in (nl.net_attr(d, "fvlint_waive") for d in ent["dests"] if d) if w), None)
        chk = Check(kind="dead_branch", target=name, src=ent["src"], desc=DESC, checker=REACH,
                    conds=ent["conds"], waive_attr=waive, condition=condition(nl, [(s, v)] + path))
        checks.append((chk, _guard(nl, path) or ""))
    _name(checks)
    return sorted((c for c, _ in checks), key=lambda c: (src_key(c.src), c.id))


def _name(checks: list):
    """Arms with the same condition in different places ([(check, guard)]):
    told apart by the FSM state they sit in (the guard), then by number in
    source order (detect._dedupe)."""
    by_id = {}
    for c, guard in checks:
        by_id.setdefault(c.id, []).append((c, guard))
    for group in by_id.values():
        if len(group) > 1:
            for c, guard in group:
                c.target += guard
    _dedupe([c for c, _ in checks])


# --------------------------------------------------------------- verdicts
def reach_verdicts(results: list):
    """Turn the engine's verdicts on reachability checks into dead-branch
    results: a counterexample is a trace that takes the branch (PROVEN: the
    branch is live); a proof that the condition never holds is a dead branch
    (WARN)."""
    for r in results:
        if not r.check.reach:
            continue
        if r.status == FAIL:
            r.status = PROVEN
            how = "found by a bounded search on the full cone" if r.engine == "BMC" else "confirmed on the full cone"
            r.detail = f"live: taken at step {r.step} ({how}; the trace is the witness)"
        elif r.status == PROVEN:
            r.status = WARN
            cond = f"`{r.check.condition}`" if r.check.condition else "the branch condition"
            r.detail = f"dead: {cond} never holds after reset; {r.detail}"
        elif r.status == UNKNOWN:
            r.detail = f"neither taken nor proven dead: {r.detail}"

