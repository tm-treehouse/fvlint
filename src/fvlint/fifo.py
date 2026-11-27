# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""FIFO checks: no write when full, no read when empty.

A FIFO here is a memory with one write port whose write address comes from
a register (the write pointer) and one of whose read ports reads at another
register (the read pointer), both on the memory's write clock.  Each pointer
may only hold, add 1, or go back to 0 from the memory's last entry (its
wrap); a reset is allowed, a flush (a pointer loaded in mid-run) is not,
and makes the memory no FIFO for these checks.  A pointer may be wider than
the address (an extra wrap bit).

The checker (fvl_fifo) keeps its own count of the entries held: +1 when the
write pointer moves, -1 when the read pointer moves, 0 while the pointers
are reset (by the FIFO's own reset: another reset that is released later,
a synchronized copy, must not lose a move; both pointers must reset alike).
Violations are judged while no reset is active, as for every check.

fifo_overflow: a write without a read while DEPTH entries are held (it
overwrites one that was never read).  fifo_underflow: a read while none is
held.  After the first of either, the count no longer matches the FIFO, so
later events aren't judged: a trace has at most one violation, and the
check of its kind reports it.  How the design itself tracks full and empty
(a count, flags, an extra pointer bit) doesn't matter; the proof relates it
to the count.
"""

from __future__ import annotations

from dataclasses import dataclass

from .branches import _pinned
from .checks import FIFO_POINTER, INFO, Check
from .detect import FF_TYPES, _operand_is, mux_sources
from .fsm import _Eval
from .netlist import Netlist, const_value

FIFO = "fvl_fifo"
_POINTER_FF = ("$dff", "$adff", "$aldff")          # $aldff: slang's asynchronous reset (a constant load)


@dataclass
class Pointer:
    cell: str
    clk: object
    d: list
    q: list
    reset: frozenset          # the conditions under which the pointer is reset (empty: never)
    natural: bool             # wraps by overflowing its width (no explicit wrap to 0)


def _increment(nl: Netlist, bits: list, q: list) -> bool:
    """bits are q + 1 (Yosys may compute it wider: `wp + 1` is 32 bits)."""
    drv = nl.whole_driver(bits)
    if drv is None or drv[1] != "Y" or drv[2] != 0 or nl.ctype(drv[0]) != "$add":
        return False
    a, b = nl.conn(drv[0], "A"), nl.conn(drv[0], "B")
    return any(_operand_is(x, q) and const_value(y) == 1 for x, y in ((a, b), (b, a)))


def _wraps(nl: Netlist, conds: list, q: list, last: int) -> bool:
    """One of the conditions is `q == last`."""
    for bit, value in conds:
        hit = nl.equality(bit, value)
        if hit is not None and hit[1] == last and list(hit[0]) == list(q):
            return True
    return False


def pointer(nl: Netlist, addr: list, size: int, ev: _Eval) -> Pointer | None:
    """The register whose low bits are `addr`, if it moves like a FIFO
    pointer (see the module docstring), else None."""
    # A write port's address comes through the write's own condition, with
    # don't-care ('x) when it doesn't write: look through those muxes.
    sources = [b for b, _ in mux_sources(nl, list(addr)) if not all(x == "x" for x in b)] if addr else []
    if len(sources) != 1:
        return None
    addr = sources[0]
    d0 = nl.driver.get(addr[0])
    if d0 is None or d0.port != "Q" or d0.offset != 0 or nl.ctype(d0.cell) not in _POINTER_FF:
        return None
    cell = d0.cell
    q = nl.conn(cell, "Q")
    if q[:len(addr)] != list(addr) or nl.param(cell, "CLK_POLARITY", 1) != 1:
        return None
    d = nl.conn(cell, "D")
    resets, natural = set(), True
    if nl.ctype(cell) == "$adff":
        resets.add(frozenset([(nl.conn(cell, "ARST")[0], nl.param(cell, "ARST_POLARITY", 1))]))
    elif nl.ctype(cell) == "$aldff":
        if const_value(nl.conn(cell, "AD")) is None:
            return None                                  # loads a value, not a reset
        resets.add(frozenset([(nl.conn(cell, "ALOAD")[0], nl.param(cell, "ALOAD_POLARITY", 1))]))
    for sbits, conds in mux_sources(nl, d):
        if _pinned(conds, ev) is None:
            resets.add(frozenset(conds))                 # only while a reset is active
            continue
        if sbits == q or _increment(nl, sbits, q):
            continue                                     # hold, advance
        if const_value(sbits) == 0 and _wraps(nl, conds, q, size - 1):
            natural = False
            continue                                     # back to the first entry
        return None
    if len(resets) > 1:
        return None                                      # reset in more than one way
    return Pointer(cell, nl.conn(cell, "CLK")[0], d, q, resets.pop() if resets else frozenset(), natural)


def _count_register(nl: Netlist, wp: Pointer, rp: Pointer, size: int):
    """The design's own count of the entries, if it seems to have one: a
    register that steps up and down by itself (`cnt <= cnt + push - pop`),
    wide enough for the size, that the pointers' logic reads within two
    registers.  Only a guess: a wrong one costs a fallback proof."""
    found = []
    for cell, c in nl.cells.items():
        if c["type"] not in FF_TYPES or cell in (wp.cell, rp.cell) or "D" not in c["connections"]:
            continue
        q = nl.conn(cell, "Q")
        if not (size.bit_length() <= len(q) <= 32):
            continue
        selfstep = False
        for sbits, _ in mux_sources(nl, nl.conn(cell, "D")):
            drv = nl.whole_driver(sbits)
            if drv is not None and nl.ctype(drv[0]) in ("$add", "$sub") and \
                    any(_operand_is(nl.conn(drv[0], p), q) for p in ("A", "B")):
                selfstep = True
            elif drv is not None and nl.ctype(drv[0]) in ("$add", "$sub"):
                inner = nl.whole_driver(nl.conn(drv[0], "A"))
                if inner is not None and nl.ctype(inner[0]) in ("$add", "$sub") and \
                        any(_operand_is(nl.conn(inner[0], p), q) for p in ("A", "B")):
                    selfstep = True                      # cnt + push - pop
        if selfstep and nl.depends_on(wp.d + rp.d, set(q), 2):
            found.append((len(q), nl.name_of(q), q))
    return min(found)[2] if found else None


def _strengthened(nl: Netlist, plain: Check, wp: Pointer, rp: Pointer, size: int, abits: int) -> Check:
    """plain with the guess at the design's count (see fvl_fifo), with plain
    as its fallback; plain itself when there is nothing to guess."""
    n = _count_register(nl, wp, rp, size)
    if n is not None:
        cand, ports = 1, {"n": list(n)}
    elif wp.natural and rp.natural and len(wp.q) == len(rp.q) == abits + 1 and size == 1 << abits:
        cand, ports = 2, {}
    else:
        return plain
    params = dict(plain.params, CAND=cand, NW=len(ports.get("n", ["0"])))
    return Check(kind=plain.kind, target=plain.target, src=plain.src, desc=plain.desc, checker=plain.checker,
                 params=params, ports=dict(plain.ports, **ports), anchors=plain.anchors,
                 waive_attr=plain.waive_attr, depth_hint=plain.depth_hint, fallback=plain)


def detect_fifos(nl: Netlist, inactive: dict) -> tuple:
    """(fifo_overflow and fifo_underflow checks, the pointers that wrap by
    overflowing their width).  `inactive`: reset bit -> its inactive value
    (Resets.inactive_conds)."""
    ev = _Eval(nl.mod, dict(inactive))
    checks, natural = [], set()
    for cell, c in nl.cells.items():
        if c["type"] != "$mem_v2" or nl.param(cell, "WR_PORTS", 0) != 1 or nl.param(cell, "OFFSET", 0) != 0:
            continue
        size, abits = nl.param(cell, "SIZE"), nl.param(cell, "ABITS")
        if not nl.param(cell, "WR_CLK_ENABLE", 0) or not nl.param(cell, "WR_CLK_POLARITY", 1):
            continue
        wp = pointer(nl, nl.conn(cell, "WR_ADDR")[:abits], size, ev)
        if wp is None or wp.clk != nl.conn(cell, "WR_CLK")[0]:
            continue
        rd_addr = nl.conn(cell, "RD_ADDR")
        rp = None
        for i in range(nl.param(cell, "RD_PORTS", 0)):
            p = pointer(nl, rd_addr[i * abits:(i + 1) * abits], size, ev)
            if p is not None and p.cell != wp.cell and p.clk == wp.clk:
                rp = p
                break
        if rp is None or rp.reset != wp.reset:
            continue                                     # the count must start over with both pointers
        memid = nl.param(cell, "MEMID", cell)
        if isinstance(memid, str):
            memid = memid.lstrip("\\")
        src = nl.cell_src(cell)
        waive = nl.attrs(cell).get("fvlint_waive")
        reset = sorted(wp.reset, key=str) or [("0", 1)]          # never, for pointers without a reset
        ports = {"clk": [wp.clk], "wd": wp.d, "wq": wp.q, "rd": rp.d, "rq": rp.q, "r": [b for b, _ in reset],
                 "n": ["0"]}
        params = {"PW": len(wp.q), "RW": len(rp.q), "CW": size.bit_length(), "DEPTH": size,
                  "NR": len(reset), "RPOL": sum(v << i for i, (_, v) in enumerate(reset))}
        for over, kind, desc in ((1, "fifo_overflow", f"no write to the full FIFO {memid} ({size} entries) "
                                  "without a read"),
                                 (0, "fifo_underflow", f"no read from the empty FIFO {memid}")):
            plain = Check(kind=kind, target=memid, src=src, desc=desc, checker=FIFO,
                          params=dict(params, OVER=over), ports=ports, anchors=[wp.cell, rp.cell],
                          waive_attr=waive, depth_hint=2 * size + 4)
            checks.append(_strengthened(nl, plain, wp, rp, size, abits))
        natural |= {p.cell for p in (wp, rp) if p.natural}
    return checks, natural


def settle_pointers(checks: list, pointers: set) -> int:
    """A FIFO pointer that wraps by overflowing its width does so by design:
    its counter_overflow check is INFO (the FIFO checks are what can go
    wrong).  One with an explicit wrap keeps its check: that proves the wrap
    works.  Returns how many."""
    n = 0
    for c in checks:
        if c.kind == "counter_overflow" and c.preset is None and pointers & set(c.anchors):
            c.preset, c.reason = INFO, FIFO_POINTER
            c.detail = "a FIFO pointer: it wraps by design; fifo_overflow and fifo_underflow check the FIFO"
            n += 1
    return n
