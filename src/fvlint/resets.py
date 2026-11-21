# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Reset discovery.

* The *primary* reset is a top-level input, given with --reset or guessed
  from its name.
* *Derived* resets are 1-bit registers that are forced to a constant while
  some reset is active and otherwise only load constants or other derived
  resets, i.e. reset synchronizers and "reset done" pipelines.  They settle
  to their inactive value a few cycles after the primary reset is released.

Checks are disabled while any reset is active, and the primary reset is held
long enough for the longest synchronizer chain to propagate.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field

from .netlist import FF_TYPES, Netlist, const_value, is_const

_RESET_RE = re.compile(r"(^|_)(a?rst|a?reset|rst_?sync)(_?n|_ni|_b|_i)?$", re.I)


@dataclass
class ResetBit:
    name: str
    bit: object
    active: int        # value while in reset
    depth: int = 0     # register stages after the primary reset


@dataclass
class Resets:
    primary: ResetBit | None = None
    derived: list = field(default_factory=list)
    cycles: int = 1
    anytime: bool = False       # allow reset to be re-asserted after start-up

    def all(self) -> list:
        return ([self.primary] if self.primary else []) + list(self.derived)

    def inactive_conds(self) -> list:
        """Path conditions meaning 'no reset is active'."""
        return [(r.bit, 1 - r.active) for r in self.all()]

    def names(self) -> dict:
        return {r.name: r.active for r in self.all()}


def find_primary(nl: Netlist, spec: str | None) -> ResetBit | None:
    """--reset NAME[:LEVEL] or a name heuristic over 1-bit top-level inputs."""
    if spec:
        name, _, lvl = spec.partition(":")
        if name not in nl.ports or nl.ports[name]["direction"] != "input":
            raise ValueError(f"--reset port {name!r} is not an input of the top module")
        active = int(lvl) if lvl else (0 if re.search(r"(n|_ni|_b)$", name, re.I) else 1)
        return ResetBit(name, nl.ports[name]["bits"][0], active)
    cands = [n for n, p in nl.ports.items()
             if p["direction"] == "input" and len(p["bits"]) == 1 and _RESET_RE.search(n)]
    if not cands:
        return None
    name = sorted(cands, key=len)[0]
    m = _RESET_RE.search(name)
    low = bool(m.group(3)) and m.group(3).lower() in ("n", "_n", "_ni", "_b")
    return ResetBit(name, nl.ports[name]["bits"][0], 0 if low else 1)


def _bit_sources(nl: Netlist, d_bit):
    from .detect import mux_sources
    return mux_sources(nl, [d_bit])


def find_derived(nl: Netlist, primary: ResetBit, max_depth: int = 8) -> list:
    known = {primary.bit: primary}
    derived = []
    for _ in range(max_depth):
        added = False
        for cell, c in nl.cells.items():
            if c["type"] not in FF_TYPES or "D" not in c["connections"]:
                continue
            ff = nl.ff_info(cell)
            for i, (q, d) in enumerate(zip(ff["Q"], ff["D"])):
                if is_const(q) or q in known:
                    continue
                r = _derived_bit(nl, cell, i, d, known)
                if r is None:
                    continue
                active, depth = r
                name = nl.bit_name.get(q, str(q))
                rb = ResetBit(name, q, active, depth)
                known[q] = rb
                derived.append(rb)
                added = True
        if not added:
            break
    return derived


def _as_reset(nl: Netlist, bit, known: dict, hops: int = 4):
    """(ResetBit, active level of `bit`) if `bit` is a known reset, possibly
    through inverters (Yosys inverts negedge async resets), else None."""
    inv = 0
    for _ in range(hops):
        if bit in known:
            r = known[bit]
            return r, r.active ^ inv
        d = nl.driver.get(bit)
        if d is None:
            return None
        t = nl.ctype(d.cell)
        a = nl.conn(d.cell, "A")
        if len(a) != 1 or t not in _INVERT | _BUFFER:
            return None
        bit = a[0]
        if t in _INVERT:
            inv ^= 1
    return None


_INVERT = {"$not", "$logic_not"}
_BUFFER = {"$pos", "$buf", "$reduce_or", "$reduce_and", "$reduce_bool", "$reduce_xor"}


def _derived_bit(nl: Netlist, cell: str, i: int, d, known: dict):
    """(active value, depth) if bit i of FF `cell` behaves like a reset: it is
    forced to a constant while a reset is active (asynchronously or through
    its D logic) or simply copies another reset, and otherwise only ever
    moves towards its inactive value."""
    conns = nl.cells[cell]["connections"]
    forced = None
    depth = 0
    if "ARST" in conns:
        hit = _as_reset(nl, nl.conn(cell, "ARST")[0], known)
        if hit and nl.param(cell, "ARST_POLARITY", 1) == hit[1]:
            forced = (nl.param(cell, "ARST_VALUE", 0) >> i) & 1
            depth = hit[0].depth
    consts, copies = set(), []
    for bits, conds in _bit_sources(nl, d):
        in_reset = []
        for b, val in conds:
            hit = _as_reset(nl, b, known)
            if hit and val == hit[1]:
                in_reset.append(hit[0])
        v = const_value(bits)
        if in_reset:
            if v is None:
                return None
            if forced is not None and forced != v:
                return None
            forced = v
            depth = max(depth, max(r.depth for r in in_reset))
        elif v is not None:
            consts.add(v)
        elif len(bits) == 1 and bits[0] in known:
            copies.append(known[bits[0]])
        else:
            return None
    if forced is None:
        # A plain copy of a reset (synchronizer stage) takes its active value.
        actives = {r.active for r in copies}
        if len(actives) != 1:
            return None
        forced = actives.pop()
    if any(c != 1 - forced for c in consts) or any(r.active != forced for r in copies):
        return None
    depth = max([depth] + [r.depth for r in copies])
    return forced, depth + 1


def discover(nl: Netlist, spec: str | None, no_reset: bool, cycles: int | None,
             anytime: bool = False) -> Resets:
    if no_reset:
        return Resets(None, [], 0)
    primary = find_primary(nl, spec)
    if primary is None:
        return Resets(None, [], 0)
    derived = find_derived(nl, primary)
    depth = max((r.depth for r in derived), default=0)
    return Resets(primary, derived, cycles if cycles is not None else depth + 1, anytime)
