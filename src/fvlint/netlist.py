# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""A small read-only model of a flattened Yosys JSON netlist.

Bits are Yosys bit ids (ints) or constant strings ("0", "1", "x", "z").
"""

from __future__ import annotations

import json
import os
from dataclasses import dataclass

# Cells that hold state: the cone walker stops at these and decides whether
# to include them or replace their outputs with free ($anyseq) values.
STATEFUL = {
    "$dff", "$dffe", "$adff", "$adffe", "$sdff", "$sdffe", "$sdffce", "$aldff", "$aldffe",
    "$dffsr", "$dffsre", "$dlatch", "$adlatch", "$dlatchsr", "$sr", "$ff",
    "$mem", "$mem_v2", "$memrd", "$memrd_v2", "$memwr", "$memwr_v2", "$anyinit",
}
FF_TYPES = STATEFUL - {"$mem", "$mem_v2", "$memrd", "$memrd_v2", "$memwr", "$memwr_v2"}
# Property and debug cells are sinks and are never pulled into a cone.
SINKS = {"$assert", "$assume", "$cover", "$live", "$fair", "$check", "$print", "$scopeinfo"}

Bit = "int | str"


def is_const(b) -> bool:
    return isinstance(b, str)


def param_int(v) -> int:
    """Decode a Yosys JSON parameter (binary string or int) as unsigned int."""
    if isinstance(v, int):
        return v
    if isinstance(v, str) and v and set(v) <= set("01"):
        return int(v, 2)
    raise ValueError(f"not an integer parameter: {v!r}")


def attr_true(v) -> bool:
    if v is None:
        return False
    if isinstance(v, int):
        return v != 0
    if isinstance(v, str):
        return ("1" in v) if set(v) <= set("01xz") else bool(v)
    return bool(v)


def const_value(bits) -> int | None:
    """LSB-first constant bit list -> int, or None if any bit is non-constant/x."""
    v = 0
    for i, b in enumerate(bits):
        if b == "1":
            v |= 1 << i
        elif b != "0":
            return None
    return v


def src_short(src: str | None, base: str | None = None, src_map=None) -> str:
    """'a/b.v:12.3-14.8|...' -> 'a/b.v:12', with the file shown relative to
    the CWD.  `base` is the directory Yosys ran in; `src_map` is an optional
    (staged_root, original_root) pair for inputs that were copied."""
    if not src:
        return "?"
    s = src.split("|")[0]
    if ":" not in s:
        return s
    f, pos = s.rsplit(":", 1)
    if base:
        f = os.path.normpath(os.path.join(base, f))
        if src_map and (f + os.sep).startswith(src_map[0] + os.sep):
            f = os.path.join(src_map[1], os.path.relpath(f, src_map[0]))
        f = display_path(f)
    return f"{f}:{pos.split('.')[0]}"


def display_path(p: str) -> str:
    """Relative to the CWD when below it, absolute otherwise."""
    r = os.path.relpath(p)
    return p if r.startswith("..") else r


@dataclass
class Driver:
    cell: str
    port: str
    offset: int


class Netlist:
    def __init__(self, data: dict, top: str, src_base: str | None = None, src_map=None):
        self.data = data
        self.src_base = src_base
        self.src_map = src_map
        self.top = top
        if top not in data["modules"]:
            raise KeyError(f"top module {top!r} not in netlist")
        self.mod = data["modules"][top]
        self.cells: dict = self.mod["cells"]
        self.ports: dict = self.mod["ports"]
        self.netnames: dict = self.mod["netnames"]
        self.driver: dict = {}       # bit -> Driver
        self.port_in: set = set()    # bits driven by top-level input/inout ports
        self.readers: dict = {}      # bit -> list of (cell, port, offset)
        self.max_bit = 1
        self._index()

    @classmethod
    def load(cls, path: str, top: str, src_base: str | None = None, src_map=None) -> "Netlist":
        """src_base: directory Yosys ran in (src attributes are relative to it)."""
        with open(path) as f:
            return cls(json.load(f), top, src_base, src_map)

    def src(self, raw: str | None) -> str:
        return src_short(raw, self.src_base, self.src_map)

    # ------------------------------------------------------------------ index
    def _index(self):
        for pname, p in self.ports.items():
            for b in p["bits"]:
                if not is_const(b):
                    self.max_bit = max(self.max_bit, b)
                    if p["direction"] in ("input", "inout"):
                        self.port_in.add(b)
        for cname, c in self.cells.items():
            dirs = c.get("port_directions", {})
            for port, bits in c["connections"].items():
                d = dirs.get(port, "input")
                for i, b in enumerate(bits):
                    if is_const(b):
                        continue
                    self.max_bit = max(self.max_bit, b)
                    if d in ("output", "inout"):
                        self.driver[b] = Driver(cname, port, i)
                    if d in ("input", "inout"):
                        self.readers.setdefault(b, []).append((cname, port, i))
        self.bit_name = {}
        for name, n in self._ranked_nets():
            for i, b in enumerate(n["bits"]):
                if not is_const(b) and b not in self.bit_name:
                    w = len(n["bits"])
                    self.bit_name[b] = name if w == 1 else f"{name}[{i}]"

    def _ranked_nets(self):
        """Visible names first; among those, the innermost declaration (most
        hierarchy levels), which is where a register's logic lives."""
        return sorted(self.netnames.items(),
                      key=lambda kv: (kv[1].get("hide_name", 0), -kv[0].count("."), len(kv[0]), kv[0]))

    # ---------------------------------------------------------------- helpers
    def ctype(self, cell: str) -> str:
        return self.cells[cell]["type"]

    def conn(self, cell: str, port: str) -> list:
        return self.cells[cell]["connections"].get(port, [])

    def param(self, cell: str, name: str, default=None):
        v = self.cells[cell]["parameters"].get(name)
        if v is None:
            return default
        try:
            return param_int(v)
        except ValueError:
            return v

    def attrs(self, cell: str) -> dict:
        return self.cells[cell].get("attributes", {})

    def cell_src(self, cell: str) -> str:
        return self.src(self.attrs(cell).get("src"))

    def is_stateful(self, cell: str) -> bool:
        return self.ctype(cell) in STATEFUL

    def is_blackbox(self, cell: str) -> bool:
        return not self.ctype(cell).startswith("$")

    def whole_driver(self, bits: list):
        """If all bits are consecutive bits of one cell output port, return
        (cell, port, offset); otherwise None."""
        if not bits or any(is_const(b) for b in bits):
            return None
        d0 = self.driver.get(bits[0])
        if d0 is None:
            return None
        for i, b in enumerate(bits):
            d = self.driver.get(b)
            if d is None or d.cell != d0.cell or d.port != d0.port or d.offset != d0.offset + i:
                return None
        return d0.cell, d0.port, d0.offset

    def name_of(self, bits: list) -> str:
        """Best-effort readable name for a bit vector."""
        if not bits:
            return "?"
        if all(is_const(b) for b in bits):
            return "'" + "".join(reversed(bits))
        for name, n in self._ranked_nets():
            if n["bits"] == bits:
                return name
        names = [self.bit_name.get(b, str(b)) for b in bits]
        base = {nm.rsplit("[", 1)[0] for nm in names}
        if len(base) == 1:
            return f"{base.pop()}[{len(bits)}b]"
        return "{" + ",".join(reversed(names)) + "}"

    def net_by_bits(self, bits: list):
        """Return (name, netname-dict) for a user-visible net exactly covering bits."""
        for name, n in self._ranked_nets():
            if n["bits"] == bits and not n.get("hide_name", 0):
                return name, n
        return None, None

    def net_src(self, bits: list) -> str:
        _, n = self.net_by_bits(bits)
        if n:
            return self.src(n.get("attributes", {}).get("src"))
        return "?"

    def net_attr(self, bits: list, attr: str):
        """Attribute from any net that is exactly these bits (a register and
        the ports it is connected to are all aliases after flattening)."""
        for _, n in self._ranked_nets():
            if n["bits"] == bits and attr in n.get("attributes", {}):
                return n["attributes"][attr]
        return None

    def fanin_cells(self, bits, stop_at_state=True) -> set:
        """Combinational fanin cells of the given bits (stops at state cells)."""
        seen, out, todo = set(), set(), [b for b in bits if not is_const(b)]
        while todo:
            b = todo.pop()
            if b in seen:
                continue
            seen.add(b)
            d = self.driver.get(b)
            if d is None:
                continue
            out.add(d.cell)
            if stop_at_state and (self.is_stateful(d.cell) or self.is_blackbox(d.cell)):
                continue
            for port, pbits in self.cells[d.cell]["connections"].items():
                if self.cells[d.cell].get("port_directions", {}).get(port, "input") == "input":
                    todo.extend(x for x in pbits if not is_const(x))
        return out

    def depends_on(self, bits, targets: set, max_seq: int) -> bool:
        """True if any of `bits` depends on any bit in `targets`, crossing at
        most `max_seq` state elements."""
        targets = set(targets)
        frontier = [b for b in bits if not is_const(b)]
        seen = set()
        for _ in range(max_seq + 1):
            nxt = []
            while frontier:
                b = frontier.pop()
                if b in targets:
                    return True
                if b in seen:
                    continue
                seen.add(b)
                d = self.driver.get(b)
                if d is None:
                    continue
                c = self.cells[d.cell]
                for port, pbits in c["connections"].items():
                    if c.get("port_directions", {}).get(port, "input") != "input":
                        continue
                    lst = nxt if (self.is_stateful(d.cell) or self.is_blackbox(d.cell)) else frontier
                    lst.extend(x for x in pbits if not is_const(x))
            frontier = nxt
        return False

    def ff_info(self, cell: str) -> dict:
        """Normalise flip-flop control ports into path conditions."""
        t = self.ctype(cell)
        p = lambda n, d=1: self.param(cell, n, d)
        conds = []  # (bit, value) that must hold for D to be captured
        if "EN" in self.cells[cell]["connections"]:
            conds.append((self.conn(cell, "EN")[0], p("EN_POLARITY")))
        for rport in ("ARST", "SRST", "ALOAD"):
            if rport in self.cells[cell]["connections"]:
                pol = p(rport + "_POLARITY") if rport != "ALOAD" else p("ALOAD_POLARITY")
                conds.append((self.conn(cell, rport)[0], 1 - pol))
        return {"type": t, "D": self.conn(cell, "D"), "Q": self.conn(cell, "Q"), "conds": conds}
