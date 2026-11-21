# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""A read-only model of a flattened Yosys JSON netlist.

Bits are Yosys bit ids (ints) or constant strings ("0", "1", "x", "z").

Cell semantics are classified conservatively: only cell types fvlint knows to
be combinational or stateful are modelled; anything else (new Yosys cell
types, blackboxes, vendor primitives) is *opaque* and always cut, which
over-approximates its behaviour and therefore keeps proofs sound.
"""

from __future__ import annotations

import json
import os
import re
from dataclasses import dataclass

# Coarse-grain combinational cells (kernel/celltypes.h) plus formal sources.
COMB = {
    "$not", "$pos", "$neg", "$reduce_and", "$reduce_or", "$reduce_xor", "$reduce_xnor",
    "$reduce_bool", "$logic_not", "$slice", "$lut", "$sop", "$buf",
    "$and", "$or", "$xor", "$xnor", "$shl", "$shr", "$sshl", "$sshr", "$shift", "$shiftx",
    "$lt", "$le", "$eq", "$ne", "$eqx", "$nex", "$ge", "$gt", "$add", "$sub", "$mul", "$div",
    "$mod", "$divfloor", "$modfloor", "$pow", "$logic_and", "$logic_or", "$concat", "$bweqx",
    "$mux", "$pmux", "$bmux", "$demux", "$bwmux", "$alu", "$lcu", "$fa", "$macc", "$macc_v2",
    "$initstate", "$anyconst", "$anyseq", "$allconst", "$allseq",
}
# State-holding coarse-grain cells.
FF_TYPES = {
    "$dff", "$dffe", "$adff", "$adffe", "$sdff", "$sdffe", "$sdffce", "$aldff", "$aldffe",
    "$dffsr", "$dffsre", "$dlatch", "$adlatch", "$dlatchsr", "$sr", "$ff", "$anyinit",
}
MEM_TYPES = {"$mem", "$mem_v2", "$memrd", "$memrd_v2", "$memwr", "$memwr_v2"}
LATCH_TYPES = {"$dlatch", "$adlatch", "$dlatchsr", "$sr"}
STATEFUL = FF_TYPES | MEM_TYPES
_GATE_STATE = re.compile(r"^\$_(DFF|DFFE|SDFF|SDFFE|SDFFCE|ALDFF|ALDFFE|DFFSR|DFFSRE|DLATCH|DLATCHSR|SR|FF)_")

# Yosys versions the test suite has been run against.
TESTED_YOSYS = [(0, 71)]


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


@dataclass(frozen=True)
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
        self.unknown_types: set = set()
        self._kind: dict = {}
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
        for p in self.ports.values():
            if p["direction"] in ("input", "inout"):
                self.port_in.update(b for b in p["bits"] if not is_const(b))
        for cname, c in self.cells.items():
            dirs = c.get("port_directions", {})
            for port, bits in c["connections"].items():
                d = dirs.get(port, "input")
                for i, b in enumerate(bits):
                    if is_const(b):
                        continue
                    if d in ("output", "inout"):
                        self.driver[b] = Driver(cname, port, i)
                    if d in ("input", "inout"):
                        self.readers.setdefault(b, []).append((cname, port, i))
            self._kind[cname] = self._classify(c["type"])
        # Visible names first; among those the innermost declaration (most
        # hierarchy levels, where a register's logic lives), then shortest.
        ranked = sorted(self.netnames.items(),
                        key=lambda kv: (kv[1].get("hide_name", 0), -kv[0].count("."), len(kv[0]), kv[0]))
        self._nets_by_bits: dict = {}
        self.bit_name: dict = {}
        for name, n in ranked:
            self._nets_by_bits.setdefault(tuple(n["bits"]), []).append((name, n))
            w = len(n["bits"])
            for i, b in enumerate(n["bits"]):
                if not is_const(b) and b not in self.bit_name:
                    self.bit_name[b] = name if w == 1 else f"{name}[{i}]"

    def _classify(self, t: str) -> str:
        if t in STATEFUL or _GATE_STATE.match(t):
            return "state"
        if t in COMB or t.startswith("$_"):
            return "comb"
        if t in ("$assert", "$assume", "$cover", "$live", "$fair", "$check", "$print",
                 "$scopeinfo", "$specify2", "$specify3", "$specrule", "$equiv"):
            return "sink"
        if t.startswith("$"):
            self.unknown_types.add(t)
        return "opaque"

    # ---------------------------------------------------------------- helpers
    def ctype(self, cell: str) -> str:
        return self.cells[cell]["type"]

    def kind(self, cell: str) -> str:
        """'comb', 'state', 'sink' or 'opaque' (blackbox or unknown type)."""
        return self._kind[cell]

    def conn(self, cell: str, port: str) -> list:
        return self.cells[cell]["connections"].get(port, [])

    def inputs(self, cell: str):
        c = self.cells[cell]
        dirs = c.get("port_directions", {})
        for port, bits in c["connections"].items():
            if dirs.get(port, "input") in ("input", "inout"):
                yield port, bits

    def outputs(self, cell: str):
        c = self.cells[cell]
        dirs = c.get("port_directions", {})
        for port, bits in c["connections"].items():
            if dirs.get(port) in ("output", "inout"):
                yield port, bits

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
        return self._kind[cell] == "state"

    def is_opaque(self, cell: str) -> bool:
        return self._kind[cell] == "opaque"

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

    # ------------------------------------------------------------- naming
    def nets_for(self, bits: list) -> list:
        """All (name, net) pairs exactly covering `bits`, best name first."""
        return self._nets_by_bits.get(tuple(bits), [])

    def name_of(self, bits: list) -> str:
        """Best-effort readable name for a bit vector."""
        if not bits:
            return "?"
        if all(is_const(b) for b in bits):
            return "'" + "".join(reversed(bits))
        nets = self.nets_for(bits)
        if nets:
            return nets[0][0]
        names = [self.bit_name.get(b, str(b)) for b in bits]
        base = {nm.rsplit("[", 1)[0] for nm in names}
        if len(base) == 1:
            return f"{base.pop()}[{len(bits)}b]"
        return "{" + ",".join(reversed(names)) + "}"

    def visible_name(self, bits: list) -> str | None:
        for name, n in self.nets_for(bits):
            if not n.get("hide_name", 0):
                return name
        return None

    def net_src(self, bits: list) -> str:
        for _, n in self.nets_for(bits):
            if not n.get("hide_name", 0):
                return self.src(n.get("attributes", {}).get("src"))
        return "?"

    def net_attr(self, bits: list, attr: str):
        """Attribute from any net that is exactly these bits (a register and
        the ports it is connected to are all aliases after flattening)."""
        for _, n in self.nets_for(bits):
            if attr in n.get("attributes", {}):
                return n["attributes"][attr]
        return None

    # ------------------------------------------------------------ structure
    def compare_cells(self, bits: list, types) -> set:
        """Cells of the given types that read any of `bits`."""
        out = set()
        for b in bits:
            for cell, _, _ in self.readers.get(b, ()):
                if self.ctype(cell) in types:
                    out.add(cell)
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
                if d is None or self._kind[d.cell] in ("opaque", "sink"):
                    continue
                lst = nxt if self._kind[d.cell] == "state" else frontier
                for _, pbits in self.inputs(d.cell):
                    lst.extend(x for x in pbits if not is_const(x))
            frontier = nxt
        return False

    def ff_info(self, cell: str) -> dict:
        """Normalise flip-flop control ports into path conditions."""
        p = lambda n, d=1: self.param(cell, n, d)  # noqa: E731
        conds = []  # (bit, value) that must hold for D to be captured
        conns = self.cells[cell]["connections"]
        if "EN" in conns:
            conds.append((self.conn(cell, "EN")[0], p("EN_POLARITY")))
        for rport in ("ARST", "SRST", "ALOAD"):
            if rport in conns:
                conds.append((self.conn(cell, rport)[0], 1 - p(rport + "_POLARITY")))
        return {"type": self.ctype(cell), "D": self.conn(cell, "D"), "Q": self.conn(cell, "Q"),
                "conds": conds}

    def clocks(self, cell: str) -> set:
        """(clock bit, polarity) pairs a state cell is sensitive to; latches
        and unclocked memories report ('latch', 0)."""
        t = self.ctype(cell)
        if t in LATCH_TYPES:
            return {("latch", 0)}
        if t in FF_TYPES and "CLK" in self.cells[cell]["connections"]:
            clk = self.conn(cell, "CLK")[0]
            return set() if is_const(clk) else {(clk, self.param(cell, "CLK_POLARITY", 1))}
        out = set()
        if t == "$mem_v2":
            for kind in ("RD", "WR"):
                n = self.param(cell, f"{kind}_PORTS", 0)
                en = self.param(cell, f"{kind}_CLK_ENABLE", 0)
                pol = self.param(cell, f"{kind}_CLK_POLARITY", 0)
                clks = self.conn(cell, f"{kind}_CLK")
                for i in range(n):
                    if (en >> i) & 1 and i < len(clks) and not is_const(clks[i]):
                        out.add((clks[i], (pol >> i) & 1))
        return out


def parse_yosys_version(text: str):
    m = re.search(r"Yosys (\d+)\.(\d+)", text)
    return (int(m.group(1)), int(m.group(2))) if m else None
