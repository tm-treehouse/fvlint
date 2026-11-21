# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Cone-of-influence slicing with cut-points.

Starting from the bits a check reads, walk the fanin.  Combinational cells
are always kept.  State cells are kept if they are anchors (the structure
under test, or cells restored by counterexample-guided refinement) or lie
within `level` register stages of the roots; beyond that their outputs are
cut, i.e. replaced by unconstrained $anyseq values.  Opaque cells (blackboxes
and cell types fvlint does not model) are always cut.

Cutting over-approximates the design's behaviour, so a property proven on a
slice holds on the full design.  The union of several slices is again an
over-approximation (with fewer cuts), which is what lets checks be batched.
"""

from __future__ import annotations

import copy
import re
from collections import deque
from dataclasses import dataclass, field

from .netlist import Netlist, is_const

UNBOUNDED = 1 << 30


@dataclass
class ConeSpec:
    keep: set = field(default_factory=set)          # cells kept (combinational and state)
    cut: set = field(default_factory=set)           # state/opaque cells replaced by $anyseq
    undriven: set = field(default_factory=set)      # undriven bits (also free)
    inputs: set = field(default_factory=set)        # top-level input bits used

    @property
    def kept_state(self) -> set:
        return self._kept_state

    def finish(self, nl: Netlist) -> "ConeSpec":
        self.cut -= self.keep
        self._kept_state = {c for c in self.keep if nl.is_stateful(c)}
        return self

    @property
    def full(self) -> bool:
        return not self.cut

    def size(self) -> int:
        return len(self.keep)


def slice_spec(nl: Netlist, roots, anchors, level: int) -> ConeSpec:
    anchors = set(anchors)
    dq = deque((b, 0) for b in roots if not is_const(b))
    seen_bit = {}
    spec = ConeSpec()
    decided = set()
    while dq:
        b, dep = dq.popleft()
        if b in seen_bit and seen_bit[b] <= dep:
            continue
        seen_bit[b] = dep
        d = nl.driver.get(b)
        if d is None:
            (spec.inputs if b in nl.port_in else spec.undriven).add(b)
            continue
        cell = d.cell
        if cell in decided:
            continue
        decided.add(cell)
        kind = nl.kind(cell)
        if kind in ("opaque", "sink"):
            spec.cut.add(cell)
            continue
        if kind == "state":
            if cell in anchors:
                ndep = dep
            elif dep < level:
                ndep = dep + 1
            else:
                spec.cut.add(cell)
                continue
        else:
            ndep = dep
        spec.keep.add(cell)
        for _, bits in nl.inputs(cell):
            for x in bits:
                if not is_const(x):
                    # 0-1 BFS: same-depth work first, so each cell is decided
                    # at the smallest depth it can be reached with.
                    (dq.appendleft if ndep == dep else dq.append)((x, ndep))
    return spec.finish(nl)


def merge_specs(nl: Netlist, specs) -> ConeSpec:
    out = ConeSpec()
    for s in specs:
        out.keep |= s.keep
        out.cut |= s.cut
        out.undriven |= s.undriven
        out.inputs |= s.inputs
    return out.finish(nl)


def clocks(nl: Netlist, spec: ConeSpec) -> set:
    out = set()
    for cell in spec.kept_state:
        out |= nl.clocks(cell)
    return out


def needs_multiclock(nl: Netlist, spec: ConeSpec) -> bool:
    """SymbiYosys' default model steps every flip-flop on one global clock.
    That is only faithful for a single clock net and edge without latches."""
    c = clocks(nl, spec)
    return len(c) > 1 or ("latch", 0) in c


_SAN = re.compile(r"[^A-Za-z0-9_.$]")


def _stable(name: str) -> str:
    # Yosys-generated names ($procmux$12, ...) could collide with names a
    # fresh Yosys process generates while reading the slice back; prefix them.
    return "$fvl" + name[1:] if name.startswith("$") else name


def build_module(nl: Netlist, spec: ConeSpec, keep_ports=(), uninit="zero") -> dict:
    mod = nl.mod
    cells = {}
    available = set()
    for name in sorted(spec.keep):
        cells[_stable(name)] = copy.deepcopy(nl.cells[name])
        for _, bits in nl.outputs(name):
            available.update(b for b in bits if not is_const(b))
    for n, name in enumerate(sorted(spec.cut)):
        for port, bits in nl.outputs(name):
            free = [b for b in bits if not is_const(b) and b not in available]
            if not free:
                continue
            cname = f"$fvlcut${n}$" + _SAN.sub("_", name.lstrip("$\\")) + "$" + port
            cells[cname] = {"hide_name": 1, "type": "$anyseq", "parameters": {"WIDTH": len(bits)},
                            "attributes": {"fvlint_cut": name}, "port_directions": {"Y": "output"},
                            "connections": {"Y": bits}}
            available.update(free)
    for b in sorted(spec.undriven - available):
        cells[f"$fvlundriven${b}"] = {
            "hide_name": 1, "type": "$anyseq", "parameters": {"WIDTH": 1}, "attributes": {},
            "port_directions": {"Y": "output"}, "connections": {"Y": [b]}}
        available.add(b)

    ports = {}
    keep_ports = set(keep_ports)
    for pname, p in mod["ports"].items():
        if p["direction"] not in ("input", "inout"):
            continue
        if pname in keep_ports or any(b in spec.inputs for b in p["bits"] if not is_const(b)):
            ports[pname] = {"direction": "input", "bits": p["bits"]}
            available.update(b for b in p["bits"] if not is_const(b))

    netnames = {}
    for name, net in mod["netnames"].items():
        if all(is_const(b) or b in available for b in net["bits"]):
            netnames[_stable(name)] = copy.deepcopy(net)

    if uninit == "zero":
        _zero_init(nl, spec, cells, netnames)
    return {"attributes": dict(mod.get("attributes", {})), "ports": ports,
            "cells": cells, "netnames": netnames}


def _zero_init(nl: Netlist, spec: ConeSpec, cells: dict, netnames: dict):
    """FPGA-style power-up: registers and memories without an explicit init
    value start at zero instead of an arbitrary value."""
    init_bits = set()
    for net in nl.netnames.values():
        if "init" in net.get("attributes", {}):
            init_bits.update(b for b in net["bits"] if not is_const(b))
    for n, cell in enumerate(sorted(spec.kept_state)):
        c = cells[_stable(cell)]
        if c["type"] in ("$mem_v2", "$mem"):
            init = c["parameters"].get("INIT")
            if isinstance(init, str) and init and set(init) <= set("x"):
                c["parameters"]["INIT"] = "0" * len(init)
            continue
        q = c["connections"].get("Q")
        if not q or any(b in init_bits for b in q if not is_const(b)):
            continue
        netnames[f"$fvlinit${n}$" + _SAN.sub("_", cell.lstrip("$\\"))] = {
            "hide_name": 1, "bits": q, "attributes": {"init": "0" * len(q)}}
