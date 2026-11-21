# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Cone-of-influence slicing with cut-points.

Starting from the bits a check reads, walk the fanin.  Combinational cells
are always kept.  State cells are kept if they are anchors (the structure
under test) or lie within `level` register stages of the roots; beyond that
their outputs are cut, i.e. replaced by unconstrained $anyseq values.

Cutting over-approximates the design's behaviour, so a property proven on
the slice holds on the full design; a counterexample on the slice may be
spurious and is retried with a larger cone.
"""

from __future__ import annotations

import copy
from collections import deque
from dataclasses import dataclass

from .netlist import Netlist, is_const

UNBOUNDED = 1 << 30


@dataclass
class Cone:
    module: dict
    kept_state: set
    cut_state: set
    full: bool


def _outputs(nl: Netlist, cell: str):
    c = nl.cells[cell]
    dirs = c.get("port_directions", {})
    for port, bits in c["connections"].items():
        if dirs.get(port) in ("output", "inout"):
            yield port, bits


def slice_cone(nl: Netlist, roots, anchors, level: int, keep_ports=(), uninit="zero") -> Cone:
    anchors = set(anchors)
    dq = deque((b, 0) for b in roots if not is_const(b))
    seen_bit = {}
    keep, kept_state, cut_state = set(), set(), set()
    decided = {}
    undriven = set()
    used_inputs = set()

    while dq:
        b, dep = dq.popleft()
        if b in seen_bit and seen_bit[b] <= dep:
            continue
        seen_bit[b] = dep
        d = nl.driver.get(b)
        if d is None:
            if b in nl.port_in:
                used_inputs.add(b)
            else:
                undriven.add(b)
            continue
        cell = d.cell
        if cell in decided:
            continue
        stateful = nl.is_stateful(cell)
        if nl.is_blackbox(cell):
            decided[cell] = "cut"
            cut_state.add(cell)
            continue
        if stateful:
            if cell in anchors:
                ndep = dep
            elif dep < level:
                ndep = dep + 1
            else:
                decided[cell] = "cut"
                cut_state.add(cell)
                continue
            kept_state.add(cell)
        else:
            ndep = dep
        decided[cell] = "keep"
        keep.add(cell)
        c = nl.cells[cell]
        dirs = c.get("port_directions", {})
        for port, bits in c["connections"].items():
            if dirs.get(port, "input") in ("input", "inout"):
                for x in bits:
                    if not is_const(x):
                        if ndep == dep:
                            dq.appendleft((x, ndep))
                        else:
                            dq.append((x, ndep))

    mod = nl.mod
    cells = {name: copy.deepcopy(nl.cells[name]) for name in sorted(keep)}
    available = set()
    for name in keep:
        for _, bits in _outputs(nl, name):
            available.update(b for b in bits if not is_const(b))
    n = 0
    for name in sorted(cut_state):
        for port, bits in _outputs(nl, name):
            cells[f"fvl_cut_{n}"] = {
                "hide_name": 1, "type": "$anyseq", "parameters": {"WIDTH": len(bits)},
                "attributes": {"fvlint_cut": name}, "port_directions": {"Y": "output"},
                "connections": {"Y": bits}}
            available.update(b for b in bits if not is_const(b))
            n += 1
    for b in sorted(undriven - available):
        cells[f"fvl_undriven_{n}"] = {
            "hide_name": 1, "type": "$anyseq", "parameters": {"WIDTH": 1}, "attributes": {},
            "port_directions": {"Y": "output"}, "connections": {"Y": [b]}}
        available.add(b)
        n += 1

    ports = {}
    keep_ports = set(keep_ports)
    for pname, p in mod["ports"].items():
        if p["direction"] not in ("input", "inout"):
            continue
        if pname in keep_ports or any(b in used_inputs for b in p["bits"] if not is_const(b)):
            ports[pname] = {"direction": "input", "bits": p["bits"]}
            available.update(b for b in p["bits"] if not is_const(b))

    netnames = {}
    for name, net in mod["netnames"].items():
        if all(is_const(b) or b in available for b in net["bits"]):
            netnames[name] = copy.deepcopy(net)

    if uninit == "zero":
        _zero_init(nl, cells, netnames, kept_state)

    # Yosys-generated names ($procmux$12, ...) in the slice could collide with
    # names a fresh Yosys process generates while reading it back; rename them.
    cells = {(f"$fvlc${i}" if name.startswith("$") else name): c
             for i, (name, c) in enumerate(cells.items())}
    netnames = {(f"$fvln${i}" if name.startswith("$") else name): n
                for i, (name, n) in enumerate(netnames.items())}

    module = {"attributes": dict(mod.get("attributes", {})), "ports": ports,
              "cells": cells, "netnames": netnames}
    return Cone(module, kept_state, cut_state, full=not cut_state)


def _zero_init(nl: Netlist, cells: dict, netnames: dict, kept_state: set):
    """FPGA-style power-up: registers and memories without an explicit init
    value start at zero instead of an arbitrary value."""
    init_bits = set()
    for net in nl.netnames.values():
        if "init" in net.get("attributes", {}):
            init_bits.update(b for b in net["bits"] if not is_const(b))
    for i, cell in enumerate(sorted(kept_state)):
        c = cells[cell]
        if c["type"] in ("$mem_v2", "$mem"):
            init = c["parameters"].get("INIT")
            if isinstance(init, str) and init and set(init) <= set("x"):
                c["parameters"]["INIT"] = "0" * len(init)
            continue
        q = c["connections"].get("Q")
        if not q or any(b in init_bits for b in q if not is_const(b)):
            continue
        netnames[f"$fvl_init${i}"] = {"hide_name": 1, "bits": q,
                                      "attributes": {"init": "0" * len(q)}}
