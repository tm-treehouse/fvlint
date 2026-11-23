# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Shared helpers for the unit tests: a netlist builder for hand-made Yosys
JSON, access to the committed Yosys netlist snapshots, and small fakes."""

from __future__ import annotations

import contextlib
import io
import json
import os
import shutil
import tempfile
import unittest

from fvlint.netlist import Netlist

DATA = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data")

OUT_PORTS = {"Y", "Q", "RD_DATA", "X", "CO", "CTRL_OUT"}


def const(v: int, w: int) -> list:
    """Integer -> LSB-first Yosys constant bit list."""
    return ["1" if (v >> i) & 1 else "0" for i in range(w)]


class NB:
    """Netlist builder.  Allocates bit ids and infers port directions
    (Y/Q/RD_DATA/... are outputs, everything else an input)."""

    def __init__(self):
        self._next = 2
        self.ports, self.cells, self.netnames = {}, {}, {}
        self._n = 0

    def new(self, w: int = 1) -> list:
        bits = list(range(self._next, self._next + w))
        self._next += w
        return bits

    def net(self, name: str, bits: list, hidden: bool = False, **attrs) -> list:
        self.netnames[name] = {"hide_name": int(hidden), "bits": list(bits), "attributes": dict(attrs)}
        return bits

    def input(self, name: str, w: int = 1, direction: str = "input") -> list:
        bits = self.new(w)
        self.ports[name] = {"direction": direction, "bits": bits}
        self.net(name, bits)
        return bits

    def output(self, name: str, bits: list) -> list:
        self.ports[name] = {"direction": "output", "bits": list(bits)}
        self.net(name, bits)
        return bits

    def cell(self, name: str | None, ctype: str, conns: dict, params=None, attrs=None, dirs=None) -> str:
        if name is None:
            self._n += 1
            name = f"${ctype.lstrip('$')}$t.v:{self._n}${self._n}"
        if dirs is None:
            dirs = {p: ("output" if p in OUT_PORTS else "input") for p in conns}
        self.cells[name] = {"hide_name": int(name.startswith("$")), "type": ctype,
                            "parameters": dict(params or {}), "attributes": dict(attrs or {}),
                            "port_directions": dirs, "connections": {k: list(v) for k, v in conns.items()}}
        return name

    def op(self, ctype: str, w: int | None = None, name: str | None = None, params=None, attrs=None,
           **ins) -> list:
        """A combinational cell; returns its Y bits (width w, default len(A))."""
        w = w if w is not None else len(ins.get("A", [None]))
        y = self.new(w)
        p = {"Y_WIDTH": w}
        for k, v in ins.items():
            if k in ("A", "B"):
                p[f"{k}_WIDTH"] = len(v)
                p.setdefault(f"{k}_SIGNED", 0)
        p.update(params or {})
        self.cell(name, ctype, dict(ins, Y=y), p, attrs)
        return y

    def mux(self, a: list, b: list, s, name=None, attrs=None) -> list:
        y = self.new(len(a))
        self.cell(name, "$mux", {"A": a, "B": b, "S": [s] if not isinstance(s, list) else s, "Y": y},
                  {"WIDTH": len(a)}, attrs)
        return y

    def pmux(self, a: list, bs: list, sels: list, name=None, attrs=None) -> list:
        y = self.new(len(a))
        flat = [b for chunk in bs for b in chunk]
        self.cell(name, "$pmux", {"A": a, "B": flat, "S": sels, "Y": y},
                  {"WIDTH": len(a), "S_WIDTH": len(sels)}, attrs)
        return y

    def ff(self, d: list, clk, q: list | None = None, name=None, en=None, en_pol=1, arst=None, arst_pol=1,
           arst_val=0, srst=None, srst_pol=1, srst_val=0, clk_pol=1, attrs=None) -> list:
        """$dff/$dffe/$adff/$adffe/$sdff/$sdffe, chosen by the controls given."""
        q = q if q is not None else self.new(len(d))
        conns = {"CLK": [clk], "D": d, "Q": q}
        params = {"WIDTH": len(d), "CLK_POLARITY": clk_pol}
        t = "$dff"
        if arst is not None:
            t = "$adff"
            conns["ARST"] = [arst]
            params.update(ARST_POLARITY=arst_pol, ARST_VALUE=arst_val)
        elif srst is not None:
            t = "$sdff"
            conns["SRST"] = [srst]
            params.update(SRST_POLARITY=srst_pol, SRST_VALUE=srst_val)
        if en is not None:
            t += "e"
            conns["EN"] = [en]
            params["EN_POLARITY"] = en_pol
        self.cell(name, t, conns, params, attrs)
        return q

    def module(self) -> dict:
        return {"attributes": {}, "ports": self.ports, "cells": self.cells, "netnames": self.netnames}

    def data(self, top: str = "t") -> dict:
        return {"creator": "unit", "modules": {top: self.module()}}

    def build(self, top: str = "t", **kw) -> Netlist:
        return Netlist(self.data(top), top, **kw)


def snapshot(top: str, kind: str = "main") -> str:
    """Path of a committed Yosys netlist snapshot (see data/make_snapshots.py)."""
    return os.path.join(DATA, "snapshots", f"{top}.{kind}.json")


def load_snapshot(top: str) -> Netlist:
    return Netlist.load(snapshot(top), top)


class TempDirCase(unittest.TestCase):
    """A TestCase with a fresh temporary directory in self.tmp."""

    def setUp(self):
        super().setUp()
        self.tmp = os.path.realpath(tempfile.mkdtemp(prefix="fvlint_unit_"))   # macOS: /var is a link to /private/var
        self.addCleanup(shutil.rmtree, self.tmp, True)

    def write(self, rel: str, text: str) -> str:
        p = os.path.join(self.tmp, rel)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, "w") as f:
            f.write(text)
        return p

    def write_json(self, rel: str, obj) -> str:
        return self.write(rel, json.dumps(obj))

    def chdir(self, path: str):
        old = os.getcwd()
        os.chdir(path)
        self.addCleanup(os.chdir, old)


@contextlib.contextmanager
def captured():
    """Capture stdout and stderr: `with captured() as (out, err): ...`."""
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        yield out, err
