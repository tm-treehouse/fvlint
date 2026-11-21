# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Counterexample replay for counterexample-guided refinement.

A counterexample found on a slice may be spurious: the cut registers took
values the real logic could not produce.  To decide, the slice's top-level
input sequence is pinned onto the check's *full* cone (no cuts) and a short
cover job asks whether the violation still happens.  If it does, the failure
is real.  If not, the cut registers whose values differ between the slice
trace and the replay are the ones that made it spurious; only those are
restored before the next attempt.
"""

from __future__ import annotations

import json
import re


def read_yw(path: str) -> dict:
    """Yosys witness file -> {signal name: [int value per step]} for
    single-element paths (top-level inputs and cut values)."""
    with open(path) as f:
        d = json.load(f)
    sigs = d.get("signals", [])
    total = sum(s["width"] for s in sigs)
    out = {}
    for step in d.get("steps", []):
        bits = step.get("bits", "")
        if len(bits) != total:
            continue
        pos = total
        for s in sigs:
            w = s["width"]
            chunk = bits[pos - w:pos]
            pos -= w
            if len(s["path"]) != 1 or s.get("init_only"):
                continue
            name = s["path"][0].lstrip("\\")
            if s.get("offset", 0) != 0:
                name = f"{name}@{s['offset']}"
            out.setdefault(name, []).append(chunk)
    return out


_VAR = re.compile(r"\$var\s+\S+\s+(\d+)\s+(\S+)\s+(\S+)(?:\s+\[[^\]]*\])?\s+\$end")


def read_vcd(path: str) -> dict:
    """smtbmc VCD -> {hierarchical name (without the top scope): [value
    string per smt_step]}."""
    scopes, ids, step_id = [], {}, None
    with open(path, errors="replace") as f:
        text = f.read()
    head, _, body = text.partition("$enddefinitions")
    for tok in re.finditer(r"\$scope\s+\S+\s+(\S+)\s+\$end|\$upscope\s+\$end|" + _VAR.pattern, head):
        s = tok.group(0)
        if s.startswith("$scope"):
            scopes.append(tok.group(1))
        elif s.startswith("$upscope"):
            scopes.pop()
        else:
            ident, name = tok.group(3), tok.group(4)
            if name == "smt_step":
                step_id = ident
                continue
            full = ".".join(scopes[1:] + [name]) if scopes else name
            ids.setdefault(ident, []).append(full)
    cur, out, step = {}, {}, None

    def snapshot():
        if step is None:
            return
        for ident, names in ids.items():
            v = cur.get(ident)
            if v is None:
                continue
            for n in names:
                lst = out.setdefault(n, [])
                while len(lst) < step:
                    lst.append(None)
                if len(lst) == step:
                    lst.append(v)
                else:
                    lst[step] = v

    for line in body.splitlines():
        line = line.strip()
        if not line:
            continue
        if line[0] == "#":
            snapshot()
            continue
        if line[0] in "bBrR":
            val, _, ident = line[1:].partition(" ")
        elif line[0] in "01xXzZ":
            val, ident = line[0], line[1:]
        else:
            continue
        if ident == step_id:
            try:
                step = int(val, 2)
            except ValueError:
                pass
            continue
        cur[ident] = val
    snapshot()
    return out


def _norm(v: str | None, width: int) -> str | None:
    if v is None:
        return None
    v = v.lower()
    if len(v) < width:
        v = (v[0] if v[0] in "xz" else "0") * (width - len(v)) + v
    return v[-width:]


def stim_module(ports: list, values: dict, last_step: int) -> str:
    """Verilog for fvl_stim: pins each listed port to its traced value per
    step, and covers reaching `last_step` (so the replay always yields a
    trace to compare against)."""
    lines = ["module fvl_stim ("]
    lines.append(",\n".join(f"  input [{w - 1}:0] p{i}" for i, (_, w) in enumerate(ports)))
    lines.append(");")
    lines.append("  (* gclk *) wire gclk;")
    lines.append("  reg [15:0] n = 16'd0;")
    lines.append("  always @(posedge gclk) if (n != 16'hffff) n <= n + 16'd1;")
    lines.append("  always @* begin")
    lines.append("    case (n)")
    for k in range(last_step + 1):
        conds = []
        for i, (name, w) in enumerate(ports):
            vals = values.get(name, [])
            if k >= len(vals) or vals[k] is None:
                continue
            v = _norm(vals[k], w)
            mask = "".join("0" if ch not in "01" else "1" for ch in v)
            val = "".join(ch if ch in "01" else "0" for ch in v)
            if "1" not in mask:
                continue
            conds.append(f"assume ((p{i} & {w}'b{mask}) == {w}'b{val});")
        if conds:
            lines.append(f"      16'd{k}: begin " + " ".join(conds) + " end")
    lines.append("      default: ;")
    lines.append("    endcase")
    lines.append("  end")
    lines.append(f"  always @* cover (n == 16'd{last_step});")
    lines.append("endmodule")
    return "\n".join(lines) + "\n"


def divergent(slice_vcd: dict, replay_vcd: dict, cut_nets: dict, last_step: int) -> set:
    """Cut cells whose traced value differs from the real (replayed) one at
    some step up to the failure.  cut_nets maps cell -> [(net name, width)].
    A cell whose value cannot be observed in both traces counts as divergent
    (restoring it is always safe)."""
    out = set()
    for cell, nets in cut_nets.items():
        if not nets:
            out.add(cell)
            continue
        for name, w in nets:
            a, b = slice_vcd.get(name), replay_vcd.get(name)
            if a is None or b is None:
                out.add(cell)
                break
            diff = False
            for k in range(min(last_step + 1, len(a), len(b))):
                va, vb = _norm(a[k], w), _norm(b[k], w)
                if va is None or vb is None or "x" in va or "x" in vb:
                    continue
                if va != vb:
                    diff = True
                    break
            if diff:
                out.add(cell)
                break
    return out
