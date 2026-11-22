# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Console, JSON and JUnit XML reports."""

from __future__ import annotations

import json
from collections import Counter
from xml.sax.saxutils import escape, quoteattr

from .checks import ERROR, FAIL, PROVEN, SEVERITY, UNKNOWN, VACUOUS, WAIVED, src_key


# Console column caps (longer ids / locations run into the next column).
ID_WIDTH, SRC_WIDTH = 60, 32

def _order(r):
    return (SEVERITY.index(r.status), src_key(r.check.src), r.check.id)


def console(results, verbose=False) -> str:
    counts = Counter(r.status for r in results)
    summary = ", ".join(f"{counts[s]} {s.lower()}" for s in SEVERITY if counts[s])
    lines = [f"fvlint: {len(results)} checks: {summary}", ""]
    rows = [(r.status, r.check.id, r.check.src, r.detail) for r in sorted(results, key=_order)
            if verbose or r.status not in (PROVEN, WAIVED)]
    if rows:
        w1 = max(len(x[0]) for x in rows)
        w2 = min(max(len(x[1]) for x in rows), ID_WIDTH)
        w3 = min(max(len(x[2]) for x in rows), SRC_WIDTH)
        for st, cid, src, detail in rows:
            lines.append(f"{st:<{w1}}  {cid:<{w2}}  {src:<{w3}}  {detail}")
    if not verbose and (counts[PROVEN] or counts[WAIVED]):
        lines.append(f"({counts[PROVEN]} proven and {counts[WAIVED]} waived checks hidden; use -v)")
    return "\n".join(lines)


def write_json(results, path: str, meta: dict):
    with open(path, "w") as f:
        json.dump({"meta": meta, "results": [r.to_dict() for r in sorted(results, key=_order)]},
                  f, indent=2)


def write_junit(results, path: str, suite="fvlint"):
    fails = sum(r.status in (FAIL, ERROR, VACUOUS) for r in results)
    skipped = sum(r.status == UNKNOWN for r in results)
    out = ['<?xml version="1.0" encoding="UTF-8"?>',
           f'<testsuite name={quoteattr(suite)} tests="{len(results)}" failures="{fails}" skipped="{skipped}">']
    for r in sorted(results, key=_order):
        name = quoteattr(r.check.id)
        cls = quoteattr(r.check.kind)
        out.append(f"  <testcase classname={cls} name={name}>")
        msg = f"{r.check.src}: {r.check.desc}: {r.detail}"
        if r.status in (FAIL, ERROR, VACUOUS):
            out.append(f"    <failure message={quoteattr(r.status)}>{escape(msg)}"
                       f"{escape(' trace: ' + r.trace) if r.trace else ''}</failure>")
        elif r.status == UNKNOWN:
            out.append(f"    <skipped message={quoteattr(msg)}/>")
        else:
            out.append(f"    <system-out>{escape(r.status + ': ' + msg)}</system-out>")
        out.append("  </testcase>")
    out.append("</testsuite>")
    with open(path, "w") as f:
        f.write("\n".join(out) + "\n")
