# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Console, JSON and JUnit XML reports."""

from __future__ import annotations

import json
import os
from collections import Counter
from xml.sax.saxutils import escape, quoteattr

from .baseline import FINDINGS
from .checks import ERROR, FAIL, PROVEN, SEVERITY, UNKNOWN, VACUOUS, WAIVED, WARN, src_key


# Console column caps (longer ids / locations run into the next column).
ID_WIDTH, SRC_WIDTH = 60, 32

def _order(r):
    return (SEVERITY.index(r.status), src_key(r.check.src), r.check.id)


def known_note(r) -> str:
    """'(in baseline) ' before the detail of a known finding."""
    if r.baseline is None:
        return ""
    return "(in baseline) " if r.baseline == r.status else f"(in baseline as {r.baseline}) "


def baseline_summary(results, baseline: dict | None) -> str:
    """'baseline FILE: 2 known findings, 1 new' when a baseline was given."""
    if not baseline:
        return ""
    known = sum(r.baseline is not None for r in results)
    new = sum(r.baseline is None and r.status in FINDINGS for r in results)
    return (f"baseline {baseline['file']}: {known} known finding{'s' if known != 1 else ''}, "
            f"{new} new")


def console(results, verbose=False, baseline: dict | None = None) -> str:
    counts = Counter(r.status for r in results)
    summary = ", ".join(f"{counts[s]} {s.lower()}" for s in SEVERITY if counts[s])
    lines = [f"fvlint: {len(results)} checks: {summary}"]
    if baseline:
        lines.append(baseline_summary(results, baseline))
    lines.append("")
    rows = [(r.status, r.check.id, r.check.src, known_note(r) + r.detail) for r in sorted(results, key=_order)
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
    fails = sum(r.status in (FAIL, ERROR, VACUOUS) and r.baseline is None for r in results)
    skipped = sum(r.status == UNKNOWN or (r.status in (FAIL, ERROR, VACUOUS) and r.baseline is not None)
                  for r in results)
    out = ['<?xml version="1.0" encoding="UTF-8"?>',
           f'<testsuite name={quoteattr(suite)} tests="{len(results)}" failures="{fails}" skipped="{skipped}">']
    for r in sorted(results, key=_order):
        name = quoteattr(r.check.id)
        cls = quoteattr(r.check.kind)
        out.append(f"  <testcase classname={cls} name={name}>")
        msg = f"{r.check.src}: {r.check.desc}: {r.detail}"
        if r.baseline is not None and r.status in (FAIL, ERROR, VACUOUS, UNKNOWN):
            out.append(f"    <skipped message={quoteattr(f'known finding ({r.status}, in the baseline): {msg}')}/>")
        elif r.status in (FAIL, ERROR, VACUOUS):
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


def _md_cell(text) -> str:
    return str(text or "").replace("|", "\\|").replace("\n", " ")


def markdown(results, meta: dict, title: str, unused_waivers=(), waiver_file=None) -> str:
    """A Markdown section for a CI job summary: counts, then every result
    that isn't PROVEN (known findings marked), then waivers that matched no
    check and baseline entries that want updating."""
    counts = Counter(r.status for r in results)
    summary = ", ".join(f"{counts[s]} {s.lower()}" for s in SEVERITY if counts[s]) or "no checks"
    lines = [f"### fvlint: {title}", "", f"{summary} in {meta.get('elapsed_s', '?')} s", ""]
    baseline = meta.get("baseline")
    if baseline:
        lines += [_md_cell(baseline_summary(results, baseline)), ""]
    shown = [r for r in sorted(results, key=_order) if r.status != PROVEN]
    if shown:
        lines += ["| Status | Check | Location | Detail |", "|---|---|---|---|"]
        lines += [f"| {r.status}{' (baseline)' if r.baseline else ''} | `{_md_cell(r.check.id)}` | "
                  f"{_md_cell(r.check.src)} | {_md_cell(r.detail)} |" for r in shown]
        lines.append("")
    lines += _md_waivers(unused_waivers, waiver_file)
    lines += _md_baseline(baseline)
    return "\n".join(lines) + "\n"


def _md_baseline(baseline: dict | None) -> list:
    if not baseline or not (baseline.get("gone") or baseline.get("fixed")):
        return []
    out = [f"Entries of `{_md_cell(baseline['file'])}` to update (`--update-baseline`):", ""]
    out += [f"- `{_md_cell(cid)}`: no such check any more" for cid in baseline.get("gone", [])]
    out += [f"- `{_md_cell(cid)}`: no finding now" for cid in baseline.get("fixed", [])]
    return out + [""]


def _md_waivers(unused_waivers, waiver_file, where="") -> list:
    if not unused_waivers:
        return []
    return ([f"Waivers in `{_md_cell(waiver_file)}` that match no check{where}:", ""]
            + [f"- line {n}: `{_md_cell(pat)}`" for n, pat in unused_waivers] + [""])


def markdown_project_waivers(files) -> str:
    """The Markdown section for a project file's runs: waiver lines that
    matched no check in any configuration that loaded their file.  `files`:
    [(waiver file, [(line, pattern)])]."""
    lines = ["### fvlint: waivers", ""]
    for path, unused in files:
        lines += _md_waivers(unused, path, " in any configuration")
    return "\n".join(lines) + "\n"


def _gh_data(s: str) -> str:
    return str(s).replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")


def _gh_prop(s: str) -> str:
    return _gh_data(s).replace(":", "%3A").replace(",", "%2C")


def _gh_location(src: str, root: str) -> str:
    """',file=...,line=...' for a 'file:line' location inside `root`, else ''."""
    f, _, line = (src or "").rpartition(":")
    if not f or not line.isdigit():
        return ""
    rel = os.path.relpath(os.path.abspath(f), root)
    if rel.startswith(".."):
        return ""
    return f",file={_gh_prop(rel.replace(os.sep, '/'))},line={line}"


GH_LEVEL = {FAIL: "error", ERROR: "error", VACUOUS: "error", UNKNOWN: "warning", WARN: "warning"}


def github_annotations(results, root: str, unused_waivers=(), waiver_file=None, unneeded=(),
                       baseline: dict | None = None) -> list:
    """GitHub Actions workflow commands that put findings on the lines they
    are about (paths relative to `root`, the repository checkout).  Known
    findings (in the baseline) are notices."""
    out = []
    for r in sorted(results, key=_order):
        level = GH_LEVEL.get(r.status)
        if level:
            known = " (in baseline)" if r.baseline else ""
            title = _gh_prop(f"fvlint {r.status}{known}: {r.check.id}")
            out.append(f"::{'notice' if known else level} title={title}{_gh_location(r.check.src, root)}::"
                       f"{_gh_data(f'{r.check.desc}: {r.detail}')}")
    for n, pat in unused_waivers:
        loc = _gh_location(f"{waiver_file}:{n}", root) if waiver_file else ""
        out.append(f"::warning title={_gh_prop('fvlint: unused waiver')}{loc}::"
                   f"{_gh_data(f'{pat} matches no check (renamed, fixed or no longer present?)')}")
    for cid in unneeded:
        out.append(f"::notice title={_gh_prop('fvlint: waiver no longer needed')}::"
                   f"{_gh_data(f'{cid} passes now; its waiver can go')}")
    if baseline:
        lines = baseline.get("lines", {})
        for cid, what, level in ([(c, "matches no check (renamed, fixed or no longer present?)", "warning")
                                  for c in baseline.get("gone", [])]
                                 + [(c, "is no finding now", "notice") for c in baseline.get("fixed", [])]):
            loc = _gh_location(f"{baseline['file']}:{lines[cid]}", root) if cid in lines else ""
            out.append(f"::{level} title={_gh_prop('fvlint: baseline out of date')}{loc}::"
                       f"{_gh_data(f'{cid} {what}; update the baseline with --update-baseline')}")
    return out
