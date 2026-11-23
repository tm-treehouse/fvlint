# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Data model for generated checks, helper lemmas and results."""

from __future__ import annotations

from dataclasses import dataclass, field

# Result statuses, most severe first.
FAIL = "FAIL"          # counterexample on the full design (or replayed onto it)
ERROR = "ERROR"        # tool error, unsatisfiable assumptions, ...
VACUOUS = "VACUOUS"    # proven, but the check's enabling condition can never occur
UNKNOWN = "UNKNOWN"    # neither proven nor refuted
WARN = "WARN"
INFO = "INFO"
PROVEN = "PROVEN"
WAIVED = "WAIVED"
SEVERITY = [FAIL, ERROR, VACUOUS, UNKNOWN, WARN, INFO, PROVEN, WAIVED]


def src_key(src: str) -> tuple:
    """Sort key for 'file:line' locations: by file, then numerically by line."""
    f, _, line = (src or "").rpartition(":")
    return (f, int(line)) if line.isdigit() else (src or "", 0)


@dataclass
class Check:
    kind: str                 # e.g. counter_overflow, parallel_case, mem_addr, fsm_unreachable
    target: str               # structural name: register, memory port, destination signal
    src: str                  # file:line
    desc: str                 # one-line description of the property
    checker: str | None = None          # checker module in checkers.v (None = no proof needed)
    params: dict = field(default_factory=dict)   # checker parameters (ints)
    ports: dict = field(default_factory=dict)    # checker port -> list of bits
    conds: list = field(default_factory=list)    # [(bit, 0|1)] all must hold for the check to apply
    anchors: list = field(default_factory=list)  # state cells always kept in the cone
    waive_attr: str | None = None       # value of an fvlint_waive attribute on the object
    preset: str | None = None           # status decided without a proof (graph checks, info)
    detail: str = ""
    depth_hint: int = 0                 # BMC depth that would expose a violation, if known
    min_cycles: int | None = None       # a violation needs at least this many cycles (counters), if known
    group: str | None = None            # id of the reported check this one is a part of (case statements)
    part: str = ""                      # what this part covers (the signal a case statement assigns)

    @property
    def id(self) -> str:
        return f"{self.kind}:{self.target}"

    def roots(self) -> list:
        out = []
        for bits in self.ports.values():
            out += bits
        return out + [b for b, _ in self.conds]


@dataclass
class Lemma:
    """A candidate invariant about one state cell, offered to k-induction.

    Lemmas are guesses mined from the structure (e.g. 'counter <= its compare
    constant').  False or non-inductive ones are discarded per proof
    (Houdini-style), so a bad guess costs time but never soundness.
    """
    owner: str                # state cell the lemma talks about
    desc: str
    checker: str
    params: dict
    ports: dict
    bound: int = 0            # used to size bounded-model-check depth hints


@dataclass
class Result:
    check: Check
    status: str
    detail: str = ""
    level: str | None = None          # cone that decided the result ("0", "1", "full", "cegar")
    full: bool = False                # True if the deciding cone had no cuts
    trace: str | None = None
    step: int | None = None
    engine: str | None = None
    lemmas_used: int = 0
    refinements: int = 0
    vacuity: str | None = None        # "ok", "vacuous", "unknown" or None (not checked)
    history: list = field(default_factory=list)   # [(cone, outcome)]
    waiver: str | None = None
    seconds: float = 0.0

    def to_dict(self) -> dict:
        return {
            "id": self.check.id, "kind": self.check.kind, "target": self.check.target,
            "src": self.check.src, "property": self.check.desc, "status": self.status,
            "detail": self.detail, "cone": self.level, "full_design": self.full,
            "trace": self.trace, "cex_step": self.step, "engine": self.engine,
            "lemmas_used": self.lemmas_used, "refinements": self.refinements,
            "vacuity": self.vacuity, "history": self.history, "waiver": self.waiver,
        }


# How a part's status counts towards its case statement: any failure,
# error or open question decides; then any proof (the statement is live and
# holds); a statement is vacuous or dead only if every part is.
_MERGE_ORDER = [WAIVED, FAIL, ERROR, UNKNOWN, PROVEN, VACUOUS, WARN, INFO]


def merge_parts(results: list) -> list:
    """One result per case statement: the results of its part checks (one
    per signal it assigns, see detect_case) merged.  Other results pass
    through unchanged, in order."""
    out, groups = [], {}
    for r in results:
        g = r.check.group
        if g is None:
            out.append(r)
        else:
            if g not in groups:
                groups[g] = []
                out.append(g)
            groups[g].append(r)
    merged = []
    for item in out:
        if not isinstance(item, str):
            merged.append(item)
            continue
        parts = groups[item]
        status = min((p.status for p in parts), key=_MERGE_ORDER.index)
        lead = next(p for p in parts if p.status == status)
        kind, _, target = item.partition(":")
        chk = Check(kind=kind, target=target, src=lead.check.src, desc=lead.check.desc,
                    waive_attr=lead.check.waive_attr)
        signals = ", ".join(p.check.part for p in parts)
        detail = lead.detail
        if status not in (WAIVED, INFO, VACUOUS) or len({p.detail for p in parts}) > 1:
            detail = f"{detail} (for {lead.check.part}; checked for each signal it assigns: {signals})"
        res = Result(check=chk, status=status, detail=detail, level=lead.level, full=lead.full,
                     trace=lead.trace, step=lead.step, engine=lead.engine, lemmas_used=lead.lemmas_used,
                     refinements=sum(p.refinements for p in parts), vacuity=lead.vacuity,
                     history=lead.history, waiver=lead.waiver, seconds=round(sum(p.seconds for p in parts), 2))
        merged.append(res)
    return merged
