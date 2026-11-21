# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Data model for generated checks, helper lemmas and results."""

from __future__ import annotations

from dataclasses import dataclass, field

# Result statuses, most severe first.
FAIL = "FAIL"
ERROR = "ERROR"
UNKNOWN = "UNKNOWN"
WARN = "WARN"
INFO = "INFO"
PROVEN = "PROVEN"
WAIVED = "WAIVED"
SEVERITY = [FAIL, ERROR, UNKNOWN, WARN, INFO, PROVEN, WAIVED]


@dataclass
class Check:
    kind: str                 # e.g. counter_overflow, parallel_case, mem_addr, fsm_unreachable
    target: str               # human-readable object name (register, memory, src location)
    src: str                  # file:line
    desc: str                 # one-line description of the property
    checker: str | None = None          # checker module in checkers.v (None = no proof needed)
    params: dict = field(default_factory=dict)   # checker parameters (ints)
    ports: dict = field(default_factory=dict)    # checker port -> list of bits
    conds: list = field(default_factory=list)    # [(bit, 0|1)] all must hold for the check to apply
    anchors: list = field(default_factory=list)  # state cells always kept in the cone
    waive_attr: str | None = None       # value of an fvlint_waive attribute on the object
    preset: str | None = None           # status decided without a proof (graph checks, info)
    depth_hint: int = 0                 # BMC depth that would expose a violation, if known
    detail: str = ""

    @property
    def id(self) -> str:
        return f"{self.kind}:{self.target}"


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
    level: int | None = None          # cone level that decided the result
    full: bool = False                # True if that cone was the whole design
    trace: str | None = None
    step: int | None = None
    lemmas_used: int = 0
    runs: int = 0
    history: list = field(default_factory=list)   # [(level, outcome)]
    waiver: str | None = None

    def to_dict(self) -> dict:
        return {
            "id": self.check.id, "kind": self.check.kind, "target": self.check.target,
            "src": self.check.src, "property": self.check.desc, "status": self.status,
            "detail": self.detail, "cone_level": self.level, "full_design": self.full,
            "trace": self.trace, "cex_step": self.step, "lemmas_used": self.lemmas_used,
            "solver_runs": self.runs, "history": self.history, "waiver": self.waiver,
        }
