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
