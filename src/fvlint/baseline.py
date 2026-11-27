# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Baselines: the findings a design is known to have, so that CI fails only
on new ones.

    fvlint ... --baseline fvlint/baseline.json --update-baseline   # record
    fvlint ... --baseline fvlint/baseline.json                     # compare

A baseline file lists check ids with their status, for every result that is
a finding (FAIL, ERROR, VACUOUS, UNKNOWN, WARN):

    {
      "fvlint_baseline": 1,
      "top": "demo_top",
      "findings": {
        "counter_overflow:u_timer.ticks": "FAIL",
        "fsm_trap:u_ctrl.st={3'b101}": "WARN"
      }
    }

A finding is known when the baseline lists its id with the same status or a
more severe one (a FAIL that is UNKNOWN now is still known; an UNKNOWN that
is FAIL now is new).  Known findings are still reported, marked as such, but
don't count towards the exit status.  Ids are structural names, so a renamed
register or a moved case statement makes its findings new: a baseline can
hide a known finding, never a new one.  A results.json from an earlier run
works as a baseline too.
"""

from __future__ import annotations

import json
import os
from dataclasses import dataclass, field

from .checks import ERROR, FAIL, SEVERITY, UNKNOWN, VACUOUS, WARN

FORMAT = 1
FINDINGS = (FAIL, ERROR, VACUOUS, UNKNOWN, WARN)


class BaselineError(Exception):
    pass


def _kind(check_id: str) -> str:
    return check_id.split(":", 1)[0]


@dataclass
class Baseline:
    path: str
    findings: dict = field(default_factory=dict)     # check id -> status

    @classmethod
    def load(cls, path: str, missing_ok: bool = False) -> "Baseline":
        """Read a baseline file, or a results.json.  With missing_ok, a file
        that doesn't exist is an empty baseline (--update-baseline creates it)."""
        if missing_ok and not os.path.exists(path):
            return cls(path)
        try:
            with open(path) as f:
                data = json.load(f)
        except OSError as e:
            raise BaselineError(f"{path}: {e.strerror or e}") from None
        except json.JSONDecodeError as e:
            raise BaselineError(f"{path}: not valid JSON: {e}") from None
        if isinstance(data, dict) and isinstance(data.get("findings"), dict):
            if data.get("fvlint_baseline") != FORMAT:
                raise BaselineError(f"{path}: unknown baseline format {data.get('fvlint_baseline')!r} "
                                    f"(this fvlint reads format {FORMAT})")
            findings = data["findings"]
        elif isinstance(data, dict) and isinstance(data.get("results"), list):
            # A results.json: its findings.
            findings = {}
            for r in data["results"]:
                if not (isinstance(r, dict) and isinstance(r.get("id"), str)):
                    raise BaselineError(f"{path}: a result without an id")
                if r.get("status") in FINDINGS:
                    findings[r["id"]] = r["status"]
        else:
            raise BaselineError(f"{path}: not a baseline (no \"findings\") or results.json (no \"results\")")
        for cid, status in findings.items():
            if status not in FINDINGS:
                raise BaselineError(f"{path}: {cid}: {status!r} is not a finding status "
                                    f"({', '.join(FINDINGS)})")
        return cls(path, dict(findings))

    def known(self, check_id: str, status: str) -> str | None:
        """The baseline's status for a finding it already lists (with that
        status or a more severe one), else None."""
        old = self.findings.get(check_id)
        if status in FINDINGS and old is not None and SEVERITY.index(old) <= SEVERITY.index(status):
            return old
        return None

    def apply(self, results):
        """Mark each known finding (Result.baseline: the baseline's status)."""
        for r in results:
            r.baseline = self.known(r.check.id, r.status)

    def stale(self, results, kinds) -> tuple:
        """(gone, fixed): ids the baseline lists that no check has any more,
        and ids whose check is no finding now; both mean the baseline wants
        updating.  Only ids of the check kinds that ran (`kinds`) count."""
        status = {r.check.id: r.status for r in results}
        gone, fixed = [], []
        for cid in sorted(self.findings):
            if _kind(cid) not in kinds:
                continue
            if cid not in status:
                gone.append(cid)
            elif status[cid] not in FINDINGS:
                fixed.append(cid)
        return gone, fixed

    def updated(self, results, kinds) -> dict:
        """The findings of this run, plus the baseline's entries for check
        kinds that didn't run (so --checks doesn't drop them)."""
        out = {cid: st for cid, st in self.findings.items() if _kind(cid) not in kinds}
        out.update({r.check.id: r.status for r in results if r.status in FINDINGS})
        return out

    def lines(self, ids) -> dict:
        """{id: line number of the file where it is listed} for annotations."""
        try:
            with open(self.path) as f:
                text = f.read().splitlines()
        except OSError:
            return {}
        out = {}
        for cid in ids:
            quoted = json.dumps(cid)
            n = next((i for i, line in enumerate(text, 1) if quoted in line), None)
            if n is not None:
                out[cid] = n
        return out

    def write(self, findings: dict, top: str):
        d = os.path.dirname(os.path.abspath(self.path))
        os.makedirs(d, exist_ok=True)
        with open(self.path, "w") as f:
            json.dump({"fvlint_baseline": FORMAT, "top": top, "findings": dict(sorted(findings.items()))},
                      f, indent=2)
            f.write("\n")
