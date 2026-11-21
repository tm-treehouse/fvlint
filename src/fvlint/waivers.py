# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Waivers: a file of check-id globs, or an fvlint_waive attribute in the RTL.

Waiver file format (one per line, '#' starts the reason/comment):

    counter_overflow:u_timer.ticks     # free-running timebase, wrap is intended
    fsm_trap:*                         # terminal states are expected in this IP

RTL attribute (on the register or memory the check is about):

    (* fvlint_waive = "counter_overflow" *) reg [15:0] ticks;
    (* fvlint_waive = "all" *) reg [7:0] scratch [0:99];
"""

from __future__ import annotations

import fnmatch


class Waivers:
    def __init__(self):
        self.rules = []   # (glob, reason)

    @classmethod
    def load(cls, path: str | None) -> "Waivers":
        w = cls()
        if path:
            with open(path) as f:
                for line in f:
                    pat, _, reason = line.partition("#")
                    pat = pat.strip()
                    if pat:
                        w.rules.append((pat, reason.strip() or "waived"))
        return w

    def match(self, check) -> str | None:
        for pat, reason in self.rules:
            if fnmatch.fnmatchcase(check.id, pat):
                return f"waiver file: {pat} ({reason})"
        if check.waive_attr:
            kinds = {k.strip() for k in str(check.waive_attr).split(",")}
            if "all" in kinds or check.kind in kinds:
                return f"fvlint_waive attribute ({check.waive_attr})"
        return None
