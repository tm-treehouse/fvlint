# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""fvlint.baseline: reading, matching and writing known findings."""

from __future__ import annotations

import json
import os
import unittest

from fvlint.baseline import FINDINGS, FORMAT, Baseline, BaselineError
from fvlint.checks import ERROR, FAIL, INFO, PROVEN, SEVERITY, UNKNOWN, VACUOUS, WAIVED, WARN, Check, Result

from .support import TempDirCase


def res(cid: str, status: str) -> Result:
    kind, _, target = cid.partition(":")
    return Result(check=Check(kind, target, "a.v:1", "p"), status=status)


class Load(TempDirCase):
    def test_baseline_file(self):
        p = self.write_json("b.json", {"fvlint_baseline": 1, "top": "t",
                                       "findings": {"counter_overflow:q": "FAIL", "fsm_trap:s={2'b01}": "WARN"}})
        b = Baseline.load(p)
        self.assertEqual((b.path, b.findings), (p, {"counter_overflow:q": FAIL, "fsm_trap:s={2'b01}": WARN}))

    def test_results_json(self):
        # An earlier run's results.json: its findings, not its passes.
        p = self.write_json("r.json", {"meta": {}, "results": [
            {"id": "a:x", "status": "FAIL"}, {"id": "a:y", "status": "PROVEN"}, {"id": "b:z", "status": "UNKNOWN"},
            {"id": "c:w", "status": "WAIVED"}, {"id": "d:v", "status": "INFO"}]})
        self.assertEqual(Baseline.load(p).findings, {"a:x": FAIL, "b:z": UNKNOWN})

    def test_missing_file(self):
        p = os.path.join(self.tmp, "nope.json")
        with self.assertRaisesRegex(BaselineError, r"nope\.json: No such file"):
            Baseline.load(p)
        self.assertEqual(Baseline.load(p, missing_ok=True).findings, {})          # --update-baseline creates it
        with self.assertRaisesRegex(BaselineError, "nope.json"):
            Baseline.load(os.path.join(self.tmp, "nope.json/x"), missing_ok=False)

    def test_malformed(self):
        cases = [("{", "not valid JSON"),
                 ('{"fvlint_baseline": 2, "findings": {}}', "unknown baseline format 2"),
                 ('{"findings": {}}', "unknown baseline format None"),
                 ('{"fvlint_baseline": 1, "findings": {"a:x": "PROVEN"}}', "a:x: 'PROVEN' is not a finding status"),
                 ('{"results": [{"status": "FAIL"}]}', "a result without an id"),
                 ('{"results": ["a:x"]}', "a result without an id"),
                 ('{"results": [{"id": 3, "status": "FAIL"}]}', "a result without an id"),
                 ('{"findings": ["a:x"]}', "not a baseline"),
                 ('[]', "not a baseline"),
                 ('{"results": {}}', "not a baseline")]
        for text, msg in cases:
            with self.subTest(text=text):
                p = self.write("bad.json", text)
                with self.assertRaises(BaselineError) as cm:
                    Baseline.load(p)
                self.assertIn(msg, str(cm.exception))
                self.assertTrue(str(cm.exception).startswith(p + ": "))

    def test_every_finding_status_is_accepted(self):
        self.assertEqual(FINDINGS, (FAIL, ERROR, VACUOUS, UNKNOWN, WARN))
        self.assertEqual(FORMAT, 1)
        p = self.write_json("b.json", {"fvlint_baseline": 1, "findings": {f"k:{s}": s for s in FINDINGS}})
        self.assertEqual(len(Baseline.load(p).findings), 5)


class Matching(unittest.TestCase):
    def test_known_with_the_same_or_a_more_severe_status(self):
        for old in FINDINGS:
            for new in SEVERITY:
                with self.subTest(old=old, new=new):
                    b = Baseline("b.json", {"k:x": old})
                    want = old if new in FINDINGS and SEVERITY.index(old) <= SEVERITY.index(new) else None
                    self.assertEqual(b.known("k:x", new), want)
        self.assertEqual(Baseline("b.json", {"k:x": FAIL}).known("k:FAIL", FAIL), None)   # by id only

    def test_apply_marks_results(self):
        b = Baseline("b.json", {"k:a": FAIL, "k:b": UNKNOWN, "k:c": FAIL})
        rs = [res("k:a", FAIL), res("k:b", FAIL), res("k:c", PROVEN), res("k:d", FAIL)]
        rs[2].baseline = "stale"
        b.apply(rs)
        self.assertEqual([r.baseline for r in rs], [FAIL, None, None, None])

    def test_stale_entries(self):
        b = Baseline("b.json", {"k:gone": FAIL, "k:fixed": FAIL, "k:waived": WARN, "k:still": UNKNOWN,
                                "other:x": FAIL})
        rs = [res("k:fixed", PROVEN), res("k:waived", WAIVED), res("k:still", UNKNOWN), res("k:new", FAIL)]
        self.assertEqual(b.stale(rs, {"k"}), (["k:gone"], ["k:fixed", "k:waived"]))
        self.assertEqual(b.stale(rs, {"k", "other"}), (["k:gone", "other:x"], ["k:fixed", "k:waived"]))
        self.assertEqual(b.stale(rs, set()), ([], []))
        self.assertEqual(b.stale([res("k:fixed", INFO), res("k:gone", ERROR)], {"k"}),
                         (["k:still", "k:waived"], ["k:fixed"]))

    def test_updated_keeps_kinds_that_did_not_run(self):
        b = Baseline("b.json", {"k:old": FAIL, "fsm_trap:s": WARN, "k:fixed": FAIL})
        rs = [res("k:new", UNKNOWN), res("k:fixed", PROVEN), res("k:w", WAIVED), res("k:v", VACUOUS)]
        self.assertEqual(b.updated(rs, {"k"}), {"fsm_trap:s": WARN, "k:new": UNKNOWN, "k:v": VACUOUS})
        self.assertEqual(b.updated(rs, {"k", "fsm_trap"}), {"k:new": UNKNOWN, "k:v": VACUOUS})


class Write(TempDirCase):
    def test_round_trip_sorted_one_per_line(self):
        p = os.path.join(self.tmp, "sub", "dir", "b.json")
        b = Baseline(p)
        b.write({"z:1": FAIL, "a:2": WARN}, "top")
        with open(p) as f:
            text = f.read()
        self.assertEqual(text, '{\n  "fvlint_baseline": 1,\n  "top": "top",\n  "findings": {\n'
                               '    "a:2": "WARN",\n    "z:1": "FAIL"\n  }\n}\n')
        self.assertEqual(json.loads(text), {"fvlint_baseline": 1, "top": "top",
                                            "findings": {"a:2": WARN, "z:1": FAIL}})
        self.assertLess(text.index('"a:2"'), text.index('"z:1"'))
        self.assertEqual(len([ln for ln in text.splitlines() if '": "' in ln and ":" in ln]), 3)
        self.assertEqual(Baseline.load(p).findings, {"a:2": WARN, "z:1": FAIL})

    def test_relative_path(self):
        self.chdir(self.tmp)
        Baseline("b.json").write({}, "t")
        self.assertTrue(os.path.exists(os.path.join(self.tmp, "b.json")))

    def test_lines(self):
        p = self.write("b.json", '{\n  "findings": {\n    "k:a": "FAIL",\n    "k:ab": "WARN"\n  }\n}\n')
        b = Baseline(p)
        self.assertEqual(b.lines(["k:ab", "k:a", "k:zz"]), {"k:a": 3, "k:ab": 4})
        self.assertEqual(Baseline(os.path.join(self.tmp, "missing.json")).lines(["k:a"]), {})


if __name__ == "__main__":
    unittest.main()
