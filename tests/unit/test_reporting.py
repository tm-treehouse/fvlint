# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""fvlint.checks, fvlint.waivers and fvlint.report."""

from __future__ import annotations

import json
import unittest
import xml.etree.ElementTree as ET

from fvlint.checks import ERROR, FAIL, INFO, PROVEN, SEVERITY, UNKNOWN, VACUOUS, WAIVED, WARN, Check, Result
from fvlint import report
from fvlint.checks import src_key
from fvlint.report import console, write_json, write_junit
from fvlint.waivers import Waivers, _glob_match

from .support import TempDirCase


def res(kind, target, status, src="a.v:1", detail="", **kw):
    return Result(check=Check(kind=kind, target=target, src=src, desc=f"{kind} holds"), status=status,
                  detail=detail, **kw)


class Model(unittest.TestCase):
    def test_severity_order(self):
        self.assertEqual(SEVERITY, [FAIL, ERROR, VACUOUS, UNKNOWN, WARN, INFO, PROVEN, WAIVED])

    def test_check_id_and_roots(self):
        c = Check(kind="k", target="t", src="", desc="", ports={"v": [1, 2], "e": [3]}, conds=[(4, 1), (5, 0)])
        self.assertEqual(c.id, "k:t")
        self.assertEqual(c.roots(), [1, 2, 3, 4, 5])
        self.assertEqual(Check("k", "t", "", "").roots(), [])

    def test_undecided_result_defaults(self):
        d = Result(check=Check("k", "t", "a.v:1", "p"), status=WAIVED).to_dict()
        self.assertEqual({k: d[k] for k in ("detail", "cone", "full_design", "trace", "cex_step", "engine",
                                             "lemmas_used", "refinements", "vacuity", "history", "waiver")},
                         {"detail": "", "cone": None, "full_design": False, "trace": None, "cex_step": None,
                          "engine": None, "lemmas_used": 0, "refinements": 0, "vacuity": None, "history": [],
                          "waiver": None})

    def test_defaults_are_not_shared(self):
        a, b = Check("k", "a", "", ""), Check("k", "b", "", "")
        a.conds.append((1, 1))
        a.params["W"] = 1
        self.assertEqual((b.conds, b.params), ([], {}))
        r1, r2 = res("k", "a", PROVEN), res("k", "b", PROVEN)
        r1.history.append(("0", "pass"))
        self.assertEqual(r2.history, [])

    def test_result_dict(self):
        r = res("counter_overflow", "q", FAIL, detail="cex", level="full", full=True, trace="t.vcd", step=4,
                engine="PDR", lemmas_used=2, refinements=1, vacuity="ok", history=[("0", "fail")], waiver=None)
        d = r.to_dict()
        self.assertEqual(d, {
            "id": "counter_overflow:q", "kind": "counter_overflow", "target": "q", "src": "a.v:1",
            "property": "counter_overflow holds", "status": FAIL, "detail": "cex", "cone": "full",
            "full_design": True, "trace": "t.vcd", "cex_step": 4, "engine": "PDR", "lemmas_used": 2,
            "refinements": 1, "vacuity": "ok", "history": [("0", "fail")], "waiver": None})
        json.dumps(d)                                                   # serialisable


class WaiverRules(TempDirCase):
    def test_load(self):
        p = self.write("w.txt", "# header comment\n\ncounter_overflow:u_timer.*   # wrap is intended\n"
                                "fsm_trap:*\n   parallel_case:gnt#2  #  \n#tight\nk:t\t#tab\n")
        w = Waivers.load(p)
        self.assertEqual(w.rules, [("counter_overflow:u_timer.*", "wrap is intended"), ("fsm_trap:*", "waived"),
                                   ("parallel_case:gnt#2", "waived"), ("k:t", "tab")])
        self.assertEqual(Waivers.load(None).rules, [])

    def test_reported_ids_waive_themselves(self):
        # Ids may contain '#' (numbered duplicates) and glob metacharacters.
        ids = [("parallel_case", "gnt#1"), ("counter_overflow", "q[3:2]"), ("fsm_trap", "st={2'b10, 2'b11}"),
               ("fsm_unreachable", "st=2'b11")]
        p = self.write("w.txt", "".join(f"{k}:{t}   # reviewed\n" for k, t in ids))
        w = Waivers.load(p)
        for kind, target in ids:
            with self.subTest(target=target):
                self.assertIsNotNone(w.match(Check(kind, target, "", "")))
        self.assertIsNone(w.match(Check("parallel_case", "gnt", "", "")))
        self.assertIsNone(w.match(Check("counter_overflow", "q3", "", "")))

    def test_globs_are_case_sensitive_and_anchored(self):
        w = Waivers()
        w.rules = [("counter_overflow:u_timer.*", "r")]
        self.assertEqual(w.match(Check("counter_overflow", "u_timer.ticks", "", "")),
                         "waiver file: counter_overflow:u_timer.* (r)")
        for kind, target in (("counter_overflow", "U_TIMER.ticks"), ("counter_overflow", "x.u_timer.q"),
                             ("counter_underflow", "u_timer.ticks")):
            with self.subTest(target=target):
                self.assertIsNone(w.match(Check(kind, target, "", "")))

    def test_brackets_are_literal_in_globs(self):
        cases = [("q[1]x", "q[1]*", True), ("q1x", "q[1]*", False), ("a]b", "a]*", True), ("a[b", "a[*", True),
                 ("q[3:2]", "q[3:2]", True), ("q3", "q[3:2]", False), ("u.q[7]", "u.*[?]", True)]
        for cid, pat, want in cases:
            with self.subTest(cid=cid, pat=pat):
                self.assertEqual(_glob_match(cid, pat), want)

    def test_attribute(self):
        w = Waivers()
        self.assertTrue(w.match(Check("mem_addr", "m.rd0", "", "", waive_attr="all")))
        self.assertTrue(w.match(Check("mem_addr", "m.rd0", "", "", waive_attr=" counter_overflow , mem_addr")))
        self.assertIsNone(w.match(Check("mem_addr", "m.rd0", "", "", waive_attr="mem")))
        self.assertIsNone(w.match(Check("mem_addr", "m.rd0", "", "", waive_attr="")))
        self.assertEqual(w.match(Check("k", "t", "", "", waive_attr="k")), "fvlint_waive attribute (k)")

    def test_file_rule_reported_before_attribute(self):
        w = Waivers()
        w.rules = [("k:*", "file")]
        self.assertTrue(w.match(Check("k", "t", "", "", waive_attr="k")).startswith("waiver file"))


class Reports(TempDirCase):
    def setUp(self):
        super().setUp()
        self.results = [
            res("counter_overflow", "a", PROVEN, src="b.v:9"),
            res("mem_addr", "m.rd0", FAIL, src="b.v:3", detail="counterexample at step 4", trace="jobs/t.vcd"),
            res("parallel_case", "y<&\"z\"", UNKNOWN, src="a.v:2", detail="not <proven> & 'odd'"),
            res("fsm_trap", "st={2'b10}", WARN),
            res("fsm_summary", "st", INFO),
            res("counter_overflow", "b", VACUOUS, detail="vacuous"),
            res("index_range", "sel", WAIVED, detail="waiver"),
            res("full_case", "y", ERROR, detail="tool error"),
        ]

    def test_console_summary_order_and_hiding(self):
        text = console(self.results)
        lines = text.splitlines()
        self.assertEqual(lines[0], "fvlint: 8 checks: 1 fail, 1 error, 1 vacuous, 1 unknown, 1 warn, 1 info, "
                                   "1 proven, 1 waived")
        statuses = [ln.split()[0] for ln in lines[2:-1]]
        self.assertEqual(statuses, [FAIL, ERROR, VACUOUS, UNKNOWN, WARN, INFO])
        self.assertEqual(lines[-1], "(1 proven and 1 waived checks hidden; use -v)")
        verbose = console(self.results, verbose=True)
        self.assertIn("counter_overflow:a", verbose)
        self.assertNotIn("hidden", verbose)

    def test_console_columns_are_aligned_and_capped(self):
        rs = [res("k", "x" * 100, FAIL, src="s" * 50, detail="D1"), res("k", "y", UNKNOWN, src="s.v:1", detail="D2")]
        lines = console(rs).splitlines()[2:]
        self.assertTrue(lines[0].endswith("D1") and lines[1].endswith("D2"))
        self.assertEqual(lines[1].index("D2"), len("UNKNOWN") + 2 + report.ID_WIDTH + 2 + report.SRC_WIDTH + 2)

    def test_console_nothing_to_show(self):
        self.assertEqual(console([]), "fvlint: 0 checks: \n")
        self.assertEqual(console([res("k", "t", PROVEN)]).splitlines()[-1],
                         "(1 proven and 0 waived checks hidden; use -v)")

    def test_json(self):
        p = f"{self.tmp}/r.json"
        write_json(self.results, p, {"top": "t"})
        with open(p) as f:
            d = json.load(f)
        self.assertEqual(d["meta"], {"top": "t"})
        self.assertEqual([r["status"] for r in d["results"]],
                         [FAIL, ERROR, VACUOUS, UNKNOWN, WARN, INFO, PROVEN, WAIVED])

    def test_order_within_a_status_is_by_source_then_id(self):
        rs = [res("k", "b", FAIL, src="b.v:1"), res("k", "z", FAIL, src="a.v:9"), res("k", "a", FAIL, src="b.v:1")]
        p = f"{self.tmp}/r.json"
        write_json(rs, p, {})
        with open(p) as f:
            self.assertEqual([r["id"] for r in json.load(f)["results"]], ["k:z", "k:a", "k:b"])

    def test_lines_sort_numerically_within_a_file(self):
        rs = [res("k", t, FAIL, src=src) for t, src in (("a", "a.v:10"), ("b", "a.v:9"), ("c", "?"), ("d", "a.v"))]
        p = f"{self.tmp}/r.json"
        write_json(rs, p, {})
        with open(p) as f:
            self.assertEqual([r["id"] for r in json.load(f)["results"]], ["k:c", "k:d", "k:b", "k:a"])
        self.assertEqual([src_key(x) for x in ("a.v:9", "a.v:10", "?", "", "c:/w/a.v:3", "a.v:x")],
                         [("a.v", 9), ("a.v", 10), ("?", 0), ("", 0), ("c:/w/a.v", 3), ("a.v:x", 0)])

    def test_junit(self):
        p = f"{self.tmp}/j.xml"
        write_junit(self.results, p, suite="my<suite>")
        root = ET.parse(p).getroot()                                    # well-formed despite <, &, quotes
        self.assertEqual((root.tag, root.get("name"), root.get("tests"), root.get("failures"), root.get("skipped")),
                         ("testsuite", "my<suite>", "8", "3", "1"))
        cases = {tc.get("name"): tc for tc in root}
        fail = cases["mem_addr:m.rd0"].find("failure")
        self.assertEqual(fail.get("message"), FAIL)
        self.assertEqual(fail.text, "b.v:3: mem_addr holds: counterexample at step 4 trace: jobs/t.vcd")
        self.assertEqual(cases["counter_overflow:b"].find("failure").get("message"), VACUOUS)
        skipped = cases["parallel_case:y<&\"z\""].find("skipped")
        self.assertEqual(skipped.get("message"), "a.v:2: parallel_case holds: not <proven> & 'odd'")
        self.assertEqual(cases["counter_overflow:a"].find("system-out").text, "PROVEN: b.v:9: counter_overflow holds: ")
        self.assertEqual(cases["counter_overflow:a"].get("classname"), "counter_overflow")


if __name__ == "__main__":
    unittest.main()
