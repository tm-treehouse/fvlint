# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""fvlint.checks, fvlint.waivers and fvlint.report."""

from __future__ import annotations

import json
import os
import unittest
import xml.etree.ElementTree as ET

from fvlint.checks import ERROR, FAIL, INFO, PROVEN, SEVERITY, UNKNOWN, VACUOUS, WAIVED, WARN, Check, Result
from fvlint import report
from fvlint.checks import DEAD_STATE, FREE_RUNNING, FULL_CASE_X, HORIZON, merge_parts, src_key
from fvlint.report import _gh_location, console, github_annotations, markdown, write_json, write_junit
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
            "refinements": 1, "vacuity": "ok", "history": [("0", "fail")], "waiver": None, "reason": None,
            "baseline": None, "condition": None})
        json.dumps(d)                                                   # serialisable

    def test_reason_of_info_results(self):
        c = Check("counter_overflow", "q", "a.v:1", "p", reason=HORIZON)
        self.assertEqual(Result(check=c, status=INFO).to_dict()["reason"], "horizon")
        self.assertIsNone(Result(check=c, status=WAIVED).to_dict()["reason"])      # waived: no INFO to explain
        self.assertIsNone(Result(check=Check("k", "t", "", ""), status=INFO).to_dict()["reason"])
        self.assertEqual((FREE_RUNNING, HORIZON, DEAD_STATE, FULL_CASE_X),
                         ("free_running", "horizon", "dead_state", "full_case_x"))


class WaiverRules(TempDirCase):
    def test_load(self):
        p = self.write("w.txt", "# header comment\n\ncounter_overflow:u_timer.*   # wrap is intended\n"
                                "fsm_trap:*\n   parallel_case:gnt#2  #  \n#tight\nk:t\t#tab\n")
        w = Waivers.load(p)
        self.assertEqual(w.rules, [("counter_overflow:u_timer.*", "wrap is intended", 3), ("fsm_trap:*", "waived", 4),
                                   ("parallel_case:gnt#2", "waived", 5), ("k:t", "tab", 7)])
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
        w.rules = [("counter_overflow:u_timer.*", "r", 1)]
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
        w.rules = [("k:*", "file", 1)]
        self.assertTrue(w.match(Check("k", "t", "", "", waive_attr="k")).startswith("waiver file"))


class UnusedWaivers(TempDirCase):
    def test_unused(self):
        p = self.write("w.txt", "counter_overflow:a   # used\n"
                                "counter_overflow:*   # also matches a: used too\n"
                                "parallel_case:gnt#2  # renamed since\n"
                                "fsm_trap:*           # kind not run\n"
                                "*:old                # any kind\n"
                                "parallel_case:a,b    # a statement, by its id\n")
        w = Waivers.load(p)
        w.match(Check("counter_overflow", "a", "", ""))
        w.match(Check("parallel_case", "a,b~0", "", "", group="parallel_case:a,b"))
        self.assertEqual(w.unused(), [(3, "parallel_case:gnt#2"), (4, "fsm_trap:*"), (5, "*:old")])
        self.assertEqual(w.unused({"counter_overflow", "parallel_case"}), [(3, "parallel_case:gnt#2"), (5, "*:old")])
        self.assertEqual(Waivers.load(None).unused(), [])


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




class MergeParts(unittest.TestCase):
    """merge_parts: one result per case statement from its per-signal parts."""

    @staticmethod
    def part(group, part, status, detail="d", **kw):
        kind, _, target = group.partition(":")
        c = Check(kind=kind, target=f"{target}~{part}", src="c.v:9", desc="p", group=group, part=part)
        return Result(check=c, status=status, detail=detail, **kw)

    def merged(self, *statuses, details=None):
        parts = [self.part("parallel_case:a,b", f"s{i}", st, (details or {}).get(i, "d"))
                 for i, st in enumerate(statuses)]
        (r,) = merge_parts(parts)
        return r

    def test_status(self):
        cases = [((PROVEN, FAIL, VACUOUS), FAIL), ((PROVEN, ERROR), ERROR), ((PROVEN, UNKNOWN), UNKNOWN),
                 ((PROVEN, VACUOUS), PROVEN), ((VACUOUS, VACUOUS), VACUOUS), ((INFO, VACUOUS), VACUOUS),
                 ((INFO, INFO), INFO), ((INFO, PROVEN), PROVEN), ((WAIVED, WAIVED), WAIVED)]
        for statuses, want in cases:
            with self.subTest(statuses=statuses):
                self.assertEqual(self.merged(*statuses).status, want)

    def test_the_deciding_part_is_reported(self):
        parts = [self.part("parallel_case:a,b", "a", PROVEN, "proven by PDR"),
                 self.part("parallel_case:a,b", "b", FAIL, "counterexample at step 3", trace="t.vcd", step=3,
                           refinements=1, seconds=1.5)]
        (r,) = merge_parts(parts)
        self.assertEqual((r.check.id, r.check.kind, r.check.target, r.check.group), ("parallel_case:a,b",
                                                                                   "parallel_case", "a,b", None))
        self.assertEqual((r.trace, r.step, r.refinements, r.seconds), ("t.vcd", 3, 1, 1.5))
        self.assertEqual(r.detail, "counterexample at step 3 (for b; checked for each signal it assigns: a, b)")

    def test_detail_of_agreeing_parts(self):
        self.assertEqual(self.merged(INFO, INFO).detail, "d")              # dead: the same reason for every part
        self.assertEqual(self.merged(VACUOUS, VACUOUS, details={1: "e"}).detail,
                         "d (for s0; checked for each signal it assigns: s0, s1)")

    def test_reason(self):
        def merged(*parts):
            rs = [self.part("parallel_case:a,b", f"s{i}", st) for i, (st, _) in enumerate(parts)]
            for r, (_, why) in zip(rs, parts):
                r.check.reason = why
            (r,) = merge_parts(rs)
            return r.to_dict()["reason"]
        self.assertEqual(merged((INFO, DEAD_STATE), (INFO, DEAD_STATE)), "dead_state")
        self.assertIsNone(merged((INFO, DEAD_STATE), (INFO, FULL_CASE_X)))        # mixed: no one reason
        self.assertIsNone(merged((INFO, FULL_CASE_X), (VACUOUS, None)))           # VACUOUS decides
        self.assertEqual(merged((INFO, FULL_CASE_X), (VACUOUS, None), (INFO, FULL_CASE_X)), None)

    def test_order_and_other_results(self):
        lone = Result(check=Check(kind="mem_addr", target="m.wr0", src="m.v:1", desc="x"), status=PROVEN)
        parts = [self.part("parallel_case:a,b", "a", PROVEN), lone, self.part("parallel_case:a,b", "b", PROVEN),
                 self.part("full_case:a,b", "a", FAIL)]
        self.assertEqual([r.check.id for r in merge_parts(parts)],
                         ["parallel_case:a,b", "mem_addr:m.wr0", "full_case:a,b"])
        self.assertEqual(merge_parts([]), [])


class CiFormats(TempDirCase):
    def test_markdown(self):
        rs = [res("counter_overflow", "a|b", FAIL, src="r.v:3", detail="line1\nline2"),
              res("mem_addr", "m.wr0", PROVEN, src="r.v:9")]
        text = markdown(rs, {"elapsed_s": 1.5}, "top", [(4, "x:y")], "w.txt")
        self.assertEqual(text, "### fvlint: top\n\n1 fail, 1 proven in 1.5 s\n\n"
                               "| Status | Check | Location | Detail |\n|---|---|---|---|\n"
                               "| FAIL | `counter_overflow:a\\|b` | r.v:3 | line1 line2 |\n\n"
                               "Waivers in `w.txt` that match no check:\n\n- line 4: `x:y`\n\n")
        self.assertEqual(markdown([], {}, "t"), "### fvlint: t\n\nno checks in ? s\n\n")

    def test_annotations(self):
        os.makedirs(os.path.join(self.tmp, "rtl"))
        rtl = os.path.join(self.tmp, "rtl", "a.v")
        rs = [res("counter_overflow", "q", FAIL, src=f"{rtl}:7", detail="50%\ndone"),
              res("index_range", "x", UNKNOWN, src="?"), res("fsm_trap", "s", WARN, src=f"{rtl}:2"),
              res("mem_addr", "m", PROVEN, src=f"{rtl}:1"), res("parallel_case", "p", VACUOUS, src="/elsewhere/b.v:3")]
        got = github_annotations(rs, self.tmp, [(3, "k:t")], os.path.join(self.tmp, "w.txt"), ["mem_addr:m"])
        self.assertEqual(got, [
            "::error title=fvlint FAIL%3A counter_overflow%3Aq,file=rtl/a.v,line=7::counter_overflow holds: "
            "50%25%0Adone",
            "::error title=fvlint VACUOUS%3A parallel_case%3Ap::parallel_case holds: ",
            "::warning title=fvlint UNKNOWN%3A index_range%3Ax::index_range holds: ",
            "::warning title=fvlint WARN%3A fsm_trap%3As,file=rtl/a.v,line=2::fsm_trap holds: ",
            "::warning title=fvlint%3A unused waiver,file=w.txt,line=3::k:t matches no check (renamed, fixed or no "
            "longer present?)",
            "::notice title=fvlint%3A waiver no longer needed::mem_addr:m passes now; its waiver can go"])
        self.assertEqual(_gh_location("a,b.v:3", self.tmp), "")         # outside the checkout
        self.assertEqual(_gh_location(os.path.join(self.tmp, "x.v:y"), self.tmp), "")     # no line number
        self.assertEqual(_gh_location(":4", self.tmp), "")
        odd = os.path.join(self.tmp, "a,b:c.v")
        self.assertEqual(_gh_location(f"{odd}:4", self.tmp), ",file=a%2Cb%3Ac.v,line=4")
        (err,) = github_annotations([res("mem_addr", "m", ERROR, src="?", detail="a\rb")], self.tmp)
        self.assertEqual(err, "::error title=fvlint ERROR%3A mem_addr%3Am::mem_addr holds: a%0Db")


class BaselineReports(TempDirCase):
    """Known findings (Result.baseline) in every report."""

    def results(self):
        return [res("counter_overflow", "q", FAIL, src="r.v:3", detail="cex", baseline=FAIL),
                res("index_range", "x", UNKNOWN, src="r.v:4", detail="?", baseline=FAIL),
                res("mem_addr", "m", FAIL, src="r.v:5", detail="new"), res("fsm_trap", "s", WARN, src="r.v:6"),
                res("full_case", "c", PROVEN, src="r.v:7")]

    META = {"file": "fvlint/b.json", "gone": ["k:gone"], "fixed": ["k:fixed"], "lines": {"k:gone": 4}}

    def test_console(self):
        text = console(self.results(), False, self.META)
        self.assertEqual(text.splitlines()[:2], ["fvlint: 5 checks: 2 fail, 1 unknown, 1 warn, 1 proven",
                                                 "baseline fvlint/b.json: 2 known findings, 2 new"])
        self.assertIn("counter_overflow:q  r.v:3  (in baseline) cex", text)
        self.assertIn("index_range:x       r.v:4  (in baseline as FAIL) ?", text)
        self.assertIn("mem_addr:m          r.v:5  new", text)
        self.assertNotIn("baseline", console(self.results()[2:], False))
        one = [res("a", "b", FAIL, baseline=FAIL)]
        self.assertEqual(report.baseline_summary(one, self.META), "baseline fvlint/b.json: 1 known finding, 0 new")
        self.assertEqual(report.baseline_summary(one, None), "")
        self.assertEqual(report.known_note(res("a", "b", FAIL)), "")

    def test_markdown(self):
        text = markdown(self.results(), {"elapsed_s": 2, "baseline": self.META}, "top")
        self.assertIn("\n\nbaseline fvlint/b.json: 2 known findings, 2 new\n\n", text)
        self.assertIn("| FAIL (baseline) | `counter_overflow:q` |", text)
        self.assertIn("| UNKNOWN (baseline) | `index_range:x` |", text)
        self.assertIn("| FAIL | `mem_addr:m` |", text)
        self.assertTrue(text.endswith("Entries of `fvlint/b.json` to update (`--update-baseline`):\n\n"
                                      "- `k:gone`: no such check any more\n- `k:fixed`: no finding now\n\n"))
        fixed_only = markdown(self.results(), {"baseline": dict(self.META, gone=[])}, "top")
        self.assertTrue(fixed_only.endswith("to update (`--update-baseline`):\n\n- `k:fixed`: no finding now\n\n"))
        quiet = markdown(self.results(), {"baseline": dict(self.META, gone=[], fixed=[])}, "top")
        self.assertNotIn("to update", quiet)
        self.assertNotIn("to update", markdown(self.results(), {"baseline": {"file": "f"}}, "top"))
        self.assertNotIn("baseline", markdown(self.results()[2:], {}, "top"))

    def test_annotations(self):
        meta = dict(self.META, file=os.path.join(self.tmp, "b.json"))
        got = github_annotations(self.results(), self.tmp, baseline=meta)
        self.assertEqual(got, [
            "::notice title=fvlint FAIL (in baseline)%3A counter_overflow%3Aq::counter_overflow holds: cex",
            "::error title=fvlint FAIL%3A mem_addr%3Am::mem_addr holds: new",
            "::notice title=fvlint UNKNOWN (in baseline)%3A index_range%3Ax::index_range holds: ?",
            "::warning title=fvlint WARN%3A fsm_trap%3As::fsm_trap holds: ",
            "::warning title=fvlint%3A baseline out of date,file=b.json,line=4::k:gone matches no check (renamed, "
            "fixed or no longer present?); update the baseline with --update-baseline",
            "::notice title=fvlint%3A baseline out of date::k:fixed is no finding now; update the baseline with "
            "--update-baseline"])
        self.assertEqual(len(github_annotations(self.results(), self.tmp, baseline={"file": "x"})), 4)

    def test_junit(self):
        p = os.path.join(self.tmp, "j.xml")
        write_junit(self.results(), p)
        root = ET.parse(p).getroot()
        self.assertEqual((root.get("tests"), root.get("failures"), root.get("skipped")), ("5", "1", "2"))
        cases = {c.get("name"): c for c in root}
        self.assertEqual(cases["counter_overflow:q"][0].tag, "skipped")
        self.assertTrue(cases["counter_overflow:q"][0].get("message").startswith(
            "known finding (FAIL, in the baseline): r.v:3: counter_overflow holds: cex"))
        self.assertTrue(cases["index_range:x"][0].get("message").startswith("known finding (UNKNOWN, in the baseline)"))
        self.assertEqual(cases["mem_addr:m"][0].tag, "failure")
        known_warn = [res("fsm_trap", "s", WARN, baseline=WARN)]
        write_junit(known_warn, p)
        self.assertEqual(ET.parse(p).getroot()[0][0].tag, "system-out")

if __name__ == "__main__":
    unittest.main()
