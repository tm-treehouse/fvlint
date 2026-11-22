# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""fvlint.regress: manifests, judging a case run, reports and the driver.
fvlint itself is replaced by a fake subprocess."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import unittest
import xml.etree.ElementTree as ET
from unittest import mock

from fvlint import regress
from fvlint.regress import Case, Outcome, _env, _select, load_manifest, record, run_case, write_junit

from .support import TempDirCase, captured

MANIFEST = """
[defaults]
budget_s = 30
engines = ["pdr", "smtbmc"]
strict = true

[[case]]
name = "counters/a"
files = ["rtl/a.sv", "../shared/b.sv"]
top = "a"
args = ["--waivers", "{dir}/w.txt", "--depth", "9"]
expect = { "counter_overflow:q" = "PROVEN" }
tags = ["counter", "smoke"]

[[case]]
name = "fsm/b"
filelist = "lists/b.f"
top = "b"
strict = false
exit = 1
expect_error = "boom"
expect_detail = { "x:y" = "text" }
budget_s = 5
engines = ["auto"]
"""


def case(**kw):
    d = dict(name="grp/c", top="c", files=["/r/c.sv"], filelist=None, args=[], expect={}, strict=False, exit=None,
             expect_error=None, expect_detail={}, tags=[], budget_s=60.0, engines=["auto"], base="/m")
    d.update(kw)
    return Case(**d)


class Manifest(TempDirCase):
    def test_load(self):
        p = self.write("m/manifest.toml", MANIFEST)
        a, b = load_manifest(p)
        base = os.path.join(self.tmp, "m")
        self.assertEqual((a.name, a.top, a.base), ("counters/a", "a", base))
        self.assertEqual(a.files, [os.path.join(base, "rtl", "a.sv"), os.path.join(self.tmp, "shared", "b.sv")])
        self.assertEqual(a.args, ["--waivers", f"{base}/w.txt", "--depth", "9"])
        self.assertEqual((a.strict, a.budget_s, a.engines, a.filelist, a.exit),
                         (True, 30.0, ["pdr", "smtbmc"], None, None))
        self.assertEqual((a.expect, a.tags, a.expect_error, a.expect_detail), ({"counter_overflow:q": "PROVEN"},
                                                                               ["counter", "smoke"], None, {}))
        self.assertEqual((b.filelist, b.files, b.strict, b.exit), (os.path.join(base, "lists", "b.f"), [], False, 1))
        self.assertEqual((b.expect_error, b.expect_detail, b.budget_s, b.engines),
                         ("boom", {"x:y": "text"}, 5.0, ["auto"]))

    def test_built_in_defaults(self):
        p = self.write("m.toml", '[[case]]\nname = "x"\ntop = "x"\n')
        (c,) = load_manifest(p)
        self.assertEqual((c.strict, c.budget_s, c.engines, c.expect, c.tags), (False, 120.0, ["auto"], {}, []))
        self.assertEqual(load_manifest(self.write("empty.toml", "")), [])

    def test_select(self):
        cs = [case(name="counters/mod100", tags=["counter"]), case(name="fsm/clean", tags=["fsm"]),
              case(name="reset/sync", tags=["counter", "reset"])]
        names = lambda pats: [c.name for c in _select(cs, pats)]   # noqa: E731
        self.assertEqual(names([]), [c.name for c in cs])
        self.assertEqual(names(["counters/*"]), ["counters/mod100"])
        self.assertEqual(names(["counter"]), ["counters/mod100", "reset/sync"])     # tag (and substring)
        self.assertEqual(names(["clean", "reset"]), ["fsm/clean", "reset/sync"])
        self.assertEqual(names(["nothing"]), [])

    def test_env_puts_this_package_first(self):
        with mock.patch.dict(os.environ, {"PYTHONPATH": "/other"}):
            pp = _env()["PYTHONPATH"].split(os.pathsep)
        self.assertEqual(pp[1:], ["/other"])
        self.assertTrue(os.path.isfile(os.path.join(pp[0], "fvlint", "regress.py")))
        with mock.patch.dict(os.environ, {}, clear=True):
            self.assertNotIn(os.pathsep, _env()["PYTHONPATH"])


class FakeFvlint:
    """Stands in for subprocess.run of `python -m fvlint`."""

    def __init__(self, results=None, rc=0, stderr="", timeout=False):
        self.results, self.rc, self.stderr, self.timeout = results, rc, stderr, timeout
        self.cmds = []

    def __call__(self, cmd, capture_output, text, env, timeout):
        assert capture_output is True and text is True
        self.cmds.append((cmd, timeout, env))
        if self.timeout:
            raise subprocess.TimeoutExpired(cmd, timeout)
        if self.results is not None:
            out = cmd[cmd.index("-o") + 1]
            os.makedirs(out, exist_ok=True)
            with open(os.path.join(out, "results.json"), "w") as f:
                rows = [{"id": k, "status": v[0] if isinstance(v, tuple) else v,
                         "detail": v[1] if isinstance(v, tuple) else "d"} for k, v in self.results.items()]
                json.dump({"results": rows}, f)
        return subprocess.CompletedProcess(cmd, self.rc, "", self.stderr)


class Judging(TempDirCase):
    def run_with(self, c, fake, engine="auto", abc=True, scale=1.0, times=None):
        with mock.patch.object(regress.subprocess, "run", fake):
            if times:
                with mock.patch.object(regress.time, "time", side_effect=times):
                    return run_case(c, engine, self.tmp, scale, abc)
            return run_case(c, engine, self.tmp, scale, abc)

    def test_command_line(self):
        fake = FakeFvlint({})
        o = self.run_with(case(name="g/x", files=["/r/a.sv"], filelist="/r/l.f", args=["--depth", "3"], budget_s=10),
                          fake, engine="smtbmc", scale=2)
        cmd, timeout, env = fake.cmds[0]
        out = os.path.join(self.tmp, "g__x__smtbmc")
        self.assertEqual(cmd, [sys.executable, "-m", "fvlint", "--top", "c", "-o", out, "-j", "1", "--engine", "smtbmc",
                               "/r/a.sv", "--depth", "3", "-F", "/r/l.f"])
        self.assertEqual(timeout, 10 * 2 * 3 + 60)
        self.assertIn("PYTHONPATH", env)
        self.assertEqual((o.ok, o.out, o.engine), (True, out, "smtbmc"))

    def test_expectations_met(self):
        o = self.run_with(case(expect={"a": "PROVEN", "b": "FAIL"}, expect_detail={"b": "step 3"}),
                          FakeFvlint({"a": "PROVEN", "b": ("FAIL", "cex at step 3"), "c": "INFO"}, rc=1))
        self.assertEqual((o.ok, o.problems), (True, []))
        self.assertEqual(o.statuses, {"a": "PROVEN", "b": "FAIL", "c": "INFO"})

    def test_mismatches(self):
        o = self.run_with(case(expect={"a": "PROVEN", "gone": "PROVEN"}, expect_detail={"a": "lemma", "gone": "x"}),
                          FakeFvlint({"a": ("UNKNOWN", "induction failed"), "z": "VACUOUS", "e": "ERROR",
                                      "w": "WARN"}, rc=1))
        self.assertFalse(o.ok)
        self.assertEqual(o.problems, ["a: expected PROVEN, got UNKNOWN (induction failed)",
                                      "gone: expected PROVEN, got missing",
                                      "a: detail lacks 'lemma'", "gone: detail lacks 'x'",
                                      "z: unexpected VACUOUS", "e: unexpected ERROR"])

    def test_strict_and_exit_codes(self):
        o = self.run_with(case(strict=True), FakeFvlint({"a": "PROVEN"}))
        self.assertEqual(o.problems, ["a: unexpected check (PROVEN)"])
        o = self.run_with(case(expect={"a": "FAIL"}), FakeFvlint({"a": "FAIL"}, rc=0))
        self.assertEqual(o.problems, ["exit code 0, expected 1"])
        o = self.run_with(case(expect={"a": "UNKNOWN"}, exit=1), FakeFvlint({"a": "UNKNOWN"}, rc=1))
        self.assertTrue(o.ok)

    def test_budget(self):
        o = self.run_with(case(budget_s=10), FakeFvlint({}), times=[100.0, 125.0])
        self.assertEqual(o.problems, ["took 25.0s, budget 10s"])
        o = self.run_with(case(budget_s=10), FakeFvlint({}), scale=3, times=[100.0, 125.0])
        self.assertTrue(o.ok)
        o = self.run_with(case(budget_s=10), FakeFvlint({}), times=[100.0, 110.0])
        self.assertTrue(o.ok)                                           # exactly on budget
        o = self.run_with(case(budget_s=10), FakeFvlint(timeout=True), times=[5.0, 100.0])
        self.assertEqual((o.ok, o.problems, o.seconds), (False, ["killed after 95s (budget 10s)"], 95.0))

    def test_aborted_runs(self):
        o = self.run_with(case(), FakeFvlint(None, rc=2, stderr="fvlint: warning: x\nfvlint: Yosys not found\n"))
        self.assertEqual(o.problems, ["fvlint aborted (exit 2): fvlint: Yosys not found"])
        o = self.run_with(case(), FakeFvlint(None, rc=1, stderr=""))          # no results.json
        self.assertEqual(o.problems, ["fvlint aborted (exit 1): "])
        o = self.run_with(case(expect={"a": "PROVEN"}), FakeFvlint({"a": "PROVEN"}, rc=2, stderr="fvlint: late\n"))
        self.assertEqual(o.problems, ["fvlint aborted (exit 2): fvlint: late"])   # stale results ignored

    def test_expected_errors(self):
        c = case(expect_error="are not inputs")
        self.assertTrue(self.run_with(c, FakeFvlint(None, rc=2, stderr="ports x are not inputs of t")).ok)
        o = self.run_with(c, FakeFvlint({"a": "PROVEN"}, rc=0, stderr=""))
        self.assertEqual(o.problems, ["expected an abort (exit 2), got exit 0", "stderr lacks 'are not inputs'"])

    def test_pdr_without_abc_is_skipped(self):
        fake = FakeFvlint({})
        o = self.run_with(case(), fake, engine="pdr", abc=False)
        self.assertEqual((o.ok, o.skipped, fake.cmds), (True, True, []))
        self.assertIn("no yosys-abc", o.problems[0])
        o = self.run_with(case(), FakeFvlint({}), engine="auto", abc=False)
        self.assertEqual((o.ok, o.skipped), (True, False))


class Reports(TempDirCase):
    def outcomes(self):
        return [Outcome(case(name="a/ok"), "pdr", True, seconds=1.234, statuses={"k:t": "PROVEN", "k:a": "FAIL"}),
                Outcome(case(name="a/bad<x>"), "smtbmc", False, problems=["k: expected A, got B", "exit & code"]),
                Outcome(case(name="b/skip"), "pdr", True, skipped=True, problems=["skipped: no abc"])]

    def test_junit(self):
        p = os.path.join(self.tmp, "j.xml")
        write_junit(self.outcomes(), p)
        root = ET.parse(p).getroot()
        self.assertEqual((root.get("tests"), root.get("failures"), root.get("skipped")), ("3", "1", "1"))
        ok, bad, skip = list(root)
        self.assertEqual((ok.get("classname"), ok.get("name"), ok.get("time")), ("a", "a/ok [pdr]", "1.23"))
        self.assertEqual(list(ok), [])
        self.assertEqual(bad.find("failure").text, "k: expected A, got B\nexit & code")
        self.assertEqual(skip.find("skipped").get("message"), "skipped: no abc")

    def test_record(self):
        text = record(self.outcomes())
        self.assertEqual(text, '# a/ok [pdr] (1.2s)\nexpect = { "k:a" = "FAIL", "k:t" = "PROVEN" }\n\n'
                               '# a/bad<x> [smtbmc] (0.0s)\nexpect = {  }\n')


class Driver(TempDirCase):
    def setUp(self):
        super().setUp()
        self.manifest = self.write("m.toml", MANIFEST)
        self.chdir(self.tmp)

    def test_list(self):
        with captured() as (out, _):
            self.assertEqual(regress.main([self.manifest, "--list", "-k", "smoke"]), 0)
        self.assertEqual(out.getvalue().splitlines(), ["counters/a [pdr] tags=counter,smoke budget=30s",
                                                       "counters/a [smtbmc] tags=counter,smoke budget=30s"])
        with captured() as (out, _):
            regress.main([self.manifest, "--list", "--engines", "auto"])
        self.assertEqual(len(out.getvalue().splitlines()), 2)

    def test_default_manifest_is_fvlint_own(self):
        with captured() as (out, _):
            self.assertEqual(regress.main(["--list"]), 0)
        self.assertGreater(len(out.getvalue().splitlines()), 20)

    def test_missing_toolchain(self):
        def boom():
            raise regress_tools.ToolError("Yosys not found")
        from fvlint import tools as regress_tools
        with mock.patch.object(regress_tools.Toolchain, "discover", staticmethod(boom)), captured() as (_, err):
            self.assertEqual(regress.main([self.manifest]), 2)
        self.assertIn("Yosys not found", err.getvalue())

    def test_defaults(self):
        # -j: half the CPUs; -o: fvlint_regress; budget scale 1 unless the
        # environment sets one.
        from fvlint import tools as tools_mod
        workers, seen = [], []

        class Pool(regress.ThreadPoolExecutor):
            def __init__(self, max_workers):
                workers.append(max_workers)
                super().__init__(max_workers)

        def fake_run_case(c, engine, outroot, scale, abc):
            seen.append((outroot, scale))
            return Outcome(c, engine, True)
        env = {k: v for k, v in os.environ.items() if k != "FVLINT_BUDGET_SCALE"}
        for cpus, jobs in ((8, 4), (None, 1)):
            with self.subTest(cpus=cpus), mock.patch.dict(os.environ, env, clear=True), \
                    mock.patch.object(regress.os, "cpu_count", return_value=cpus), \
                    mock.patch.object(regress, "ThreadPoolExecutor", Pool), \
                    mock.patch.object(regress, "run_case", fake_run_case), \
                    mock.patch.object(tools_mod.Toolchain, "discover", staticmethod(lambda: mock.Mock(abc=None))), \
                    captured():
                self.assertEqual(regress.main([self.manifest]), 0)
            self.assertEqual(workers[-1], jobs)
        self.assertEqual(set(seen), {("fvlint_regress", 1.0)})

    def run_main(self, outcome_ok, *args, fuzz=None):
        from fvlint import fuzz as fuzz_mod
        from fvlint import tools as tools_mod
        seen = []

        def fake_run_case(c, engine, outroot, scale, abc):
            seen.append((c.name, engine, outroot, scale, abc))
            ok = outcome_ok(c, engine)
            return Outcome(c, engine, ok is not False, skipped=ok is None, statuses={"k:t": "PROVEN"},
                           problems=[] if ok else ["broken"])
        fake_tools = mock.Mock(abc=None)
        with mock.patch.object(regress, "run_case", fake_run_case), \
                mock.patch.object(tools_mod.Toolchain, "discover", staticmethod(lambda: fake_tools)), \
                mock.patch.object(fuzz_mod, "run", fuzz or (lambda seeds, out: self.fail("no fuzzing"))), \
                captured() as (out, _):
            rc = regress.main([self.manifest, "-o", "o", "-j", "2", *args])
        return rc, out.getvalue(), seen

    def test_all_pass(self):
        with mock.patch.dict(os.environ, {"FVLINT_BUDGET_SCALE": "1"}):
            _, _, seen = self.run_main(lambda c, e: True)
        self.assertEqual({s for *_, s, _ in seen}, {1.0})
        rc, out, seen = self.run_main(lambda c, e: None if e == "pdr" else True, "--junit", "j.xml", "--record",
                                      "--budget-scale", "2")
        self.assertEqual(rc, 0)
        self.assertEqual(sorted((n, e) for n, e, *_ in seen),
                         [("counters/a", "pdr"), ("counters/a", "smtbmc"), ("fsm/b", "auto")])
        self.assertTrue(all(o == "o" and s == 2.0 and a is False for _, _, o, s, a in seen))
        self.assertIn("3/3 case runs passed (1 skipped)", out)
        marks = {ln.split()[0] for ln in out.splitlines() if ln.split() and ln.split()[0] in ("SKIP", "PASS")}
        self.assertEqual(marks, {"SKIP", "PASS"})
        rows = [ln.replace("[", " ").replace("]", " ").split()[:3] for ln in out.splitlines()]
        self.assertIn(["SKIP", "counters/a", "pdr"], rows)
        self.assertIn('expect = { "k:t" = "PROVEN" }', out)
        with open(os.path.join("o", "summary.json")) as f:
            rows = json.load(f)
        self.assertEqual(len(rows), 3)
        self.assertEqual(set(rows[0]), {"case", "engine", "ok", "skipped", "seconds", "problems", "statuses"})
        self.assertTrue(os.path.exists("j.xml"))

    def test_engine_override(self):
        _, _, seen = self.run_main(lambda c, e: True, "--engines", "pdr,smtbmc")
        self.assertEqual(sorted((n, e) for n, e, *_ in seen), [("counters/a", "pdr"), ("counters/a", "smtbmc"),
                                                               ("fsm/b", "pdr"), ("fsm/b", "smtbmc")])

    def test_a_failure_fails_the_run(self):
        rc, out, _ = self.run_main(lambda c, e: e != "smtbmc")
        self.assertEqual(rc, 1)
        rows = [ln.replace("[", " ").replace("]", " ").split()[:3] for ln in out.splitlines()]
        self.assertIn(["FAIL", "counters/a", "smtbmc"], rows)
        self.assertIn("        broken", out)
        self.assertIn("2/3 case runs passed", out)

    def test_fuzzing(self):
        summary = {"seeds": 3, "checks": 10, "statuses": {"PROVEN": 10}, "inconclusive": [], "seconds": 1.0,
                   "problems": []}
        calls = []
        rc, out, _ = self.run_main(lambda c, e: True, "--fuzz", "3",
                                   fuzz=lambda seeds, outdir: calls.append((list(seeds), outdir)) or summary)
        self.assertEqual((rc, calls), (0, [([1, 2, 3], os.path.join("o", "fuzz"))]))
        self.assertIn("PASS  soundness fuzzer: 3 designs, 10 checks", out)
        summary["problems"] = ["seed 2: wrong"]
        rc, out, _ = self.run_main(lambda c, e: True, "--fuzz", "3", fuzz=lambda seeds, outdir: summary)
        self.assertEqual(rc, 1)
        self.assertIn("seed 2: wrong", out)


if __name__ == "__main__":
    unittest.main()
