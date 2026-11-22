# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""fvlint.cli: argument handling, the flow from netlist to report, exit codes.

The toolchain, elaboration and proof engine are faked at the module boundary;
detection, reset discovery, waivers and reporting run for real on the
committed Yosys snapshots."""

from __future__ import annotations

import json
import os
import unittest
import xml.etree.ElementTree as ET
from unittest import mock

from fvlint import __version__, cli
from fvlint.checks import FAIL, PROVEN, UNKNOWN, VACUOUS, Result
from fvlint.tools import ToolError

from .support import NB, TempDirCase, captured, snapshot


class FakeTools:
    def __init__(self, abc=True, warning=None):
        self.abc = "/x/yosys-abc" if abc else None
        self.solver, self.version, self.warning = "z3", (0, 71), warning

    def version_warning(self):
        return self.warning

    def describe(self):
        return "fake toolchain"


class FakeEngine:
    """Records how the CLI drives the engine; every check gets `status`."""
    last = None

    def __init__(self, nl, tools, out, lemmas, resets, opts, assume_ports, assume_file):
        type(self).last = self
        self.nl, self.out, self.lemmas, self.resets, self.opts = nl, out, lemmas, resets, opts
        self.assume_ports, self.assume_file = assume_ports, assume_file
        self.stats = {"jobs": 7, "batches": 2, "replays": 1}
        self.proved = None
        if opts.engine == "auto":
            opts.engine = "pdr"

    env_error = None
    status = PROVEN
    boom = None

    def environment_ok(self):
        return self.env_error

    def prove_all(self, checks):
        self.proved = list(checks)
        if self.boom:
            raise self.boom
        st = self.status
        return [Result(check=c, status=st(c) if callable(st) else st, detail="fake") for c in checks]


class CliCase(TempDirCase):
    top = "snap_counters"

    def setUp(self):
        super().setUp()
        self.rtl = self.write("rtl/top.sv", "// stand-in source\n")
        self.out = os.path.join(self.tmp, "out")
        self.tools = FakeTools()
        self.elab = {"main": snapshot(self.top), "fsm": snapshot(self.top, "fsm"), "fsm_warning": None,
                     "src_base": None, "src_map": None, "assume_ports": None, "assume_file": None}
        self.elab_calls = []
        self.Engine = type("Engine", (FakeEngine,), {"last": None})     # fresh class state per test
        for p in (mock.patch.object(cli.Toolchain, "discover", staticmethod(lambda solver=None: self.tools)),
                  mock.patch.object(cli, "elaborate", self.fake_elaborate),
                  mock.patch.object(cli, "Engine", self.Engine)):
            p.start()
            self.addCleanup(p.stop)

    def fake_elaborate(self, src, top, frontend, tools, out, assume):
        self.elab_calls.append((src, top, frontend, out, assume))
        if isinstance(self.elab, Exception):
            raise self.elab
        return self.elab

    def run_cli(self, *args, top=None):
        argv = ["--top", top or self.top, self.rtl, "-o", self.out, *args]
        with captured() as (out, err):
            rc = cli.main(argv)
        return rc, out.getvalue(), err.getvalue()

    def results(self):
        with open(os.path.join(self.out, "results.json")) as f:
            return json.load(f)


class Arguments(CliCase):
    def test_version(self):
        with captured() as (out, _), self.assertRaises(SystemExit) as cm:
            cli.main(["--version"])
        self.assertEqual((cm.exception.code, out.getvalue().strip()), (0, f"fvlint {__version__}"))

    def test_version_matches_the_package_metadata(self):
        import tomllib
        path = os.path.join(os.path.dirname(__file__), "..", "..", "pyproject.toml")
        with open(path, "rb") as f:
            self.assertEqual(__version__, tomllib.load(f)["project"]["version"])

    def test_top_is_required(self):
        with captured(), self.assertRaises(SystemExit) as cm:
            cli.main([self.rtl])
        self.assertEqual(cm.exception.code, 2)

    def test_no_sources(self):
        with captured() as (_, err):
            self.assertEqual(cli.main(["--top", "t"]), 2)
        self.assertIn("no source files", err.getvalue())

    def test_sources_and_filelists_reach_elaboration(self):
        fl = self.write("lists/l.f", "b.sv\n+incdir+inc\n")
        fl2 = self.write("lists/m.f", "c.sv\n")
        assume = self.write("a.sv", "")
        self.chdir(self.tmp)
        self.run_cli("-F", fl, "-f", fl2, "-I", "i1", "-D", "X=1", "-P", "W=4", "--lib", "prims.v",
                     "--frontend", "slang", "--assume", assume)
        src, top, frontend, out, a = self.elab_calls[0]
        self.assertEqual(src.files, [self.rtl, os.path.join(self.tmp, "lists", "b.sv"),   # -F: list-relative
                                     os.path.join(self.tmp, "c.sv")])                      # -f: cwd-relative
        self.assertEqual(src.incdirs, ["i1", os.path.join(self.tmp, "lists", "inc")])
        self.assertEqual((src.defines, src.params, src.libs), (["X=1"], ["W=4"], ["prims.v"]))
        self.assertEqual((top, frontend, out, a), (self.top, "slang", self.out, assume))
        self.assertTrue(os.path.isdir(self.out))

    def test_options_reach_the_engine(self):
        self.run_cli("--engine", "smtbmc", "--max-level", "5", "--no-full", "--no-cegar", "--no-vacuity",
                     "--depth", "9",
                     "--max-bmc-depth", "99", "--timeout", "12", "--pdr-timeout", "3", "--batch-cells", "10",
                     "--batch-props", "2", "-j", "3", "--uninit", "free")
        o = self.Engine.last.opts
        self.assertEqual((o.engine, o.max_level, o.try_full, o.cegar, o.vacuity, o.depth, o.max_bmc_depth),
                         ("smtbmc", 5, False, False, False, 9, 99))
        self.assertEqual((o.timeout, o.pdr_timeout, o.batch_cells, o.batch_props, o.jobs, o.uninit),
                         (12, 3, 10, 2, 3, "free"))
    def test_defaults_match_the_engine_defaults(self):
        from dataclasses import fields
        self.run_cli()
        got, want = self.Engine.last.opts, cli.Options()
        for f in fields(want):
            if f.name not in ("engine", "jobs"):                         # engine: resolved; jobs: per machine
                with self.subTest(option=f.name):
                    self.assertEqual(getattr(got, f.name), getattr(want, f.name))
        self.assertEqual(got.jobs, max(1, (os.cpu_count() or 2) // 2))
        self.assertGreaterEqual(got.jobs, 1)


class ToolProblems(CliCase):
    def test_missing_toolchain(self):
        def boom(solver=None):
            raise ToolError("Yosys not found")
        with mock.patch.object(cli.Toolchain, "discover", staticmethod(boom)):
            rc, _, err = self.run_cli()
        self.assertEqual(rc, 2)
        self.assertIn("fvlint: Yosys not found", err)

    def test_pdr_needs_abc(self):
        self.tools.abc = None
        rc, _, err = self.run_cli("--engine", "pdr")
        self.assertEqual(rc, 2)
        self.assertIn("--engine pdr needs yosys-abc", err)

    def test_auto_engine_without_abc(self):
        self.tools.abc = None
        self.assertEqual(self.run_cli()[0], 0)

    def test_version_warning(self):
        self.tools.warning = "Yosys 0.99 has not been tested"
        rc, _, err = self.run_cli()
        self.assertEqual(rc, 0)
        self.assertIn("fvlint: warning: Yosys 0.99 has not been tested", err)

    def test_elaboration_error(self):
        self.elab = ToolError("elaboration failed:\nsyntax error")
        rc, _, err = self.run_cli()
        self.assertEqual(rc, 2)
        self.assertIn("syntax error", err)
        self.assertFalse(os.path.exists(os.path.join(self.out, "results.json")))

    def test_unknown_cells_and_fsm_warnings(self):
        b = NB()
        b.input("clk")
        b.cell("u", "$frobnicate", {})
        b.cell("v", "$zap", {})
        p = self.write_json("frob.json", b.data("frob"))
        self.elab.update(main=p, fsm=None, fsm_warning="FSM extraction failed in Yosys")
        rc, _, err = self.run_cli(top="frob")
        self.assertEqual(rc, 0)
        self.assertIn("cell types not modelled by fvlint are cut (treated as free): $frobnicate, $zap", err)
        self.assertIn("warning: FSM extraction failed in Yosys", err)


class Environment(CliCase):
    def test_assumption_ports_must_be_top_inputs(self):
        for ports in ({"nope": "input"}, {"en": "output"}, {"o": "input"}):
            with self.subTest(ports=ports):
                self.elab["assume_ports"] = ports
                rc, _, err = self.run_cli()
                self.assertEqual(rc, 2)
                self.assertIn(f"fvlint_assumptions ports {next(iter(ports))} are not inputs of snap_counters", err)
        self.elab["assume_ports"] = {"en": "input", "din": "input"}
        self.assertEqual(self.run_cli()[0], 0)
        self.assertEqual(self.Engine.last.assume_ports, {"en": "input", "din": "input"})

    def test_reset_options(self):
        rc, _, err = self.run_cli("--reset", "nope")
        self.assertEqual(rc, 2)
        self.assertIn("--reset port 'nope' is not an input", err)
        rc, _, err = self.run_cli("--reset", "rst:0", "--reset-cycles", "4", "--reset-anytime")
        r = self.Engine.last.resets
        self.assertEqual((r.primary.name, r.primary.active, r.cycles, r.anytime), ("rst", 0, 4, True))
        self.assertIn("reset: rst (active 0, held 4 cycle(s))", err)
        rc, _, err = self.run_cli("--no-reset")
        self.assertIn("reset: none;", err)
        self.assertIsNone(self.Engine.last.resets.primary)
        self.assertEqual(self.results()["meta"]["reset"], None)

    def test_unsatisfiable_environment(self):
        self.Engine.env_error = "the environment is unsatisfiable"
        rc, out, _ = self.run_cli()
        self.assertEqual(rc, 1)
        self.assertIsNone(self.Engine.last.proved)
        statuses = {r["id"]: r["status"] for r in self.results()["results"]}
        self.assertEqual(statuses.pop("counter_overflow:free_q"), "INFO")    # preset, needs no proof
        self.assertEqual(set(statuses.values()), {"ERROR"})
        self.assertEqual(len(statuses), 6)


class Flow(CliCase):
    def test_list(self):
        rc, out, err = self.run_cli("--list")
        self.assertEqual(rc, 0)
        ids = [ln.split()[0] for ln in out.splitlines()]
        self.assertIn("counter_overflow:mod_q", ids)
        self.assertEqual(len(ids), 7)
        self.assertIsNone(self.Engine.last)                              # no engine for --list
        self.assertFalse(os.path.exists(os.path.join(self.out, "results.json")))
        self.assertIn("top snap_counters, 41 cells, 7 checks", err)

    def test_presets_waivers_and_proofs(self):
        w = self.write("w.txt", "counter_overflow:mod_q   # reviewed\n")
        rc, out, _ = self.run_cli("--waivers", w, "-v")
        self.assertEqual(rc, 0)
        res = {r["id"]: r for r in self.results()["results"]}
        self.assertEqual(res["counter_overflow:mod_q"]["status"], "WAIVED")
        self.assertEqual(res["counter_overflow:mod_q"]["waiver"], "waiver file: counter_overflow:mod_q (reviewed)")
        self.assertEqual(res["counter_overflow:free_q"]["status"], "INFO")       # preset: never proved
        self.assertIn("free-running", res["counter_overflow:free_q"]["detail"])
        proved = sorted(c.id for c in self.Engine.last.proved)
        self.assertEqual(len(proved), 5)
        self.assertNotIn("counter_overflow:mod_q", proved)
        self.assertNotIn("counter_overflow:free_q", proved)
        self.assertIn("counter_overflow:mod_q", out)                    # -v shows waived checks

    def test_check_selection(self):
        self.run_cli("--checks", "counter_underflow, ")
        self.assertEqual(sorted(c.id for c in self.Engine.last.proved),
                         ["counter_underflow:acc", "counter_underflow:down_q"])

    def test_unknown_check_kinds_are_an_error(self):
        # A typo used to select nothing and report a clean run.
        rc, _, err = self.run_cli("--checks", "counter_overfow,index_range")
        self.assertEqual(rc, 2)
        self.assertIn("unknown check kind(s) counter_overfow", err)
        self.assertIsNone(self.Engine.last)

    # Spelled out here, not read back from cli.KINDS: a misspelt entry there
    # would make that kind unselectable while a loop over KINDS still passes.
    ALL_KINDS = ["counter_overflow", "counter_underflow", "parallel_case", "full_case", "index_range", "mem_addr",
                 "fsm_unreachable", "fsm_trap", "fsm_reset", "fsm_summary"]

    def test_every_check_kind_is_accepted(self):
        self.assertEqual(cli.KINDS, self.ALL_KINDS)
        for kind in self.ALL_KINDS:
            with self.subTest(kind=kind):
                self.assertNotEqual(self.run_cli("--checks", kind)[0], 2)
        self.assertNotEqual(self.run_cli("--checks", ",".join(self.ALL_KINDS))[0], 2)   # all of them at once

    def test_every_option_choice_is_accepted(self):
        p = cli.build_parser()
        expected = {"--frontend": ["yosys", "slang"], "--uninit": ["zero", "free"],
                    "--engine": ["auto", "pdr", "smtbmc"], "--fail-on": ["fail", "vacuous", "unknown"]}
        self.assertEqual({a.option_strings[-1]: a.choices for a in p._actions if a.choices}, expected)
        for option, choices in expected.items():
            for choice in choices:
                with self.subTest(option=option, choice=choice):
                    dest = option[2:].replace("-", "_")
                    self.assertEqual(getattr(p.parse_args(["--top", "t", option, choice]), dest), choice)
        args = p.parse_args(["--top", "t"])
        self.assertEqual((args.frontend, args.uninit, args.engine, args.fail_on, args.out),
                         ("yosys", "zero", "auto", "vacuous", "fvlint_out"))

    def test_default_jobs_is_half_the_cpus(self):
        for cpus, jobs in ((8, 4), (3, 1), (None, 1)):
            with self.subTest(cpus=cpus), mock.patch.object(cli.os, "cpu_count", return_value=cpus):
                self.assertEqual(cli.build_parser().parse_args(["--top", "t"]).jobs, jobs)

    def test_lemmas_include_fsm_lemmas(self):
        self.top = "snap_fsm"
        self.elab.update(main=snapshot("snap_fsm"), fsm=snapshot("snap_fsm", "fsm"))
        rc, _, _ = self.run_cli()
        self.assertEqual(rc, 1)                                         # preset FAIL: unreachable state
        lemmas = self.Engine.last.lemmas
        self.assertEqual([lm.checker for lms in lemmas.values() for lm in lms], ["fvl_member"])
        statuses = {r["id"]: r["status"] for r in self.results()["results"]}
        self.assertEqual(statuses["fsm_unreachable:st=2'b11"], "FAIL")
        self.assertIsNone(self.Engine.last.proved)                     # FSM checks need no proof

    def test_internal_error_keeps_the_report(self):
        self.Engine.boom = RuntimeError("kaput")
        rc, _, _ = self.run_cli()
        self.assertEqual(rc, 1)
        errs = [r for r in self.results()["results"] if r["status"] == "ERROR"]
        self.assertEqual(len(errs), 6)
        self.assertTrue(all("internal error: RuntimeError('kaput')" == r["detail"] for r in errs))

    def test_outputs_and_meta(self):
        rc, out, err = self.run_cli()
        d = self.results()
        self.assertEqual(d["meta"]["top"], "snap_counters")
        self.assertEqual((d["meta"]["engine"], d["meta"]["solver"], d["meta"]["yosys"]), ("pdr", "z3", "0.71"))
        self.assertEqual((d["meta"]["reset"], d["meta"]["reset_cycles"], d["meta"]["derived_resets"]), ("rst", 1, []))
        self.assertEqual((d["meta"]["jobs"], d["meta"]["batches"], d["meta"]["replays"]), (7, 2, 1))
        self.assertTrue(0 <= d["meta"]["elapsed_s"] < 60)
        self.assertEqual((d["meta"]["version"], d["meta"]["uninit"], d["meta"]["max_level"]), (__version__, "zero", 3))
        self.assertEqual(ET.parse(os.path.join(self.out, "junit.xml")).getroot().get("tests"), "7")
        self.assertTrue(out.startswith("fvlint: 7 checks: 1 info, 6 proven"))
        self.assertIn("7 solver jobs, engine pdr", err)
        j, x = os.path.join(self.tmp, "r.json"), os.path.join(self.tmp, "r.xml")
        self.run_cli("--json", j, "--junit", x)
        self.assertTrue(os.path.exists(j) and os.path.exists(x))

    def test_exit_codes(self):
        cases = [(PROVEN, None, 0), (UNKNOWN, None, 0), (UNKNOWN, "unknown", 1), (VACUOUS, None, 1),
                 (VACUOUS, "fail", 0), (VACUOUS, "unknown", 1), (FAIL, "fail", 1)]
        for status, fail_on, want in cases:
            with self.subTest(status=status, fail_on=fail_on):
                self.Engine.status = status
                rc, _, _ = self.run_cli(*(["--fail-on", fail_on] if fail_on else []))
                self.assertEqual(rc, want)

    def test_one_failure_is_enough(self):
        self.Engine.status = staticmethod(lambda c: FAIL if c.target == "acc" else PROVEN)
        self.assertEqual(self.run_cli("--fail-on", "fail")[0], 1)


if __name__ == "__main__":
    unittest.main()
