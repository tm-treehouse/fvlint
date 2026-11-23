# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""fvlint.project: several configurations in one TOML file (--config)."""

from __future__ import annotations

import json
import os
import re
import sys
import unittest
from unittest import mock

from fvlint import cli
from fvlint.checks import FAIL, PROVEN
from fvlint.project import ConfigError, _out_root, _split, entry_argv, load

from .support import captured, snapshot
from .test_cli import CliCase


class EntryArgs(unittest.TestCase):
    def test_every_kind_of_key(self):
        entry = {"top": "t", "files": ["rtl/a.sv", "/abs/b.sv"], "filelists": "a.f", "filelists_rel": ["b.f"],
                 "include": ["inc"], "defines": {"SIM": 1, "W": "8"}, "params": ["N=4"], "libs": "prims.v",
                 "frontend": "slang", "reset": "rst_n:0", "no_reset": False, "reset_anytime": True,
                 "reset_cycles": 3, "uninit": "free", "assume": "a.sv", "waivers": "w.txt",
                 "recheck_waived": True, "engine": "pdr", "solver": "z3", "max_level": 2, "depth": 30,
                 "timeout": 60.5, "pdr_timeout": 10, "horizon": "2^48", "checks": ["mem_addr", "index_range"],
                 "fail_on": "unknown", "jobs": 4, "args": ["--no-cegar"]}
        b = os.path.join(os.sep, "proj")
        self.assertEqual(entry_argv(entry, b), [
            "--top", "t", "-f", os.path.join(b, "a.f"), "-F", os.path.join(b, "b.f"), "-I", os.path.join(b, "inc"),
            "-D", "SIM=1", "-D", "W=8", "-P", "N=4", "--lib", os.path.join(b, "prims.v"), "--frontend", "slang",
            "--reset", "rst_n:0", "--reset-anytime", "--reset-cycles", "3", "--uninit", "free",
            "--assume", os.path.join(b, "a.sv"), "--waivers", os.path.join(b, "w.txt"), "--recheck-waived",
            "--engine", "pdr", "--solver", "z3", "--max-level", "2", "--depth", "30", "--timeout", "60.5",
            "--pdr-timeout", "10", "--horizon", "2^48", "--checks", "mem_addr,index_range", "--fail-on", "unknown",
            "-j", "4", "--no-cegar", os.path.join(b, "rtl", "a.sv"), "/abs/b.sv"])
        self.assertEqual(entry_argv({"top": "t", "params": {"EN": True}}, b), ["--top", "t", "-P", "EN=1"])

    def test_every_option_maps_to_a_real_option(self):
        from fvlint.project import KEYS
        opts = {s for a in cli.build_parser()._actions for s in a.option_strings}
        self.assertEqual({o for o, _ in KEYS.values() if o} - opts, set())

    def test_messages(self):
        for entry, msg in (({"files": ["a.v"]}, "no top"),):
            with self.assertRaises(ConfigError) as cm:
                entry_argv(entry, "/p")
            self.assertEqual(str(cm.exception), msg)
        self.assertEqual(entry_argv({"top": "t", "args": "--no-cegar"}, "/p"), ["--top", "t", "--no-cegar"])

    def test_errors(self):
        for entry, msg in (({"top": "t", "tops": "x"}, "unknown key(s) tops"), ({"files": ["a.v"]}, "no top"),
                           ({"top": 3}, "top: expected a string"),
                           ({"top": "t", "jobs": "2"}, "jobs: expected a number"),
                           ({"top": "t", "jobs": True}, "jobs: expected a number"),
                           ({"top": "t", "no_reset": 1}, "no_reset: expected true or false"),
                           ({"top": "t", "files": [1]}, "files: expected a string or a list"),
                           ({"top": "t", "assume": ["a"]}, "assume: expected a path"),
                           ({"top": "t", "params": {"N": [1]}}, "params.N: expected a number or a string")):
            with self.subTest(msg=msg), self.assertRaisesRegex(ConfigError, re.escape(msg)):
                entry_argv(entry, "/p")


class CommandLine(unittest.TestCase):
    def test_names_and_options(self):
        self.assertEqual(_split(["--config", "f.toml", "a", "--fail-on", "unknown", "b", "-j", "2", "-j4", "-v",
                                 "--horizon=2^40", "--", "c"]),
                         ("f.toml", ["a", "b"], ["--fail-on", "unknown", "-j", "2", "-j4", "-v", "--horizon=2^40",
                                                 "c"]))
        self.assertEqual(_split(["--config=f.toml"]), ("f.toml", [], []))
        self.assertEqual(_split(["--config=a=b.toml"]), ("a=b.toml", [], []))
        self.assertEqual(_split(["--config"]), (None, [], []))
        # Flags take no value; `--opt=value` and `-j4` carry theirs; unknown options take none.
        for args, names in ((["-v", "x"], ["x"]), (["--horizon=2^40", "x"], ["x"]), (["-j4", "x"], ["x"]),
                            (["--nope", "x"], ["x"]), (["--github", "x"], ["x"]), (["-", "x"], ["-", "x"]),
                            (["--timeout", "5", "x"], ["x"]), (["-z", "x"], ["x"])):
            with self.subTest(args=args):
                self.assertEqual(_split(args)[1], names)

    def test_output_root(self):
        self.assertEqual(_out_root(["-v"], {}), ("fvlint_out", ["-v"]))
        self.assertEqual(_out_root(["-v"], {"out": "o"}), ("o", ["-v"]))
        self.assertEqual(_out_root(["--out=a=b"], {}), ("a=b", []))
        for args in (["-o", "r"], ["--out", "r"], ["--out=r"], ["-or"]):
            with self.subTest(args=args):
                self.assertEqual(_out_root(args + ["-v"], {"out": "o"}), ("r", ["-v"]))
        self.assertEqual(_out_root(["-o"], {"out": "o"}), ("o", []))           # no value: the file's
        with self.assertRaisesRegex(ConfigError, "out: expected a path"):
            _out_root([], {"out": 3})


class Projects(CliCase):
    def setUp(self):
        super().setUp()
        self.chdir(self.tmp)            # relative outputs (out = "...") stay in the test's directory

    def fake_elaborate(self, src, top, frontend, tools, out, assume):
        self.elab = dict(self.elab, main=snapshot(top), fsm=snapshot(top, "fsm"))
        return super().fake_elaborate(src, top, frontend, tools, out, assume)

    def project(self, text):
        return self.write("proj/fvlint.toml", text)

    def run_project(self, *args):
        with captured() as (out, err):
            rc = cli.main(["--config", *args])
        return rc, out.getvalue(), err.getvalue()

    TWO = ('out = "{out}"\n[defaults]\njobs = 3\n'
           '[config.counters]\ntop = "snap_counters"\nfiles = ["../rtl/top.sv"]\n'
           '[config.mux]\ntop = "snap_mux"\nfiles = ["../rtl/top.sv"]\njobs = 1\n')

    def test_runs_every_configuration(self):
        p = self.project(self.TWO.format(out=self.out))
        rc, out, err = self.run_project(p)
        self.assertEqual(rc, 0)
        self.assertEqual([c[1] for c in self.elab_calls], ["snap_counters", "snap_mux"])
        self.assertEqual([c[3] for c in self.elab_calls], [os.path.join(self.out, "counters"),
                                                           os.path.join(self.out, "mux")])
        self.assertEqual([c[0].files for c in self.elab_calls], [[self.rtl], [self.rtl]])   # relative to the file
        self.assertIn("=== fvlint: counters", err)
        self.assertTrue(os.path.exists(os.path.join(self.out, "mux", "results.json")))
        self.assertEqual(self.Engine.last.opts.jobs, 1)                  # the configuration wins over [defaults]

    def test_names_options_and_output_root(self):
        p = self.project(self.TWO.format(out="ignored"))
        root = os.path.join(self.tmp, "elsewhere")
        rc, _, _ = self.run_project(p, "mux", "-o", root, "-j", "5", "--fail-on", "unknown")
        self.assertEqual(rc, 0)
        self.assertEqual([c[1] for c in self.elab_calls], ["snap_mux"])
        self.assertEqual(self.elab_calls[0][3], os.path.join(root, "mux"))
        self.assertEqual(self.Engine.last.opts.jobs, 5)                  # the command line wins over the file

    def test_worst_exit_status(self):
        p = self.project(self.TWO.format(out=self.out))
        self.Engine.status = FAIL
        self.assertEqual(self.run_project(p)[0], 1)
        self.Engine.status = PROVEN
        p = self.project(self.TWO.format(out=self.out) + '[config.broken]\ntop = "t"\nfrontend = 7\n'
                         '[config.later]\ntop = "snap_counters"\nfiles = ["../rtl/top.sv"]\n')
        rc, _, err = self.run_project(p)
        self.assertEqual(rc, 2)
        self.assertIn("config.broken: frontend: expected a string", err)
        self.assertIn("=== fvlint: later", err)                          # the others still run
        p = self.project('[config.bad]\ntop = "t"\nfiles = ["x.v"]\nfrontend = "verilator"\n')
        self.assertEqual(self.run_project(p)[0], 2)                      # rejected by fvlint's own parser

    def test_defaults_apply(self):
        p = self.project('[defaults]\njobs = 3\n[config.c]\ntop = "snap_counters"\nfiles = ["../rtl/top.sv"]\n')
        self.assertEqual(self.run_project(p, "-o", self.out)[0], 0)
        self.assertEqual(self.Engine.last.opts.jobs, 3)

    def test_a_broken_configuration_is_not_run(self):
        p = self.project(self.TWO.format(out=self.out) + '[config.broken]\ntop = "t"\nfrontend = 7\n')
        self.assertEqual(self.run_project(p)[0], 2)
        self.assertEqual([c[1] for c in self.elab_calls], ["snap_counters", "snap_mux"])

    def test_exit_requests_of_a_run(self):
        # A run that exits (argparse errors, --version, --help) counts with its code; a non-number is 2.
        from fvlint import project
        p = self.project(self.TWO.format(out=self.out))
        for code, want in ((0, 0), (1, 1), ("boom", 2), (None, 2)):
            def run(argv, code=code, project=None):
                raise SystemExit(code)
            with self.subTest(code=code), mock.patch.object(cli, "main", run), captured():
                self.assertEqual(project.run_config(["--config", p]), want)

    def test_project_file_errors(self):
        for text, msg in (("[config", "not valid TOML"), ("x = 1\n[config.a]\ntop = 't'\n", "unknown top-level key"),
                          ("out = 'o'\n", "no configurations"), ("[config]\na = 1\n", "no configurations"),
                          ("defaults = 1\n[config.a]\ntop = 't'\n", "defaults: expected a table"),
                          ("out = 1\n[config.a]\ntop = 't'\n", "out: expected a path")):
            with self.subTest(msg=msg):
                rc, _, err = self.run_project(self.project(text))
                self.assertEqual(rc, 2)
                self.assertIn(msg, err)
        rc, _, err = self.run_project(os.path.join(self.tmp, "missing.toml"))
        self.assertEqual(rc, 2)
        rc, _, err = self.run_project(self.project(self.TWO.format(out=self.out)), "nope")
        self.assertEqual(rc, 2)
        self.assertIn("no configuration nope; there are: counters, mux", err)
        with captured() as (_, err):
            self.assertEqual(cli.main(["--config"]), 2)
        self.assertIn("--config needs a file", err.getvalue())

    def test_config_with_equals_and_the_real_command_line(self):
        p = self.project(self.TWO.format(out=self.out))
        rc, _, _ = self.run_project_raw([f"--config={p}", "mux"])
        self.assertEqual((rc, [c[1] for c in self.elab_calls]), (0, ["snap_mux"]))
        self.elab_calls.clear()
        with mock.patch.object(sys, "argv", ["fvlint", "--config", p, "counters"]), captured():
            self.assertEqual(cli.main(), 0)                              # arguments from sys.argv
        self.assertEqual([c[1] for c in self.elab_calls], ["snap_counters"])

    def run_project_raw(self, argv):
        with captured() as (out, err):
            rc = cli.main(argv)
        return rc, out.getvalue(), err.getvalue()

    def test_a_shared_waiver_file_is_judged_over_every_configuration(self):
        # waivers.txt: line 1 matches only in `counters`, line 2 only in
        # `mux`, line 3 nowhere.  own.txt is `own`'s alone, and its line 3 is
        # for a kind that configuration doesn't run.
        self.write("proj/waivers.txt", "counter_overflow:mod_q\nparallel_case:gnt\nmem_addr:gone.rd0\n")
        self.write("proj/own.txt", "index_range:lane\nindex_range:old\nmem_addr:x.rd0\n")
        md = os.path.join(self.tmp, "summary.md")
        p = self.project(f'out = "{self.out}"\n[defaults]\nwaivers = "waivers.txt"\n'
                         '[config.counters]\ntop = "snap_counters"\nfiles = ["../rtl/top.sv"]\n'
                         '[config.mux]\ntop = "snap_mux"\nfiles = ["../rtl/top.sv"]\n'
                         '[config.own]\ntop = "snap_mux"\nfiles = ["../rtl/top.sv"]\nwaivers = "own.txt"\n'
                         'checks = ["index_range"]\n')
        rc, out, err = self.run_project(p, "--github", "--summary-md", md)
        self.assertEqual(rc, 0)
        warnings = [ln for ln in err.splitlines() if "matches no check" in ln]
        self.assertEqual(warnings, [
            "fvlint: warning: proj/waivers.txt:3: waiver 'mem_addr:gone.rd0' matches no check in any configuration "
            "(renamed, fixed or no longer present?)",
            "fvlint: warning: proj/own.txt:2: waiver 'index_range:old' matches no check in any configuration "
            "(renamed, fixed or no longer present?)"])
        notes = [ln for ln in out.splitlines() if "unused waiver" in ln]
        self.assertEqual(notes, ["::warning title=fvlint%3A unused waiver,file=proj/waivers.txt,line=3::"
                                 "mem_addr:gone.rd0 matches no check (renamed, fixed or no longer present?)",
                                 "::warning title=fvlint%3A unused waiver,file=proj/own.txt,line=2::"
                                 "index_range:old matches no check (renamed, fixed or no longer present?)"])
        with open(md) as f:
            text = f.read()
        self.assertEqual(text.count("that match no check"), 2)                  # only the project's section
        self.assertTrue(text.endswith("### fvlint: waivers\n\n"
                                      "Waivers in `proj/waivers.txt` that match no check in any configuration:\n\n"
                                      "- line 3: `mem_addr:gone.rd0`\n\n"
                                      "Waivers in `proj/own.txt` that match no check in any configuration:\n\n"
                                      "- line 2: `index_range:old`\n\n"), text)
        # Each run still records its own view in results.json.
        for name, lines in (("counters", [2, 3]), ("mux", [1, 3]), ("own", [2])):
            with open(os.path.join(self.out, name, "results.json")) as f:
                self.assertEqual([w["line"] for w in json.load(f)["meta"]["unused_waivers"]], lines, name)

    def test_no_unused_waivers_no_report(self):
        self.write("proj/waivers.txt", "counter_overflow:mod_q\n")
        p = self.project(f'out = "{self.out}"\n[config.c]\ntop = "snap_counters"\nfiles = ["../rtl/top.sv"]\n'
                         'waivers = "waivers.txt"\n[config.n]\ntop = "snap_mux"\nfiles = ["../rtl/top.sv"]\n')
        rc, out, err = self.run_project(p, "--github")
        self.assertEqual(rc, 0)
        self.assertNotIn("matches no check", err + out)

    def test_load(self):
        p = self.project(self.TWO.format(out="o"))
        self.assertEqual(sorted(load(p)["config"]), ["counters", "mux"])


if __name__ == "__main__":
    unittest.main()
