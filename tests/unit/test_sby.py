# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""fvlint.sby (job files, log parsing) and fvlint.replay (traces, stimulus).

Log lines are copied from real SymbiYosys runs (YoWASP 0.71 build)."""

from __future__ import annotations

import json
import os
import re
import shutil
import unittest

from fvlint.replay import _norm, divergent, read_vcd, read_yw, stim_module
from fvlint.sby import (CHECKERS_V, JobResult, Prop, PropResult, _complete_summary, instance, parse_job, prop_key,
                        write_job, yw_for)

from .support import DATA, TempDirCase

W = "_witness_.check_flatten_"
SMTBMC = "smtbmc --keep-going z3"
PDR = "abc --keep-going pdr"


def line(text):
    return f"SBY 13:16:43 [run] {text}\n"


def eng(text, phase=None):
    """An smtbmc engine line (with its elapsed-time column)."""
    return line(f"engine_0{'.' + phase if phase else ''}: ##   0:00:00  {text}")


def assert_failed(prop, phase=None, loc="fvl_checkers.v:44.77-44.88"):
    return eng(f"Assert failed in top: {loc} ({W}{prop})", phase)


def failed_summary(prop, step, loc="fvl_checkers.v:75.77-75.88"):
    return line(f"summary:   failed assertion top.{W}{prop} at {loc} step {step}")


class Instances(unittest.TestCase):
    def test_range_checker(self):
        inst = instance(Prop("fvl_t0", "fvl_range", {"W": 4, "LO": 1, "HI": 9, "SIGNED": 0},
                             {"v": [5, 6, 7, 8]}, [(10, 0), (11, 1), ("1", 1)], mode=2))
        p = inst["parameters"]
        self.assertEqual(p, {"NC": 2, "POL": "10", "MODE": 2, "W": 4, "LO": "0001", "HI": "1001", "SIGNED": 0,
                             "NE": 1})
        self.assertEqual(inst["connections"], {"c": [10, 11], "v": [5, 6, 7, 8], "e": ["1"]})
        self.assertEqual(inst["port_directions"], {"c": "input", "v": "input", "e": "input"})
        self.assertEqual((inst["type"], inst["hide_name"]), ("fvl_range", 0))

    def test_signed_bounds_are_twos_complement(self):
        p = instance(Prop("t", "fvl_range", {"W": 8, "LO": -128, "HI": -1, "SIGNED": 1}, {"v": list(range(8))},
                          []))["parameters"]
        self.assertEqual((p["LO"], p["HI"]), ("10000000", "11111111"))

    def test_no_conditions_means_always(self):
        inst = instance(Prop("t", "fvl_onehot0", {"W": 3}, {"s": [1, 2, 3]}, [("1", 1), ("0", 0)]))
        self.assertEqual((inst["parameters"]["NC"], inst["parameters"]["POL"]), (1, "1"))
        self.assertEqual(inst["connections"]["c"], ["1"])
        self.assertNotIn("e", inst["connections"])                      # only fvl_range has an enable vector

    def test_explicit_enable_vector(self):
        inst = instance(Prop("t", "fvl_range", {"W": 2, "LO": 0, "HI": 2, "SIGNED": 0},
                             {"v": [1, 2], "e": [3, 4, 5]}, []))
        self.assertEqual((inst["connections"]["e"], inst["parameters"]["NE"]), ([3, 4, 5], 3))

    def test_member_set_packing(self):
        p = instance(Prop("t", "fvl_member", {"W": 2, "N": 3, "SET": 0b100100}, {"v": [1, 2]}, []))["parameters"]
        self.assertEqual(p["SET"], "100100")                            # N*W bits, MSB first

    def test_polarity_bit_order(self):
        conds = [(10 + i, v) for i, v in enumerate([1, 0, 0, 1, 1])]
        p = instance(Prop("t", "fvl_nonzero", {"W": 1}, {"s": [1]}, conds))["parameters"]
        self.assertEqual(p["POL"], "11001")                            # bit i = polarity of cond i

    def test_checker_library_matches_instances(self):
        # Every parameter instance() emits exists in the checker module.
        mods = dict(re.findall(r"module (\w+) #\((.*?)\) \(", CHECKERS_V, re.S))
        examples = [Prop("t", "fvl_range", {"W": 2, "LO": 0, "HI": 1, "SIGNED": 0}, {"v": [1, 2]}, []),
                    Prop("t", "fvl_rel", {"W": 2, "SIGNED": 0}, {"a": [1, 2], "b": [3, 4]}, []),
                    Prop("t", "fvl_onehot0", {"W": 2}, {"s": [1, 2]}, []),
                    Prop("t", "fvl_nonzero", {"W": 2}, {"s": [1, 2]}, []),
                    Prop("t", "fvl_member", {"W": 2, "N": 1, "SET": 1}, {"v": [1, 2]}, [])]
        for p in examples:
            with self.subTest(checker=p.checker):
                declared = set(re.findall(r"parameter (?:\[[^\]]*\] |integer )?(\w+)", mods[p.checker]))
                inst = instance(p)
                self.assertLessEqual(set(inst["parameters"]), declared)
                ports = re.search(rf"module {p.checker} #\(.*?\) \((.*?)\);", CHECKERS_V, re.S).group(1)
                self.assertEqual(set(re.findall(r"input (?:\[[^\]]*\]\s*)?(\w+)", ports)), set(inst["connections"]))


class JobFiles(TempDirCase):
    def job(self, **kw):
        args = dict(d=os.path.join(self.tmp, "j"), top="top",
                    module={"attributes": {}, "ports": {}, "cells": {"c": {"type": "$not"}}, "netnames": {}},
                    props=[Prop("fvl_t0", "fvl_nonzero", {"W": 1}, {"s": [2]}, [])], mode="prove", depth=20,
                    engine=SMTBMC, multiclock=False, timeout=60.7, creator="me")
        args.update(kw)
        sby = write_job(**args)
        with open(sby) as f:
            return args["d"], f.read()

    def test_layout_and_options(self):
        d, text = self.job()
        self.assertEqual(sorted(os.listdir(d)), ["cone.json", "fvl_checkers.v", "run.sby"])
        self.assertIn("[options]\nmode prove\ndepth 20\ntimeout 60\n", text)
        self.assertIn("[engines]\nsmtbmc --keep-going z3\n", text)
        self.assertIn("read_json cone.json\nread_verilog -formal -sv fvl_checkers.v\n", text)
        self.assertIn("hierarchy -top top\nflatten\nprep -top top\n", text)
        self.assertTrue(text.endswith("[files]\ncone.json\nfvl_checkers.v\n"))
        with open(os.path.join(d, "cone.json")) as f:
            cone = json.load(f)
        self.assertEqual(cone["creator"], "me")
        self.assertEqual(set(cone["modules"]["top"]["cells"]), {"c", "fvl_t0"})
        with open(os.path.join(d, "fvl_checkers.v")) as f:
            self.assertEqual(f.read(), CHECKERS_V)

    def test_pdr_prove_has_no_depth(self):
        _, text = self.job(engine=PDR, aigsmt="z3")
        self.assertNotIn("depth", text)
        self.assertIn("aigsmt z3\n", text)
        _, text = self.job(engine=PDR, mode="bmc")
        self.assertIn("depth 20", text)

    def test_multiclock_no_timeout_and_extra_files(self):
        d, text = self.job(multiclock=True, timeout=None, extra_files={"fvl_stim.sv": "module fvl_stim; endmodule\n"})
        self.assertIn("multiclock on", text.splitlines())
        self.assertNotIn("timeout", text)
        self.assertIn("read_verilog -formal -sv fvl_stim.sv", text)
        self.assertIn("fvl_stim.sv\n", text.split("[files]")[1])
        self.assertTrue(os.path.exists(os.path.join(d, "fvl_stim.sv")))

    def test_module_argument_is_not_modified(self):
        module = {"attributes": {}, "ports": {}, "cells": {}, "netnames": {}}
        self.job(module=module)
        self.assertEqual(module["cells"], {})

    def test_rerun_into_existing_directory(self):
        self.job()
        d, _ = self.job(depth=7)
        with open(os.path.join(d, "run.sby")) as f:
            self.assertIn("depth 7", f.read())


class LogParsing(TempDirCase):
    def run_dir(self, log, ywa=None):
        d = os.path.join(self.tmp, "jobs", "00001_x")
        os.makedirs(os.path.join(d, "run", "model"), exist_ok=True)
        with open(os.path.join(d, "run", "logfile.txt"), "w") as f:
            f.write(log)
        if ywa is not None:
            with open(os.path.join(d, "run", "model", "design_aiger.ywa"), "w") as f:
                json.dump({"asserts": [["\\_witness_", f"\\check_flatten_{n}__fvl_checkers_v_75_assert_74"]
                                       for n in ywa]}, f)
        return d

    def parse(self, log, engine=SMTBMC, mode="prove", names=("fvl_t0", "fvl_t1"), rc=0, ywa=None):
        d = self.run_dir(log, ywa)
        return d, parse_job(d, self.tmp, rc, engine, mode, list(names))

    def test_prop_key(self):
        self.assertEqual(prop_key(W + "fvl_t12__fvl_checkers_v_25_assert_52"), "fvl_t12")
        self.assertEqual(prop_key("x.fvl_l3_g_assert.y"), "fvl_l3")
        self.assertEqual(prop_key(W + "fvl_s0__fvl_stim_sv_16_cover_72"), "fvl_s0")
        self.assertEqual(prop_key(W + "fvl_v7__x"), "fvl_v7")
        self.assertIsNone(prop_key("user_assert"))
        self.assertIsNone(prop_key("fvl_x1_"))
        self.assertIsNone(prop_key(None))

    def test_missing_log(self):
        d = os.path.join(self.tmp, "nolog")
        r = parse_job(d, self.tmp, 1, SMTBMC, "prove", ["fvl_t0"])
        self.assertEqual((r.status, r.props, r.error, r.dir), ("ERROR", {}, None, d))
        self.assertEqual(parse_job(d, self.tmp, -1, SMTBMC, "prove", []).status, "TIMEOUT")

    def test_kinduction_pass(self):
        _, r = self.parse(line("engine_0.basecase: ##   0:00:00  Checking assertions in step 19..") +
                          line("summary: engine_0 (smtbmc --keep-going z3) returned pass for induction") +
                          line("DONE (PASS, rc=0)"))
        self.assertEqual(r.status, "PASS")
        self.assertEqual({k: v.status for k, v in r.props.items()}, {"fvl_t0": "pass", "fvl_t1": "pass"})

    def test_pass_in_bmc_or_cover_mode_proves_nothing(self):
        for mode in ("bmc", "cover"):
            with self.subTest(mode=mode):
                _, r = self.parse(line("DONE (PASS, rc=0)"), mode=mode)
                self.assertEqual((r.status, r.props), ("PASS", {}))
                self.assertEqual(r.get("fvl_t0"), PropResult("unknown"))

    def test_basecase_and_induction_failures(self):
        log = (line("engine_0.basecase: ##   0:00:00  Checking assertions in step 0..") +
               line("engine_0.basecase: ##   0:00:00  Checking assertions in step 3..") +
               assert_failed("fvl_l1__fvl_checkers_v_44_assert_94", "basecase") +
               line("engine_0.basecase: ##   0:00:00  Writing trace to VCD file: engine_0/trace0.vcd") +
               line("engine_0.basecase: ##   0:00:00  Writing trace to Yosys witness file: engine_0/trace0.yw") +
               line("engine_0.basecase: ##   0:00:00  Checking assertions in step 4..") +
               assert_failed("fvl_l0__fvl_checkers_v_44_assert_84", "induction") +
               assert_failed("fvl_l1__fvl_checkers_v_44_assert_94", "induction") +
               assert_failed("fvl_t0__fvl_checkers_v_44_assert_74", "induction") +
               line("engine_0.induction: ##   0:00:00  Writing trace to VCD file: engine_0/trace_induct.vcd") +
               assert_failed("fvl_t1__fvl_checkers_v_44_assert_95", "basecase") +
               line("engine_0.basecase: ##   0:00:00  Writing trace to VCD file: engine_0/trace1.vcd") +
               line("DONE (FAIL, rc=2)"))
        d, r = self.parse(log, rc=2)
        self.assertEqual(r.status, "FAIL")
        jobrel = os.path.relpath(os.path.join(d, "run"), self.tmp)
        trace = lambda n: os.path.join(jobrel, "engine_0", n)   # noqa: E731
        self.assertEqual(r.props["fvl_l1"], PropResult("fail", trace("trace0.vcd"), 3, "basecase"))
        self.assertEqual(r.props["fvl_l0"], PropResult("unknown", phase="induction"))      # no trace taken
        self.assertEqual(r.props["fvl_t0"], PropResult("unknown", phase="induction"))
        self.assertEqual(r.props["fvl_t1"], PropResult("fail", trace("trace1.vcd"), 4, "basecase"))

    def test_interleaved_basecase_and_induction_traces(self):
        # The two k-induction threads log concurrently.
        log = (line("engine_0.basecase: ##   0:00:00  Checking assertions in step 2..") +
               line(f"engine_0.basecase: ##   0:00:00  Assert failed in top: x.v:1.1-1.2 ({W}fvl_t0__x)") +
               line("engine_0.induction: ##   0:00:00  Writing trace to VCD file: engine_0/trace_induct.vcd") +
               line("engine_0.basecase: ##   0:00:00  Writing trace to VCD file: engine_0/trace0.vcd") +
               line("DONE (FAIL, rc=2)"))
        _, r = self.parse(log, rc=2)
        self.assertTrue(r.props["fvl_t0"].trace.endswith(os.path.join("engine_0", "trace0.vcd")))

    def test_induction_failure_logged_before_the_basecase_failure(self):
        # From a real run (index/idx_signed_bug, smtbmc): the induction task
        # finished first.  The basecase counterexample must still win.
        prop = "fvl_t0__fvl_checkers_v_44_assert_64"
        log = (eng("Temporal induction failed!", "induction") +
               line(f"engine_0.induction: ##   0:00:00  Assert failed in idx_signed_bug: fvl_checkers.v:44.77-44.88 "
                    f"({W}{prop})") +
               eng("Writing trace to VCD file: engine_0/trace_induct.vcd", "induction") +
               eng("Status: failed", "induction") +
               eng("Checking assumptions in step 0..", "basecase") +
               eng("Checking assertions in step 0..", "basecase") +
               eng("BMC failed!", "basecase") +
               line(f"engine_0.basecase: ##   0:00:00  Assert failed in idx_signed_bug: fvl_checkers.v:44.77-44.88 "
                    f"({W}{prop})") +
               eng("Writing trace to VCD file: engine_0/trace0.vcd", "basecase") +
               line("summary: engine_0 (smtbmc --keep-going z3) returned FAIL for basecase") +
               line("summary: engine_0 (smtbmc --keep-going z3) returned FAIL for induction") +
               line("summary: counterexample trace [basecase]: run/engine_0/trace0.vcd") +
               line(f"summary:   failed assertion idx_signed_bug.{W}{prop} at fvl_checkers.v:44.77-44.88") +
               line("summary: counterexample trace [induction]: run/engine_0/trace_induct.vcd") +
               line(f"summary:   failed assertion idx_signed_bug.{W}{prop} at fvl_checkers.v:44.77-44.88") +
               line("DONE (FAIL, rc=2)"))
        d, r = self.parse(log, names=["fvl_t0"], rc=2)
        trace = os.path.join(os.path.relpath(os.path.join(d, "run"), self.tmp), "engine_0", "trace0.vcd")
        self.assertEqual(r.props["fvl_t0"], PropResult("fail", trace, 0, "basecase"))

    def test_first_basecase_counterexample_is_kept(self):
        # The same assertion failing again later (--keep-going) does not
        # replace the earliest counterexample and its trace.
        log = (eng("Checking assertions in step 2..") + assert_failed("fvl_t0__x") +
               eng("Writing trace to VCD file: engine_0/trace0.vcd") +
               eng("Checking assertions in step 5..") + assert_failed("fvl_t0__x") +
               eng("Writing trace to VCD file: engine_0/trace1.vcd") +
               line("DONE (FAIL, rc=2)"))
        _, r = self.parse(log, mode="bmc", rc=2)
        self.assertEqual(r.props["fvl_t0"].step, 2)
        self.assertTrue(r.props["fvl_t0"].trace.endswith("trace0.vcd"))

    def test_steps_of_an_induction_trace_are_ignored(self):
        log = (eng("Checking assertions in step 3..", "basecase") +
               assert_failed("fvl_t0__fvl_checkers_v_75_assert_74", "basecase") +
               eng("Writing trace to VCD file: engine_0/trace0.vcd", "basecase") +
               assert_failed("fvl_t0__fvl_checkers_v_75_assert_74", "induction") +
               line("summary: counterexample trace [basecase]: run/engine_0/trace0.vcd") +
               failed_summary("fvl_t0__fvl_checkers_v_75_assert_74", 3) +
               line("summary: counterexample trace [induction]: run/engine_0/trace_induct.vcd") +
               failed_summary("fvl_t0__fvl_checkers_v_75_assert_74", 7) +
               line("DONE (FAIL, rc=2)"))
        _, r = self.parse(log, names=["fvl_t0"], rc=2)
        self.assertEqual((r.props["fvl_t0"].phase, r.props["fvl_t0"].step), ("basecase", 3))

    def test_summary_step_overrides_last_checked_step(self):
        log = (line("engine_0: ##   0:00:00  Checking assertions in step 5..") +
               assert_failed("fvl_v0__fvl_checkers_v_89_assert_70", loc="fvl_checkers.v:89.220-89.232") +
               assert_failed("fvl_v1__fvl_checkers_v_75_assert_79", loc="fvl_checkers.v:75.220-75.232") +
               line("engine_0: ##   0:00:00  Writing trace to VCD file: engine_0/trace0.vcd") +
               failed_summary("fvl_v1__fvl_checkers_v_75_assert_79", 2, "fvl_checkers.v:75.220-75.232") +
               line("DONE (FAIL, rc=2)"))
        _, r = self.parse(log, mode="bmc", names=["fvl_v0", "fvl_v1"], rc=2)
        self.assertEqual((r.props["fvl_v0"].step, r.props["fvl_v1"].step), (5, 2))
        self.assertEqual(r.props["fvl_v0"].trace, r.props["fvl_v1"].trace)          # one trace, both props

    def test_cover(self):
        log = (eng("Reached cover statement in step 3 at top: fvl_stim.sv:16.13-16.31 "
                   f"({W}fvl_s0__fvl_stim_sv_16_cover_72)") +
               eng("Writing trace to VCD file: engine_0/trace0.vcd") +
               eng("Reached cover statement in step 3 at top: fvl_stim.sv:18.13-18.31 "
                   f"({W}fvl_s0__fvl_stim_sv_18_cover_96)") +
               line("engine_0: ##   0:00:00  Writing trace to VCD file: engine_0/trace1.vcd") +
               line("DONE (PASS, rc=0)"))
        _, r = self.parse(log, mode="cover", names=["fvl_s0", "fvl_t0"])
        s0 = r.get("fvl_s0")
        self.assertEqual((s0.status, s0.step, s0.phase), ("fail", 3, "cover"))
        self.assertTrue(r.get("fvl_s0").trace.endswith(os.path.join("engine_0", "trace0.vcd")))   # first one kept
        self.assertEqual(r.get("fvl_t0").status, "unknown")

    def test_unsatisfiable_assumptions_and_foreign_asserts(self):
        log = (line("engine_0.basecase: ##   0:00:00  Assumptions are unsatisfiable!") +
               line("engine_0: ##   0:00:00  Assert failed in top: user.v:3.1-3.9 (top.u_core.user_assert)") +
               line("DONE (ERROR, rc=16)"))
        _, r = self.parse(log, rc=16)
        self.assertEqual(r.status, "ERROR")
        self.assertIn("assumptions are unsatisfiable", r.error)
        self.assertEqual(r.props, {})

    def test_timeout(self):
        _, r = self.parse(line("summary: engine_0 (smtbmc) returned TIMEOUT") + line("DONE (TIMEOUT, rc=8)"), rc=8)
        self.assertEqual(r.status, "TIMEOUT")
        _, r = self.parse("", rc=-1)                                    # killed by the backstop
        self.assertEqual(r.status, "TIMEOUT")

    def test_pdr(self):
        log = (line("engine_0: Output 2 was asserted in frame  3 ( 3) (solved 1 out of 4 outputs).") +
               line("engine_0: Output 1 was asserted in frame 18 (18) (solved 2 out of 4 outputs).") +
               line("engine_0: Proved output 0 in frame 4.") +
               line("engine_0: Proved output 3 in frame 1449658768 (converged).") +
               line("summary: engine_0 (abc --keep-going pdr) returned FAIL") +
               line("summary: counterexample trace: run/engine_0/trace_0.vcd") +
               failed_summary("fvl_t1__fvl_checkers_v_75_assert_74", 46) +
               line("DONE (FAIL, rc=2)"))
        d, r = self.parse(log, engine=PDR, rc=2, ywa=["fvl_t0", "fvl_t1", "fvl_l0", "fvl_t2"])
        jobrel = os.path.relpath(os.path.join(d, "run"), self.tmp)
        self.assertEqual(r.props["fvl_t0"], PropResult("pass"))
        self.assertEqual(r.props["fvl_t2"], PropResult("pass"))
        self.assertEqual(r.props["fvl_t1"], PropResult("fail", os.path.join(jobrel, "engine_0", "trace_0.vcd"), 46,
                                                       "basecase"))                 # summary step, not frame 18
        self.assertEqual(r.props["fvl_l0"], PropResult("fail", phase="basecase"))     # no trace reported
        self.assertEqual(set(r.props), {"fvl_t0", "fvl_t1", "fvl_t2", "fvl_l0"})

    def test_cut_short_summary_is_completed_from_the_status_file(self):
        # SymbiYosys lists five traces in the log, then "see run/FAIL for a
        # complete summary" (formats from a real run with eight failures).
        names = [f"fvl_t{i}" for i in range(7)]
        log = line("summary: engine_0 (abc --keep-going pdr) returned FAIL")
        full = "engine_0 (abc --keep-going pdr) returned FAIL\n"
        for i, n in enumerate(names):
            assertion = (f"failed assertion top._witness_.check_flatten_{n}__fvl_checkers_v_75_assert_74 "
                         f"at x.v:1.2-1.3 step {i}")
            if i < 5:
                log += line(f"summary: counterexample trace: run/engine_0/trace_{i}.vcd")
                log += line(f"summary:   {assertion}")
            full += "".join(f"counterexample trace: engine_0/trace_{i}.{ext}\n" for ext in ("vcd", "yw", "aiw"))
            full += f"  {assertion}\n"
        log += line("summary: and 2 further traces") + line("summary: see run/FAIL for a complete summary")
        log += line("DONE (FAIL, rc=2)")
        d = self.run_dir(log, names)
        with open(os.path.join(d, "run", "FAIL"), "w") as f:
            f.write(full)
        r = parse_job(d, self.tmp, 2, PDR, "prove", names)
        jobrel = os.path.relpath(os.path.join(d, "run"), self.tmp)
        self.assertEqual({n: (p.status, p.trace, p.step) for n, p in r.props.items()},
                         {n: ("fail", os.path.join(jobrel, "engine_0", f"trace_{i}.vcd"), i)
                          for i, n in enumerate(names)})
        # The same log without the status file: the first five only.
        os.remove(os.path.join(d, "run", "FAIL"))
        self.assertEqual(set(parse_job(d, self.tmp, 2, PDR, "prove", names).props), set(names[:5]))

    def test_cut_short_property_list_of_one_trace(self):
        # SymbiYosys also lists at most five properties per trace ("  and 2
        # further assertions"), without the "further traces" line.
        names = [f"fvl_t{i}" for i in range(7)]
        failed = [f"failed assertion top._witness_.check_flatten_{n}__x at x.v:1.2-1.3 step 4" for n in names]
        log = line("summary: counterexample trace: run/engine_0/trace_0.vcd")
        log += "".join(line(f"summary:   {a}") for a in failed[:5])
        log += line("summary:   and 2 further assertions") + line("DONE (FAIL, rc=2)")
        d = self.run_dir(log, names)
        with open(os.path.join(d, "run", "FAIL"), "w") as f:
            f.write("counterexample trace: engine_0/trace_0.vcd\n" + "".join(f"  {a}\n" for a in failed))
        r = parse_job(d, self.tmp, 2, PDR, "prove", names)
        self.assertEqual(sorted(r.props), names)
        self.assertEqual({(p.status, p.step) for p in r.props.values()}, {("fail", 4)})
        self.assertTrue(all(p.trace for p in r.props.values()))

    def test_cut_short_kinduction_summary(self):
        # k-induction: the steps of traces past the fifth come from the status file too.
        log = eng("Checking assertions in step 9..")
        full = ""
        for i in range(7):
            log += assert_failed(f"fvl_t{i}__x") + eng(f"Writing trace to VCD file: engine_0/trace{i}.vcd")
            full += f"counterexample trace [basecase]: engine_0/trace{i}.vcd\n"
            full += f"  failed assertion top._witness_.check_flatten_fvl_t{i}__x at x.v:1.2-1.3 step {i}\n"
        log += line("summary: and 2 further traces") + line("DONE (FAIL, rc=2)")
        d = self.run_dir(log)
        with open(os.path.join(d, "run", "FAIL"), "w") as f:
            f.write(full)
        r = parse_job(d, self.tmp, 2, SMTBMC, "prove", [f"fvl_t{i}" for i in range(7)])
        self.assertEqual([r.props[f"fvl_t{i}"].step for i in range(7)], list(range(7)))
        # The phase is kept: steps listed under an induction trace are not
        # counterexample steps.  The file is read leniently (a stray byte).
        with open(os.path.join(d, "run", "FAIL"), "wb") as f:
            f.write(b"\xff\n" + full.replace("[basecase]", "[induction]").encode())
        r = parse_job(d, self.tmp, 2, SMTBMC, "prove", [f"fvl_t{i}" for i in range(7)])
        self.assertEqual([r.props[f"fvl_t{i}"].step for i in range(7)], [9] * 7)   # from the engine lines

    def test_completed_summary_lines(self):
        # The appended lines read like SymbiYosys's own: a phase only where the file has one.
        d = os.path.join(self.tmp, "job")
        os.makedirs(d)
        with open(os.path.join(d, "FAIL"), "w") as f:
            f.write("counterexample trace [basecase]: engine_0/trace0.vcd\n"
                    "counterexample trace [basecase]: engine_0/trace0.yw\n"
                    "  failed assertion top.x at x.v:1.2-1.3 step 3\n"
                    "counterexample trace: engine_0/trace_1.vcd\n")
        self.assertEqual(_complete_summary(d, "summary: and 1 further trace", "FAIL"),
                         "\nsummary: counterexample trace [basecase]: job/engine_0/trace0.vcd\n"
                         "summary:   failed assertion top.x at x.v:1.2-1.3 step 3\n"
                         "summary: counterexample trace: job/engine_0/trace_1.vcd\n")
        self.assertEqual(_complete_summary(d, "summary: counterexample trace: x.vcd", "FAIL"), "")   # not cut short

    def test_pdr_failure_at_step_zero(self):
        # Verbatim from a YoWASP 0.71 run: SymbiYosys leaves "step 0" out.
        log = ("SBY 16:39:24 [run] engine_0: Output 0 was asserted in frame  0 ( 0) (solved 1 out of 1 outputs).\n"
               "SBY 16:39:24 [run] summary: engine_0 (abc --keep-going pdr) returned FAIL\n"
               "SBY 16:39:24 [run] summary: counterexample trace: run/engine_0/trace_0.vcd\n"
               "SBY 16:39:24 [run] summary:   failed assertion arst_mask._witness_.check_flatten_fvl_t0__fvl_checkers_v"
               "_44_assert_64 at fvl_checkers.v:44.77-44.88\n"
               "SBY 16:39:24 [run] DONE (FAIL, rc=2)\n")
        d, r = self.parse(log, engine=PDR, rc=2, ywa=["fvl_t0"])
        jobrel = os.path.relpath(os.path.join(d, "run"), self.tmp)
        self.assertEqual(r.props["fvl_t0"], PropResult("fail", os.path.join(jobrel, "engine_0", "trace_0.vcd"), 0,
                                                       "basecase"))

    def test_summary_with_several_steps(self):
        # sby_core.py: "step{'s' if len(steps) > 1 else ''} {', '.join(steps)}", plus
        # " and N further steps" when shortened; the first step is the earliest.
        for tail, step in ((" steps 3, 7", 3), (" steps 2, 4, 6 and 5 further steps", 2), (" step 9", 9), ("", 0)):
            with self.subTest(tail=tail):
                log = (line("summary: counterexample trace: run/engine_0/trace_0.vcd") +
                       line(f"summary:   failed assertion top.{W}fvl_t0__x at fvl_checkers.v:1.1-1.2{tail}") +
                       line("DONE (FAIL, rc=2)"))
                _, r = self.parse(log, engine=PDR, rc=2, ywa=["fvl_t0"])
                self.assertEqual(r.props["fvl_t0"].step, step)
                log = (eng("Checking assertions in step 12..") + assert_failed("fvl_t0__x") +
                       eng("Writing trace to VCD file: engine_0/trace0.vcd") +
                       line(f"summary:   failed assertion top.{W}fvl_t0__x at fvl_checkers.v:1.1-1.2{tail}") +
                       line("DONE (FAIL, rc=2)"))
                _, r = self.parse(log, mode="bmc", rc=2)
                self.assertEqual(r.props["fvl_t0"].step, step)

    def test_pdr_variants(self):
        # "of miter" form, summary trace tag, PASS filling in the rest.
        log = (line("engine_0: Output 0 of miter top was asserted in frame 2.") +
               line("summary: counterexample trace [run]: run/engine_0/trace_0.vcd") +
               line(f"summary:   failed assertion top.{W}fvl_t0__x at fvl_checkers.v:1.1-1.2 step 2") +
               line("DONE (PASS, rc=0)"))
        _, r = self.parse(log, engine=PDR, ywa=["fvl_t0", "fvl_t1", "user"])
        self.assertEqual((r.props["fvl_t0"].status, r.props["fvl_t0"].step), ("fail", 2))
        self.assertEqual(r.props["fvl_t1"], PropResult("pass"))
        self.assertEqual(set(r.props), {"fvl_t0", "fvl_t1"})

    def test_pdr_odd_lines(self):
        log = (failed_summary("fvl_t0__x", 2) +                                 # no trace line before it
               line("engine_0: Output 2 was asserted in frame 3.") +             # no such output
               line("DONE (FAIL, rc=2)"))
        _, r = self.parse(log, engine=PDR, ywa=["fvl_t0", "fvl_t1"])
        self.assertEqual(r.props, {})

    def test_pdr_without_witness_map(self):
        _, r = self.parse(line("engine_0: Proved output 0 in frame 4.") + line("DONE (PASS, rc=0)"), engine=PDR)
        self.assertEqual(r.props, {})                                   # cannot tell which property

    def test_prop_default_mode_is_assert(self):
        self.assertEqual(Prop("t", "c", {}, {}, []).mode, 0)

    def test_job_result_get(self):
        r = JobResult("PASS", {"a": PropResult("pass")})
        self.assertEqual((r.get("a").status, r.get("b").status), ("pass", "unknown"))

    def test_yw_for(self):
        vcd = self.write("e/trace0.vcd", "")
        self.assertIsNone(yw_for(vcd))
        yw = self.write("e/trace0.yw", "{}")
        self.assertEqual(yw_for(vcd), yw)


class Traces(TempDirCase):
    def test_real_witness(self):
        sig = read_yw(os.path.join(DATA, "traces", "replay.yw"))
        # signals clk, go, rst; bits strings are MSB...LSB with the first signal last
        self.assertEqual(sig, {"clk": ["0", "0", "0", "0"], "go": ["0", "0", "0", "0"], "rst": ["1", "1", "1", "0"]})

    def test_witness_details(self):
        p = self.write_json("t.yw", {"signals": [
            {"path": ["\\a"], "width": 2, "offset": 0, "init_only": False},
            {"path": ["\\b"], "width": 1, "offset": 3, "init_only": False},      # part of a wider signal
            {"path": ["\\u", "\\q"], "width": 1, "offset": 0, "init_only": False},  # hierarchical: skipped
            {"path": ["\\st"], "width": 1, "offset": 0, "init_only": True}],     # initial value: skipped
            "steps": [{"bits": "10110"}, {"bits": "000"}, {"bits": "01001"}]})    # step 2 is malformed
        self.assertEqual(read_yw(p), {"a": ["10", "01"], "b@3": ["1", "0"]})

    def test_real_vcd(self):
        # Each step holds the values last written before the next step starts
        # (so a clock shows its second half-cycle); the trace ends in step 4.
        v = read_vcd(os.path.join(DATA, "traces", "replay.vcd"))
        self.assertEqual(v["rst"], ["1", "1", "1", "0", "0"])
        self.assertEqual(v["clk"], ["0", "0", "0", "0", "1"])
        self.assertEqual(v["st"], ["000", "000", "000", "001", "001"])
        self.assertEqual(v["r1"], ["0", "1", "1", "1", "1"])
        self.assertEqual(v["fvl_t0.s"], ["000", "000", "000", "100", "100"])   # nested scope, top stripped
        self.assertEqual(v["fvl_s0.n"][2], "0000000000000010")
        self.assertNotIn("smt_step", v)
        self.assertEqual(len(v), 15)

    def test_vcd_aliases_gaps_and_odd_values(self):
        p = self.write("t.vcd", "$var integer 32 t smt_step $end\n$scope module top $end\n"
                                "$var wire 1 a x $end\n$var wire 1 a x_alias $end\n$var wire 4 b w [3:0] $end\n"
                                "$var real 64 r rr $end\n$upscope $end\n$enddefinitions $end\n"
                                "#0\nb0 t\n0a\nbxx01 b\nr1.5 r\n#10\nb10 t\n1a\nB1111 b\n#20\nbz t\n")
        v = read_vcd(p)
        self.assertEqual(v["x"], ["0", None, "1"])                     # step 1 missing: padded
        self.assertEqual(v["x_alias"], v["x"])
        self.assertEqual(v["w"], ["xx01", None, "1111"])
        self.assertEqual(v["rr"], ["1.5", None, "1.5"])

    def test_vcd_signal_without_a_value_yet(self):
        p = self.write("t.vcd", "$var integer 32 t smt_step $end\n$scope module top $end\n"
                                "$var wire 1 a x $end\n$var wire 1 b late $end\n$var wire 1 c never $end\n"
                                "$upscope $end\n$enddefinitions $end\n"
                                "#0\nb0 t\n0a\n\n#10\nb1 t\n1b\n#20\n")
        v = read_vcd(p)
        self.assertEqual((v["x"], v["late"]), (["0", "0"], [None, "1"]))
        self.assertNotIn("never", v)                    # no value at all: absent, so replay cannot match it

    def test_vcd_without_step_variable(self):
        p = self.write("t.vcd", "$scope module top $end\n$var wire 1 a x $end\n$upscope $end\n"
                                "$enddefinitions $end\n#0\n1a\n")
        self.assertEqual(read_vcd(p), {})

    def test_norm(self):
        self.assertIsNone(_norm(None, 3))
        self.assertEqual(_norm("1", 4), "0001")
        self.assertEqual(_norm("X1", 3), "xx1")
        self.assertEqual(_norm("z", 2), "zz")
        self.assertEqual(_norm("10110", 3), "110")

    def test_stimulus_module(self):
        text = stim_module([("req", 2), ("go", 1)], {"req": ["10", "x1", None], "go": ["1"]}, 2)
        self.assertIn("  input [1:0] p0,\n  input [0:0] p1\n);", text)
        self.assertIn("16'd0: begin assume ((p0 & 2'b11) == 2'b10); assume ((p1 & 1'b1) == 1'b1); end", text)
        self.assertIn("16'd1: begin assume ((p0 & 2'b01) == 2'b01); end", text)      # x bits left free
        self.assertNotIn("16'd2:", text)                                              # nothing known at step 2
        self.assertNotIn("16'd1:", stim_module([("go", 1)], {"go": ["1", "1", "1"]}, 0))  # only up to last_step
        self.assertIn("always @* cover (n == 16'd2);", text)
        self.assertTrue(text.startswith("module fvl_stim (") and text.endswith("endmodule\n"))

    def test_stimulus_module_text(self):
        self.assertEqual(stim_module([("go", 1)], {"go": ["1", None]}, 1),
                         "module fvl_stim (\n"
                         "  input [0:0] p0\n"
                         ");\n"
                         "  (* gclk *) wire gclk;\n"
                         "  reg [15:0] n = 16'd0;\n"
                         "  always @(posedge gclk) if (n != 16'hffff) n <= n + 16'd1;\n"
                         "  always @* begin\n"
                         "    case (n)\n"
                         "      16'd0: begin assume ((p0 & 1'b1) == 1'b1); end\n"
                         "      default: ;\n"
                         "    endcase\n"
                         "  end\n"
                         "  always @* cover (n == 16'd1);\n"
                         "endmodule\n")

    def test_stimulus_fully_unknown_step_and_no_ports(self):
        text = stim_module([("a", 2)], {"a": ["xx"]}, 0)
        self.assertNotIn("16'd0:", text)
        self.assertIn("module fvl_stim (\n\n);", stim_module([], {}, 0))

    def test_divergence(self):
        slice_v = {"a": ["0", "1", "1"], "b": ["1", "1", "1"], "w": ["01", "x1", "11"], "late": ["0", "0", "0"]}
        real_v = {"a": ["0", "0", "1"], "b": ["1", "1", "1"], "w": ["1", "00", "11"], "late": ["0", "0", "1"]}
        slice_v["half"], real_v["other_half"] = ["0"], ["0"]
        cut = {"A": [("a", 1)], "B": [("b", 1)], "C": [("missing", 1)], "D": [], "W": [("w", 2)],
               "L": [("late", 1)], "M": [("b", 1), ("a", 1)], "H": [("half", 1)], "O": [("other_half", 1)]}
        self.assertEqual(divergent(slice_v, real_v, cut, 1), {"A", "C", "D", "M", "H", "O"})
        self.assertEqual(divergent(slice_v, real_v, cut, 2), {"A", "C", "D", "M", "H", "O", "L"})
        # Unknown bits on either side are no evidence of divergence.
        self.assertEqual(divergent({"u": ["1", "x"]}, {"u": ["x", "0"]}, {"U": [("u", 1)]}, 1), set())

    def test_divergence_against_real_trace(self):
        v = read_vcd(os.path.join(DATA, "traces", "replay.vcd"))
        shutil.copy(os.path.join(DATA, "traces", "replay.vcd"), self.tmp)
        self.assertEqual(divergent(v, v, {"r1": [("r1", 1)], "st": [("st", 3)]}, 3), set())
        other = dict(v, st=["000", "000", "000", "010"])
        self.assertEqual(divergent(v, other, {"r1": [("r1", 1)], "st": [("st", 3)]}, 3), {"st"})


if __name__ == "__main__":
    unittest.main()
