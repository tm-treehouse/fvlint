# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""fvlint.fuzz: the design generator and the oracle's judging logic.  The
oracle's bounded model check is faked; its verdict rules run for real."""

from __future__ import annotations

import json
import os
import re
import shutil
import unittest
from unittest import mock

from fvlint import cli, fuzz
from fvlint.detect import detect_all
from fvlint.engine import Engine
from fvlint.netlist import Netlist
from fvlint.sby import JobResult, PropResult
from fvlint.tools import Toolchain

from .support import TempDirCase, captured, snapshot


class Generator(unittest.TestCase):
    def test_deterministic_per_seed(self):
        self.assertEqual(fuzz.generate(7), fuzz.generate(7))
        self.assertNotEqual(fuzz.generate(7)[0], fuzz.generate(8)[0])
        text, top = fuzz.generate(42)
        self.assertEqual(top, "fz42")
        self.assertTrue(text.startswith("module fz42 (") and text.endswith("endmodule\n"))

    def test_shape(self):
        for seed in range(1, 60):
            text, _ = fuzz.generate(seed)
            with self.subTest(seed=seed):
                regs = re.findall(r"reg \[(\d+):0\] r(\d+);", text)
                self.assertTrue(2 <= len(regs) <= 4)
                self.assertTrue(all(1 <= int(w) <= 4 for w, _ in regs))           # 2..5-bit registers
                self.assertEqual([int(i) for _, i in regs], list(range(len(regs))))
                outs = re.search(r"assign o = \{(.*)\};", text).group(1).split(", ")
                self.assertEqual(outs[:len(regs)], [f"r{i}" for i in range(len(regs))])   # nothing optimised away
                declared = set(re.findall(r"(?:reg|wire)(?: signed)?(?: \[[^\]]*\])? (\w+)", text))
                self.assertLessEqual(set(outs), declared)
                self.assertEqual(text.count("module "), 1)
                self.assertEqual(text.splitlines()[-1], "endmodule")

    def test_every_feature_is_generated(self):
        texts = "\n".join(fuzz.generate(s)[0] for s in range(1, 120))
        for feature in ("posedge clk2", "negedge clk", "unique casez", "unique case (1'b1)", "*4 +: 4]",
                        "reg [3:0] mem [0:", "else if (r", "<= 1'b1; else ok", "r0 - ",
                        "s1 <= rst; s2 <= s1;", "if (s2) r", "msk <= 1'b1; else msk <= s1", "if (msk) r",
                        "wire signed [3:0] sidx = {in", "wire signed [3:0] sidx = {1'b0"):
            with self.subTest(feature=feature):
                self.assertIn(feature, texts)


class OracleCase(TempDirCase):
    """An fvlint output directory for the snap_counters / snap_fsm snapshots."""

    def outdir(self, top, results: dict, cex_steps=None):
        d = os.path.join(self.tmp, top)
        os.makedirs(os.path.join(d, "elab"))
        shutil.copy(snapshot(top), os.path.join(d, "elab", "main.json"))
        shutil.copy(snapshot(top, "fsm"), os.path.join(d, "elab", "fsm.json"))
        rows = []
        for cid, st in results.items():
            kind, _, target = cid.partition(":")
            rows.append({"id": cid, "kind": kind, "target": target, "status": st,
                         "cex_step": (cex_steps or {}).get(cid)})
        with open(os.path.join(d, "results.json"), "w") as f:
            json.dump({"results": rows}, f)
        return d

    def oracle(self, d, top, answer, depth=24, max_depth=80):
        """answer(call_props) -> JobResult for the oracle's single BMC job."""
        calls = []

        def fake_run(eng, tag, spec, props, mode, depth, multiclock, engine=None, **kw):
            calls.append((tag, spec, props, mode, depth, multiclock, engine))
            self.engine, self.extra = eng, kw
            return answer(props)
        with mock.patch.object(Engine, "run", fake_run), \
                mock.patch.object(Toolchain, "discover",
                                  staticmethod(lambda solver=None: mock.Mock(abc=None, solver="z3"))):
            out = fuzz.oracle(d, top, depth, {}, max_depth)
        return out, calls


class Oracle(OracleCase):
    def test_agreeing_verdicts(self):
        d = self.outdir("snap_counters", {"counter_overflow:mod_q": "PROVEN", "counter_underflow:down_q": "FAIL",
                                          "counter_overflow:free_q": "INFO"}, {"counter_underflow:down_q": 6})
        (problems, inconclusive), calls = self.oracle(
            d, "snap_counters", lambda props: JobResult("FAIL", {props[1].name: PropResult("fail")}))
        self.assertEqual((problems, inconclusive), ([], []))
        (tag, spec, props, mode, depth, mc, engine), = calls
        self.assertEqual((tag, mode, depth, mc, engine), ("oracle_bmc", "bmc", 24, False, "smtbmc --keep-going z3"))
        self.assertTrue(spec.full)                                      # the whole cone, no cuts
        self.assertEqual([p.mode for p in props], [0, 0])
        rst = Netlist.load(snapshot("snap_counters"), "snap_counters").ports["rst"]["bits"][0]
        self.assertTrue(all((rst, 0) in p.conds for p in props))        # reset gating as in fvlint
        self.assertEqual(self.engine.resets.primary.name, "rst")        # reset held as fvlint holds it

    def test_disagreements(self):
        d = self.outdir("snap_counters", {"counter_overflow:mod_q": "PROVEN", "counter_overflow:acc": "VACUOUS",
                                          "counter_underflow:down_q": "FAIL"}, {"counter_underflow:down_q": 3})
        (problems, inconclusive), calls = self.oracle(
            d, "snap_counters", lambda props: JobResult("FAIL", {props[0].name: PropResult("fail"),
                                                                 props[1].name: PropResult("fail")}))
        self.assertEqual(problems, ["counter_overflow:mod_q: fvlint PROVEN, oracle found a violation",
                                    "counter_overflow:acc: fvlint VACUOUS, oracle reached the check's condition",
                                    "counter_underflow:down_q: fvlint FAIL, oracle found no violation within 24 steps"])
        self.assertEqual(inconclusive, [])
        self.assertEqual([p.mode for p in calls[0][2]], [0, 2, 0])      # VACUOUS: probe the condition

    def test_fail_beyond_the_oracle(self):
        d = self.outdir("snap_counters", {"counter_underflow:down_q": "FAIL"}, {"counter_underflow:down_q": 90})
        (problems, inconclusive), calls = self.oracle(d, "snap_counters", lambda props: JobResult("PASS"))
        self.assertEqual(problems, [])
        self.assertEqual(calls[0][4], 80)                               # bound capped at max_depth
        self.assertIn("FAIL at step 90 beyond the oracle's reach (bound 80, job PASS)", inconclusive[0])

    def test_unfinished_oracle_job(self):
        d = self.outdir("snap_counters", {"counter_underflow:down_q": "FAIL"}, {"counter_underflow:down_q": 2})
        (problems, inconclusive), calls = self.oracle(d, "snap_counters", lambda props: JobResult("TIMEOUT"))
        self.assertEqual((problems, len(inconclusive)), ([], 1))
        self.assertEqual(calls[0][4], 24)                               # max(depth, step + 4)

    def test_unreachable_fsm_state(self):
        d = self.outdir("snap_fsm", {"fsm_unreachable:st=2'b11": "FAIL", "fsm_trap:st={2'b10}": "WARN"})
        (problems, _), calls = self.oracle(d, "snap_fsm", lambda props: JobResult("PASS"))
        self.assertEqual(problems, [])
        (p,) = calls[0][2]
        self.assertEqual(p.ports, {"v": Netlist.load(snapshot("snap_fsm"), "snap_fsm").netnames["st"]["bits"]})
        self.assertEqual((p.checker, p.params, p.mode),
                         ("fvl_member", {"W": 2, "N": 3, "SET": 0 | (1 << 2) | (2 << 4)}, 0))
        (problems, _), _ = self.oracle(d, "snap_fsm", lambda props: JobResult("FAIL", {"fvl_t0": PropResult("fail")}))
        self.assertEqual(problems, ["fsm_unreachable:st=2'b11: fvlint says unreachable, oracle reached it"])

    def test_nothing_to_check(self):
        d = self.outdir("snap_counters", {"counter_overflow:free_q": "INFO", "counter_overflow:mod_q": "UNKNOWN",
                                          "fsm_unreachable:nope=2'b11": "FAIL", "fsm_unreachable:st=x": "FAIL",
                                          "fsm_unreachable:free_q=4'b1111": "WAIVED"})
        out, calls = self.oracle(d, "snap_counters", lambda props: self.fail("no job"))
        self.assertEqual((out, calls), (([], []), []))

    def test_wide_state_registers_are_skipped(self):
        d = self.outdir("snap_counters", {"fsm_unreachable:acc=6'b111111": "FAIL",      # 6 bits: checked
                                          "fsm_unreachable:o=32'b1": "FAIL"})          # too wide to enumerate
        (_, _), calls = self.oracle(d, "snap_counters", lambda props: JobResult("PASS"))
        self.assertEqual([p.params["W"] for p in calls[0][2]], [6])

    def test_eight_bit_state_registers_are_enumerated(self):
        d = self.outdir("snap_ops", {"fsm_unreachable:w=8'b00000011": "FAIL"})
        _, calls = self.oracle(d, "snap_ops", lambda props: JobResult("PASS"))
        (p,) = calls[0][2]
        self.assertEqual((p.params["W"], p.params["N"]), (8, 255))

    def test_oracle_regenerates_checks_with_fvlints_default_level(self):
        seen = []
        real = detect_all

        def spy(nl, max_level):
            seen.append(max_level)
            return real(nl, max_level)
        d = self.outdir("snap_counters", {"counter_overflow:mod_q": "PROVEN"})
        with mock.patch("fvlint.detect.detect_all", spy):
            self.oracle(d, "snap_counters", lambda props: JobResult("PASS"))
        self.assertEqual(seen, [cli.build_parser().parse_args(["--top", "t"]).max_level])

    def test_timeout_reaches_the_oracle_engine(self):
        d = self.outdir("snap_counters", {"counter_overflow:mod_q": "PROVEN"})
        calls = []
        with mock.patch.object(Engine, "run", lambda eng, *a, **kw: calls.append(eng.opts) or JobResult("PASS")), \
                mock.patch.object(Toolchain, "discover",
                                  staticmethod(lambda solver=None: mock.Mock(abc=None, solver="z3"))):
            fuzz.oracle(d, "snap_counters", 24, {"timeout": 7}, 80)
        self.assertEqual((calls[0].timeout, calls[0].engine), (7, "smtbmc"))

    def test_active_high_primary_reset_gating(self):
        # snap_counters' rst is active high: the oracle's own gating holds it at 0.
        from fvlint.resets import ResetBit, Resets
        nl = Netlist.load(snapshot("snap_counters"), "snap_counters")
        rst, lim0 = nl.ports["rst"]["bits"][0], nl.netnames["lim"]["bits"][0]
        resets = Resets(ResetBit("rst", rst, 1), [ResetBit("lim[0]", lim0, 1, 1)], 2)
        d = self.outdir("snap_counters", {"counter_overflow:mod_q": "PROVEN"})
        with mock.patch("fvlint.resets.discover", lambda *a, **kw: resets):
            _, calls = self.oracle(d, "snap_counters", lambda props: JobResult("PASS"))
        own, indep = calls[0][2]
        chk = {c.id: c for c in detect_all(nl, 3)[0]}["counter_overflow:mod_q"]
        settled = self.extra["extra_cells"]["fvo_settle"]["connections"]["done"][0]
        self.assertEqual(own.conds, chk.conds + [(rst, 0), (lim0, 0)])
        self.assertEqual(indep.conds, chk.conds + [(rst, 0), (settled, 1)])

    def test_bound_and_reach(self):
        # bound = min(max(depth, cex step + 4), max_depth); a FAIL counts as
        # missed only if its step + 4 fits within a finished bound.
        cases = [({"counter_underflow:down_q": None}, 2, 4), ({"counter_underflow:down_q": 6}, 2, 10),
                 ({"counter_underflow:down_q": 77}, 2, 80)]
        for steps, depth, bound in cases:
            with self.subTest(steps=steps):
                d = self.outdir("snap_counters", {"counter_underflow:down_q": "FAIL"}, steps)
                (problems, inconc), calls = self.oracle(d, "snap_counters", lambda props: JobResult("PASS"),
                                                        depth=depth)
                self.assertEqual(calls[0][4], bound)
                missed = steps["counter_underflow:down_q"] != 77                # 77 + 4 > 80: out of reach
                self.assertEqual((len(problems), len(inconc)), (1, 0) if missed else (0, 1))
                shutil.rmtree(d)

    def test_index_checks_use_the_oracles_own_bounds(self):
        # Bounds come from the $shiftx cell and are compared in wider signed
        # arithmetic: the 0.2.0 signed-index false proof had a wrong bound.
        d = self.outdir("snap_index", {"index_range:ys": "PROVEN", "index_range:yu": "FAIL"},
                        {"index_range:yu": 1})
        _, calls = self.oracle(d, "snap_index", lambda props: JobResult("FAIL", {props[1].name: PropResult("fail")}))
        got = [(p.checker, p.params) for p in calls[0][2]]
        self.assertEqual(got, [("fvo_index", {"BW": 4, "SIGNED": 1, "MAXOFF": 11}),
                               ("fvo_index", {"BW": 4, "SIGNED": 0, "MAXOFF": 11})])
        nl = Netlist.load(snapshot("snap_index"), "snap_index")
        idx = {c.id: c for c in detect_all(nl, 3)[0]}
        self.assertEqual([p.ports for p in calls[0][2]], [idx["index_range:ys"].ports, idx["index_range:yu"].ports])
        self.assertEqual(set(self.extra["extra_files"]), {"fvo_oracle.v"})

    def test_derived_resets_get_independent_gating(self):
        # snap_reset: primary rst_n, synchronized r1 and r2 (reset held 3 cycles).
        nl = Netlist.load(snapshot("snap_reset"), "snap_reset")
        d = self.outdir("snap_reset", {"counter_overflow:q": "PROVEN"})
        (problems, _), calls = self.oracle(
            d, "snap_reset", lambda props: JobResult("FAIL", {props[1].name: PropResult("fail")}))
        own, indep = calls[0][2]
        rst_n = nl.ports["rst_n"]["bits"][0]
        derived = [(nl.netnames[n]["bits"][0], 1) for n in ("r1", "r2")]
        chk = {c.id: c for c in detect_all(nl, 3)[0]}["counter_overflow:q"]
        settled = self.extra["extra_cells"]["fvo_settle"]["connections"]["done"][0]
        self.assertEqual(own.conds, chk.conds + [(rst_n, 1)] + derived)
        self.assertEqual(indep.conds, chk.conds + [(rst_n, 1), (settled, 1)])     # no derived resets
        self.assertNotIn(settled, [b for n in nl.netnames.values() for b in n["bits"]])   # a fresh bit
        self.assertEqual(self.extra["extra_cells"]["fvo_settle"],
                         {"hide_name": 0, "type": "fvo_settled", "parameters": {"N": 3 + fuzz.SETTLE},
                          "attributes": {}, "port_directions": {"done": "output"}, "connections": {"done": [settled]}})
        self.assertEqual(calls[0][4], 24)
        self.assertEqual((own.ports, indep.ports), (chk.ports, chk.ports))
        _, calls = self.oracle(d, "snap_reset", lambda props: JobResult("PASS"), depth=2)
        self.assertEqual(calls[0][4], 3 + fuzz.SETTLE + 6)              # deep enough to get past the settle time
        with mock.patch("fvlint.cone.needs_multiclock", return_value=True):
            self.oracle(d, "snap_reset", lambda props: JobResult("PASS"))
        self.assertEqual(self.extra["extra_cells"]["fvo_settle"]["parameters"], {"N": 2 * (3 + fuzz.SETTLE)})
        self.assertEqual(problems, ["counter_overflow:q: fvlint PROVEN, oracle found a violation "
                                    "(with the oracle's own reset gating)"])

    def test_fail_verdicts_use_fvlints_gating_only(self):
        d = self.outdir("snap_reset", {"counter_overflow:q": "FAIL"}, {"counter_overflow:q": 4})
        _, calls = self.oracle(d, "snap_reset", lambda props: JobResult("FAIL", {props[0].name: PropResult("fail")}))
        self.assertEqual(len(calls[0][2]), 1)

    def test_oracle_library_matches_its_props(self):
        mods = dict(re.findall(r"module (\w+) #\((.*?)\)\s*\(", fuzz.ORACLE_V, re.S))
        self.assertEqual(set(re.findall(r"parameter integer (\w+)", mods["fvo_index"])) - {"NC", "MODE"},
                         {"BW", "SIGNED", "MAXOFF"})
        self.assertIn("N", re.findall(r"parameter integer (\w+)", mods["fvo_settled"]))

    def test_oracle_checks_match_fvlint_checks(self):
        nl = Netlist.load(snapshot("snap_counters"), "snap_counters")
        ids = {c.id for c in detect_all(nl, 3)[0]}
        self.assertIn("counter_overflow:mod_q", ids)                    # the ids used above are real


class Driver(TempDirCase):
    def test_run(self):
        argvs = []

        def fake_main(argv):
            argvs.append(argv)
            out = argv[argv.index("-o") + 1]
            if out.endswith("seed2"):
                with open(os.path.join(out, "results.json"), "w") as f:
                    json.dump({"results": []}, f)                       # stale or partial results
                return 2
            if out.endswith("seed4"):
                return 1                                                # crashed before writing results
            with open(os.path.join(out, "results.json"), "w") as f:
                json.dump({"results": [{"status": "PROVEN"}, {"status": "FAIL"}]}, f)
            return 1
        oracle_calls = []

        def fake_oracle(d, top, depth, opts):
            oracle_calls.append((os.path.basename(d), top, depth))
            return (["x: disagreement"], ["y: too deep"]) if top == "fz3" else ([], [])
        with mock.patch.object(cli, "main", fake_main), mock.patch.object(fuzz, "oracle", fake_oracle), \
                captured() as (_, err):
            s = fuzz.run([1, 2, 3, 4], self.tmp, depth=12, extra_args=["--engine", "pdr"], verbose=True)
            again = fuzz.run([1], self.tmp, depth=12)                    # same output tree again
        self.assertEqual((s["seeds"], s["checks"], s["statuses"]), (4, 4, {"PROVEN": 2, "FAIL": 2}))
        self.assertEqual((again["seeds"], again["problems"]), (1, []))
        d1 = os.path.join(self.tmp, "seed1")
        self.assertEqual(argvs[0], ["--top", "fz1", os.path.join(d1, "fz1.v"), "-o", d1, "-j", "1", "--engine", "pdr"])
        self.assertTrue(0 <= s["seconds"] < 60)
        self.assertEqual(oracle_calls, [("seed1", "fz1", 12), ("seed3", "fz3", 12), ("seed1", "fz1", 12)])
        self.assertEqual(len(s["problems"]), 3)
        self.assertIn("seed 2: fvlint did not complete (rc=2)", s["problems"][0])
        self.assertTrue(s["problems"][1].startswith("seed 3: x: disagreement (design: "))
        self.assertIn("seed 4: fvlint did not complete (rc=1)", s["problems"][2])
        self.assertEqual(s["inconclusive"], ["seed 3: y: too deep"])
        self.assertIn("seed 3: 2 checks, 1 problem(s)", err.getvalue())
        with open(os.path.join(self.tmp, "seed1", "fz1.v")) as f:
            self.assertEqual(f.read(), fuzz.generate(1)[0])

    def test_main(self):
        captured_args = []

        def fake_run(seeds, out, depth, extra, verbose):
            captured_args.append((list(seeds), out, depth, extra, verbose))
            return {"seeds": 2, "checks": 5, "statuses": {}, "problems": ["p"] if depth == 9 else [],
                    "inconclusive": [], "seconds": 0.1}
        with mock.patch.object(fuzz, "run", fake_run), captured() as (out, _):
            self.assertEqual(fuzz.main(["--seeds", "2", "--first-seed", "5", "-o", "x", "--engine", "smtbmc"]), 0)
            self.assertEqual(fuzz.main(["--depth", "9"]), 1)
            for engine in ("auto", "pdr"):
                self.assertEqual(fuzz.main(["--engine", engine]), 0)
        self.assertEqual(captured_args[0], ([5, 6], "x", 24, ["--engine", "smtbmc"], False))
        self.assertEqual(captured_args[1], (list(range(1, 21)), "fvlint_fuzz", 9, ["--engine", "auto"], False))
        self.assertEqual([a[3] for a in captured_args[2:]], [["--engine", "auto"], ["--engine", "pdr"]])
        self.assertIn("  p", out.getvalue().splitlines())


if __name__ == "__main__":
    unittest.main()
