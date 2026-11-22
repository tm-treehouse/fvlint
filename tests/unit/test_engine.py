# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""fvlint.engine: the proof scheduler.

Engine.run (the one method that starts SymbiYosys) is replaced by a scripted
fake, so slicing, batching, refinement, replay, deep BMC and vacuity logic run
for real against controlled solver answers."""

from __future__ import annotations

import json
import os
import threading
import unittest
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field

from fvlint.checks import ERROR, FAIL, PROVEN, UNKNOWN, VACUOUS, Check, Lemma, Result
from fvlint.cone import UNBOUNDED, ConeSpec, slice_spec
from fvlint.detect import detect_counters
from fvlint.engine import Engine, Options, St
from fvlint.netlist import Netlist, is_const
from fvlint.resets import ResetBit, Resets, discover
from fvlint.sby import JobResult, PropResult, instance

from .support import NB, TempDirCase, const


class FakeTools:
    def __init__(self, abc=True, solver="z3"):
        self.abc = "/usr/bin/yosys-abc" if abc else None
        self.solver = solver
        self.sby_calls = []
        self.log = "SBY 1:00:00 [run] DONE (PASS, rc=0)\n"

    def run_sby(self, sby, d, timeout):
        self.sby_calls.append((sby, d, timeout))
        os.makedirs(os.path.join(d, "run"), exist_ok=True)
        with open(os.path.join(d, "run", "logfile.txt"), "w") as f:
            f.write(self.log)
        return 0


@dataclass
class Call:
    tag: str
    spec: ConeSpec
    props: list
    mode: str
    depth: int
    multiclock: bool
    engine: str
    extra_cells: dict = field(default_factory=dict)
    extra_files: dict = field(default_factory=dict)
    extra_ports: tuple = ()
    timeout: float | None = None

    @property
    def names(self):
        return [p.name for p in self.props]

    def prop(self, name):
        return next(p for p in self.props if p.name == name)


def jr(status="PASS", error=None, **props):
    """JobResult; props given as PropResult or a status string."""
    return JobResult(status, {k: (v if isinstance(v, PropResult) else PropResult(v)) for k, v in props.items()},
                     error=error, dir="/job")


class Scripted:
    """Stands in for Engine.run.  `policy(call)` returns the JobResult.

    Every job is also checked to be closed: each bit a checker, lemma or
    helper cell reads must be driven inside the job or be one of its ports.
    An open bit is silently a free input in SymbiYosys, which is how the
    synchronized resets once went missing from every proof."""

    def __init__(self, engine, policy):
        self.engine, self.policy, self.calls = engine, policy, []
        self._lock = threading.Lock()

    def __call__(self, tag, spec, props, mode, depth, multiclock, engine=None, extra_cells=None, extra_files=None,
                 extra_ports=(), timeout=None):
        c = Call(tag, spec, list(props), mode, depth, multiclock, engine or self.engine.engine_str(),
                 dict(extra_cells or {}), dict(extra_files or {}), tuple(extra_ports), timeout)
        open_bits = self.open_bits(c)
        assert not open_bits, f"job {tag} reads undriven bits {open_bits}"
        with self._lock:
            self.calls.append(c)
        return self.policy(c)

    def open_bits(self, c):
        mod = self.engine._module(c.spec, c.extra_ports)
        mod["cells"].update(json.loads(json.dumps(c.extra_cells)))
        for p in c.props:
            mod["cells"][p.name] = instance(p)
        job = Netlist({"modules": {"t": mod}}, "t")
        return sorted({(name, b) for name in job.cells for _, bits in job.inputs(name) for b in bits
                       if not is_const(b) and b not in job.driver and b not in job.port_in})

    @property
    def tags(self):
        return [c.tag for c in self.calls]


def design():
    """cnt counts up while en && cnt < lim; lim is a register one stage away.
    A second, unrelated counter `other` runs on the same clock."""
    b = NB()
    clk, rst, en, load = (b.input(n)[0] for n in ("clk", "rst", "en", "load"))
    din = b.input("din", 4)
    lim = b.net("lim", b.new(4))
    b.ff(b.mux(lim, din, load), clk, q=lim, name="ff_lim")
    cnt = b.net("cnt", b.new(4))
    go = b.op("$and", A=[en], B=b.op("$lt", w=1, A=cnt, B=lim))
    b.ff(b.mux(b.mux(cnt, b.op("$add", A=cnt, B=const(1, 4)), go[0]), const(0, 4), rst), clk, q=cnt, name="ff_cnt")
    other = b.net("other", b.new(3))
    ok = b.op("$ne", w=1, A=other, B=const(7, 3))
    b.ff(b.mux(other, b.op("$add", A=other, B=const(1, 3)), ok[0]), clk, q=other, name="ff_other")
    nl = b.build()
    checks, lemmas = detect_counters(nl, 3)
    by = {c.target: c for c in checks}
    return nl, by, lemmas


class EngineCase(TempDirCase):
    def setUp(self):
        super().setUp()
        self.nl, self.checks, self.lemmas = design()
        self.rst = ResetBit("rst", self.nl.ports["rst"]["bits"][0], 1)

    def engine(self, policy=None, abc=False, resets=None, lemmas=None, assume_ports=None, assume_file=None, **opts):
        o = Options(**dict({"engine": "auto", "jobs": 1}, **opts))
        eng = Engine(self.nl, FakeTools(abc=abc), self.tmp, self.lemmas if lemmas is None else lemmas,
                     resets if resets is not None else Resets(self.rst, [], 1), o, assume_ports, assume_file)
        if policy is not None:
            eng.run = Scripted(eng, policy)
        return eng

    def state(self, eng, check, level=0, keep=()):
        s = St(chk=check, idx=0, level=level, keep=set(keep))
        s.res = Result(check=check, status=UNKNOWN)
        s.spec = eng._slice(check, sorted(s.keep), level)
        return s

    def trace(self, rel, values: dict, yw_inputs: dict | None = None):
        """Write a VCD (and optionally a witness) under the output dir."""
        p = os.path.join(self.tmp, rel)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        steps = len(next(iter(values.values())))
        head = "$var integer 32 t smt_step $end\n$scope module top $end\n"
        ids = {}
        for i, (name, vals) in enumerate(values.items()):
            ids[name] = f"n{i}"
            head += f"$var wire {len(vals[0])} n{i} {name} $end\n"
        body = ""
        for k in range(steps):
            body += f"#{k * 10}\nb{k:b} t\n" + "".join(f"b{v[k]} {ids[n]}\n" for n, v in values.items())
        with open(p, "w") as f:
            f.write(head + "$upscope $end\n$enddefinitions $end\n" + body + f"#{steps * 10}\n")
        if yw_inputs is not None:
            sigs = [{"path": [f"\\{n}"], "width": len(v[0]), "offset": 0, "init_only": False}
                    for n, v in yw_inputs.items()]
            nsteps = len(next(iter(yw_inputs.values())))
            stepbits = ["".join(yw_inputs[n][k] for n in reversed(list(yw_inputs))) for k in range(nsteps)]
            with open(os.path.splitext(p)[0] + ".yw", "w") as f:
                json.dump({"signals": sigs, "steps": [{"bits": s} for s in stepbits]}, f)
        return rel


class Plumbing(EngineCase):
    def test_default_options_choose_an_engine(self):
        for abc, want in ((True, "pdr"), (False, "smtbmc")):
            eng = Engine(self.nl, FakeTools(abc=abc), self.tmp, {}, Resets(), Options())
            self.assertEqual(eng.opts.engine, want)

    def test_engine_selection(self):
        self.assertEqual(self.engine(abc=True).opts.engine, "pdr")
        self.assertEqual(self.engine(abc=False).opts.engine, "smtbmc")
        self.assertEqual(self.engine(abc=True, engine="smtbmc").opts.engine, "smtbmc")

    def test_engine_strings(self):
        eng = self.engine(abc=True)
        self.assertEqual(eng.engine_str(), "abc --keep-going pdr")
        self.assertEqual(eng.smtbmc_str(), "smtbmc --keep-going z3")
        self.assertEqual(eng.smtbmc_str(keep_going=False), "smtbmc z3")
        self.assertEqual(eng.engine_str_cover(), "smtbmc z3")
        eng.opts.engine = "smtbmc"
        self.assertEqual((eng.engine_str(), eng.engine_str(False)), ("smtbmc --keep-going z3", "smtbmc z3"))
        eng.tools.solver = None
        self.assertEqual((eng.smtbmc_str(), eng.engine_str_cover()), ("smtbmc --keep-going", "smtbmc"))

    def test_old_job_directory_is_cleared(self):
        self.write("jobs/00001_old/x", "stale")
        self.engine()
        self.assertFalse(os.path.exists(os.path.join(self.tmp, "jobs")))

    def test_job_directories_are_unique_across_threads(self):
        eng = self.engine()
        with ThreadPoolExecutor(8) as ex:
            dirs = list(ex.map(lambda i: eng._dir(f"t{i % 3}"), range(400)))
        self.assertEqual(len(set(dirs)), 400)
        self.assertEqual(eng.stats["jobs"], 400)
        self.assertEqual(os.path.basename(eng._dir("x")), "00401_x")

    def test_reset_and_assumption_cells(self):
        eng = self.engine(resets=Resets(self.rst, [], 3, anytime=True), assume_ports={"en": "input", "nope": "input"})
        self.assertEqual(eng._keep_ports(), {"en", "nope", "rst"})
        spec = slice_spec(self.nl, self.checks["cnt"].roots(), ["ff_cnt"], 0)
        m = eng._module(spec)
        r = m["cells"]["fvl_reset"]
        self.assertEqual((r["type"], r["parameters"], r["connections"]),
                         ("fvl_reset_init", {"ACTIVE": 1, "CYCLES": 3, "ANYTIME": 1}, {"rst": [self.rst.bit]}))
        a = m["cells"]["fvl_assume"]
        self.assertEqual((a["type"], a["connections"]), ("fvlint_assumptions", {"en": self.nl.ports["en"]["bits"]}))
        self.assertIn("rst", m["ports"])
        self.assertIn("en", m["ports"])

    def test_no_reset_no_assumptions(self):
        eng = self.engine(resets=Resets())
        m = eng._module(slice_spec(self.nl, self.checks["cnt"].roots(), ["ff_cnt"], 0))
        self.assertNotIn("fvl_reset", m["cells"])
        self.assertNotIn("fvl_assume", m["cells"])
        self.assertEqual(eng._keep_ports(), set())
        self.assertEqual(eng._extra_files(), {})

    def test_reset_cycles(self):
        eng = self.engine(resets=Resets(self.rst, [], 0))
        self.assertEqual(eng._reset_cycles(None), 1)                     # at least one cycle
        eng.resets.cycles = 2
        single = slice_spec(self.nl, self.checks["cnt"].roots(), ["ff_cnt"], 0)
        self.assertEqual(eng._reset_cycles(single), 2)
        latch = ConeSpec(keep={"l"})
        self.nl.cells["l"] = {"type": "$dlatch", "parameters": {}, "attributes": {}, "port_directions": {},
                              "connections": {}}
        self.nl._kind["l"] = "state"
        self.assertEqual(eng._reset_cycles(latch.finish(self.nl)), 4)  # two global steps per clock cycle

    def test_assumption_file(self):
        p = self.write("a.sv", "module fvlint_assumptions; endmodule\n")
        self.assertEqual(self.engine(assume_file=p)._extra_files(),
                         {"fvl_assume.sv": "module fvlint_assumptions; endmodule\n"})

    def test_target_and_lemma_props(self):
        eng = self.engine(resets=Resets(self.rst, [ResetBit("r2", 99, 0, 1)], 2))
        c = self.checks["cnt"]
        s = self.state(eng, c)
        self.assertEqual(eng._target(s, "fvl_t0").mode, 0)
        p = eng._target(s, "fvl_t3", mode=2)
        self.assertEqual((p.name, p.checker, p.params, p.ports, p.mode), ("fvl_t3", c.checker, c.params, c.ports, 2))
        self.assertEqual(p.conds, c.conds + [(self.rst.bit, 0), (99, 1)])
        self.assertEqual(c.conds, self.checks["cnt"].conds)              # the check itself is not modified
        lemmas = {"ff_cnt": [Lemma("ff_cnt", "a", "fvl_range", {"W": 4, "LO": 0, "HI": 9, "SIGNED": 0}, {"v": [1]}),
                             Lemma("ff_cnt", "b", "fvl_rel", {"W": 4, "SIGNED": 0}, {"a": [1], "b": [2]})],
                  "ff_lim": [Lemma("ff_lim", "c", "fvl_range", {"W": 4, "LO": 0, "HI": 3, "SIGNED": 0}, {"v": [2]})]}
        eng.lemmas = lemmas
        props = eng._lemma_props(s.spec)                                # ff_lim is cut at level 0
        self.assertEqual([(p.name, p.checker) for p in props], [("fvl_l0", "fvl_range"), ("fvl_l1", "fvl_rel")])
        self.assertEqual(props[0].conds, [(self.rst.bit, 0), (99, 1)])
        full = slice_spec(self.nl, c.roots(), c.anchors, UNBOUNDED)
        self.assertEqual(len(eng._lemma_props(full)), 3)
        eng.lemmas = {}
        self.assertEqual(eng._lemma_bound(full), 0)


class RunJob(EngineCase):
    """Engine.run itself, with write_job/parse_job and a fake SymbiYosys."""

    def test_job_contents(self):
        eng = self.engine(abc=True, timeout=77)
        s = self.state(eng, self.checks["cnt"])
        r = eng.run("r0_pdr", s.spec, [eng._target(s, "fvl_t0")], "prove", 20, False)
        self.assertEqual(r.status, "PASS")
        self.assertEqual(r.get("fvl_t0").status, "unknown")             # PDR: no witness map, no verdicts
        sby, d, timeout = eng.tools.sby_calls[0]
        self.assertEqual((os.path.basename(d), timeout), ("00001_r0_pdr", 77))
        with open(sby) as f:
            text = f.read()
        self.assertIn("[engines]\nabc --keep-going pdr\n", text)
        self.assertIn("aigsmt z3", text)
        self.assertNotIn("depth", text)
        with open(os.path.join(d, "cone.json")) as f:
            cone = json.load(f)
        self.assertEqual(cone["creator"], "unit")                       # Yosys' creator string is passed on
        cells = cone["modules"][eng.nl.top]["cells"]
        self.assertIn("fvl_t0", cells)
        self.assertIn("fvl_reset", cells)

    def test_multiclock_doubles_depth_and_smtbmc_has_no_aigsmt(self):
        eng = self.engine(abc=False)
        s = self.state(eng, self.checks["cnt"])
        eng.run("x", s.spec, [eng._target(s, "fvl_t0")], "bmc", 9, True, timeout=5,
                extra_cells={"fvl_s0": {"type": "fvl_cover_true", "parameters": {}, "attributes": {},
                                        "port_directions": {}, "connections": {}}},
                extra_files={"fvl_stim.sv": "module fvl_stim; endmodule\n"}, extra_ports=["din"])
        sby, d, timeout = eng.tools.sby_calls[0]
        with open(sby) as f:
            text = f.read()
        self.assertIn("depth 18", text)
        self.assertIn("multiclock on", text)
        self.assertNotIn("aigsmt", text)
        self.assertEqual(timeout, 5)
        with open(os.path.join(d, "cone.json")) as f:
            mod = json.load(f)["modules"][eng.nl.top]
        self.assertIn("fvl_s0", mod["cells"])
        self.assertIn("din", mod["ports"])
        self.assertTrue(os.path.exists(os.path.join(d, "fvl_stim.sv")))


class Environment(EngineCase):
    def test_nothing_to_check_without_reset_or_assumptions(self):
        eng = self.engine(lambda c: self.fail("no job expected"), resets=Resets())
        self.assertIsNone(eng.environment_ok())

    def test_satisfiable(self):
        eng = self.engine(lambda c: jr("PASS", fvl_s0="fail"))
        self.assertIsNone(eng.environment_ok())
        (c,) = eng.run.calls
        self.assertEqual((c.tag, c.mode, c.depth, c.props, c.engine, c.multiclock),
                         ("env", "cover", 2 + 2, [], "smtbmc z3", False))
        self.assertEqual((c.extra_cells["fvl_s0"]["type"], c.extra_cells["fvl_s0"]["parameters"]),
                         ("fvl_cover_true", {"N": 2}))

    def test_probe_reaches_past_the_reset_window(self):
        # Reset held 3 cycles (steps 0-2): the probe must reach step 4, after
        # release, or an assumption contradicting the release goes unnoticed.
        for cycles, n in ((3, 4), (0, 2), (400, 254)):
            with self.subTest(cycles=cycles):
                eng = self.engine(lambda c: jr("PASS", fvl_s0="fail"), resets=Resets(self.rst, [], cycles))
                eng.environment_ok()
                c = eng.run.calls[0]
                self.assertEqual((c.extra_cells["fvl_s0"]["parameters"]["N"], c.depth), (n, n + 2))

    def test_unsatisfiable_or_broken(self):
        for result in (jr("FAIL"), jr("ERROR", error="assumptions are unsatisfiable")):
            with self.subTest(status=result.status):
                eng = self.engine(lambda c, r=result: r, assume_ports={"en": "input"})
                self.assertIn("unsatisfiable", eng.environment_ok())


class Packing(EngineCase):
    def states(self, eng, specs):
        out = []
        for i, (name, keep) in enumerate(specs):
            c = Check("k", name, f"a.v:{10 - i}", "")
            s = St(chk=c, idx=i)
            s.spec = ConeSpec(keep=set(keep)).finish(self.nl)
            out.append(s)
        return out

    def test_overlapping_cones_share_a_batch(self):
        eng = self.engine(batch_props=8)
        ss = self.states(eng, [("a", {"ff_cnt"}), ("b", {"ff_cnt", "ff_lim"}), ("c", {"ff_lim"}), ("d", {"ff_other"})])
        batches = eng._pack(ss)
        self.assertEqual(len(batches), 1)                               # small groups, same clock: one job
        self.assertEqual([s.chk.target for s in batches[0]], ["c", "b", "a", "d"])   # group by src, then next group

    def test_budgets(self):
        eng = self.engine()
        ss = self.states(eng, [("a", {"ff_cnt"}), ("b", {"ff_other"}), ("c", {"ff_lim"})])
        self.assertEqual([len(b) for b in eng._pack(ss, props=2)], [2, 1])
        self.assertEqual([len(b) for b in eng._pack(ss, cells=1)], [1, 1, 1])
        self.assertEqual([len(b) for b in eng._pack(ss, cells=2)], [2, 1])     # exactly at the budget, then over
        self.assertEqual([len(b) for b in eng._pack(ss, props=3)], [3])
        one = self.states(eng, [("a", {"ff_cnt"}), ("b", {"ff_cnt"}), ("c", {"ff_other"})])
        self.assertEqual([len(b) for b in eng._pack(one, props=2)], [2, 1])   # a group exactly at the budget
        # A cone exactly at the cell budget still takes a check whose cone it
        # already contains (stateless checks: no clocks, no shared registers).
        comb = sorted(c for c in self.nl.cells if self.nl.kind(c) == "comb")
        two = self.states(eng, [("a", comb[:3]), ("b", comb[:2])])
        self.assertEqual([len(b) for b in eng._pack(two, cells=3)], [2])

    def test_large_group_is_split(self):
        eng = self.engine()
        ss = self.states(eng, [(n, {"ff_cnt"}) for n in "abcde"])      # sources a.v:10 down to a.v:6
        self.assertEqual([[s.chk.target for s in b] for b in eng._pack(ss, props=2)], [["e", "d"], ["c", "b"], ["a"]])
        self.assertEqual([[s.chk.target for s in b] for b in eng._pack(ss, cells=0)], [list("edcba")])

    def test_different_clocks_are_not_mixed(self):
        b = NB()
        c1, c2 = b.input("clk")[0], b.input("clk2")[0]
        b.ff(b.input("x"), c1, name="r1")
        b.ff(b.input("y"), c2, name="r2")
        b.ff(b.input("z"), c1, name="r3", clk_pol=0)
        self.nl = b.build()
        eng = self.engine(resets=Resets())
        ss = self.states(eng, [("a", {"r1"}), ("b", {"r2"}), ("c", {"r3"}), ("d", set())])
        groups = sorted(sorted(s.chk.target for s in batch) for batch in eng._pack(ss))
        self.assertEqual(groups, [["a"], ["b"], ["c"], ["d"]])


class Houdini(EngineCase):
    def setUp(self):
        super().setUp()
        reg = "ff_cnt"
        self.my_lemmas = {reg: [Lemma(reg, f"l{i}", "fvl_range", {"W": 4, "LO": 0, "HI": 9 + i, "SIGNED": 0},
                                      {"v": self.nl.netnames["cnt"]["bits"]}) for i in range(3)]}

    def run_houdini(self, answers, targets=1, max_iter=None, **opts):
        answers = list(answers)
        eng = self.engine(lambda c: answers.pop(0) if answers else self.fail(f"unexpected job {c.tag}"),
                          lemmas=self.my_lemmas, **opts)
        sts = [self.state(eng, self.checks["cnt"]) for _ in range(targets)]
        for i, s in enumerate(sts):
            s.idx = i
        spec = sts[0].spec
        out = eng._houdini(0, spec, False, {f"fvl_t{i}": s for i, s in enumerate(sts)}, {}, max_iter=max_iter)
        return eng, out

    def test_proof_on_first_try(self):
        eng, out = self.run_houdini([jr("PASS")])
        self.assertEqual(out, {0: ("pass", None, "k-induction", 3, False)})
        (c,) = eng.run.calls
        self.assertEqual((c.tag, c.mode, c.depth, c.engine), ("r0_kind0", "prove", 20, "smtbmc --keep-going z3"))
        self.assertEqual(c.names, ["fvl_t0", "fvl_l0", "fvl_l1", "fvl_l2"])

    def test_false_lemmas_are_dropped(self):
        eng, out = self.run_houdini([jr("FAIL", fvl_l1=PropResult("fail", phase="basecase")),
                                     jr("FAIL", fvl_l0=PropResult("unknown", phase="induction")),
                                     jr("PASS")])
        self.assertEqual(out, {0: ("pass", None, "k-induction", 1, False)})
        self.assertEqual([c.names for c in eng.run.calls],
                         [["fvl_t0", "fvl_l0", "fvl_l1", "fvl_l2"], ["fvl_t0", "fvl_l0", "fvl_l2"],
                          ["fvl_t0", "fvl_l2"]])
        self.assertEqual(eng.run.tags, ["r0_kind0", "r0_kind1", "r0_kind2"])

    def test_target_failures(self):
        cex = PropResult("fail", trace="t.vcd", step=3, phase="basecase")
        eng, out = self.run_houdini([jr("FAIL", fvl_t1=cex, fvl_l2=PropResult("fail", phase="basecase")),
                                     jr("FAIL", fvl_t0=PropResult("unknown", phase="induction"))], targets=2)
        self.assertEqual(out[1], ("fail", cex, "k-induction", 0, False))
        self.assertEqual(out[0], ("unknown", "induction failed", "k-induction", 0, False))
        self.assertEqual(eng.run.calls[1].names, ["fvl_t0", "fvl_l0", "fvl_l1"])

    def test_lemma_dropped_before_target_is_given_up(self):
        # Both fail induction on the same trace.  Dropping a lemma only weakens
        # the hypothesis, so the target still fails in round 2: it is then
        # reported undecided, not proven.
        ind = PropResult("unknown", phase="induction")
        eng, out = self.run_houdini([jr("FAIL", fvl_l0=ind, fvl_t0=ind), jr("FAIL", fvl_t0=ind)])
        self.assertEqual(out[0], ("unknown", "induction failed", "k-induction", 0, False))
        self.assertEqual(eng.run.calls[1].names, ["fvl_t0", "fvl_l1", "fvl_l2"])

    def test_timeout_and_errors(self):
        _, out = self.run_houdini([jr("TIMEOUT")])
        self.assertEqual(out[0], ("unknown", "timeout", "k-induction", 0, False))
        _, out = self.run_houdini([jr("ERROR", error="assumptions are unsatisfiable")])
        self.assertEqual(out[0], ("error", "assumptions are unsatisfiable", "k-induction", 0, False))
        _, out = self.run_houdini([jr("ERROR")])
        self.assertEqual(out[0][0], "error")
        self.assertIn("tool error, see", out[0][1])

    def test_error_after_useful_verdicts_continues(self):
        _, out = self.run_houdini([jr("ERROR", fvl_l0=PropResult("fail", phase="basecase")), jr("PASS")])
        self.assertEqual(out[0][0], "pass")

    def test_no_information_and_iteration_limit(self):
        _, out = self.run_houdini([jr("FAIL")])
        self.assertEqual(out[0], ("unknown", "induction inconclusive", "k-induction", 0, False))
        lemma_fail = lambda n: jr("FAIL", **{n: PropResult("unknown", phase="induction")})   # noqa: E731
        eng, out = self.run_houdini([lemma_fail("fvl_l0"), lemma_fail("fvl_l1")], max_iter=2)
        self.assertEqual((out[0][1], len(eng.run.calls)), ("induction inconclusive", 2))
        eng, out = self.run_houdini([lemma_fail("fvl_l0")] * 2, max_houdini=2)
        self.assertEqual(len(eng.run.calls), 2)


class Portfolio(EngineCase):
    def test_smtbmc_engine_uses_k_induction(self):
        eng = self.engine(lambda c: jr("PASS"), abc=False)
        out = eng._prove_batch(0, [self.state(eng, self.checks["cnt"])])
        self.assertEqual(out[0][2], "k-induction")
        self.assertEqual(eng.run.tags, ["r0_kind0"])

    def test_pdr_after_a_short_k_induction_try(self):
        def policy(c):
            if c.tag.startswith("r0_kind"):
                return jr("FAIL", fvl_t0=PropResult("unknown", phase="induction"))
            return jr("FAIL", fvl_t1=PropResult("pass"), fvl_t2=PropResult("fail", trace="t.vcd", step=4))
        eng = self.engine(policy, abc=True)
        lemmas = {"ff_cnt": [Lemma("ff_cnt", "x", "fvl_range", {"W": 4, "LO": 0, "HI": 9, "SIGNED": 0},
                                   {"v": self.nl.netnames["cnt"]["bits"]})]}
        eng.lemmas = lemmas
        batch = [self.state(eng, self.checks["cnt"]) for _ in range(3)]
        for i, s in enumerate(batch):
            s.idx = i
        out = eng._prove_batch(0, batch)
        self.assertEqual(eng.run.tags[-1], "r0_pdr")
        self.assertLessEqual(len(eng.run.tags), 4)                      # at most 3 k-induction rounds
        pdr = eng.run.calls[-1]
        self.assertEqual((pdr.names, pdr.engine, pdr.mode),
                         (["fvl_t0", "fvl_t1", "fvl_t2"], "abc --keep-going pdr", "prove"))
        self.assertEqual({i: o[0] for i, o in out.items()}, {0: "unknown", 1: "pass", 2: "fail"})
        self.assertEqual(out[1], ("pass", PropResult("pass"), "PDR", 0, False))   # PDR uses no lemmas

    def test_k_induction_verdicts_are_final(self):
        def policy(c):
            if c.tag == "r0_kind0":
                return jr("FAIL", fvl_t1=PropResult("fail", trace="t.vcd", step=1, phase="basecase"))
            if c.tag == "r0_kind1":
                return jr("PASS")
            self.fail("PDR not needed")
        eng = self.engine(policy, abc=True)
        eng.lemmas = {"ff_cnt": [Lemma("ff_cnt", "x", "fvl_range", {"W": 4, "LO": 0, "HI": 9, "SIGNED": 0},
                                       {"v": self.nl.netnames["cnt"]["bits"]})]}
        batch = [self.state(eng, self.checks["cnt"]) for _ in range(2)]
        batch[1].idx = 1
        out = eng._prove_batch(0, batch)
        self.assertEqual((out[0][0], out[1][0]), ("pass", "fail"))

    def test_pdr_budget(self):
        eng = self.engine(lambda c: jr("UNKNOWN"), abc=True, lemmas={}, pdr_timeout=40, timeout=100, max_level=2)
        cut = self.state(eng, self.checks["cnt"], level=0)
        self.assertFalse(cut.spec.full)
        eng._prove_batch(0, [cut])
        last = self.state(eng, self.checks["cnt"], level=2)
        eng._prove_batch(1, [last])
        eng.opts.timeout = 25
        eng._prove_batch(2, [last])
        eng.opts.timeout = 100
        eng._prove_batch(3, [self.state(eng, self.checks["cnt"], level=0, keep={"ff_lim"})])   # full at level 0
        eng.opts.max_level = 0
        eng._prove_batch(4, [self.state(eng, self.checks["cnt"], level=0)])                   # cut, last level
        self.assertEqual([c.timeout for c in eng.run.calls], [5.0, 40, 25, 40, 40])

    def test_pdr_timeout_keeps_its_reason(self):
        eng = self.engine(lambda c: jr("TIMEOUT"), abc=True, lemmas={})
        self.assertEqual(eng._prove_batch(0, [self.state(eng, self.checks["cnt"])])[0],
                         ("unknown", "timeout", "PDR", 0, False))
        (r,) = self.engine(lambda c: jr("TIMEOUT"), abc=True, lemmas={}).prove_all([self.checks["cnt"]])
        self.assertEqual((r.status, r.detail), (UNKNOWN, "timeout on cone full"))

    def test_pdr_error_and_unknown(self):
        eng = self.engine(lambda c: jr("ERROR", error="boom"), abc=True, lemmas={})
        self.assertEqual(eng._prove_batch(0, [self.state(eng, self.checks["cnt"])])[0],
                         ("error", "boom", "PDR", 0, False))
        eng = self.engine(lambda c: jr("UNKNOWN", fvl_t0=PropResult("unknown")), abc=True, lemmas={})
        self.assertEqual(eng._prove_batch(0, [self.state(eng, self.checks["cnt"])])[0][0], "unknown")


class Transitions(EngineCase):
    def test_grow_through_levels_to_full(self):
        eng = self.engine(max_level=2)
        s = self.state(eng, self.checks["other"])
        s.spec = ConeSpec(cut={"x"}).finish(self.nl)
        seen = []
        while not s.done:
            seen.append(s.level)
            eng._grow(s)
        self.assertEqual(seen, [0, 1, 2, UNBOUNDED])
        self.assertEqual(s.res.detail, "not proven and no counterexample found")

    def test_grow_without_full_fallback(self):
        eng = self.engine(max_level=1, try_full=False)
        s = self.state(eng, self.checks["cnt"], level=1)
        s.spec = ConeSpec(cut={"x"}).finish(self.nl)
        eng._grow(s)
        self.assertTrue(s.done)
        self.assertEqual(s.level, 1)

    def test_full_cone_cannot_grow(self):
        eng = self.engine()
        s = self.state(eng, self.checks["cnt"], level=0, keep={"ff_lim"})
        self.assertTrue(s.spec.full)
        eng._grow(s)
        self.assertTrue(s.done)

    def test_labels(self):
        eng = self.engine()
        s = self.state(eng, self.checks["cnt"], level=0)
        self.assertEqual(s.label(), "0")
        s.keep = {"a", "b"}
        self.assertEqual(s.label(), "0+2r")
        s.level = UNBOUNDED
        self.assertEqual(s.label(), "full+2r")
        s.spec = ConeSpec().finish(self.nl)
        self.assertEqual(s.label(), "full")

    def test_advance_pass(self):
        eng = self.engine()
        s = self.state(eng, self.checks["cnt"], level=0)
        s.res.refinements = 2
        eng._advance(s, ("pass", None, "PDR", 2, True), [])
        self.assertEqual((s.res.status, s.res.level, s.res.full, s.res.lemmas_used, s.done),
                         (PROVEN, "0", False, 2, True))
        self.assertEqual(s.res.detail, "proven by PDR with 2 helper lemma(s) on cone 0 after 2 refinement(s) "
                                       "(multi-clock model)")
        self.assertIs(s.proven_spec, s.spec)
        self.assertEqual(s.res.history, [("0", "pass")])

    def test_advance_error(self):
        eng = self.engine()
        s = self.state(eng, self.checks["cnt"])
        eng._advance(s, ("error", "boom", "PDR", 0, False), [])
        self.assertEqual((s.res.status, s.res.detail, s.done), (ERROR, "boom", True))

    def test_advance_fail_on_full_and_cut_cones(self):
        eng = self.engine()
        cex = PropResult("fail", trace="t.vcd", step=5)
        full = self.state(eng, self.checks["cnt"], keep={"ff_lim"})
        eng._advance(full, ("fail", cex, "k-induction", 0, False), [])
        self.assertEqual((full.res.status, full.res.trace, full.res.step, full.res.full), (FAIL, "t.vcd", 5, True))
        self.assertIn("on the full design", full.res.detail)

        replays = []
        cut = self.state(eng, self.checks["cnt"])
        eng._advance(cut, ("fail", cex, "k-induction", 0, False), replays)
        self.assertEqual((replays, cut.cex, cut.done), ([(cut, cex, False)], ("t.vcd", 5, "0"), False))

    def test_cut_counterexample_without_replay(self):
        for kw, pr in (({"cegar": False}, PropResult("fail", trace="t.vcd", step=5)),
                       ({}, PropResult("fail", trace=None, step=5)),
                       ({"max_refinements": 0}, PropResult("fail", trace="t.vcd", step=5))):
            with self.subTest(kw=kw, trace=pr.trace):
                eng = self.engine(**kw)
                s = self.state(eng, self.checks["cnt"])
                replays = []
                eng._advance(s, ("fail", pr, "PDR", 0, False), replays)
                self.assertEqual((replays, s.level), ([], 1))          # grew instead

    def test_advance_undecided_without_a_reason(self):
        eng = self.engine()
        s = self.state(eng, self.checks["cnt"])
        eng._advance(s, ("unknown", PropResult("unknown"), "PDR", 0, False), [])
        self.assertEqual(s.res.detail, "undecided by PDR on cone 0")

    def test_advance_unknown(self):
        eng = self.engine()
        s = self.state(eng, self.checks["cnt"])
        eng._advance(s, ("unknown", "induction failed", "k-induction", 0, False), [])
        self.assertEqual((s.level, s.done, s.res.detail), (1, False, "induction failed on cone 0"))

    def test_finish_unknown_with_a_cut_counterexample(self):
        eng = self.engine()
        s = self.state(eng, self.checks["cnt"])
        s.cex = ("t.vcd", 4, "1+2r")
        eng._finish_unknown(s)
        self.assertEqual((s.res.trace, s.res.step, s.res.level, s.done), ("t.vcd", 4, "1+2r", True))
        self.assertIn("counterexample only on cone 1+2r", s.res.detail)
        s2 = self.state(eng, self.checks["cnt"])
        s2.res.status = PROVEN
        eng._finish_unknown(s2)
        self.assertEqual(s2.res.status, PROVEN)                         # decided results are left alone
        s3 = self.state(eng, self.checks["cnt"])
        s3.res.detail = "timeout"
        eng._finish_unknown(s3)
        self.assertEqual(s3.res.detail, "timeout")


class Replay(EngineCase):
    def cut_state(self, eng):
        s = self.state(eng, self.checks["cnt"])
        self.assertEqual(s.spec.cut, {"ff_lim"})
        return s

    def test_nothing_to_replay(self):
        eng = self.engine(lambda c: self.fail("no job"))
        tr = self.trace("tr/1/trace.vcd", {"cnt": ["0000"]})
        self.assertEqual(eng._replay(self.cut_state(eng), PropResult("fail", trace=tr, step=0)), ("none", None))

    def test_real_counterexample(self):
        hit = PropResult("fail", trace="tr/2/run/engine_0/trace0.vcd", step=3, phase="cover")
        eng = self.engine(lambda c: jr("PASS", fvl_t0=hit, fvl_s0="fail"))
        tr = self.trace("tr/1/trace.vcd", {"cnt": ["0000"] * 4},
                        {"rst": ["1", "0", "0", "0"], "en": ["0", "1", "1", "1"], "din": ["0000"] * 4})
        s = self.cut_state(eng)
        kind, payload = eng._replay(s, PropResult("fail", trace=tr, step=3))
        self.assertEqual((kind, payload), ("real", hit))
        (c,) = eng.run.calls
        self.assertEqual((c.tag, c.mode, c.depth, c.engine), ("replay", "cover", 5, "smtbmc z3"))
        self.assertTrue(c.spec.full)
        self.assertEqual((c.names, c.prop("fvl_t0").mode), (["fvl_t0"], 1))
        self.assertEqual(sorted(c.extra_ports), ["din", "en", "rst"])     # inputs found in the witness
        stim = c.extra_files["fvl_stim.sv"]
        self.assertIn("cover (n == 16'd3)", stim)
        cell = c.extra_cells["fvl_s0"]
        self.assertEqual(cell["type"], "fvl_stim")
        ports = [n for n in self.nl.ports if n in ("rst", "en", "din")]
        self.assertEqual([cell["connections"][f"p{i}"] for i in range(3)], [self.nl.ports[n]["bits"] for n in ports])

    def test_step_defaults_to_trace_length(self):
        eng = self.engine(lambda c: jr("PASS"))
        tr = self.trace("tr/1/trace.vcd", {"cnt": ["0000"] * 3}, {"en": ["1", "1", "1"]})
        eng._replay(self.cut_state(eng), PropResult("fail", trace=tr, step=None))
        self.assertEqual(eng.run.calls[0].depth, 2 + 2)

    def test_reached_stimulus_without_a_trace_is_spurious(self):
        eng = self.engine(lambda c: jr("PASS", fvl_s0=PropResult("fail", trace=None, step=0)))
        tr = self.trace("tr/1/trace.vcd", {"cnt": ["0000"]}, {"en": ["1"]})
        self.assertEqual(eng._replay(self.cut_state(eng), PropResult("fail", trace=tr, step=0)), ("spurious", set()))

    def test_witness_without_inputs(self):
        eng = self.engine(lambda c: jr("PASS"))
        tr = self.trace("tr/1/trace.vcd", {"cnt": ["0000"]})
        with open(os.path.join(self.tmp, "tr/1/trace.yw"), "w") as f:
            json.dump({"signals": [], "steps": [{"bits": ""}]}, f)
        eng._replay(self.cut_state(eng), PropResult("fail", trace=tr, step=None))
        self.assertEqual((eng.run.calls[0].depth, eng.run.calls[0].extra_ports), (2, ()))

    def test_unreachable_stimulus_is_spurious(self):
        eng = self.engine(lambda c: jr("PASS"))
        tr = self.trace("tr/1/trace.vcd", {"cnt": ["0000"]}, {"en": ["1"]})
        self.assertEqual(eng._replay(self.cut_state(eng), PropResult("fail", trace=tr, step=0)), ("spurious", set()))

    def test_divergent_cut_registers_are_restored(self):
        real = self.trace("tr/2/real.vcd", {"lim": ["0000", "0000", "0011"]})
        eng = self.engine(lambda c: jr("PASS", fvl_s0=PropResult("fail", trace=real, step=2, phase="cover")))
        tr = self.trace("tr/1/trace.vcd", {"lim": ["0000", "1111", "1111"]}, {"en": ["1", "1", "1"]})
        s = self.cut_state(eng)
        self.assertEqual(eng._replay(s, PropResult("fail", trace=tr, step=2)), ("spurious", {"ff_lim"}))
        s.keep = {"ff_lim"}
        self.assertEqual(eng._replay(s, PropResult("fail", trace=tr, step=2)), ("spurious", set()))

    def test_opaque_cut_cells_are_never_restored(self):
        # Blackboxes are cut forever; restoring one would change nothing.
        b = NB()
        clk = b.input("clk")[0]
        bb = b.net("bb_out", b.new(4))
        b.cell("pll", "vendor_pll", {"O": bb}, dirs={"O": "output"})
        q = b.net("q", b.new(4))
        b.ff(b.mux(q, b.op("$add", A=q, B=const(1, 4)), b.op("$lt", w=1, A=q, B=bb)[0]), clk, q=q, name="ff_q")
        self.nl = b.build()
        (chk,), _ = detect_counters(self.nl, 3)
        real = self.trace("tr/2/real.vcd", {"bb_out": ["0000", "0000"]})
        eng = self.engine(lambda c: jr("PASS", fvl_s0=PropResult("fail", trace=real, step=1, phase="cover")),
                          resets=Resets())
        tr = self.trace("tr/1/trace.vcd", {"bb_out": ["0000", "1111"]}, {"clk": ["0", "0"]})
        s = self.state(eng, chk, level=UNBOUNDED)
        self.assertEqual(s.spec.cut, {"pll"})
        self.assertEqual(eng._replay(s, PropResult("fail", trace=tr, step=1)), ("spurious", set()))

    def test_matching_traces_restore_nothing(self):
        real = self.trace("tr/2/real.vcd", {"lim": ["0000", "1111"]})
        eng = self.engine(lambda c: jr("PASS", fvl_s0=PropResult("fail", trace=real, step=1, phase="cover")))
        tr = self.trace("tr/1/trace.vcd", {"lim": ["0000", "1111"]}, {"en": ["1", "1"]})
        self.assertEqual(eng._replay(self.cut_state(eng), PropResult("fail", trace=tr, step=1)), ("spurious", set()))


class Scenarios(EngineCase):
    """prove_all from start to finish."""

    def test_proven_at_level_zero_with_vacuity_check(self):
        def policy(c):
            if c.tag == "r0_kind0":
                return jr("PASS")
            if c.tag == "vacuity_bmc":
                return jr("FAIL", fvl_v0="fail")
            self.fail(c.tag)
        eng = self.engine(policy, lemmas={})
        (r,) = eng.prove_all([self.checks["cnt"]])
        self.assertEqual((r.status, r.level, r.full, r.engine, r.vacuity, r.history),
                         (PROVEN, "0", False, "k-induction", "ok", [("0", "pass")]))
        self.assertEqual(r.detail, "proven by k-induction on cone 0")
        self.assertLess(r.seconds, 60)
        (r,) = self.engine(policy, lemmas={}).prove_all([self.checks["other"]])
        self.assertEqual((r.level, r.full), ("full", True))             # self-contained: no cuts at all
        self.assertEqual(eng.run.tags, ["r0_kind0", "vacuity_bmc"])
        v = eng.run.calls[1]
        self.assertEqual((v.names, v.prop("fvl_v0").mode, v.mode, v.depth), (["fvl_v0"], 2, "bmc", 20))
        self.assertGreaterEqual(r.seconds, 0)
        self.assertEqual(eng.stats["batches"], 1)

    def test_vacuous_proof(self):
        def policy(c):
            # (parse_job reports every property of a passing prove job as passed)
            return {"r0_kind0": jr("PASS"), "vacuity_bmc": jr("PASS"), "vacuity_kind": jr("PASS", fvl_v0="pass")}[c.tag]
        eng = self.engine(policy, lemmas={})
        (r,) = eng.prove_all([self.checks["other"]])
        self.assertEqual((r.status, r.vacuity), (VACUOUS, "vacuous"))
        self.assertIn("VACUOUS: the check's condition can never hold", r.detail)
        self.assertTrue(r.detail.startswith("proven by k-induction"))
        last = eng.run.calls[-1]
        self.assertEqual((last.tag, last.mode, last.prop("fvl_v0").mode), ("vacuity_kind", "prove", 2))

    def test_vacuity_undecided_and_disabled(self):
        def policy(c):
            return {"r0_kind0": jr("PASS"), "vacuity_bmc": jr("PASS"), "vacuity_kind": jr("UNKNOWN")}[c.tag]
        (r,) = self.engine(policy, lemmas={}).prove_all([self.checks["other"]])
        self.assertEqual((r.status, r.vacuity), (PROVEN, "unknown"))
        eng = self.engine(lambda c: jr("PASS"), lemmas={}, vacuity=False)
        (r,) = eng.prove_all([self.checks["other"]])
        self.assertEqual((r.status, r.vacuity, eng.run.tags), (PROVEN, None, ["r0_kind0"]))

    def test_vacuity_with_pdr_probes_the_proven_cone(self):
        def policy(c):
            if c.tag == "r0_pdr":
                return jr("PASS", fvl_t0="pass")
            if c.tag == "vacuity_bmc":
                return jr("PASS")
            return jr("FAIL", fvl_v0="fail")
        eng = self.engine(policy, abc=True, lemmas={}, pdr_timeout=7)
        (r,) = eng.prove_all([self.checks["other"]])
        self.assertEqual((r.status, r.vacuity), (PROVEN, "ok"))
        self.assertEqual(eng.run.tags, ["r0_pdr", "vacuity_bmc", "vacuity_pdr"])
        self.assertEqual(eng.run.calls[2].mode, "prove")
        self.assertEqual(eng.run.calls[2].timeout, 7)
        self.assertIs(eng.run.calls[1].spec, eng.run.calls[2].spec)

    def test_spurious_counterexample_is_refined_away(self):
        tr = self.trace("tr/s/trace.vcd", {"lim": ["0000", "1111"]}, {"en": ["1", "1"], "rst": ["1", "0"]})
        real = self.trace("tr/r/real.vcd", {"lim": ["0000", "0000"]})

        def policy(c):
            if c.tag == "r0_kind0":
                self.assertFalse(c.spec.full)
                return jr("FAIL", fvl_t0=PropResult("fail", trace=tr, step=1, phase="basecase"))
            if c.tag == "replay":
                return jr("PASS", fvl_s0=PropResult("fail", trace=real, step=1, phase="cover"))
            if c.tag == "r1_kind0":
                self.assertTrue(c.spec.full)                           # ff_lim restored, nothing else cut
                return jr("PASS")
            return jr("FAIL", fvl_v0="fail")
        eng = self.engine(policy, lemmas={})
        (r,) = eng.prove_all([self.checks["cnt"]])
        self.assertEqual((r.status, r.refinements, r.level), (PROVEN, 1, "full"))
        self.assertIn("after 1 refinement(s)", r.detail)
        self.assertEqual(r.history, [("0", "fail"), ("replay", "spurious, restored 1"), ("full", "pass")])
        self.assertEqual(eng.stats["replays"], 1)

    def test_confirmed_counterexample(self):
        tr = self.trace("tr/s/trace.vcd", {"lim": ["0000"]}, {"en": ["1"]})
        hit = PropResult("fail", trace="tr/r/hit.vcd", step=0, phase="cover")

        def policy(c):
            if c.tag == "r0_kind0":
                return jr("FAIL", fvl_t0=PropResult("fail", trace=tr, step=0, phase="basecase"))
            return jr("PASS", fvl_t0=hit, fvl_s0="fail")
        eng = self.engine(policy, lemmas={})
        (r,) = eng.prove_all([self.checks["cnt"]])
        self.assertEqual((r.status, r.trace, r.full, r.level), (FAIL, "tr/r/hit.vcd", True, "full (replayed)"))
        self.assertIn("confirmed by replay on the full cone", r.detail)
        self.assertEqual(r.history[-1], ("replay", "confirmed"))

    def test_replay_without_divergence_grows_the_cone(self):
        tr = self.trace("tr/s/trace.vcd", {"lim": ["0000"]}, {"en": ["1"]})

        def policy(c):
            if c.tag == "r0_kind0":
                return jr("FAIL", fvl_t0=PropResult("fail", trace=tr, step=0, phase="basecase"))
            if c.tag == "replay":
                return jr("PASS")                                       # stimulus not even reachable
            if c.tag == "r1_kind0":
                return jr("PASS")
            return jr("FAIL", fvl_v0="fail")
        eng = self.engine(policy, lemmas={})
        (r,) = eng.prove_all([self.checks["cnt"]])
        self.assertEqual((r.status, r.level, r.refinements), (PROVEN, "full", 1))
        self.assertEqual(r.history[1], ("replay", "spurious"))

    def test_refuted_and_unreplayable_counterexamples(self):
        # A refuted slice counterexample is forgotten (deep BMC still runs);
        # one that could not be replayed is kept as evidence.
        tr = self.trace("tr/s/trace.vcd", {"lim": ["0000"]}, {"en": ["1"]})
        no_witness = self.trace("tr/n/trace.vcd", {"lim": ["0000"]})
        for trace, replay, want_bmc, want_detail in ((tr, jr("PASS"), True, "no counterexample within 18"),
                                                     (no_witness, None, False, "counterexample only on cone 0")):
            def policy(c, trace=trace, replay=replay):
                if c.tag == "r0_kind0":
                    return jr("FAIL", fvl_t0=PropResult("fail", trace=trace, step=0, phase="basecase"))
                if c.tag == "replay":
                    return replay
                if c.tag == "deepbmc":
                    return jr("PASS")
                return jr("FAIL", fvl_t0=PropResult("unknown", phase="induction"))
            with self.subTest(trace=trace):
                eng = self.engine(policy, lemmas={}, depth=5, max_level=0, try_full=False)
                (r,) = eng.prove_all([self.checks["cnt"]])
                self.assertEqual((r.status, r.refinements, "deepbmc" in eng.run.tags), (UNKNOWN, 1, want_bmc))
                self.assertIn(("replay", "spurious" if want_bmc else "no trace"), r.history)
                self.assertIn(want_detail, r.detail)

    def test_undecided_everywhere_then_deep_bmc(self):
        def policy(c):
            if "kind" in c.tag:
                return jr("FAIL", fvl_t0=PropResult("unknown", phase="induction"))
            if c.tag == "deepbmc":
                return jr("PASS")
            self.fail(c.tag)
        eng = self.engine(policy, lemmas={}, depth=10, max_level=1)
        (r,) = eng.prove_all([self.checks["cnt"]])
        self.assertEqual(r.status, UNKNOWN)
        self.assertEqual(eng.run.tags, ["r0_kind0", "r1_kind0", "deepbmc"])
        bmc = eng.run.calls[-1]
        self.assertEqual((bmc.mode, bmc.depth, bmc.engine, bmc.names), ("bmc", 18, "smtbmc z3", ["fvl_t0"]))
        self.assertEqual(r.detail, "not proven; no counterexample within 18 cycles")
        self.assertEqual(r.history[-1], ("full", "bmc18:PASS"))

    def test_round_limit(self):
        eng = self.engine(lambda c: jr("FAIL", fvl_t0=PropResult("unknown", phase="induction")),
                          lemmas={}, max_rounds=1, depth=100)
        (r,) = eng.prove_all([self.checks["cnt"]])
        self.assertEqual((r.status, r.detail), (UNKNOWN, "induction failed on cone 0"))
        self.assertEqual(eng.run.tags, ["r0_kind0"])

    def test_round_limit_with_a_cut_counterexample(self):
        tr = self.trace("tr/s/trace.vcd", {"lim": ["0000"]}, {"en": ["1"]})
        eng = self.engine(lambda c: jr("FAIL", fvl_t0=PropResult("fail", trace=tr, step=0, phase="basecase")),
                          lemmas={}, cegar=False, max_rounds=1)
        (r,) = eng.prove_all([self.checks["cnt"]])
        self.assertEqual((r.status, r.trace), (UNKNOWN, tr))
        self.assertIn("counterexample only on cone 0", r.detail)

    def test_cut_counterexample_kept_when_nothing_decides(self):
        tr = self.trace("tr/s/trace.vcd", {"lim": ["0000"]}, {"en": ["1"]})

        def policy(c):
            if c.tag == "r0_kind0":
                return jr("FAIL", fvl_t0=PropResult("fail", trace=tr, step=0, phase="basecase"))
            return jr("TIMEOUT")
        eng = self.engine(policy, lemmas={}, cegar=False, max_level=0, try_full=False, depth=5)
        (r,) = eng.prove_all([self.checks["cnt"]])
        self.assertEqual((r.status, r.trace, r.step), (UNKNOWN, tr, 0))
        self.assertIn("counterexample only on cone 0", r.detail)
        self.assertNotIn("deepbmc", eng.run.tags)                       # a cut cex already exists

    def test_errors_end_the_check(self):
        eng = self.engine(lambda c: jr("ERROR", error="assumptions are unsatisfiable"), lemmas={})
        (r,) = eng.prove_all([self.checks["cnt"]])
        self.assertEqual((r.status, r.detail), (ERROR, "assumptions are unsatisfiable"))

    def test_many_checks_in_parallel(self):
        def policy(c):
            if "kind" in c.tag:
                return jr("PASS")
            return jr("FAIL", **{n: "fail" for n in c.names})
        checks = [self.checks["cnt"], self.checks["other"]] * 6
        eng = self.engine(policy, lemmas={}, jobs=4, batch_props=2)
        results = eng.prove_all(checks)
        self.assertEqual([r.check for r in results], checks)            # order preserved
        self.assertTrue(all(r.status == PROVEN and r.vacuity == "ok" for r in results))
        self.assertGreater(eng.stats["batches"], 1)


class SynchronizedReset(EngineCase):
    """Checks gated by a derived (synchronized) reset."""

    def setUp(self):
        super().setUp()
        b = NB()
        clk, rst, en = b.input("clk")[0], b.input("rst")[0], b.input("en")[0]
        r1 = b.ff([rst], clk, q=b.net("r1", b.new(1)), name="ff_r1")
        r2 = b.ff(r1, clk, q=b.net("r2", b.new(1)), name="ff_r2")
        for name in ("a", "b"):                                         # two unrelated counters, both reset by r2
            q = b.net(name, b.new(3))
            go = b.op("$and", A=[en], B=b.op("$ne", w=1, A=q, B=const(7, 3)))
            nxt = b.mux(q, b.op("$add", A=q, B=const(1, 3)), go[0])
            b.ff(b.mux(nxt, const(0, 3), r2[0]), clk, q=q, name=f"ff_{name}")
        self.nl = b.build()
        self.resets = discover(self.nl, None, False, None)
        self.assertEqual([r.name for r in self.resets.derived], ["r1", "r2"])
        checks, _ = detect_counters(self.nl, 3)
        self.checks = {c.target: c for c in checks}

    def test_every_job_contains_the_synchronizer(self):
        def policy(c):
            return jr("PASS") if c.mode == "prove" else jr("FAIL", **{n: "fail" for n in c.names})
        eng = self.engine(policy, resets=self.resets, lemmas={})
        results = eng.prove_all([self.checks["a"], self.checks["b"]])     # Scripted also checks closure
        self.assertEqual([r.status for r in results], [PROVEN, PROVEN])
        for c in eng.run.calls:
            self.assertLessEqual({"ff_r1", "ff_r2"}, c.spec.kept_state, c.tag)
            self.assertEqual(c.prop("fvl_t0" if c.mode == "prove" else "fvl_v0").conds[-3:],
                             [(r.bit, 1 - r.active) for r in self.resets.all()])

    def test_replay_cone_contains_the_synchronizer(self):
        tr = self.trace("tr/s/trace.vcd", {"a": ["000"]}, {"en": ["1"]})
        eng = self.engine(lambda c: jr("PASS"), resets=self.resets, lemmas={})
        s = self.state(eng, self.checks["a"])
        s.spec = eng._slice(s.chk, [], 0)
        eng._replay(s, PropResult("fail", trace=tr, step=0))
        self.assertLessEqual({"ff_r1", "ff_r2"}, eng.run.calls[0].spec.kept_state)

    def test_shared_synchronizer_does_not_merge_unrelated_checks(self):
        eng = self.engine(resets=self.resets, lemmas={})
        sts = []
        for i, t in enumerate("ab"):
            s = self.state(eng, self.checks[t])
            s.idx, s.spec = i, eng._slice(s.chk, [], 0)
            sts.append(s)
        self.assertEqual(len(sts[0].spec.kept_state), 3)
        self.assertEqual([len(b) for b in eng._pack(sts, cells=3)], [1, 1])


class DeepBmc(EngineCase):
    def unknown_state(self, eng, full=False, check="cnt"):
        s = self.state(eng, self.checks[check], keep={"ff_lim"} if full else ())
        s.res.detail = "induction failed"
        return s

    def test_skipped_when_shallow(self):
        eng = self.engine(lambda c: self.fail("no job"), lemmas={}, depth=20)
        eng._deep_bmc([self.unknown_state(eng)])                          # hint 18 <= depth 20
        eng.opts.depth = 18
        eng._deep_bmc([self.unknown_state(eng)])                          # nothing deeper to search

    def test_lemma_bounds_deepen_the_search(self):
        eng = self.engine(lambda c: jr("PASS"), depth=10, max_bmc_depth=40,
                          lemmas={"ff_cnt": [Lemma("ff_cnt", "x", "fvl_range", {}, {}, bound=30)]})
        eng._deep_bmc([self.unknown_state(eng)])
        self.assertEqual(eng.run.calls[0].depth, 34)
        self.assertEqual(eng._lemma_bound(self.unknown_state(eng).spec), 30)
        eng.lemmas["ff_cnt"][0].bound = 300
        eng.run.calls.clear()
        eng._deep_bmc([self.unknown_state(eng)])
        self.assertEqual(eng.run.calls[0].depth, 40)                      # capped

    def test_failure_on_the_full_cone(self):
        cex = PropResult("fail", trace="t.vcd", step=17)
        eng = self.engine(lambda c: jr("FAIL", fvl_t0=cex), lemmas={}, depth=5)
        s = self.unknown_state(eng, full=True)
        eng._deep_bmc([s])
        self.assertEqual((s.res.status, s.res.step, s.res.trace), (FAIL, 17, "t.vcd"))
        self.assertIn("on the full design", s.res.detail)

    def test_failure_on_a_cut_cone_is_replayed(self):
        tr = self.trace("tr/d/trace.vcd", {"lim": ["0000"]}, {"en": ["1"]})
        hit = PropResult("fail", trace="tr/r/hit.vcd", step=0, phase="cover")

        def policy(c):
            if c.tag == "deepbmc":
                return jr("FAIL", fvl_t0=PropResult("fail", trace=tr, step=0))
            return jr("PASS", fvl_t0=hit, fvl_s0="fail")
        eng = self.engine(policy, lemmas={}, depth=5)
        s = self.unknown_state(eng)
        eng._deep_bmc([s])
        self.assertEqual((s.res.status, s.res.trace), (FAIL, "tr/r/hit.vcd"))
        self.assertIn("confirmed by replay", s.res.detail)

        eng = self.engine(lambda c: jr("FAIL", fvl_t0=PropResult("fail", trace=tr, step=0)) if c.tag == "deepbmc"
                          else jr("PASS"), lemmas={}, depth=5)
        s = self.unknown_state(eng)
        eng._deep_bmc([s])
        self.assertEqual((s.res.status, s.res.trace), (UNKNOWN, tr))
        self.assertIn("not confirmed on the full cone", s.res.detail)

    def test_timeout(self):
        eng = self.engine(lambda c: jr("TIMEOUT"), lemmas={}, depth=5)
        s = self.unknown_state(eng)
        eng._deep_bmc([s])
        self.assertEqual(s.res.detail, "not proven; bounded search to 18 cycles timed out")

    def test_other_outcomes_keep_the_detail(self):
        eng = self.engine(lambda c: jr("ERROR"), lemmas={}, depth=5)
        s = self.unknown_state(eng)
        eng._deep_bmc([s])
        self.assertEqual(s.res.detail, "induction failed")


if __name__ == "__main__":
    unittest.main()
