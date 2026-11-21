# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Run one check: slice, prove, discard bad lemmas, grow the cone on failure."""

from __future__ import annotations

import json
import os
import re
import shutil
from dataclasses import dataclass, field
from importlib import resources

from .checks import ERROR, FAIL, PROVEN, UNKNOWN, Check, Result
from .cone import UNBOUNDED, slice_cone
from .netlist import Netlist, is_const
from .tools import Toolchain

CHECKERS_V = resources.files("fvlint").joinpath("checkers.v").read_text()

_FAIL_RE = re.compile(r"engine_\d+(?:\.(basecase|induction))?: .*Assert failed in \S+: \S+ \(([^)]*)\)")
_STEP_RE = re.compile(r"engine_\d+(?:\.basecase)?: .*Checking assertions in step (\d+)")
_LEM_RE = re.compile(r"fvl_lem_(\d+)_")


@dataclass
class Options:
    max_level: int = 3
    try_full: bool = True
    depth: int = 20
    max_bmc_depth: int = 200
    max_houdini: int = 12
    timeout: float = 120.0
    engine: str = "smtbmc"
    uninit: str = "zero"
    keep_runs: bool = True


@dataclass
class Reset:
    port: str
    bit: object
    active: int


@dataclass
class RunOutcome:
    status: str                    # PASS / FAIL / UNKNOWN / ERROR / TIMEOUT
    phase: str | None = None       # basecase / induction for failures
    failed: str | None = None      # witness name of the (first) failing assertion
    base_fails: set = field(default_factory=set)   # every assertion failing in basecase
    trace: str | None = None
    step: int | None = None
    log: str = ""


def _bin(v: int, w: int) -> str:
    return format(v & ((1 << w) - 1), f"0{w}b")


def _instance(checker: str, params: dict, ports: dict, conds: list) -> dict:
    conds = [(b, v) for b, v in conds if not is_const(b)]
    if not conds:
        conds = [("1", 1)]
    c_bits = [b for b, _ in conds]
    pol = 0
    for i, (_, v) in enumerate(conds):
        pol |= v << i
    p = {"NC": len(conds), "POL": _bin(pol, len(conds))}
    w = params.get("W", 1)
    for k, v in params.items():
        if k in ("LO", "HI"):
            p[k] = _bin(v, w)
        elif k == "SET":
            p[k] = _bin(v, params["N"] * w)
        else:
            p[k] = v
    conn = {"c": c_bits}
    conn.update(ports)
    if checker == "fvl_range":
        e = ports.get("e", ["1"])
        conn["e"] = e
        p["NE"] = len(e)
    return {"hide_name": 0, "type": checker, "parameters": p, "attributes": {},
            "port_directions": {k: "input" for k in conn}, "connections": conn}


class Prover:
    def __init__(self, nl: Netlist, tools: Toolchain, outdir: str, lemmas: dict,
                 reset: Reset | None, opts: Options, assume_ports: dict | None = None,
                 assume_file: str | None = None):
        self.nl, self.tools, self.outdir = nl, tools, outdir
        self.lemmas = lemmas
        self.reset = reset
        self.opts = opts
        self.assume_ports = assume_ports or {}
        self.assume_src = assume_file
        self.creator = nl.data.get("creator", "fvlint")

    # ----------------------------------------------------------- run helpers
    def _engine(self, keep_going=False) -> str:
        if self.opts.engine == "pdr":
            return "abc pdr"
        kg = "--keep-going " if keep_going else ""
        return f"smtbmc {kg}{self.tools.solver or ''}".strip()

    def _write_job(self, d: str, module: dict, mode: str, depth: int, engine: str) -> str:
        os.makedirs(d, exist_ok=True)
        top = self.nl.top
        with open(os.path.join(d, "cone.json"), "w") as f:
            json.dump({"creator": self.creator, "modules": {top: module}}, f)
        with open(os.path.join(d, "fvl_checkers.v"), "w") as f:
            f.write(CHECKERS_V)
        files = ["cone.json", "fvl_checkers.v"]
        reads = ["read_json cone.json", "read_verilog -formal fvl_checkers.v"]
        if self.assume_ports:
            shutil.copy(self.assume_src, os.path.join(d, "fvl_assume.sv"))
            files.append("fvl_assume.sv")
            reads.append("read_verilog -formal -sv fvl_assume.sv")
        sby = os.path.join(d, "run.sby")
        with open(sby, "w") as f:
            f.write(f"[options]\nmode {mode}\ndepth {depth}\n\n[engines]\n{engine}\n\n[script]\n")
            f.write("\n".join(reads))
            f.write(f"\nhierarchy -top {top}\nflatten\nprep -top {top}\n\n[files]\n")
            f.write("\n".join(files) + "\n")
        return sby

    def _run(self, d: str, module: dict, mode: str, depth: int, engine: str | None = None) -> RunOutcome:
        sby = self._write_job(d, module, mode, depth, engine or self._engine())
        rc = self.tools.run_sby(sby, d, self.opts.timeout)
        wd = os.path.join(d, "run")
        log_path = os.path.join(wd, "logfile.txt")
        log = open(log_path, errors="replace").read() if os.path.exists(log_path) else ""
        if rc == -1:
            return RunOutcome("TIMEOUT", log=log)
        status = "ERROR"
        m = re.search(r"DONE \((\w+)", log)
        if m:
            status = m.group(1)
        out = RunOutcome(status, log=log)
        last_step = None
        base_fail = ind_fail = None
        for line in log.splitlines():
            sm = _STEP_RE.search(line)
            if sm:
                last_step = int(sm.group(1))
            fm = _FAIL_RE.search(line)
            if not fm:
                continue
            phase = fm.group(1) or "basecase"   # bmc mode has no phase prefix
            if phase == "basecase":
                out.base_fails.add(fm.group(2))
            if phase == "basecase" and base_fail is None:
                base_fail = (fm.group(2), last_step)
            elif phase == "induction" and ind_fail is None:
                ind_fail = fm.group(2)
        if base_fail:
            out.phase, (out.failed, out.step) = "basecase", base_fail
        elif ind_fail:
            out.phase, out.failed = "induction", ind_fail
        for cand in ("engine_0/trace.vcd", "engine_0/trace0.vcd"):
            if os.path.exists(os.path.join(wd, cand)):
                out.trace = os.path.relpath(os.path.join(wd, cand), self.outdir)
                break
        return out

    # -------------------------------------------------------------- building
    def _module(self, chk: Check, level: int):
        roots = []
        for bits in chk.ports.values():
            roots += bits
        roots += [b for b, _ in chk.conds]
        keep_ports = set(self.assume_ports)
        if self.reset:
            keep_ports.add(self.reset.port)
        cone = slice_cone(self.nl, roots, chk.anchors, level, keep_ports, self.opts.uninit)
        return cone

    def _reset_conds(self):
        return [(self.reset.bit, 1 - self.reset.active)] if self.reset else []

    def _assemble(self, cone, chk: Check, lemmas: list) -> dict:
        mod = json.loads(json.dumps(cone.module))
        cells = mod["cells"]
        rc = self._reset_conds()
        cells["fvl_tgt"] = _instance(chk.checker, chk.params, chk.ports, chk.conds + rc)
        for i, lem in lemmas:
            cells[f"fvl_lem_{i}"] = _instance(lem.checker, lem.params, lem.ports, rc)
        if self.reset:
            cells["fvl_reset"] = {"hide_name": 0, "type": "fvl_reset_init",
                                  "parameters": {"ACTIVE": self.reset.active}, "attributes": {},
                                  "port_directions": {"rst": "input"},
                                  "connections": {"rst": [self.reset.bit]}}
        if self.assume_ports:
            conn = {p: mod["ports"][p]["bits"] for p in self.assume_ports if p in mod["ports"]}
            cells["fvl_assume"] = {"hide_name": 0, "type": "fvlint_assumptions", "parameters": {},
                                   "attributes": {}, "port_directions": {p: "input" for p in conn},
                                   "connections": conn}
        return mod

    def _cone_lemmas(self, cone) -> list:
        out = []
        for cell in sorted(cone.kept_state):
            out += self.lemmas.get(cell, [])
        return list(enumerate(out))

    # --------------------------------------------------------------- driver
    def run_check(self, chk: Check, slug: str) -> Result:
        res = Result(check=chk, status=UNKNOWN)
        base = os.path.join(self.outdir, "checks", slug)
        if os.path.isdir(base):
            shutil.rmtree(base)
        levels = list(range(self.opts.max_level + 1))
        if self.opts.try_full:
            levels.append(UNBOUNDED)
        prev_state = None
        last_cex = None
        last = None    # (cone, lvl_name, level) of the largest cone tried
        for level in levels:
            cone = self._module(chk, level)
            if prev_state is not None and cone.kept_state == prev_state:
                continue   # nothing new pulled in; same answer as before
            prev_state = set(cone.kept_state)
            lvl_name = "full" if cone.full else str(level)
            last = (cone, lvl_name, level)
            outcome, detail, used, trace, step = self._prove_level(chk, cone, base, lvl_name, res)
            res.history.append((lvl_name, outcome))
            if outcome == PROVEN:
                res.status, res.level, res.full, res.lemmas_used = PROVEN, level, cone.full, used
                prior = [h for h in res.history[:-1] if h[1] != PROVEN]
                res.detail = detail
                if prior:
                    res.detail += f"; smaller cones did not prove it (level {', '.join(h[0] for h in prior)})"
                return res
            if outcome == ERROR:
                res.status, res.detail = ERROR, detail
                return res
            if outcome == FAIL:
                last_cex = (level, trace, step, len(cone.cut_state))
                if cone.full:
                    return self._fail(res, level, trace, step)
            if cone.full:
                break

        # Not proven by any cone.  Only now spend time on a deep bounded search,
        # on the largest cone, for a counterexample induction could not reach.
        if last is not None and not (last_cex and last_cex[0] == last[2]):
            cone, lvl_name, level = last
            hint = max(self._depth_hint(cone), min(chk.depth_hint, self.opts.max_bmc_depth))
            if hint > self.opts.depth:
                d = os.path.join(base, f"L{lvl_name}_bmc")
                o = self._run(d, self._assemble(cone, chk, []), "bmc", hint)
                res.runs += 1
                res.history.append((lvl_name, f"bmc{hint}:{o.status}"))
                if o.status == "FAIL":
                    if cone.full:
                        return self._fail(res, level, o.trace, o.step)
                    last_cex = (level, o.trace, o.step, len(cone.cut_state))
                elif o.status == "PASS":
                    res.detail = f"not proven; no counterexample within {hint} cycles"
                elif o.status == "TIMEOUT":
                    res.detail = f"not proven; bounded search to {hint} cycles timed out"
        if last_cex:
            level, trace, step, ncut = last_cex
            res.status, res.level, res.trace, res.step = UNKNOWN, level, trace, step
            res.detail = (f"counterexample only with {ncut} register(s) cut at cone level {level}; "
                          "may be spurious (full design not reached or inconclusive)")
        elif not res.detail:
            res.detail = f"not proven; no counterexample within {self.opts.depth} cycles"
        return res

    def _fail(self, res, level, trace, step):
        res.status, res.level, res.full = FAIL, level, True
        res.trace, res.step = trace, step
        res.detail = f"counterexample at step {step} on the full design (top-level inputs unconstrained)"
        return res

    def _prove_level(self, chk, cone, base, lvl_name, res):
        """Houdini loop at one cone level.  Returns (outcome, detail, lemmas_used, trace, step)."""
        lemmas = self._cone_lemmas(cone) if self.opts.engine != "pdr" else []
        for it in range(self.opts.max_houdini):
            mod = self._assemble(cone, chk, lemmas)
            d = os.path.join(base, f"L{lvl_name}_{it}")
            o = self._run(d, mod, "prove", self.opts.depth, self._engine(keep_going=bool(lemmas)))
            res.runs += 1
            if o.status == "PASS":
                how = "PDR" if self.opts.engine == "pdr" else "k-induction"
                extra = f" with {len(lemmas)} helper lemma(s)" if lemmas else ""
                return PROVEN, f"proven by {how}{extra} at cone level {lvl_name}", len(lemmas), None, None
            if o.status == "TIMEOUT":
                return UNKNOWN, "timeout", 0, None, None
            bad_lemmas = {int(m.group(1)) for m in map(_LEM_RE.search, o.base_fails) if m}
            target_failed = any(not _LEM_RE.search(n) for n in o.base_fails)
            if target_failed:
                if not lemmas:
                    return FAIL, "counterexample", 0, o.trace, o.step
                # Re-run without lemmas for a trace that is about the target only.
                d = os.path.join(base, f"L{lvl_name}_cex")
                c = self._run(d, self._assemble(cone, chk, []), "bmc", self.opts.depth)
                res.runs += 1
                return FAIL, "counterexample", 0, c.trace, c.step
            if bad_lemmas:
                lemmas = [(i, lem) for i, lem in lemmas if i not in bad_lemmas]
                continue
            if o.phase == "induction":
                lm = _LEM_RE.search(o.failed or "")
                if lm:
                    idx = int(lm.group(1))
                    lemmas = [(i, lem) for i, lem in lemmas if i != idx]
                    continue
                break   # induction failed on the target itself
            return ERROR, f"unexpected solver result {o.status}, see {os.path.relpath(d, self.outdir)}", 0, None, None
        return UNKNOWN, f"not proven by k-induction to depth {self.opts.depth}", 0, None, None

    def _depth_hint(self, cone) -> int:
        bound = 0
        for cell in cone.kept_state:
            for lem in self.lemmas.get(cell, []):
                bound = max(bound, lem.bound)
        return min(bound + 4, self.opts.max_bmc_depth)
