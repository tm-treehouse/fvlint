# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Multi-property SymbiYosys jobs.

A job is a sliced module plus a set of named properties (checker instances).
`run_job` returns a verdict per property, using either

* ABC's PDR with --keep-going (`abc --keep-going pdr`): proves or refutes every
  property independently and finds inductive invariants by itself, or
* yosys-smtbmc with --keep-going: base-case failures are reported per
  property; induction reports one failure at a time, so callers iterate.
"""

from __future__ import annotations

import json
import os
import re
from dataclasses import dataclass, field
from importlib import resources

from .netlist import is_const

CHECKERS_V = resources.files("fvlint").joinpath("checkers.v").read_text()

PROP_RE = re.compile(r"fvl_([tlvs])(\d+)_")
_ASSERT_RE = re.compile(r"engine_\d+(?:\.(basecase|induction))?: .*Assert failed in \S+: \S+ \(([^)]*)\)")
_COVER_RE = re.compile(r"engine_\d+: .*Reached cover statement in step (\d+) at \S+: \S+ \(([^)]*)\)")
_TRACE_RE = re.compile(r"engine_\d+(?:\.(basecase|induction))?: .*Writing trace to VCD file: (\S+)")
_STEP_RE = re.compile(r"engine_\d+(?:\.basecase)?: .*Checking assertions in step (\d+)")
_SUMMARY_STEP_RE = re.compile(r"summary:\s+failed assertion (\S+) at \S+ step (\d+)")
_PDR_PROVED_RE = re.compile(r"Proved output (\d+)")
_PDR_FAILED_RE = re.compile(r"Output (\d+) (?:of miter \S+ )?was asserted in frame\s+(\d+)")


def prop_key(witness_name: str):
    m = PROP_RE.search(witness_name or "")
    return f"fvl_{m.group(1)}{m.group(2)}" if m else None


@dataclass
class Prop:
    name: str            # instance name: fvl_t<n> target, fvl_l<n> lemma, fvl_v<n> vacuity, fvl_s<n> stim
    checker: str
    params: dict
    ports: dict
    conds: list
    mode: int = 0        # 0 assert, 1 cover violation, 2 vacuity (assert !en)


@dataclass
class PropResult:
    status: str                      # "pass", "fail", "unknown"
    trace: str | None = None         # VCD path
    step: int | None = None
    phase: str | None = None         # "basecase" / "induction" / "cover"


@dataclass
class JobResult:
    status: str                      # SBY status: PASS FAIL UNKNOWN ERROR TIMEOUT
    props: dict = field(default_factory=dict)
    error: str | None = None
    dir: str = ""

    def get(self, name) -> PropResult:
        return self.props.get(name, PropResult("unknown"))


def _bin(v: int, w: int) -> str:
    return format(v & ((1 << w) - 1), f"0{w}b")


def instance(p: Prop) -> dict:
    conds = [(b, v) for b, v in p.conds if not is_const(b)]
    if not conds:
        conds = [("1", 1)]
    pol = 0
    for i, (_, v) in enumerate(conds):
        pol |= v << i
    params = {"NC": len(conds), "POL": _bin(pol, len(conds)), "MODE": p.mode}
    w = p.params.get("W", 1)
    for k, v in p.params.items():
        if k in ("LO", "HI"):
            params[k] = _bin(v, w)
        elif k == "SET":
            params[k] = _bin(v, p.params["N"] * w)
        else:
            params[k] = v
    conn = {"c": [b for b, _ in conds]}
    conn.update(p.ports)
    if p.checker == "fvl_range":
        e = p.ports.get("e", ["1"])
        conn["e"] = e
        params["NE"] = len(e)
    return {"hide_name": 0, "type": p.checker, "parameters": params, "attributes": {},
            "port_directions": {k: "input" for k in conn}, "connections": conn}


def write_job(d: str, top: str, module: dict, props: list, mode: str, depth: int, engine: str,
              multiclock: bool, timeout: float | None, creator: str, extra_files: dict | None = None,
              aigsmt: str | None = None):
    """Write cone.json, the checker library and run.sby into directory d."""
    os.makedirs(d, exist_ok=True)
    module = json.loads(json.dumps(module))
    for p in props:
        module["cells"][p.name] = instance(p)
    with open(os.path.join(d, "cone.json"), "w") as f:
        json.dump({"creator": creator, "modules": {top: module}}, f)
    files = {"fvl_checkers.v": CHECKERS_V}
    files.update(extra_files or {})
    for name, text in files.items():
        with open(os.path.join(d, name), "w") as f:
            f.write(text)
    reads = ["read_json cone.json"] + [f"read_verilog -formal -sv {n}" for n in files]
    opts = [f"mode {mode}"]
    if mode != "prove" or not engine.startswith("abc"):
        opts.append(f"depth {depth}")
    if multiclock:
        opts.append("multiclock on")
    if timeout:
        opts.append(f"timeout {int(timeout)}")
    if aigsmt:
        opts.append(f"aigsmt {aigsmt}")
    sby = os.path.join(d, "run.sby")
    with open(sby, "w") as f:
        f.write("[options]\n" + "\n".join(opts) + f"\n\n[engines]\n{engine}\n\n[script]\n")
        f.write("\n".join(reads))
        f.write(f"\nhierarchy -top {top}\nflatten\nprep -top {top}\n\n[files]\n")
        f.write("\n".join(["cone.json"] + list(files)) + "\n")
    return sby


def parse_job(d: str, outdir: str, rc: int, engine: str, mode: str, names) -> JobResult:
    wd = os.path.join(d, "run")
    log_path = os.path.join(wd, "logfile.txt")
    log = ""
    if os.path.exists(log_path):
        with open(log_path, errors="replace") as f:
            log = f.read()
    res = JobResult("TIMEOUT" if rc == -1 else "ERROR", dir=d)
    m = re.search(r"DONE \((\w+)", log)
    if m:
        res.status = m.group(1)
    if "Assumptions are unsatisfiable" in log:
        res.error = "assumptions are unsatisfiable (contradictory --assume file or reset model)"
    rel = lambda p: os.path.relpath(os.path.join(wd, p), outdir)  # noqa: E731

    if engine.startswith("abc"):
        _parse_pdr(wd, log, res, rel)
        return res
    pending = []
    last_step = None
    steps_by_name = {}
    for line in log.splitlines():
        s = _SUMMARY_STEP_RE.search(line)
        if s:
            k = prop_key(s.group(1))
            if k:
                steps_by_name[k] = int(s.group(2))
    for line in log.splitlines():
        sm = _STEP_RE.search(line)
        if sm:
            last_step = int(sm.group(1))
        am = _ASSERT_RE.search(line)
        if am:
            k = prop_key(am.group(2))
            if k and k not in res.props:
                phase = am.group(1) or "basecase"
                st = steps_by_name.get(k, last_step if phase == "basecase" else None)
                if phase == "induction":
                    res.props[k] = PropResult("unknown", phase="induction")
                else:
                    res.props[k] = PropResult("fail", step=st, phase="basecase")
                    pending.append(k)
            continue
        cm = _COVER_RE.search(line)
        if cm:
            k = prop_key(cm.group(2))
            if k and k not in res.props:
                res.props[k] = PropResult("fail", step=int(cm.group(1)), phase="cover")
                pending.append(k)
            continue
        tm = _TRACE_RE.search(line)
        if tm and tm.group(1) != "induction":
            for k in pending:
                res.props[k].trace = rel(tm.group(2))
            pending = []
    if res.status == "PASS" and mode == "prove":
        for n in names:
            res.props.setdefault(n, PropResult("pass"))
    return res


_SUMMARY_TRACE_RE = re.compile(r"summary: counterexample trace(?: \[\w+\])?: (\S+)")


def _parse_pdr(wd: str, log: str, res: JobResult, rel):
    """Per-property PDR verdicts.  Proved outputs are reported by index (the
    witness map gives the order); failed ones are taken from the summary,
    which pairs each trace with its assertion and real trace length (the
    'frame' in ABC's own message is not the trace length)."""
    ywa = os.path.join(wd, "model", "design_aiger.ywa")
    names = []
    if os.path.exists(ywa):
        with open(ywa) as f:
            names = [prop_key("".join(a)) for a in json.load(f).get("asserts", [])]
    for m in _PDR_PROVED_RE.finditer(log):
        i = int(m.group(1))
        if i < len(names) and names[i]:
            res.props[names[i]] = PropResult("pass")
    trace = None
    for line in log.splitlines():
        tm = _SUMMARY_TRACE_RE.search(line)
        if tm:
            trace = tm.group(1)
            continue
        sm = _SUMMARY_STEP_RE.search(line)
        if sm and trace:
            k = prop_key(sm.group(1))
            if k:
                path = os.path.join(os.path.dirname(wd), trace)
                res.props[k] = PropResult("fail", trace=rel(os.path.relpath(path, wd)),
                                          step=int(sm.group(2)), phase="basecase")
            trace = None
    # A failure ABC reported but whose trace could not be produced.
    for m in _PDR_FAILED_RE.finditer(log):
        i = int(m.group(1))
        if i < len(names) and names[i] and names[i] not in res.props:
            res.props[names[i]] = PropResult("fail", phase="basecase")
    if res.status == "PASS":
        for n in names:
            if n and n not in res.props:
                res.props[n] = PropResult("pass")


def yw_for(trace_vcd_abs: str) -> str | None:
    p = os.path.splitext(trace_vcd_abs)[0] + ".yw"
    return p if os.path.exists(p) else None
