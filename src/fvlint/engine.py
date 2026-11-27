# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""The proof scheduler.

Every check starts on a small slice of logic.  Each round:

1. slice every pending check at its current cone (level + restored cells),
2. pack checks into batches (union of slices; a union is still a sound
   over-approximation) and prove each batch in one SymbiYosys job,
3. PROVEN checks are done; a counterexample on a check whose own cone had
   no cuts is a real FAIL; a counterexample on a cut slice is replayed on
   the check's full cone: reproduced -> FAIL, spurious -> restore only the
   cut registers whose values diverged (counterexample-guided refinement);
   inconclusive checks get one more register stage.

Afterwards: a deep bounded search for checks k-induction could not decide,
and a vacuity probe (can the check's condition ever hold?) for every proof.
"""

from __future__ import annotations

import os
import shutil
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field

from .checks import ERROR, FAIL, PROVEN, UNKNOWN, VACUOUS, Check, Result, src_key
from .cone import UNBOUNDED, ConeSpec, build_module, clocks, merge_specs, needs_multiclock, slice_spec
from .elaborate import ASSUME_LIB, ASSUME_LIB_FILE
from .netlist import Netlist, is_const
from .replay import divergent, read_vcd, read_yw, stim_module
from .resets import Resets
from .sby import JobResult, Prop, parse_job, write_job, yw_for
from .tools import Toolchain


@dataclass
class Options:
    max_level: int = 3
    try_full: bool = True
    depth: int = 20
    max_bmc_depth: int = 200
    max_houdini: int = 12
    timeout: float = 120.0
    pdr_timeout: float = 30.0     # PDR gets this long; undecided checks go to k-induction
    engine: str = "auto"          # auto | pdr | smtbmc
    uninit: str = "zero"
    vacuity: bool = True
    cegar: bool = True
    batch_cells: int = 1500
    batch_props: int = 8
    max_rounds: int = 12
    max_refinements: int = 6
    jobs: int = 1


@dataclass
class St:
    chk: Check
    idx: int
    level: int = 0
    keep: set = field(default_factory=set)
    spec: ConeSpec | None = None
    res: Result | None = None
    done: bool = False
    cex: tuple | None = None        # (trace, step, label) on a cut cone
    proven_spec: ConeSpec | None = None
    t0: float = 0.0

    def label(self) -> str:
        if self.spec is not None and self.spec.full:
            return "full"
        base = "full" if self.level >= UNBOUNDED else str(self.level)
        return f"{base}+{len(self.keep)}r" if self.keep else base


class Engine:
    def __init__(self, nl: Netlist, tools: Toolchain, outdir: str, lemmas: dict, resets: Resets,
                 opts: Options, assume: dict | None = None, assume_file: str | None = None):
        self.nl, self.tools, self.outdir = nl, tools, outdir
        self.lemmas, self.resets, self.opts = lemmas, resets, opts
        # fvlint_assumptions port -> the design bits it reads (cli.bind_assumptions).
        self.assume = assume or {}
        self.assume_file = assume_file
        self.creator = nl.data.get("creator", "fvlint")
        if opts.engine == "auto":
            opts.engine = "pdr" if tools.abc else "smtbmc"
        self.jobdir = os.path.join(outdir, "jobs")
        if os.path.isdir(self.jobdir):
            shutil.rmtree(self.jobdir)
        self._n = 0
        self._lock = threading.Lock()
        self.stats = {"jobs": 0, "batches": 0, "replays": 0}
        # Every check is gated on the resets being inactive, so every slice
        # must contain them: the primary reset as a port, the derived ones
        # with their synchronizer flops (anchored, never cut into free inputs).
        self.reset_bits = [r.bit for r in resets.all()]
        self.reset_cells = sorted({nl.driver[r.bit].cell for r in resets.derived if r.bit in nl.driver})
        # The signals the assumptions read are in every slice too.  An
        # assumption on an internal net constrains the logic that drives it;
        # left out, the net would be free and a counterexample the assumption
        # rules out could pass for a real one.  Their logic is shared by every
        # slice, so it is no reason to batch checks together.
        self.assume_bits = [b for bits in self.assume.values() for b in bits if not is_const(b)]
        self.assume_cells = (slice_spec(nl, self.assume_bits, [], UNBOUNDED).kept_state
                             if self.assume_bits else set())

    def _slice(self, chk: Check, keep: list, level: int) -> ConeSpec:
        return slice_spec(self.nl, chk.roots() + self.reset_bits + self.assume_bits,
                          list(chk.anchors) + self.reset_cells + keep, level)

    # ------------------------------------------------------------ job plumbing
    def _dir(self, tag: str) -> str:
        with self._lock:
            self._n += 1
            self.stats["jobs"] += 1
            d = os.path.join(self.jobdir, f"{self._n:05d}_{tag}")
        if os.path.isdir(d):
            shutil.rmtree(d)
        return d

    def _keep_ports(self) -> set:
        # (The inputs the assumptions read are in every slice already: their bits are roots.)
        return {self.resets.primary.name} if self.resets.primary else set()

    def _module(self, spec: ConeSpec, extra_ports=()) -> dict:
        mod = build_module(self.nl, spec, self._keep_ports() | set(extra_ports), self.opts.uninit)
        cells = mod["cells"]
        r = self.resets.primary
        if r:
            cells["fvl_reset"] = {"hide_name": 0, "type": "fvl_reset_init",
                                  "parameters": {"ACTIVE": r.active, "CYCLES": self._reset_cycles(spec),
                                                 "ANYTIME": int(self.resets.anytime)},
                                  "attributes": {}, "port_directions": {"rst": "input"},
                                  "connections": {"rst": [r.bit]}}
        if self.assume:
            conn = {p: list(bits) for p, bits in self.assume.items()}
            cells["fvl_assume"] = {"hide_name": 0, "type": "fvlint_assumptions", "parameters": {},
                                   "attributes": {}, "port_directions": {p: "input" for p in conn},
                                   "connections": conn}
        return mod

    def _reset_cycles(self, spec) -> int:
        n = max(1, self.resets.cycles)
        # With multiclock on, a design clock cycle takes at least two global steps.
        return 2 * n if spec is not None and needs_multiclock(self.nl, spec) else n

    def _extra_files(self) -> dict:
        if not self.assume_file:
            return {}
        with open(self.assume_file) as f:
            return {ASSUME_LIB_FILE: ASSUME_LIB, "fvl_assume.sv": f.read()}

    def run(self, tag, spec, props, mode, depth, multiclock, engine=None, extra_cells=None,
            extra_files=None, extra_ports=(), timeout=None) -> JobResult:
        engine = engine or self.engine_str()
        timeout = timeout or self.opts.timeout
        d = self._dir(tag)
        module = self._module(spec, extra_ports)
        module["cells"].update(extra_cells or {})
        files = self._extra_files()
        files.update(extra_files or {})
        if multiclock:
            depth *= 2
        aigsmt = self.tools.solver if engine.startswith("abc") else None
        sby = write_job(d, self.nl.top, module, props, mode, depth, engine, multiclock,
                        timeout, self.creator, files, aigsmt)
        rc = self.tools.run_sby(sby, d, timeout)
        return parse_job(d, self.outdir, rc, engine, mode, [p.name for p in props])

    def engine_str(self, keep_going=True) -> str:
        if self.opts.engine == "pdr":
            return "abc --keep-going pdr"
        return self.smtbmc_str(keep_going)

    def smtbmc_str(self, keep_going=True) -> str:
        kg = "--keep-going " if keep_going else ""
        return f"smtbmc {kg}{self.tools.solver or ''}".strip()

    def _target(self, st: St, name: str, mode: int = 0) -> Prop:
        c = st.chk
        return Prop(name, c.checker, c.params, c.ports, c.conds + self.resets.inactive_conds(), mode)

    def _lemma_props(self, spec: ConeSpec) -> list:
        out = []
        for cell in sorted(spec.kept_state):
            for lem in self.lemmas.get(cell, []):
                out.append(Prop(f"fvl_l{len(out)}", lem.checker, lem.params, lem.ports,
                                self.resets.inactive_conds()))
        return out

    # ------------------------------------------------------------------ main
    def environment_ok(self) -> str | None:
        """Reset model + assumptions must be satisfiable, or every proof is vacuous."""
        if not self.assume and not self.resets.primary:
            return None
        # The logic behind assumed internal nets is part of it, on its own clocks.
        spec = slice_spec(self.nl, self.assume_bits + self.reset_bits, self.reset_cells, UNBOUNDED)
        mc = needs_multiclock(self.nl, spec)
        # Reach the first step after reset release (plus one): an assumption
        # that contradicts the release itself is only visible from there on.
        n = min(self._reset_cycles(spec) + 1, 254)
        cell = {"fvl_s0": {"hide_name": 0, "type": "fvl_cover_true", "parameters": {"N": n},
                           "attributes": {}, "port_directions": {}, "connections": {}}}
        r = self.run("env", spec, [], "cover", n + 2, mc, engine=self.engine_str_cover(), extra_cells=cell)
        if r.error or r.get("fvl_s0").status != "fail":
            return ("the environment is unsatisfiable: the --assume constraints (with the reset "
                    "model) contradict each other, so every proof would be vacuous")
        return None

    def engine_str_cover(self) -> str:
        return f"smtbmc {self.tools.solver or ''}".strip()

    def prove_all(self, checks: list) -> list:
        states = [St(chk=c, idx=i, res=Result(check=c, status=UNKNOWN), t0=time.time())
                  for i, c in enumerate(checks)]
        self._reach_first([s for s in states if s.chk.reach])
        for rnd in range(self.opts.max_rounds):
            active = [s for s in states if not s.done]
            if not active:
                break
            for s in active:
                s.spec = self._slice(s.chk, sorted(s.keep), s.level)
            batches = self._pack(active)
            self.stats["batches"] += len(batches)
            with ThreadPoolExecutor(max_workers=max(1, self.opts.jobs)) as ex:
                outcomes = list(ex.map(lambda b: self._prove_batch(rnd, b), batches))
            replays = []
            for batch, out in zip(batches, outcomes):
                for s in batch:
                    self._advance(s, out.get(s.idx, ("unknown", None, "?", 0, False)), replays)
            if replays:
                with ThreadPoolExecutor(max_workers=max(1, self.opts.jobs)) as ex:
                    verdicts = list(ex.map(lambda it: self._replay(it[0], it[1]), replays))
                for (s, pr, _), (kind, payload) in zip(replays, verdicts):
                    self.stats["replays"] += 1
                    if kind == "real":
                        s.res.history.append(("replay", "confirmed"))
                        self._fail(s, payload.trace, payload.step, "full (replayed)", replayed=True)
                    elif kind == "spurious" and payload:
                        s.res.refinements += 1
                        s.cex = None          # refuted: not evidence of anything any more
                        s.keep |= payload
                        s.res.history.append(("replay", f"spurious, restored {len(payload)}"))
                    else:
                        s.res.refinements += 1
                        if kind == "spurious":
                            s.cex = None
                        s.res.history.append(("replay", "spurious" if kind == "spurious" else "no trace"))
                        self._grow(s)
        for s in states:
            if not s.done:
                self._finish_unknown(s)
        self._deep_bmc([s for s in states if s.res.status == UNKNOWN and not s.cex])
        if self.opts.vacuity:
            # A reachability check's probe would be its own property again.
            self._vacuity([s for s in states if s.res.status == PROVEN and not s.chk.reach])
        for s in states:
            s.res.seconds = round(time.time() - s.t0, 2)
        return [s.res for s in states]

    # --------------------------------------------------------------- batching
    def _pack(self, states: list, props: int | None = None, cells: int | None = None) -> list:
        """Batch checks whose cones overlap (e.g. a counter's overflow and
        underflow checks, a memory's read and write ports, checks sharing an
        FSM).  Unrelated checks are not packed together: one bigger SMT
        problem costs more than the process start-up it would save."""
        parent = list(range(len(states)))

        def find(i):
            while parent[i] != i:
                parent[i] = parent[parent[i]]
                i = parent[i]
            return i
        owner = {}
        shared = set(self.reset_cells) | self.assume_cells     # in every slice: not a reason to batch together
        for i, s in enumerate(states):
            for cell in s.spec.kept_state - shared:
                j = owner.setdefault(cell, i)
                if j != i:
                    parent[find(i)] = find(j)
        groups = {}
        for i, s in enumerate(states):
            groups.setdefault(find(i), []).append(s)
        # Then pack whole groups (largest first) into batches under the
        # budget: small unrelated groups share a job, a group never splits
        # across jobs unless it alone exceeds the budget.
        props = props or self.opts.batch_props
        cells = cells or self.opts.batch_cells
        batches = []
        open_batches = []   # [states, keep, mc]
        for group in sorted(groups.values(), key=lambda g: -len(g)):
            group.sort(key=lambda s: (src_key(s.chk.src), s.chk.id))
            keep = set().union(*(s.spec.keep for s in group))
            # Clock signature: groups are only packed with groups on the same
            # clock(s), so packing never turns a single-clock problem into a
            # (slower) multi-clock one.
            mc = frozenset(set().union(*(clocks(self.nl, s.spec) for s in group)))
            if len(group) > props or len(keep) > cells:
                for i in range(0, len(group), props):
                    batches.append(group[i:i + props])
                continue
            for ob in open_batches:
                if ob[2] == mc and len(ob[0]) + len(group) <= props and len(ob[1] | keep) <= cells:
                    ob[0].extend(group)
                    ob[1] |= keep
                    break
            else:
                open_batches.append([list(group), keep, mc])
        batches += [ob[0] for ob in open_batches]
        return batches

    def _prove_batch(self, rnd: int, batch: list) -> dict:
        spec = merge_specs(self.nl, [s.spec for s in batch])
        mc = needs_multiclock(self.nl, spec)
        targets = {f"fvl_t{i}": s for i, s in enumerate(batch)}
        out = {}
        if self.opts.engine != "pdr":
            return self._houdini(rnd, spec, mc, targets, out)
        # Portfolio: with structure-derived lemma candidates (counters),
        # k-induction is usually fastest, so try it briefly first; PDR then
        # handles whatever is left and finds its own invariants.
        if self._lemma_props(spec):
            self._houdini(rnd, spec, mc, targets, out, max_iter=3)
            targets = {n: s for n, s in targets.items() if out.get(s.idx, ("unknown",))[0] == "unknown"}
            for s in targets.values():
                out.pop(s.idx, None)
            if not targets:
                return out
        props = [self._target(s, n) for n, s in targets.items()]
        # On a cut cone an undecided property usually needs more context, not
        # more solver time: keep PDR short there and spend the full budget on
        # full cones or the last level.
        last = spec.full or all(s.level >= min(self.opts.max_level, UNBOUNDED) for s in targets.values())
        budget = self.opts.pdr_timeout if last else min(self.opts.pdr_timeout, 5.0)
        r = self.run(f"r{rnd}_pdr", spec, props, "prove", self.opts.depth, mc,
                     timeout=min(budget, self.opts.timeout))
        if r.error:
            for s in targets.values():
                out[s.idx] = ("error", r.error, "PDR", 0, mc)
            return out
        for n, s in targets.items():
            pr = r.get(n)
            if pr.status in ("pass", "fail"):
                out[s.idx] = (pr.status, pr, "PDR", 0, mc)
            else:
                out[s.idx] = ("unknown", "timeout" if r.status == "TIMEOUT" else pr, "PDR", 0, mc)
        return out

    def _houdini(self, rnd, spec, mc, targets: dict, out: dict, max_iter: int | None = None) -> dict:
        alive = dict(targets)
        lemmas = self._lemma_props(spec)
        for it in range(max_iter or self.opts.max_houdini):
            if not alive:
                break
            props = [self._target(s, n) for n, s in alive.items()] + lemmas
            r = self.run(f"r{rnd}_kind{it}", spec, props, "prove", self.opts.depth, mc,
                         engine=self.smtbmc_str())
            if r.status == "PASS":
                for n, s in alive.items():
                    out[s.idx] = ("pass", None, "k-induction", len(lemmas), mc)
                return out
            if r.error or r.status == "TIMEOUT" or (r.status == "ERROR" and not r.props):
                why = r.error or ("timeout" if r.status == "TIMEOUT" else
                                  f"tool error, see {os.path.relpath(r.dir, self.outdir)}")
                for n, s in alive.items():
                    out[s.idx] = ("error" if r.error or r.status == "ERROR" else "unknown",
                                  why, "k-induction", 0, mc)
                return out
            progressed = False
            for n, pr in r.props.items():
                if pr.status == "fail" and pr.phase == "basecase":
                    if n in alive:
                        out[alive.pop(n).idx] = ("fail", pr, "k-induction", 0, mc)
                    else:
                        lemmas = [lm for lm in lemmas if lm.name != n]
                    progressed = True
            if progressed:
                continue
            ind = [n for n, pr in r.props.items() if pr.phase == "induction"]
            if not ind:
                break
            n = ind[0]
            if n in alive:
                out[alive.pop(n).idx] = ("unknown", "induction failed", "k-induction", 0, mc)
            else:
                lemmas = [lm for lm in lemmas if lm.name != n]
        for n, s in alive.items():
            out[s.idx] = ("unknown", "induction inconclusive", "k-induction", 0, mc)
        return out

    # ---------------------------------------------------------- transitions
    def _advance(self, s: St, outcome, replays: list):
        status, info, engine, nlem, mc = outcome
        res = s.res
        res.engine = engine
        label = s.label()
        res.history.append((label, status))
        if status == "pass":
            res.status, res.level, res.full, res.lemmas_used = PROVEN, label, s.spec.full, nlem
            how = f"proven by {engine}" + (f" with {nlem} helper lemma(s)" if nlem else "")
            how += f" on cone {label}"
            if res.refinements:
                how += f" after {res.refinements} refinement(s)"
            if mc:
                how += " (multi-clock model)"
            res.detail = how
            s.done = True
            s.proven_spec = s.spec
            return
        if status == "error":
            res.status, res.detail, s.done = ERROR, str(info), True
            return
        if status == "fail":
            pr = info
            if s.spec.full:
                self._fail(s, pr.trace, pr.step, label, replayed=False)
                return
            s.cex = (pr.trace, pr.step, label)
            if s.chk.reach and self.opts.try_full:
                # A slice takes a branch easily, through values its cut
                # registers can't really have; the first bounded search found
                # the near ones, so only the full cone's verdict is worth having.
                s.level, s.cex = UNBOUNDED, None
                return
            if self.opts.cegar and pr.trace and res.refinements < self.opts.max_refinements:
                replays.append((s, pr, mc))
            else:
                self._grow(s)
            return
        # Keep the latest reason (timeout, induction failure, ...) so an
        # UNKNOWN result says why; a deeper bounded search may replace it.
        res.detail = (f"{info} on cone {label}" if isinstance(info, str) and info
                      else f"undecided by {engine} on cone {label}")
        self._grow(s)

    def _grow(self, s: St):
        if s.spec is not None and s.spec.full:
            s.done = True
            self._finish_unknown(s)
            return
        if s.level >= UNBOUNDED:
            s.done = True
            self._finish_unknown(s)
        elif s.level >= self.opts.max_level:
            if self.opts.try_full:
                s.level = UNBOUNDED
            else:
                s.done = True
                self._finish_unknown(s)
        else:
            s.level += 1

    def _fail(self, s: St, trace, step, label, replayed: bool):
        res = s.res
        res.status, res.level, res.full, res.trace, res.step = FAIL, label, True, trace, step
        res.detail = (f"counterexample at step {step}, confirmed by replay on the full cone"
                      if replayed else
                      f"counterexample at step {step} on the full design (top-level inputs unconstrained)")
        s.done = True

    def _finish_unknown(self, s: St):
        res = s.res
        if res.status != UNKNOWN:
            return
        if s.cex:
            trace, step, label = s.cex
            res.trace, res.step, res.level = trace, step, label
            res.detail = (f"counterexample only on cone {label} (with cut registers); "
                          "replay on the full cone did not confirm it and no larger cone decided")
        elif not res.detail:
            res.detail = "not proven and no counterexample found"
        s.done = True

    # --------------------------------------------------------------- replay
    def _replay(self, s: St, pr):
        """Replay a slice counterexample on the check's full cone.
        Returns ("real", PropResult) | ("spurious", set of cells to restore)
        | ("none", None) when there is nothing to replay."""
        full = self._slice(s.chk, [], UNBOUNDED)
        trace_abs = os.path.join(self.outdir, pr.trace)
        yw = yw_for(trace_abs)
        if not yw:
            return ("none", None)
        sig = read_yw(yw)
        ports = [(n, len(p["bits"])) for n, p in self.nl.ports.items()
                 if p["direction"] == "input" and n in sig]
        step = pr.step if pr.step is not None else max((len(v) for v in sig.values()), default=1) - 1
        cell = {"fvl_s0": {"hide_name": 0, "type": "fvl_stim", "parameters": {}, "attributes": {},
                           "port_directions": {f"p{i}": "input" for i in range(len(ports))},
                           "connections": {f"p{i}": self.nl.ports[n]["bits"] for i, (n, _) in enumerate(ports)}}}
        r = self.run("replay", full, [self._target(s, "fvl_t0", mode=1)], "cover", step + 2,
                     needs_multiclock(self.nl, full), engine=self.engine_str_cover(), extra_cells=cell,
                     extra_files={"fvl_stim.sv": stim_module(ports, sig, step)},
                     extra_ports=[n for n, _ in ports])
        hit = r.get("fvl_t0")
        if hit.status == "fail":
            return ("real", hit)
        reach = r.get("fvl_s0")
        if reach.status != "fail" or not reach.trace:
            return ("spurious", set())
        cut_nets = {}
        for cell_name in s.spec.cut:
            if not self.nl.is_stateful(cell_name):
                continue
            nets = []
            for _, bits in self.nl.outputs(cell_name):
                n = self.nl.visible_name(bits)
                if n:
                    nets.append((n, len(bits)))
            cut_nets[cell_name] = nets
        slice_v = read_vcd(trace_abs)
        real_v = read_vcd(os.path.join(self.outdir, reach.trace))
        return ("spurious", divergent(slice_v, real_v, cut_nets, step) - s.keep)

    # ---------------------------------------------------------- reachability
    def _reach_first(self, states: list):
        """Reachability checks (dead branches) are mostly reached within a few
        cycles of reset.  One bounded search per batch on the checks' full
        cones finds those witnesses at once, and they are real: nothing is
        cut.  The rest go through the rounds like any check, where a proof
        on a slice means the condition never holds."""
        if not states:
            return
        for s in states:
            s.spec = self._slice(s.chk, [], UNBOUNDED)
        batches = self._pack(states, props=4 * self.opts.batch_props, cells=2 * self.opts.batch_cells)

        def one(batch):
            spec = merge_specs(self.nl, [s.spec for s in batch])
            mc = needs_multiclock(self.nl, spec)
            props = {f"fvl_t{i}": s for i, s in enumerate(batch)}
            r = self.run("reach_bmc", spec, [self._target(s, n) for n, s in props.items()], "bmc",
                         self.opts.depth, mc, engine=self.smtbmc_str())
            for n, s in props.items():
                pr = r.get(n)
                s.res.history.append(("full", f"bmc{self.opts.depth}:{pr.status if pr.status == 'fail' else r.status}"))
                if pr.status == "fail":
                    s.res.engine = "BMC"
                    self._fail(s, pr.trace, pr.step, "full", replayed=False)
        with ThreadPoolExecutor(max_workers=max(1, self.opts.jobs)) as ex:
            list(ex.map(one, batches))
        for s in states:
            s.spec = None

    # ------------------------------------------------------------ deep BMC
    def _deep_bmc(self, states: list):
        """k-induction gave up: search deeper for a counterexample, with a depth
        derived from the structure (e.g. 2^width for a counter)."""
        def one(s: St):
            spec = s.spec
            # A branch nothing decided: as deep as allowed (nothing in its
            # structure says how far away it is).
            hint = (self.opts.max_bmc_depth if s.chk.reach else
                    min(max(s.chk.depth_hint, self._lemma_bound(spec) + 4), self.opts.max_bmc_depth))
            if hint <= self.opts.depth:
                return
            r = self.run("deepbmc", spec, [self._target(s, "fvl_t0")], "bmc", hint,
                         needs_multiclock(self.nl, spec), engine=self.smtbmc_str(False))
            pr = r.get("fvl_t0")
            s.res.history.append((s.label(), f"bmc{hint}:{pr.status if pr.status == 'fail' else r.status}"))
            if pr.status == "fail":
                kind, payload = ("real", pr) if spec.full else self._replay(s, pr)
                if kind == "real":
                    s.res.status = UNKNOWN
                    self._fail(s, payload.trace, payload.step, s.label(), replayed=not spec.full)
                else:
                    s.res.trace, s.res.step = pr.trace, pr.step
                    s.res.detail = (f"counterexample at step {pr.step} only on cone {s.label()} "
                                    "(cut registers); not confirmed on the full cone")
            elif r.status == "PASS":
                s.res.detail = f"not proven; no counterexample within {hint} cycles"
            elif r.status == "TIMEOUT":
                s.res.detail = f"not proven; bounded search to {hint} cycles timed out"
        with ThreadPoolExecutor(max_workers=max(1, self.opts.jobs)) as ex:
            list(ex.map(one, states))

    def _lemma_bound(self, spec) -> int:
        return max((lem.bound for cell in spec.kept_state for lem in self.lemmas.get(cell, [])), default=0)

    # -------------------------------------------------------------- vacuity
    def _vacuity(self, states: list):
        """assert(!en) on the cone where each check was proven: if that holds,
        the check's condition can never be true and the proof means nothing."""
        for s in states:
            s.spec = s.proven_spec or s.spec
        # Vacuity probes are shallow and usually refuted at once: pack more.
        batches = self._pack(states, props=4 * self.opts.batch_props, cells=2 * self.opts.batch_cells)

        def one(batch):
            spec = merge_specs(self.nl, [s.spec for s in batch])
            mc = needs_multiclock(self.nl, spec)
            props = {f"fvl_v{i}": s for i, s in enumerate(batch)}
            # Phase 1: a bounded search usually reaches every condition at once.
            r = self.run("vacuity_bmc", spec, [self._target(s, n, mode=2) for n, s in props.items()],
                         "bmc", self.opts.depth, mc, engine=self.smtbmc_str())
            rest = {}
            for n, s in props.items():
                if r.get(n).status == "fail":
                    s.res.vacuity = "ok"
                else:
                    rest[n] = s
            if not rest:
                return
            # Phase 2: prove the rest unreachable (=> vacuous) or reach them deeper.
            plist = [self._target(s, n, mode=2) for n, s in rest.items()]
            if self.opts.engine == "pdr":
                r = self.run("vacuity_pdr", spec, plist, "prove", self.opts.depth, mc,
                             timeout=min(self.opts.pdr_timeout, self.opts.timeout))
            else:
                r = self.run("vacuity_kind", spec, plist, "prove", self.opts.depth, mc,
                             engine=self.smtbmc_str())
            for n, s in rest.items():
                pr = r.get(n)
                if pr.status == "pass":
                    s.res.vacuity = "vacuous"
                    s.res.status = VACUOUS
                    s.res.detail += ("; VACUOUS: the check's condition can never hold "
                                     "(over-constrained assumptions or dead logic)")
                elif pr.status == "fail":
                    s.res.vacuity = "ok"
                else:
                    s.res.vacuity = "unknown"
        with ThreadPoolExecutor(max_workers=max(1, self.opts.jobs)) as ex:
            list(ex.map(one, batches))
