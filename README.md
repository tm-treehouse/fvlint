<!--
SPDX-FileCopyrightText: 2026 The fvlint Authors
SPDX-License-Identifier: ISC
-->
# fvlint: lightweight formal lint for RTL

fvlint finds common hardware structures in your RTL (counters, `unique`/`parallel_case`
statements, variable part-selects, non-power-of-two memories, FSMs), generates a
small property for each one and proves it on **just the logic around that
structure**. You get lint-style output and lint-style speed, but each result
is a formal proof or a counterexample trace, not a pattern match.

It is built entirely on open-source tools: Yosys for elaboration,
SymbiYosys for running proofs, ABC's PDR or an SMT solver as the engine, and
optionally yosys-slang for SystemVerilog. The idea follows the "auto-formal"
or "formal lint" apps in commercial tools.

```
$ fvlint --frontend slang --top demo_top examples/demo/demo_top.sv
fvlint: 11 checks: 2 fail, 1 info, 7 proven, 1 waived

FAIL  fsm_unreachable:u_framer.st=3'b100  examples/demo/demo_top.sv:61  unreachable: decoded by the logic (case item / compare) but never assigned
FAIL  index_range:u_framer.hdr_byte       examples/demo/demo_top.sv:88  counterexample at step 1 on the full design (top-level inputs unconstrained)
INFO  fsm_summary:u_framer.st             examples/demo/demo_top.sv:61  4 reachable states from reset 3'b000
(7 proven and 1 waived checks hidden; use -v)
```

## What it checks

| Check | Structure | Property |
|---|---|---|
| `counter_overflow` / `counter_underflow` | register fed back through `+ c` / `- c` with a constant step (signed or unsigned) | the step is never taken when it would wrap (or overflow, for signed arithmetic) |
| `parallel_case` | `unique case`, `unique casez`, `(* parallel_case *)` | at most one item matches whenever the result is used |
| `full_case` | `unique` / full case with no default | some item always matches |
| `index_range` | variable part/bit select (`x[i*8 +: 8]`) | the offset stays inside the vector |
| `mem_addr` | memory whose depth is not a power of two | read/write addresses stay in range when enabled |
| `fsm_unreachable` | FSM state register | every assigned or decoded state is reachable from reset |
| `fsm_trap` (warning) | FSM state register | the FSM can get back to its reset state from every reachable state |

A counter whose increment condition doesn't depend on the counter itself (a
free-running timer, say) is reported as `INFO`, since its wrap-around looks
intentional. Logic disabled by a parameter (even through a wire) is
recognized as dead and isn't checked.

Check IDs are **structural**: they name the register, memory port or
destination signal, e.g. `parallel_case:u_arb.gnt` or
`counter_overflow:u_fifo.count`. Waivers therefore survive edits elsewhere in
the file.

## How it works

1. **Elaborate** once with Yosys (`proc; flatten`), keeping the structure
   intact, plus Yosys' FSM extraction on a saved copy of the design.
2. **Detect** structures in the JSON netlist, together with the *path
   condition* under which each value matters. For example, a `unique case`
   inside `if (valid)` is only checked when `valid` is set.
3. **Slice** a cone of influence around each check. Registers more than
   `level` stages away are **cut**: replaced by unconstrained values. Cutting
   only adds behaviour, so **a proof on a slice holds on the full design**.
   Cell types fvlint doesn't model (new Yosys cells, blackboxes) are always
   cut, which keeps that guarantee regardless of the Yosys version.
4. **Batch** checks whose cones overlap, plus small unrelated groups on the
   same clock, into one SymbiYosys job. A union of slices is still a sound
   over-approximation.
5. **Prove** with a portfolio:
   * If the cone has structure-derived *helper lemmas*, k-induction runs
     first. Lemmas are candidate invariants such as `count <= 999` from a
     compare constant, `count <= limit_q` from a compare with a register, or
     "the state register only holds reachable codes". They are filtered
     Houdini-style, so a false guess costs time but never soundness.
   * ABC's **PDR** (IC3), which finds its own invariants, handles the rest.
     It proves or refutes every property in the batch independently.
6. **Refine from counterexamples.** A counterexample on a check whose own
   cone has no cuts is a real `FAIL`. One on a cut slice is **replayed**:
   its top-level input sequence is pinned onto the check's full cone. If the
   violation reproduces, it's a `FAIL`. If not, only the cut registers whose
   values diverged are restored, and the check is retried.
7. **Clocks.** A cone with more than one clock net or edge, or with latches,
   is proven with SymbiYosys' multi-clock model, so slow/fast domain
   interactions aren't hidden by a single global clock.
8. **Deep search last.** Checks nothing decided get one bounded search with
   a structure-derived depth (e.g. 2^width for a counter).
9. **Vacuity.** For every proof fvlint also asks whether the check's
   condition can ever hold. If it can't, for example because an assumption
   rules it out, the result is `VACUOUS`, not `PROVEN`.

FSM checks need no solver. Yosys' FSM extraction treats control inputs as
free, so a state that is unreachable in the extracted graph is truly
unreachable. Transitions taken while a reset is asserted are ignored when
looking for trap states, so synchronous-reset FSMs work too.

### Reset model

The reset port is guessed from its name (`rst`, `rst_n`, `areset`,
`*_rst_ni`, …) or given with `--reset NAME[:LEVEL]`. fvlint also finds
**reset synchronizers**: registers that are forced by a reset and then
settle, like a two-flop synchronizer or an async-assert/sync-release bridge.
Reset is held at start-up long enough for the longest chain to propagate,
then released for good (`--reset-anytime` allows it to be re-asserted).
Checks are disabled while the reset or any synchronized copy of it is
active.

## Installing

fvlint is pure Python 3.11+ with no Python dependencies. It needs Yosys,
SymbiYosys and an SMT solver, and optionally `yosys-abc` for PDR:

* **Recommended:** [OSS CAD Suite](https://github.com/YosysHQ/oss-cad-suite-build)
  (native Yosys, SymbiYosys, yosys-slang, Yices, Bitwuzla, ABC).
* **Pip-only:** `pip install .[yowasp]` installs YoWASP's WebAssembly
  Yosys + SymbiYosys (with slang built in), Z3, and the `pyosys` wheel, whose
  `yosys-abc` binary fvlint uses for PDR. This works anywhere but is several
  times slower per proof job.

```
pip install .            # or: pip install .[yowasp]
fvlint --help
```

## Usage

```
fvlint --top TOP [files...] [-f files.f | -F files.f] [-I dir] [-D define] [-P param=value]
       [--frontend yosys|slang] [--reset NAME[:LEVEL] | --no-reset] [--reset-cycles N]
       [--reset-anytime] [--uninit zero|free] [--assume assumptions.sv]
       [--waivers waivers.txt] [--checks kind,...] [--engine auto|pdr|smtbmc]
       [--max-level N] [--no-cegar] [--no-vacuity] [-j N] [-o OUTDIR] [-v]
```

* `--frontend slang` is recommended for real SystemVerilog (packages,
  `import` in module headers, `.*`). Yosys' built-in parser handles a subset.
* `--uninit zero` (default) starts registers without a reset or `initial`
  value at 0, as on most FPGAs. Use `free` for arbitrary power-up values.
* The exit status is 1 on any `FAIL`, `ERROR` or `VACUOUS` result (adjust
  with `--fail-on fail|vacuous|unknown`) and 2 if fvlint couldn't run.
  `OUTDIR/results.json` and `OUTDIR/junit.xml` are written every run, and
  counterexamples come with a VCD trace.
* `--list` shows the detected checks without proving anything.
* File lists follow the simulator convention: relative paths in a list given
  with `-f` are relative to the current directory, with `-F` relative to the
  list file. Inside a list, `+incdir+`, `+define+`, `-I`, `-D`, nested
  `-f`/`-F` and `-v FILE` are understood; other simulator options are skipped.

### Results

| Status | Meaning |
|---|---|
| `PROVEN` | holds on a slice, hence on the whole design |
| `FAIL` | counterexample on the full cone, or a slice counterexample confirmed by replay, with unconstrained top-level inputs |
| `VACUOUS` | "proven", but the check's condition can never occur (over-constrained assumptions or dead logic) |
| `ERROR` | tool error, or an unsatisfiable environment (contradictory `--assume`) |
| `UNKNOWN` | neither proven nor refuted, or refuted only on a cut slice |
| `WARN` / `INFO` | FSM trap states, free-running counters, FSM summaries |
| `WAIVED` | matched a waiver |

### Triage: assumptions and waivers

Most `FAIL`s on block-level runs come from unconstrained top-level inputs.
Constrain them with a module named `fvlint_assumptions` whose ports are
top-level inputs, matched by name. Misspelled ports are rejected, and
contradictory assumptions are reported, never silently accepted:

```systemverilog
module fvlint_assumptions (input [1:0] lane);
  always @* assume (lane <= 2'd2);
endmodule
```

Waive what is intentional, either in a file of check-id globs or with an
attribute on the register or memory in the RTL:

```
# waivers.txt
fsm_unreachable:u_framer.st=*   # S_ERR is a defensive state kept on purpose
```
```systemverilog
(* fvlint_waive = "counter_overflow" *) logic [3:0] seq;   // wraps by design
```

```
$ fvlint --frontend slang --top demo_top examples/demo/demo_top.sv \
         --assume examples/demo/assumptions.sv --waivers examples/demo/waivers.txt
fvlint: 11 checks: 1 info, 8 proven, 2 waived
```

## Regression testing

`fvlint.regress` runs a **manifest** of designs with the expected status of
every check. It is how fvlint tests itself, and you can point it at your own
IP library the same way:

```toml
# my_ip.toml
[defaults]
budget_s = 120
engines = ["auto"]            # or ["pdr", "smtbmc"] to run each case per engine

[[case]]
name = "uart/tx"
filelist = "cores/uart/rtl.f"    # or files = [...]
top = "uart_tx"
args = ["--frontend", "slang", "--waivers", "{dir}/uart_waivers.txt"]
expect = { "counter_overflow:u_baud.cnt" = "PROVEN", "fsm_trap:u_tx.st={3'b101}" = "WAIVED" }
strict = true                    # any check not listed fails the case
```

```
python -m fvlint.regress my_ip.toml -j 4 --junit regress.xml
python -m fvlint.regress my_ip.toml --record     # print expectations for new cases
```

A case fails on a changed status, an unexpected `FAIL`/`ERROR`/`VACUOUS`, a
wrong exit code, or a blown time budget (`--budget-scale` for slow
machines). `--fuzz N` adds the soundness fuzzer (below).

fvlint's own suite:

| Suite | What it covers |
|---|---|
| `tests/unit/` | unit tests of every module's internals, no toolchain needed (about 1 s). Netlists are built by hand for exact edge cases and also loaded from committed Yosys snapshots of `tests/unit/data/rtl` for the shapes Yosys really produces; SymbiYosys log parsing is tested on lines in the formats of real runs, verbatim for the irregular ones (a step-0 failure has no step number). The scheduler is tested with a scripted solver (refinement, replay, batching, deep BMC, vacuity) that also checks every job it is handed is closed (no bit a checker reads is left undriven), external tools with stub executables. Kept honest by branch coverage and mutation testing (below). |
| `tests/regress/manifest.toml` | 57 case runs over the fixtures in `tests/fixtures`. Each fixture has clean structures and planted bugs, including a reproduction for every defect found in the design review: multi-clock false proofs, vacuous assumptions, parameter-disabled logic, synchronous-reset FSM traps, reset synchronizers, signed counters, register-bounded timers. Many cases run under both engines, plus a 200-counter throughput case. |
| `fvlint.fuzz` | soundness fuzzer: random designs (counters, registered guards, case statements, part-selects including narrow signed indices, memories, second clocks, falling edges, synchronized resets, and flops that look like reset stages but that data can set). Every `PROVEN`, `VACUOUS`, `FAIL` and unreachable-state verdict is re-checked by a plain bounded model check of the whole design, with no slicing, refinement, lemmas or PDR. Proofs are checked twice: under fvlint's own reset gating and under the oracle's (primary reset released plus a settle time, ignoring fvlint's derived resets); part-select bounds are computed by the oracle itself. |

```
python -m unittest discover -s tests/unit -t .   # unit tests (no toolchain)
python -m fvlint.regress -j 4 --fuzz 30          # end-to-end regression + fuzzer
python -m unittest -v tests.test_regress         # same, as unittest (FVLINT_FUZZ_SEEDS=...)
```

The unit tests are checked two ways. Branch coverage (`coverage run
--branch --source=src/fvlint -m unittest discover -s tests/unit -t .`) must
stay at 95% or more in CI. Mutation testing plants one small bug at a time in
a copy of the sources (a flipped comparison, an off-by-one constant, a negated
condition, a dropped `break`, a changed string) and reports every bug the unit
tests miss:

```
python tests/unit/mutation.py -j 4                 # all modules (~30 min)
python tests/unit/mutation.py detect cone          # selected modules
```

A surviving mutant is either a missing test, an equivalent change (one that
cannot alter behaviour), or an accepted one (a tuning constant, wording of a
message). Equivalent and accepted survivors are listed with their reason in
`tests/unit/mutation_baseline.json`; the report separates new survivors from
those, and `--strict` (used by the weekly CI run) fails on new ones.

The committed Yosys snapshots are regenerated with
`python tests/unit/data/make_snapshots.py` (`--check` reports drift).

`.github/workflows/ci.yml` runs lint, REUSE and the unit tests with coverage
on Python 3.11 to 3.13, then the full regression with the fuzzer on both the
pip toolchain and OSS CAD Suite. `mutation.yml` runs mutation testing weekly
or on demand.

## Limitations

* **Assumptions** can only constrain top-level inputs.
* **Vendor primitives** must be supplied as blackbox stubs (`--lib`). Their
  outputs are unconstrained.
* **Multi-clock model inputs:** under the multi-clock model, top-level inputs
  may change between any two clock edges. That is right for asynchronous
  inputs and pessimistic for synchronous ones.
* **k-induction and multiple clocks:** clocks may stall in the multi-clock
  model, so k-induction alone rarely proves invariants that span clock
  edges. Those end `UNKNOWN` with `--engine smtbmc`; PDR (the default when
  `yosys-abc` is available) proves them.
* **PDR on wide counters:** PDR is slow on counters with large limits. They
  fall back to k-induction with helper lemmas after `--pdr-timeout`.
* **Structure recognition** is heuristic. A counter is a register with a
  `+/- constant` feedback path through a mux tree. FSM detection relies on
  Yosys' `fsm_detect` (forced on for every non-port register). A `case`
  branch identical to `default` is merged away by the frontend.
* **The fuzzer's oracle is bounded** (24+ cycles), so it can't see a
  disagreement deeper than that. Designs are kept small so the bound covers
  them. Apart from part-select bounds and reset gating, it still uses
  fvlint's own check parameters and path conditions, so a mistake there would
  be shared.
* **Derived resets are recognised conservatively.** A register counts as a
  synchronized reset only if every way it can change other than through its D
  input (asynchronous reset, load, set or clear, synchronous reset, enable) is
  off or driven by a known reset. Otherwise checks are not gated on it, which
  can only add (true) failures inside unusual reset networks.
* **Every `FAIL` is real only relative to the block's inputs**, since those
  are unconstrained: read it as "true at this block boundary".

## License and prior art

fvlint is released under the [ISC license](LICENSE), the same license as
Yosys and SymbiYosys. Every file carries SPDX headers and the repository is
[REUSE](https://reuse.software)-compliant. External tools and their licenses
are listed in [THIRD_PARTY.md](THIRD_PARTY.md). fvlint invokes them as separate
programs and doesn't bundle them.

The approach of automatically extracting properties from RTL structures and
proving them formally is well established in commercial "auto-formal" and
"formal lint" tools. These were used as background reading only; no code or
text was taken from them:

* *Enabling high quality design sign off with Jasper structural and auto
  formal checks* (Intel), DVCon proceedings:
  <https://dvcon-proceedings.org/wp-content/uploads/Enabling-high-quality-design-sign-off-with-Jasper-structural-and-auto-formal-checks.pdf>
* *Taming Lint with Formal*, Semiconductor Engineering:
  <https://semiengineering.com/taming-lint-with-formal>

Copyright is covered by the license above. No patent review has been done;
EDA vendors hold patents in this area.
