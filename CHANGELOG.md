<!--
SPDX-FileCopyrightText: 2026 The fvlint Authors
SPDX-License-Identifier: ISC
-->

# Changelog

## 0.4.0

Fewer findings that need a waiver, and the integration work a project had
to do by hand, both from the PicoRV32 integration example: 12 of its 15
findings on the default configuration were patterns fvlint can settle
itself.

### Breaking changes

* **Check ids of case statements.** A case statement that assigns several
  signals is one check, named after all of them
  (`parallel_case:alu_wait,alu_wait_2,cpu_state,mem_do_rinst`), not one
  check per signal; statements that would share a name get the FSM state
  they sit in (`@cpu_state=8'b00010000`). Waivers and CI expectations for
  the old per-signal ids no longer match.
* **Checks settled without a proof** no longer fail: logic in an
  unreachable FSM state, counters that can't wrap within the horizon, and
  `full_case` pragmas that change nothing are `INFO`, which never fails a
  run, where they used to be `VACUOUS`, `FAIL` or proved.
* **`--horizon` is on by default** (2^60 cycles): counters that provably
  can't wrap sooner are `INFO` instead of checked.

Migration: run once with your waiver files. Every line reported as
matching no check needs the new id, which `--list` shows; with `--config`,
lines are reported after all configurations ran. `--horizon 0` restores
checking every counter.

### Fewer false or redundant findings

* **Parameter-disabled logic behind an expression.** `if (ENABLE_IRQ &&
  timer) timer <= timer - 1` with the parameter at 0 is a `$logic_and` with
  a constant input (elaboration runs no `opt_expr`), not a constant select,
  so fvlint checked the decrement (twice) and reported it `VACUOUS`. Path
  conditions are now evaluated through constant logic.
* **Checks in an unreachable FSM state** are `INFO` ("dead logic: applies
  only in state cpu_state=8'b00010000, which is unreachable"), pointing at
  the `fsm_unreachable` finding, instead of being proved `VACUOUS` one by
  one.
* **`full_case` on a signal first set to `'x`** is `INFO`: simulation and
  synthesis agree. Yosys' frontend replaces the value a blocking assignment
  gave the signal before a full_case statement with `'x`, so fvlint
  elaborates the design once more with its pragmas neutralised (attribute,
  `synopsys` comment, `unique`, `priority`) to see it. Before, both this
  harmless style and the real hazard were reported alike.
* **Counters that can't wrap within `--horizon`** (default 2^60 cycles) are
  `INFO`: a counter that only resets or loads constants and steps by
  constants needs at least its distance to the end divided by its step. One
  that steps both ways needs that for the first wrap of either kind (0 - 1
  is all ones, one increment from overflowing). A counter that ends
  `UNKNOWN` says how many cycles a wrap needs, as a `--horizon` value that
  can be pasted back.
* `results.json` gives each `INFO` result a machine-readable `reason`:
  `free_running`, `horizon`, `dead_state` or `full_case_x`.
* **Path conditions through fan-out.** Where a value fans out into several
  mux trees (nested if/else inside a case item), every branch is followed
  and the conditions all of them need are kept; before, the walk stopped
  there, with fewer conditions and no destination name.

### Check ids and case statements

* **One check per case statement**, named after the signals it assigns
  (`parallel_case:alu_wait,alu_wait_2,cpu_state,mem_do_rinst`), with the FSM
  state it sits in where two would share a name (`@cpu_state=8'b00010000`).
  The property is still proven for each signal; the result names the one
  that failed. Each instance of a module has its own checks. PicoRV32's 53
  per-signal checks become 20.
* **Names instead of line numbers**: a case result that reaches its register
  through fan-out, or through Yosys' intermediate nets (`$0\cpu_state`,
  `$0$memwr$\cpuregs`), is named after that register; the `file:line`
  fallback, which broke waivers when lines moved, is now rare.

### Ease of use

* **Project files**: `fvlint --config fvlint.toml [NAME...]` runs several
  configurations (tops, parameters, assumptions, waivers) into OUT/NAME and
  exits with the worst status. A waiver file that several configurations
  share is judged over all of them.
* **CI**: `--summary-md FILE` (Markdown summary) and `--github` (annotations
  on the source lines, and the summary in `$GITHUB_STEP_SUMMARY`), and a
  GitHub Action (`uses: tm-treehouse/fvlint@...`) that installs the OSS CAD
  Suite and fvlint, runs a project file and uploads the results. fvlint's
  own CI runs the Action from the checkout on a small project file.
* **Waivers**: lines that match no check are reported (stale after a rename
  or a fix), and `--recheck-waived` proves waived checks and names the
  waivers no longer needed. A waiver on a case statement's id covers it.
* Paths up to two directories above the current one are shown relative, and
  a current directory reached through a symbolic link (macOS's `/tmp`) no
  longer makes every path absolute.

### Result parsing

* SymbiYosys's log summary also stops after five properties per trace
  ("and 2 further assertions"); those are now read from the status file
  too. When several assertions failed in one PDR trace, only the first got
  its trace and step.

### Tests

* The soundness fuzzer's oracle also checks the verdicts that skip a proof.
  The generator adds a case statement inside a state of its FSM (dead when
  the state is unreachable), counters that step both ways, `full_case` on a
  signal set to `'x` and on one set to a value, and counters behind a
  parameter guard, each from its own random stream so existing seeds keep
  their designs; about half the seeds run with a small `--horizon`. The
  oracle checks dead logic like `VACUOUS`, a horizon claim with a bounded
  model check exactly as deep as the claim, a harmless `full_case` against
  what the generator wrote, and that live guarded logic has a check. With
  the up/down wrap bound fixed in this release planted back, it reports the
  false horizon claims (in 2 of 50 seeds); with the fix, 50 seeds are clean.
* The mutation runner runs each test suite in a directory of its own:
  parallel workers shared the checkout, and a test writing a relative path
  gave 36 false "killed" verdicts under `-j 8`.
* The unit tests pass on macOS (temporary directories through `/private`).
* Regression fixtures for each pattern above (`tests/fixtures/review.sv`),
  a module instantiated twice, and a 64-bit up/down counter.

## 0.3.2

Fixes for false findings and a lost FSM pass, found by running fvlint on
PicoRV32 for the integration example, and two fixes for SymbiYosys's
cut-short summaries, found by CI.

### False findings (0.3.1 reported FAIL for a design without the problem)

* **FSM reset state.** For a register without an asynchronous reset, Yosys
  guesses the FSM's reset state "from the mux tree", and an assignment after
  the reset branch (`if (!resetn) st <= FETCH; else case ...` followed by
  `if (err) st <= TRAP;`) makes it guess the overriding state. fvlint took
  the guess, so PicoRV32's `cpu_state` was reported as reaching only TRAP
  and six of its states as unreachable. The start states now come from the
  transitions that can fire while the reset is asserted; inputs computed
  from the reset (`!resetn || trap`) are evaluated with the reset applied,
  and the start set errs on the large side. Yosys' own reset state is used
  only when the state register has an asynchronous reset. An FSM whose
  start set has several states reports them as `{2'b00, 2'b11}`.
* **full_case on a case with a default item.** Yosys marks every case
  statement that has a default item `full_case`; when the default leaves a
  signal at an `'x` assigned before the case, the result looked like a
  `full_case` pragma, and fvlint reported "no item matches" whenever the
  default was taken. The source's pragma is now told apart at elaboration
  (renamed to `fvlint_full_case`), and only cases that carry it are checked.

### FSM extraction

* Yosys' `fsm_extract` can stop with an internal assertion on one register
  (PicoRV32's `irq_state` with `ENABLE_IRQ=1`), and fvlint then skipped every
  FSM check. The FSM pass now runs again on the saved design without that
  register (up to three registers), and the warning names them.

### Result parsing

* When more than five properties of one SymbiYosys job fail, the log's
  summary stops after five; the rest are now read from the job's status
  file, so their counterexample traces are no longer missing.
* The fuzzer's oracle now reads SBY's full summary file as well as its log.
  The log's summary lists only the first five counterexample traces, so a
  failure the oracle's BMC found in a later trace went unread, and a correct
  FAIL from fvlint was reported as a disagreement (seed 13 under the OSS CAD
  Suite, whose yices run writes one trace per failed assertion).

### Fuzzer

* Designs now include a small state machine, sometimes with an assignment
  after the reset branch; with 0.3.1's FSM code the oracle reports the false
  "unreachable" finding above.

## 0.3.1

Test infrastructure only; fvlint's own behaviour is unchanged.

* The soundness fuzzer's oracle is now independent of fvlint for every check
  kind. The generator writes down, as plain Verilog, when each construct it
  builds is active and when it goes wrong; the oracle adds those monitors to
  its own copy of the design and runs a plain bounded model check with
  SymbiYosys. It no longer reads fvlint's netlist, check parameters, path
  conditions or discovered resets. With an off-by-one planted in fvlint's
  counter limits, or a path condition dropped, the new oracle reports the
  wrong verdicts; the old one agreed with them.
* The scheduler is also tested against a fake solver that answers from a
  per-property truth table, over many random mixes, so its answers cannot
  contradict each other.
* The mutation-testing baseline names each accepted survivor by its
  enclosing function, so edits elsewhere no longer shift an entry onto a
  different line. Entries whose code changed fail the ordinary unit tests,
  and `--strict` also fails on entries that are now killed.
* CI: current major versions of the GitHub actions, the OSS CAD Suite build
  pinned to one from just after Yosys 0.71, `pyosys` pinned with
  `yowasp-yosys`, and job time limits.

## 0.3.0

Unit tests for the internals (`tests/unit/`), checked by branch coverage and
mutation testing, and an independent review of them. Writing and reviewing
the tests found the following defects in 0.2.0.

### Soundness (0.2.0 could report PROVEN for a check that can fail)

* **Narrow signed part-select index.** The upper bound of an `index_range`
  check was truncated to the index width, so a 4-bit signed index into a
  12-bit vector accepted `-8` as offset 8. Fixture `index/idx_signed_bug`.
* **Registers that data can force were taken for resets.** A flop that copies
  a reset synchronizer stage but that a data input can also set
  asynchronously (or load, clear, reset synchronously, or hold through an
  enable) was treated as a derived reset, switching every check off whenever
  that input was high. Fixture `reset/rst_data_set`.
* **Mux traversal dropped paths** beyond its path and depth limits, so reset
  discovery could miss a hold path in a large case statement and take the
  register for a reset.

### Missed failures

* With the smtbmc engine, the basecase and induction tasks log concurrently.
  When the induction task finished first, the basecase counterexample of the
  same check was ignored and the check came out UNKNOWN ("induction failed")
  instead of FAIL; the step listed for an induction trace in the summary
  could also replace the counterexample's step. Timing-dependent; found by
  the regression (`index/idx_signed_bug`, smtbmc).

### False failures and diagnostics

* Derived (synchronized) resets were left out of every proof slice, so the
  solver treated them as free inputs: checks fired inside the synchronizer
  window and the counterexample was "confirmed by replay". Fixture
  `reset/rst_sync_window`.
* A PDR failure at step 0 lost its trace and step ("counterexample at step
  None"): SymbiYosys leaves "step 0" out of its summary. Plural
  `steps a, b` summaries are understood too.
* The environment check (`--assume` against the reset model) looked at step 2,
  inside the reset window when reset is held 2+ cycles, so a contradictory
  assumption went unnoticed with `--no-vacuity`.
* UNKNOWN results keep their reason (`timeout on cone 1`, `induction failed
  on cone full`) instead of a generic message, for k-induction and PDR.
* An unclocked memory write port is treated as level-sensitive (multi-clock
  model), like a latch.

### Behaviour changes

* `-f` file lists follow the simulator convention: relative paths are
  relative to the current directory. New `-F` for paths relative to the list
  file (the 0.2.0 behaviour of `-f`). Inside lists, `-y DIR` and other
  option arguments are no longer read as source files.
* Check ids for part of a vector name the bit range (`q[3:2]`) instead of
  only its width (`q[2b]`), so two slices of one vector no longer collide.
* Waiver files: `#` starts a comment only at the start of a line or after
  whitespace, and `[`/`]` are literal, so every reported id (`gnt#1`,
  `q[3:2]`, FSM codes) can be waived as written.
* Counter lemma candidates are taken in the counter's own signed or unsigned
  domain, skip bounds that say nothing (`q <= 0`, `q <= max`), and are chosen
  deterministically (whole signals first).
* Derived-reset depth limits count register stages, independent of netlist
  order.
* Reports sort source lines numerically (`a.v:9` before `a.v:10`).
* `--checks` with an unknown kind is an error (exit 2); a typo used to
  select nothing and report a clean run.

### Testing

* `tests/unit/`: about 430 unit tests, no toolchain needed, ~1 s. Branch
  coverage 99% (CI gate 95%) on Python 3.11 to 3.13.
* `tests/unit/mutation.py`: mutation testing with a committed baseline of
  equivalent and accepted survivors, each with its reason; weekly CI job
  fails on any new survivor.
* The fuzzer's oracle no longer shares fvlint's part-select bounds or reset
  gating, and the generator produces synchronized resets, data-settable
  reset look-alikes and narrow signed indices.
* CI pins the pip toolchain's Yosys to the tested release and fails on
  drift of the unit tests' netlist snapshots.

## 0.2.0

Design review fixes and the regression system (manifest runner, soundness
fuzzer).

## 0.1.0

First prototype.
