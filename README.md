<!--
SPDX-FileCopyrightText: 2026 The fvlint Authors
SPDX-License-Identifier: ISC
-->
# fvlint: lightweight formal lint for RTL

fvlint finds common hardware structures in your RTL (counters, `unique`/`parallel_case`
statements, variable part-selects and shifts, divisions, narrowing assignments,
non-power-of-two memories, FIFOs, FSMs), generates a small property for each one
and proves it on **just the logic around that structure**. You get lint-style output and lint-style speed, but each result
is a formal proof or a counterexample trace, not a pattern match.

It is built entirely on open-source tools: Yosys for elaboration,
SymbiYosys for running proofs, ABC's PDR or an SMT solver as the engine, and
optionally yosys-slang for SystemVerilog. The idea follows the "auto-formal"
or "formal lint" apps in commercial tools.

```
$ fvlint --frontend slang --top demo_top examples/demo/demo_top.sv
fvlint: 13 checks: 2 fail, 1 info, 9 proven, 1 waived

FAIL  fsm_unreachable:u_framer.st=3'b100  examples/demo/demo_top.sv:61  unreachable: decoded by the logic (case item / compare) but never assigned
FAIL  index_range:u_framer.hdr_byte       examples/demo/demo_top.sv:88  counterexample at step 1 on the full design (top-level inputs unconstrained)
INFO  fsm_summary:u_framer.st             examples/demo/demo_top.sv:61  4 reachable states from reset 3'b000
(9 proven and 1 waived checks hidden; use -v)
```

## What it checks

| Check | Structure | Property |
|---|---|---|
| `counter_overflow` / `counter_underflow` | register fed back through `+ c` / `- c` with a constant step (signed or unsigned) | the step is never taken when it would wrap (or overflow, for signed arithmetic) |
| `parallel_case` | `unique case`, `unique casez`, `(* parallel_case *)` | at most one item matches whenever the result is used |
| `full_case` | `unique` / `priority` / `(* full_case *)` case with no default | an item that assigns the signal always matches (otherwise synthesis may differ from simulation) |
| `index_range` | variable part/bit select (`x[i*8 +: 8]`) | the offset stays inside the vector |
| `shift_range` | shift by a variable amount (`<<`, `>>`, `<<<`, `>>>`) | the amount stays below the result's width (left) or the shifted value's (right), so the shift doesn't move every bit out |
| `div_zero` | division or modulo by a variable (`/`, `%`) | the divisor is never 0 where the result is used |
| `truncation` | arithmetic result stored in fewer bits (`q <= a + b` with a narrow `q`) | the dropped bits are 0 (signed: copies of the sign) where the result is used |
| `mem_addr` | memory whose depth is not a power of two | read/write addresses stay in range when enabled |
| `fifo_overflow` / `fifo_underflow` | memory written at one pointer register and read at another (a FIFO) | no write while it is full (without a read), no read while it is empty |
| `fsm_unreachable` | FSM state register | every assigned or decoded state is reachable from reset |
| `fsm_trap` (warning) | FSM state register | the FSM can get back to its reset state from every reachable state |
| `dead_branch` (warning, opt-in) | if/else arm, case item, `?:` choice | the branch is taken in some state reachable from reset |

Logic disabled by a parameter, even through a wire or an expression such as
`ENABLE_IRQ && timer`, is recognized as dead and isn't checked at all.

### Settled without a proof

Some checks are reported as `INFO` without a proof; `results.json` gives the
`reason`:

* **Free-running counters** (`free_running`): the increment condition doesn't
  depend on the counter itself (a timebase, say), so the wrap-around looks
  intentional.
* **Counters that can't wrap within the horizon** (`horizon`): a counter that
  only resets or loads constants and steps by constants can't wrap sooner
  than its distance to the end divided by its largest step. A 64-bit
  instruction counter that adds 1 needs 2^64 cycles. Past `--horizon`
  (default 2^60 cycles, about 36 years at 1 GHz) it isn't checked. A counter
  that ends `UNKNOWN` says how many cycles a wrap needs at least, so you can
  judge it (`--horizon 2^32` accepts a 32-bit UART divider).
* **FIFO pointers** (`fifo_pointer`): a pointer that wraps by overflowing its
  width (a 2-bit pointer of a 4-entry FIFO) does so by design;
  `fifo_overflow` and `fifo_underflow` check what can actually go wrong. A
  pointer with an explicit wrap keeps its check, which proves the wrap works.
* **Logic in an unreachable FSM state** (`dead_state`): a check that only
  applies in a state the FSM analysis shows is unreachable points at that
  `fsm_unreachable` finding instead of being proved vacuous. Waive or fix
  the state and the rest follows.
* **`full_case` pragmas that change nothing** (`full_case_x`): when the code
  sets the signal to `'x` before the case (`alu_out = 'bx; case ...`),
  simulation gives `'x` when no item matches, just as synthesis may. fvlint
  elaborates the design a second time without the pragmas to see the value
  before the case, and only checks the statements where it isn't `'x`.

### Truncation

`truncation` looks only at result bits that nothing reads and no one named:
an explicit slice of a named wire (`wire [7:0] s = a + b; q <= s[3:0]`) is a
choice, not a truncation. Only bits that can actually be set count: an
unsized constant makes Yosys compute `c + 1` in 32 bits, but for a 4-bit `c`
only 5 of them can be set. A register stepped by a constant is left to the
counter checks.

### FIFOs

A FIFO is recognised by its pointers: one register gives the memory's write
address and another a read address, on the same clock, and each only holds,
adds 1, or goes back to 0 from the last entry. The checker keeps its own
count of the entries (+1 when the write pointer moves, -1 when the read
pointer moves, 0 while the FIFO's reset is active), so it doesn't matter how
the design tracks full and empty: a count, flags or an extra pointer bit.
After the first overflow or underflow the count no longer matches the FIFO,
so later events aren't judged: every `FAIL` is the first real one. A FIFO
whose pointers can be loaded in mid-run (a flush) can't be counted this way
and gets no FIFO checks.

### Dead branches

`--dead-branches` (or `dead_branches = true` in a project file) adds a
`dead_branch` check for every if/else arm, case item and `?:` choice: can
its condition hold after reset? A branch that is never taken is a `WARN`,
with the condition and the proof (``dead: `n == 3'd7` never holds after
reset; proven by PDR on cone 0``). A branch that is taken is `PROVEN`, and
its trace is the witness. Typical finds are an `else if` for a value a
counter never reaches, a case item for a state no transition leads to, and
a condition that is always true (its `else` is dead).

It is opt-in because it adds a check per branch, and because defensive code
(an `else` for "can't happen") is dead on purpose; waive those, or record
them in a [baseline](#baselines). Left out are a case statement's `default`
(and the implicit one, when no item matches), the reset branch
(`if (!rst_n)`), branches that only matter while a reset is active, and
logic a parameter switches off. Branches inside an unreachable FSM state are
`INFO` and point at the `fsm_unreachable` finding. A branch that assigns
several signals is one check, taken if any of its assignments can be. On
PicoRV32 that is 185 branches in about 15 seconds; the 5 dead ones are the
compressed-instruction and interrupt state that the default parameters
never set.

### Check IDs

Check IDs are **structural**: they name the register, memory port or
destination signal, e.g. `parallel_case:u_arb.gnt` or
`counter_overflow:u_fifo.count`. Waivers and baselines therefore survive
edits elsewhere in the file. A case statement is one check, named after the
signals it assigns (`parallel_case:alu_wait,alu_wait_2,cpu_state,mem_do_rinst`,
with the first three and a count past four). Each instance of a module has
its own checks, named after that instance's signals (`parallel_case:u_a.gnt`,
`parallel_case:u_b.gnt`). Statements that would share a name get the FSM
state they sit in (`@cpu_state=8'b00010000`), then a number in source
order (`#1`). Behind one check, the property is proven for each signal the
statement assigns (Yosys builds one multiplexer per signal); the result
names the signal that failed. A dead branch is named after its condition
(`dead_branch:n==3'd7`, `dead_branch:!(a&&b)`), and `results.json` has the
condition as Verilog in `condition`.

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
   * A FIFO check is first tried together with a guess at how the design
     counts its entries (a register that steps up and down, or the
     difference of pointers with an extra wrap bit). That stronger property
     is usually inductive; if it isn't proven, the plain one is, so a wrong
     guess costs time, never a verdict.
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
9. **Dead branches** run the other way round: the property is "the
   condition never holds", so a proof is a dead branch and a counterexample
   on the full cone is a taken one. One bounded search over the full cones
   settles most taken branches before the rounds; a branch a slice takes
   goes straight to the full cone.
10. **Vacuity.** For every proof fvlint also asks whether the check's
    condition can ever hold. If it can't, for example because an assumption
    rules it out, the result is `VACUOUS`, not `PROVEN`.

FSM checks need no solver. Yosys' FSM extraction treats control inputs as
free, so a state that is unreachable in the extracted graph is truly
unreachable. The start states are the ones a transition can enter while the
reset is asserted (control inputs computed from the reset, such as
`!rst_n || err`, are evaluated with it applied); Yosys' own guess of the reset
state is used only for an asynchronous reset. Transitions taken while a reset
is asserted are ignored when looking for trap states, so synchronous-reset
FSMs work too.

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
       [--waivers waivers.txt] [--recheck-waived] [--checks kind,...] [--dead-branches]
       [--baseline FILE [--update-baseline]] [--horizon CYCLES]
       [--engine auto|pdr|smtbmc] [--max-level N] [--no-cegar] [--no-vacuity] [-j N]
       [-o OUTDIR] [-v] [--summary-md FILE] [--github]
fvlint --config fvlint.toml [NAME...] [options for every configuration]
```

* `--frontend slang` is recommended for real SystemVerilog (packages,
  `import` in module headers, `.*`). Yosys' built-in parser handles a subset.
* `--uninit zero` (default) starts registers without a reset or `initial`
  value at 0, as on most FPGAs. Use `free` for arbitrary power-up values.
* The exit status is 1 on any `FAIL`, `ERROR` or `VACUOUS` result (adjust
  with `--fail-on fail|vacuous|unknown`) and 2 if fvlint couldn't run.
  With `--baseline`, only findings the baseline doesn't know count (see
  [Baselines](#baselines)).
  `OUTDIR/results.json` and `OUTDIR/junit.xml` are written every run, and
  counterexamples come with a VCD trace. In `results.json`, an `INFO`
  result's `reason` says why it needed no proof: `free_running`,
  `horizon`, `fifo_pointer`, `dead_state` or `full_case_x` (`null` for
  summaries).
* `--list` shows the detected checks without proving anything.
* `--horizon CYCLES` (an integer or `2^N`; default `2^60`, `0` to check
  every counter): see *What it checks*.
* `--summary-md FILE` appends a Markdown summary (the results that aren't
  `PROVEN`, and unused waivers). `--github` prints GitHub Actions
  annotations, so findings show on their source lines in a pull request,
  and appends the summary to `$GITHUB_STEP_SUMMARY`. GitHub shows at most
  10 error and 10 warning annotations per step; the job summary has every
  finding.
* File lists follow the simulator convention: relative paths in a list given
  with `-f` are relative to the current directory, with `-F` relative to the
  list file. Inside a list, `+incdir+`, `+define+`, `-I`, `-D`, nested
  `-f`/`-F` and `-v FILE` are understood; other simulator options are skipped.

### Project files

A design usually needs several runs: different tops, or one top under
different parameters, since logic a parameter switches off can't be checked.
Put them in a TOML file and run them together:

```toml
# fvlint.toml
out = "fvlint_out"                 # each configuration writes to OUT/NAME

[defaults]                         # shared by every configuration
jobs = 2

[config.default]
top = "picorv32"
files = ["picorv32.v"]             # paths are relative to this file
waivers = "fvlint/waivers/default.txt"

[config.irq]
top = "picorv32"
files = ["picorv32.v"]
params = { ENABLE_IRQ = 1, ENABLE_IRQ_QREGS = 1, ENABLE_IRQ_TIMER = 1 }
assume = "fvlint/assume/irq.sv"
waivers = "fvlint/waivers/irq.txt"
```

```
fvlint --config fvlint.toml                  # every configuration
fvlint --config fvlint.toml irq -j 4 -v      # just this one, with more options
```

The keys are the long option names with `_` for `-`: `top`, `files`,
`filelists` (`-f`), `filelists_rel` (`-F`), `include` (`-I`), `defines`,
`params` (tables or `NAME=VALUE` lists), `libs`, `frontend`, `reset`,
`no_reset`, `reset_anytime`, `reset_cycles`, `uninit`, `assume`, `waivers`,
`recheck_waived`, `baseline`, `dead_branches`, `engine`, `solver`,
`max_level`, `depth`, `timeout`, `pdr_timeout`, `horizon`, `checks`,
`fail_on`, `jobs`, and `args` for any other options. Options on the command
line apply to every configuration and win over the file, except the ones
that can be given several times (`-I`, `-D`, `-P`, `--lib`, `-f`, `-F`):
those are added to the file's. The exit
status is the worst one: 2 if a configuration couldn't run, else 1 if any
has a finding. A configuration's name is its output directory, so it may use
letters, digits, `_`, `.` and `-`, and starts with a letter or digit.

### In CI (GitHub Actions)

This repository is also a GitHub Action. It installs the OSS CAD Suite and
the matching fvlint, runs a project file with `--github` (annotations and a
job summary), and uploads the results with their counterexample traces:

```yaml
jobs:
  fvlint:
    runs-on: ubuntu-latest
    strategy:
      matrix:
        config: [default, irq]
    steps:
      - uses: actions/checkout@v7
      - uses: tm-treehouse/fvlint@v0.7.0
        with:
          config: fvlint.toml        # the default
          configs: ${{ matrix.config }}
```

Other inputs: `args` (more options), `output`, `upload`, `artifact-name`,
`annotations` (`"false"`: the job summary only, no annotations on source
lines), `fail-on-findings` (`"false"`: report only; the `exit-code` output
still says 1, and a run that couldn't start still fails), `python-version`
and `oss-cad-suite-version` (default: the build fvlint's own CI uses). The
action can run several times in one job (the OSS CAD Suite is installed
once), with one `oss-cad-suite-version` per job. To gate a design that
already has findings on new ones only, give its configurations a `baseline`
(see [Baselines](#baselines)).

[fvlint-example](https://github.com/tm-treehouse/fvlint-example) is a
minimal repository set up this way: a small design, a project file,
assumptions, waivers and the workflow, with its CI passing.
[picorv32-fvlint](https://github.com/tm-treehouse/picorv32-fvlint) runs
fvlint on a real core, PicoRV32.

### Results

| Status | Meaning |
|---|---|
| `PROVEN` | holds on a slice, hence on the whole design (for `dead_branch`: the branch is taken, with a trace) |
| `FAIL` | counterexample on the full cone, or a slice counterexample confirmed by replay, with unconstrained top-level inputs |
| `VACUOUS` | "proven", but the check's condition can never occur (over-constrained assumptions or dead logic) |
| `ERROR` | tool error, or an unsatisfiable environment (contradictory `--assume`) |
| `UNKNOWN` | neither proven nor refuted, or refuted only on a cut slice |
| `WARN` / `INFO` | FSM trap states, dead branches, FSM summaries, and checks settled without a proof (free-running counters, counters past the horizon, FIFO pointers, logic in unreachable states, `full_case` pragmas that change nothing) |
| `WAIVED` | matched a waiver |

### Triage: assumptions and waivers

Most `FAIL`s on block-level runs come from unconstrained top-level inputs.
Constrain them with a module named `fvlint_assumptions` whose ports are
matched to the design's signals by name. Misspelled ports are rejected (with
the nearest names), and contradictory assumptions are reported, never
silently accepted:

```systemverilog
module fvlint_assumptions (input [1:0] lane);
  always @* assume (lane <= 2'd2);
endmodule
```

A port can also read any other net of the design, by its hierarchical
name: in an `fvlint_net` attribute, or as an escaped identifier. That is the
way to state what a submodule's environment guarantees, or a fact about
internal state the design relies on:

```systemverilog
module fvlint_assumptions (
  (* fvlint_net = "u_core.mem_wordsize" *) input [1:0] wordsize,
  input \u_dec.illegal
);
  always @* assume (wordsize != 2'd3);
  always @* assume (!\u_dec.illegal );
endmodule
```

The logic behind an assumed net is part of every proof, so an assumption
on an internal net is as strong as one on an input: a `FAIL` is still a
trace of the whole design that meets every assumption. The more logic stands
behind the assumed nets, the larger each proof gets.

fvlint ships interface rules to instantiate in `fvlint_assumptions`. The
clocked ones say nothing while the reset (active at `RST_ACTIVE`) is
active:

| Module | Assumes |
|---|---|
| `fvl_assume_onehot #(W) (s)` | exactly one bit of `s` is set |
| `fvl_assume_onehot0 #(W) (s)` | at most one bit of `s` is set |
| `fvl_assume_range #(W, LO, HI) (v)` | `LO <= v <= HI` (unsigned) |
| `fvl_assume_stable #(W, RST_ACTIVE) (clk, rst, v)` | `v` keeps its value from the first cycle after reset (configuration inputs, straps) |
| `fvl_assume_handshake #(W, RST_ACTIVE) (clk, rst, valid, ready, data)` | a raised `valid` stays raised, with `data` unchanged, until a clock edge with `ready` |
| `fvl_assume_pulse #(RST_ACTIVE) (clk, rst, p)` | `p` is never high in two consecutive cycles |

```systemverilog
module fvlint_assumptions (input clk, input rst_n, input in_valid, input in_ready,
                           input [31:0] in_data, input [3:0] cfg);
  fvl_assume_handshake #(.W(32), .RST_ACTIVE(0)) u_in (clk, rst_n, in_valid, in_ready, in_data);
  fvl_assume_stable #(.W(4), .RST_ACTIVE(0)) u_cfg (clk, rst_n, cfg);
endmodule
```

A `full_case` FAIL means a cycle where no item that assigns the signal
matches, so the pragma lets synthesis pick any value where simulation keeps
the one assigned before the case. (Where the code assigns `'x` before the
case, both agree; fvlint recognizes that and doesn't check it.) When fvlint
can't follow a case result to the register that uses it, `parallel_case` is
checked in every cycle, so overlapping items in a cycle whose result is
never used also FAIL; those are harmless.

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
fvlint: 13 checks: 1 info, 10 proven, 2 waived
```

Waivers go stale as the design changes. fvlint warns about every line of a
waiver file that matches no check (with `--github`, on that line), and
`--recheck-waived` proves the waived checks anyway and names the waivers that
are no longer needed, while still treating them as waived. With `--config`,
a waiver file that several configurations share is judged over all of them:
after the last run, fvlint reports the lines that matched no check in any
configuration that loaded the file.

### Baselines

A design that already has findings can still gate its CI on new ones.
Record what it has now, commit the file, and compare every later run
against it:

```
fvlint ... --baseline fvlint/baseline.json --update-baseline   # record (creates the file)
fvlint ... --baseline fvlint/baseline.json                     # compare
```

The baseline lists the check id and status of every finding (`FAIL`,
`ERROR`, `VACUOUS`, `UNKNOWN`, `WARN`), one per line, sorted, so its diff
in a pull request shows what was accepted. A finding is known when the
baseline has its id with the same status or a more severe one: a `FAIL`
that is `UNKNOWN` now is still known, an `UNKNOWN` that became a `FAIL` is
new. Known findings are still reported, marked `(in baseline)`; they don't
count towards the exit status, are notices rather than errors in GitHub
annotations and skipped tests in JUnit. Check ids are structural, so a
renamed register makes its findings new: a baseline can hide a known
finding, never a new one.

fvlint warns about baseline entries that are out of date: ids no check has
any more, and checks that are no finding now. `--update-baseline` rewrites
the file (keeping entries of check kinds that didn't run, with `--checks`)
and exits 0. An earlier run's `results.json` works as a baseline too. With
`--fail-on unknown` and a baseline, a proof that times out where it used
to pass fails the run, while the `UNKNOWN`s you already have don't.

In a project file, give each configuration its own file (`baseline =
"fvlint/baseline/irq.json"`); `fvlint --config fvlint.toml
--update-baseline` refreshes them all. Two configurations can't share one.

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
| `tests/unit/` | unit tests of every module's internals, no toolchain needed (about 2 s). Netlists are built by hand for exact edge cases and also loaded from committed Yosys snapshots of `tests/unit/data/rtl` for the shapes Yosys really produces; SymbiYosys log parsing is tested on lines in the formats of real runs, verbatim for the irregular ones (a step-0 failure has no step number). The scheduler is tested with a scripted solver (refinement, replay, batching, deep BMC, vacuity) that also checks every job it is handed is closed (no bit a checker reads is left undriven), and against a solver that answers from a per-property truth table over many random mixes, so its verdicts must follow from the truth; external tools are tested with stub executables. Kept honest by branch coverage and mutation testing (below). |
| `tests/regress/manifest.toml` | 112 case runs over the fixtures in `tests/fixtures`. Each fixture has clean structures and planted bugs, including a reproduction for every defect found in the design review: multi-clock false proofs, vacuous assumptions, parameter-disabled logic, synchronous-reset FSM traps, reset synchronizers, signed counters, register-bounded timers; and for the patterns found on PicoRV32: case statements in unreachable states, parameter-guarded timers, harmless and harmful `full_case` pragmas, wide counters and the horizon, up/down counters, statements told apart by FSM state, a module instantiated twice; and clean, guarded and buggy fixtures for every newer check (shifts, divisions, assumptions on internal nets, dead branches, truncation, FIFOs) and for baselines. Many cases run under both engines, plus a 200-counter throughput case. |
| `fvlint.fuzz` | soundness fuzzer: random designs (counters, registered guards, case statements, part-selects including narrow signed indices, memories, state machines (some overridden after the reset branch), second clocks, falling edges, synchronized resets, and flops that look like reset stages but that data can set; and the constructs fvlint settles without a proof: case statements inside FSM states, up/down counters under a small `--horizon`, `full_case` on signals set to `'x` or to a value first, parameter guards; and shifts and divisions by registers, sums stored in fewer bits, four-entry FIFOs with one guard wrong or none, and assumptions on internal nets). The generator writes down, for each construct it builds, when it is active and when it goes wrong, as plain Verilog. An independent oracle appends those monitors to its own copy of the design and re-checks every `PROVEN`, `VACUOUS`, `FAIL` and unreachable-state verdict, and the `INFO` verdicts that skip a proof (dead logic, the horizon), with a plain bounded model check: it uses none of fvlint's netlist, slicing, refinement, lemmas, PDR, check parameters, path conditions or reset discovery. A harmless `full_case` must be one the generator set to `'x`, and a construct whose parameter guard is 1 must have a check. Half the designs also run with `--dead-branches`: fvlint writes each branch's condition down as Verilog over the design's signals, and the oracle must reach every branch fvlint says is taken (within its witness's step) and must not reach one it says is dead; only that condition comes from fvlint's netlist. |

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
`tests/unit/mutation_baseline.json`. An entry names the module, the
enclosing function, the line of code and the change (and which occurrence of
that in the function), so edits elsewhere don't move it onto another site.
The report separates new survivors from listed ones and flags entries that
are now killed or whose code is gone; `--strict` (used by the weekly CI run)
fails on any of those. Entries whose code changed also fail the ordinary unit
tests, so they are caught at once rather than in the weekly run.

The committed Yosys snapshots are regenerated with
`python tests/unit/data/make_snapshots.py` (`--check` reports drift).

`.github/workflows/ci.yml` runs lint, REUSE and the unit tests with coverage
on Python 3.11 to 3.13, then the full regression with the fuzzer on both the
pip toolchain and OSS CAD Suite. `mutation.yml` runs mutation testing weekly
or on demand.

## Limitations

* **Assumptions** read nets of the flattened design. A net Yosys optimises
  away (unused, or merged into another name) can't be named; the error
  lists the nearest names that are still there.
* **`div_zero` and `shift_range`** follow the result through multiplexers
  to the register that stores it, like `index_range`. A result stored every
  cycle counts as used every cycle, even if nothing reads it while the
  divisor is 0 or the amount is too large.
* **FIFO proofs** relate fvlint's own count of the entries to the design's
  bookkeeping. fvlint first tries the property together with a guess at
  that relation (a register that counts up and down, or the difference of
  pointers with an extra wrap bit), which is usually inductive: the demo's
  100-entry FIFO is proven in seconds. When the guess doesn't hold or
  doesn't help, the plain property is proven on its own, which can take PDR
  long on deep FIFOs and end `UNKNOWN`; with k-induction alone (`--engine
  smtbmc`) more of them do. Failures are found either way. FIFOs on two
  clocks, with several write ports, or whose pointers aren't plain registers
  (a read pointer computed ahead for a first-word-fall-through FIFO) aren't
  recognised.
* **`truncation`** sees arithmetic (`+`, `-`, `*`, `<<`, unary `-`) whose
  result is wider than what is kept. Verilog sizes `a + b` to its widest
  operand or the destination, so a sum that overflows into a destination
  as wide as its operands loses its carry inside the expression; that is
  `counter_overflow`'s ground when it is a counter, and not seen otherwise.
* **`dead_branch`** checks a branch's own condition together with the
  conditions under which its result is used (the enclosing ifs and case
  items, a register's enable); where fvlint can't follow the result, it
  checks fewer of them, which can only make a dead branch look taken. A
  case item that matches only when an earlier item matches too counts as
  taken, since Yosys compares each item on its own. Branches Yosys folds
  away (a repeated case item, `if (0)`) aren't seen at all. The implicit
  default of a case statement is recognised by its source location (the
  item is on a later line than `case`), so on a case written on one line it
  is checked like an `else`. A branch with no condition fvlint can write as
  Verilog is named after the signals it assigns (`dead_branch:q:then`).
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
  them. The oracle shares the tools (Yosys, SymbiYosys) and the contract
  (registers start at zero, the reset is held at start, checks apply while
  the resets are inactive) with fvlint, so a mistake in those would be
  shared. Where a register has two increments by the same constant, the
  oracle watches them together, so with mixed verdicts it checks only the
  `FAIL`, or only that neither goes wrong.
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
