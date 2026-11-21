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
SymbiYosys with an SMT solver for the proofs, and optionally yosys-slang for
SystemVerilog. The idea follows the "auto-formal" or "formal lint" apps in
commercial tools.

```
$ fvlint --frontend slang --top demo_top examples/demo/demo_top.sv
fvlint: 11 checks: 2 fail, 1 info, 7 proven, 1 waived

FAIL  fsm_unreachable:u_framer.st=3'b100  examples/demo/demo_top.sv:61  unreachable: decoded by the logic (case item / compare) but never assigned
FAIL  index_range:demo_top.sv:88          examples/demo/demo_top.sv:88  counterexample at step 1 on the full design (top-level inputs unconstrained)
INFO  fsm_summary:u_framer.st             examples/demo/demo_top.sv:61  4 reachable states from reset 3'b000
(7 proven and 1 waived checks hidden; use -v)
```

## What it checks

| Check | Structure | Property |
|---|---|---|
| `counter_overflow` / `counter_underflow` | register fed back through `+ c` / `- c` with a constant step | the increment (decrement) is never taken when it would wrap |
| `parallel_case` | `unique case`, `unique casez`, `(* parallel_case *)` | at most one item matches whenever the result is used |
| `full_case` | `unique` / full case with no default | some item always matches |
| `index_range` | variable part/bit select (`x[i*8 +: 8]`) | the offset stays inside the vector |
| `mem_addr` | memory whose depth is not a power of two | read/write addresses stay in range when enabled |
| `fsm_unreachable` | FSM state register | every assigned or decoded state is reachable from reset |
| `fsm_trap` (warning) | FSM state register | the FSM can get back to its reset state from every reachable state |

A counter whose increment condition doesn't depend on the counter itself (a
free-running timer, say) is reported as `INFO`: its wrap-around looks intentional.

## How it works

1. **Elaborate** with Yosys (`proc; flatten`), keeping the structure intact,
   and run Yosys' own FSM extraction.
2. **Detect** structures in the JSON netlist. For each one, also work out the
   *path condition* under which the value matters. For example, a `unique case`
   inside `if (valid)` is checked only when `valid` is set.
3. **Slice** a cone of influence around each check. Registers more than
   `level` stages away are **cut**: replaced by unconstrained values.
4. **Prove** on the slice with SymbiYosys (k-induction).
   * Cutting only adds behaviour, so **a proof on a slice holds on the full design**.
   * A counterexample on a slice may be spurious, so fvlint **grows the cone**
     (level 0, 1, 2, … then the full design) and only reports `FAIL` when the
     full design fails. In the test fixtures, `credit_ok`'s overflow check
     fails at level 0 and proves once the registered "not full" flag is pulled in.
5. **Helper lemmas.** k-induction struggles with counters (e.g. a 16-bit
   modulo-1000 counter). fvlint guesses candidate invariants from the
   structure, such as `count <= 999` from the compare constant or "the state
   register only holds reachable codes" for FSMs. It filters them
   Houdini-style: candidates that turn out false or non-inductive are
   dropped, so a bad guess costs time but never soundness.
6. **Deep search last.** If no cone proves the property, one bounded search runs
   on the largest cone, with a depth derived from the structure (e.g. 2^width
   for a counter). This finds wrap bugs that only show up after 100+ cycles.

FSM checks don't need a solver. Yosys' FSM extraction treats control inputs
as free, so a state that is unreachable in the extracted graph is truly
unreachable.

## Installing

fvlint is pure Python 3.10+ with no Python dependencies. It needs Yosys,
SymbiYosys and an SMT solver on `PATH`:

* **Recommended:** [OSS CAD Suite](https://github.com/YosysHQ/oss-cad-suite-build)
  (native Yosys, SymbiYosys, yosys-slang, Yices, Bitwuzla, ABC).
* **Pip-only:** `pip install .[yowasp]` installs YoWASP's WebAssembly
  Yosys + SymbiYosys (with slang built in) and Z3. This works anywhere but is
  several times slower per proof.

```
pip install .            # or: pip install .[yowasp]
fvlint --help
```

## Usage

```
fvlint --top TOP [files...] [-f files.f] [-I dir] [-D define] [-P param=value]
       [--frontend yosys|slang] [--reset NAME[:LEVEL] | --no-reset] [--uninit zero|free]
       [--assume assumptions.sv] [--waivers waivers.txt] [--checks kind,...]
       [--max-level N] [--depth N] [--engine smtbmc|pdr] [-j N] [-o OUTDIR] [-v]
```

* `--frontend slang` is recommended for real SystemVerilog (packages,
  `import` in module headers, `.*`). Yosys' built-in parser handles a subset.
* **Reset:** guessed from port names (`rst`, `rst_n`, `areset`, `*_rst_ni`, …)
  and assumed active in the first cycle. Checks are disabled while reset is
  asserted. Override with `--reset`.
* **Power-up values:** `--uninit zero` (default) starts registers without a
  reset or `initial` value at 0, as on most FPGAs. Use `free` for ASIC-style
  arbitrary values.
* Exit status is 1 if any check fails (also on `UNKNOWN` with `--fail-on unknown`),
  so it drops into CI. `OUTDIR/results.json` and `OUTDIR/junit.xml` are written
  every run, and counterexamples come with a VCD trace.
* `--list` shows the detected checks without proving anything.

### Results

| Status | Meaning |
|---|---|
| `PROVEN` | holds on a slice, hence on the whole design |
| `FAIL` | counterexample on the full design, with unconstrained top-level inputs |
| `UNKNOWN` | neither proven nor refuted, or refuted only on a cut slice |
| `WARN` / `INFO` | FSM trap states, free-running counters, FSM summaries |
| `WAIVED` | matched a waiver |

### Triage: assumptions and waivers

Most `FAIL`s on block-level runs come from unconstrained top-level inputs.
Constrain them with a module named `fvlint_assumptions` whose ports are
top-level inputs, matched by name:

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

### CI / FuseSoC

fvlint reads `.f` file lists (`-f`, with `+incdir+`, `+define+`, `-I`, `-D`).
With FuseSoC you can export a file list for a core and point fvlint at it, or
wrap fvlint in a FuseSoC generator or hook.

## Limitations (prototype)

* **Single clock.** Proofs use SymbiYosys' default global-clock model.
  Multi-clock designs need `multiclock on`, which fvlint doesn't set up yet.
* **Vendor primitives** must be supplied as blackbox stubs (`--lib`). Their
  outputs are treated as unconstrained.
* **Assumptions** can only constrain top-level inputs.
* **Structure recognition** is heuristic. A counter is a register with a
  `+/- constant` feedback path through a mux tree. FSM detection relies on
  Yosys' `fsm_detect` (forced on for every non-port register). Registers
  driving top-level ports aren't analysed as FSMs, and a `case` branch
  identical to `default` gets merged away by the frontend.
* `--engine pdr` (ABC's IC3/PDR via `yosys-abc`) is wired up but **untested**,
  because the development environment had no `yosys-abc`. The default
  k-induction engine is what the test suite exercises.
* A `FAIL` on the full design is real with respect to the **unconstrained**
  top-level inputs, so treat it as "true at this block boundary".

## Development

```
python -m unittest -v tests.test_fvlint      # end-to-end, needs the toolchain
reuse lint                                   # SPDX/REUSE compliance
```

`tests/fixtures` contains small original designs, each with clean structures
and planted bugs (a terminal count that doesn't fit its counter, an
off-by-one registered threshold, a ring pointer that wraps one entry late,
overlapping `unique casez` items, a 3-lane select driven by a 2-bit pointer,
an orphan FSM state). The suite checks that each one gets exactly the
expected result.

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
