<!--
SPDX-FileCopyrightText: 2026 The fvlint Authors
SPDX-License-Identifier: ISC
-->
# Third-party software

fvlint is pure Python with **no runtime Python dependencies** (standard library
only). It does not include, link against or redistribute any third-party code.
It runs the tools below as **separate programs**, which the user installs
independently. Their licenses apply to those tools, not to fvlint.

Licenses were checked against the packages themselves where installed
(Python package metadata, bundled license files, `yosys -p license`) and
against the projects' own pages otherwise, in November 2026.

| Tool | Used for | License | Required? |
|---|---|---|---|
| [Yosys](https://github.com/YosysHQ/yosys) (incl. `yosys-smtbmc`, `yosys-witness`) | elaboration, netlists, SMT model | ISC | yes |
| [SymbiYosys](https://github.com/YosysHQ/sby) (`sby`) | runs each proof job | ISC | yes |
| SMT solver for `smtbmc`: [Z3](https://github.com/Z3Prover/z3) | proofs | MIT | one solver needed |
| — or [Yices 2](https://github.com/SRI-CSL/yices2) | proofs | BSD-3-Clause from 2.8.0 (Nov 2026); GPL-3.0 for earlier releases | optional |
| — or [Bitwuzla](https://github.com/bitwuzla/bitwuzla) | proofs | MIT | optional |
| — or [Boolector](https://github.com/Boolector/boolector) 3.x | proofs | MIT | optional |
| [yosys-slang](https://github.com/povik/yosys-slang) | `--frontend slang` | ISC; parts derived from slang are MIT | optional |
| [slang](https://github.com/MikePopoloski/slang) | used by yosys-slang | MIT | optional |
| [ABC](https://github.com/berkeley-abc/abc) (`yosys-abc`) | `--engine pdr` | permissive license, © The Regents of the University of California | optional |
| [YoWASP](https://yowasp.org) `yowasp-yosys`, `yowasp-runtime` | pip-installable Yosys + SymbiYosys | ISC | optional (`pip install fvlint[yowasp]`) |
| [wasmtime-py](https://github.com/bytecodealliance/wasmtime-py) | dependency of YoWASP | Apache-2.0 WITH LLVM-exception | with YoWASP |

## Notes for redistribution

* Publishing or using fvlint itself only involves fvlint's ISC license.
* If you ship fvlint **bundled with** these tools (a container image, an
  internal tool distribution), you must also meet each bundled tool's license.
  Most are permissive. The one copyleft case is Yices **before 2.8.0**
  (GPL-3.0): bundling it means providing its source under GPL-3.0 terms. Yices
  2.8.0+, Z3 and Bitwuzla avoid that.
* Each proof job copies fvlint's own checker library (`src/fvlint/checkers.v`,
  ISC) into its work directory, next to a netlist derived from **your** RTL.
  Those netlists, traces and reports are derived from your design and remain
  yours. Don't publish `fvlint_out/` for proprietary designs.

## Development-only tools

The [REUSE](https://reuse.software) linter (`pip install reuse`, GPL-3.0-or-later)
is used to check that every file carries SPDX copyright and license
information. It is not a dependency of fvlint and is not distributed with it.
