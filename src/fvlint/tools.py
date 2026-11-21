# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Locate and run the external tools (Yosys, SymbiYosys, SMT solvers).

fvlint never links against or bundles these tools; it only invokes them as
separate programs.  Native installs (e.g. OSS CAD Suite) are preferred, with the
YoWASP Python packages (``yowasp-yosys``) as a fallback.
"""

from __future__ import annotations

import os
import shutil
import subprocess
from dataclasses import dataclass, field


class ToolError(RuntimeError):
    pass


def _which(*names: str) -> str | None:
    for n in names:
        p = shutil.which(n)
        if p:
            return p
    return None


@dataclass
class Toolchain:
    yosys: str
    sby: str
    smtbmc: str | None
    witness: str | None
    abc: str | None
    solver: str | None
    is_yowasp: bool
    env: dict = field(default_factory=dict)

    @classmethod
    def discover(cls, solver: str | None = None) -> "Toolchain":
        yosys = os.environ.get("FVLINT_YOSYS") or _which("yosys")
        yowasp = False
        if not yosys:
            yosys = _which("yowasp-yosys")
            yowasp = yosys is not None
        if not yosys:
            raise ToolError("Yosys not found: install OSS CAD Suite or `pip install yowasp-yosys`")

        if yowasp:
            sby = _which("yowasp-sby")
            smtbmc = _which("yowasp-yosys-smtbmc")
            witness = _which("yowasp-yosys-witness")
        else:
            sby = os.environ.get("FVLINT_SBY") or _which("sby")
            smtbmc = _which("yosys-smtbmc")
            witness = _which("yosys-witness")
        if not sby:
            raise ToolError("SymbiYosys (sby) not found")
        abc = _which("yosys-abc")

        if solver is None:
            for exe, name in (("yices-smt2", "yices"), ("bitwuzla", "bitwuzla"),
                              ("boolector", "boolector"), ("z3", "z3")):
                if _which(exe):
                    solver = name
                    break

        env = dict(os.environ)
        env["YOSYS"] = yosys
        if smtbmc:
            env["SMTBMC"] = smtbmc
        if witness:
            env["WITNESS"] = witness
        if abc:
            env["ABC"] = abc
        return cls(yosys, sby, smtbmc, witness, abc, solver, yowasp, env)

    def run_yosys(self, script: str, cwd: str, name: str) -> None:
        """Run a Yosys script in `cwd`; raise ToolError with the log tail on failure."""
        log = os.path.join(cwd, name + ".log")
        with open(os.path.join(cwd, name + ".ys"), "w") as f:
            f.write(script)
        with open(log, "w") as lf:
            r = subprocess.run([self.yosys, "-q", "-l", name + ".log.full", "-s", name + ".ys"],
                               cwd=cwd, stdout=lf, stderr=subprocess.STDOUT, env=self.env)
        if r.returncode != 0:
            tail = ""
            for p in (log, log + ".full"):
                if os.path.exists(p):
                    with open(p, errors="replace") as f:
                        tail += "".join(f.readlines()[-15:])
            raise ToolError(f"yosys failed (see {log}.full):\n{tail}")

    def slang_prefix(self, cwd: str) -> str:
        """Commands needed before read_slang: nothing if the frontend is built
        in (YoWASP), 'plugin -i slang' for an installed yosys-slang plugin."""
        if getattr(self, "_slang", None) is not None:
            return self._slang
        for prefix in ("", "plugin -i slang\n"):
            r = subprocess.run([self.yosys, "-q", "-p", prefix.replace("\n", "; ") + "help read_slang"],
                               cwd=cwd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=self.env)
            if r.returncode == 0:
                self._slang = prefix
                return prefix
        raise ToolError("--frontend slang: Yosys has no read_slang command and the yosys-slang "
                        "plugin could not be loaded")

    def run_sby(self, sby_file: str, cwd: str, timeout: float | None) -> int:
        try:
            r = subprocess.run([self.sby, "-f", os.path.basename(sby_file)], cwd=cwd,
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                               env=self.env, timeout=timeout)
            return r.returncode
        except subprocess.TimeoutExpired:
            return -1

    def describe(self) -> str:
        parts = [f"yosys={self.yosys}", f"sby={self.sby}", f"solver={self.solver}"]
        parts.append(f"abc={'yes' if self.abc else 'no'}")
        return ", ".join(parts)
