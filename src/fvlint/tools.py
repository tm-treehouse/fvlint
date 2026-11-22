# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Locate and run the external tools (Yosys, SymbiYosys, ABC, SMT solvers).

fvlint never links against or bundles these tools; it only invokes them as
separate programs.  Native installs (e.g. OSS CAD Suite) are preferred, with
the YoWASP packages (``yowasp-yosys``) and the ``yosys-abc`` binary shipped in
the ``pyosys`` wheel as pip-installable fallbacks.
"""

from __future__ import annotations

import os
import re
import shutil
import signal
import subprocess
from dataclasses import dataclass, field

from .netlist import TESTED_YOSYS, parse_yosys_version


class ToolError(RuntimeError):
    pass


_SAFE = re.compile(r"^[A-Za-z0-9_./+=:@,\-\\$\[\]]+$")
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_$]*$")


def yosys_arg(s: str) -> str:
    """Quote one argument for a Yosys script line.  Yosys treats '#' as a
    comment and ';' as a command separator outside quotes."""
    if _SAFE.match(s):
        return s
    if '"' in s or "\n" in s:
        raise ToolError(f"cannot pass {s!r} to Yosys (contains a quote or newline)")
    return f'"{s}"'


def _which(*names: str) -> str | None:
    for n in names:
        p = shutil.which(n)
        if p:
            return p
    return None


def _pyosys_abc() -> str | None:
    try:
        import importlib.util
        spec = importlib.util.find_spec("pyosys")
    except (ImportError, ValueError):
        return None
    if not spec or not spec.submodule_search_locations:
        return None
    for d in spec.submodule_search_locations:
        p = os.path.join(d, "yosys-abc")
        if os.path.isfile(p) and os.access(p, os.X_OK):
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
    version: tuple | None = None
    env: dict = field(default_factory=dict)
    _slang: str | None = None

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
        abc = os.environ.get("FVLINT_ABC") or _which("yosys-abc") or _pyosys_abc()

        if solver is None:
            for exe, name in (("yices-smt2", "yices"), ("bitwuzla", "bitwuzla"),
                              ("boolector", "boolector"), ("z3", "z3")):
                if _which(exe):
                    solver = name
                    break
        env = dict(os.environ)
        env["YOSYS"] = yosys
        for k, v in (("SMTBMC", smtbmc), ("WITNESS", witness), ("ABC", abc)):
            if v:
                env[k] = v
        tc = cls(yosys, sby, smtbmc, witness, abc, solver, yowasp, env=env)
        try:
            out = subprocess.run([yosys, "-V"], capture_output=True, text=True, env=env, timeout=120)
            tc.version = parse_yosys_version(out.stdout + out.stderr)
        except (OSError, subprocess.TimeoutExpired):
            tc.version = None
        return tc

    def version_warning(self) -> str | None:
        if self.version is None:
            return "could not determine the Yosys version"
        if self.version not in TESTED_YOSYS:
            tested = ", ".join(f"{a}.{b}" for a, b in TESTED_YOSYS)
            return (f"Yosys {self.version[0]}.{self.version[1]} has not been tested with this "
                    f"fvlint release (tested: {tested}); unknown cell types are cut conservatively")
        return None

    def run_yosys(self, script: str, cwd: str, name: str, allow_fail: bool = False) -> int:
        """Run a Yosys script in `cwd`; raise ToolError with the log tail on failure."""
        log = os.path.join(cwd, name + ".log")
        with open(os.path.join(cwd, name + ".ys"), "w") as f:
            f.write(script)
        with open(log, "w") as lf:
            r = subprocess.run([self.yosys, "-q", "-l", name + ".log.full", "-s", name + ".ys"],
                               cwd=cwd, stdout=lf, stderr=subprocess.STDOUT, env=self.env)
        if r.returncode != 0 and not allow_fail:
            raise ToolError(f"yosys failed (see {log}.full):\n{self.log_tail(log)}")
        return r.returncode

    @staticmethod
    def log_tail(log: str, n: int = 15) -> str:
        tail = ""
        for p in (log, log + ".full"):
            if os.path.exists(p):
                with open(p, errors="replace") as f:
                    tail += "".join(f.readlines()[-n:])
        return tail

    def slang_prefix(self, cwd: str) -> str:
        """Commands needed before read_slang: nothing if the frontend is built
        in (YoWASP), 'plugin -i slang' for an installed yosys-slang plugin."""
        if self._slang is not None:
            return self._slang
        for prefix in ("", "plugin -i slang\n"):
            r = subprocess.run([self.yosys, "-q", "-p", prefix.replace("\n", "; ") + "help read_slang"],
                               cwd=cwd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=self.env)
            if r.returncode == 0:
                self._slang = prefix
                return prefix
        raise ToolError("--frontend slang: Yosys has no read_slang command and the yosys-slang "
                        "plugin could not be loaded")

    # Seconds SymbiYosys gets beyond its own `timeout` option to shut down.
    SBY_GRACE = 30.0

    def run_sby(self, sby_file: str, cwd: str, timeout: float | None) -> int:
        """Run SymbiYosys.  The job's own `timeout` option normally ends it;
        this is a backstop that kills the whole process group.  Returns the
        exit code, or -1 if the backstop fired."""
        p = subprocess.Popen([self.sby, "-f", os.path.basename(sby_file)], cwd=cwd,
                             stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=self.env,
                             start_new_session=True)
        try:
            return p.wait(timeout=None if timeout is None else timeout + self.SBY_GRACE)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(p.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            p.wait()
            return -1

    def describe(self) -> str:
        v = f"{self.version[0]}.{self.version[1]}" if self.version else "?"
        return (f"yosys {v} ({'yowasp' if self.is_yowasp else 'native'}), solver={self.solver}, "
                f"abc={'yes' if self.abc else 'no'}")
