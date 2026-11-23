# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""fvlint.tools: discovery, quoting and process handling, against stub
executables on a private PATH (POSIX only)."""

from __future__ import annotations

import os
import stat
import time
import types
import unittest
from unittest import mock

from fvlint import tools
from fvlint.tools import Toolchain, ToolError, _pyosys_abc, _which, yosys_arg

from .support import TempDirCase

POSIX = os.name == "posix"

YOSYS_STUB = r"""#!/bin/sh
# -V: version; -p "...help read_slang": slang probe; -q -l LOG -s SCRIPT: run.
if [ "$1" = "-V" ]; then echo "${STUB_VERSION-Yosys 0.71 (git sha1 0000000, Release)}"; exit 0; fi
if [ "$1" = "-q" ] && [ "$2" = "-p" ]; then
  case "$3" in
    "plugin -i slang; help read_slang") [ "$STUB_SLANG" = plugin ] && exit 0; exit 1;;
    "help read_slang") [ "$STUB_SLANG" = builtin ] && exit 0; exit 1;;
  esac
fi
if [ "$1" = "-q" ] && [ "$2" = "-l" ]; then
  [ "$4" = "-s" ] || exit 9
  echo "full log line" > "$3"; echo "stdout line"; cat "$5" > ran_script.txt; exit ${STUB_RC-0}
fi
exit 3
"""


def _alive(pid: int) -> bool:
    """Running (a killed process may linger as an unreaped zombie in
    containers whose init does not reap orphans)."""
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    try:
        with open(f"/proc/{pid}/stat") as f:
            return f.read().split(")")[-1].split()[0] != "Z"
    except OSError:
        return True


class Quoting(unittest.TestCase):
    def test_safe_arguments_are_unquoted(self):
        for s in ("rtl/a.sv", "-Iinc", "-DW=8", "a+b", "x@y,z", "C:\\w\\a.v", "$top", "a[0]", "../up.v"):
            with self.subTest(s=s):
                self.assertEqual(yosys_arg(s), s)

    def test_specials_are_quoted(self):
        for s in ("my dir/a.sv", "a;b", "x#y", "tab\there", "a'b", "a*b"):
            with self.subTest(s=s):
                self.assertEqual(yosys_arg(s), f'"{s}"')

    def test_unrepresentable(self):
        for s in ('bad"name', "line\nbreak"):
            with self.subTest(s=s), self.assertRaises(ToolError):
                yosys_arg(s)


@unittest.skipUnless(POSIX, "stub executables are shell scripts")
class Discovery(TempDirCase):
    def setUp(self):
        super().setUp()
        self.bin = os.path.join(self.tmp, "bin")
        os.makedirs(self.bin)
        env = {k: v for k, v in os.environ.items() if not k.startswith(("FVLINT_", "STUB_"))}
        env["PATH"] = self.bin
        p = mock.patch.dict(os.environ, env, clear=True)
        p.start()
        self.addCleanup(p.stop)
        p2 = mock.patch.object(tools, "_pyosys_abc", return_value=None)
        self.pyosys = p2.start()
        self.addCleanup(p2.stop)

    def stub(self, name, text="#!/bin/sh\nexit 0\n", where=None):
        path = os.path.join(where or self.bin, name)
        with open(path, "w") as f:
            f.write(text)
        os.chmod(path, os.stat(path).st_mode | stat.S_IXUSR)
        return path

    def test_native(self):
        y = self.stub("yosys", YOSYS_STUB)
        for n in ("sby", "yosys-smtbmc", "yosys-witness", "yosys-abc", "bitwuzla", "z3", "yowasp-yosys"):
            self.stub(n)
        tc = Toolchain.discover()
        self.assertEqual((tc.yosys, tc.is_yowasp, tc.solver, tc.version), (y, False, "bitwuzla", (0, 71)))
        self.assertEqual(tc.sby, os.path.join(self.bin, "sby"))
        self.assertEqual(tc.abc, os.path.join(self.bin, "yosys-abc"))
        self.assertEqual({k: tc.env[k] for k in ("YOSYS", "SMTBMC", "WITNESS", "ABC")},
                         {"YOSYS": y, "SMTBMC": tc.smtbmc, "WITNESS": tc.witness, "ABC": tc.abc})
        self.assertEqual(tc.describe(), "yosys 0.71 (native), solver=bitwuzla, abc=yes")
        self.assertIsNone(tc.version_warning())

    def test_solver_preference(self):
        self.stub("yosys", YOSYS_STUB)
        self.stub("sby")
        self.assertIsNone(Toolchain.discover().solver)
        for exe, name in (("z3", "z3"), ("boolector", "boolector"), ("bitwuzla", "bitwuzla"), ("yices-smt2", "yices")):
            self.stub(exe)
            self.assertEqual(Toolchain.discover().solver, name)
        self.assertEqual(Toolchain.discover("z3").solver, "z3")
        self.assertEqual(Toolchain.discover("cvc5").solver, "cvc5")    # explicit choice is not second-guessed

    def test_environment_overrides(self):
        other = os.path.join(self.tmp, "other")
        os.makedirs(other)
        y = self.stub("my-yosys", YOSYS_STUB, other)
        s = self.stub("my-sby", where=other)
        a = self.stub("my-abc", where=other)
        self.stub("yosys", YOSYS_STUB)
        self.stub("sby")
        with mock.patch.dict(os.environ, {"FVLINT_YOSYS": y, "FVLINT_SBY": s, "FVLINT_ABC": a}):
            tc = Toolchain.discover()
        self.assertEqual((tc.yosys, tc.sby, tc.abc, tc.is_yowasp), (y, s, a, False))
        self.assertNotIn("SMTBMC", tc.env)                              # not found: not exported

    def test_yowasp_fallback(self):
        y = self.stub("yowasp-yosys", YOSYS_STUB)
        for n in ("yowasp-sby", "yowasp-yosys-smtbmc", "yowasp-yosys-witness", "sby"):
            self.stub(n)
        self.pyosys.return_value = "/site/pyosys/yosys-abc"
        tc = Toolchain.discover()
        self.assertEqual((tc.yosys, tc.is_yowasp), (y, True))
        self.assertEqual(tc.sby, os.path.join(self.bin, "yowasp-sby"))   # never mix with a native sby
        self.assertEqual(tc.smtbmc, os.path.join(self.bin, "yowasp-yosys-smtbmc"))
        self.assertEqual((tc.abc, tc.env["ABC"]), ("/site/pyosys/yosys-abc", "/site/pyosys/yosys-abc"))
        self.assertIn("(yowasp)", tc.describe())

    def test_missing_tools(self):
        with self.assertRaisesRegex(ToolError, "Yosys not found"):
            Toolchain.discover()
        self.stub("yosys", YOSYS_STUB)
        with self.assertRaisesRegex(ToolError, "SymbiYosys"):
            Toolchain.discover()
        self.stub("yowasp-yosys")
        os.remove(os.path.join(self.bin, "yosys"))
        with self.assertRaisesRegex(ToolError, "SymbiYosys"):        # yowasp-yosys without yowasp-sby
            Toolchain.discover()

    def test_unknown_version(self):
        self.stub("yosys", YOSYS_STUB)
        self.stub("sby")
        with mock.patch.dict(os.environ, {"STUB_VERSION": "something else"}):
            tc = Toolchain.discover()
        self.assertIsNone(tc.version)
        self.assertEqual(tc.version_warning(), "could not determine the Yosys version")
        self.assertIn("yosys ? (native)", tc.describe())
        with mock.patch.dict(os.environ, {"STUB_VERSION": "Yosys 0.99"}):
            w = Toolchain.discover().version_warning()
        self.assertIn("Yosys 0.99 has not been tested", w)
        self.assertIn("tested: 0.71", w)

    def test_yosys_that_cannot_run(self):
        self.stub("yosys", "#!/nonexistent/interpreter\n")
        self.stub("sby")
        self.assertIsNone(Toolchain.discover().version)

    def test_which(self):
        self.stub("b")
        self.assertIsNone(_which("a"))
        self.assertEqual(_which("a", "b"), os.path.join(self.bin, "b"))


class PyosysAbc(TempDirCase):
    def spec(self, *dirs):
        return types.SimpleNamespace(submodule_search_locations=list(dirs))

    def test_found(self):
        exe = self.write("pkg/yosys-abc", "#!/bin/sh\n")
        os.chmod(exe, 0o755)
        with mock.patch("importlib.util.find_spec", return_value=self.spec(self.tmp, os.path.dirname(exe))) as fs:
            self.assertEqual(_pyosys_abc(), exe)
        fs.assert_called_once_with("pyosys")

    def test_not_found(self):
        self.write("pkg/yosys-abc", "not executable")
        for ret in (None, self.spec(), self.spec(os.path.join(self.tmp, "pkg"))):
            with mock.patch("importlib.util.find_spec", return_value=ret):
                self.assertIsNone(_pyosys_abc())
        with mock.patch("importlib.util.find_spec", side_effect=ValueError):
            self.assertIsNone(_pyosys_abc())
        no_dirs = types.SimpleNamespace(submodule_search_locations=None)
        with mock.patch("importlib.util.find_spec", return_value=no_dirs):
            self.assertIsNone(_pyosys_abc())


@unittest.skipUnless(POSIX, "stub executables are shell scripts")
class Running(TempDirCase):
    def tc(self, **env):
        y = self.write("bin/yosys", YOSYS_STUB)
        os.chmod(y, 0o755)
        e = dict(os.environ, **env)
        return Toolchain(y, os.path.join(self.tmp, "bin", "sby"), None, None, None, "z3", False, env=e)

    def test_run_yosys(self):
        tc = self.tc()
        rc = tc.run_yosys("read_verilog a.v\n", self.tmp, "elab")
        self.assertEqual(rc, 0)
        with open(os.path.join(self.tmp, "elab.ys")) as f:
            self.assertEqual(f.read(), "read_verilog a.v\n")
        with open(os.path.join(self.tmp, "ran_script.txt")) as f:
            self.assertEqual(f.read(), "read_verilog a.v\n")           # Yosys was handed that script
        with open(os.path.join(self.tmp, "elab.log")) as f:
            self.assertEqual(f.read(), "stdout line\n")

    def test_run_yosys_failure(self):
        tc = self.tc(STUB_RC="3")
        with self.assertRaises(ToolError) as cm:
            tc.run_yosys("x\n", self.tmp, "elab")
        self.assertIn("elab.log.full", str(cm.exception))
        self.assertIn("stdout line", str(cm.exception))
        self.assertIn("full log line", str(cm.exception))
        self.assertEqual(tc.run_yosys("x\n", self.tmp, "elab", allow_fail=True), 3)

    def test_log_tail(self):
        p = self.write("x.log", "".join(f"l{i}\n" for i in range(30)))
        self.assertEqual(Toolchain.log_tail(p, 3), "l27\nl28\nl29\n")
        self.write("x.log.full", "f1\nf2\n")
        self.assertEqual(Toolchain.log_tail(p, 1), "l29\nf2\n")
        self.assertEqual(Toolchain.log_tail(os.path.join(self.tmp, "none.log")), "")
        os.remove(p + ".full")
        self.assertEqual(Toolchain.log_tail(p), "".join(f"l{i}\n" for i in range(15, 30)))   # default: 15 lines

    def test_slang_prefix(self):
        for mode, want in (("builtin", ""), ("plugin", "plugin -i slang\n")):
            with self.subTest(mode=mode):
                tc = self.tc(STUB_SLANG=mode)
                self.assertEqual(tc.slang_prefix(self.tmp), want)
                tc.env["STUB_SLANG"] = "none"
                self.assertEqual(tc.slang_prefix(self.tmp), want)          # cached
        with self.assertRaisesRegex(ToolError, "read_slang"):
            self.tc(STUB_SLANG="none").slang_prefix(self.tmp)

    def sby_stub(self, body):
        s = self.write("bin/sby", "#!/bin/sh\n" + body)
        os.chmod(s, 0o755)
        tc = self.tc()
        tc.sby = s
        return tc

    def test_run_sby_exit_code_and_arguments(self):
        tc = self.sby_stub('echo "$@" > args.txt; pwd > cwd.txt; exit 2\n')
        job = os.path.join(self.tmp, "job")
        os.makedirs(job)
        self.assertEqual(tc.run_sby(os.path.join(job, "run.sby"), job, 10), 2)
        with open(os.path.join(job, "args.txt")) as f:
            self.assertEqual(f.read().strip(), "-f run.sby")
        with open(os.path.join(job, "cwd.txt")) as f:
            self.assertEqual(os.path.realpath(f.read().strip()), os.path.realpath(job))
        self.assertEqual(tc.run_sby("run.sby", job, None), 2)            # no timeout at all

    def test_run_sby_backstop_kills_the_process_group(self):
        tc = self.sby_stub("sleep 60 &\necho $! > child.pid\nsleep 60\n")
        tc.SBY_GRACE = 0.0
        pidfile = os.path.join(self.tmp, "child.pid")
        # Under load (parallel mutation runs) the stub may not reach the line
        # that starts the grandchild before the timeout: then nothing is left
        # to check, so try again with more time.
        for timeout in (0.5, 1, 2, 4, 8):
            t0 = time.time()
            self.assertEqual(tc.run_sby("run.sby", self.tmp, timeout), -1)
            self.assertLess(time.time() - t0, 20 + timeout)
            if os.path.exists(pidfile) and os.path.getsize(pidfile):
                break
        else:
            self.fail("the stub never started its child")
        with open(pidfile) as f:
            pid = int(f.read())
        for _ in range(50):                                             # the grandchild goes too
            if not _alive(pid):
                break
            time.sleep(0.1)
        else:
            self.fail("grandchild process survived")


if __name__ == "__main__":
    unittest.main()
