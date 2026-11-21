# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""End-to-end regression: every case in tests/regress/manifest.toml (one
subtest per case and engine) plus a soundness-fuzzer smoke run.  Needs the
toolchain (Yosys, SymbiYosys, a solver; ABC for the PDR cases).

    python -m unittest -v tests.test_regress
    FVLINT_FUZZ_SEEDS=40 FVLINT_BUDGET_SCALE=2 python -m unittest tests.test_regress
"""

from __future__ import annotations

import os
import sys
import unittest
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "src"))

from fvlint import fuzz, regress                  # noqa: E402
from fvlint.tools import Toolchain, ToolError     # noqa: E402

OUT = os.path.join(HERE, "_out")
MANIFEST = os.path.join(HERE, "regress", "manifest.toml")


def _tools():
    try:
        return Toolchain.discover()
    except ToolError:
        return None


TOOLS = _tools()


@unittest.skipIf(TOOLS is None, "Yosys/SymbiYosys not installed")
class Regression(unittest.TestCase):
    def test_manifest(self):
        cases = regress.load_manifest(MANIFEST)
        runs = [(c, e) for c in cases for e in c.engines]
        scale = float(os.environ.get("FVLINT_BUDGET_SCALE", "1"))
        jobs = int(os.environ.get("FVLINT_TEST_JOBS", max(1, (os.cpu_count() or 2) // 2)))
        with ThreadPoolExecutor(max_workers=jobs) as ex:
            outcomes = list(ex.map(lambda ce: regress.run_case(ce[0], ce[1], os.path.join(OUT, "regress"),
                                                               scale, bool(TOOLS.abc)), runs))
        for o in outcomes:
            with self.subTest(case=o.case.name, engine=o.engine):
                if o.skipped:
                    continue
                self.assertTrue(o.ok, "\n".join(o.problems))

    def test_fuzz_soundness(self):
        n = int(os.environ.get("FVLINT_FUZZ_SEEDS", "8"))
        s = fuzz.run(range(1, n + 1), os.path.join(OUT, "fuzz"))
        self.assertEqual(s["problems"], [])
        self.assertEqual(s["seeds"], n)


if __name__ == "__main__":
    unittest.main()
