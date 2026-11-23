# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Files of the repository that must agree with each other."""

from __future__ import annotations

import os
import re
import unittest

ROOT = os.path.join(os.path.dirname(__file__), "..", "..")


def read(rel: str) -> str:
    with open(os.path.join(ROOT, rel)) as f:
        return f.read()


class Pins(unittest.TestCase):
    def test_action_installs_the_toolchain_ci_runs(self):
        # The Action's default OSS CAD Suite build is the one fvlint's own CI
        # tests with; the two can't drift apart.
        action = read("action.yml")
        m = re.search(r"\n  oss-cad-suite-version:\n(?:    .*\n)*?    default: \"([^\"]+)\"\n", action)
        self.assertIsNotNone(m, "no default for the oss-cad-suite-version input in action.yml")
        ci = read(".github/workflows/ci.yml")
        pinned = re.findall(r"uses: YosysHQ/setup-oss-cad-suite@\S+\n\s+with:\n\s+version: \"([^\"]+)\"", ci)
        self.assertEqual(pinned, [m.group(1)])
        self.assertIn(f"build of {m.group(1)}", ci)                    # the comment next to the pin

    def test_ci_runs_the_action_from_the_checkout(self):
        ci = read(".github/workflows/ci.yml")
        self.assertEqual(ci.count("      - uses: ./\n"), 2)
        for path in re.findall(r"config: (\S+)", ci):
            self.assertTrue(os.path.exists(os.path.join(ROOT, path)), path)


if __name__ == "__main__":
    unittest.main()
