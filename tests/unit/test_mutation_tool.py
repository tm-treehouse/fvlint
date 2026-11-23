# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""tests/unit/mutation.py: how mutation sites are found and named, and that
the committed baseline still names code that exists."""

from __future__ import annotations

import ast
import json
import os
import tempfile
import unittest

from . import mutation
from .support import TempDirCase

SRC = '''\
LIMIT = 4


def deco(f):
    return f


def f(x, y=LIMIT + 1):
    if x > 0:
        return 1
    return 0


class C:
    @deco
    def m(self, x):
        def inner():
            return x > 0
        return inner() and x > 0
'''


class Sites(TempDirCase):
    def sites(self, text):
        _, ms = mutation.mutants(self.write("mod.py", text))
        return ms

    def keys(self, text):
        return {mutation._site(dict(m, module="mod")) for m in self.sites(text)}

    def test_scopes(self):
        scope = {(m["line"], m["desc"]): m["scope"] for m in self.sites(SRC)}
        self.assertEqual(scope[(1, "4 -> 5")], "<module>")
        self.assertEqual(scope[(8, "Add -> Sub")], "f")                 # a default belongs to its def
        self.assertEqual(scope[(9, "Gt -> GtE")], "f")
        self.assertEqual(scope[(18, "Gt -> GtE")], "C.m.inner")
        self.assertEqual(scope[(19, "Gt -> GtE")], "C.m")
        self.assertEqual(scope[(19, "And -> Or")], "C.m")

    def test_every_site_has_its_own_key(self):
        text = SRC + "\n\ndef g(x):\n    if x > 0:\n        return 1\n    if x > 0:\n        return 1\n"
        ms = self.sites(text)
        self.assertEqual(len({mutation._site(dict(m, module="mod")) for m in ms}), len(ms))
        self.assertEqual([m["nth"] for m in ms if m["scope"] == "g" and m["desc"] == "Gt -> GtE"], [0, 1])

    def test_keys_survive_edits_elsewhere(self):
        before = self.keys(SRC)
        # The same code added to another function, at module level before f,
        # and later in f itself: the original sites keep their keys.
        after = SRC.replace("def deco(f):", "if LIMIT > 0:\n    pass\n\n\ndef deco(f):")
        after = after.replace("    return 0\n", "    if x > 0:\n        return 2\n    return 0\n")
        after += "\n\ndef g(x):\n    if x > 0:\n        return 1\n"
        self.assertLessEqual(before, self.keys(after))

    def test_nth_follows_source_order(self):
        # ast.walk visits the nested comparison first; nth still counts from the top.
        text = "def f(x):\n    if x > 0:\n        if x > 0:\n            return 1\n"
        ms = [m for m in self.sites(text) if m["desc"] == "Gt -> GtE"]
        self.assertEqual(sorted((m["line"], m["nth"]) for m in ms), [(2, 0), (3, 1)])

    def test_mutate_changes_one_site(self):
        ms = self.sites(SRC)
        (i,) = [m["index"] for m in ms if m["scope"] == "f" and m["desc"] == "Gt -> GtE"]
        out = mutation.mutate(SRC, i)
        self.assertEqual(out.count(">="), 1)
        self.assertIn("if x >= 0:", out)
        self.assertEqual(ast.dump(ast.parse(mutation.mutate(SRC, i))), ast.dump(ast.parse(out)))
        with self.assertRaises(IndexError):
            mutation.mutate(SRC, len(ms))


class Baseline(TempDirCase):
    ENTRY = {"module": "m", "scope": "f", "code": "x", "desc": "d", "nth": 0, "reason": "equivalent: why"}

    def test_load(self):
        p = self.write_json("b.json", {"accepted": [self.ENTRY]})
        self.assertEqual(mutation.load_baseline(p), {("m", "f", "x", "d", 0): "equivalent: why"})
        self.assertEqual(mutation.load_baseline(os.path.join(self.tmp, "missing.json")), {})

    def test_duplicates_and_missing_reasons_are_errors(self):
        p = self.write_json("b.json", {"accepted": [self.ENTRY, dict(self.ENTRY, reason="again")]})
        with self.assertRaisesRegex(ValueError, "duplicate"):
            mutation.load_baseline(p)
        p = self.write_json("c.json", {"accepted": [dict(self.ENTRY, reason=" ")]})
        with self.assertRaisesRegex(ValueError, "without a reason"):
            mutation.load_baseline(p)

    @unittest.skipIf(os.environ.get("FVLINT_MUTATION_RUN"), "a property of the checkout, not of a mutant")
    def test_committed_baseline_names_existing_code(self):
        # An edit that changes or moves an accepted line fails here, at once,
        # instead of in the weekly mutation run.
        path = os.path.join(os.path.dirname(__file__), "mutation_baseline.json")
        baseline = mutation.load_baseline(path)
        modules = sorted({k[0] for k in baseline})
        missing = sorted(set(baseline) - mutation.all_sites(modules))
        self.assertEqual(missing, [], "baseline entries whose code changed; re-judge them with mutation.py")
        with open(path) as f:
            for e in json.load(f)["accepted"]:
                self.assertRegex(e["reason"], r"^(equivalent|accepted): ")


class Workers(TempDirCase):
    # A suite that writes a file to a relative path and fails if it finds one
    # there already, and that checks where temporary files go.
    PROBE = """\
import os
import tempfile
import unittest


class Probe(unittest.TestCase):
    def test_relative_files_are_private(self):
        self.assertFalse(os.path.exists("probe.txt"), os.getcwd())
        with open("probe.txt", "w") as f:
            f.write("x")
        self.assertEqual(os.path.realpath(tempfile.gettempdir()), os.path.realpath(os.getcwd()))
"""

    def worker(self, name):
        d = os.path.join(self.tmp, name)
        os.makedirs(os.path.join(d, "src", "fvlint"))
        tests = os.path.join(self.tmp, f"{name}_tests")
        self.write(f"{name}_tests/unit/__init__.py", "")
        self.write(f"{name}_tests/unit/test_probe.py", self.PROBE)
        os.symlink(tests, os.path.join(d, "tests"))                 # as main() links the checkout's tests
        return d

    def test_runs_do_not_share_a_working_directory(self):
        # Two workers, and one worker twice: every run starts without the
        # others' relative files (parallel workers once shared the checkout).
        ws = [self.worker("w0"), self.worker("w1")]
        for w in ws + ws[:1]:
            run = tempfile.mkdtemp(dir=w, prefix="tmp")
            self.assertEqual(mutation._run_tests(w, 60, run)[0], "survived", w)
        self.assertFalse(os.path.exists(os.path.join(mutation.ROOT, "probe.txt")))


if __name__ == "__main__":
    unittest.main()
