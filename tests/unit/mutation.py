# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Mutation testing for the unit tests.

Plants one small bug at a time in a copy of src/fvlint (a flipped
comparison, a swapped operator, an off-by-one constant, a negated condition,
a dropped `break`, ...), runs the unit tests against the copy, and reports
every mutant the tests did not notice.  A surviving mutant is either a gap in
the tests or an *equivalent* mutant (a change that cannot alter behaviour);
survivors are listed so a person can tell which.

    python tests/unit/mutation.py                     # all modules
    python tests/unit/mutation.py detect cone -j 4    # some modules
    python tests/unit/mutation.py --list              # count mutants only

Survivors that are equivalent or accepted are listed, each with a reason, in
mutation_baseline.json.  An entry names the module, the enclosing function
(or class, or <module>), the line of code and the change, plus which
occurrence it is among identical ones in that function, in source order; so
edits elsewhere in the module, or later in the same function, leave it
pointing at the same site.  The report separates new survivors from
accepted ones and lists entries that are now killed or whose code is gone;
--strict fails on any of those.  With --json, finished mutants are also
appended to JSON.partial as they complete, and a rerun resumes from it as
long as no source or test file changed.  Lines ending in
`# pragma: no mutate` are skipped.  Needs no toolchain.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import os
import queue
import shutil
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
PKG = os.path.join(ROOT, "src", "fvlint")

CMP = {ast.Lt: ast.LtE, ast.LtE: ast.Lt, ast.Gt: ast.GtE, ast.GtE: ast.Gt, ast.Eq: ast.NotEq,
       ast.NotEq: ast.Eq, ast.In: ast.NotIn, ast.NotIn: ast.In, ast.Is: ast.IsNot, ast.IsNot: ast.Is}
BIN = {ast.Add: ast.Sub, ast.Sub: ast.Add, ast.Mult: ast.FloorDiv, ast.FloorDiv: ast.Mult,
       ast.LShift: ast.RShift, ast.RShift: ast.LShift, ast.BitAnd: ast.BitOr, ast.BitOr: ast.BitAnd,
       ast.BitXor: ast.BitOr, ast.Mod: ast.FloorDiv}
BOOL = {ast.And: ast.Or, ast.Or: ast.And}


def _skip_lines(text: str) -> set:
    return {i + 1 for i, line in enumerate(text.splitlines()) if line.rstrip().endswith("# pragma: no mutate")}


def _main_guard(node) -> bool:
    return (isinstance(node, ast.If) and isinstance(node.test, ast.Compare)
            and isinstance(node.test.left, ast.Name) and node.test.left.id == "__name__")


def _scopes(tree: ast.AST) -> dict:
    """id(node) -> qualified name of the innermost function or class whose
    definition contains it ("Engine._grow", "main.one"), or "<module>".
    Decorators, base classes and argument defaults count as part of the
    definition they belong to."""
    out = {}

    def visit(node, scope):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            scope = node.name if scope == "<module>" else f"{scope}.{node.name}"
        out[id(node)] = scope
        for child in ast.iter_child_nodes(node):
            visit(child, scope)
    visit(tree, "<module>")
    return out


def _sites(tree: ast.AST, skip: set):
    """Yield (node, kind, description, apply) for every mutation site, in a
    deterministic walk order.  apply(node) mutates the node in place."""
    docstrings = set()
    for n in ast.walk(tree):
        if isinstance(n, (ast.Module, ast.FunctionDef, ast.ClassDef, ast.AsyncFunctionDef)) and n.body:
            first = n.body[0]
            if isinstance(first, ast.Expr) and isinstance(first.value, ast.Constant):
                docstrings.add(id(first.value))
    in_fstring = set()
    for n in ast.walk(tree):
        if isinstance(n, ast.JoinedStr):
            for m in ast.walk(n):
                in_fstring.add(id(m))
    guarded = set()        # never-evaluated or user-facing-only code: __main__ guards, annotations, help text
    for n in ast.walk(tree):
        subtrees = []
        if _main_guard(n):
            subtrees.append(n)
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)) and n.returns is not None:
            subtrees.append(n.returns)
        if isinstance(n, ast.arg) and n.annotation is not None:
            subtrees.append(n.annotation)
        if isinstance(n, ast.AnnAssign):
            subtrees.append(n.annotation)
        if isinstance(n, ast.keyword) and n.arg in ("help", "description"):
            subtrees.append(n.value)
        for t in subtrees:
            for m in ast.walk(t):
                guarded.add(id(m))

    def swap(table, attr, idx=None):
        def apply(node):
            if idx is None:
                setattr(node, attr, table[type(getattr(node, attr))]())
            else:
                getattr(node, attr)[idx] = table[type(getattr(node, attr)[idx])]()
        return apply

    for node in ast.walk(tree):
        line = getattr(node, "lineno", None)
        if line in skip or id(node) in guarded:
            continue
        if isinstance(node, ast.Compare):
            for i, op in enumerate(node.ops):
                if type(op) in CMP:
                    yield node, "compare", f"{type(op).__name__} -> {CMP[type(op)].__name__}", swap(CMP, "ops", i)
        elif isinstance(node, ast.BinOp) and type(node.op) in BIN and id(node) not in in_fstring:
            yield node, "arith", f"{type(node.op).__name__} -> {BIN[type(node.op)].__name__}", swap(BIN, "op")
        elif isinstance(node, ast.AugAssign) and type(node.op) in BIN:
            yield node, "arith", f"{type(node.op).__name__}= -> {BIN[type(node.op)].__name__}=", swap(BIN, "op")
        elif isinstance(node, ast.BoolOp):
            yield node, "boolean", f"{type(node.op).__name__} -> {BOOL[type(node.op)].__name__}", swap(BOOL, "op")
        elif isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            yield node, "boolean", "drop 'not'", _replace_with_operand
        elif isinstance(node, (ast.If, ast.While, ast.IfExp)):
            def negate(n):
                n.test = ast.UnaryOp(op=ast.Not(), operand=n.test)
            yield node, "condition", "negate condition", negate
        elif isinstance(node, (ast.Break, ast.Continue)):
            yield node, "control", f"{type(node).__name__.lower()} -> pass", None
        elif isinstance(node, ast.Constant) and id(node) not in docstrings and id(node) not in in_fstring:
            v = node.value
            if isinstance(v, bool):
                def flip(n):
                    n.value = not n.value
                yield node, "constant", f"{v} -> {not v}", flip
            elif isinstance(v, int):
                def inc(n):
                    n.value = n.value + 1
                yield node, "constant", f"{v} -> {v + 1}", inc
            elif isinstance(v, str) and 0 < len(v) <= 16 and "\n" not in v:
                def mangle(n):           # prepended: argparse would accept an appended flag as a prefix
                    n.value = "\x01" + n.value
                yield node, "string", f"{v!r} -> '\\x01'+{v!r}", mangle


class _NotRemover(ast.NodeTransformer):
    def __init__(self, target):
        self.target = target

    def visit_UnaryOp(self, node):
        self.generic_visit(node)
        return node.operand if node is self.target else node


class _Replacer(ast.NodeTransformer):
    def __init__(self, target):
        self.target = target

    def visit_Break(self, node):
        return ast.Pass() if node is self.target else node

    visit_Continue = visit_Break


def _replace_with_operand(node):     # marker; handled in mutate()
    raise AssertionError


def mutants(path: str):
    """(text, sites): every mutation site of the file, with the fields that
    identify it in the baseline (scope, code, desc, nth) and where it is."""
    with open(path) as f:
        text = f.read()
    tree = ast.parse(text)
    lines, scopes = text.splitlines(), _scopes(tree)
    out = []
    for i, (node, kind, desc, _) in enumerate(_sites(tree, _skip_lines(text))):
        line = getattr(node, "lineno", 0)
        out.append({"index": i, "line": line, "col": getattr(node, "col_offset", 0), "kind": kind, "desc": desc,
                    "code": lines[line - 1].strip() if line else "", "scope": scopes[id(node)]})
    groups = {}
    for m in sorted(out, key=lambda m: (m["line"], m["col"], m["index"])):     # source order
        k = (m["scope"], m["code"], m["desc"])
        m["nth"] = groups[k] = groups.get(k, -1) + 1
    return text, out


def mutate(text: str, index: int) -> str:
    tree = ast.parse(text)
    for i, (node, kind, desc, apply) in enumerate(_sites(tree, _skip_lines(text))):
        if i != index:
            continue
        if apply is _replace_with_operand:
            tree = _NotRemover(node).visit(tree)
        elif apply is None:
            tree = _Replacer(node).visit(tree)
        else:
            apply(node)
        ast.fix_missing_locations(tree)
        return ast.unparse(tree) + "\n"
    raise IndexError(index)


def _run_tests(src_root: str, timeout: float, tmpdir: str) -> tuple[str, float]:
    """Run the unit suite against src_root.  Temporary files go to tmpdir,
    which the caller removes, so a suite killed by the timeout leaks nothing."""
    env = dict(os.environ, FVLINT_SRC=src_root, FVLINT_MUTATION_RUN="1", PYTHONDONTWRITEBYTECODE="1",
               TMPDIR=tmpdir)
    t0 = time.time()
    try:
        p = subprocess.run([sys.executable, "-m", "unittest", "discover", "-s", "tests/unit", "-t", ".", "-f", "-q"],
                           cwd=ROOT, env=env, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return "timeout", time.time() - t0
    return ("survived" if p.returncode == 0 else "killed"), time.time() - t0


def _tree_digest() -> str:
    """Digest of everything a verdict depends on: all sources and the tests."""
    h = hashlib.sha1()
    for top in (PKG, os.path.join(ROOT, "tests", "unit")):
        for dp, dns, fns in sorted(os.walk(top)):
            dns[:] = sorted(d for d in dns if d != "__pycache__")
            for fn in sorted(fns):
                if fn.endswith((".py", ".v", ".sv", ".json", ".vcd", ".yw")) and not fn.endswith(".partial"):
                    with open(os.path.join(dp, fn), "rb") as f:
                        h.update(fn.encode() + f.read())
    return h.hexdigest()[:12]


def _site(r) -> tuple:
    """How a mutant is matched against the baseline: by module, enclosing
    function, code and change (and which occurrence of that in the
    function), not by line number."""
    return (r["module"], r["scope"], r["code"], r["desc"], r["nth"])


def load_baseline(path: str) -> dict:
    """Accepted survivors: {(module, scope, code, desc, nth): reason}."""
    if not path or not os.path.exists(path):
        return {}
    with open(path) as f:
        entries = json.load(f)["accepted"]
    out = {}
    for e in entries:
        k = _site(e)
        if k in out:
            raise ValueError(f"{path}: duplicate entry {k}")
        if not e.get("reason", "").strip():
            raise ValueError(f"{path}: entry without a reason {k}")
        out[k] = e["reason"]
    return out


def all_sites(names) -> set:
    """Baseline keys of every mutation site in the given modules."""
    return {_site(dict(m, module=n)) for n in names for m in mutants(os.path.join(PKG, f"{n}.py"))[1]}


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("modules", nargs="*", help="module names (default: all)")
    ap.add_argument("-j", "--jobs", type=int, default=os.cpu_count() or 2)
    ap.add_argument("--kinds", help="comma-separated mutation kinds (compare,arith,boolean,condition,control,"
                                    "constant,string)")
    ap.add_argument("--timeout", type=float, default=60,
                    help="seconds per test run; a run that times out is retried once with twice the time")
    ap.add_argument("--json", help="write the full report here")
    ap.add_argument("--baseline", default=os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                       "mutation_baseline.json"),
                    help="accepted survivors, each with a reason (default: %(default)s)")
    ap.add_argument("--strict", action="store_true", help="exit 1 if a survivor is not in the baseline")
    ap.add_argument("--list", action="store_true", help="count mutants and exit")
    args = ap.parse_args(argv)

    names = args.modules or sorted(f[:-3] for f in os.listdir(PKG) if f.endswith(".py"))
    kinds = set(args.kinds.split(",")) if args.kinds else None
    baseline = load_baseline(args.baseline)        # fail early on a malformed baseline
    digest = _tree_digest()
    work, texts, sites = [], {}, set()
    for name in names:
        text, ms = mutants(os.path.join(PKG, f"{name}.py"))
        texts[name] = text
        sites |= {_site(dict(m, module=name)) for m in ms}
        work += [(name, dict(m, module=name, key=f"{name}:{m['index']}:{digest}")) for m in ms
                 if kinds is None or m["kind"] in kinds]
    if args.list:
        for name in names:
            print(f"{name:12} {sum(1 for n, _ in work if n == name)}")
        print(f"{'total':12} {len(work)}")
        return 0

    # Resume an interrupted run, but only for verdicts made on identical sources and tests.
    partial = args.json + ".partial" if args.json else None
    previous = {}
    if partial and os.path.exists(partial):
        with open(partial) as f:
            for row in f:
                if row.strip():
                    r = json.loads(row)
                    previous[r["key"]] = r
    resumed = [previous[m["key"]] for _, m in work if m["key"] in previous]
    if resumed:
        print(f"  resuming: {len(resumed)} mutants already judged", file=sys.stderr)
    work = [(n, m) for n, m in work if m["key"] not in previous]

    tmp = tempfile.mkdtemp(prefix="fvlint_mut_")
    workers = queue.Queue()
    for w in range(max(1, args.jobs)):
        d = os.path.join(tmp, f"w{w}")
        shutil.copytree(os.path.join(ROOT, "src"), os.path.join(d, "src"),
                        ignore=shutil.ignore_patterns("__pycache__"))
        os.symlink(os.path.join(ROOT, "tests"), os.path.join(d, "tests"))   # for paths relative to the package
        workers.put(d)

    def run_suite(d, timeout):
        t = tempfile.mkdtemp(dir=d, prefix="tmp")
        try:
            return _run_tests(os.path.join(d, "src"), timeout, t)
        finally:
            shutil.rmtree(t, ignore_errors=True)

    base, _ = run_suite(workers.queue[0], args.timeout)
    if base != "survived":
        print("the unit tests fail on the unmodified sources; fix that first", file=sys.stderr)
        shutil.rmtree(tmp, ignore_errors=True)
        return 2

    done, t_start, log_lock = [0], time.time(), threading.Lock()

    def record(r):
        if partial:
            with log_lock, open(partial, "a") as f:
                f.write(json.dumps(r) + "\n")
        return r

    def one(item):
        name, m = item
        d = workers.get()
        target = os.path.join(d, "src", "fvlint", f"{name}.py")
        try:
            try:
                code = mutate(texts[name], m["index"])
            except (ValueError, SyntaxError, IndexError) as e:      # unparseable mutant: not a test result
                return record(dict(m, outcome="invalid", error=repr(e)))
            with open(target, "w") as f:
                f.write(code)
            outcome, secs = run_suite(d, args.timeout)
            if outcome == "timeout":                                # machine load, or a real hang?
                outcome, secs = run_suite(d, 2 * args.timeout)
            return record(dict(m, outcome=outcome, seconds=round(secs, 2)))
        finally:
            with open(target, "w") as f:
                f.write(texts[name])
            workers.put(d)
            with log_lock:
                done[0] += 1
                if done[0] % 100 == 0:
                    print(f"  {done[0]}/{len(work)} mutants, {time.time() - t_start:.0f}s", file=sys.stderr)

    with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as ex:
        results = resumed + list(ex.map(one, work))
    shutil.rmtree(tmp, ignore_errors=True)

    valid = [r for r in results if r["outcome"] != "invalid"]
    survivors = [r for r in valid if r["outcome"] == "survived"]
    new = [r for r in survivors if _site(r) not in baseline]
    judged = {_site(r) for r in valid}
    surviving_sites = {_site(r) for r in survivors}
    stale = [k for k in baseline if k in judged and k not in surviving_sites]
    orphaned = [k for k in baseline if k[0] in names and k not in sites]

    print(f"{'module':12} {'mutants':>8} {'killed':>7} {'(hangs)':>8} {'accepted':>9} {'new':>5} {'score':>6}")
    for name in names + ["total"]:
        rs = [r for r in valid if name == "total" or r["module"] == name]
        if not rs:
            continue
        killed = sum(r["outcome"] in ("killed", "timeout") for r in rs)
        hangs = sum(r["outcome"] == "timeout" for r in rs)
        surv = [r for r in rs if r["outcome"] == "survived"]
        accepted = sum(_site(r) in baseline for r in surv)
        print(f"{name:12} {len(rs):8} {killed:7} {hangs:8} {accepted:9} {len(surv) - accepted:5} "
              f"{100 * killed / len(rs):5.1f}%")
    print("\n(score: share of mutants a test failed on; hangs are mutants that never finished, counted as caught;"
          "\n accepted: survivors listed with a reason in the baseline)")
    if new:
        print(f"\n{len(new)} survivors not in the baseline (a missing test, or add them with a reason):")
        for r in new:
            print(f"  {r['module']}.py:{r['line']}: [{r['kind']}] {r['desc']}    {r['code'][:90]}")
    if stale:
        print(f"\n{len(stale)} baseline entries are killed now; remove them:")
        for module, scope, code, desc, nth in stale:
            print(f"  {module}.py {scope} #{nth}: {desc}    {code[:90]}")
    if orphaned:
        print(f"\n{len(orphaned)} baseline entries match no code any more (it was changed); re-judge them:")
        for module, scope, code, desc, nth in orphaned:
            print(f"  {module}.py {scope} #{nth}: {desc}    {code[:90]}")
    if args.json:
        with open(args.json, "w") as f:
            json.dump(results, f, indent=1)
        if os.path.exists(partial):
            os.remove(partial)
    return 1 if args.strict and (new or stale or orphaned) else 0


if __name__ == "__main__":
    sys.exit(main())
