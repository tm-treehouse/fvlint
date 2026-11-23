# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Project files: several fvlint configurations in one TOML file.

    fvlint --config fvlint.toml [NAME...] [OPTION...]

runs every configuration (or the ones named), each into OUT/NAME, and exits
with the worst status: 2 if any configuration couldn't run, else 1 if any
has a finding, else 0.  Options on the command line apply to every
configuration and win over the file.  Example:

    out = "fvlint_out"                 # relative to the current directory, like -o

    [defaults]                         # shared by every configuration
    jobs = 2

    [config.default]
    top = "picorv32"
    files = ["picorv32.v"]             # paths are relative to this file
    waivers = "fvlint/waivers/default.txt"

    [config.irq]
    top = "picorv32"
    files = ["picorv32.v"]
    params = { ENABLE_IRQ = 1, ENABLE_IRQ_QREGS = 1 }
    assume = "fvlint/assume/irq.sv"
    waivers = "fvlint/waivers/irq.txt"
"""

from __future__ import annotations

import os
import sys
import tomllib

# key -> (option, kind).  kinds: str, int, num, flag, path, paths, defs, list, raw.
KEYS = {
    "top": ("--top", "str"),
    "files": (None, "paths"),
    "filelists": ("-f", "paths"),
    "filelists_rel": ("-F", "paths"),
    "include": ("-I", "paths"),
    "defines": ("-D", "defs"),
    "params": ("-P", "defs"),
    "libs": ("--lib", "paths"),
    "frontend": ("--frontend", "str"),
    "reset": ("--reset", "str"),
    "no_reset": ("--no-reset", "flag"),
    "reset_anytime": ("--reset-anytime", "flag"),
    "reset_cycles": ("--reset-cycles", "int"),
    "uninit": ("--uninit", "str"),
    "assume": ("--assume", "path"),
    "waivers": ("--waivers", "path"),
    "recheck_waived": ("--recheck-waived", "flag"),
    "engine": ("--engine", "str"),
    "solver": ("--solver", "str"),
    "max_level": ("--max-level", "int"),
    "depth": ("--depth", "int"),
    "timeout": ("--timeout", "num"),
    "pdr_timeout": ("--pdr-timeout", "num"),
    "horizon": ("--horizon", "cycles"),
    "checks": ("--checks", "list"),
    "fail_on": ("--fail-on", "str"),
    "jobs": ("-j", "int"),
    "args": (None, "raw"),
}
TOP_KEYS = {"out", "defaults", "config"}


class ConfigError(Exception):
    pass


def _strs(key, v) -> list:
    if isinstance(v, str):
        return [v]
    if isinstance(v, list) and all(isinstance(x, str) for x in v):
        return list(v)
    raise ConfigError(f"{key}: expected a string or a list of strings")


def entry_argv(entry: dict, base: str) -> list:
    """fvlint command-line arguments for one configuration; paths in it are
    relative to `base` (the project file's directory)."""
    unknown = sorted(set(entry) - set(KEYS))
    if unknown:
        raise ConfigError(f"unknown key(s) {', '.join(unknown)}; known: {', '.join(sorted(KEYS))}")
    if "top" not in entry:
        raise ConfigError("no top")
    path = lambda p: os.path.normpath(os.path.join(base, os.path.expanduser(p)))  # noqa: E731
    argv, files = [], []
    for key, value in entry.items():
        opt, kind = KEYS[key]
        if kind == "flag":
            if not isinstance(value, bool):
                raise ConfigError(f"{key}: expected true or false")
            argv += [opt] if value else []
        elif kind in ("str", "int", "num", "cycles"):
            ok = {"str": (str,), "int": (int,), "num": (int, float), "cycles": (int, str)}[kind]
            if isinstance(value, bool) or not isinstance(value, ok):
                raise ConfigError(f"{key}: expected {'a number' if kind != 'str' else 'a string'}")
            argv += [opt, str(value)]
        elif kind == "path":
            if not isinstance(value, str):
                raise ConfigError(f"{key}: expected a path")
            argv += [opt, path(value)]
        elif kind == "paths":
            ps = [path(p) for p in _strs(key, value)]
            if opt is None:
                files += ps
            else:
                for p in ps:
                    argv += [opt, p]
        elif kind == "defs":
            if isinstance(value, dict):
                items = []
                for k, v in value.items():
                    if isinstance(v, bool):
                        v = int(v)
                    if not isinstance(v, (int, str)):
                        raise ConfigError(f"{key}.{k}: expected a number or a string")
                    items.append(f"{k}={v}")
            else:
                items = _strs(key, value)
            for it in items:
                argv += [opt, it]
        elif kind == "list":
            argv += [opt, ",".join(_strs(key, value))]
        else:                                                   # raw command-line arguments
            argv += _strs(key, value)
    return argv + files


def _split(argv: list) -> tuple:
    """(project file, configuration names, other arguments) from the
    command line.  Option arity comes from fvlint's own parser, so a value
    such as `--fail-on unknown` is not taken for a name."""
    from .cli import build_parser
    takes_value = {}
    for action in build_parser()._actions:
        for s in action.option_strings:
            takes_value[s] = action.nargs != 0
    path, names, rest = None, [], []
    it = iter(argv)
    for a in it:
        if a == "--config":
            path = next(it, None)
        elif a.startswith("--config="):
            path = a.split("=", 1)[1]
        elif a == "--":
            rest += list(it)
        elif a.startswith("-") and a != "-":
            rest.append(a)
            if a.startswith("--"):
                needs_next = takes_value.get(a.split("=", 1)[0], False) and "=" not in a
            else:
                needs_next = len(a) == 2 and takes_value.get(a, False)   # -j4: the value is attached
            if needs_next:
                v = next(it, None)
                if v is not None:
                    rest.append(v)
        else:
            names.append(a)
    return path, names, rest


def _out_root(rest: list, data: dict) -> tuple:
    """The output root: -o/--out on the command line, else the file's `out`,
    else fvlint_out.  Returns (root, the other arguments)."""
    root, others = None, []
    it = iter(rest)
    for a in it:
        if a in ("-o", "--out"):
            root = next(it, root)
        elif a.startswith("--out="):
            root = a.split("=", 1)[1]
        elif a.startswith("-o") and len(a) > 2:
            root = a[2:]
        else:
            others.append(a)
    if root is None:
        root = data.get("out", "fvlint_out")
        if not isinstance(root, str):
            raise ConfigError("out: expected a path")
    return root, others


def load(path: str) -> dict:
    try:
        with open(path, "rb") as f:
            data = tomllib.load(f)
    except OSError as e:
        raise ConfigError(str(e)) from None
    except tomllib.TOMLDecodeError as e:
        raise ConfigError(f"not valid TOML: {e}") from None
    unknown = sorted(set(data) - TOP_KEYS)
    if unknown:
        raise ConfigError(f"unknown top-level key(s) {', '.join(unknown)}; known: {', '.join(sorted(TOP_KEYS))}")
    configs = data.get("config")
    if not isinstance(configs, dict) or not configs or not all(isinstance(v, dict) for v in configs.values()):
        raise ConfigError("no configurations: add at least one [config.NAME] table")
    if not isinstance(data.get("defaults", {}), dict):
        raise ConfigError("defaults: expected a table")
    return data


def run_config(argv: list) -> int:
    from . import cli
    path, names, rest = _split(argv)
    if not path:
        print("fvlint: --config needs a file", file=sys.stderr)
        return 2
    try:
        data = load(path)
        root, extra = _out_root(rest, data)
    except ConfigError as e:
        print(f"fvlint: {path}: {e}", file=sys.stderr)
        return 2
    configs = data["config"]
    missing = [n for n in names if n not in configs]
    if missing:
        print(f"fvlint: {path}: no configuration {', '.join(missing)}; there are: {', '.join(configs)}",
              file=sys.stderr)
        return 2
    base = os.path.dirname(os.path.abspath(path))
    rc = 0
    for name in names or list(configs):
        try:
            run_argv = entry_argv({**data.get("defaults", {}), **configs[name]}, base)
        except ConfigError as e:
            print(f"fvlint: {path}: config.{name}: {e}", file=sys.stderr)
            rc = 2
            continue
        print(f"=== fvlint: {name}", file=sys.stderr)
        sys.stderr.flush()
        try:
            r = cli.main(run_argv + ["-o", os.path.join(root, name), "--run-name", name] + extra)
        except SystemExit as e:                                 # an argument error in this configuration
            r = e.code if isinstance(e.code, int) else 2
        rc = max(rc, r)                                         # 2 (couldn't run) > 1 (findings) > 0
    return rc
