# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Elaborate the user's RTL with Yosys into the netlists fvlint analyses."""

from __future__ import annotations

import json
import os
import re
import shlex
import shutil
from dataclasses import dataclass, field

from .tools import IDENT, Toolchain, ToolError, yosys_arg


# Simulator options in .f files that take a separate argument fvlint ignores.
_ARG_OPTIONS = {"-y", "-timescale", "-top", "-l", "-o", "-L", "-work", "-sverilog_ext", "-libext"}


@dataclass
class Sources:
    files: list = field(default_factory=list)
    incdirs: list = field(default_factory=list)
    defines: list = field(default_factory=list)   # "NAME" or "NAME=VALUE"
    libs: list = field(default_factory=list)      # blackbox stubs (vendor primitives)
    params: list = field(default_factory=list)    # "NAME=VALUE" top-level overrides

    def add_filelist(self, path: str, relative_to_list: bool = False):
        """Parse a simple .f file: files, +incdir+, +define+, -I, -D, nested
        -f/-F lists and -v FILE (a library file, read as a source).  Other
        simulator options are skipped, with their argument for the ones that
        take one (-y DIR, -timescale ..., ...).

        Relative paths follow the simulator convention (Verilator, VCS,
        Xcelium): in a list given with -f they are relative to the current
        directory, in one given with -F to the directory of the list itself."""
        base = os.path.dirname(os.path.abspath(path)) if relative_to_list else os.getcwd()
        rel = lambda p: p if os.path.isabs(p) else os.path.normpath(os.path.join(base, p))
        with open(path) as f:
            toks = []
            for line in f:
                line = line.split("//", 1)[0].strip()
                if line and not line.startswith("#"):
                    toks += shlex.split(line)
        it = iter(toks)
        for t in it:
            if t.startswith("+incdir+"):
                self.incdirs += [rel(p) for p in t[8:].split("+") if p]
            elif t.startswith("+define+"):
                self.defines += [d for d in t[8:].split("+") if d]
            elif t == "-I":
                self.incdirs.append(rel(next(it)))
            elif t.startswith("-I"):
                self.incdirs.append(rel(t[2:]))
            elif t == "-D":
                self.defines.append(next(it))
            elif t.startswith("-D"):
                self.defines.append(t[2:])
            elif t in ("-f", "-F"):
                self.add_filelist(rel(next(it)), relative_to_list=(t == "-F"))
            elif t in _ARG_OPTIONS:
                next(it, None)
            elif t.startswith("-") or t.startswith("+"):
                continue  # ignore simulator-specific options
            else:
                self.files.append(rel(t))


def _rel(p: str, cwd: str) -> str:
    return os.path.relpath(os.path.abspath(p), cwd)


def _slang_arg(s: str) -> str:
    # read_slang takes its arguments verbatim (no quote processing).
    if any(ch.isspace() for ch in s) or any(ch in s for ch in ';#"'):
        raise ToolError(f"--frontend slang cannot take {s!r}: avoid spaces, ';', '#' and quotes")
    return s


def read_commands(src: Sources, top: str, frontend: str, tools: Toolchain, path) -> str:
    """Yosys commands that read and elaborate the design; `path` maps a file
    or directory to the form handed to Yosys."""
    if not IDENT.match(top):
        raise ToolError(f"--top {top!r} is not a plain module name")
    lines = []
    for lib in src.libs:
        lines.append(f"read_verilog -sv -lib {yosys_arg(path(lib))}")
    if frontend == "slang":
        opts = ["--top", top]
        for i in src.incdirs:
            opts += ["-I", _slang_arg(path(i))]
        for d in src.defines:
            opts += ["-D", _slang_arg(d)]
        for p in src.params:
            opts += ["-G", _slang_arg(p)]
        if tools.is_yowasp:
            opts += ["--threads", "1"]   # WebAssembly build cannot spawn threads
        files = [_slang_arg(path(f)) for f in src.files]
        lines.append(tools.slang_prefix(".") + "read_slang " + " ".join(opts + files))
    else:
        opts = ["-sv"]
        opts += [yosys_arg("-I" + path(i)) for i in src.incdirs]
        opts += [yosys_arg("-D" + d) for d in src.defines]
        files = [yosys_arg(path(f)) for f in src.files]
        lines.append("read_verilog " + " ".join(opts + files))
        for p in src.params:
            name, _, value = p.partition("=")
            if not IDENT.match(name):
                raise ToolError(f"-P {p!r}: bad parameter name")
            lines.append(f"chparam -set {name} {yosys_arg(value)} {top}")
    lines.append(f"hierarchy -check -top {top}")
    return "\n".join(lines) + "\n"


HDL_EXT = {".v", ".sv", ".vh", ".svh", ".vinc", ".inc", ".h", ".pkg", ".sva", ".svi"}


def _stage(src: Sources, assume_file, edir: str):
    """Copy the inputs under edir/src, mirroring their layout relative to the
    deepest common directory.  Used with the WebAssembly Yosys build, which
    only resolves plain relative paths below its working directory."""
    paths = src.files + src.libs + ([assume_file] if assume_file else [])
    dirs = [os.path.dirname(os.path.abspath(p)) for p in paths] + [os.path.abspath(d) for d in src.incdirs]
    orig_root = os.path.commonpath(dirs)
    stage_root = os.path.join(edir, "src")
    if os.path.isdir(stage_root):
        shutil.rmtree(stage_root)

    def put(p):
        rel = os.path.relpath(os.path.abspath(p), orig_root)
        dst = os.path.join(stage_root, rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copy2(p, dst)
        return dst

    for d in src.incdirs:
        for dp, dns, fns in os.walk(d):
            dns[:] = [x for x in dns if not x.startswith(".")]
            for fn in fns:
                if os.path.splitext(fn)[1].lower() in HDL_EXT:
                    put(os.path.join(dp, fn))
    staged = Sources(files=[put(f) for f in src.files], libs=[put(f) for f in src.libs],
                     incdirs=[os.path.join(stage_root, os.path.relpath(os.path.abspath(d), orig_root))
                              for d in src.incdirs],
                     defines=list(src.defines), params=list(src.params))
    for d in staged.incdirs:
        os.makedirs(d, exist_ok=True)
    return staged, (put(assume_file) if assume_file else None), (stage_root, orig_root)


MAX_FSM_RETRIES = 3

_EXTRACTING = re.compile(r"Extracting FSM `\\?(.+?)' from module")


def _fsm_commands(skip: list) -> str:
    """Yosys commands (after the elaborated design is loaded) that write
    fsm.json, leaving the registers in `skip` out of FSM extraction."""
    # Ask fsm_detect to consider every register (except ones driving ports),
    # not only those it would re-encode for synthesis.
    cmds = ("proc\nflatten\nopt -nodffe -nosdff\n"
            "setattr -set fsm_encoding \"auto\" t:$dff t:$adff %u %co1:+[Q] w:* %i x:* %d\n")
    if skip:
        # Wildcards in a name would be patterns: let them match any character.
        names = " ".join("w:" + re.sub(r"[][*?\\]", "?", n) for n in skip)
        cmds += f"setattr -set fsm_encoding \"none\" {names}\n"
    return cmds + "fsm_detect\nfsm_extract\nwrite_json fsm.json\n"


def failed_fsm(log_full: str) -> str | None:
    """The register fsm_extract was working on when Yosys stopped with an
    error, from a Yosys log; None if the error was elsewhere."""
    if not os.path.exists(log_full):
        return None
    with open(log_full, errors="replace") as f:
        text = f.read()
    err = text.find("\nERROR:")
    if err < 0:
        return None
    names = _EXTRACTING.findall(text[:err])
    return names[-1] if names else None


def elaborate(src: Sources, top: str, frontend: str, tools: Toolchain, outdir: str,
              assume_file: str | None = None) -> dict:
    """One Yosys run producing main.json (structure preserved for detection
    and slicing) and fsm.json (Yosys' extracted $fsm cells).  FSM extraction
    runs on a saved copy of the elaborated design; if it fails, the main
    netlist is still used and FSM checks are skipped."""
    edir = os.path.join(outdir, "elab")
    os.makedirs(edir, exist_ok=True)
    for f in ("main.json", "fsm.json", "assume.json"):
        if os.path.exists(os.path.join(edir, f)):
            os.remove(os.path.join(edir, f))
    src_map = None
    if tools.is_yowasp:
        src, assume_file, src_map = _stage(src, assume_file, edir)
        path = lambda p: _rel(p, edir)  # noqa: E731
    else:
        path = os.path.abspath
    script = (read_commands(src, top, frontend, tools, path) +
              # Keep the source's full_case pragmas apart from the full_case
              # that proc_rmdead puts on every case with a default item.
              "attrmap -rename full_case fvlint_full_case\n"
              "design -save fvl_elab\nwrite_rtlil fvl_elab.il\n"
              "proc -noopt\nflatten\nmemory_collect\nopt_clean\nwrite_json main.json\n"
              "design -load fvl_elab\n" + _fsm_commands([]))
    rc = tools.run_yosys(script, edir, "elab", allow_fail=True)
    main = os.path.join(edir, "main.json")
    fsm_json = os.path.join(edir, "fsm.json")
    log = os.path.join(edir, "elab.log")
    if not os.path.exists(main):
        tail = tools.log_tail(log)
        hint = ""
        if frontend == "yosys" and "syntax error" in tail:
            hint = "\nhint: Yosys' built-in parser covers only part of SystemVerilog; try --frontend slang"
        raise ToolError(f"elaboration failed (see {log}.full):\n{tail}{hint}")
    # fsm_extract can stop Yosys on one register it can't handle (an internal
    # assertion); extract the others without it.
    fsm_warning, skipped, failed_log = None, [], log + ".full"
    while rc != 0 or not os.path.exists(fsm_json):
        name = failed_fsm(failed_log)
        if name is None or name in skipped or len(skipped) >= MAX_FSM_RETRIES:
            fsm_warning = (f"FSM extraction failed in Yosys; FSM checks skipped (see "
                           f"{os.path.basename(failed_log)})")
            break
        skipped.append(name)
        rc = tools.run_yosys("read_rtlil fvl_elab.il\n" + _fsm_commands(skipped), edir, "fsm", allow_fail=True)
        failed_log = os.path.join(edir, "fsm.log.full")
    else:
        if skipped:
            fsm_warning = (f"FSM extraction failed in Yosys on {', '.join(skipped)}; FSM checks skip "
                           f"{'it' if len(skipped) == 1 else 'them'} (see elab.log.full)")

    assume_ports = None
    if assume_file:
        tools.run_yosys(f"read_verilog -formal -sv {yosys_arg(path(assume_file))}\n"
                        "hierarchy -top fvlint_assumptions\nproc\nwrite_json assume.json\n",
                        edir, "assume")
        with open(os.path.join(edir, "assume.json")) as f:
            m = json.load(f)["modules"]["fvlint_assumptions"]
        assume_ports = {n: p["direction"] for n, p in m["ports"].items()}
    return {"main": main, "fsm": fsm_json if os.path.exists(fsm_json) else None,
            "fsm_warning": fsm_warning, "src_base": edir, "src_map": src_map,
            "assume_ports": assume_ports, "assume_file": assume_file}
