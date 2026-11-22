# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""fvlint.elaborate: file lists, Yosys read scripts, staging and the
elaboration driver (with a fake toolchain)."""

from __future__ import annotations

import json
import os
import unittest

from fvlint.elaborate import (HDL_EXT, MAX_FSM_RETRIES, Sources, _fsm_commands, _slang_arg, _stage, elaborate,
                              failed_fsm, read_commands)
from fvlint.tools import ToolError

from .support import TempDirCase


class FakeTools:
    """Records Yosys scripts; `outputs` says which files each run writes."""

    def __init__(self, is_yowasp=False, outputs=("main.json", "fsm.json"), rc=0, log="", slang=""):
        self.is_yowasp, self.outputs, self.rc, self.log, self.slang = is_yowasp, outputs, rc, log, slang
        self.runs = []

    def slang_prefix(self, cwd):
        self.slang_cwd = cwd
        return self.slang

    def run_yosys(self, script, cwd, name, allow_fail=False):
        self.runs.append((name, script, cwd, allow_fail))
        with open(os.path.join(cwd, name + ".log"), "w") as f:
            f.write(self.log)
        if name == "assume":
            with open(os.path.join(cwd, "assume.json"), "w") as f:
                json.dump({"modules": {"fvlint_assumptions": {"ports": {
                    "lane": {"direction": "input", "bits": [2, 3]}, "x": {"direction": "output", "bits": [4]}}}}}, f)
            return 0
        for out in self.outputs:
            with open(os.path.join(cwd, out), "w") as f:
                f.write("{}")
        return self.rc

    @staticmethod
    def log_tail(log, n=15):
        with open(log) as f:
            return f.read()


class ScriptedTools(FakeTools):
    """A FakeTools whose successive Yosys runs write the given outputs, return
    the given codes and leave the given logs (also as NAME.log.full)."""

    def __init__(self, plan):
        super().__init__()
        self.plan = list(plan)

    def run_yosys(self, script, cwd, name, allow_fail=False):
        self.runs.append((name, script, cwd, allow_fail))
        outputs, rc, log = self.plan.pop(0)
        for suffix in (".log", ".log.full"):
            with open(os.path.join(cwd, name + suffix), "w") as f:
                f.write(log)
        for out in outputs:
            with open(os.path.join(cwd, out), "w") as f:
                f.write("{}")
        return rc


class FileLists(TempDirCase):
    def test_options(self):
        fl = self.write("proj/t.f", "// comment\n# full-line comment\n+incdir+inc+inc2\n+define+A=1+B\n-D C\n"
                                    "-DD=2\n-I other\n-Imore\n-sv +libext+.v -y libdir -timescale 1ns/1ps\n"
                                    "-top tb -l sim.log -o simv -L work2 -work w -libext .vh -sverilog_ext .sv\n"
                                    "rtl/a.sv  // trailing\nrtl/b#1.sv\n\"my dir/c.sv\"\n/abs/d.sv\n-v lib/cells.v\n")
        s = Sources()
        s.add_filelist(fl, relative_to_list=True)
        base = os.path.join(self.tmp, "proj")
        self.assertEqual(s.files, [os.path.join(base, "rtl", "a.sv"), os.path.join(base, "rtl", "b#1.sv"),
                                   os.path.join(base, "my dir", "c.sv"), "/abs/d.sv",
                                   os.path.join(base, "lib", "cells.v")])    # option arguments are not files
        self.assertEqual(s.incdirs, [os.path.join(base, d) for d in ("inc", "inc2", "other", "more")])
        self.assertEqual(s.defines, ["A=1", "B", "C", "D=2"])

    def test_dash_f_is_relative_to_the_current_directory(self):
        fl = self.write("lists/a.f", "rtl/x.v\n+incdir+inc\n")
        os.makedirs(os.path.join(self.tmp, "run"))
        self.chdir(os.path.join(self.tmp, "run"))
        s = Sources()
        s.add_filelist(fl)
        self.assertEqual((s.files, s.incdirs), ([os.path.join(self.tmp, "run", "rtl", "x.v")],
                                                [os.path.join(self.tmp, "run", "inc")]))
        s = Sources()
        s.add_filelist(fl, relative_to_list=True)
        self.assertEqual(s.files, [os.path.join(self.tmp, "lists", "rtl", "x.v")])

    def test_nested_lists(self):
        # top.f (-F) names sub.f relative to itself; sub.f was included with
        # -f, so its paths (including leaf.f's) are relative to the current
        # directory; leaf.f was included with -F.
        self.write("a/top.f", "-f ../b/sub.f\ntop.sv\n")
        self.write("b/sub.f", "+incdir+inc\n-F b/c/leaf.f\nsub.sv\n")
        self.write("b/c/leaf.f", "leaf.sv\n")
        self.chdir(self.tmp)
        s = Sources()
        s.add_filelist(os.path.join(self.tmp, "a", "top.f"), relative_to_list=True)
        self.assertEqual(s.files, [os.path.join(self.tmp, "b", "c", "leaf.sv"), os.path.join(self.tmp, "sub.sv"),
                                   os.path.join(self.tmp, "a", "top.sv")])
        self.assertEqual(s.incdirs, [os.path.join(self.tmp, "inc")])

    def test_relative_list_path(self):
        self.write("x/l.f", "a.v\n")
        self.chdir(self.tmp)
        s = Sources()
        s.add_filelist("x/l.f", relative_to_list=True)
        self.assertEqual(s.files, [os.path.join(self.tmp, "x", "a.v")])


class ReadScripts(unittest.TestCase):
    def src(self, **kw):
        return Sources(files=["/p/a.sv", "/p/b c.sv"], incdirs=["/p/inc"], defines=["W=8", "FAST"],
                       libs=["/p/prims.v"], params=["DEPTH=16"], **kw)

    def test_yosys_frontend(self):
        text = read_commands(self.src(), "top", "yosys", FakeTools(), lambda p: p)
        self.assertEqual(text, "read_verilog -sv -lib /p/prims.v\n"
                               'read_verilog -sv -I/p/inc -DW=8 -DFAST /p/a.sv "/p/b c.sv"\n'
                               "chparam -set DEPTH 16 top\n"
                               "hierarchy -check -top top\n")

    def test_path_mapping_is_applied(self):
        text = read_commands(Sources(files=["/p/a.sv"], incdirs=["/p/inc"], libs=["/p/l.v"]), "top", "yosys",
                             FakeTools(), lambda p: "src" + p)
        self.assertIn("-lib src/p/l.v", text)
        self.assertIn("-Isrc/p/inc src/p/a.sv", text)

    def test_slang_frontend(self):
        s = Sources(files=["/p/a.sv"], incdirs=["/p/inc"], defines=["W=8"], params=["DEPTH=16"])
        tools = FakeTools(slang="plugin -i slang\n")
        text = read_commands(s, "top", "slang", tools, lambda p: p)
        self.assertEqual(text, "plugin -i slang\nread_slang --top top -I /p/inc -D W=8 -G DEPTH=16 /p/a.sv\n"
                               "hierarchy -check -top top\n")
        self.assertEqual(tools.slang_cwd, ".")                          # probed where the script will run
        text = read_commands(s, "top", "slang", FakeTools(is_yowasp=True), lambda p: p)
        self.assertIn("read_slang --top top -I /p/inc -D W=8 -G DEPTH=16 --threads 1 /p/a.sv",
                      text.splitlines())                                # WebAssembly build: no threads

    def test_rejected_names(self):
        for top in ("1top", "a b", "top;x", "a.b"):
            with self.subTest(top=top), self.assertRaisesRegex(ToolError, "--top"):
                read_commands(Sources(files=["a.v"]), top, "yosys", FakeTools(), lambda p: p)
        with self.assertRaisesRegex(ToolError, "-P"):
            read_commands(Sources(files=["a.v"], params=["9X=1"]), "top", "yosys", FakeTools(), lambda p: p)
        with self.assertRaisesRegex(ToolError, "slang"):
            read_commands(Sources(files=["my dir/a.v"]), "top", "slang", FakeTools(), lambda p: p)

    def test_slang_arguments(self):
        self.assertEqual(_slang_arg("rtl/a.sv"), "rtl/a.sv")
        for bad in ("a b", "a;b", "a#b", 'a"b', "a\tb"):
            with self.subTest(bad=bad), self.assertRaises(ToolError):
                _slang_arg(bad)


class Staging(TempDirCase):
    def test_layout_is_mirrored_below_the_common_root(self):
        a = self.write("ip/rtl/a.sv", "A")
        a2 = self.write("ip/rtl/a2.sv", "A2")                           # same directory as a.sv
        lib = self.write("ip/lib/prims.v", "P")
        self.write("ip/inc/defs.svh", "D")
        self.write("ip/inc/sub/more.vh", "M")
        self.write("ip/inc/notes.txt", "not HDL")
        exts = (".v", ".sv", ".vh", ".svh", ".vinc", ".inc", ".h", ".pkg", ".sva", ".svi")
        for ext in exts:
            self.write(f"ip/inc/all/x{ext}", ext)
        self.write("ip/inc/.git/x.v", "hidden")
        assume = self.write("ip/fv/assume.sv", "S")
        os.makedirs(os.path.join(self.tmp, "ip", "empty_inc"))
        edir = os.path.join(self.tmp, "out", "elab")
        src = Sources(files=[a, a2], libs=[lib], incdirs=[os.path.join(self.tmp, "ip", "inc"),
                                                      os.path.join(self.tmp, "ip", "empty_inc")],
                      defines=["X"], params=["P=1"])
        staged, staged_assume, (stage_root, orig_root) = _stage(src, assume, edir)
        self.assertEqual((stage_root, orig_root), (os.path.join(edir, "src"), os.path.join(self.tmp, "ip")))
        self.assertEqual(staged.files, [os.path.join(stage_root, "rtl", "a.sv"),
                                        os.path.join(stage_root, "rtl", "a2.sv")])
        self.assertEqual(staged.libs, [os.path.join(stage_root, "lib", "prims.v")])
        self.assertEqual(staged_assume, os.path.join(stage_root, "fv", "assume.sv"))
        self.assertEqual(staged.incdirs, [os.path.join(stage_root, "inc"), os.path.join(stage_root, "empty_inc")])
        self.assertTrue(os.path.isdir(staged.incdirs[1]))
        copied = sorted(os.path.relpath(os.path.join(dp, f), stage_root)
                        for dp, _, fs in os.walk(stage_root) for f in fs)
        self.assertEqual(copied, sorted(["rtl/a.sv", "rtl/a2.sv", "lib/prims.v", "fv/assume.sv", "inc/defs.svh",
                                         "inc/sub/more.vh"] + [f"inc/all/x{e}" for e in exts]))
        self.assertEqual((staged.defines, staged.params), (["X"], ["P=1"]))
        self.assertIsNot(staged.defines, src.defines)

    def test_restaging_replaces_stale_copies(self):
        a = self.write("ip/a.sv", "new")
        edir = os.path.join(self.tmp, "elab")
        self.write("elab/src/stale.v", "old")
        staged, none, _ = _stage(Sources(files=[a]), None, edir)
        self.assertIsNone(none)
        self.assertEqual(os.listdir(os.path.join(edir, "src")), ["a.sv"])

    def test_hdl_extensions(self):
        self.assertTrue({".v", ".sv", ".svh", ".vh"} <= HDL_EXT)
        self.assertNotIn(".txt", HDL_EXT)


class Elaboration(TempDirCase):
    def setUp(self):
        super().setUp()
        self.rtl = self.write("rtl/a.sv", "module top; endmodule\n")
        self.out = os.path.join(self.tmp, "out")

    def test_native_run(self):
        tools = FakeTools()
        r = elaborate(Sources(files=[self.rtl]), "top", "yosys", tools, self.out)
        edir = os.path.join(self.out, "elab")
        self.assertEqual(r, {"main": os.path.join(edir, "main.json"), "fsm": os.path.join(edir, "fsm.json"),
                             "fsm_warning": None, "src_base": edir, "src_map": None, "assume_ports": None,
                             "assume_file": None})
        (name, script, cwd, allow_fail), = tools.runs
        self.assertEqual((name, cwd, allow_fail), ("elab", edir, True))
        self.assertIn(f"read_verilog -sv {self.rtl}\nhierarchy -check -top top\n"
                      "attrmap -rename full_case fvlint_full_case\ndesign -save fvl_elab\n", script)
        main_part, fsm_part = script.split("design -load fvl_elab\n")
        self.assertIn("proc -noopt\nflatten\nmemory_collect\nopt_clean\nwrite_json main.json\n", main_part)
        self.assertIn("fsm_detect\nfsm_extract\nwrite_json fsm.json\n", fsm_part)
        self.assertIn('setattr -set fsm_encoding "auto"', fsm_part)

    def test_yowasp_run_uses_staged_relative_paths(self):
        tools = FakeTools(is_yowasp=True)
        r = elaborate(Sources(files=[self.rtl]), "top", "yosys", tools, self.out)
        edir = os.path.join(self.out, "elab")
        self.assertEqual(r["src_map"], (os.path.join(edir, "src"), os.path.join(self.tmp, "rtl")))
        self.assertIn("read_verilog -sv src/a.sv\n", tools.runs[0][1])
        self.assertTrue(os.path.exists(os.path.join(edir, "src", "a.sv")))

    def test_stale_outputs_are_removed_first(self):
        edir = os.path.join(self.out, "elab")
        for f in ("main.json", "fsm.json", "assume.json"):
            self.write(os.path.join("out", "elab", f), "stale")
        with self.assertRaises(ToolError):
            elaborate(Sources(files=[self.rtl]), "top", "yosys", FakeTools(outputs=()), self.out)
        self.assertEqual(sorted(os.listdir(edir)), ["elab.log"])

    def test_failed_elaboration(self):
        tools = FakeTools(outputs=(), rc=1, log="ERROR: syntax error, unexpected TOK_ID\n")
        with self.assertRaises(ToolError) as cm:
            elaborate(Sources(files=[self.rtl]), "top", "yosys", tools, self.out)
        self.assertIn("elaboration failed", str(cm.exception))
        self.assertIn("syntax error", str(cm.exception))
        self.assertIn("try --frontend slang", str(cm.exception))
        with self.assertRaises(ToolError) as cm:
            elaborate(Sources(files=[self.rtl]), "top", "slang", tools, self.out)
        self.assertNotIn("try --frontend slang", str(cm.exception))
        tools.log = "ERROR: Module `top' not found!\n"
        with self.assertRaises(ToolError) as cm:
            elaborate(Sources(files=[self.rtl]), "top", "yosys", tools, self.out)
        self.assertNotIn("hint", str(cm.exception))

    def test_fsm_extraction_failure_is_a_warning(self):
        r = elaborate(Sources(files=[self.rtl]), "top", "yosys", FakeTools(outputs=("main.json",), rc=1), self.out)
        self.assertIsNone(r["fsm"])
        self.assertIn("FSM extraction failed", r["fsm_warning"])
        r = elaborate(Sources(files=[self.rtl]), "top", "yosys", FakeTools(rc=1), self.out)
        self.assertIsNotNone(r["fsm"])                                  # written, but Yosys still failed
        self.assertIsNotNone(r["fsm_warning"])

    def test_fsm_extraction_retried_without_the_failing_register(self):
        # fsm_extract stops Yosys on one register (an internal assertion): the
        # FSM pass is run again on the saved design without it.
        crash = ("Extracting FSM `\\cpu_state' from module `\\t'.\n  found ctrl input: x\n"
                 "Extracting FSM `\\irq_state' from module `\\t'.\n"
                 "ERROR: Assert `ce.stop_signals.check_all(undef)' failed in fsm_extract.cc:241.\n")
        tools = ScriptedTools([(("main.json",), 1, crash), (("fsm.json",), 0, "")])
        r = elaborate(Sources(files=[self.rtl]), "top", "yosys", tools, self.out)
        self.assertEqual(r["fsm"], os.path.join(self.out, "elab", "fsm.json"))
        self.assertIn("on irq_state; FSM checks skip it", r["fsm_warning"])
        (name, script, cwd, allow_fail), = tools.runs[1:]
        self.assertEqual((name, cwd, allow_fail), ("fsm", os.path.join(self.out, "elab"), True))
        self.assertEqual(script, "read_rtlil fvl_elab.il\n" + _fsm_commands(["irq_state"]))
        self.assertIn("design -save fvl_elab\nwrite_rtlil fvl_elab.il\n", tools.runs[0][1])
        # Two registers in turn.
        crash2 = "Extracting FSM `\\u.st' from module `\\t'.\nERROR: Assert failed\n"
        tools = ScriptedTools([(("main.json",), 1, crash), ((), 1, crash2), (("fsm.json",), 0, "")])
        r = elaborate(Sources(files=[self.rtl]), "top", "yosys", tools, self.out)
        self.assertIn("on irq_state, u.st; FSM checks skip them", r["fsm_warning"])
        self.assertEqual(tools.runs[2][1], "read_rtlil fvl_elab.il\n" + _fsm_commands(["irq_state", "u.st"]))

    def test_fsm_extraction_retries_give_up(self):
        crash = "Extracting FSM `\\a' from module `\\t'.\nERROR: Assert failed\n"
        tools = ScriptedTools([(("main.json",), 1, crash)] + [((), 1, crash)] * 3)      # the same register again
        r = elaborate(Sources(files=[self.rtl]), "top", "yosys", tools, self.out)
        self.assertEqual((len(tools.runs), r["fsm"]), (2, None))
        self.assertEqual(r["fsm_warning"], "FSM extraction failed in Yosys; FSM checks skipped (see fsm.log.full)")
        logs = [f"Extracting FSM `\\r{i}' from module `\\t'.\nERROR: x\n" for i in range(MAX_FSM_RETRIES + 2)]
        tools = ScriptedTools([(("main.json",), 1, logs[0])] + [((), 1, lg) for lg in logs[1:]])
        r = elaborate(Sources(files=[self.rtl]), "top", "yosys", tools, self.out)
        self.assertEqual(len(tools.runs), 1 + MAX_FSM_RETRIES)                      # then it stops
        self.assertIn("FSM checks skipped", r["fsm_warning"])

    def test_failed_fsm(self):
        log = self.write("y.log.full", "Extracting FSM `\\st' from module `\\t'.\nok\n")
        self.assertIsNone(failed_fsm(log))                                          # no error
        self.assertIsNone(failed_fsm(os.path.join(self.tmp, "missing.log")))
        log = self.write("y.log.full", "ERROR: syntax error\nExtracting FSM `\\st' from module `\\t'.\n")
        self.assertIsNone(failed_fsm(log))                                          # the error came first
        log = self.write("y.log.full", "Extracting FSM `u.st' from module `\\t'.\n\nERROR: x\n")
        self.assertEqual(failed_fsm(log), "u.st")
        log = self.write("y.log.full", "Extracting FSM `\\a' from module `\\t'.\nExtracting FSM `\\b[1]' "
                                       "from module `\\t'.\nERROR: x\nExtracting FSM `\\c' from module `\\t'.\n")
        self.assertEqual(failed_fsm(log), "b[1]")
        with open(log, "wb") as f:                                                  # a stray byte in the log
            f.write(b"\xff\nExtracting FSM `\\st' from module `\\t'.\nERROR: x\n")
        self.assertEqual(failed_fsm(log), "st")

    def test_fsm_commands(self):
        self.assertEqual(_fsm_commands([]).splitlines()[-3:], ["fsm_detect", "fsm_extract", "write_json fsm.json"])
        self.assertNotIn('"none"', _fsm_commands([]))
        self.assertIn('setattr -set fsm_encoding "none" w:a w:g?0?.st w:x?y w:p?q w:b?s\nfsm_detect\n',
                      _fsm_commands(["a", "g[0].st", "x*y", "p?q", "b\\s"]))

    def test_assumptions(self):
        assume = self.write("fv/assume.sv", "module fvlint_assumptions(input [1:0] lane); endmodule\n")
        tools = FakeTools()
        r = elaborate(Sources(files=[self.rtl]), "top", "yosys", tools, self.out, assume)
        self.assertEqual(r["assume_ports"], {"lane": "input", "x": "output"})
        self.assertEqual(r["assume_file"], assume)
        name, script, _, allow_fail = tools.runs[1]
        self.assertEqual((name, allow_fail), ("assume", False))
        self.assertEqual(script, f"read_verilog -formal -sv {assume}\nhierarchy -top fvlint_assumptions\n"
                                 "proc\nwrite_json assume.json\n")


if __name__ == "__main__":
    unittest.main()
