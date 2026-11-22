# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Regenerate the Yosys netlist snapshots the unit tests read.

The unit tests run without Yosys.  To still exercise the detectors on the
netlist shapes Yosys really produces, the RTL in rtl/ is elaborated once with
fvlint's own elaboration step and the resulting main.json / fsm.json are
committed under snapshots/.  `src` attributes are reduced to the file's base
name so the snapshots do not depend on where or how Yosys ran.

    python tests/unit/data/make_snapshots.py          # rewrite snapshots/
    python tests/unit/data/make_snapshots.py --check  # exit 1 if they drifted

Run it after changing rtl/ or the elaboration script, and review the diff:
unit-test expectations are written against these netlists.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.environ.get("FVLINT_SRC") or os.path.join(HERE, "..", "..", "..", "src"))

from fvlint.elaborate import Sources, elaborate   # noqa: E402
from fvlint.tools import Toolchain                # noqa: E402

TOPS = {"snap_counters": "snap_counters.sv", "snap_mux": "snap_mux.sv",
        "snap_fsm": "snap_fsm.sv", "snap_reset": "snap_reset.sv", "snap_index": "snap_index.sv",
        "snap_ops": "snap_ops.sv"}

_SRC_PART = re.compile(r"([^|]*?)([^/|]+):(\d+\.\d+-\d+\.\d+)")


def _norm_src(v: str) -> str:
    return _SRC_PART.sub(lambda m: f"{m.group(2)}:{m.group(3)}", v)


def _normalise(obj):
    if isinstance(obj, dict):
        return {k: (_norm_src(v) if k == "src" and isinstance(v, str) else _normalise(v))
                for k, v in obj.items()}
    if isinstance(obj, list):
        return [_normalise(x) for x in obj]
    return obj


def generate(outdir: str) -> dict:
    tools = Toolchain.discover()
    written = {}
    for top, rtl in TOPS.items():
        with tempfile.TemporaryDirectory() as tmp:
            r = elaborate(Sources(files=[os.path.join(HERE, "rtl", rtl)]), top, "yosys", tools, tmp)
            for kind, path in (("main", r["main"]), ("fsm", r["fsm"])):
                if not path:
                    continue
                with open(path) as f:
                    data = _normalise(json.load(f))
                data["creator"] = "Yosys (snapshot)"
                name = f"{top}.{kind}.json"
                text = json.dumps(data, sort_keys=True, separators=(",", ":")) + "\n"
                written[name] = text
                with open(os.path.join(outdir, name), "w") as f:
                    f.write(text)
    return written


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--check", action="store_true", help="compare instead of writing")
    args = ap.parse_args()
    snap = os.path.join(HERE, "snapshots")
    if not args.check:
        os.makedirs(snap, exist_ok=True)
        for name in generate(snap):
            print(f"wrote snapshots/{name}")
        return 0
    with tempfile.TemporaryDirectory() as tmp:
        fresh = generate(tmp)
    drift = []
    for name, text in fresh.items():
        p = os.path.join(snap, name)
        if not os.path.exists(p) or open(p).read() != text:
            drift.append(name)
    for name in drift:
        print(f"drifted: snapshots/{name}")
    return 1 if drift else 0


if __name__ == "__main__":
    sys.exit(main())
