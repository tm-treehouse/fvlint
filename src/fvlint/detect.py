# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Structure detectors: find counters, parallel/unique case muxes, variable
part-selects and memories in a flattened netlist and turn each into checks."""

from __future__ import annotations

import os

from .checks import INFO, Check, Lemma
from .netlist import FF_TYPES, Netlist, attr_true, const_value, is_const

COMPARE_TYPES = {"$eq", "$ne", "$eqx", "$nex", "$lt", "$le", "$gt", "$ge"}
MAX_PATHS = 64


def _mask(w: int) -> int:
    return (1 << w) - 1


def _feasible(conds) -> bool:
    seen = {}
    for b, v in conds:
        if is_const(b):
            if b != str(v):
                return False
            continue
        if seen.setdefault(b, v) != v:
            return False
    return True


def _clean(conds):
    out, seen = [], set()
    for b, v in conds:
        if is_const(b) or (b, v) in seen:
            continue
        seen.add((b, v))
        out.append((b, v))
    return out


# --------------------------------------------------------------- mux trees
def mux_sources(nl: Netlist, bits: list, conds=(), depth=0, out=None):
    """Enumerate the sources feeding `bits` through a $mux/$pmux tree.

    Yields (bits_of_source, conditions) where conditions is a list of
    (select_bit, value) that must hold for that source to be selected.
    """
    if out is None:
        out = []
    if len(out) >= MAX_PATHS or depth > 24 or not _feasible(conds):
        return out
    d = nl.whole_driver(bits)
    if d is None:
        out.append((bits, list(conds)))
        return out
    cell, port, off = d
    t = nl.ctype(cell)
    w = len(bits)
    if t == "$mux" and port == "Y":
        s = nl.conn(cell, "S")[0]
        mux_sources(nl, nl.conn(cell, "A")[off:off + w], list(conds) + [(s, 0)], depth + 1, out)
        mux_sources(nl, nl.conn(cell, "B")[off:off + w], list(conds) + [(s, 1)], depth + 1, out)
    elif t == "$pmux" and port == "Y":
        width = nl.param(cell, "WIDTH")
        sel = nl.conn(cell, "S")
        b = nl.conn(cell, "B")
        for i, sb in enumerate(sel):
            mux_sources(nl, b[i * width + off:i * width + off + w], list(conds) + [(sb, 1)], depth + 1, out)
        mux_sources(nl, nl.conn(cell, "A")[off:off + w], list(conds) + [(sb, 0) for sb in sel], depth + 1, out)
    else:
        out.append((bits, list(conds)))
    return out


def forward_conds(nl: Netlist, bits: list, max_depth=16) -> list:
    """Conditions under which `bits` actually propagate through the mux tree
    that consumes them (used to avoid checking values that are discarded)."""
    conds = []
    cur = [b for b in bits]
    for _ in range(max_depth):
        if any(is_const(b) for b in cur):
            break
        readers = {}
        ok = True
        for b in cur:
            rs = nl.readers.get(b, [])
            if len(rs) != 1:
                ok = False
                break
            readers.setdefault((rs[0][0], rs[0][1]), []).append(rs[0][2])
        if not ok or len(readers) != 1:
            break
        (cell, port), offs = next(iter(readers.items()))
        t = nl.ctype(cell)
        if t in FF_TYPES and port == "D":
            conds += nl.ff_info(cell)["conds"]
            break
        if t == "$mux" and port in ("A", "B"):
            conds.append((nl.conn(cell, "S")[0], 0 if port == "A" else 1))
            cur = [nl.conn(cell, "Y")[o] for o in offs]
        elif t == "$pmux" and port in ("A", "B"):
            width = nl.param(cell, "WIDTH")
            sel = nl.conn(cell, "S")
            if port == "A":
                conds += [(s, 0) for s in sel]
                cur = [nl.conn(cell, "Y")[o] for o in offs]
            else:
                idx = {o // width for o in offs}
                if len(idx) != 1:
                    break
                i = idx.pop()
                conds.append((sel[i], 1))
                cur = [nl.conn(cell, "Y")[o - i * width] for o in offs]
        else:
            break
    return _clean(conds)


# ---------------------------------------------------------------- counters
def _operand_is(bits: list, q: list) -> bool:
    """bits == q, optionally zero-extended."""
    if len(bits) < len(q) or bits[:len(q)] != q:
        return False
    return all(b == "0" for b in bits[len(q):])


def _compare_constants(nl: Netlist, q: list) -> set:
    ks = set()
    qs = set(q)
    for cell, c in nl.cells.items():
        if c["type"] not in COMPARE_TYPES:
            continue
        a, b = nl.conn(cell, "A"), nl.conn(cell, "B")
        if not (qs & set(a) or qs & set(b)):
            continue
        for x, y in ((a, b), (b, a)):
            if _operand_is(x, q):
                k = const_value(y)
                if k is not None:
                    ks.add(k)
    return ks


def detect_counters(nl: Netlist, max_level: int):
    checks, lemmas = [], {}
    for cell, c in nl.cells.items():
        if c["type"] not in FF_TYPES or c["type"] in ("$anyinit",) or "D" not in c["connections"]:
            continue
        ff = nl.ff_info(cell)
        q, d = ff["Q"], ff["D"]
        w = len(q)
        if w < 2 or any(is_const(b) for b in q):
            continue
        paths = mux_sources(nl, d)
        steps = []      # (dir, step, conds)
        loads = set()
        for sbits, conds in paths:
            k = const_value(sbits)
            if k is not None:
                loads.add(k)
                continue
            drv = nl.whole_driver(sbits)
            if drv is None:
                continue
            acell, aport, aoff = drv
            at = nl.ctype(acell)
            if aport != "Y" or aoff != 0 or at not in ("$add", "$sub"):
                continue
            a, b = nl.conn(acell, "A"), nl.conn(acell, "B")
            if _operand_is(a, q) and const_value(b) is not None:
                steps.append(("up" if at == "$add" else "down", const_value(b), conds))
            elif at == "$add" and _operand_is(b, q) and const_value(a) is not None:
                steps.append(("up", const_value(a), conds))
        if not steps:
            continue

        name = nl.name_of(q)
        src = nl.net_src(q)
        if src == "?":
            src = nl.cell_src(cell)
        waive = nl.net_attr(q, "fvlint_waive")
        ks = _compare_constants(nl, q)
        bounded_any = False
        for direction, step, conds in steps:
            if step <= 0 or step > _mask(w):
                continue
            all_conds = _clean(conds + ff["conds"])
            cond_bits = [b for b, _ in all_conds]
            bounded = nl.depends_on(cond_bits, set(q), max_level)
            bounded_any |= bounded
            kind = "counter_overflow" if direction == "up" else "counter_underflow"
            if direction == "up":
                hi = _mask(w) - step
                params = {"W": w, "LO": 0, "HI": hi}
                desc = f"{name} + {step} never wraps past {_mask(w)} ({w} bits)"
            else:
                params = {"W": w, "LO": step, "HI": _mask(w)}
                desc = f"{name} - {step} never wraps below 0"
            chk = Check(kind=kind, target=name, src=src, desc=desc, checker="fvl_range",
                        params=params, ports={"v": q}, conds=all_conds, anchors=[cell],
                        waive_attr=waive, depth_hint=(1 << w) // step + 2)
            if not bounded:
                chk.preset = INFO
                chk.detail = ("free-running: the increment condition does not depend on the "
                              "counter, so wrap-around looks intentional; not checked")
            checks.append(chk)

        # Candidate invariants: 'q <= K' for compare/load constants.
        cands = set()
        for k in ks | loads:
            for kk in (k - 1, k, k + 1):
                if 0 <= kk < _mask(w):
                    cands.add(kk)
        for k in sorted(cands)[:8]:
            lemmas.setdefault(cell, []).append(Lemma(
                owner=cell, desc=f"{name} <= {k}", checker="fvl_range",
                params={"W": w, "LO": 0, "HI": k}, ports={"v": q}, bound=k))
    # Disambiguate duplicate ids (several add paths on one register).
    seen = {}
    for chk in checks:
        n = seen.get(chk.id, 0)
        seen[chk.id] = n + 1
        if n:
            chk.target = f"{chk.target}#{n}"
    return checks, lemmas


# ------------------------------------------------------------ case / pmux
def detect_case(nl: Netlist):
    checks = []
    for cell, c in nl.cells.items():
        if c["type"] != "$pmux":
            continue
        attrs = c.get("attributes", {})
        if not attr_true(attrs.get("parallel_case")):
            continue
        sel = nl.conn(cell, "S")
        if len(sel) < 2 or all(is_const(b) for b in sel):
            continue
        src = nl.cell_src(cell)
        fconds = forward_conds(nl, nl.conn(cell, "Y"))
        checks.append(Check(
            kind="parallel_case", target=_loc_id(src), src=src,
            desc="at most one item of a unique/parallel_case statement matches",
            checker="fvl_onehot0", params={"W": len(sel)}, ports={"s": sel}, conds=fconds))
        a = nl.conn(cell, "A")
        if attr_true(attrs.get("full_case")) and a and all(b == "x" for b in a):
            checks.append(Check(
                kind="full_case", target=_loc_id(src), src=src,
                desc="some item of a full/unique case statement without default always matches",
                checker="fvl_nonzero", params={"W": len(sel)}, ports={"s": sel}, conds=fconds))
    return _dedupe(checks)


# ------------------------------------------------------- part-select index
def detect_index(nl: Netlist):
    checks = []
    for cell, c in nl.cells.items():
        if c["type"] != "$shiftx":
            continue
        b = nl.conn(cell, "B")
        if all(is_const(x) for x in b):
            continue
        aw, yw = len(nl.conn(cell, "A")), len(nl.conn(cell, "Y"))
        hi = aw - yw
        if hi < 0:
            continue
        bw = len(b)
        signed = nl.param(cell, "B_SIGNED", 0)
        # Unsigned compare also rejects negative signed values (MSB set).
        if not signed and hi >= _mask(bw):
            continue
        src = nl.cell_src(cell)
        checks.append(Check(
            kind="index_range", target=_loc_id(src), src=src,
            desc=f"variable select offset stays within 0..{hi} ({aw}-bit vector, {yw}-bit slice)",
            checker="fvl_range", params={"W": bw, "LO": 0, "HI": hi}, ports={"v": b},
            conds=forward_conds(nl, nl.conn(cell, "Y"))))
    return _dedupe(checks)


# ----------------------------------------------------------------- memory
def detect_memory(nl: Netlist):
    checks = []
    for cell, c in nl.cells.items():
        if c["type"] != "$mem_v2":
            continue
        size = nl.param(cell, "SIZE")
        offset = nl.param(cell, "OFFSET", 0)
        abits = nl.param(cell, "ABITS")
        width = nl.param(cell, "WIDTH")
        if offset == 0 and size >= (1 << abits):
            continue  # every address is valid
        lo, hi = offset, offset + size - 1
        memid = nl.param(cell, "MEMID", cell)
        if isinstance(memid, str):
            memid = memid.lstrip("\\")
        src = nl.cell_src(cell)
        waive = nl.attrs(cell).get("fvlint_waive")
        rd_addr, rd_en, rd_data = nl.conn(cell, "RD_ADDR"), nl.conn(cell, "RD_EN"), nl.conn(cell, "RD_DATA")
        for i in range(nl.param(cell, "RD_PORTS", 0)):
            addr = rd_addr[i * abits:(i + 1) * abits]
            if all(is_const(x) for x in addr):
                continue
            en = rd_en[i:i + 1] if rd_en else ["1"]
            conds = forward_conds(nl, rd_data[i * width:(i + 1) * width])
            checks.append(Check(
                kind="mem_addr", target=f"{memid}.rd{i}", src=src,
                desc=f"read address of {memid}[{lo}:{hi}] stays in range", checker="fvl_range",
                params={"W": abits, "LO": lo, "HI": hi}, ports={"v": addr, "e": en},
                conds=conds, waive_attr=waive))
        wr_addr, wr_en = nl.conn(cell, "WR_ADDR"), nl.conn(cell, "WR_EN")
        for i in range(nl.param(cell, "WR_PORTS", 0)):
            addr = wr_addr[i * abits:(i + 1) * abits]
            if all(is_const(x) for x in addr):
                continue
            en = wr_en[i * width:(i + 1) * width]
            checks.append(Check(
                kind="mem_addr", target=f"{memid}.wr{i}", src=src,
                desc=f"write address of {memid}[{lo}:{hi}] stays in range", checker="fvl_range",
                params={"W": abits, "LO": lo, "HI": hi}, ports={"v": addr, "e": en},
                waive_attr=waive))
    return checks


def _loc_id(src: str) -> str:
    """Stable, CWD-independent id for an anonymous object: 'file.sv:12'."""
    return os.path.basename(src)


def _dedupe(checks):
    seen = {}
    for chk in checks:
        n = seen.get(chk.id, 0)
        seen[chk.id] = n + 1
        if n:
            chk.target = f"{chk.target}#{n}"
    return checks


def detect_all(nl: Netlist, max_level: int):
    counters, lemmas = detect_counters(nl, max_level)
    checks = counters + detect_case(nl) + detect_index(nl) + detect_memory(nl)
    return checks, lemmas
