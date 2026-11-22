# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Structure detectors: find counters, unique/parallel case muxes, variable
part-selects and memories in a flattened netlist and turn each into checks.

Check ids are structural (the register, memory or destination signal the
check is about), so waivers survive edits elsewhere in the source.
"""

from __future__ import annotations

import os

from .checks import INFO, Check, Lemma, src_key
from .netlist import FF_TYPES, Netlist, attr_true, const_value, is_const

COMPARE_TYPES = {"$eq", "$ne", "$eqx", "$nex", "$lt", "$le", "$gt", "$ge"}
MAX_PATHS = 64
MAX_BMUX = 64


def _mask(w: int) -> int:
    return (1 << w) - 1


def clean_conds(conds):
    """Drop constant-true and duplicate conditions.  Returns None when the
    conditions can never hold (a constant mismatch or a contradiction): the
    logic is dead, so the check is skipped rather than reported."""
    out, seen = [], {}
    for b, v in conds:
        if is_const(b):
            if b in ("0", "1") and b != str(v):
                return None
            continue
        if b in seen:
            if seen[b] != v:
                return None
            continue
        seen[b] = v
        out.append((b, v))
    return out


def _bits_of(v: int, n: int):
    return [(v >> i) & 1 for i in range(n)]


# --------------------------------------------------------------- mux trees
def mux_sources(nl: Netlist, bits: list, conds=(), depth=0, out=None):
    """Enumerate the sources feeding `bits` through a $mux/$pmux/$bmux tree.

    Returns [(bits_of_source, conditions)], conditions being (select_bit,
    value) pairs that must hold for that source to be selected.  Infeasible
    paths (constant or contradictory selects) are dropped.  Beyond the path
    and depth limits a sub-tree is returned unexpanded, as one opaque source,
    so the result always accounts for every way a value can arrive (reset
    discovery relies on that).
    """
    if out is None:
        out = []
    if clean_conds(conds) is None:
        return out
    if len(out) >= MAX_PATHS or depth > 24:
        out.append((bits, list(conds)))
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
        mux_sources(nl, nl.conn(cell, "A")[off:off + w], list(conds) + [(sb, 0) for sb in sel],
                    depth + 1, out)
    elif t == "$bmux" and port == "Y" and (1 << len(nl.conn(cell, "S"))) <= MAX_BMUX:
        width = nl.param(cell, "WIDTH")
        sel = nl.conn(cell, "S")
        a = nl.conn(cell, "A")
        for i in range(1 << len(sel)):
            c = list(conds) + list(zip(sel, _bits_of(i, len(sel))))
            mux_sources(nl, a[i * width + off:i * width + off + w], c, depth + 1, out)
    else:
        out.append((bits, list(conds)))
    return out


def forward(nl: Netlist, bits: list, max_depth=16):
    """Follow `bits` through the mux tree that consumes them.

    Returns (conditions, destination_bits): the conditions under which the
    value propagates, and where it ends up (a register's Q, or the net where
    the mux chain stops).  conditions is None if it can never propagate.
    """
    conds = []
    cur = list(bits)
    dest = None
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
            q = nl.conn(cell, "Q")
            dest = [q[o] for o in offs]
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
        elif t == "$bmux" and port == "A":
            width = nl.param(cell, "WIDTH")
            sel = nl.conn(cell, "S")
            idx = {o // width for o in offs}
            if len(idx) != 1:
                break
            i = idx.pop()
            conds += list(zip(sel, _bits_of(i, len(sel))))
            cur = [nl.conn(cell, "Y")[o - i * width] for o in offs]
        else:
            break
    return clean_conds(conds), (dest or cur)


def _dest_name(nl: Netlist, dest: list, fallback_bits: list, src: str) -> str:
    """Structural name for an anonymous object: the signal its value lands in."""
    for bits in (dest, fallback_bits):
        name = nl.visible_name(bits) if bits else None
        if name:
            return name
        if bits:
            names = {nl.bit_name.get(b, "").rsplit("[", 1)[0] for b in bits if not is_const(b)}
            names.discard("")
            visible = [n for n in names if not n.startswith("$")]
            if len(visible) == 1:
                return visible[0]
    return os.path.basename(src)


# ---------------------------------------------------------------- counters
def _operand_is(bits: list, q: list) -> bool:
    """bits == q, optionally zero-extended."""
    if len(bits) < len(q) or bits[:len(q)] != q:
        return False
    return all(b == "0" for b in bits[len(q):])


def _fit(bits: list, w: int):
    """Resize an operand to w bits if that loses nothing (zero-extension)."""
    if len(bits) >= w:
        return bits[:w] if all(b == "0" for b in bits[w:]) else None
    return bits + ["0"] * (w - len(bits))


def _signed_val(v: int, w: int) -> int:
    return v - (1 << w) if v >> (w - 1) & 1 else v


def _compares(nl: Netlist, q: list):
    """(constants, other-operand bit lists) that q is compared against."""
    ks, others = set(), []
    for cell in sorted(nl.compare_cells(q, COMPARE_TYPES)):
        a, b = nl.conn(cell, "A"), nl.conn(cell, "B")
        for x, y in ((a, b), (b, a)):
            if _operand_is(x, q):
                k = const_value(y)
                if k is not None:
                    ks.add(k)
                elif not any(b in q for b in y if not is_const(b)):
                    yy = _fit(y, len(q))
                    if yy is not None and yy not in others:
                        others.append(yy)
    return ks, others


def detect_counters(nl: Netlist, max_level: int):
    checks, lemmas = [], {}
    for cell, c in nl.cells.items():
        if c["type"] not in FF_TYPES or c["type"] == "$anyinit" or "D" not in c["connections"]:
            continue
        ff = nl.ff_info(cell)
        q, d = ff["Q"], ff["D"]
        w = len(q)
        if w < 2 or any(is_const(b) for b in q):
            continue
        paths = mux_sources(nl, d)
        steps = []      # (dir, step, signed, conds)
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
            signed = bool(nl.param(acell, "A_SIGNED", 0)) and bool(nl.param(acell, "B_SIGNED", 0))
            if _operand_is(a, q) and const_value(b) is not None:
                steps.append(("up" if at == "$add" else "down", b, signed, conds))
            elif at == "$add" and _operand_is(b, q) and const_value(a) is not None:
                steps.append(("up", a, signed, conds))
        if not steps:
            continue

        name = nl.name_of(q)
        src = nl.net_src(q)
        if src == "?":
            src = nl.cell_src(cell)
        waive = nl.net_attr(q, "fvlint_waive")
        ks, others = _compares(nl, q)
        any_signed = False
        counts_up = False
        for direction, step_bits, signed, conds in steps:
            raw = const_value(step_bits)
            # A signed add of a negative constant is a decrement.
            if signed:
                step = _signed_val(raw & _mask(len(step_bits)), len(step_bits))
                if step < 0:
                    direction, step = ("down" if direction == "up" else "up"), -step
            else:
                step = raw
            if step <= 0 or step > _mask(w):
                continue
            all_conds = clean_conds(conds + ff["conds"])
            if all_conds is None:
                continue
            any_signed |= signed
            counts_up |= direction == "up"
            bounded = nl.depends_on([b for b, _ in all_conds], set(q), max_level)
            kind = "counter_overflow" if direction == "up" else "counter_underflow"
            if signed:
                smin, smax = -(1 << (w - 1)), (1 << (w - 1)) - 1
                lo, hi = (smin, smax - step) if direction == "up" else (smin + step, smax)
                desc = (f"signed {name} {'+' if direction == 'up' else '-'} {step} stays within "
                        f"{smin}..{smax}")
            else:
                lo, hi = (0, _mask(w) - step) if direction == "up" else (step, _mask(w))
                desc = (f"{name} + {step} never wraps past {_mask(w)} ({w} bits)" if direction == "up"
                        else f"{name} - {step} never wraps below 0")
            chk = Check(kind=kind, target=name, src=src, desc=desc, checker="fvl_range",
                        params={"W": w, "LO": lo, "HI": hi, "SIGNED": int(signed)},
                        ports={"v": q}, conds=all_conds, anchors=[cell], waive_attr=waive,
                        depth_hint=(1 << w) // step + 2)
            if not bounded:
                chk.preset = INFO
                chk.detail = ("free-running: the increment condition does not depend on the "
                              "counter, so wrap-around looks intentional; not checked")
            checks.append(chk)

        # Candidate invariants (Houdini-filtered later): q <= K for the
        # constants q is compared against (largest first: the clearing/limit
        # compare usually bounds the counter), the largest load value of a
        # counter that only counts down, and q <= r for signals q is compared
        # with.  Values are taken in the counter's own (signed or unsigned)
        # domain; q <= min and q <= max say nothing useful about a counter and
        # are skipped.  Kept small on purpose: each false candidate costs
        # solver queries.
        val = (lambda k: _signed_val(k, w)) if any_signed else (lambda k: k)
        lo_end, hi_end = ((-(1 << (w - 1)), (1 << (w - 1)) - 1) if any_signed else (0, _mask(w)))
        useful = lambda k: lo_end < val(k) < hi_end  # noqa: E731
        cands = sorted({k for k in ks if useful(k)}, key=val, reverse=True)[:3]
        top_load = max(loads, key=val) if loads else None
        if not counts_up and top_load is not None and useful(top_load) and top_load not in cands:
            cands.append(top_load)
        for k in cands:
            lemmas.setdefault(cell, []).append(Lemma(
                owner=cell, desc=f"{name} <= {val(k)}", checker="fvl_range",
                params={"W": w, "LO": lo_end, "HI": val(k), "SIGNED": int(any_signed)},
                ports={"v": q}, bound=k))
        # Whole signals first (a zero-extended slice is a weaker bound), then
        # by name: the choice must not depend on cell names or set order.
        ranked = sorted(others, key=lambda r: (sum(is_const(b) for b in r), nl.name_of(r)))
        for r in ranked[:2]:
            lemmas.setdefault(cell, []).append(Lemma(
                owner=cell, desc=f"{name} <= {nl.name_of(r)}", checker="fvl_rel",
                params={"W": w, "SIGNED": int(any_signed)}, ports={"a": q, "b": r}))
    return _dedupe(checks), lemmas


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
        y = nl.conn(cell, "Y")
        conds, dest = forward(nl, y)
        if conds is None:
            continue   # the case result is never used (constant-disabled logic)
        src = nl.cell_src(cell)
        target = _dest_name(nl, dest, y, src)
        checks.append(Check(
            kind="parallel_case", target=target, src=src,
            desc="at most one item of a unique/parallel_case statement matches",
            checker="fvl_onehot0", params={"W": len(sel)}, ports={"s": sel}, conds=conds))
        # full_case from the source (renamed at elaboration; proc_rmdead also
        # marks every case that has a default item).  Yosys implements it as
        # an 'x default: when no item that assigns the signal matches, the
        # synthesized value is arbitrary, while simulation keeps the value the
        # code assigned before the case.
        a = nl.conn(cell, "A")
        if attr_true(attrs.get("fvlint_full_case")) and a and all(b == "x" for b in a):
            checks.append(Check(
                kind="full_case", target=target, src=src,
                desc="an item of a full_case/unique case statement (no default) assigns the signal",
                checker="fvl_nonzero", params={"W": len(sel)}, ports={"s": sel}, conds=conds))
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
        a, y = nl.conn(cell, "A"), nl.conn(cell, "Y")
        aw, yw = len(a), len(y)
        hi = aw - yw
        if hi < 0:
            continue
        bw = len(b)
        signed = nl.param(cell, "B_SIGNED", 0)
        # The offset is checked with an unsigned compare against 0..HI, which
        # also rejects negative signed offsets (MSB set) as long as HI is
        # below the sign bit; so HI is clamped to the largest offset B can
        # express.  An unsigned offset that can never exceed hi needs no check.
        top = (1 << (bw - 1)) - 1 if signed else _mask(bw)
        if not signed and hi >= top:
            continue
        conds, dest = forward(nl, y)
        if conds is None:
            continue
        src = nl.cell_src(cell)
        checks.append(Check(
            kind="index_range", target=_dest_name(nl, dest, y, src), src=src,
            desc=f"variable select offset stays within 0..{hi} ({aw}-bit vector, {yw}-bit slice)",
            checker="fvl_range", params={"W": bw, "LO": 0, "HI": min(hi, top), "SIGNED": 0},
            ports={"v": b}, conds=conds))
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
            conds, _ = forward(nl, rd_data[i * width:(i + 1) * width])
            if conds is None or en == ["0"]:
                continue
            checks.append(Check(
                kind="mem_addr", target=f"{memid}.rd{i}", src=src,
                desc=f"read address of {memid}[{lo}:{hi}] stays in range", checker="fvl_range",
                params={"W": abits, "LO": lo, "HI": hi, "SIGNED": 0}, ports={"v": addr, "e": en},
                conds=conds, waive_attr=waive))
        wr_addr, wr_en = nl.conn(cell, "WR_ADDR"), nl.conn(cell, "WR_EN")
        for i in range(nl.param(cell, "WR_PORTS", 0)):
            addr = wr_addr[i * abits:(i + 1) * abits]
            en = wr_en[i * width:(i + 1) * width]
            if all(is_const(x) for x in addr) or all(b == "0" for b in en):
                continue
            checks.append(Check(
                kind="mem_addr", target=f"{memid}.wr{i}", src=src,
                desc=f"write address of {memid}[{lo}:{hi}] stays in range", checker="fvl_range",
                params={"W": abits, "LO": lo, "HI": hi, "SIGNED": 0}, ports={"v": addr, "e": en},
                waive_attr=waive))
    return checks


def _dedupe(checks):
    """Several objects with the same structural name (e.g. two case statements
    assigning one register) get '#n' suffixes in source order."""
    groups = {}
    for chk in checks:
        groups.setdefault(chk.id, []).append(chk)
    for group in groups.values():
        if len(group) > 1:
            for n, chk in enumerate(sorted(group, key=lambda c: src_key(c.src))):
                if n:
                    chk.target = f"{chk.target}#{n}"
    return checks


def detect_all(nl: Netlist, max_level: int):
    counters, lemmas = detect_counters(nl, max_level)
    checks = counters + detect_case(nl) + detect_index(nl) + detect_memory(nl)
    return checks, lemmas
