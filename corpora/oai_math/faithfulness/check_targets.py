#!/usr/bin/env python3
"""Gate: a datapoint's targets are EXACTLY the texts it claims to be — on BOTH sides.

Formal side. For a `seg-*` unit that means the proposition inside `(stepK : …)` in `Main.lean` — the
thing the segment asserts — with nothing added and nothing dropped. Not the binder name, not the
tactic around it, not the `obtain`/`set`/`have` lines above it, not the `:= by` body. A segment
asserts its claim and only its claim, so that proposition is the whole of what its sentence is judged
against; anything else in `T_F` is text the prose was never answering, and padding a target is the one
way to make an alignment look complete while the sentence is not actually being checked. For the
`statement` unit it means the item's header plus the theorem signature, as `tf_norm.normalize_tf`
flattens it. For an `asm-*` unit it means the TYPE on its `-- @pistis_assumption ("clause", TYPE)`
marker, which is where a consumed premise's formalization lives.

NL side, for segments. The target is the segment MINUS the substrings `split.json` lists under
`assumptions`, one `…` left where each stood — the paper's `assert(s_i)`. This half is checked for
the same reason the formal half is: a target that quietly keeps the premises in it is a target the
claim cannot answer, and the way to make it answerable is to widen the claim into a conjunction,
which breaks Atomicity (`check_main.py` check 6). So the subtraction is re-derived here from
`Main.lean` + `split.json` and compared character for character.

The check is deliberately INDEPENDENT of `pistis_proof.proof_outline`: the claims are re-read from
`Main.lean` with `pistis_lean.parse_main` and the markers with `pistis_lean.parse_assumptions`, the
same parsers `check_main.py` gates the prose with, and the assumption lists come from `split.json`
itself. So it catches a stale datapoint on disk AND a change of mind in the generator. Only the
subtraction rule itself is shared (`segment_nl_target`), because a second copy of that could drift
from the one the datapoints are built with and then agree with nothing.

Exit status: 0 when every target matches, 1 otherwise.
Usage:
    python3 faithfulness/check_targets.py                 # every items/item*
    python3 faithfulness/check_targets.py items/item1
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent                                  # the corpus root
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "ui"))
from pistis_proof import (                          # noqa: E402
    PISTIS_SCRIPTS, _statement_target, assumption_markers, proof_outline, segment_nl_target,
    segment_target,
)
from gen_datapoints import stored_target            # noqa: E402
from pistis_lean import parse_main                  # noqa: E402

assert PISTIS_SCRIPTS.is_dir()                      # imported for its path side effect


def _first_difference(want: str, got: str) -> str:
    """Where `got` first departs from `want`, as a line the reader can act on."""
    i = 0
    while i < min(len(want), len(got)) and want[i] == got[i]:
        i += 1
    if i == len(want) and len(got) > len(want):
        return f"{len(got) - len(want)} extra character(s) at the end: {got[i:]!r}"
    if i == len(got) and len(want) > len(got):
        return f"truncated: {want[i:]!r} is missing from the end"
    return f"differs at character {i}: expected {want[i:i + 40]!r}, found {got[i:i + 40]!r}"


def _expected(item_dir: Path) -> dict[str, str]:
    """`{unit id: the exact text its T_F must hold}`, read straight from `Main.lean`."""
    src = (item_dir / "Main.lean").read_text(encoding="utf-8")
    want = {"statement": _statement_target(src)}
    for seg in parse_main(src):
        if seg["kind"] == "segment":
            want[f"seg-{seg['loc']}"] = segment_target(seg)
    for uid, mark in assumption_markers(src).items():
        want[uid] = mark["type"]
    return want


def _expected_nl(item_dir: Path) -> dict[str, str]:
    """`{unit id: the exact text its T_N must hold}` for the units whose NL target is COMPUTED.

    That is the segments, whose target is the sentence minus its assumptions. The `statement` unit's
    `T_N` is a whole file and an `asm-*` unit's is a `split.json` entry quoted verbatim; both are
    plain copies, and `check_verbatim.py` already holds every `T_N` to being text the source
    contains. What needs gating here is the SUBTRACTION — the one target in the tree that is not a
    copy of anything.
    """
    src = (item_dir / "Main.lean").read_text(encoding="utf-8")
    split = json.loads((item_dir / "split.json").read_text(encoding="utf-8"))
    want: dict[str, str] = {}
    for seg in parse_main(src):
        if seg["kind"] != "segment":
            continue
        pos = int(seg["loc"].rsplit(".", 1)[-1])
        entry = split[pos] if 0 <= pos < len(split) else {}
        want[f"seg-{seg['loc']}"] = segment_nl_target(
            seg["text"], list(entry.get("assumptions") or []))
    return want


_NOUN = {
    "segment": "the claim inside `(stepK : …)`",
    "assumption": "the TYPE on its `-- @pistis_assumption (\"clause\", TYPE)` marker",
    "statement": "the theorem statement",
}


def check_item(item_dir: Path) -> list[str]:
    item_dir = item_dir.resolve()
    want = _expected(item_dir)
    want_nl = _expected_nl(item_dir)
    errors: list[str] = []

    # 1. the generator still derives the targets this gate demands
    for unit in proof_outline(item_dir)["units"]:
        uid = unit["id"]
        if uid not in want:
            errors.append(f"{uid}: proof_outline produced a unit this gate does not know about")
        elif unit["formal"] != want[uid]:
            errors.append(f"{uid}: proof_outline's formal target is not "
                          f"{_NOUN.get(unit['kind'], 'what this gate expects')} — "
                          f"{_first_difference(want[uid], unit['formal'])}")
        if uid in want_nl and unit["nl_text"] != want_nl[uid]:
            errors.append(f"{uid}: proof_outline's NL target is not the segment MINUS its "
                          f"`assumptions` (the paper's assert) — "
                          f"{_first_difference(want_nl[uid], unit['nl_text'])}")

    # 2. and the datapoints on disk still hold them
    align = item_dir / "align"
    for d in sorted(p for p in align.glob("*") if p.is_dir()) if align.is_dir() else []:
        uid = d.name
        tf = d / "artifacts" / "formal" / "T_F.lean"
        if uid not in want:
            errors.append(f"{uid}: no such unit in Main.lean — a leftover datapoint; delete {d}")
            continue
        if not tf.exists():
            errors.append(f"{uid}: no artifacts/formal/T_F.lean (run gen_datapoints.py)")
            continue
        got, expect = tf.read_text(encoding="utf-8"), stored_target(want[uid])
        if got != expect:
            kind = ("segment" if uid.startswith("seg-")
                    else "assumption" if uid.startswith("asm-") else "statement")
            errors.append(f"{uid}: T_F.lean is not {_NOUN[kind]} — "
                          f"{_first_difference(expect, got)}\n"
                          f"           want: {want[uid]!r}\n"
                          f"           got:  {got.rstrip(chr(10))!r}")
        # the NL half, for the one target that is computed rather than copied
        tn = d / "artifacts" / "nl" / "T_N.txt"
        if uid in want_nl and tn.exists():
            got_n, expect_n = tn.read_text(encoding="utf-8"), stored_target(want_nl[uid])
            if got_n != expect_n:
                errors.append(f"{uid}: T_N.txt is not the segment MINUS its `assumptions` — "
                              f"{_first_difference(expect_n, got_n)}\n"
                              f"           want: {want_nl[uid]!r}\n"
                              f"           got:  {got_n.rstrip(chr(10))!r}")
    missing = [uid for uid in want if not (align / uid / "artifacts" / "formal" / "T_F.lean").exists()]
    for uid in missing:
        if not any(uid in e for e in errors):
            errors.append(f"{uid}: no datapoint on disk (run gen_datapoints.py)")
    return errors


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Check every datapoint's T_F against Main.lean.")
    ap.add_argument("items", nargs="*", help="item dirs, e.g. items/item1 (default: all)")
    args = ap.parse_args(argv)
    dirs = [Path(p) for p in args.items] or sorted(
        p for p in (REPO / "items").glob("item*") if (p / "Main.lean").exists())
    total = 0
    for d in dirs:
        errors = check_item(d)
        print(f"[{'FAIL' if errors else 'ok'}] {d}")
        for e in errors:
            print("    ERROR  " + e)
        total += len(errors)
    print(f"\n{total} target mismatch(es)" if total else "\nevery T_F is exactly its formal target")
    return 1 if total else 0


if __name__ == "__main__":
    raise SystemExit(main())
