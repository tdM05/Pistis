#!/usr/bin/env python3
"""Faithfulness gate for a mapped `Main.lean` (the map-stage analog of check_split.py).

After the map stage fills `Main.lean`, this checks — source-level, no Lean build — that the map is
FAITHFUL by the paper's conditions that survive into Main:

  1. coverage — the `pistis_*` segment texts recovered from Main tile the item's nl.json BYTE-FOR-BYTE
     (statement/intro == nl_statement; the joined non-intro segments == nl_proof), and in the SAME order
     and locators the scaffold stamped (the map agent must never edit text/locator/order);
  2. no vacuous claim — no `pistis_segment` claim is `True` (RULE 2: every reasoning segment asserts
     something);
  3. no stray sorry — every `sorry` sits in a `pistis_segment := by sorry` body or a `have … := by
     sorry`; in particular the scaffold's `@pistis_closer` placeholder line must be GONE;
  4. no unfilled assumption — no `@pistis_assumption (..., TODO)` remains.

`lake env lean Main.lean` (that it ELABORATES) is a SEPARATE gate the map skill runs; this script is the
build-free faithfulness half.

Usage:
    python3 scripts/check_main.py <corpus>/item<N>          # e.g. proofnet_verified/item8
    python3 scripts/check_main.py --main path/to/Main.lean --source path/to/nl.json

Exit 0 = PASS, 1 = FAIL, 2 = usage / file error.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
from typing import List, Tuple

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_split import _compare, tile  # reuse the exact same tiling gate as the split stage
from pistis_lean import parse_main, parse_assumptions


def _strip_comments_and_strings(src: str) -> str:
    """Blank `--` line comments, `/- -/` block comments, and `"..."` string literals (keep newlines) so
    a `sorry` scan sees only real code — never a `sorry` inside a segment's TEXT or a comment."""
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        two = src[i:i + 2]
        if depth == 0 and two == "--":
            while i < n and src[i] != "\n":
                out.append(" "); i += 1
            continue
        if two == "/-":
            depth += 1; out.append("  "); i += 2; continue
        if two == "-/" and depth > 0:
            depth -= 1; out.append("  "); i += 2; continue
        if depth > 0:
            out.append("\n" if src[i] == "\n" else " "); i += 1; continue
        if src[i] == '"':
            i += 1
            out.append(" ")
            while i < n and src[i] != '"':
                if src[i] == "\\" and i + 1 < n:
                    out.append("  "); i += 2; continue
                out.append("\n" if src[i] == "\n" else " "); i += 1
            if i < n:
                out.append(" "); i += 1
            continue
        out.append(src[i]); i += 1
    return "".join(out)


def check_main(main_src: str, nl_statement: str, nl_proof: str) -> Tuple[bool, List[str]]:
    """Pure faithfulness check of a mapped Main.lean. Returns (ok, message-lines)."""
    segs = parse_main(main_src)
    if not segs:
        return False, ["no pistis_* segments found in Main.lean"]

    intro = segs[0]
    lines: List[str] = []
    ok = True

    # (1) coverage: intro == nl_statement; joined non-intro == nl_proof
    if intro["kind"] != "intro":
        ok = False
        lines.append(f"segment 0 must be pistis_intro (the statement); got pistis_{intro['kind']}")
    ok_stmt, msg_stmt = _compare(intro["text"], nl_statement, "statement/intro")
    rest = segs[1:]
    ok_proof, msg_proof = tile([s["text"] for s in rest], nl_proof, "proof")
    lines += msg_stmt + msg_proof
    ok = ok and ok_stmt and ok_proof

    # (2) no vacuous claim
    vacuous = [s for s in segs if s["kind"] == "segment" and s["claim"].strip() == "True"]
    if vacuous:
        ok = False
        lines.append("vacuous claims (still `True` — RULE 2):")
        for s in vacuous:
            lines.append(f"  line {s['line']}: {s['name']} : True   (loc {s['loc']})")

    # (3) no stray sorry: a `sorry` is only allowed immediately after `:= by`
    code = _strip_comments_and_strings(main_src)
    for m in re.finditer(r"\bsorry\b", code):
        prefix = code[:m.start()]
        # legal iff the nearest preceding non-space tokens are `:= by`
        if not re.search(r":=\s*by\s*$", prefix):
            ln = main_src.count("\n", 0, m.start()) + 1
            ok = False
            lines.append(f"stray sorry at line {ln}: a sorry is only allowed as a `:= by sorry` body "
                         f"(the @pistis_closer placeholder must be replaced)")

    # (4) no unfilled @pistis_assumption TODO
    todos = [a for a in parse_assumptions(main_src) if a["type"] == "TODO"]
    if todos:
        ok = False
        lines.append("unfilled @pistis_assumption TODO:")
        for a in todos:
            lines.append(f"  line {a['line']}: (\"{a['text']}\", TODO)")

    if ok:
        n_seg = sum(1 for s in segs if s["kind"] == "segment")
        lines.append(f"faithful: {n_seg} segment claim(s) filled, coverage + no-stray-sorry OK")
    return ok, lines


def _resolve(item: str) -> Tuple[str, str]:
    item = item.rstrip("/")
    return os.path.join(item, "Main.lean"), os.path.join(item, "data", "nl.json")


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Faithfulness gate for a mapped Main.lean.")
    ap.add_argument("item", nargs="?", help="<corpus>/item<N>, e.g. proofnet_verified/item8")
    ap.add_argument("--main", help="explicit path to Main.lean")
    ap.add_argument("--source", help="explicit path to nl.json")
    args = ap.parse_args(argv)

    if args.main and args.source:
        main_path, source_path = args.main, args.source
    elif args.item:
        main_path, source_path = _resolve(args.item)
    else:
        ap.print_usage(sys.stderr)
        return 2

    for p in (main_path, source_path):
        if not os.path.exists(p):
            print(f"file not found: {p}", file=sys.stderr)
            return 2

    main_src = open(main_path, encoding="utf-8").read()
    d = json.load(open(source_path, encoding="utf-8"))
    ok, lines = check_main(main_src, d["nl_statement"], d["nl_proof"])
    print(f"{'PASS' if ok else 'FAIL'} — {main_path}")
    for line in lines:
        print(line)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
