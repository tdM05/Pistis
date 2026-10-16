#!/usr/bin/env python3
"""Cut an item's `data/nl.json` as two VERBATIM substrings of a LaTeX source file.

This is the OAI-corpus analog of ProofNet's pre-made `nl.json`: openai/math ships prose as `.tex`,
so the statement and proof have to be located in that file. The ONLY operation performed is
`src[a:b]` — literal byte slicing at offsets found by anchor strings. Nothing is unwrapped,
normalized, reflowed, de-duplicated, or macro-expanded:

  - hard line wraps stay as `\\n` exactly where the author put them, mid-sentence included;
  - the two spaces after a sentence period stay two spaces;
  - `\\[ ... \\]` display math keeps its surrounding newlines and leading indent;
  - macros (`\\R`, `\\im`, `\\rank`, `\\abs`) stay unexpanded — `meta.json` records what they mean.

Whitespace and LaTeX ARE the text (pistis-split RULE 2). Tidying them here would silently rewrite
the source of truth that every later stage is gated against byte-for-byte.

The slices are chosen by ANCHORS, not line numbers, so the cut survives upstream edits elsewhere in
the file: `--stmt-from`/`--stmt-to` and `--proof-from`/`--proof-to` are verbatim strings that must
each occur EXACTLY ONCE in the source. The `-to` anchors are inclusive. Every emitted slice is
re-checked to be a literal substring of the file before anything is written.

Usage:
  python3 scripts/extract_tex.py --tex <path.tex> --out <item>/data/nl.json \\
      --stmt-from "For finite index sets" --stmt-to "one has $x_jy_s=0$." \\
      --proof-from "Suppose instead that"  --proof-to "a contradiction."
"""
from __future__ import annotations

import argparse
import json
import sys


def _offset(src: str, anchor: str, what: str) -> int:
    """Index of `anchor` in `src`, requiring it to be unambiguous."""
    n = src.count(anchor)
    if n == 0:
        sys.exit(f"ERROR: {what} anchor not found in source: {anchor!r}")
    if n > 1:
        sys.exit(f"ERROR: {what} anchor occurs {n} times (must be unique), lengthen it: {anchor!r}")
    return src.index(anchor)


def slice_verbatim(src: str, frm: str, to: str, what: str) -> str:
    """`src[start_of(frm) : end_of(to)]` — a literal substring, `to` inclusive."""
    a = _offset(src, frm, f"{what} start")
    b = _offset(src, to, f"{what} end") + len(to)
    if b <= a:
        sys.exit(f"ERROR: {what} end anchor precedes its start anchor")
    out = src[a:b]
    # Paranoia: the result must still be findable verbatim in the source.
    if out not in src:
        sys.exit(f"ERROR: {what} slice is not a literal substring of the source (bug)")
    return out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Cut nl.json as verbatim substrings of a .tex file.")
    ap.add_argument("--tex", required=True, help="path to the LaTeX source file")
    ap.add_argument("--out", required=True, help="path to write, e.g. items/item1/data/nl.json")
    ap.add_argument("--stmt-from", required=True)
    ap.add_argument("--stmt-to", required=True, help="inclusive")
    ap.add_argument("--proof-from", required=True)
    ap.add_argument("--proof-to", required=True, help="inclusive")
    args = ap.parse_args(argv)

    with open(args.tex, encoding="utf-8") as fh:
        src = fh.read()

    statement = slice_verbatim(src, args.stmt_from, args.stmt_to, "statement")
    proof = slice_verbatim(src, args.proof_from, args.proof_to, "proof")

    if statement in proof or proof in statement:
        sys.exit("ERROR: the statement and proof slices overlap")

    with open(args.out, "w", encoding="utf-8") as fh:
        json.dump({"nl_statement": statement, "nl_proof": proof}, fh,
                  ensure_ascii=False, indent=2)
        fh.write("\n")

    print(f"OK: wrote {args.out}")
    print(f"  nl_statement: {len(statement)} chars, {statement.count(chr(10))} newline(s)")
    print(f"  nl_proof:     {len(proof)} chars, {proof.count(chr(10))} newline(s)")
    print("  both slices verified as literal substrings of the source (no normalization applied)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
