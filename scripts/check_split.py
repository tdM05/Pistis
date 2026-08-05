#!/usr/bin/env python3
"""Coverage gate for a Pistis segmentation (`split.json`).

Verifies that a problem's `split.json` tiles its source natural-language text BYTE-FOR-BYTE — the
paper's *coverage* condition: concatenating the segments must recover the original proof
character-for-character (nothing reworded, dropped, duplicated, or reordered).

This is the domain-agnostic tiling gate. It knows nothing about Lean, Mathlib, geometry, or any
particular corpus — it only compares strings. It is shared by every case study.

Source model
------------
A problem's NL source has TWO fields, `nl_statement` and `nl_proof` (in the item's
`<corpus>/item<N>/data/nl.json`). The split tiles the WHOLE thing:

  * the `intro` segment (index 0) must equal `nl_statement` VERBATIM;
  * every NON-intro segment, joined by exactly one space in array order, must equal `nl_proof` VERBATIM.

The two halves are checked independently (no artificial join-space is inserted between the statement
and the proof).

Join semantics (identical to the joined-with-one-space convention): segment texts are concatenated with
EXACTLY ONE space between consecutive segments. Any extra whitespace/newline the source contains at a
boundary must be carried INSIDE a segment slice (trailing the left / leading the right). Whitespace
inside a slice is copied verbatim.

Usage
-----
    python3 scripts/check_split.py <corpus>/item<N>          # e.g. proofnet_verified/item8
    python3 scripts/check_split.py --split-file path/to/split.json --source path/to/nl.json

Exit code 0 = PASS, 1 = FAIL (with an actionable diff), 2 = usage / file error.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
from typing import List, Tuple


def _compare(concat: str, canon: str, label: str) -> Tuple[bool, List[str]]:
    """Byte-for-byte compare `concat` against `canon`. Returns (ok, message-lines).

    On mismatch, pinpoints the divergence the same way the Euclid checker does: first a WORD-level
    divergence (wrong/missing/extra token), else a WHITESPACE-only mismatch (all words match, spacing
    differs), else a length overrun/underrun.
    """
    canon = canon.rstrip("\n")
    concat = concat.rstrip("\n")

    if concat == canon:
        return True, [f"{label}: reproduces source exactly ({len(concat)} chars)"]

    cw, mw = canon.split(), concat.split()
    for j in range(min(len(cw), len(mw))):
        if cw[j] != mw[j]:
            ctx = " ".join(mw[max(0, j - 4):j])
            return False, [
                f"{label}: diverges at word {j}",
                f"  ...{ctx} <HERE>",
                f"  source:    {cw[j]!r}",
                f"  your text: {mw[j]!r}",
            ]
    if len(cw) == len(mw):
        # Same words in the same order, raw strings differ -> a WHITESPACE mismatch: the source has a
        # multi-space/newline run the single-space join didn't reproduce. Keep the extra whitespace
        # INSIDE a slice (trailing left / leading right) so the 1-space join reproduces it.
        k = next((i for i in range(min(len(canon), len(concat))) if canon[i] != concat[i]),
                 min(len(canon), len(concat)))
        return False, [
            f"{label}: whitespace mismatch — all words match, only spacing differs "
            f"(first differs at char {k})",
            f"  source:    {canon[max(0, k - 25):k + 25]!r}",
            f"  your text: {concat[max(0, k - 25):k + 25]!r}",
            "  -> the source has a multi-space/newline run here; keep the extra whitespace INSIDE a "
            "slice (trailing the left / leading the right) so the 1-space join reproduces it.",
        ]
    if len(mw) < len(cw):
        return False, [
            f"{label}: source continues past your last segment — "
            f"missing (e.g.) {' '.join(cw[len(mw):len(mw) + 8])!r} ..."
        ]
    return False, [
        f"{label}: your text runs past the end of the source: "
        f"{' '.join(mw[len(cw):len(cw) + 8])!r} ..."
    ]


def check_tiling(segments: List[dict], nl_statement: str, nl_proof: str) -> Tuple[bool, List[str]]:
    """Core, pure tiling check. `segments` is the ordered split.json array.

    Returns (ok, message-lines). Does not print, read files, or exit — unit-testable directly.
    """
    if not segments:
        return False, ["split is empty — expected at least the intro segment (index 0 = nl_statement)"]

    intro = segments[0]
    if intro.get("role") != "intro":
        return False, [f"segment 0 must have role 'intro' (the nl_statement); got {intro.get('role')!r}"]

    rest = segments[1:]
    # The conclusion (and every non-intro role) tiles nl_proof; only the intro is the statement.
    for i, seg in enumerate(rest, start=1):
        if seg.get("role") == "intro":
            return False, [f"only segment 0 may be 'intro'; segment {i} is also 'intro'"]
        if "text" not in seg:
            return False, [f"segment {i} (role {seg.get('role')!r}) has no 'text' field"]

    ok_stmt, msg_stmt = _compare(intro.get("text", ""), nl_statement, "statement/intro")
    proof_concat = " ".join(seg["text"] for seg in rest)
    ok_proof, msg_proof = _compare(proof_concat, nl_proof, "proof")

    lines = msg_stmt + msg_proof
    return (ok_stmt and ok_proof), lines


def _load_source(source_path: str) -> Tuple[str, str]:
    with open(source_path, encoding="utf-8") as fh:
        d = json.load(fh)
    if "nl_statement" not in d or "nl_proof" not in d:
        raise KeyError(f"{source_path} must have 'nl_statement' and 'nl_proof'")
    return d["nl_statement"], d["nl_proof"]


def _resolve_problem(problem: str) -> Tuple[str, str]:
    """Given an item path `<corpus>/item<N>` (e.g. proofnet_verified/item8), return
    (split_path, source_path).

    Per-item layout: split lives at `<corpus>/item<N>/split.json`; the NL source at
    `<corpus>/item<N>/data/nl.json`.
    """
    itemdir = problem.rstrip("/")
    if not os.path.basename(itemdir):
        raise ValueError(f"expected <corpus>/item<N>, got {problem!r}")
    split_path = os.path.join(itemdir, "split.json")
    source_path = os.path.join(itemdir, "data", "nl.json")
    return split_path, source_path


def main(argv: List[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Coverage (verbatim tiling) gate for a Pistis split.json.")
    ap.add_argument("problem", nargs="?", help="<corpus>/item<N>, e.g. proofnet_verified/item8")
    ap.add_argument("--split-file", help="explicit path to split.json (overrides <problem>)")
    ap.add_argument("--source", help="explicit path to the source json with nl_statement/nl_proof")
    args = ap.parse_args(argv)

    if args.split_file and args.source:
        split_path, source_path = args.split_file, args.source
    elif args.problem:
        try:
            split_path, source_path = _resolve_problem(args.problem)
        except ValueError as e:
            print(f"usage error: {e}", file=sys.stderr)
            return 2
    else:
        ap.print_usage(sys.stderr)
        return 2

    for p in (split_path, source_path):
        if not os.path.exists(p):
            print(f"file not found: {p}", file=sys.stderr)
            return 2

    with open(split_path, encoding="utf-8") as fh:
        segments = json.load(fh)
    nl_statement, nl_proof = _load_source(source_path)

    ok, lines = check_tiling(segments, nl_statement, nl_proof)
    status = "PASS" if ok else "FAIL"
    print(f"{status} — {split_path}")
    for line in lines:
        print(line)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
