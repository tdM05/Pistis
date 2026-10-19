#!/usr/bin/env python3
"""Coverage gate for a Pistis segmentation (`split.json`).

Verifies two of the paper's conditions on a problem's `split.json`:
  1. *coverage* — concatenating the segments recovers the source NL text BYTE-FOR-BYTE (nothing
     reworded, dropped, duplicated, or reordered); and
  2. *substring* (§4) — for every default (reasoning) segment, its `assert` and each `assumptions`
     entry is an EXACT substring of that segment's own `text`.

This is the domain-agnostic tiling gate. It knows nothing about Lean, Mathlib, geometry, or any
particular corpus — it only compares strings. It is shared by every case study.

Source model
------------
A problem's NL source is TWO plain-text files in the item's `<corpus>/item<N>/data/`:
`nl_statement.txt` and `nl_proof.txt`. Each file's bytes ARE the text — no JSON escaping, no
trailing newline, nothing normalized — so the same bytes these gates compare are the bytes you can
Ctrl-F in the paper's `.tex`. The split tiles the WHOLE thing:

  * the `intro` segment (index 0) must equal `nl_statement.txt` VERBATIM;
  * every NON-intro segment, in array order, must tile `nl_proof.txt` VERBATIM (see "Join semantics").

The two halves are checked independently (no artificial join-space is inserted between the statement
and the proof).

Join semantics — ORDERED VERBATIM PARTITION WITH WHITESPACE GAPS. The segments must tile the source as

    source == t1 + g1 + t2 + g2 + ... + g(n-1) + tn

where each `ti` is a segment's text matched VERBATIM and each interior `gi` is a NON-EMPTY,
WHITESPACE-ONLY run taken from the source. So the source is reconstructed byte-for-byte from the
segments plus the inter-segment whitespace; nothing non-whitespace may be dropped, reworded,
duplicated or reordered, and whitespace INSIDE a slice is still copied verbatim.

This generalizes the older "joined by exactly one space" convention, which is the special case
`gi == " "`. The old rule could not express a boundary whose only separator is a newline: the join
inserted a space the source did not have, so a cut there was impossible and two distinct assertions had
to be merged into one segment (visible in tests/test_check_split.py::test_proofnet8_shaped). Hard-wrapped
LaTeX — e.g. openai/math preprints at 72 columns — puts a bare `\n` at a large fraction of its sentence
boundaries, so under the old rule atomicity (one `assert` per segment) was unachievable there. The gap is
whatever whitespace the source actually has, so no segmentation can hide content in it.

Usage
-----
    python3 scripts/check_split.py <corpus>/item<N>          # e.g. proofnet_verified/item8
    python3 scripts/check_split.py --split-file path/to/split.json --source path/to/item/data

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


def tile(texts: List[str], canon: str, label: str) -> Tuple[bool, List[str]]:
    """Check that `texts`, in order, tile `canon` verbatim up to non-empty whitespace gaps.

    Walks `canon` with a cursor: each text must match VERBATIM at the cursor, and between consecutive
    texts the source must supply a non-empty whitespace-only run (the gap). The gaps are taken FROM the
    source, so `t1 + g1 + t2 + ... + tn` is then byte-identical to `canon` — which is asserted at the
    end rather than assumed.

    No backtracking is needed or wanted: a segment must start exactly where the previous one's gap
    ended, which is what makes the partition ordered and total. On failure we delegate the human-readable
    diff to `_compare` on the one-space join, which pinpoints a word/whitespace divergence.
    """
    canon = canon.rstrip("\n")
    if not texts:
        return False, [f"{label}: no segments to tile against a {len(canon)}-char source"]

    for i, t in enumerate(texts):
        if not t.strip():
            return False, [f"{label}: segment {i} has empty/whitespace-only text"]

    pos, gaps = 0, []
    for i, t in enumerate(texts):
        if i > 0:
            start = pos
            while pos < len(canon) and canon[pos].isspace():
                pos += 1
            gap = canon[start:pos]
            if not gap:
                _, msg = _compare(" ".join(texts), canon, label)
                return False, [
                    f"{label}: segment {i} starts immediately after segment {i - 1} with no whitespace "
                    f"between them (char {pos}) — segments must be separated by whitespace in the source",
                ] + msg
            gaps.append(gap)
        if not canon.startswith(t, pos):
            # Either this slice's bytes are wrong, or the previous slice over/under-ran. Show where.
            _, msg = _compare(" ".join(texts), canon, label)
            return False, [
                f"{label}: segment {i} does not match the source at char {pos}",
                f"  source:  {canon[pos:pos + 60]!r}",
                f"  segment: {t[:60]!r}",
            ] + msg
        pos += len(t)

    if pos != len(canon):
        _, msg = _compare(" ".join(texts), canon, label)
        tail = canon[pos:]
        if not tail.strip():
            return False, [f"{label}: {len(tail)} trailing whitespace char(s) left unaccounted: {tail!r}"] + msg
        return False, [f"{label}: source continues past your last segment — "
                       f"missing {tail[:60]!r} ..."] + msg

    # Belt and braces: the partition must literally reassemble the source.
    rebuilt = "".join(t + g for t, g in zip(texts, gaps + [""]))
    if rebuilt != canon:
        return False, [f"{label}: internal error — reassembly from segments + gaps != source"]

    kinds = sorted({repr(g) for g in gaps})
    return True, [f"{label}: reproduces source exactly ({len(canon)} chars, {len(texts)} segment(s), "
                  f"gap(s) {', '.join(kinds) if kinds else 'none'})"]


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
    ok_proof, msg_proof = tile([seg["text"] for seg in rest], nl_proof, "proof")

    ok_sub, msg_sub = _check_substrings(segments)

    lines = msg_stmt + msg_proof + msg_sub
    return (ok_stmt and ok_proof and ok_sub), lines


# Roles that are STRUCTURAL: they carry only `text` (no assumptions/assert).
_STRUCTURAL_ROLES = {"intro", "wts", "conclusion"}


def _check_substrings(segments: List[dict]) -> Tuple[bool, List[str]]:
    """Enforce the paper's condition (§4): for every DEFAULT segment, `assert` and each `assumptions`
    entry must be an EXACT substring of that segment's `text`. Structural segments (intro/wts/conclusion)
    carry neither and are skipped.
    """
    errors: List[str] = []
    for i, seg in enumerate(segments):
        role = seg.get("role")
        text = seg.get("text", "")
        if role in _STRUCTURAL_ROLES:
            # Structural segments must NOT carry assumptions/assert.
            for f in ("assumptions", "assert"):
                if seg.get(f):
                    errors.append(f"segment {i} (role {role!r}) should not carry {f!r}")
            continue
        # Default segment: must have a single assert, an exact substring of text.
        assertion = seg.get("assert")
        if assertion is None:
            errors.append(f"segment {i}: default segment has no 'assert'")
        elif assertion not in text:
            errors.append(
                f"segment {i}: assert is not a substring of text\n"
                f"  assert: {assertion!r}\n"
                f"  text:   {text!r}"
            )
        # Every assumption must be an exact substring of text.
        assumptions = seg.get("assumptions", [])
        if not isinstance(assumptions, list):
            errors.append(f"segment {i}: 'assumptions' must be a list (a set of substrings)")
        else:
            for a in assumptions:
                if a not in text:
                    errors.append(
                        f"segment {i}: assumption is not a substring of text\n"
                        f"  assumption: {a!r}\n"
                        f"  text:       {text!r}"
                    )
    if errors:
        return False, ["substring check FAILED:"] + errors
    return True, ["substring check: all assert/assumptions are substrings of their segment"]


NL_FILES = ("nl_statement.txt", "nl_proof.txt")


def load_nl(data_dir: str) -> Tuple[str, str]:
    """(nl_statement, nl_proof) read verbatim from `<data_dir>/nl_{statement,proof}.txt`.

    The files ARE the text — their bytes are the paper's bytes, with no trailing newline and no
    normalization (see scripts/convert_nl_to_txt.py). So this reads them with `newline=""` to keep
    universal-newline translation from rewriting a `\r\n` the source actually has; every gate here
    compares byte-for-byte, and silently repairing line endings on load is exactly the kind of
    invisible edit those gates exist to catch.
    """
    out = []
    for name in NL_FILES:
        path = os.path.join(data_dir, name)
        if not os.path.exists(path):
            raise FileNotFoundError(f"{path} not found (expected {' and '.join(NL_FILES)} in {data_dir})")
        with open(path, encoding="utf-8", newline="") as fh:
            out.append(fh.read())
    return out[0], out[1]


def _resolve_problem(problem: str) -> Tuple[str, str]:
    """Given an item path `<corpus>/item<N>` (e.g. proofnet_verified/item8), return
    (split_path, data_dir).

    Per-item layout: split lives at `<corpus>/item<N>/split.json`; the NL source is the pair of
    `.txt` files in `<corpus>/item<N>/data/`.
    """
    itemdir = problem.rstrip("/")
    if not os.path.basename(itemdir):
        raise ValueError(f"expected <corpus>/item<N>, got {problem!r}")
    split_path = os.path.join(itemdir, "split.json")
    data_dir = os.path.join(itemdir, "data")
    return split_path, data_dir


def main(argv: List[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Coverage (verbatim tiling) gate for a Pistis split.json.")
    ap.add_argument("problem", nargs="?", help="<corpus>/item<N>, e.g. proofnet_verified/item8")
    ap.add_argument("--split-file", help="explicit path to split.json (overrides <problem>)")
    ap.add_argument("--source", help="explicit path to the dir holding nl_statement.txt/nl_proof.txt")
    args = ap.parse_args(argv)

    if args.split_file and args.source:
        split_path, data_dir = args.split_file, args.source
    elif args.problem:
        try:
            split_path, data_dir = _resolve_problem(args.problem)
        except ValueError as e:
            print(f"usage error: {e}", file=sys.stderr)
            return 2
    else:
        ap.print_usage(sys.stderr)
        return 2

    for p in (split_path, data_dir):
        if not os.path.exists(p):
            print(f"file not found: {p}", file=sys.stderr)
            return 2

    with open(split_path, encoding="utf-8") as fh:
        segments = json.load(fh)
    try:
        nl_statement, nl_proof = load_nl(data_dir)
    except FileNotFoundError as e:
        print(str(e), file=sys.stderr)
        return 2

    ok, lines = check_tiling(segments, nl_statement, nl_proof)
    status = "PASS" if ok else "FAIL"
    print(f"{status} — {split_path}")
    for line in lines:
        print(line)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
