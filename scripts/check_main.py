#!/usr/bin/env python3
"""Faithfulness gate for a mapped `Main.lean` (the map-stage analog of check_split.py).

After the map stage fills `Main.lean`, this checks — source-level, no Lean build — that the map is
FAITHFUL by the paper's conditions that survive into Main:

  1. coverage — the `pistis_*` segment texts recovered from Main tile the item's NL source BYTE-FOR-BYTE
     (statement/intro == nl_statement.txt; the joined non-intro segments == nl_proof.txt), and in the SAME order
     and locators the scaffold stamped (the map agent must never edit text/locator/order). A
     `pistis_assumption`'s text is EXCLUDED from this tiling — it is a substring of the `pistis_segment`
     it is wired to (same `loc`), already counted once there, and tiling it a second time would double
     it.
  2. no vacuous claim — no `pistis_segment` or `pistis_assumption` claim is `True` (RULE 2: every
     reasoning segment asserts something, and `True` is the scaffold's unfilled-placeholder sentinel
     for an assumption's type too);
  3. no stray sorry — every `sorry` sits in a `pistis_segment`/`pistis_assumption := by sorry` body or
     a `have … := by sorry`; in particular the scaffold's `@pistis_closer` placeholder line must be
     GONE;
  4. verbatim bytes — each segment's and each assumption's NL text occurs in `Main.lean` AS ITSELF,
     i.e. it is stored in a raw literal `r"…"`. Check 1 only compares decoded VALUES, so an escaped
     `"…\\\\subseteq…"` passes it while the file says something the paper does not and Ctrl-F finds
     nothing; this is the check on the bytes, which nothing here had before.
  5. assumptions wired — every `assumptions` entry a segment has in `split.json` is still a
     `pistis_assumption "<that segment's loc>" "entry" (name : TYPE) := by …` tactic sharing that
     segment's `loc`, and no segment has one `split.json` does not list. Needs `split.json`, so it
     runs in the `<corpus>/item<N>` form only.

`lake env lean Main.lean` (that it ELABORATES) is a SEPARATE gate the map skill runs; this script is the
build-free faithfulness half.

Usage:
    python3 scripts/check_main.py <corpus>/item<N>          # e.g. proofnet_verified/item8
    python3 scripts/check_main.py --main path/to/Main.lean --source path/to/item/data

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
from check_split import _compare, load_nl, tile  # the exact same tiling gate + loader as the split stage
from pistis_lean import parse_main, raw_open


def _strip_comments_and_strings(src: str) -> str:
    """Blank `--` line comments, `/- -/` block comments, and string literals (keep newlines) so a
    `sorry` scan sees only real code — never a `sorry` inside a segment's TEXT or a comment.

    Raw literals (`r"…"`, `r#"…"#`) are blanked as a unit. They have to be: NL text is stored raw, a
    LaTeX `\\"` in it does NOT escape the quote the way it would in an ordinary literal, so scanning
    one with the ordinary rules can run off the end of the string and blank real code after it.
    """
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        two = src[i:i + 2]
        if depth == 0 and two == "--":
            while i < n and src[i] != "\n":
                out.append(" "); i += 1
            continue
        if depth == 0 and src[i] == "r":
            m = raw_open(src, i)
            if m:
                close = '"' + m.group(1)
                j = src.find(close, m.end())
                j = n if j < 0 else j + len(close)
                out.append("".join("\n" if c == "\n" else " " for c in src[i:j]))
                i = j
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


def _check_assumptions(segs: List[dict], segments: List[dict]) -> Tuple[bool, List[str]]:
    r"""Check 5: `split.json`'s `assumptions` survive in Main as `pistis_assumption` tactics.

    ATOMICITY is the paper's condition that a segment has a SINGLE assertion, with its premises as
    `assumps(s_i)` — "since P and Q, therefore R" has `assumps = {P, Q}` and `assert = R`. The split
    stage draws that line and `check_split.py` gates it; the map stage is then told (pistis-map RULE
    3) that "a consumed premise is a `pistis_assumption`, NEVER a conjunct of the claim".

    Nothing checked that it obeyed. Check 2 rejects an UNFILLED assumption (`True`), so the one way
    to break Atomicity that no gate could see was to DELETE the assumption and fold its content into
    the claim as an extra conjunct — which is what `oai_math/items/item1` segment 1.7 did before this
    tactic existed:

        (step7 : (∀ v ∈ LinearMap.range D.mulVecLin, y ⬝ᵥ v = 0) ∧ y s ≠ 0 ∧
            (Pi.single s (1 : ℝ) : I → ℝ) ∉ LinearMap.range D.mulVecLin)

    Three assertions in one claim where `split.json` says two premises and one assertion, with the
    two assumptions `scaffold_main.py` had seeded gone. Every check above passed: the text still
    tiles, the claim is not `True`, no `sorry` strays, the bytes are the paper's. A claim that
    silently absorbs its own premises also cannot be told from one that proves them, and the
    assumption phase has nothing left to materialize as a `have`.

    A `pistis_assumption` is owned by the `pistis_segment` sharing its `loc` — enforced by Lean
    itself now (`pistis_assumption`'s elaboration records that `loc`), so attribution is a plain
    dict lookup rather than "the first tactic declared below it". Order matters too: the assumptions
    on a segment must read in `split.json`'s order, so a diff of the two is a diff of two lists.

    The units paired here are ALL the non-intro, non-assumption segments — i.e. every entry
    `parse_main` returns except `pistis_intro` and `pistis_assumption`. A structural `pistis_conclude`
    carries no `assumptions` (`check_split.py`'s `_STRUCTURAL_ROLES`), so it contributes an empty list
    and must still have no assumption wired to its `loc` — and pairing by `kind == "segment"` instead
    silently desynchronized the two lists for any item that has a conclusion, which made this whole
    check bail out on `proofnet_verified/item1`.
    """
    rest_main = [s for s in segs[1:] if s["kind"] != "assumption"]
    rest = segments[1:]
    if len(rest_main) != len(rest):
        return True, []                    # check 1 already reported the mismatch; don't pile on

    by_loc: dict[str, List[dict]] = {}
    for a in segs:
        if a["kind"] == "assumption":
            by_loc.setdefault(a["loc"], []).append(a)

    n, unattributed, errors = 0, 0, []
    claimed = set()
    for seg, split_seg in zip(rest_main, rest):
        want = list(split_seg.get("assumptions") or [])
        got = by_loc.get(seg["loc"], [])
        claimed.add(seg["loc"])
        # An EMPTY text is the documented marker for a consumed input the prose does not state
        # (`pistis_assumption "<loc>" "" (… : …) := by …`). `split.json` can only list assumptions it
        # can quote — `check_split.py` holds every entry to being a substring of the segment — so an
        # unattributed input has no entry to match and is not an "extra" one.
        have = [a["text"] for a in got if a["text"]]
        unattributed += sum(1 for a in got if not a["text"])
        n += len(want)
        if have == want:
            continue
        errors.append(f"  loc {seg['loc']} ({seg.get('name') or 'pistis_' + seg['kind']}, line "
                      f"{seg['line']}): pistis_assumption \"{seg['loc']}\" … tactics do not match "
                      f"split.json's `assumptions`")
        for t in want:
            if t not in have:
                errors.append(f"      MISSING  (\"{t}\", TYPE)  — split.json lists it as an "
                              f"assumption, so it is an INPUT to this step, not part of its claim")
        for t in have:
            if t not in want:
                errors.append(f"      EXTRA    (\"{t}\", …)  — split.json does not list it as an "
                              f"assumption of this segment (use \"\" if the input is not something "
                              f"the prose states)")
        if sorted(have) == sorted(want):
            errors.append(f"      (same set, wrong order: split.json says {want})")

    for loc in by_loc:
        if loc not in claimed:
            errors.append(f"  loc {loc}: pistis_assumption tactic(s) at this loc have no matching "
                          f"pistis_segment / structural tactic")

    if errors:
        return False, ["pistis_assumption tactics out of step with split.json "
                       "(ATOMICITY: the claim is the `assert`; each `assumptions` entry is its own "
                       "pistis_assumption):"] + errors
    extra = f", {unattributed} unattributed (\"\")" if unattributed else ""
    return True, [f"assumptions wired: {n} pistis_assumption tactic(s) match split.json{extra}"]


def check_main(main_src: str, nl_statement: str, nl_proof: str,
               segments: List[dict] | None = None) -> Tuple[bool, List[str]]:
    """Pure faithfulness check of a mapped Main.lean. Returns (ok, message-lines).

    `segments` is `split.json`'s array; pass None to skip check 5, which is the only check that
    needs it.
    """
    segs = parse_main(main_src)
    if not segs:
        return False, ["no pistis_* segments found in Main.lean"]

    intro = segs[0]
    lines: List[str] = []
    ok = True

    # (1) coverage: intro == nl_statement; joined non-intro, non-assumption == nl_proof. A
    # `pistis_assumption`'s text is a substring of the segment it is wired to (same `loc`), already
    # counted there once — tiling it again would double it.
    if intro["kind"] != "intro":
        ok = False
        lines.append(f"segment 0 must be pistis_intro (the statement); got pistis_{intro['kind']}")
    ok_stmt, msg_stmt = _compare(intro["text"], nl_statement, "statement/intro")
    rest = [s for s in segs[1:] if s["kind"] != "assumption"]
    ok_proof, msg_proof = tile([s["text"] for s in rest], nl_proof, "proof")
    lines += msg_stmt + msg_proof
    ok = ok and ok_stmt and ok_proof

    # (2) no vacuous claim — on a segment OR an assumption. `True` is the scaffold's
    # unfilled-placeholder sentinel for both: every reasoning segment asserts something (RULE 2), and
    # every assumption has a real type, even if that type happens to be trivially true in substance
    # (that is fine; literally `True` is reserved for "not yet filled").
    vacuous = [s for s in segs if s["kind"] in ("segment", "assumption") and s["claim"].strip() == "True"]
    if vacuous:
        ok = False
        lines.append("vacuous claims (still `True` — RULE 2):")
        for s in vacuous:
            lines.append(f"  line {s['line']}: {s['name']} : True   (loc {s['loc']}, pistis_{s['kind']})")

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

    # (4) VERBATIM BYTES: each segment's and each assumption's NL text must occur in Main.lean as
    # itself.
    #
    # Check (1) compares string VALUES, which an ordinary `"…"` literal satisfies while the file on
    # disk reads `$T\\subseteq I\\times J$` — the value is right, the bytes are not, and `grep` or an
    # editor's Ctrl-F for a sentence of the paper finds nothing. Every value-level gate here passed on
    # exactly that, for every segment, which is why it went unnoticed: no check looked at the bytes.
    # Storing the NL in a raw literal (`r"…"`) makes the file's text the paper's text; this is the
    # check that keeps it so, and it is deliberately the dumbest possible one — `in`, on the raw file.
    not_verbatim = [s for s in segs if s["text"] not in main_src]
    if not_verbatim:
        ok = False
        lines.append(f'NL text not verbatim in the file ({len(not_verbatim)} segment(s)) — store it in '
                     f'a RAW literal r"…" so the bytes are the paper\'s, not an escaped "…\\\\…":')
        for s in not_verbatim:
            lines.append(f"  line {s['line']}: loc {s['loc']} (pistis_{s['kind']})")

    # (5) ASSUMPTIONS WIRED: split.json's assert/assumption line, kept in Main. See _check_assumptions.
    if segments is not None:
        ok_a, msg_a = _check_assumptions(segs, segments)
        ok = ok and ok_a
        lines += msg_a

    if ok:
        n_seg = sum(1 for s in segs if s["kind"] == "segment")
        lines.append(f"faithful: {n_seg} segment claim(s) filled, coverage + no-stray-sorry OK")
    return ok, lines


def _resolve(item: str) -> Tuple[str, str, str]:
    item = item.rstrip("/")
    return (os.path.join(item, "Main.lean"), os.path.join(item, "data"),
            os.path.join(item, "split.json"))


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Faithfulness gate for a mapped Main.lean.")
    ap.add_argument("item", nargs="?", help="<corpus>/item<N>, e.g. proofnet_verified/item8")
    ap.add_argument("--main", help="explicit path to Main.lean")
    ap.add_argument("--source", help="explicit path to the dir holding nl_statement.txt/nl_proof.txt")
    args = ap.parse_args(argv)

    if args.main and args.source:
        main_path, data_dir, split_path = args.main, args.source, None
    elif args.item:
        main_path, data_dir, split_path = _resolve(args.item)
    else:
        ap.print_usage(sys.stderr)
        return 2

    for p in (main_path, data_dir):
        if not os.path.exists(p):
            print(f"file not found: {p}", file=sys.stderr)
            return 2

    main_src = open(main_path, encoding="utf-8").read()
    try:
        nl_statement, nl_proof = load_nl(data_dir)
    except FileNotFoundError as e:
        print(str(e), file=sys.stderr)
        return 2
    segments = None
    if split_path:
        if not os.path.exists(split_path):
            print(f"file not found: {split_path}", file=sys.stderr)
            return 2
        with open(split_path, encoding="utf-8") as fh:
            segments = json.load(fh)
    ok, lines = check_main(main_src, nl_statement, nl_proof, segments)
    print(f"{'PASS' if ok else 'FAIL'} — {main_path}")
    for line in lines:
        print(line)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
