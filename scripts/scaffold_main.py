#!/usr/bin/env python3
"""Assemble a placeholder `Main.lean` template from an item's `split.json` (the map-stage scaffold).

This is the deterministic bridge from segmentation (pistis-split) to the map stage: it turns the
verified `split.json` into a `Main.lean` skeleton with one `pistis_*` tactic per segment, TEXT copied
verbatim from split.json (so the assembled Main tiles the source by construction), and every reasoning
segment's claim left as a `True` placeholder with a `sorry` body. The map agent then FILLS each `True`
with the real Lean claim; it never hand-types the boilerplate or re-types the text.

Domain-agnostic: it reuses the item's own `data/statement.lean` header + theorem signature verbatim
(its `import Mathlib`, `open`s, and the real theorem name), and emits only plain-Lean structure
(`have`s via `pistis_segment`, a reductio `have habsurd … := by intro …` skeleton where a `frame` marks
one). No System E, no SMT cap, no geometry constructions.

Layout (per the item convention):
  Reads:  <corpus>/item<N>/split.json         (segments; TEXT source of truth, gated by check_split.py)
        + <corpus>/item<N>/meta.json          (index, for the locator)
        + <corpus>/item<N>/data/statement.lean (header + theorem signature)
  Writes: <corpus>/item<N>/Main.lean          (the fill-in template; refuses to clobber, use --force)

Usage:
  python3 scripts/scaffold_main.py <corpus>/item<N>          # e.g. proofnet_verified/item8
  python3 scripts/scaffold_main.py <corpus>/item<N> --force  # overwrite an existing Main.lean
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
from typing import List


def _lean_str(s: str) -> str:
    """`s` as a complete Lean RAW string literal: `r"…"`, or `r#"…"#` if the text contains a quote.

    Raw, because an ordinary `"…"` literal has to escape every LaTeX backslash (`\\in` -> `\\\\in`) and
    then the bytes in Main.lean are not the bytes of the paper: searching the file for a sentence of
    the proof finds nothing. The value would still be right, so every gate comparing string VALUES
    passes — which is exactly how escaped NL survived here unnoticed. A raw literal has no escapes,
    so the NL text IS the file's text, and `check_main.py` gates that byte-for-byte.

    The `#` count is the smallest one the body cannot be mistaken for the closing delimiter with:
    `r"…"` unless the text contains `"`, then `r#"…"#` unless it contains `"#`, and so on.
    """
    n = 0
    while '"' + "#" * n in s:
        n += 1
    h = "#" * n
    return f'r{h}"{s}"{h}'


def _split_signature(statement_text: str) -> str:
    """Return the item's header + theorem signature verbatim, up to and including `:= by`.

    Everything before the body (imports, opens, the informal-statement comment, the `theorem <name>
    … :` signature) is preserved exactly; the trailing `sorry` body is dropped so we can append ours.
    """
    m = re.search(r":=\s*by\b", statement_text)
    if not m:
        sys.exit("ERROR: could not find ':= by' in statement.lean")
    return statement_text[: m.end()]


def build_body(segments: List[dict], index: int) -> List[str]:
    """Emit the proof-body lines: pistis_intro, per-segment tactics (+ reductio frames), pistis_conclude,
    and a final `sorry` closer. TEXT verbatim from split.json."""
    body: List[str] = []
    indent = 1

    def sp(extra: int = 0) -> str:
        return "  " * (indent + extra)

    # role/segment lookup by position
    intro = next((e for e in segments if e.get("role") == "intro"), None)
    conclusion = next((e for e in segments if e.get("role") == "conclusion"), None)
    if intro is None:
        sys.exit("ERROR: split.json has no 'intro' segment (index 0 = the statement)")

    # intro (structural — records the statement text, no `have`)
    body.append(f'{sp()}pistis_intro "{index}.0"')
    body.append(f'{sp(1)}{_lean_str(intro["text"])}')
    body.append("")

    habsurd = 0
    step_no = 0
    for pos, e in enumerate(segments):
        role = e.get("role")
        if role in ("intro", "conclusion"):
            continue

        if role == "wts":
            body.append(f'{sp()}pistis_wts "{index}.{pos}"')
            body.append(f'{sp(1)}{_lean_str(e["text"])}')
            body.append("")
            continue

        frame = e.get("frame") or {}
        kind = frame.get("kind")

        if kind == "reductio_open":
            habsurd += 1
            # ¬(sorry): the negation of the supposition; the map agent fills the real proposition and
            # makes the trailing reductio_close claim match. `intro` names the supposition hypothesis.
            body.append(f"{sp()}have habsurd{habsurd} : ¬(sorry) := by")
            indent += 1
            body.append(f"{sp()}intro hsuppose{habsurd}")

        step_no += 1
        name = f"step{pos}"
        # a contradiction segment reaches `False`; every other reasoning segment starts `True`
        claim = "False" if kind == "contradiction" else "True"
        # pistis_assumption tactics: one per consumed prior fact (the segment's `assumptions` set),
        # with the SAME loc as the pistis_segment they are wired to. Each starts as a `True`
        # placeholder with a `sorry` body, exactly like the segment's own claim — the map agent
        # replaces `True` with the real type (`lake env lean` then elaborates it immediately), and a
        # later fill stage replaces `sorry` with the real proof of that premise.
        for i, a in enumerate(e.get("assumptions", [])):
            body.append(f'{sp()}pistis_assumption "{index}.{pos}" {_lean_str(a)}')
            body.append(f'{sp(1)}(asm{pos}_{i} : True) := by sorry')
        body.append(f'{sp()}pistis_segment "{index}.{pos}"')
        body.append(f'{sp(1)}{_lean_str(e["text"])}')
        body.append(f"{sp(1)}({name} : {claim}) := by sorry")
        body.append("")

        if kind == "contradiction":
            if body and body[-1] == "":
                body.pop()
            body.append(f"{sp()}exact {name}")
            body.append("")
            indent = max(1, indent - 1)

    # conclusion (structural), if present
    if conclusion is not None:
        cpos = segments.index(conclusion)
        body.append(f'  pistis_conclude "{index}.{cpos}"')
        body.append(f'    {_lean_str(conclusion["text"])}')
        body.append("")

    # Close the goal. With `True` placeholder claims we cannot `exact` a step yet, so the template ends
    # in a MARKED placeholder closer. The map agent MUST replace this line with the real closing
    # assembly (`exact`/`refine …`) — a finished map has NO stray `sorry` (only `:= by sorry` step
    # bodies, which the prove stage discharges). The marker makes that requirement greppable/enforceable.
    body.append("  sorry -- @pistis_closer: replace with the real closing (exact/refine); no stray sorry")
    return body


def assemble(item_dir: str) -> str:
    split_path = os.path.join(item_dir, "split.json")
    meta_path = os.path.join(item_dir, "meta.json")
    stmt_path = os.path.join(item_dir, "data", "statement.lean")
    for p in (split_path, meta_path, stmt_path):
        if not os.path.exists(p):
            sys.exit(f"ERROR: missing {p}")

    segments = json.load(open(split_path, encoding="utf-8"))
    index = json.load(open(meta_path, encoding="utf-8"))["index"]
    statement_text = open(stmt_path, encoding="utf-8").read()

    signature = _split_signature(statement_text)
    body = build_body(segments, index)

    # Ensure the pistis tactics are in scope. The item's statement.lean imports Mathlib; we add the
    # Pistis import right after it (idempotent — only if not already present).
    header = signature
    if "import Pistis" not in header:
        header = re.sub(r"(import Mathlib\b)", r"\1\nimport Pistis", header, count=1)
    # The structural tactics (pistis_intro/wts/conclude) only RECORD metadata and emit no tactic, which
    # trips Lean's unusedTactic linter. Silence it so the template elaborates cleanly.
    if "linter.unusedTactic" not in header:
        header = re.sub(r"(import Pistis\n)", r"\1set_option linter.unusedTactic false\n", header, count=1)

    return header + "\n" + "\n".join(body) + "\n"


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Assemble a placeholder Main.lean from an item's split.json.")
    ap.add_argument("item", help="<corpus>/item<N>, e.g. proofnet_verified/item8")
    ap.add_argument("--force", action="store_true", help="overwrite an existing Main.lean")
    args = ap.parse_args(argv)

    item_dir = args.item.rstrip("/")
    out = os.path.join(item_dir, "Main.lean")
    if os.path.exists(out) and not args.force:
        print(f"FAIL: {out} already exists. Use --force to overwrite.")
        return 1

    content = assemble(item_dir)
    with open(out, "w", encoding="utf-8") as fh:
        fh.write(content)
    print(f"OK: wrote {out}")
    print(f"  Next: fill each `(stepN : True)` claim in the map stage, then check with check_split.py "
          f"(text is already tiled by construction).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
