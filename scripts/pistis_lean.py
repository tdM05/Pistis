"""Shared parser for `pistis_*` tactics in a Main.lean (source-level, no Lean build).

Recovers, in source order, the segments a scaffolded/mapped Main.lean records:
  - pistis_intro "loc" "text"
  - pistis_wts "loc" "text"
  - pistis_conclude "loc" "text"
  - pistis_segment "loc" "text" (name : claim) := by <body>

The `text` stored in Main is a Lean string literal produced by scaffold_main._lean_str (which escaped
`\\` -> `\\\\` and `"` -> `\\"`); `read_string_literal` decodes it back to the original source text so it
can be compared byte-for-byte against nl.json. Used by check_main.py and check_steps.py.
"""
from __future__ import annotations

import re
from typing import List, Tuple

_TAC = re.compile(r"\bpistis_(intro|wts|conclude|segment)\b")


def read_string_literal(src: str, i: int) -> Tuple[str, int]:
    """`src[i]` must be an opening `"`. Return (decoded text, index just past the closing `"`).

    Decodes the two escapes scaffold_main emits (`\\\\`->`\\`, `\\"`->`"`); other backslash sequences are
    left verbatim. Raw newlines inside the literal are preserved (Lean allows them).
    """
    if src[i] != '"':
        raise ValueError(f"expected string literal at index {i}")
    i += 1
    out: List[str] = []
    while i < len(src):
        c = src[i]
        if c == "\\":
            nxt = src[i + 1] if i + 1 < len(src) else ""
            if nxt == "\\":
                out.append("\\"); i += 2; continue
            if nxt == '"':
                out.append('"'); i += 2; continue
            out.append(c); i += 1; continue
        if c == '"':
            return "".join(out), i + 1
        out.append(c); i += 1
    raise ValueError("unterminated string literal")


def _balanced_type(src: str, start: int) -> Tuple[str, int]:
    """`start` is just AFTER the `:` of `(name : type)`; the annotation paren is already open (depth 1).
    Scan to its matching close paren, skipping string literals. Return (type_text, index_after_close)."""
    depth, i, n = 1, start, len(src)
    while i < n:
        c = src[i]
        if c == '"':
            _, i = read_string_literal(src, i)
            continue
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return src[start:i], i + 1
        i += 1
    return src[start:], n


def _next_quote(src: str, i: int) -> int:
    j = src.index('"', i)
    return j


def _skip_trivia(src: str, i: int) -> int:
    """Advance past whitespace and Lean comments (`--` to EOL, nestable `/- … -/`)."""
    n = len(src)
    while i < n:
        if src[i].isspace():
            i += 1
        elif src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j + 1
        elif src.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if src.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif src.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
        else:
            break
    return i


def parse_main(src: str) -> List[dict]:
    """Return the ordered list of pistis segments in `src` (a Main.lean's text).

    Each dict has: kind ('intro'|'wts'|'conclude'|'segment'), loc, text, line. A 'segment' also has
    name and claim.
    """
    segs: List[dict] = []
    for m in _TAC.finditer(src):
        kind = m.group(1)
        line = src.count("\n", 0, m.start()) + 1
        # loc string
        q = _next_quote(src, m.end())
        loc, after_loc = read_string_literal(src, q)
        # text string
        q2 = _next_quote(src, after_loc)
        text, after_text = read_string_literal(src, q2)
        entry = {"kind": kind, "loc": loc, "text": text, "line": line}
        if kind == "segment":
            # A comment may sit between the NL literal and the claim, explaining the formalization
            # choice; `(see split.json)` in one would otherwise be read as the claim's binder.
            popen = _skip_trivia(src, after_text)
            if src[popen:popen + 1] != "(":
                popen = src.index("(", after_text)
            colon = src.index(":", popen)
            entry["name"] = src[popen + 1:colon].strip()
            claim, _ = _balanced_type(src, colon + 1)
            entry["claim"] = " ".join(claim.split())
        segs.append(entry)
    return segs


# `-- @pistis_assumption ("substring", TYPE)` annotation lines.
_ASSUMPTION = re.compile(r'--\s*@pistis_assumption\s*\(\s*"((?:[^"\\]|\\.)*)"\s*,\s*(.*?)\)\s*$', re.M)


def parse_assumptions(src: str) -> List[dict]:
    """Return every `-- @pistis_assumption ("text", TYPE)` as {text, type, line}."""
    out = []
    for m in _ASSUMPTION.finditer(src):
        text_raw = m.group(1).replace('\\"', '"').replace("\\\\", "\\")
        out.append({
            "text": text_raw,
            "type": m.group(2).strip(),
            "line": src.count("\n", 0, m.start()) + 1,
        })
    return out
