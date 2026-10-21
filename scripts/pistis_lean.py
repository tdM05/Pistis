"""Shared parser for `pistis_*` tactics in a Main.lean (source-level, no Lean build).

Recovers, in source order, the segments a scaffolded/mapped Main.lean records:
  - pistis_intro "loc" "text"
  - pistis_wts "loc" "text"
  - pistis_conclude "loc" "text"
  - pistis_segment "loc" "text" (name : claim) := by <body>
  - pistis_assumption "loc" "text" (name : type) := by <body>

A `pistis_assumption` is a premise a segment CONSUMES rather than asserts; it has the SAME shape as
`pistis_segment` (and the same `(name : type) := by <body>` tail) but its `loc` is the loc of the
`pistis_segment` that consumes it — several assumptions may share one `loc`, ordered by source
position within it.

The `text` stored in Main is a Lean RAW string literal produced by scaffold_main._lean_str (`r"…"`,
or `r#"…"#` when the text itself contains a quote). A raw literal has no escapes, so the NL text in a
Main.lean is the paper's bytes: `grep` and editor Ctrl-F find a sentence of the proof in the file.
An ordinary `"…"` literal would have to double every LaTeX backslash (`\\in` -> `\\\\in`), and then the
file says something the paper does not — which is how escaped NL went unnoticed here for so long,
since decoding made every VALUE-level gate pass. `check_main.py` now also gates the bytes.

`read_string_literal` reads either form, so a hand-written or pre-raw Main.lean keeps parsing, and
returns the text so it can be compared byte-for-byte against the NL `.txt` files. Used by
check_main.py and check_steps.py.
"""
from __future__ import annotations

import re
from typing import List, Optional, Tuple

_TAC = re.compile(r"\bpistis_(intro|wts|conclude|segment|assumption)\b")

# A Lean raw string literal opener: `r"`, `r#"`, `r##"`, … The closing delimiter is `"` followed by
# the SAME number of `#`, so the body can contain anything shorter than that.
_RAW_OPEN = re.compile(r'r(#*)"')


def _raw_open_at(src: str, j: int) -> Optional[re.Match]:
    """If the `"` at `src[j]` is the quote of a raw opener, the match covering `r#*"`; else None.

    Called when a scanner has already walked to the `"` (it cannot know the `r#*` prefix was a
    prefix), so the prefix is recovered by stepping back over the `#`s and the `r`.
    """
    if j >= len(src) or src[j] != '"':
        return None
    k = j
    while k > 0 and src[k - 1] == "#":
        k -= 1
    if k == 0 or src[k - 1] != "r":
        return None
    # The `r` must be its own token: in `var"x"` the `r` is the tail of an identifier, not a prefix.
    if k - 2 >= 0 and (src[k - 2].isalnum() or src[k - 2] in "_'!?"):
        return None
    return _RAW_OPEN.match(src, k - 1)


def raw_open(src: str, i: int) -> Optional[re.Match]:
    """The `r#*"` opener starting AT `src[i]`, if there is one; else None.

    For scanners that walk left-to-right and want to skip a raw literal whole. The closing delimiter
    is `'"' + m.group(1)` — a quote plus the same number of `#`.
    """
    m = _RAW_OPEN.match(src, i)
    if not m:
        return None
    if i > 0 and (src[i - 1].isalnum() or src[i - 1] in "_'!?"):
        return None                                 # the `r` is the tail of an identifier
    return m


def read_string_literal(src: str, i: int) -> Tuple[str, int]:
    """Read the Lean string literal at `src[i]`. Return (text, index just past it).

    `i` may sit on the opening `"`, or on the `r`/`#` prefix of a raw literal.

    A RAW literal's body has no escapes, so the text is the file's bytes verbatim — that is the point
    of using one for NL. An ordinary literal is decoded for the two escapes scaffold_main used to
    emit (`\\\\`->`\\`, `\\"`->`"`); other backslash sequences are left verbatim. Raw newlines inside
    either form are preserved (Lean allows them).
    """
    m = _RAW_OPEN.match(src, i) or _raw_open_at(src, i)
    if m:
        close = '"' + m.group(1)
        j = src.find(close, m.end())
        if j < 0:
            raise ValueError("unterminated raw string literal")
        return src[m.end():j], j + len(close)
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
    """Index where the next string literal STARTS — its `r#*` prefix included, when it is raw."""
    j = src.index('"', i)
    m = _raw_open_at(src, j)
    return m.start() if m else j


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

    Each dict has: kind ('intro'|'wts'|'conclude'|'segment'|'assumption'), loc, text, line. A
    'segment' or 'assumption' also has name and claim — the two share the same
    `"loc" "text" (name : claim) := by ...` tail, so they are parsed identically; the only
    difference is the keyword matched. An 'assumption' entry's `loc` is the loc of the
    `pistis_segment` it is wired to, not a loc of its own.
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
        if kind in ("segment", "assumption"):
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
