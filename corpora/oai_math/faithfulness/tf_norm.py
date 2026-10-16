"""Normalize a Lean statement into a clean T_F.

T_F is plain text; its segmentation is the *spans* of S_F, never newlines. So we
strip comments and flatten the declaration onto a single flowing line (imports /
opens stay on their own lines because Lean requires it). No `\n` is used to
structure the theorem.
"""
from __future__ import annotations

import re

_HEAD_KW = re.compile(r"^(import|open|namespace|section|end|set_option|variable|universe)\b")

# keywords that start a new top-level declaration in the flattened body
_DECL_KW = {"theorem", "lemma", "example", "def", "abbrev", "instance",
            "structure", "inductive", "class", "axiom", "opaque"}
# modifiers that precede a declaration keyword and must stay attached to it
_DECL_MOD = {"noncomputable", "private", "protected", "partial", "unsafe",
             "scoped", "local", "mutual"}


def _split_decls(body: str) -> list[str]:
    """Split a whitespace-collapsed body into one string per top-level
    declaration, so a helper `def`/`abbrev` and the `theorem` that follows land
    on separate lines. Modifiers (and `@[...]` attributes) stay with their
    declaration. A body with a single declaration is returned unchanged."""
    toks = body.split(" ")
    decls: list[str] = []
    cur: list[str] = []
    for t in toks:
        if t in _DECL_KW:
            # pull any trailing modifiers/attributes off `cur` onto the new decl
            k = len(cur)
            while k > 0 and (cur[k - 1] in _DECL_MOD or cur[k - 1].startswith("@[")):
                k -= 1
            moved, cur = cur[k:], cur[:k]
            if cur:
                decls.append(" ".join(cur))
            cur = moved + [t]
        else:
            cur.append(t)
    if cur:
        decls.append(" ".join(cur))
    return decls


def strip_comments(text: str) -> str:
    """Remove block ``/- -/`` (nested) and line ``--`` comments."""
    out: list[str] = []
    i, n, depth = 0, len(text), 0
    while i < n:
        two = text[i:i + 2]
        if depth > 0:
            if two == "/-":
                depth += 1; i += 2
            elif two == "-/":
                depth -= 1; i += 2
            else:
                i += 1
            continue
        if two == "/-":
            depth += 1; i += 2
        elif two == "--":
            j = text.find("\n", i)
            if j < 0:
                break
            i = j
        else:
            out.append(text[i]); i += 1
    return "".join(out)


def normalize_tf(src: str) -> str:
    """Return the clean T_F: import/open lines, then the whole declaration
    flattened to one whitespace-collapsed line."""
    lines = [ln.strip() for ln in strip_comments(src).splitlines() if ln.strip()]
    head: list[str] = []
    decl: list[str] = []
    in_decl = False
    for ln in lines:
        if not in_decl and _HEAD_KW.match(ln):
            head.append(ln)
        else:
            in_decl = True
            decl.append(ln)
    body = re.sub(r"\s+", " ", " ".join(decl)).strip()
    return "\n".join(head + (_split_decls(body) if body else [])) + "\n"
