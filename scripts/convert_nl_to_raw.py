#!/usr/bin/env python3
r"""One-off migration: store NL text in Python RAW strings, so the file's bytes are the paper's.

The companion to `convert_nl_to_txt.py`, which moved the NL out of `nl.json` into `.txt`. That
migration missed every OTHER place the NL was stored escaped — `Main.lean`'s ordinary Lean literals
(fixed by `scaffold_main.py`, which now emits `r"…"`) and the Python generators under
`corpora/*/{faithfulness,kpistis}/`, which held the paper's sentences as `"$T\\subseteq I\\times J$"`.
Both decode to the right VALUE, which is why every value-level gate passed; neither is findable by
`grep` or an editor's Ctrl-F. `scripts/check_nl_verbatim.py` is the standing gate.

Kept in the repo rather than thrown away because the texts it rewrote are the paper's and nobody
should have to take the rewrite on trust. It is mechanical and value-preserving:

  * each string literal is re-emitted in the smallest raw form whose body is the decoded value
    VERBATIM — `r"…"`, `r\'…\'`, or a raw triple-quote when the text spans lines;
  * a run of implicitly-concatenated literals whose combined text spans lines is merged into ONE raw
    triple-quoted literal, which is both the verbatim form and the readable one: each source line
    becomes one line of the paper, so Ctrl-F of a whole passage hits;
  * the rewrite is REJECTED unless every `ast.Constant` in the module is unchanged, so no value can
    move; and a literal raw cannot hold (one ending in a backslash, e.g. `"\\"` itself) is left
    alone and reported rather than silently half-converted.

Re-running it on already-converted files is a no-op, which is the audit: `--write` then `git diff`.

    python3 scripts/convert_nl_to_raw.py [--write] FILE...
"""
from __future__ import annotations

import ast
import io
import sys
import tokenize

SKIP_BETWEEN = {tokenize.NL, tokenize.COMMENT, tokenize.INDENT, tokenize.DEDENT}


def prefix_of(lit: str) -> str:
    """The letters before the literal's opening quote (`r`, `rb`, `f`, `` …)."""
    i = min((lit.index(q) for q in "\"'" if q in lit), default=len(lit))
    return lit[:i].lower()


def raw_form(v: str) -> str | None:
    """The smallest raw literal whose body is `v` verbatim, or None if raw cannot hold it.

    Raw bodies are taken as-is with two hard limits: no closing delimiter inside, and no trailing
    backslash (the one escape `r"…"` still honours, so `r"\\"` does not exist).
    """
    if v.endswith("\\"):
        return None
    if "\n" not in v:
        if '"' not in v:
            return f'r"{v}"'
        if "'" not in v:
            return f"r'{v}'"
        return None
    for q in ('"""', "'''"):
        if q not in v and not v.endswith(q[0]):
            return f"r{q}{v}{q}"
    return None


def _groups(src: str):
    """Yield runs of implicitly-concatenated STRING tokens, in source order."""
    run: list[tokenize.TokenInfo] = []
    for tok in tokenize.generate_tokens(io.StringIO(src).readline):
        if tok.type == tokenize.STRING:
            run.append(tok)
        elif tok.type in SKIP_BETWEEN:
            continue
        elif run:
            yield run
            run = []
    if run:
        yield run


def convert(src: str) -> tuple[str, list[tuple[int, str]]]:
    lines = src.splitlines(keepends=True)
    out, skipped, last = [], [], (1, 0)

    def upto(pos):
        (r1, c1), (r2, c2) = last, pos
        if r1 == r2:
            return lines[r1 - 1][c1:c2]
        return "".join([lines[r1 - 1][c1:], *lines[r1:r2 - 1], lines[r2 - 1][:c2]])

    def emit(tok_start, tok_end, new):
        nonlocal last
        out.append(upto(tok_start))
        out.append(new)
        last = tok_end

    def value(tok):
        try:
            return ast.literal_eval(tok.string)
        except Exception:
            return None

    for run in _groups(src):
        plain = [t for t in run if not (set(prefix_of(t.string)) & set("rbf"))]
        vals = [value(t) for t in run]
        # Merge the whole run when it is all plain, all decodable, and the text spans lines.
        if len(run) > 1 and len(plain) == len(run) and all(v is not None for v in vals):
            joined = "".join(vals)
            if "\\" in joined and "\n" in joined:
                new = raw_form(joined)
                if new is not None and ast.literal_eval(new) == joined:
                    emit(run[0].start, run[-1].end, new)
                    continue
        for tok in run:
            if set(prefix_of(tok.string)) & set("rbf"):
                continue                       # already raw, or bytes/f-string: leave alone
            v = value(tok)
            if v is None or "\\" not in v:
                continue                       # nothing escaped: the bytes are already the text
            new = raw_form(v)
            if new is None or ast.literal_eval(new) != v:
                skipped.append((tok.start[0], tok.string))
                continue
            emit(tok.start, tok.end, new)
    out.append(upto((len(lines), len(lines[-1]) if lines else 0)))
    return "".join(out), skipped


def main(argv: list[str]) -> int:
    write = "--write" in argv
    for p in (a for a in argv if not a.startswith("--")):
        src = open(p, encoding="utf-8", newline="").read()
        new, skipped = convert(src)
        print(f"{p}: {len(new) - len(src):+d} bytes, {len(skipped)} skipped")
        for ln, lit in skipped:
            print(f"    SKIP line {ln}: {lit[:70]}")
        old_c = [c.value for c in ast.walk(ast.parse(src)) if isinstance(c, ast.Constant)]
        new_c = [c.value for c in ast.walk(ast.parse(new)) if isinstance(c, ast.Constant)]
        assert old_c == new_c, f"{p}: VALUES CHANGED"
        print(f"    all {len(old_c)} module constants unchanged")
        if write and new != src:
            open(p, "w", encoding="utf-8", newline="").write(new)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
