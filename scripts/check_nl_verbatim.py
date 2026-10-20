#!/usr/bin/env python3
r"""Repo-wide gate: no file may hold a line of the NL source in ESCAPED form.

`check_main.py` check 5 holds one file — `Main.lean` — to the paper's bytes. This holds every other
file in the repo to the same rule, and it is the check whose absence let escaped NL spread: the NL
was stored escaped in `Main.lean`, in `split.json` and in several Python generators, every
VALUE-level gate passed (escaping is value-preserving, so it must), and the defect was only visible
by Ctrl-F'ing a sentence of the paper and getting no hit.

So this gate IS Ctrl-F, with nothing in between. For every line of every `data/nl_*.txt` that
contains a backslash, it asks whether some file contains that line with its backslashes DOUBLED but
not the line itself. A hit means someone pasted the paper through a string literal that escapes:

    the paper   $T\subseteq I\times J$ means a real matrix whose entries outside $T$ are
    the file    $T\\subseteq I\\times J$ means a real matrix whose entries outside $T$ are

Both decode to the same text, which is why nothing else sees it, and only the first is findable.

The unit is a LINE of the source, not a fragment, which is what keeps this free of false alarms: a
docstring that discusses escaping (this one, `pistis_lean.py`'s) writes `\\in` or `\\\\in` in
isolation and never a whole wrapped line of the paper, so it does not match.

`.json` is EXEMPT, and it is the only exemption. JSON has no verbatim option — a newline must be the
two characters `\` `n` and a backslash must be doubled — so `split.json` and the `kpistis/units`
artifacts cannot satisfy this and are not asked to. Every other format here has one: Lean has raw
literals `r"…"`, Python has raw strings `r"…"` / `r\"\"\"…\"\"\"`, Markdown has code fences. Where a
format offers verbatim, verbatim is required.

Exit 0 = PASS, 1 = FAIL.
Usage:
    python3 scripts/check_nl_verbatim.py            # the whole repo
    python3 scripts/check_nl_verbatim.py -v         # list the sources and files scanned
"""
from __future__ import annotations

import argparse
import os
import re
from functools import lru_cache
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# Formats with a verbatim option, so the rule applies. `.json` is absent on purpose (see above).
SCANNED = {".py", ".lean", ".md", ".txt", ".html", ".js", ".css", ".tex", ".yaml", ".yml", ".toml"}
SKIP_DIRS = {".git", ".lake", "__pycache__", ".pytest_cache", "node_modules", ".venv"}

# A line shorter than this is a fragment, not a quotation of the paper; requiring `grep` to find
# `$T$` verbatim would flag every discussion of the notation rather than a mis-stored passage.
MIN_LINE = 24


def nl_sources() -> list[Path]:
    """Every `data/nl_statement.txt` / `data/nl_proof.txt` in the repo — the source of truth."""
    return sorted(REPO.glob("corpora/*/items/item*/data/nl_*.txt"))


def needles() -> list[tuple[str, Path]]:
    """(line, the source file it came from) for every NL line that could be stored escaped."""
    out: list[tuple[str, Path]] = []
    seen: set[str] = set()
    for src in nl_sources():
        text = src.read_text(encoding="utf-8", newline="")
        for line in text.split("\n"):
            line = line.rstrip("\r")
            if "\\" in line and len(line) >= MIN_LINE and line not in seen:
                seen.add(line)
                out.append((line, src))
    return out


def escaped_lines(text: str, lines: list[str]) -> list[str]:
    """Those `lines` that `text` holds with backslashes DOUBLED but not verbatim.

    The whole gate, as one pure function: `escaped in text and line not in text`. The second half
    matters — a file is allowed to show the escaped form *alongside* the real one (a docstring
    explaining the rule, this repo's tests), and only a file that has the escaped form INSTEAD is
    storing text no one can find.

    The naive form is `len(lines)` substring searches per file, which across the repo is millions.
    One alternation finds every candidate in a single C-level pass instead, and only the lines that
    actually hit pay for the second question.
    """
    if not lines:
        return []
    pat, back = _alternation(tuple(lines))
    hits = dict.fromkeys(pat.findall(text))           # escaped forms found, in order, deduped
    return [back[e] for e in hits if back[e] not in text]


@lru_cache(maxsize=4)
def _alternation(lines: tuple[str, ...]) -> tuple[re.Pattern[str], dict[str, str]]:
    """(pattern matching the escaped form of any of `lines`, escaped -> original).

    Longest alternative first, so an NL line that is a suffix of another cannot mask it. Cached
    because the needle set is the same for every file scanned.
    """
    back = {ln.replace("\\", "\\\\"): ln for ln in lines}
    esc = sorted(back, key=len, reverse=True)
    return re.compile("|".join(re.escape(e) for e in esc)), back


def scanned_files() -> list[Path]:
    """Every file in the repo whose format has a verbatim option.

    `os.walk` with in-place pruning of `dirnames`, not `rglob`: a glob filters paths it has already
    produced, so it descends into each corpus's `.lake` and walks all of Mathlib — a quarter of a
    million paths to throw away, which was the bulk of this gate's runtime.
    """
    out = []
    for root, dirnames, filenames in os.walk(REPO):
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
        for name in filenames:
            if os.path.splitext(name)[1] in SCANNED:
                out.append(Path(root) / name)
    return sorted(out)


def check(verbose: bool = False) -> tuple[int, list[str]]:
    pairs = needles()
    origin = dict(pairs)
    lines_only = [line for line, _ in pairs]
    files = scanned_files()
    msgs: list[str] = []
    n_bad = 0
    for path in files:
        try:
            text = path.read_text(encoding="utf-8", newline="")
        except (UnicodeDecodeError, OSError):
            continue
        if "\\\\" not in text:
            continue                                  # nothing doubled anywhere: cannot be a hit
        for line in escaped_lines(text, lines_only):
            escaped = line.replace("\\", "\\\\")
            n_bad += 1
            ln = text.count("\n", 0, text.index(escaped)) + 1
            msgs.append(f"{path.relative_to(REPO)}:{ln}: holds a line of "
                        f"{origin[line].relative_to(REPO)} with its backslashes DOUBLED, so Ctrl-F "
                        f"for the paper's text misses it")
            msgs.append(f"    paper: {line}")
            msgs.append(f"    file:  {escaped}")
    if verbose:
        msgs.append(f"(scanned {len(files)} file(s) against {len(pairs)} NL line(s) from "
                    f"{len(nl_sources())} source file(s))")
    return n_bad, msgs


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="No file may hold a line of the NL source escaped.")
    ap.add_argument("-v", "--verbose", action="store_true", help="report what was scanned")
    args = ap.parse_args(argv)
    n_bad, msgs = check(args.verbose)
    for m in msgs:
        print(m)
    if n_bad:
        print(f"\nFAIL — {n_bad} escaped NL line(s). Store the text in a raw literal "
              f'(Lean `r"…"`, Python `r"…"`) so the file\'s bytes are the paper\'s.')
        return 1
    print("PASS — every file that quotes the NL source quotes its bytes")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
