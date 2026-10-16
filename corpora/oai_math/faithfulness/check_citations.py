#!/usr/bin/env python3
"""Gate: every `path:line` citation in a datapoint points at the text it says it does.

A `C_F` item is a claim about the proof — "the proof says `obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ ≠ 0`, and you
can find it at `items/item1/Main.lean:46`". That citation is the only thing tying the item back to
the formalization, and nothing checked it: a line inserted into `Main.lean` shifts every citation
below it, and the annotation would go on pointing confidently at the wrong line. It is also what the
labeler's left panel jumps to when you click a citation, so an unchecked citation is a click that
silently lands in the wrong place.

What is checked, for a citation of a file inside this corpus:
  * the file exists and has that many lines;
  * the cited line(s), read raw, are not all comment, and the stored text is in them;
  * `pistis_proof._ambient` — the same reader that SEEDS `C_F` — reads a clause off exactly those
    lines, and the clause it reads there is the one the datapoint stores.

Together that is what "the citation type-checks" means here: not that Lean elaborates the file (that
is `lake env lean`'s job, and `Main.lean` is the one artefact already held to it), but that the line
cited actually says what the item claims it says. The second check is the load-bearing one, because
it is the only one that does not go through the reader that wrote the citation in the first place —
see `_check_cite`.

A citation `_ambient` reads nothing off is a NOTE, not an error, when the lines do contain the stored
text: `_ambient` is a best-effort reader of one file, and a hand-added item may quote a clause it
never learned to parse. Citing nothing at all is a note too, for the same reason — the UI lets you
paste a `C_F` item without provenance. A citation that is simply WRONG is an error.

Citations outside the corpus (`Mathlib/Order/Basic.lean:123`, upstream's usual provenance) are
reported and skipped: there is no checkout here to read them in.

Exit status: 0 when every citation resolves, 1 otherwise.
Usage:
    python3 faithfulness/check_citations.py                 # every items/item*
    python3 faithfulness/check_citations.py items/item1
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent                                  # the corpus root
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "ui"))
from pistis_proof import _ambient                   # noqa: E402

# `items/item1/Main.lean:46`, or `…:11-12` — a file and a 1-based line, or a range of them, which is
# how `_ambient` writes provenance. A range is for a clause genuinely WRITTEN across more than one
# line, such as a `def` whose signature wraps; the range is the tightest one containing the words
# shown, so the citation is still exactly where a reader finds them (see `check_verbatim.py`).
_CITE = re.compile(r"^(?P<path>\S+\.lean):(?P<lo>\d+)(?:-(?P<hi>\d+))?$")


def _collapse(s: str) -> str:
    """Whitespace is the one liberty: a clause written across two indented lines is stored on one."""
    return re.sub(r"\s+", " ", s).strip()


def _introduced(item_dir: Path, rel_main: str) -> dict[str, list[str]]:
    """`{citation: [clause, …]}` for every clause `Main.lean` brings into scope.

    Keyed by the citation `_ambient` itself writes (`items/item1/Main.lean:46`, or a range), because
    a clause is now identified by its words and where they are, not by a name. Straight from
    `_ambient`, so this gate and the `C_F` seeds cannot disagree about what a line says.
    """
    src = (item_dir / "Main.lean").read_text(encoding="utf-8")
    out: dict[str, list[str]] = {}
    for rec in _ambient(src, rel_main):
        out.setdefault(rec["source"], []).append(rec["signature"])
    return out


def _check_cite(cite: str, signature: str,
                introduced: dict[str, list[str]]) -> tuple[str | None, str | None]:
    """One citation -> (error, note), either of which may be None."""
    m = _CITE.match(cite.strip())
    if not m:
        return None, f"{cite!r} is not a path:line citation — not checkable, and not clickable"
    rel = m.group("path")
    lo = int(m.group("lo"))
    hi = int(m.group("hi") or lo)
    loc = f"{lo}-{hi}" if hi > lo else f"{lo}"
    path = (REPO / rel)
    if not path.is_file():
        if rel.startswith("items/"):
            return f"cites {rel}:{loc}, but there is no such file in this corpus", None
        return None, f"{rel} is outside this corpus — citation unchecked"
    lines = path.read_text(encoding="utf-8").splitlines()
    if not 1 <= lo <= hi <= len(lines):
        return f"cites {rel}:{loc}, but that file has {len(lines)} line(s)", None
    cited = lines[lo - 1:hi]
    text = " ⏎ ".join(ln.strip() for ln in cited)   # the whole citation, for the messages below
    bare = text.strip()
    # Against the RAW line, deliberately, and BEFORE asking `_ambient` anything: `_ambient` is what
    # wrote this citation, so asking it whether the citation is right only establishes that the two
    # agree. A line-numbering bug in the reader shifts the seeds and its own answer together — which
    # is exactly what happened here. `strip_comments` drops the newlines inside a block comment, so
    # everything below item1's two-line `/-- … -/` was cited one line above the clause it quoted:
    # `hτ` pointed at a comment, `hDτ` at the `obtain` above its own `set`. These two checks are the
    # ones that catch that, because `splitlines()` cannot be fooled about where a line is.
    if all(not ln.strip() or ln.strip().startswith("--") for ln in cited):
        return f"cites {rel}:{loc}, which is a comment: {bare!r}", None
    if signature and _collapse(signature) not in _collapse(" ".join(cited)):
        return f"cites {rel}:{loc}, which does not say {_collapse(signature)!r}: {bare!r}", None
    # Keyed by the whole citation: a range says "this clause is written across these lines together",
    # so a record citing `37-38` is not the same claim as one citing `38`.
    sigs = introduced.get(f"{rel}:{loc}", [])
    if not sigs:
        if signature:
            return None, (f"{rel}:{loc} does contain {_collapse(signature)!r}, but `_ambient` reads "
                          f"no clause off exactly those lines — citation left as written")
        return None, None
    if signature not in sigs:
        want = sigs[0] if len(sigs) == 1 else f"one of {sigs!r}"
        return (f"cites {rel}:{loc}, off which the proof reads {want!r}, "
                f"not {signature!r}"), None
    return None, None


def check_item(item_dir: Path) -> tuple[list[str], list[str]]:
    """(errors, notes) for every citation in every datapoint of this item."""
    item_dir = item_dir.resolve()
    meta = json.loads((item_dir / "meta.json").read_text(encoding="utf-8"))
    rel_main = f"items/item{meta['index']}/Main.lean"
    introduced = _introduced(item_dir, rel_main)
    errors: list[str] = []
    notes: list[str] = []
    align = item_dir / "align"
    for d in sorted(p for p in align.glob("*") if p.is_dir()) if align.is_dir() else []:
        art = d / "artifacts"
        cf = art / "formal" / "C_F.json"
        if not cf.exists():
            continue
        items = json.loads(cf.read_text(encoding="utf-8")).get("items") or []
        for i, it in enumerate(items):
            where = f"{d.name}: C_F[{i}]"
            cite = (it.get("source") or "").strip()
            if not cite:
                notes.append(f"{where} cites nothing — no provenance to check or jump to")
                continue
            err, note = _check_cite(cite, it.get("signature", ""), introduced)
            if err:
                errors.append(f"{where} {err}")
            if note:
                notes.append(f"{where} {note}")
        # C_N sources are free text by design (a paper and a page), so only the ones that LOOK like a
        # Lean citation are held to one -- those are the ones the UI will try to jump to.
        cn = art / "nl" / "C_N.json"
        for i, it in enumerate(json.loads(cn.read_text(encoding="utf-8")) if cn.exists() else []):
            cite = (it.get("source") or "").strip()
            if not _CITE.match(cite):
                continue
            err, _ = _check_cite(cite, "", introduced)
            if err:
                errors.append(f"{d.name}: C_N[{i}] {err}")
    return errors, notes


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Check every datapoint's path:line citations.")
    ap.add_argument("items", nargs="*", help="item dirs, e.g. items/item1 (default: all)")
    ap.add_argument("-q", "--quiet", action="store_true", help="errors only, no notes")
    args = ap.parse_args(argv)
    dirs = [Path(p) for p in args.items] or sorted(
        p for p in (REPO / "items").glob("item*") if (p / "Main.lean").exists())
    total, n_notes = 0, 0
    for d in dirs:
        errors, notes = check_item(d)
        print(f"[{'FAIL' if errors else 'ok'}] {d}")
        for e in errors:
            print("    ERROR  " + e)
        if not args.quiet:
            for n in notes:
                print("    note   " + n)
        total += len(errors)
        n_notes += len(notes)
    tail = f" ({n_notes} note(s))" if n_notes and not args.quiet else ""
    print(f"\n{total} bad citation(s){tail}" if total
          else f"\nevery citation points at what it says it does{tail}")
    return 1 if total else 0


if __name__ == "__main__":
    raise SystemExit(main())
