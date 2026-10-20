#!/usr/bin/env python3
"""Gate: every string a datapoint SHOWS is text that `Main.lean` / the NL source actually contains.

The right panel is read as a quotation. `hsuppose1 : x j * y s ≠ 0` next to a citation of
`Main.lean:38` says "line 38 of the proof puts this in scope, in these words" — but line 38 is
`intro hsuppose1` and those words are nowhere on it. The proposition came from the `have` above, and
the seeder assembled the two into a string that exists only in the datapoint. That is the failure
this gate is for: an alignment is only evidence about a formalization if the formalization is what is
being quoted, and a plausible paraphrase is the one kind of wrong a reader cannot catch by reading.

Checked, per datapoint:

| string                  | held to                                                               |
| ----------------------- | --------------------------------------------------------------------- |
| `T_N`                   | a byte-for-byte substring of `data/nl_{statement,proof}.txt`          |
| `T_N` (gapped)          | every piece around a `…` verbatim, in order, in one source file       |
| `T_F` (segment)         | the claim, verbatim in `Main.lean` up to whitespace                   |
| `T_F` (assumption)      | the marker's type, verbatim on a `@pistis_assumption` COMMENT line    |
| `T_F` (statement)       | every line verbatim and in source order; only `sorry` may be inserted |
| `C_F.items[].signature` | a CONTIGUOUS substring of the line(s) it cites                         |
| `C_N[].text`            | a substring of the NL source, as its own provenance claims            |
| `S_F` / `S_N`           | in range of the target they index (they are slices, so verbatim)      |

The `C_F` rule is one rule and it has no exceptions: **the signature must occur, contiguously, in the
text of the lines it cites.** Nothing may be stitched, re-ordered, inferred from what Lean would
elaborate, or added between two halves that do happen to be there. A clause the file writes as
`obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ ≠ 0` is quotable as itself; `hτ : τ ≠ 0` is not quotable from it, even
though both halves are on the line and the reconstruction is true, because that string is not in the
file and a reader following the citation will not find it. `hsuppose1 : x j * y s ≠ 0` is the same
failure in its least obvious form — the name from line 38, the proposition from line 37, the `:`
from the seeder — and an earlier version of this gate let it through as "framed". There is no framed,
and there is no declared-derivation escape hatch either: if a hypothesis's type is something Lean
computes rather than something the file says (`set x := e with h` gives `h : x = e`, where the file
writes `:=`), then the thing to show is the `set` clause, which is what the proof actually says.

A signature found elsewhere in the file says so in the message, since that is the likely repair.
Anything else is an error, and the fix is always the same: quote a real clause, or show nothing.

Two deliberate design choices, both about independence:

  * This gate reads `Main.lean` with `splitlines()` and asks substring questions. It does not call
    `_ambient`, which is the reader that WROTE these signatures — `check_citations.py` already
    cross-checks the two, and a gate that goes through the thing it is auditing can only establish
    that the thing agrees with itself. The same blind spot hid the off-by-one in every citation.
  * It checks TEXT, not meaning. That `hτ` really does prove `τ ≠ 0` is Lean's business, and
    `Main.lean` is held to `lake env lean`. Here the only question is whether a reader who follows a
    citation finds the words the datapoint showed them.

Whitespace is the one liberty, and it is forced: `parse_main` collapses runs of whitespace in a
claim, so a claim written over three indented lines is stored on one. Comments are not quotable — the
file is read through `_code_lines`, so a target can never be "found" inside a docstring that merely
discusses it.

Two targets are shaped by the ASSUMPTION model and need their own rule here:

  * A segment's `T_N` is the sentence minus the substrings `split.json` lists under `assumptions`
    (`pistis_proof.segment_nl_target`), so it is no longer one contiguous slice — there is a `…`
    where each premise was lifted out. The rule is the same claim made piecewise: every piece must be
    in ONE source file, verbatim, and the pieces must appear in the order the target puts them, with
    something between each pair. That last part matters. Without it a `…` could be inserted anywhere,
    including in the middle of a word, and the pieces would still all be "found". That the excised
    text is exactly the `assumptions` list is `check_targets.py`'s half, which re-derives the
    subtraction from `split.json`.
  * An `asm-*` unit's `T_F` is the TYPE on a `-- @pistis_assumption ("clause", TYPE)` line, which is
    a COMMENT — the one place in this gate where the blanked file is the wrong source. It is checked
    against the marker lines of the raw file instead, and only those: a type that happens to appear
    in a docstring is still not quotable, and one that appears in real code is not where the fill
    stage will look for it.

Exit status: 0 when everything shown is in the source, 1 otherwise.
Usage:
    python3 faithfulness/check_verbatim.py                 # every items/item*
    python3 faithfulness/check_verbatim.py items/item1 -v   # and print every string's status
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
from pistis_proof import GAP, _code_lines           # noqa: E402  (a comment scanner, not a reader)

# `items/item1/Main.lean:38`, or `…:11-12` when a clause is written across two adjacent lines.
_CITE = re.compile(r"^(?P<path>\S+\.lean):(?P<lo>\d+)(?:-(?P<hi>\d+))?$")


def _collapse(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


def _nl_sources(item_dir: Path) -> dict[str, str]:
    """The item's NL source documents, keyed by name: `{"nl_statement": ..., "nl_proof": ...}`.

    Each is a plain-text file whose bytes are the paper's bytes (no JSON escaping, no trailing
    newline), read with `newline=""` so nothing about line endings is repaired on the way in — this
    gate's whole claim is byte-for-byte containment.
    """
    data = item_dir / "data"
    return {name: (data / f"{name}.txt").read_text(encoding="utf-8", newline="")
            for name in ("nl_statement", "nl_proof")}


def _find_nl(text: str, sources: dict[str, str]) -> str | None:
    """Which NL source file contains `text` verbatim, if any.

    A trailing newline is allowed to be missing from the source: a unit's `T_N` ends at a sentence
    boundary, and the artifact is written with a newline whether or not the excerpt had one.
    """
    for cand in (text, text.rstrip("\n")):
        if not cand:
            continue
        for key, val in sources.items():
            if cand in val:
                return key
    return None


def _find_nl_gapped(text: str, sources: dict[str, str]) -> tuple[str | None, str | None]:
    """A GAPPED `T_N` -> (source key, error). See the module docstring's assumption-model note.

    The pieces around each `…` must all be in one file, in this order, and consecutive pieces must be
    separated there — a gap that excised nothing would mean the `…` was inserted rather than left
    behind. Empty pieces are skipped, which is what a target beginning or ending in a gap gives.
    """
    pieces = [p for p in text.rstrip("\n").split(GAP) if p]
    if not pieces:
        return None, "T_N is nothing but gaps"
    for key, val in sources.items():
        at, ok = 0, True
        for n, piece in enumerate(pieces):
            i = val.find(piece, at)
            if i < 0 or (n and i == at):
                ok = False
                break
            at = i + len(piece)
        if ok:
            return key, None
    return None, (f"T_N's pieces around its {text.count(GAP)} gap(s) are not all in one "
                  f"data/nl_*.txt, in order and separated: {[_collapse(p)[:40] for p in pieces]}")


# ---------------------------------------------------------------------------
# one C_F item
# ---------------------------------------------------------------------------
def _cited_text(cite: str, blanked: list[str]) -> tuple[str | None, str | None]:
    """The text the citation points at -> (text, error).

    Read from the comment-blanked lines, so nothing can be quoted out of a comment: a `C_F` item
    citing item1's `/-- A real matrix *supported on* … -/` would otherwise be quoting the prose that
    discusses a definition as if it were the definition.
    """
    m = _CITE.match(cite.strip())
    if not m:
        return None, None                           # not a citation at all; check_citations says so
    lo = int(m.group("lo"))
    hi = int(m.group("hi") or lo)
    if not (1 <= lo <= hi <= len(blanked)):
        return None, f"cites line(s) {lo}-{hi} of a {len(blanked)}-line file"
    return " ".join(_collapse(blanked[i - 1]) for i in range(lo, hi + 1)), None


def _status(sig: str, cited: str, code: str) -> tuple[str, str]:
    """(status, detail) for one signature. A status starting with `!` is an error.

    One question: is it in the cited text, contiguously? The answer is yes or it is an error. The
    only analysis beyond that is to help with the repair — whether the words are somewhere else in
    the file (a citation to fix), or nowhere in it (a string to delete).
    """
    sig_c = _collapse(sig)
    if sig_c in cited:
        return "quoted", ""
    detail = f"{sig_c!r} is not in the cited line(s): {cited!r}"
    if sig_c in code:
        return "!wrong-line", detail + " — but it is elsewhere in the file"
    # The characteristic shape of a reconstruction: `name : type` where each half IS in the file but
    # the whole is not. Named explicitly because it is the failure this gate was written for, and
    # because "both halves are there" is exactly the argument for letting it through.
    head, sep, rest = sig_c.partition(" : ")
    if sep and head in code and rest in code:
        return "!stitched", (f"{detail} — {head!r} and {rest!r} are both in the file, but nothing in "
                             f"it says them together. Quote the clause the proof writes instead.")
    return "!invented", detail


# ---------------------------------------------------------------------------
# one datapoint
# ---------------------------------------------------------------------------
def _check_spans(path: Path, target: str) -> list[str]:
    """`S_F`/`S_N` are UTF-16 intervals into the target, so the only way to show text the source does
    not contain is to point outside it (or backwards)."""
    if not path.exists():
        return []
    n = len(target.encode("utf-16-le")) // 2
    out = []
    for i, span in enumerate(json.loads(path.read_text(encoding="utf-8")) or []):
        for iv in span:
            if not (isinstance(iv, list) and len(iv) == 2):
                out.append(f"{path.parent.name}/{path.name}[{i}]: {iv!r} is not a [start, end] pair")
            elif not (0 <= iv[0] < iv[1] <= n):
                out.append(f"{path.parent.name}/{path.name}[{i}]: {iv!r} is not inside the "
                           f"{n}-unit target")
    return out


def check_unit(art: Path, unit: str, blanked: list[str], code: str,
               nl_sources: dict[str, str], markers: str = "") -> tuple[list[str], list[str], list[str]]:
    """(errors, notes, verbose lines) for one datapoint's artifacts.

    `markers` is the `@pistis_assumption` comment lines of the raw file, joined — the only source an
    `asm-*` unit's `T_F` may be quoted from.
    """
    errors: list[str] = []
    notes: list[str] = []
    seen: list[str] = []

    # ---- T_N: no liberty at all. It is a slice of the NL source and nothing else — or, for a
    # segment whose premises have been subtracted out, the slices around each `…`.
    tn = (art / "nl" / "T_N.txt").read_text(encoding="utf-8")
    if GAP in tn:
        key, gap_err = _find_nl_gapped(tn, nl_sources)
        if key:
            seen.append(f"T_N        quoted   ({key}, {tn.count(GAP)} gap(s), {len(tn)} chars)")
        else:
            errors.append(gap_err or "T_N is not in data/nl_*.txt")
    elif key := _find_nl(tn, nl_sources):
        seen.append(f"T_N        quoted   ({key}, {len(tn)} chars)")
    else:
        errors.append(f"T_N is not a substring of data/nl_*.txt: {_collapse(tn)[:70]!r}…")

    # ---- T_F: the claim, up to whitespace. The statement unit is several lines (header + theorem),
    # each of which must be found, in order; its `sorry` is the one token tf_norm puts in. An
    # `asm-*` unit's type is written in a COMMENT, so for it the quotable source is the marker lines
    # of the raw file rather than the blanked one (see the module docstring).
    tf = (art / "formal" / "T_F.lean").read_text(encoding="utf-8")
    tf_src = markers if unit.startswith("asm-") else code
    lines = [ln for ln in tf.splitlines() if ln.strip()] if unit == "statement" \
        else [_collapse(tf)]
    at = 0
    for k, ln in enumerate(lines):
        want = _collapse(ln)
        if unit == "statement" and k == len(lines) - 1:
            # `sorry` is the ONE token tf_norm inserts, and the permission is that narrow: the
            # declaration up to `:= by` must be quoted and the body must be exactly `sorry`. Any
            # other body is held to the whole line, which is how a swapped-in real tactic shows up
            # (that it is also not the frozen statement is `check_targets.py`'s half of the job).
            if want.endswith(" sorry"):
                want = want[: -len(" sorry")]
            else:
                errors.append("T_F's last line is the theorem, whose body must be `sorry`; this one "
                              f"ends {want[-40:]!r}")
        pos = tf_src.find(want, at)
        if pos < 0:
            where = f"T_F line {k + 1}" if len(lines) > 1 else "T_F"
            src = ("on any @pistis_assumption marker in Main.lean" if unit.startswith("asm-")
                   else "in Main.lean")
            errors.append(f"{where} is not {src}: {want[:70]!r}…" if len(want) > 70
                          else f"{where} is not {src}: {want!r}")
        elif tf_src.find(want) < at and pos != tf_src.find(want, at):
            errors.append(f"T_F line {k + 1} is out of source order: {want[:50]!r}…")
        else:
            at = pos + len(want)
    if not any(e.startswith("T_F") for e in errors):
        seen.append(f"T_F        quoted   ({len(lines)} line(s), whitespace-collapsed)")

    # ---- C_F: the part a seeder can paraphrase, and the reason this gate exists.
    cf = json.loads((art / "formal" / "C_F.json").read_text(encoding="utf-8"))
    for i, it in enumerate(cf.get("items") or []):
        sig = it.get("signature", "")
        cite = (it.get("source") or "").strip()
        cited, err = _cited_text(cite, blanked)
        if err:
            errors.append(f"C_F[{i}] {err}")
            continue
        if cited is None:
            notes.append(f"C_F[{i}] cites {cite!r}, which is not a line of this corpus — "
                         f"{_collapse(sig)!r} is unchecked")
            continue
        status, detail = _status(sig, cited, code)
        if status.startswith("!"):
            errors.append(f"C_F[{i}] {detail}")
        else:
            seen.append(f"C_F[{i}]   {status:<8} {_collapse(sig)[:60]!r}")

    # ---- C_N: free text with its own provenance, so it is held to the provenance it claims.
    cn_path = art / "nl" / "C_N.json"
    for i, it in enumerate(json.loads(cn_path.read_text(encoding="utf-8")) if cn_path.exists()
                           else []):
        text = it if isinstance(it, str) else (it.get("text") or "")
        src = "" if isinstance(it, str) else (it.get("source") or "").strip()
        key = _find_nl(text, nl_sources)
        if key:
            seen.append(f"C_N[{i}]   quoted   ({key})")
        elif src and not src.startswith(("items/", "data/")):
            notes.append(f"C_N[{i}] is not in data/nl_*.txt; its source is {src!r}, outside this "
                         f"corpus — unchecked")
        else:
            errors.append(f"C_N[{i}] is not a substring of data/nl_*.txt: {_collapse(text)[:70]!r}")

    # ---- I: implicit NL context is what the reader supplies and the text does NOT say, so being
    # absent from the source is its definition. Counted, never checked.
    i_path = art / "nl" / "I.json"
    n_i = len(json.loads(i_path.read_text(encoding="utf-8")) or []) if i_path.exists() else 0
    if n_i:
        seen.append(f"I          authored ({n_i} entr(ies) — implicit by definition, not quotable)")

    errors += _check_spans(art / "formal" / "S_F.json", tf)
    errors += _check_spans(art / "nl" / "S_N.json", tn)
    return errors, notes, seen


def check_item(item_dir: Path) -> tuple[list[str], list[str], list[str]]:
    """(errors, notes, verbose lines) for every datapoint of one item."""
    item_dir = item_dir.resolve()
    src = (item_dir / "Main.lean").read_text(encoding="utf-8")
    # Quotable source: the file with its comments blanked out, one entry per line. Joined by a single
    # space it is also the whole file as one string -- so a claim written over several indented lines
    # is contiguous here, and nothing can be "found" in a docstring that merely discusses it.
    blanked = _code_lines(src)
    code = _collapse(" ".join(blanked))
    # An assumption's TYPE is written in a comment, so `blanked` cannot hold it. Its quotable source
    # is the marker lines themselves, and nothing else in the file — not an ordinary comment, not a
    # docstring. Each line separately (not joined), so a type cannot be stitched across two markers.
    markers = "\n".join(ln for ln in src.splitlines() if "@pistis_assumption" in ln)
    markers = "\n".join(_collapse(ln) for ln in markers.splitlines())
    nl_sources = _nl_sources(item_dir)
    errors: list[str] = []
    notes: list[str] = []
    seen: list[str] = []
    align = item_dir / "align"
    for d in sorted(p for p in align.glob("*") if p.is_dir()) if align.is_dir() else []:
        art = d / "artifacts"
        if not (art / "formal" / "T_F.lean").exists():
            continue
        e, n, s = check_unit(art, d.name, blanked, code, nl_sources, markers)
        errors += [f"{d.name}: {x}" for x in e]
        notes += [f"{d.name}: {x}" for x in n]
        seen += [f"{d.name:<10} {x}" for x in s]
    return errors, notes, seen


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Check that every string a datapoint shows is in the "
                                             "source it cites.")
    ap.add_argument("items", nargs="*", help="item dirs, e.g. items/item1 (default: all)")
    ap.add_argument("-v", "--verbose", action="store_true",
                    help="print every checked string and how it is quoted")
    ap.add_argument("-q", "--quiet", action="store_true", help="errors only, no notes")
    args = ap.parse_args(argv)
    dirs = [Path(p) for p in args.items] or sorted(
        p for p in (REPO / "items").glob("item*") if (p / "Main.lean").exists())
    total, n_notes, n_ok = 0, 0, 0
    for d in dirs:
        errors, notes, seen = check_item(d)
        print(f"[{'FAIL' if errors else 'ok'}] {d}")
        for e in errors:
            print("    ERROR  " + e)
        if not args.quiet:
            for n in notes:
                print("    note   " + n)
        if args.verbose:
            for s in seen:
                print("    · " + s)
        total += len(errors)
        n_notes += len(notes)
        n_ok += len(seen)
    tail = f" ({n_notes} note(s))" if n_notes and not args.quiet else ""
    print(f"\n{total} string(s) not in the source{tail}" if total
          else f"\n{n_ok} string(s) checked, every one of them in the source it cites{tail}")
    return 1 if total else 0


if __name__ == "__main__":
    raise SystemExit(main())
