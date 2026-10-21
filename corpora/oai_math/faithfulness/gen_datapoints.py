#!/usr/bin/env python3
"""Generate the align-then-label datapoints for an item from its proof.

One datapoint per unit of `pistis_proof.proof_outline` — the statement and every `pistis_segment` —
laid out exactly as faithfulness-dataset expects:

    items/item<N>/align/<unit>/artifacts/
        format.json                 {offset_unit: "utf16", coverage: …}
        formal/T_F.lean             the formal target  (GENERATED, fixed)
        formal/C_F.json             {pin, available: [], items: […]}  (seeded, then authored)
        formal/S_F.json             regions of T_F     (seeded, then authored)
        formal/version.txt          the toolchain + mathlib pin
        nl/T_N.txt                  the NL target      (GENERATED, fixed)
        nl/S_N.json                 regions of T_N     (seeded, then authored)
        nl/C_N.json, nl/I.json      NL context / implicit assumptions (authored)
        relation/R.json             the edges          (authored)
        relation/lambda.json        the verdicts       (authored)
        label.txt, done.txt         derived / manual

What is SEEDED and what is not
------------------------------
Seeded, because it is DERIVED from files already gated as verbatim:
  * both targets — for a `seg-*` unit `T_N` is its sentence MINUS the substrings `split.json` lists
    under `assumptions` (a `…` left where each was), because the claim answers the segment's
    `assert` and not the premises it consumes, and `T_F` is that claim; for an `asm-*` unit the pair
    is the assumption clause and the Lean type on its `pistis_assumption` tactic. Every piece of
    both is text `check_main.py` already gates verbatim against `data/nl_*.txt` / `Main.lean`;
  * `S_N[0]` — the unit's focus substring: `split.json`'s `assert`, the single thing the segment
    asserts, already gated as an exact substring of the segment's text by `check_split.py` (for an
    `asm-*` unit, the whole clause);
  * `S_F[0]` — the whole formal target, as one region;
  * `C_F.items` — what this sentence introduces, i.e. the `obtain`/`set`/`have` lines between its
    tactic and the previous one, and nothing else (see `pistis_proof`).

NOT seeded, because it is the JUDGMENT the labeler is here to make: `R` (which region corresponds to
which) and `lambda` (whether each correspondence holds, and why). They start empty, so `label.txt` is
`NaN` until a human labels. For item1 that judgment is authored in `annotate_item1.py`, which is
re-runnable precisely because `--force` throws spans and edges away.

Existing work is never clobbered: a datapoint whose stored targets still match is left untouched, and
one whose targets have CHANGED is reported as stale (its spans index into the old text) and rewritten
only under `--force`.

Usage:
    python3 faithfulness/gen_datapoints.py items/item1            # create / report
    python3 faithfulness/gen_datapoints.py items/item1 --force    # rewrite stale datapoints
    python3 faithfulness/gen_datapoints.py --all
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent                                  # the corpus root
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "ui"))
from alignment_data import _utf16_len               # noqa: E402
from pistis_proof import proof_outline              # noqa: E402
from serve import detect_versions, version_text     # noqa: E402


def _utf16_span(text: str, needle: str) -> list[list[int]] | None:
    """The UTF-16 interval of `needle`'s first occurrence in `text`, or None if absent."""
    i = text.find(needle)
    if i < 0 or not needle:
        return None
    start = _utf16_len(text[:i])
    return [[start, start + _utf16_len(needle)]]


def _content_span(text: str) -> list[list[int]] | None:
    """The UTF-16 interval of `text`'s non-whitespace content (one region over the whole target)."""
    body = text.strip()
    return _utf16_span(text, body) if body else None


def stored_target(text: str) -> str:
    """A target as it goes to disk: verbatim, with exactly one trailing newline and nothing else.

    `check_targets.py` holds the stored files to this, so the convention lives in one place.
    """
    return text if text.endswith("\n") else text + "\n"


def _dump(path: Path, obj) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def _unit_files(unit: dict, versions: dict) -> dict[str, object]:
    """The full artifacts content for one unit, keyed by path relative to `artifacts/`."""
    # Targets are written VERBATIM — no strip, no re-wrap. T_N must stay byte-identical to its slice
    # of the source, which is the whole point of the Pistis text gates.
    t_f = stored_target(unit["formal"])
    t_n = stored_target(unit["nl_text"])
    # A segment's formal target is exactly the one proposition it asserts, so a single region over it
    # is the right (and derived) seed. The statement is not atomic — how to cut a theorem into regions
    # is the labeler's judgment — so it gets no seed on either side. An `asm-*` unit is atomic in the
    # same way and more simply: `T_N` is the one clause `split.json` quotes and `T_F` is the one type
    # on its marker, so `nl_focus` is the whole target and both seeds cover everything.
    atomic = unit["kind"] in ("segment", "assumption")
    s_f = _content_span(t_f) if atomic else None
    s_n = _utf16_span(t_n, unit["nl_focus"]) if atomic else None
    # A context item is a QUOTE of the proof and its citation — the clause as written, and the line(s)
    # it is written on. Nothing else: a `name` beside it was a second, paraphrased way of saying what
    # the clause already says, and a signature the file does not spell out in those words has no
    # business being shown at all (`check_verbatim.py` is the gate).
    items = [{"signature": c["signature"], "source": c["source"]} for c in unit["context"]]
    return {
        "format.json": {"offset_unit": "utf16", "coverage": unit["coverage"]},
        "formal/T_F.lean": t_f,
        "formal/S_F.json": [s_f] if s_f else [],
        "formal/C_F.json": {"pin": versions, "available": [], "items": items},
        "formal/version.txt": version_text(versions),
        "nl/T_N.txt": t_n,
        "nl/S_N.json": [s_n] if s_n else [],
        "nl/C_N.json": [],
        "nl/I.json": [],
        "relation/R.json": [],
        "relation/lambda.json": [],
        "label.txt": "NaN\n",
        "done.txt": "false\n",
    }


def _write(art: Path, files: dict[str, object]) -> None:
    for name, val in files.items():
        path = art / name
        path.parent.mkdir(parents=True, exist_ok=True)
        if isinstance(val, str):
            path.write_text(val, encoding="utf-8")
        else:
            _dump(path, val)


def _drift(art: Path, files: dict[str, object]) -> list[str]:
    """Which SEEDED files on disk no longer match what the proof derives, by name.

    Both targets and the formal context are compared. Comparing `C_F.items` is deliberate: a change to
    `pistis_proof._ambient` — a binder's signature now read correctly, say — otherwise never reaches a
    datapoint that already exists, and the annotation would go on citing text that is not there. The
    cost is that `C_F.items` edited by hand in the UI reads as drift too; losing it to `--force` is
    recoverable, whereas silent disagreement between the proof and the datapoint is not.
    """
    pairs = [("formal/T_F.lean", "T_F"), ("nl/T_N.txt", "T_N")]
    out = [label for name, label in pairs
           if (art / name).read_text(encoding="utf-8") != files[name]]
    stored = json.loads((art / "formal" / "C_F.json").read_text(encoding="utf-8"))
    if stored.get("items") != files["formal/C_F.json"]["items"]:      # type: ignore[index]
        out.append("C_F.items")
    return out


def generate(item_dir: Path, *, force: bool) -> tuple[int, list[str]]:
    """Create/refresh every unit's datapoint under `<item>/align/`. Returns (n_errors, report)."""
    outline = proof_outline(item_dir)
    versions = detect_versions()
    report, errors = [], 0
    for unit in outline["units"]:
        art = item_dir / "align" / unit["id"] / "artifacts"
        files = _unit_files(unit, versions)
        rel = str((item_dir / "align" / unit["id"]).relative_to(REPO))
        if not (art / "formal" / "T_F.lean").exists():
            _write(art, files)
            report.append(f"[new ] {rel}")
            continue
        drift = _drift(art, files)
        if not drift:
            report.append(f"[ok  ] {rel}")
        elif force:
            _write(art, files)
            report.append(f"[redo] {rel}  ({', '.join(drift)} changed; spans/edges reset)")
        else:
            errors += 1
            report.append(f"[STALE] {rel}  {', '.join(drift)} changed in Main.lean/split.json — any "
                          f"stored spans and edges index into the old text. Re-run with --force to "
                          f"rewrite.")
    return errors, report


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Generate align-then-label datapoints for an item.")
    ap.add_argument("items", nargs="*", help="item dirs, e.g. items/item1")
    ap.add_argument("--all", action="store_true", help="every items/item* with a Main.lean")
    ap.add_argument("--force", action="store_true",
                    help="rewrite datapoints whose targets changed (DISCARDS their spans and edges)")
    args = ap.parse_args(argv)

    dirs = [Path(p) for p in args.items]
    if args.all:
        dirs = sorted(p for p in (REPO / "items").glob("item*") if (p / "Main.lean").exists())
    if not dirs:
        ap.print_usage(sys.stderr)
        return 2

    total = 0
    for d in dirs:
        errors, report = generate(d.resolve(), force=args.force)
        print(f"=== {d}")
        for line in report:
            print("  " + line)
        total += errors
    print(f"\n{total} stale datapoint(s)" if total else "\nall datapoints up to date")
    return 1 if total else 0


if __name__ == "__main__":
    raise SystemExit(main())
