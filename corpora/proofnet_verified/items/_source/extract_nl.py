#!/usr/bin/env python3
"""Regenerate each ProofNet item's NL source from the master `proofnet-verified.jsonl`.

For every record, write the two texts VERBATIM into the item's data directory:

    items/item<N>/data/nl_statement.txt   <- record["informal_stmt"]
    items/item<N>/data/nl_proof.txt       <- record["informal_proof"]

Each file's bytes are the text's bytes and nothing else: no JSON escaping, no trailing newline,
nothing stripped or re-wrapped. Every gate in this repo compares these texts byte-for-byte, so the
storage format is the bytes themselves — which is also what makes them greppable and Ctrl-F-able.
(The old `nl.json` stored a newline as the two characters `\\` `n` and doubled every backslash, so
searching the file for what you saw in it found nothing.)

This is the independent regeneration path for the ProofNet corpus: it goes from the master jsonl
straight to the `.txt` files, touching no other script. Running it and getting no diff is therefore
a real check on whatever else wrote those files.

Usage:
    python3 extract_nl.py            # DRY RUN: report what would change
    python3 extract_nl.py --apply    # write the files
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ITEMS = HERE.parent
JSONL = HERE / "proofnet-verified.jsonl"
FIELDS = {"nl_statement": "informal_stmt", "nl_proof": "informal_proof"}


def records() -> list[dict]:
    out = []
    for line in JSONL.open(encoding="utf-8"):
        line = line.strip()
        if line:
            out.append(json.loads(line))
    return out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--apply", action="store_true", help="write files (default is a dry run)")
    args = ap.parse_args(argv)

    recs = records()
    changed, missing_dir, n = [], [], 0
    for rec in recs:
        data = ITEMS / f"item{rec['index']}" / "data"
        if not data.is_dir():
            missing_dir.append(str(data.relative_to(ITEMS)))
            continue
        for name, key in FIELDS.items():
            path = data / f"{name}.txt"
            want = rec[key]
            have = path.read_text(encoding="utf-8", newline="") if path.exists() else None
            if have != want:
                changed.append(f"{path.relative_to(ITEMS)} ({'differs' if have is not None else 'new'})")
            if args.apply:
                path.write_text(want, encoding="utf-8", newline="")
        n += 1

    print(f"master jsonl: {len(recs)} record(s); {n} item dir(s) present")
    for m in missing_dir[:10]:
        print(f"  no data dir: {m}")
    if changed:
        print(f"{len(changed)} file(s) {'written' if args.apply else 'would change'}:")
        for c in changed[:20]:
            print(f"  {c}")
        if len(changed) > 20:
            print(f"  ... and {len(changed) - 20} more")
    else:
        print("all .txt files already byte-identical to the master jsonl")
    return 1 if (missing_dir and not args.apply) else 0


if __name__ == "__main__":
    raise SystemExit(main())
