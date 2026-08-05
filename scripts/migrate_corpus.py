#!/usr/bin/env python3
"""One-shot migration: flat proofnet-verified corpus -> per-item folders.

Before:
    proofnet-verified/
    ├── proofnet-<N>.lean          (formal statement, := by sorry)
    └── data/
        ├── proofnet-<N>.json      ({nl_statement, nl_proof})
        └── proofnet-verified.jsonl (master; source of truth)

After (this script CREATES; it does NOT delete the originals — that's a separate manual step
after you verify):
    proofnet-verified/
    ├── item<N>/
    │   ├── meta.json              ({name, source, textbook, index})
    │   └── data/
    │       ├── nl.json            ({nl_statement, nl_proof})  regenerated from the master jsonl
    │       └── statement.lean     the formal statement, copied verbatim from proofnet-<N>.lean
    └── ... (old files still present until you delete them)

Usage:
    python3 scripts/migrate_corpus.py                 # DRY RUN (default): prints what it would do
    python3 scripts/migrate_corpus.py --apply         # actually create the item folders
    python3 scripts/migrate_corpus.py --apply --verify-only   # re-check an already-migrated corpus

Idempotent: re-running with --apply overwrites the generated files; it never deletes anything.
"""
from __future__ import annotations

import argparse
import json
import os

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CORPUS = os.path.join(REPO, "proofnet-verified")
JSONL = os.path.join(CORPUS, "data", "proofnet-verified.jsonl")
SOURCE = "proofnet-verified"  # the meta.source value


def load_master() -> dict[int, dict]:
    """index -> full jsonl record."""
    recs = {}
    with open(JSONL, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            d = json.loads(line)
            recs[d["index"]] = d
    return recs


def build_item(rec: dict, apply: bool) -> list[str]:
    """Return the list of files that would be / were written for one record."""
    idx = rec["index"]
    itemdir = os.path.join(CORPUS, f"item{idx}")
    datadir = os.path.join(itemdir, "data")

    meta = {
        "name": rec["name"],
        "source": SOURCE,
        "textbook": rec["textbook"],
        "index": idx,
    }
    nl = {"nl_statement": rec["informal_stmt"], "nl_proof": rec["informal_proof"]}

    # statement.lean = the existing per-problem formal file, verbatim.
    src_lean = os.path.join(CORPUS, f"proofnet-{idx}.lean")
    if not os.path.exists(src_lean):
        raise FileNotFoundError(f"missing formal statement file: {src_lean}")
    statement_text = open(src_lean, encoding="utf-8").read()

    targets = [
        os.path.join(itemdir, "meta.json"),
        os.path.join(datadir, "nl.json"),
        os.path.join(datadir, "statement.lean"),
    ]

    if apply:
        os.makedirs(datadir, exist_ok=True)
        with open(targets[0], "w", encoding="utf-8") as fh:
            json.dump(meta, fh, ensure_ascii=False, indent=2)
            fh.write("\n")
        with open(targets[1], "w", encoding="utf-8") as fh:
            json.dump(nl, fh, ensure_ascii=False, indent=2)
            fh.write("\n")
        with open(targets[2], "w", encoding="utf-8") as fh:
            fh.write(statement_text)

    return targets


def verify(recs: dict[int, dict]) -> tuple[int, list[str]]:
    """Check every item folder has its 3 files and nl.json matches the master. Returns (ok_count, errors)."""
    errors = []
    ok = 0
    for idx, rec in recs.items():
        itemdir = os.path.join(CORPUS, f"item{idx}")
        meta_p = os.path.join(itemdir, "meta.json")
        nl_p = os.path.join(itemdir, "data", "nl.json")
        stmt_p = os.path.join(itemdir, "data", "statement.lean")
        missing = [p for p in (meta_p, nl_p, stmt_p) if not os.path.exists(p)]
        if missing:
            errors.append(f"item{idx}: missing {', '.join(os.path.relpath(m, CORPUS) for m in missing)}")
            continue
        nl = json.load(open(nl_p, encoding="utf-8"))
        if nl["nl_statement"] != rec["informal_stmt"] or nl["nl_proof"] != rec["informal_proof"]:
            errors.append(f"item{idx}: nl.json does not match master jsonl")
            continue
        stmt = open(stmt_p, encoding="utf-8").read()
        orig = open(os.path.join(CORPUS, f"proofnet-{idx}.lean"), encoding="utf-8").read()
        if stmt != orig:
            errors.append(f"item{idx}: statement.lean does not match proofnet-{idx}.lean")
            continue
        ok += 1
    return ok, errors


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--apply", action="store_true", help="actually write files (default is dry run)")
    ap.add_argument("--verify-only", action="store_true", help="only verify an already-migrated corpus")
    args = ap.parse_args(argv)

    recs = load_master()
    print(f"master jsonl: {len(recs)} records (index range {min(recs)}..{max(recs)})")

    if args.verify_only:
        ok, errors = verify(recs)
        print(f"verify: {ok}/{len(recs)} items OK")
        for e in errors[:20]:
            print("  " + e)
        if len(errors) > 20:
            print(f"  ... and {len(errors) - 20} more")
        return 0 if not errors else 1

    if not args.apply:
        print("DRY RUN (pass --apply to write). Sample of what would be created:")
        for idx in sorted(recs)[:2] + sorted(recs)[-1:]:
            targets = build_item(recs[idx], apply=False)
            print(f"  item{idx} ({recs[idx]['name']}, {recs[idx]['textbook']}):")
            for t in targets:
                print(f"    + {os.path.relpath(t, REPO)}")
        print(f"Total: would create {len(recs)} item folders x 3 files = {len(recs) * 3} files.")
        return 0

    # apply
    n = 0
    for idx in sorted(recs):
        build_item(recs[idx], apply=True)
        n += 1
    print(f"created {n} item folders")
    ok, errors = verify(recs)
    print(f"verify: {ok}/{len(recs)} items OK")
    for e in errors[:20]:
        print("  " + e)
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
