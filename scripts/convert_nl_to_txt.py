#!/usr/bin/env python3
"""One-shot migration: `data/nl.json` -> `data/nl_statement.txt` + `data/nl_proof.txt`.

Why
---
`nl.json` stored the two NL texts as JSON strings, which means the bytes ON DISK are not the bytes
of the text: a newline is stored as the two characters `\\` `n`, and every LaTeX backslash is
doubled (`\\\\subseteq`). The text is therefore not greppable and not Ctrl-F-able against the `.tex`
it was sliced from — you cannot search for what you see. Since every gate in this repo compares
these texts BYTE-FOR-BYTE, the storage format should be the bytes themselves.

After this migration each item carries the two texts as plain UTF-8 files whose contents are
literally the text, so `grep -f` and editor Ctrl-F work directly against the paper's `.tex`.

What it does, exactly
---------------------
For each `<corpus>/items/item<N>/data/nl.json`, write

    data/nl_statement.txt   <- json["nl_statement"], verbatim
    data/nl_proof.txt       <- json["nl_proof"],     verbatim

NO trailing newline is appended and nothing is stripped, re-wrapped or normalized. The file's bytes
are `text.encode("utf-8")` and nothing else. A trailing `\\n` would be a byte the source does not
have, and `kpistis/check.py` compares `T_N` to `nl_statement + "\\n\\n" + nl_proof` with `!=` — so
"just a trailing newline" would break the root gate. The point of the migration is that the file IS
the text; adding a convenience byte would give that up on day one.

The conversion step is purely additive — it never deleted an `nl.json`, so a bad run cost an `rm`
rather than a recovery. The migration has since been completed and the 368 `nl.json` removed in a
separate commit, so `--apply` is spent and this script is now kept for `--verify` and as the record
of what the migration did.

Verification
------------
`--verify` does not trust this script's own output path: it reads the ORIGINAL `nl.json` from
`git show <BASE>:<path>` and compares that against the `.txt` files in the working tree. So the
comparison is against committed history, which the migration cannot have touched. Both the file
LIST and its contents come from git, so this keeps working after `nl.json` is deleted — a
working-tree glob would find nothing and vacuously "pass".

Usage
-----
    python3 scripts/convert_nl_to_txt.py              # DRY RUN: list what would be written
    python3 scripts/convert_nl_to_txt.py --apply      # write the .txt files
    python3 scripts/convert_nl_to_txt.py --verify     # compare working tree against git history
"""
from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
# The commit the NL text is verified against. `nl.json` was deleted in the working tree after the
# migration, so ground truth is this revision, not the current tree. Override with --base.
BASE = "e9bba4b"
FIELDS = {"nl_statement": "nl_statement.txt", "nl_proof": "nl_proof.txt"}


def items() -> list[Path]:
    """Every `data/nl.json` in every corpus, in a stable order.

    Enumerated from the COMMIT the migration started from, not from the working tree: the whole
    point of `--verify` is to check the `.txt` files against bytes this script cannot have written,
    and once `nl.json` is deleted a working-tree glob finds nothing and the check silently passes on
    an empty set. Reading the list from git keeps it honest after the cleanup commit too.
    """
    out = subprocess.run(["git", "-C", str(REPO), "ls-tree", "-r", "--name-only", BASE],
                         capture_output=True, text=True)
    if out.returncode != 0:
        raise SystemExit(f"cannot list {BASE}: {out.stderr.strip()}")
    return [REPO / line for line in out.stdout.splitlines()
            if line.startswith("corpora/") and line.endswith("/data/nl.json")]


def _git_json(path: Path) -> dict:
    """The committed `nl.json` at `BASE` — ground truth this script cannot have written."""
    rel = path.relative_to(REPO).as_posix()
    out = subprocess.run(["git", "-C", str(REPO), "show", f"{BASE}:{rel}"],
                         capture_output=True, text=True)
    if out.returncode != 0:
        raise FileNotFoundError(f"{rel} is not in {BASE}: {out.stderr.strip()}")
    return json.loads(out.stdout)


def convert(nl_path: Path, apply: bool) -> list[Path]:
    """Write (or, in dry-run, just name) the two `.txt` files for one item."""
    if not nl_path.exists():
        raise SystemExit(f"{nl_path.relative_to(REPO)} is gone — the migration is already done and "
                         f"`--apply` is spent. Use --verify to re-check the .txt files against "
                         f"{BASE}, or `git checkout {BASE} -- corpora` to get the old files back.")
    data = json.loads(nl_path.read_text(encoding="utf-8"))
    missing = [k for k in FIELDS if not isinstance(data.get(k), str)]
    if missing:
        raise KeyError(f"{nl_path}: missing string field(s) {missing}")

    written = []
    for field, name in FIELDS.items():
        out = nl_path.parent / name
        if apply:
            # Verbatim bytes: no trailing newline, no normalization. See the module docstring.
            out.write_text(data[field], encoding="utf-8", newline="")
            back = out.read_text(encoding="utf-8", newline="")
            if back != data[field]:
                raise AssertionError(f"{out}: read-back differs from nl.json (bug)")
        written.append(out)
    return written


def verify() -> tuple[int, list[str]]:
    """Compare every item's `.txt` files against the `nl.json` committed at `BASE`."""
    errors: list[str] = []
    ok = 0
    for nl_path in items():
        try:
            head = _git_json(nl_path)
        except (FileNotFoundError, json.JSONDecodeError) as e:
            errors.append(str(e))
            continue
        rel = nl_path.parent.relative_to(REPO).as_posix()
        item_ok = True
        for field, name in FIELDS.items():
            txt = nl_path.parent / name
            if not txt.exists():
                errors.append(f"{rel}: {name} does not exist")
                item_ok = False
                continue
            got = txt.read_text(encoding="utf-8", newline="")
            want = head[field]
            if got != want:
                where = next((i for i in range(min(len(got), len(want))) if got[i] != want[i]),
                             min(len(got), len(want)))
                errors.append(f"{rel}: {name} differs from {BASE}:nl.json at char {where} "
                              f"(len {len(got)} vs {len(want)})")
                item_ok = False
        ok += item_ok
    return ok, errors


def main(argv=None) -> int:
    global BASE
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--apply", action="store_true", help="write the files (default is a dry run)")
    ap.add_argument("--verify", action="store_true",
                    help="compare the working tree's .txt files against the nl.json in --base")
    ap.add_argument("--base", default=BASE, help=f"revision holding the original nl.json (default {BASE})")
    args = ap.parse_args(argv)
    BASE = args.base

    found = items()
    if not found:
        raise SystemExit(f"no data/nl.json found in {BASE} — nothing to verify against")
    print(f"{len(found)} item(s) with data/nl.json in {BASE}")

    if args.verify:
        ok, errors = verify()
        for e in errors[:20]:
            print("  ERROR  " + e)
        if len(errors) > 20:
            print(f"  ... and {len(errors) - 20} more")
        print(f"verify: {ok}/{len(found)} item(s) byte-identical to {BASE}:nl.json")
        return 1 if errors else 0

    if not args.apply:
        print("DRY RUN (pass --apply to write). Sample:")
        for nl_path in found[:2] + found[-1:]:
            for out in convert(nl_path, apply=False):
                print(f"    + {out.relative_to(REPO)}")
        print(f"Total: would write {len(found) * 2} .txt file(s); no nl.json is deleted.")
        return 0

    n = 0
    for nl_path in found:
        convert(nl_path, apply=True)
        n += 1
    print(f"wrote {n * 2} .txt file(s) for {n} item(s)")
    ok, errors = verify()
    for e in errors[:20]:
        print("  ERROR  " + e)
    print(f"verify: {ok}/{len(found)} item(s) byte-identical to {BASE}:nl.json")
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
