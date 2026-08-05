#!/usr/bin/env python3
"""Read proofnet-verified.jsonl and write one JSON per problem, matching proofnet-N.lean.

Each output file (proofnet-N.json, written next to this script in data/) contains exactly the
two NL fields, verbatim:
    { "nl_statement": ..., "nl_proof": ... }
"""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
JSONL = HERE / "proofnet-verified.jsonl"


def main() -> None:
    n = 0
    for line in JSONL.open(encoding="utf-8"):
        line = line.strip()
        if not line:
            continue
        d = json.loads(line)
        rec = {"nl_statement": d["informal_stmt"], "nl_proof": d["informal_proof"]}
        (HERE / f"proofnet-{d['index']}.json").write_text(
            json.dumps(rec, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
        )
        n += 1
    print(f"wrote {n} files to {HERE}")


if __name__ == "__main__":
    main()
