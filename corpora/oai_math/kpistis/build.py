#!/usr/bin/env python3
"""Seed an item's K-Pistis tree from `Proof.lean` and the item's existing NL.

Three things are derived, never authored:

* **the root's targets.** `T_F` is `Proof.lean` verbatim — the whole file, imports and comments
  included, because a span has to be an offset into the real text. `T_N` is the item's
  `data/nl_statement.txt` + `data/nl_proof.txt`, joined by the blank line that separates them in
  the paper.
* **the root's `S_F`.** One region per `--| <loc>` marker (see `model.markers`).
* **the root's `S_N`.** One region per entry of the item's `split.json`, each one LOCATED by
  searching `T_N` for its text rather than assumed to tile it, so a drift in either file is a loud
  `needle not found` here.

one thing is left empty on purpose:

* **`C_N`**, the prose each NL region must be read against. Seeded as one empty list per region — the
  right *shape*, no content — and the gate then fails until a human fills in every region an edge
  judges. *Which* sentences a step depends on is the judgment being recorded, and seeding it with
  "the surrounding paragraph" would be inventing that judgment rather than collecting it.

and one thing is seeded:

* **the root's edges**, wherever a marker loc `1.k` matches `split.json`'s k-th entry. That matching
  is the formalizer's own claim about which step answers which sentence, so it belongs in the file;
  the verdict stays `null`, because that is the judgment a human is here to make.

Regions with no `1.k` loc — `hdr`, `idx`, `def`, `thm`, `tech` — are deliberately left unlinked. The
statement is not one sentence and `classical` is not any sentence; how to cut them up is the
labeler's call, and `items/item1`'s authored annotation (`annotate_item1.py`) is what makes it.

    python3 kpistis/build.py item1            # seed (keeps anything already there)
    python3 kpistis/build.py item1 --force    # re-seed, discarding edits to the root
"""
from __future__ import annotations

import argparse
import json
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import model
from model import CORPUS, ROOT, find_span, markers, u16cut


def nl_target(item: str) -> str:
    """The root's `T_N`: the item's statement and proof, joined by the blank line that separates
    them in the paper. Each half is read verbatim from its own `.txt` (bytes = the paper's bytes,
    no trailing newline), so the join is the ONLY byte this function adds."""
    data = CORPUS / "items" / item / "data"
    halves = [(data / f"{name}.txt").read_text(encoding="utf-8", newline="")
              for name in ("nl_statement", "nl_proof")]
    return "\n\n".join(halves)


def split_regions(item: str, target: str) -> tuple[list, list[str]]:
    """`S_N` seeds and their locs, from the item's `split.json`, in document order."""
    split = json.loads((CORPUS / "items" / item / "split.json").read_text(encoding="utf-8"))
    spans, locs, at = [], [], 0
    for k, entry in enumerate(split):
        span = find_span(target, entry["text"], start=at)
        at = len(u16cut(target, 0, span[1]))
        spans.append([span])
        locs.append("stmt" if entry.get("role") == "intro" else f"1.{k}")
    return spans, locs


def seed(item: str, *, force: bool = False) -> dict:
    src = (ROOT / "items" / item / "Proof.lean").read_text(encoding="utf-8")
    target_n = nl_target(item)
    marks = markers(src)
    s_n, n_locs = split_regions(item, target_n)
    n_of = {loc: i for i, loc in enumerate(n_locs)}

    unit = {
        "id": item, "path": "root", "item": item,
        "loc": "root", "title": "Lemma 3.2 (Kernels at maximum support rank)",
        "category": "document", "child_category": "proof step",
        "provenance": {"kind": "file", "T_F": f"kpistis/items/{item}/Proof.lean",
                       "T_N": f"items/{item}/data/nl_statement.txt + nl_proof.txt"},
        "done": False,
        "T_F": src, "T_N": target_n,
        # One empty citation list per NL region — the shape, not the content. The root is NOT exempt:
        # context belongs to the region being claimed, and the root's regions are claimed by thirteen
        # edges. `model.cn_errors` fails until each of those regions has a cited reason.
        "C_N": [[] for _ in s_n],
        "S_F": [[m["span"]] for m in marks], "S_N": s_n,
        "edges": [{"f": i, "n": n_of[m["loc"]], "v": None, "why": "", "child": m["loc"]}
                  for i, m in enumerate(marks) if m["loc"] in n_of],
    }
    # The locs ride along so the UI can name a region; they are not part of the model.
    unit["F_locs"] = [m["loc"] for m in marks]
    unit["N_locs"] = n_locs

    out = model.unit_dir(item, "root")
    if out.exists() and not force:
        print(f"[keep ] units/{item}/root already exists; --force to re-seed")
        return model.load(item, "root")
    if out.exists():
        shutil.rmtree(out)
    model.save(unit)
    print(f"[seed ] units/{item}/root  —  {len(unit['S_F'])} formal regions, "
          f"{len(unit['S_N'])} NL regions, {len(unit['edges'])} seeded edges")
    return unit


def scaffold_children(item: str, path: str = "root", *, force: bool = False) -> int:
    """A child unit for every edge with a `child` name: the edge's two region texts, nothing else.

    `child.T_F` is the formal region's text and `child.T_N` the NL region's — byte for byte, which is
    what `check.py` holds them to. Its own `S_F`/`S_N`/`edges` start empty: the atomic cut is the next
    level's labelling, and seeding it would be inventing it.
    """
    parent = model.load(item, path)
    made = 0
    for e in parent["edges"]:
        name = e.get("child")
        if not name or e.get("f") is None or e.get("n") is None:
            continue
        d = model.unit_dir(item, f"{path}/{name}")
        exists = (d / "unit.json").exists()
        if exists and not force:
            continue
        kept = model.load(item, f"{path}/{name}") if exists else {}
        child = {
            "id": f"{item}/{name}", "path": f"{path}/{name}", "item": item,
            "loc": name, "title": f"step {name}",
            "category": parent.get("child_category", "proof step"),
            "child_category": "atomic", "done": False,
            "provenance": {"kind": "span", "parent": path, "f": e["f"], "n": e["n"]},
            "T_F": model.region_text(parent["T_F"], parent["S_F"][e["f"]]),
            "T_N": model.region_text(parent["T_N"], parent["S_N"][e["n"]]),
            # `C_N` is left empty with the rest: which sentences of the paper a region has to be read
            # against is a judgment, and seeding it with "the neighbouring paragraph" would be
            # inventing that judgment. The gate then fails until someone makes it.
            "C_N": kept.get("C_N", []),
            "S_F": kept.get("S_F", []), "S_N": kept.get("S_N", []), "edges": kept.get("edges", []),
        }
        if exists and (kept["T_F"], kept["T_N"]) != (child["T_F"], child["T_N"]):
            print(f"[STALE] units/{item}/{path}/{name}: its target moved in the parent; "
                  f"--force to re-cut (its spans index into the old text)")
            continue
        model.save(child)
        made += 1
    if made:
        print(f"[seed ] {made} child unit(s) under {path}")
    for child in model.load(item, path)["children"]:
        made += scaffold_children(item, f"{path}/{child}", force=force)
    return made


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Seed an item's K-Pistis tree from Proof.lean.")
    ap.add_argument("item", nargs="?", default="item1")
    ap.add_argument("--force", action="store_true", help="discard what is there and re-seed")
    args = ap.parse_args(argv)
    seed(args.item, force=args.force)
    scaffold_children(args.item, force=args.force)
    print()
    show(model.rollup(args.item))
    return 0


def show(node: dict, depth: int = 0) -> None:
    own = node["own"]
    cov = own["coverage"]
    print(f"{'  ' * depth}[{node['label']:<10}] {node['loc']:<6} "
          f"F {cov['F']['covered']}/{cov['F']['total']}  N {cov['N']['covered']}/{cov['N']['total']}"
          f"  edges {own['edges']} (⊥ {own['bot']}, open {len(own['open_edges'])}, "
          f"bad {len(own['bad_edges'])})"
          + (f"  crossings {len(own['inversions'])}" if own["inversions"] else ""))
    for err in own["errors"]:
        print(f"{'  ' * depth}   ! {err}")
    for sub in node["children"].values():
        show(sub, depth + 1)


if __name__ == "__main__":
    raise SystemExit(main())
