#!/usr/bin/env python3
"""The gate. Everything a K-Pistis tree claims, re-derived from the files it claims it about.

Nine checks, and the one that matters most is the third:

1. **spans**  every interval is nonempty, in bounds and does not split a surrogate pair.
2. **edges**  endpoints are real region indices, no ⊥↦⊥, verdicts are 0/1/null, judged edges have a
   reason, ⊥ edges have no child.
3. **the chain**  for every non-root unit, `T_F` is EXACTLY `region_text(parent.T_F, parent.S_F[f])`
   and `T_N` exactly `region_text(parent.T_N, parent.S_N[n])`. This is what makes the whole tree a
   quotation of two documents: follow any leaf up and you reach `Proof.lean` and the NL source, with
   every step along the way an offset rather than a transcription. It is also the check that replaces
   `faithfulness/check_verbatim.py` and `check_citations.py` wholesale — there is no `C_F` to cite, no
   signature to mis-quote and no line number to get off by one.
4. **the roots**  the root's `T_F` is `Proof.lean` byte for byte, and its `T_N` is the item's
   `nl_statement.txt` + blank line + `nl_proof.txt`.
5. **coverage**  every significant character of every target is in some region, and every region is
   in some edge. Comments and whitespace on the formal side are exempt (`model.significant`).
6. **the tree**  edges that name a child have one, children are named by an edge, and nothing else
   is on disk under a unit.
7. **no formal context**  a unit directory holds exactly the seven files of the model. A `C_F.json`
   appearing here would mean the thing this prototype removed had grown back.
8. **derived placement**  `model.ancestry` locates a unit's target inside every ancestor by arithmetic
   on the chain; re-slicing each ancestor at those offsets must give the unit's own target back. The
   UI shows this as "where am I", and nothing about it is authored.
9. **`C_N`**  `C_N` is parallel to `S_N`, so every NL region an edge judges cites the prose it must be
   read against — at every level, the root included. Every citation is in-bounds spans into the root's
   `T_N` with a reason, and no citation overlaps where its own region sits in the paper, because text
   being claimed is not context for itself. `model.regions_in_paper` supplies the "where", by the same
   arithmetic as check 8. See `model.cn_errors`.

    python3 kpistis/check.py                # gate the tree
    python3 kpistis/check.py --lean         # also elaborate Proof.lean (slow; needs lake)
    python3 kpistis/check.py --mutate       # validate the gate itself against broken copies

`--mutate` is the answer to "who checks the checker". The gate is re-run against scratch copies of
the tree with one thing wrong in each — a target retyped instead of sliced, a span slid by one, an
edge pointing at a region that does not exist, a verdict with no reason, a dropped region, a
hand-written `C_F.json`, a `C_N` citation that quietly cites the sentence it is supposed to be
context *for* — and each mutation must make it FAIL. A gate that has never been seen to fail is not
evidence of anything.
"""
from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import model
from model import CORPUS, ROOT

EXPECTED_FILES = {"unit.json", "T_F.lean", "T_N.tex", "C_N.json",
                  "S_F.json", "S_N.json", "edges.json"}


def gate(item: str, *, units_root: Path | None = None) -> list[str]:
    base = units_root or (ROOT / "units")
    errs: list[str] = []

    def load(path):
        d = base / item / path
        unit = {**json.loads((d / "unit.json").read_text(encoding="utf-8")),
                "item": item, "path": path,
                "T_F": (d / "T_F.lean").read_text(encoding="utf-8"),
                "T_N": (d / "T_N.tex").read_text(encoding="utf-8"),
                **{k: json.loads((d / f).read_text(encoding="utf-8"))
                   for k, f in model.FILES.items()}}
        unit["children"] = sorted(p.parent.name for p in d.glob("*/unit.json"))
        return unit

    # 4 — the roots
    root = load("root")
    src = (ROOT / "items" / item / "Proof.lean").read_text(encoding="utf-8")
    if root["T_F"] != src:
        errs.append("root: T_F is not Proof.lean verbatim")
    data = CORPUS / "items" / item / "data"
    halves = [(data / f"{name}.txt").read_text(encoding="utf-8", newline="")
              for name in ("nl_statement", "nl_proof")]
    if root["T_N"] != "\n\n".join(halves):
        errs.append("root: T_N is not nl_statement.txt + blank line + nl_proof.txt")
    try:
        model.markers(src)
    except ValueError as err:
        errs.append(f"root: Proof.lean markers: {err}")

    def visit(unit):
        at = unit["path"]
        d = base / item / at

        # 7 — nothing but the model on disk
        extra = {p.name for p in d.iterdir() if p.is_file()} - EXPECTED_FILES
        if extra:
            errs.append(f"{at}: unexpected file(s) {sorted(extra)}; the model is {sorted(EXPECTED_FILES)}")

        # 1 — spans
        for kind, target in (("S_F", "T_F"), ("S_N", "T_N")):
            for i, spans in enumerate(unit[kind]):
                try:
                    for a, b in model.normalize(spans):
                        model.u16cut(unit[target], a, b)
                except ValueError as err:
                    errs.append(f"{at}: {kind}[{i}]: {err}")

        # 2 — edges
        errs.extend(f"{at}: {e}" for e in model.edge_errors(unit))

        # 5 — coverage, and no region left out of the matching.
        # Guarded: check 1 above has already reported any span that cannot be sliced, and a gate that
        # raises on the first broken file stops reporting the rest of them.
        for side, kind, target in (("F", "S_F", "T_F"), ("N", "S_N", "T_N")):
            try:
                cov = model.coverage(unit[target], unit[kind], "lean" if side == "F" else "nl")
            except ValueError as err:
                errs.append(f"{at}: T_{side} coverage cannot be computed: {err}")
                continue
            if not cov["complete"]:
                missed = ", ".join(repr(model.u16cut(unit[target], a, b)) for a, b in cov["gaps"])
                errs.append(f"{at}: T_{side} has uncovered text: {missed}")
        loose = model.unlinked(unit)
        for kind, idxs in loose.items():
            for i in idxs:
                errs.append(f"{at}: {kind}[{i}] is in no edge")

        # 6 — the tree, and 3 — the chain
        named = {e["child"] for e in unit["edges"] if e.get("child")}
        for extra_child in set(unit["children"]) - named:
            errs.append(f"{at}: child {extra_child!r} is not named by any edge")
        for missing in named - set(unit["children"]):
            errs.append(f"{at}: edge names child {missing!r}, which does not exist")
        for e in unit["edges"]:
            name = e.get("child")
            if not name or name not in unit["children"]:
                continue
            child = load(f"{at}/{name}")
            for side, kind, target in (("F", "S_F", "T_F"), ("N", "S_N", "T_N")):
                idx = e["f" if side == "F" else "n"]
                if not (type(idx) is int and 0 <= idx < len(unit[kind])):
                    continue                              # already reported by check 2
                try:
                    want = model.region_text(unit[target], unit[kind][idx])
                except ValueError as err:
                    errs.append(f"{at}/{name}: parent region {kind}[{idx}] cannot be sliced: {err}")
                    continue
                if child[target] != want:
                    errs.append(f"{at}/{name}: T_{side} is not its parent's region "
                                f"{kind}[{e['f' if side == 'F' else 'n']}]\n"
                                f"      parent says {want!r}\n      child  says {child[target]!r}")
            prov = child.get("provenance", {})
            if prov.get("parent") != at or prov.get("f") != e["f"] or prov.get("n") != e["n"]:
                errs.append(f"{at}/{name}: provenance does not say which edge it refines")
            visit(child)

        # 8 — the derived placement. `model.ancestry` puts this unit's target inside EVERY ancestor
        # by composing `lift` up the chain, and the UI shows the result as "where am I". If that
        # arithmetic were wrong the answer would point at the wrong characters while looking
        # perfectly plausible, so re-slice each ancestor and demand the unit's own target back.
        #
        # 9 — `C_N`, which needs the same arithmetic: the "no overlap" rule is about where this unit
        # sits in the paper, and that is `ancestry`'s first frame.
        if at != "root":
            try:
                for fr in model.ancestry(item, at, base=base):
                    for side, target in (("F", "T_F"), ("N", "T_N")):
                        got = model.region_text(fr[target], fr[side])
                        if got != unit[target]:
                            errs.append(f"{at}: placement in {fr['path']} re-slices to {got!r}, "
                                        f"not to its own T_{side}")
            except (ValueError, KeyError, IndexError) as err:
                errs.append(f"{at}: placement cannot be derived: {err}")
        try:
            mine = model.regions_in_paper(item, at, base=base)
        except (ValueError, KeyError, IndexError) as err:
            errs.append(f"{at}: NL regions cannot be located in the paper: {err}")
            mine = None
        errs.extend(f"{at}: {e}" for e in model.cn_errors(unit, root["T_N"], mine))

    visit(root)
    return errs


# --------------------------------------------------------------------------- mutation self-test

def _mutations():
    """(name, apply) pairs, where `apply` is handed the scratch item directory.

    Each must make `gate` fail. See the module docstring: a gate nobody has watched fail is not
    evidence."""

    def retype_target(u):
        p = u / "root/1.2/T_F.lean"
        p.write_text(p.read_text(encoding="utf-8").replace("hsupp", "hsup"), encoding="utf-8")

    def slide_span(u):
        p = u / "root/1.2/S_F.json"
        spans = json.loads(p.read_text())
        spans[1][0][0] += 1
        p.write_text(json.dumps(spans))

    def dangling_edge(u):
        p = u / "root/edges.json"
        edges = json.loads(p.read_text())
        edges[0]["f"] = 999
        p.write_text(json.dumps(edges))

    def verdict_without_reason(u):
        p = u / "root/1.4/edges.json"
        edges = json.loads(p.read_text())
        edges[0]["why"] = ""
        p.write_text(json.dumps(edges))

    def drop_region(u):
        for name in ("S_N.json", "edges.json"):
            p = u / "root/1.6" / name
            data = json.loads(p.read_text())
            p.write_text(json.dumps(data[:-1] if name == "S_N.json" else
                                    [e for e in data if e.get("n") != len(data)]))

    def uncovered_text(u):
        p = u / "root/1.8/S_F.json"
        spans = json.loads(p.read_text())
        spans[1][0][1] -= 1
        p.write_text(json.dumps(spans))

    def formal_context_returns(u):
        (u / "root/1.2/C_F.json").write_text(json.dumps(
            {"items": [{"signature": "set Dτ : Matrix I J ℝ := D + τ • Matrix.single s j (1 : ℝ)",
                        "source": "kpistis/items/item1/Proof.lean:41"}]}))

    def _first_cited(cn):
        return next(r for r, items in enumerate(cn) if items)

    def cn_region_emptied(u):
        """A judged NL region left with no context, with the SHAPE still right. The length check is
        not what has to catch this — `cn_errors` has to notice that an edge claims Lean for prose
        nobody said what to read against."""
        p = u / "root/1.3/C_N.json"
        cn = json.loads(p.read_text())
        cn[_first_cited(cn)] = []
        p.write_text(json.dumps(cn))

    def cn_unparallel(u):
        """`C_N` that is no longer indexed like `S_N` — one entry dropped, so every region after it
        silently carries the citations of its neighbour."""
        p = u / "root/1.4/C_N.json"
        p.write_text(json.dumps(json.loads(p.read_text())[:-1]))

    def cn_without_reason(u):
        p = u / "root/1.4/C_N.json"
        cn = json.loads(p.read_text())
        cn[_first_cited(cn)][0]["why"] = ""
        p.write_text(json.dumps(cn))

    def cn_overlaps_region(u):
        """Context that cites the very prose its own region is. The rule it breaks is the argument
        this prototype is built on: text being claimed belongs in `T_N`, not in a citation beside
        it."""
        p = u / "root/1.5/C_N.json"
        cn = json.loads(p.read_text())
        r = _first_cited(cn)
        cn[r][0]["spans"] = model.regions_in_paper(u.name, "root/1.5", base=u.parent)[r]
        p.write_text(json.dumps(cn))

    def orphan_child(u):
        p = u / "root/edges.json"
        edges = json.loads(p.read_text())
        for e in edges:
            e.pop("child", None)
        p.write_text(json.dumps(edges))

    def bot_edge_with_child(u):
        p = u / "root/1.9/edges.json"
        edges = json.loads(p.read_text())
        edges[1]["child"] = "nowhere"
        p.write_text(json.dumps(edges))

    def root_target_edited(u):
        p = u / "root/T_F.lean"
        p.write_text(p.read_text(encoding="utf-8").replace("classical", "classical ", 1),
                     encoding="utf-8")

    return [
        ("a child target retyped rather than sliced", retype_target),
        ("a span slid by one character", slide_span),
        ("an edge pointing at region 999", dangling_edge),
        ("a verdict with no reason", verdict_without_reason),
        ("a region dropped, leaving its text uncovered", drop_region),
        ("a span shortened, leaving one character uncovered", uncovered_text),
        ("formal context grown back as C_F.json", formal_context_returns),
        ("a judged NL region left with no C_N", cn_region_emptied),
        ("a C_N no longer parallel to S_N", cn_unparallel),
        ("a C_N citation with no reason", cn_without_reason),
        ("a C_N citation overlapping its own region's place in the paper", cn_overlaps_region),
        ("a child directory no edge names", orphan_child),
        ("a ⊥ edge given a child", bot_edge_with_child),
        ("the root's T_F edited away from Proof.lean", root_target_edited),
    ]


def mutate(item: str) -> int:
    live = gate(item)
    if live:
        print("the tree itself does not pass; fix that before trusting the mutations")
        return 1
    bad = 0
    for name, apply in _mutations():
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            shutil.copytree(ROOT / "units" / item, tmp / item)
            apply(tmp / item)
            caught = bool(gate(item, units_root=tmp))
            print(f"[{'caught ' if caught else 'MISSED '}] {name}")
            bad += not caught
    print(f"\n{'all mutations caught' if not bad else f'{bad} mutation(s) slipped through'}")
    return 1 if bad else 0


def lean(item: str) -> int:
    path = f"kpistis/items/{item}/Proof.lean"
    print(f"$ lake env lean {path}")
    out = subprocess.run(["lake", "env", "lean", path], cwd=CORPUS,
                         capture_output=True, text=True)
    noise = [ln for ln in out.stdout.splitlines() + out.stderr.splitlines()
             if ln.strip() and "declaration uses `sorry`" not in ln]
    for ln in noise:
        print(f"  {ln}")
    ok = out.returncode == 0 and not noise
    print(f"[{'ok     ' if ok else 'FAIL   '}] Proof.lean elaborates "
          f"(`sorry` in the step bodies is expected)")
    return 0 if ok else 1


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Gate a K-Pistis tree.")
    ap.add_argument("item", nargs="?", default="item1")
    ap.add_argument("--lean", action="store_true", help="also elaborate Proof.lean")
    ap.add_argument("--mutate", action="store_true", help="validate the gate against broken copies")
    args = ap.parse_args(argv)

    if args.mutate:
        return mutate(args.item)
    errs = gate(args.item)
    for e in errs:
        print(f"  ! {e}")
    roll = model.rollup(args.item)
    nodes = []

    def count(node):
        nodes.append(node)
        for sub in node["children"].values():
            count(sub)
    count(roll)
    edges = sum(n["own"]["edges"] for n in nodes)
    print(f"[{'PASS   ' if not errs else 'FAIL   '}] {args.item}: {len(nodes)} units, "
          f"{edges} edges, rollup = {roll['label']}")
    return (lean(args.item) if args.lean else 0) or (1 if errs else 0)


if __name__ == "__main__":
    raise SystemExit(main())
