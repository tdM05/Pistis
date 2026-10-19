"""K-Pistis: ONE alignment primitive, applied at every level.

`doc/K_pistis.md` asks for a tree of segmentations — `C_1 = proof step`, `C_2 = faithalign label` —
and observes that there is no good reason for the number of levels to be two. This module is the
answer to that: a single node type, used unchanged at every depth.

    unit = (T_F, T_N, S_F, S_N, C_N, edges)

      T_F   the formal text this node is about          (a string)
      T_N   the natural-language text it is about       (a string)
      S_F   regions of T_F                              (lists of UTF-16 [start, end) intervals)
      S_N   regions of T_N
      C_N   per NL region, the prose you must read      (parallel to S_N; each citation is spans into
            THAT REGION against                          the ROOT's T_N — the paper — with a reason)
      edges a matching between them, each edge carrying a verdict and a reason

`C_N` is indexed like `S_N` and not like the unit, which matters: an edge is the thing being judged,
an edge names an NL region, so every edge has its context — at every level, the root included.

A node is REFINED by picking one of its edges and making a child unit out of it:

      child.T_F == the text of that edge's S_F region        (byte for byte)
      child.T_N == the text of that edge's S_N region         (byte for byte)

and the child is a unit, so it has its own `S_F`, `S_N`, `edges`, and its own children. The root's
`T_F` is a whole Lean file and its `T_N` is a whole lemma + proof; its regions are proof steps; a
step's regions are the atomic pieces `faithalign` labels. Nothing in the code knows which level it is
looking at, which is the entire point: `check.py`, `ui/` and the rollup below all recurse.

What is NOT here, and why
-------------------------
**No formal context (`C_F`).** Upstream a datapoint is (target, context): the claim, plus the
`obtain`/`set`/`variable` clauses you must read it against. That split is what forces
`items/item1/Main.lean` to put `D_τ = D + τ e_s e_jᵀ` on the NL side with nothing on the formal side
to link it to — the defining `set` is context, not target. Here a region's text IS its formal side,
so the `set` is simply part of region 1.2 and the prose that defines `D_τ` links straight to it.

The general claim, and the reason this is a *simplification* rather than a restriction: **anything
that would be formal context can instead be part of the target.** If a piece of `T_N` corresponds to
a clause in the ambient proof, enlarge `T_F` to include that clause — it is text in the same file,
immediately above. So the context-free form always exists, and it is strictly more faithful, because
a context item is a *quotation with a citation* (it can be mis-cited, re-ordered or paraphrased —
see `faithfulness/README.md`, *Is it a quote?*, for the four shapes that had to be banned) whereas a
target span cannot be any of those things: it is an offset into the text it is a span of.

**But there IS natural-language context (`C_N`), and every region an edge judges has some.** The
symmetry does not hold, and pretending it did was the mistake. On the formal side you can always rewrite
`Proof.lean` so the clause you need is adjacent and then widen the target to include it — the file is
yours. The paper is not. "For a nonzero real τ, the matrix $D_\\tau=\\dots$ is still supported on $T$"
cannot be read without the definition of *supported on $T$*, which is thirteen lines earlier in a
different paragraph; widening `T_N` until it reaches that far would make the target the whole
document, which is the root, which is where we started. So `C_N` exists.

What `C_N` is NOT is a quotation. See `cn_errors` below: a citation is **a set of spans into the
root's `T_N`** — the paper, the one fixed address space for natural language — plus a reason for
citing it. So it is *authored* (which sentences matter is a judgment, and a judgment should be
someone's) but not *transcribed*: there is no string to mis-copy, nothing to paraphrase, and no line
number to get off by one. The rule from above survives as a check rather than as an absence: a
citation for region `i` may not overlap where region `i` sits in the paper, because text that is part
of what is being claimed belongs in the region.

And it hangs off the region rather than the unit so that there is no level at which it is missing.
Per-unit was the first attempt and it had a hole in the worst place: the root's target is the whole
paper, so the root can have no context, so the view you open the tool on would show none at all.

There is still **no `C_F`** and **no implicit-assumption list (`I`)**; `check.py` fails if a
`C_F.json` appears. And there is `ancestry` below, which is a different thing again — derived, not
authored: where this unit's target sits inside its parent, inside `Proof.lean` and inside the paper,
by arithmetic (`lift`) on files that are checked anyway. Prose with no formal counterpart is still an
edge to ⊥, which is a judgment the labeler makes in the open.

**No separate `R` / `lambda`.** Upstream keeps "which regions correspond" apart from "does the
correspondence hold", because they are seeded and judged by different parties. One file here: an
edge is a record with a verdict on it.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CORPUS = ROOT.parent

BOT = None                                  # ⊥: this region corresponds to nothing on the other side
MARKER = re.compile(r"^[ \t]*--\|[ \t]*(\S+)[ \t]*$")


# ---------------------------------------------------------------- UTF-16 offsets
# Spans are UTF-16 code-unit offsets, as upstream, so that a browser's `selectionStart` and Python's
# stored intervals mean the same thing in `Dτ`, `⟨τ, hτ⟩` and `ℝ`.

def u16len(text: str) -> int:
    return len(text.encode("utf-16-le")) // 2


def u16cut(text: str, start: int, end: int) -> str:
    raw = text.encode("utf-16-le")
    if not 0 <= start <= end <= len(raw) // 2:
        raise ValueError(f"span [{start}, {end}) out of bounds for UTF-16 length {len(raw) // 2}")
    try:
        return raw[2 * start:2 * end].decode("utf-16-le")
    except UnicodeDecodeError as err:
        raise ValueError(f"span [{start}, {end}) splits a surrogate pair") from err


def u16at(text: str, py_index: int) -> int:
    """The UTF-16 offset of a Python character index."""
    return u16len(text[:py_index])


def find_span(haystack: str, needle: str, *, start: int = 0, occurrence: int = 0) -> list[int]:
    """`[a, b)` in UTF-16 units for `needle` inside `haystack` — the ADDRESS OF A STRING.

    Every authored span is written this way (see `annotate_item1.py`): a region is named by the text
    it covers and the offsets are computed, so re-indenting `Proof.lean` or re-wrapping the `.tex`
    makes the annotation fail loudly here instead of silently sliding onto the wrong characters.
    """
    found, at = -1, start
    for _ in range(occurrence + 1):
        found = haystack.find(needle, at)
        if found < 0:
            raise ValueError(f"needle not found: {needle!r}")
        at = found + 1
    return [u16at(haystack, found), u16at(haystack, found + len(needle))]


# ---------------------------------------------------------------- regions

JOIN = " … "          # how the pieces of a non-contiguous region read as one string


def region_text(target: str, spans: list[list[int]], join: str = JOIN) -> str:
    return join.join(u16cut(target, a, b) for a, b in spans)


def lift(spans, parent_spans, join: str = JOIN) -> list[list[int]]:
    """Intervals in a region's TEXT, mapped back to intervals in the text that region is OF.

    `region_text` reads a region's pieces out in the order they are stored, separated by `join`, and
    that string is a child unit's target. This is the inverse: given offsets into the child's target,
    where are those characters in the parent? Characters of the separator map nowhere and are dropped,
    which is right — they are not in the parent.

    Composable, and that is the point: applied up the chain it says where a leaf's target sits inside
    `Proof.lean` and inside the paper, with no step that is anything but arithmetic.
    """
    pieces, pos = [], 0
    for a, b in parent_spans:
        if pieces:
            pos += u16len(join)
        pieces.append((pos, pos + (b - a), a))
        pos += b - a
    out = []
    for s, e in normalize(spans):
        for lo, hi, at in pieces:
            x, y = max(s, lo), min(e, hi)
            if x < y:
                out.append([at + (x - lo), at + (y - lo)])
    return [[a, b] for a, b in normalize(out)] if out else []


def ancestry(item: str, path: str, base: Path | None = None) -> list[dict]:
    """Every ancestor of `path`, root first, each with the span THIS unit occupies inside it.

    Not context — *placement*. The two are different things and this model keeps them apart by name:
    `C_N` is authored (what you must read this against, with a reason), this is derived (where the
    text physically is). The chain already proves a unit's target is exactly a slice of its parent's,
    so the surrounding text and the offset of the slice inside it are both *computed* from files that
    are checked anyway. Nothing is stored, nothing can disagree, and so there is no reason not to
    always have it.

    The root has no entry of its own: its target is the whole document, so there is nothing outside it.
    """
    parts = path.split("/")
    units = [load(item, "/".join(parts[:k + 1]), base) for k in range(len(parts))]
    leaf = units[-1]
    at = {"S_F": [[0, u16len(leaf["T_F"])]], "S_N": [[0, u16len(leaf["T_N"])]]}
    out = []
    for i in range(len(units) - 2, -1, -1):
        parent, child = units[i], units[i + 1]
        prov = child.get("provenance", {})
        if prov.get("parent") != parent["path"] or prov.get("f") is None or prov.get("n") is None:
            raise ValueError(f"{child['path']}: provenance does not name a region of {parent['path']}")
        at = {"S_F": lift(at["S_F"], parent["S_F"][prov["f"]]),
              "S_N": lift(at["S_N"], parent["S_N"][prov["n"]])}
        out.append({"path": parent["path"], "loc": parent.get("loc", parent["path"]),
                    "title": parent.get("title", ""),
                    "T_F": parent["T_F"], "T_N": parent["T_N"],
                    "F": at["S_F"], "N": at["S_N"]})
    out.reverse()
    return out


def regions_in_paper(item: str, path: str, base: Path | None = None) -> list[list[list[int]]]:
    """Where each of a unit's NL regions sits in the paper — one span list per region.

    `ancestry` lifts the unit's whole target up the chain; this lifts each region of it. Exactly what
    `cn_errors` rule 5 needs, because the no-overlap rule is per region: `C_N[i]` must not cite the
    text of region `i`. Pure arithmetic, same `lift`, no new authored anything. The root is the paper,
    so there the answer is the regions themselves.
    """
    parts = path.split("/")
    units = [load(item, "/".join(parts[:k + 1]), base) for k in range(len(parts))]
    out = [[[a, b] for a, b in normalize(spans)] for spans in units[-1]["S_N"]]
    for i in range(len(units) - 2, -1, -1):
        up = units[i]["S_N"][units[i + 1]["provenance"]["n"]]
        out = [lift(spans, up) for spans in out]
    return out


def normalize(spans) -> tuple[tuple[int, int], ...]:
    """Canonical identity of a region: sorted, merged, order- and partition-independent."""
    if not isinstance(spans, list) or not spans:
        raise ValueError("a region must be a non-empty list of intervals")
    for iv in spans:
        if (not isinstance(iv, list) or len(iv) != 2
                or any(type(x) is not int for x in iv) or not 0 <= iv[0] < iv[1]):
            raise ValueError(f"expected a nonempty [start, end) interval, got {iv!r}")
    out: list[list[int]] = []
    for a, b in sorted(spans):
        if out and a <= out[-1][1]:
            out[-1][1] = max(out[-1][1], b)
        else:
            out.append([a, b])
    return tuple((a, b) for a, b in out)


# ---------------------------------------------------------------- coverage
# Coverage is over the SIGNIFICANT characters of a target, not all of them. On the NL side that means
# every non-space character. On the formal side comments are dropped too: a comment is not something
# the formalization asserts, so demanding an NL counterpart for one would make every explanatory note
# in the file either a lie or a ⊥ edge. `--|` markers are comments, so this also exempts them.

def significant(text: str, kind: str) -> list[bool]:
    mask = [not ch.isspace() for ch in text]
    if kind != "lean":
        return mask
    i, n, depth = 0, len(text), 0
    while i < n:
        two = text[i:i + 2]
        if depth:
            if two == "/-":
                depth += 1
                mask[i] = mask[i + 1] = False
                i += 2
                continue
            if two == "-/":
                depth -= 1
                mask[i] = mask[i + 1] = False
                i += 2
                continue
            mask[i] = False
            i += 1
            continue
        if two == "/-":
            depth = 1
            mask[i] = mask[i + 1] = False
            i += 2
            continue
        if two == "--":
            while i < n and text[i] != "\n":
                mask[i] = False
                i += 1
            continue
        if text[i] == '"':                                  # a string literal IS content
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
            continue
        i += 1
    return mask


def coverage(target: str, regions, kind: str) -> dict:
    """What fraction of the target's significant characters some region covers, and what is missed.

    Reported, not enforced. `doc/Pistis_orders.md` is the argument: First-Order Pistis gets coverage
    for free from a strict tiling rule, and the price of spans that may overlap, skip and re-order is
    that coverage becomes something an oracle has to decide about. So it is a NUMBER on the screen
    next to the gaps it is made of, which is what a human needs in order to decide.
    """
    mask = significant(target, kind)
    hit = [False] * len(target)
    for spans in regions:
        for a, b in normalize(spans):
            lo, hi = len(u16cut(target, 0, a)), len(u16cut(target, 0, b))
            for i in range(lo, hi):
                hit[i] = True
    total = sum(mask)
    covered = sum(1 for i, m in enumerate(mask) if m and hit[i])
    gaps, run = [], None
    for i, m in enumerate(mask):
        if m and not hit[i]:
            run = i if run is None else run
        elif run is not None:
            gaps.append([u16at(target, run), u16at(target, i)])
            run = None
    if run is not None:
        gaps.append([u16at(target, run), u16at(target, len(target))])
    return {"covered": covered, "total": total, "complete": covered == total, "gaps": gaps}


# ---------------------------------------------------------------- edges

def edge_errors(unit: dict) -> list[str]:
    out = []
    nf, nn = len(unit["S_F"]), len(unit["S_N"])
    for i, e in enumerate(unit["edges"]):
        if set(e) - {"f", "n", "v", "why", "child"}:
            out.append(f"edges[{i}]: unknown keys {sorted(set(e) - {'f', 'n', 'v', 'why', 'child'})}")
        f, n = e.get("f", BOT), e.get("n", BOT)
        if f is BOT and n is BOT:
            out.append(f"edges[{i}]: ⊥ ↦ ⊥ is not an edge")
        for name, idx, size in (("f", f, nf), ("n", n, nn)):
            if idx is not BOT and not (type(idx) is int and 0 <= idx < size):
                out.append(f"edges[{i}]: {name}={idx!r} is not a region index (0..{size - 1})")
        # `v: null` is UNJUDGED, and it is the state a seeded edge starts in. Seeding the matching is
        # fair game — the markers in `Proof.lean` are the formalizer's own claim about which step
        # answers which sentence, and that claim is part of what is being checked. Seeding the
        # VERDICT would be the tool grading its own homework, so a null stays null until a human
        # writes a reason next to it, and `status` reports the node `NaN` until they all do.
        if e.get("v") not in (0, 1, None):
            out.append(f"edges[{i}]: verdict must be 0, 1 or null, got {e.get('v')!r}")
        if e.get("v") is not None and not str(e.get("why", "")).strip():
            out.append(f"edges[{i}]: a judged edge needs a reason")
        if e.get("child") and (f is BOT or n is BOT):
            out.append(f"edges[{i}]: a ⊥ edge has nothing to refine, so it cannot have a child")
    return out


# ---------------------------------------------------------------- natural-language context

def cn_text(root_tn: str, item: dict) -> str:
    """A context item's text — SLICED from the paper, never stored."""
    return region_text(root_tn, item["spans"])


def judged_n(unit: dict) -> set[int]:
    """NL regions that some edge claims a formal counterpart for.

    These are the ones that need context: an edge says "this prose and that Lean say the same thing",
    and you cannot check that without whatever the prose depends on. A region only ever on the ⊥ side
    ("Moreover,", the `\\[…\\]` delimiters) is being claimed to mean nothing formal, so there is
    nothing to read it against.
    """
    return {e["n"] for e in unit.get("edges", [])
            if e.get("n") is not BOT and e.get("f") is not BOT}


def cn_errors(unit: dict, root_tn: str, own: list[list[list[int]]] | None = None) -> list[str]:
    """What makes a `C_N` legitimate rather than a quotation.

    `C_N` is **parallel to `S_N`**: `C_N[i]` is the prose you must read region `i` against. It is
    per-region and not per-unit, and that is the second correction this prototype needed. Per-unit
    context has a hole exactly where the tool is first used: the root's target is the whole paper, so
    it can have no context, so the view you land on — thirteen edges, every one of them a claim about
    a sentence that has dependencies — would show none. Attach context to the region being claimed
    and there is no hole: every edge with an NL side has a `C_N`, at every level, root included.

    It also puts the citations where the chain can keep them honest. `child.T_N` IS
    `region_text(parent.T_N, parent.S_N[n])`, so `C_N[n]` in the parent is context for exactly the
    text the child is about — one authored list, correct in both views, with nothing to keep in sync.

    Five rules, and the fifth is the one that carries the argument from the module docstring:

    1. **shape.** `C_N` is a list as long as `S_N`; `C_N[i]` is a list of `{spans, why}`.
    2. **every judged region has context.** If an edge claims this prose means that Lean, say what
       the prose needs. A labeler who thinks a region is self-contained is still making a judgment
       and can make it with one item. Regions only on the ⊥ side are exempt (see `judged_n`).
    3. **a citation is spans into the root's `T_N`**, in bounds, nonempty. The paper is the one fixed
       address space for natural language, so a citation is an offset — there is no transcribed
       string, which is the whole difference between this and upstream's `C_F`/`C_N`.
    4. **every citation has a reason.** "Here is some nearby prose" is not context; "you cannot read
       'supported on $T$' without this" is. Same rule as a verdict: no reason, no claim.
    5. **context may not overlap its own region.** If a cited span is inside where region `i` sits in
       the paper then it is not context for region `i`, it is the thing being claimed, and it belongs
       in the region. This is the "anything that would be context can be part of the target" argument
       surviving as a *check* on the side where widening the target does not always work.

    `own[i]` is region `i`'s place in the paper, which only a caller holding the chain can work out
    (`ancestry` from disk, `BUILT` mid-annotation); pass `None` to skip rule 5.
    """
    out: list[str] = []
    cn = unit.get("C_N", [])
    if not isinstance(cn, list):
        return ["C_N must be a list, one entry per S_N region"]
    if len(cn) != len(unit.get("S_N", [])):
        return [f"C_N has {len(cn)} entries for {len(unit.get('S_N', []))} NL regions — "
                f"it is parallel to S_N, one list of citations per region"]
    need = judged_n(unit)
    locs = unit.get("N_locs", [])

    for r, items in enumerate(cn):
        at = f"C_N[{r}]" + (f" ({locs[r]!r})" if r < len(locs) else "")
        if not isinstance(items, list):
            out.append(f"{at}: must be a list of {{spans, why}}")
            continue
        if not items and r in need:
            out.append(f"{at}: no context, but an edge claims this prose corresponds to Lean — "
                       f"say what it has to be read against (one item with a reason is a legitimate "
                       f"answer)")
        mine = normalize(own[r]) if own and r < len(own) else ()
        for i, c in enumerate(items):
            if not isinstance(c, dict) or set(c) - {"spans", "why"}:
                out.append(f"{at}[{i}]: a citation is {{spans, why}}, got {c!r}")
                continue
            try:
                spans = normalize(c.get("spans"))
                for a, b in spans:
                    u16cut(root_tn, a, b)
            except ValueError as err:
                out.append(f"{at}[{i}]: {err}")
                continue
            if not str(c.get("why", "")).strip():
                out.append(f"{at}[{i}]: a citation needs a reason — what it is here for")
            for a, b in spans:
                for x, y in mine:
                    if a < y and x < b:
                        out.append(f"{at}[{i}]: [{a}, {b}) overlaps this region's own place in the "
                                   f"paper [{x}, {y}) — text being claimed is not context for "
                                   f"itself; it belongs in the region")
    return out


def inversions(edges: list[dict], unit: dict | None = None) -> list[tuple[int, int]]:
    """Pairs of edges that cross: formal order and NL order disagree.

    Ordered by where the regions START IN THE TEXT, not by their index in `S_F` — an index is just the
    order someone drew the regions in, and judging order off it would make a crossing appear or vanish
    when the annotation is rewritten.

    Not an error. `doc/Pistis_orders.md` is the reason it is computed at all: order comes free in
    First-Order Pistis, where a strict tiling rule enforces it, and has to be *decided* once spans may
    overlap, skip and re-order. So the crossings are drawn and the reader judges them.
    """
    def key(kind, idx):
        if unit is None:
            return idx
        return normalize(unit[kind][idx])[0][0]

    linked = [(i, key("S_F", e["f"]), key("S_N", e["n"])) for i, e in enumerate(edges)
              if e.get("f") is not BOT and e.get("n") is not BOT]
    return [(a[0], b[0]) for ai, a in enumerate(linked) for b in linked[ai + 1:]
            if (a[1] - b[1]) * (a[2] - b[2]) < 0]


def unlinked(unit: dict) -> dict:
    """Regions no edge mentions — a region drawn and then forgotten, not a judgment."""
    used_f = {e["f"] for e in unit["edges"] if e.get("f") is not BOT}
    used_n = {e["n"] for e in unit["edges"] if e.get("n") is not BOT}
    return {"S_F": [i for i in range(len(unit["S_F"])) if i not in used_f],
            "S_N": [i for i in range(len(unit["S_N"])) if i not in used_n]}


# ---------------------------------------------------------------- unit IO
# A unit is a directory. A subdirectory holding `unit.json` is a CHILD unit, so the tree on disk is
# the tree in the model and `ls -R` is a readable picture of it.

FILES = {"C_N": "C_N.json", "S_F": "S_F.json", "S_N": "S_N.json", "edges": "edges.json"}


def unit_dir(item: str, path: str, base: Path | None = None) -> Path:
    return (base or (ROOT / "units")) / item / path


def load(item: str, path: str, base: Path | None = None) -> dict:
    """`base` reads a tree somewhere other than `units/` — `check.py --mutate` gates scratch copies."""
    d = unit_dir(item, path, base)
    meta = json.loads((d / "unit.json").read_text(encoding="utf-8"))
    unit = {
        **meta,
        "item": item, "path": path,
        "T_F": (d / "T_F.lean").read_text(encoding="utf-8"),
        "T_N": (d / "T_N.tex").read_text(encoding="utf-8"),
        **{k: json.loads((d / f).read_text(encoding="utf-8")) for k, f in FILES.items()},
    }
    unit["children"] = sorted(p.parent.name for p in d.glob("*/unit.json"))
    return unit


def save(unit: dict) -> None:
    d = unit_dir(unit["item"], unit["path"])
    d.mkdir(parents=True, exist_ok=True)
    # `F_locs` / `N_locs` are display NAMES for the regions (`1.2`, `thm`), not part of the model —
    # a region's identity is its span. They ride along so the UI can say which region it means.
    meta = {k: unit[k] for k in ("id", "loc", "title", "category", "child_category",
                                 "provenance", "F_locs", "N_locs", "done") if k in unit}
    (d / "unit.json").write_text(json.dumps(meta, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    (d / "T_F.lean").write_text(unit["T_F"], encoding="utf-8")
    (d / "T_N.tex").write_text(unit["T_N"], encoding="utf-8")
    for key, name in FILES.items():
        (d / name).write_text(json.dumps(unit[key], ensure_ascii=False, indent=2) + "\n",
                              encoding="utf-8")


def walk(item: str, path: str = "root"):
    """Every unit in the tree, parents before children."""
    unit = load(item, path)
    yield unit
    for child in unit["children"]:
        yield from walk(item, f"{path}/{child}")


# ---------------------------------------------------------------- status

def status(unit: dict) -> dict:
    """One node's own standing. `rollup` is this plus the children's.

    `C_N` is deliberately not judged here: checking it needs the root's `T_N` and this unit's place
    in it, i.e. two other files, and `status` is a pure function of one unit. `cn_errors` is the
    gate's job (`check.py`, check 9).
    """
    errs = edge_errors(unit)
    cov_f = coverage(unit["T_F"], unit["S_F"], "lean")
    cov_n = coverage(unit["T_N"], unit["S_N"], "nl")
    loose = unlinked(unit)
    bad = [i for i, e in enumerate(unit["edges"]) if e.get("v") == 0]
    open_ = [i for i, e in enumerate(unit["edges"]) if e.get("v") is None]
    return {
        "errors": errs,
        "coverage": {"F": cov_f, "N": cov_n},
        "unlinked": loose,
        "bad_edges": bad,
        "open_edges": open_,
        "inversions": inversions(unit["edges"], unit),
        "edges": len(unit["edges"]),
        "bot": sum(1 for e in unit["edges"] if e.get("f") is BOT or e.get("n") is BOT),
        "own_label": ("broken" if errs else
                      "unfaithful" if bad else
                      "NaN" if open_ or not unit["edges"] else
                      "unfaithful" if not cov_f["complete"] or not cov_n["complete"]
                      or loose["S_F"] or loose["S_N"] else "faithful"),
        "done": bool(unit.get("done")),
    }


def rollup(item: str, path: str = "root") -> dict:
    """A node's label and its subtree's, bottom-up.

    The whole document is faithful when every node is: every region of every target is covered, every
    region is in an edge, and every edge holds. One rule at every level — the reason the levels are
    the same object.
    """
    unit = load(item, path)
    st = status(unit)
    kids = {c: rollup(item, f"{path}/{c}") for c in unit["children"]}
    worst = st["own_label"]
    order = ["faithful", "NaN", "unfaithful", "broken"]
    for sub in kids.values():
        worst = max(worst, sub["label"], key=order.index)
    return {"path": path, "loc": unit.get("loc", path), "title": unit.get("title", ""),
            "own": st, "label": worst, "children": kids}


# ---------------------------------------------------------------- marker parsing

def markers(src: str) -> list[dict]:
    """The `--| <loc>` regions of a Lean file, as `{loc, span, line}` in source order.

    A region runs from the line after its marker to the line before the next marker (or EOF), trimmed
    to its first and last non-whitespace character. Text before the first marker must be comment
    only — it is the file's own explanation of itself, and leaving real code out there would silently
    exempt it from coverage.
    """
    lines = src.split("\n")
    starts = [(i, m.group(1)) for i, ln in enumerate(lines) if (m := MARKER.match(ln))]
    if not starts:
        raise ValueError("no `--| <loc>` markers in the file")
    offset = [0]
    for ln in lines:
        offset.append(offset[-1] + len(ln) + 1)
    head = src[:offset[starts[0][0]]]
    if any(significant(head, "lean")):
        raise ValueError("code above the first `--|` marker would be exempt from coverage")
    out = []
    for k, (line, loc) in enumerate(starts):
        lo = offset[line + 1]
        hi = offset[starts[k + 1][0]] if k + 1 < len(starts) else len(src)
        body = src[lo:hi]
        text = body.rstrip()
        pad = len(text) - len(text.lstrip())
        if not text.strip():
            raise ValueError(f"marker {loc!r} opens an empty region")
        out.append({"loc": loc, "line": line + 1,
                    "span": [u16at(src, lo + pad), u16at(src, lo + len(text))]})
    seen = [m["loc"] for m in out]
    if len(set(seen)) != len(seen):
        raise ValueError(f"duplicate marker locs: {seen}")
    return out
