#!/usr/bin/env python3
"""Map each segment to EXACT PDF boxes from real glyph coordinates.

No SyncTeX. Geometry and boundaries both come from content we can verify:

  * PyMuPDF gives the exact rectangle of every WORD the PDF stores, in reading
    order. These coordinates are what the renderer draws with, so an overlay
    built from them is pixel-exact by construction.

  * Each leaf segment's START in that word stream is found by matching the
    segment's own first prose words (from its source line range, TeX stripped)
    against the stream, scanning forward from the previous leaf's start. This is
    content-based, monotonic, and needs no fuzzy source<->page sync.

Pipeline:
  1. compile the paper, read all word rects (reading order).
  2. for each LEAF (in document order) find its start word index by prose match.
  3. partition the word stream at those indices: each leaf owns a contiguous run
     (leaves tile the source, so this tiles the words).
  4. box(node) = per-line union of the words it owns (parent = union of its
     descendant leaves). Per-line keeps every box tight — never a page block.
  5. SELF-CHECK: words partition exactly; no two leaf boxes overlap. Abort else.

Boxes are PDF points, top-left origin (matches the PDF.js viewport).
"""
import json
import os
import re
import shutil
import subprocess
import sys

import pymupdf

HERE = os.path.dirname(os.path.abspath(__file__))
SRC_DIR = ("/u/taddmao/code/autoform/math/preprints/"
           "A-proof-of-Seymours-second-neighborhood-conjecture-"
           "September-23-2026/build/source")
BUILD = "/tmp/seymour_build"
PDF = os.path.join(BUILD, "main.pdf")

SRC_FILES = ["main.tex", "00-introduction.tex", "01-reduction.tex",
             "02-pruning.tex", "03-incompatibility.tex",
             "04-weighted-consequences.tex", "05-directed-cycle-consequences.tex"]


# ---------------------------------------------------------------- compile
def compile_pdf():
    os.makedirs(BUILD, exist_ok=True)
    print("compiling ...")
    subprocess.run(
        ["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error",
         f"-output-directory={BUILD}", "main.tex"],
        cwd=SRC_DIR, capture_output=True, text=True)
    if not os.path.exists(PDF):
        raise SystemExit("latex compile failed")
    print("  ok:", PDF)


# ----------------------------------------------------------------- words
def load_words():
    """Every word as [page, x0, y0, x1, y1, norm_token], in reading order."""
    doc = pymupdf.open(PDF)
    out = []
    for pno in range(doc.page_count):
        for w in doc[pno].get_text("words", sort=True):
            out.append([pno + 1, w[0], w[1], w[2], w[3], norm(w[4])])
    return out


def norm(s):
    return re.sub(r"[^a-z0-9]", "", s.lower())


# --------------------------------------------------------- source prose
def strip_tex(line):
    # drop commands whose brace args are non-prose (labels, refs, env names),
    # with their contents, then remaining macros, then tex punctuation.
    line = re.sub(r"\\(label|ref|eqref|cite|input|begin|end)\s*(\[[^\]]*\])?\s*\{[^}]*\}",
                  " ", line)
    line = re.sub(r"\\[a-zA-Z]+\*?", " ", line)
    line = re.sub(r"[{}$\\&%#_^~\[\]]", " ", line)
    return [norm(t) for t in line.split() if len(norm(t)) >= 2]


def leaf_prose(node, files, n_first=10):
    """First few distinctive prose tokens of a leaf, from its source lines."""
    f, a, b = node["src"]
    lines = files[f]
    toks = []
    for L in range(a, b + 1):
        if 1 <= L <= len(lines):
            toks += strip_tex(lines[L - 1])
        if len(toks) >= n_first:
            break
    return toks[:n_first]


# ------------------------------------------------------------------ tree
def leaves_in_order(node, out):
    if not node["children"]:
        out.append(node)
    for c in node["children"]:
        leaves_in_order(c, out)


def all_nodes(node, out):
    out.append(node)
    for c in node["children"]:
        all_nodes(c, out)


def leaf_ids(n):
    if not n["children"]:
        return [n["id"]]
    out = []
    for c in n["children"]:
        out += leaf_ids(c)
    return out


# --------------------------------------------------------- match + boxes
def find_run(words, toks, lo):
    """First index >= lo where the longest prefix n-gram (n=4..1) matches."""
    for n in range(min(4, len(toks)), 0, -1):
        pat = toks[:n]
        for i in range(lo, len(words) - n + 1):
            if [words[i + d][5] for d in range(n)] == pat:
                return i
    return None


def partition_starts(words, leaves, files):
    """A strictly-increasing start index per leaf, so the word stream is cut
    into contiguous non-empty runs in document order.

    Prose n-gram match where it works (scanning forward); leaves that don't
    match (pure math / floats / run-in headings) are interpolated and then a
    strict pass guarantees start[k] > start[k-1] — no zero-width, no overlap.
    """
    N = len(leaves)
    known = [None] * N
    cursor = 0
    unmatched = []
    for k, lf in enumerate(leaves):
        i = find_run(words, leaf_prose(lf, files), cursor)
        if i is not None and i >= cursor:
            known[k] = i
            cursor = i
        else:
            unmatched.append(lf["id"])

    starts = [0] * N
    for k in range(N):
        if known[k] is None:
            prev = starts[k - 1] if k > 0 else 0
            starts[k] = prev
        else:
            starts[k] = known[k]
    # the first leaf always owns the very first word
    starts[0] = 0
    # force strictly increasing and in range
    for k in range(1, N):
        starts[k] = min(max(starts[k], starts[k - 1] + 1), len(words) - (N - k))
    return starts, unmatched


def line_key(page, y0, y1):
    return (page, round((y0 + y1) / 2 / 3.0))          # ~3pt line buckets


def compute_line_bands(words):
    """One vertical band per text line, clipped at midpoints to its vertical
    neighbors so adjacent lines NEVER overlap vertically.

    Returns {line_key: (ytop, ybot)}.
    """
    # raw extent + center per line
    raw = {}
    for (page, x0, y0, x1, y1, _t) in words:
        key = line_key(page, y0, y1)
        if key in raw:
            a0, a1 = raw[key]
            raw[key] = (min(a0, y0), max(a1, y1))
        else:
            raw[key] = (y0, y1)
    center = {k: (v[0] + v[1]) / 2 for k, v in raw.items()}

    # per page, order lines by center and clip to midpoints
    by_page = {}
    for (page, b) in raw:
        by_page.setdefault(page, []).append((page, b))
    bands = {}
    for page, keys in by_page.items():
        keys.sort(key=lambda k: center[k])
        for i, k in enumerate(keys):
            y0, y1 = raw[k]
            if i > 0:
                mid = (center[k] + center[keys[i - 1]]) / 2
                y0 = max(y0, mid)
            if i < len(keys) - 1:
                mid = (center[k] + center[keys[i + 1]]) / 2
                y1 = min(y1, mid)
            bands[k] = (y0, y1)
    return bands


def boxes_for(words, bands):
    """Box set for a group of words: per line, union x of those words, use the
    globally-clipped line band for y. Different leaves in the same line are
    side-by-side in x, so their boxes never overlap."""
    by_line = {}
    for (page, x0, y0, x1, y1, _t) in words:
        key = line_key(page, y0, y1)
        if key in by_line:
            a0, a1 = by_line[key]
            by_line[key] = (min(a0, x0), max(a1, x1))
        else:
            by_line[key] = (x0, x1)
    rects = []
    for key in sorted(by_line, key=lambda k: (k[0], bands[k][0])):
        page = key[0]
        x0, x1 = by_line[key]
        ytop, ybot = bands[key]
        rects.append({"page": page, "x": round(x0, 2), "y": round(ytop, 2),
                      "w": round(x1 - x0, 2), "h": round(ybot - ytop, 2)})
    return rects


def overlap(a, b):
    if a["page"] != b["page"]:
        return False
    return not (a["x"] + a["w"] <= b["x"] or b["x"] + b["w"] <= a["x"] or
                a["y"] + a["h"] <= b["y"] or b["y"] + b["h"] <= a["y"])


# ------------------------------------------------------------------- main
def main():
    compile_pdf()
    shutil.copyfile(PDF, os.path.join(HERE, "viz", "paper.pdf"))
    print("copied paper.pdf into viz/")

    data = json.load(open(os.path.join(HERE, "segments.json")))
    files = {f: open(os.path.join(SRC_DIR, f)).read().splitlines() for f in SRC_FILES}
    words = load_words()
    print(f"loaded {len(words)} word rects")

    leaves = []
    leaves_in_order(data["tree"], leaves)

    # strictly-increasing start index per leaf -> contiguous non-empty runs
    starts, unmatched = partition_starts(words, leaves, files)

    bounds = starts + [len(words)]
    leaf_words = {}
    for i, lf in enumerate(leaves):
        leaf_words[lf["id"]] = words[bounds[i]:bounds[i + 1]]

    # globally-clipped line bands: adjacent lines can't overlap vertically
    bands = compute_line_bands(words)

    nodes = []
    all_nodes(data["tree"], nodes)
    boxes = {}
    for n in nodes:
        ws = []
        for lid in leaf_ids(n):
            ws += leaf_words[lid]
        if ws:
            boxes[n["id"]] = boxes_for(ws, bands)

    json.dump(boxes, open(os.path.join(HERE, "boxes.json"), "w"), indent=1)

    # ---- self-checks ----
    errs = []
    total = sum(len(leaf_words[lf["id"]]) for lf in leaves)
    if total != len(words):
        errs.append(f"word partition covers {total}/{len(words)}")
    leaf_box_list = [(lf["id"], r) for lf in leaves for r in boxes.get(lf["id"], [])]
    n_over = 0
    for i in range(len(leaf_box_list)):
        for j in range(i + 1, len(leaf_box_list)):
            if leaf_box_list[i][0] != leaf_box_list[j][0] and \
               overlap(leaf_box_list[i][1], leaf_box_list[j][1]):
                n_over += 1
                if n_over <= 8:
                    errs.append(f"overlap {leaf_box_list[i][0]} <> {leaf_box_list[j][0]}")
    empty = [lf["id"] for lf in leaves if not boxes.get(lf["id"])]

    print(f"\nnodes with boxes: {len(boxes)} | leaves: {len(leaves)}")
    print(f"word partition: {total}/{len(words)}")
    print(f"prose-unmatched leaves (start interpolated): {unmatched or 'none'}")
    print(f"empty-box leaves: {empty or 'none'}")
    print(f"leaf-box overlaps: {n_over}")
    if errs:
        print("CHECK FAILED:")
        for e in errs[:12]:
            print("  ", e)
        sys.exit(1)
    print("OK: exact word partition, zero overlapping leaf boxes.")


if __name__ == "__main__":
    main()
