# NL segmentation — data model

## What we are capturing
A **tree** that makes the paper's *implicit* structure *explicit*, plus a set of
**cross-edges** that connect the high-level description of an idea to the place
where it is actually done.

Two orthogonal things are recorded for every node:

1. **Where it sits in the document** — the containment tree
   (paper → section → theorem/lemma/proof → proof-step → …). This is the outline
   you'd get from a very careful table of contents.

2. **What role it plays** — `level`:
   - `high`  — overview / signpost text that *points at* the real work elsewhere
     (abstract, "Proof strategy", the two-sentence previews before a lemma).
   - `statement` — a claim: a definition, theorem, lemma, proposition, corollary,
     remark, or a displayed equation that later text refers to by number.
   - `proof` — a container holding the steps that discharge a statement.
   - `step` — one low-level move inside a proof.
   - `meta` — front/back matter (references, bibliographic prose).

The `level` split is the point of the exercise: it separates *what is high-level
and really points to other things* from *what is the actual proof*. The viz
colours by `level` so you can see, at a glance, the signposts vs. the machinery.

## Node schema
```jsonc
{
  "id": "lem:pruning",          // stable, unique; cross-edges reference these
  "kind": "lemma",              // section|subsection|abstract|definition|notation|
                                //   theorem|lemma|proposition|corollary|remark|
                                //   note|proof|proof-part|step|equation|figure|references
  "label": "Lemma 3.1 (Pruning)",
  "level": "statement",         // high | statement | proof | step | meta
  "text": "verbatim-or-faithful text, with $…$ / $$…$$ math for KaTeX",
  "src": ["02-pruning.tex", 10, 40],   // file + line range in the LaTeX source
  "tags": ["binary-relation", "key-lemma"],
  "children": [ …nodes… ]
}
```
`text` is verbatim for statements, definitions and displayed equations. For
proof `step`s it is a faithful one- or two-sentence rendering of that move; the
`src` range always points at the exact lines so the original can be checked /
shown.

## Cross-edges (the interesting part)
A flat list, each referencing node ids. These are what let you jump from a
signpost to the machinery, or from a proof to the thing it invokes.

```jsonc
{ "from": "intro:strat:prune", "to": "lem:pruning", "rel": "points-to",
  "note": "the strategy's one-paragraph preview of the pruning step" }
```
`rel` vocabulary:
- `points-to` — a `high` node previews / signposts a concrete result.
- `proves`    — a proof (or proof-of) discharges a statement.
- `uses`      — a proof invokes another statement as a tool.
- `defines` / `uses-def` — introduces / consumes a definition or notation.
- `restates` — two statements are the same claim in different words
  (e.g. the overview inequality vs. the numbered one).
- `cites`     — relies on external prior work.

## Files
- `build_segments.py` — authoritative source; constructs the tree + edges and
  writes `segments.json`. Edit here, re-run, never hand-edit the JSON.
- `segments.json`     — generated data the viz loads.
- `viz/`              — the visualizer (`index.html`, `app.js`, `style.css`,
  `serve.py`).

## Source of truth
The LaTeX lives at
`/u/taddmao/code/autoform/math/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/build/source/`
(`00-introduction.tex` … `05-directed-cycle-consequences.tex`). All `src` line
numbers are into those files.
