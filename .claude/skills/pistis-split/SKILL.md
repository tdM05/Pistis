---
name: pistis-split
description: >
  Split a natural-language proof into ATOMIC segments (a compound sentence becomes MULTIPLE entries —
  one per idea) and mark each segment's assertion / assumption / glue spans. TEXT-focused: you read the
  NL statement + NL proof and produce an ordered JSON array; you do NOT translate to Lean and do NOT open
  the formal statement. Outputs `<corpus>/<id>/split.json`, verified to tile the source verbatim.
  Invoked with a problem path, e.g. `/pistis-split proofnet-verified/8`.
---

# Split an NL proof into atomic segments (TEXT-ONLY)

Your ONLY job: take the natural-language statement and proof of a problem and split them into atomic
**segments**. You produce a JSON file. You do NOT translate to Lean, you do NOT open the `.lean` formal
statement, you do NOT prove anything. This is pure English/LaTeX text analysis.

This realizes the paper's segmentation: the proof `Π` is partitioned into segments `s̄ = {s₁,…,sₙ}`, and
each segment carries a set of `assumption` spans (the consumed prior facts) and one `assertion` span (the
one new claim). The paper's example: *"since P and Q, therefore R"* → assumptions = {P, Q}, assert = R.
The whole point is **coverage**: concatenating the segments must recover the source text
character-for-character.

---

## Input / output

- **Input (the ONLY file you read):** `<corpus>/<id>/../data/proofnet-<id>.json` — but you are given the
  problem as a path like `proofnet-verified/8`. Read `proofnet-verified/data/proofnet-8.json`, which has
  exactly two fields: `nl_statement` and `nl_proof`. Read it DIRECTLY with the Read tool — do NOT search
  for it, do NOT open the `proofnet-N.lean` formal statement, do NOT open the baseline proof.
- **Output:** an ordered JSON array at `<corpus>/<id>/split.json`, e.g. `proofnet-verified/8/split.json`.
  Create the `<id>/` directory if it does not exist.

You tile **the whole thing**: the NL statement is the `intro` segment (index 0), then the proof is split
into ordered segments, then an optional `conclusion` at the end.

---

## HARD RULES

**RULE 1 — TEXT ONLY.** You read EXACTLY ONE input file: the problem's `data/proofnet-<id>.json`. You may
NOT open the formal `.lean` statement, the baseline proof, Mathlib, or any other problem. If you feel the
urge to "check" the formalization — STOP. Everything you need is the NL statement + NL proof.

**RULE 2 — VERBATIM TILING (WHITESPACE INCLUDED).** Your output slices, joined by EXACTLY ONE space in
index order, must reproduce the source CHARACTER-FOR-CHARACTER. The source to reproduce is
`nl_statement` (for the intro segment) followed by `nl_proof` (for the proof segments) — see "How the two
fields tile" below. Nothing reworded, dropped, duplicated, or reordered. This is mechanically checked
(byte-exact).

⚠ **WHITESPACE / LATEX IS PART OF THE TEXT — do not tidy it.** ProofNet proofs are raw LaTeX pulled from
textbooks: they contain `$…$`, `$$…$$` display math, backslash macros (`\in`, `\mathbb{Z}`, `\cap`),
runs of multiple spaces, and hard newlines (`\n`) between paragraphs and around display equations. Copy
all of it byte-for-byte.
  - **Inside a slice:** copy exactly — every `$`, every `\`, every double space, every embedded newline.
  - **At a boundary with >1 space (or a newline) between slices:** the single join-space covers ONE
    space; keep each EXTRA space/newline as a TRAILING part of the left slice (or leading part of the
    right). A dropped boundary space/newline is the #1 cause of a tiling FAIL.
  - **Display math (`$$ … $$`) spanning lines** usually belongs INSIDE the segment whose claim it states —
    do not cut a slice in the middle of a `$$…$$` block unless the block itself contains two independent
    asserted equations.

⚠ **A BUG IN THE SOURCE STAYS IN YOUR SLICES — tile it verbatim and FLAG it, never correct it.** If the
text has a typo, an internally-inconsistent statement, or a mis-attributed citation, you STILL reproduce
it character-for-character (RULE 2 is absolute) and TELL the human — you do NOT silently fix it.
Correcting an outside-source error is the human's call, not the splitter's.

**RULE 3 — ONE ATOMIC CLAIM PER SEGMENT. A long/compound sentence becomes MULTIPLE segments.** Each
segment asserts ONE thing: one equality, one membership, one inequality, one object-introduction, one
"if X then Y" consequence, one contradiction. **Do NOT keep a multi-idea sentence as a single segment
just because it is one sentence** — that is the classic under-split mistake. When a sentence packs
several ideas — "$f(x) \in (2)$ and $f(x) \in (x)$", or "$m$ must be even, and therefore $n$ must be
odd" — SPLIT it at clause boundaries into one segment per idea. The ONLY limits: each slice must stay a
**clean contiguous span that tiles** (RULE 2), and you never merge across a sentence boundary (RULE 4).
If two facts are truly interleaved in one clause (no contiguous cut), only then keep them in one segment.

**RULE 4 — SEGMENT BOUNDARIES ARE ASSERTION BOUNDARIES, NOT PERIOD BOUNDARIES.** A period does NOT
automatically create a new segment. The test: does the next sentence assert a NEW fact, or does it explain
WHY the preceding claim holds? Punctuation is a formatting artifact — faithfulness is to what was
ASSERTED, not where periods sit.
  - **Two genuine assertions always get separate segments** — but a "This means that…" / "It follows
    that…" / "since…" clause that IMMEDIATELY follows a claim and gives its reason is NOT a new
    assertion; it stays in the SAME segment as the claim it justifies (Rule 5 takes precedence).
  - **A new assertion:** "Thus, X." / "Then Y." — a claim that stands on its own. New segment.

**RULE 5 — JUSTIFICATIONS STAY WITH THEIR CLAIM — including across a period.** A "since…" / "because…" /
"This means that…" passage that gives the REASON for a claim stays in the same segment as that claim —
mark its substrings as `assumption` spans. A "by <named theorem>" clause (e.g. "by Jensen's equality",
"by the corollary of Jensen's inequality") is a citation of a prior result: it stays in the segment and
its verbatim phrase is recorded in `cite` — it does NOT become its own segment just because it is cited.

**RULE 6 — SEPARATE ASSERTION FROM ASSUMPTION; SPLIT COMPOUND ASSERTIONS.** Partition each segment's text
into ordered `spans`, each labelled `assertion` (the ONE new fact — becomes the Lean claim in the map
stage), `assumption` (a consumed prior fact — "since X" / "because Y" — becomes a discharged hypothesis),
or `glue` (connectives, punctuation, math delimiters). Joined with NOTHING (empty string) the spans must
reproduce the segment text CHARACTER-FOR-CHARACTER. If an `assertion` span bundles independent clauses
(a comma or "and"), SPLIT it into separate atomic segments — UNLESS the clauses are interleaved and
cannot be sliced contiguously, in which case keep one segment.

---

## Roles

- **intro** — ALWAYS index 0. This is the **NL statement**, verbatim (`nl_statement`), tiled as one
  segment. It states what the problem asserts (the paper's proposition `P`). Give ONLY `text` (no `spans`
  — the goal is carried by the formal statement, not proved by this segment). If `nl_statement` itself
  packs several independent claims, you MAY still keep it as one intro segment (it is the enunciation,
  not a proof step).

- **assume** — "Let $f(x) \in (2x)$", "Suppose $m^2 = 12 n^2$", "Fix $N$", "Let $m = 2r$". Introduces a
  new object or opens an assumption the rest of the proof reasons under. Provide:
  - `objects_introduced`: the labels of new objects (`["$f(x)$"]`, `["$m$", "$n$"]`), when applicable.
  - `spans`: if the introduction also consumes a prior fact ("since $x \notin U_2$, choose $v$ …"), mark
    that prior fact as an `assumption` span; otherwise a single `assertion`/`glue` partition is fine.

- **deduction** — an assertion of a new fact (the bulk of the proof). Provide:
  - `spans`: the ordered `assertion`/`assumption`/`glue` partition (RULE 6) — the primary structure.
  - `assertion`: a 1-line plain-English paraphrase of the new fact (human-readable summary).
  - `cite`: `{ "text": "<the verbatim NL phrase naming the prior result>" }` when the step invokes a
    named prior result ("by Jensen's equality", "the corollary above"), or `null`. **Record ONLY the
    verbatim phrase — this stage is TEXT-ONLY.** Do NOT try to resolve it to a Lean name: the mapping
    from that phrase to a fully-qualified Lean identifier (Mathlib lemma / prior corpus theorem / a
    helper you must formalize first) is a later, Lean-aware step that adds a `ref` field. Here you only
    capture the citation text as written. Omit / `null` when nothing is cited.

- **wts** ("what to show") — a MID-PROOF announcement of a sub-goal: "We claim that …", "We will show
  that …", "It suffices to show …", "To prove this one way, …". It states what the FOLLOWING segments
  will prove — it is NOT itself a proven fact. Mark role `wts` and give ONLY `text` (no `spans`, no
  `assertion`, no `cite`). The map stage stamps it as `pistis_wts` (a claimless structural tactic), so
  there is no claim to fill.

- **conclusion** — the last segment, when the proof has an explicit closing restatement ("Thus,
  $(2)\cap(x) = (2x)$, as required.", "QED", "The series converges."). If the proof has NO closing
  restatement, **omit this role entirely** — an empty conclusion is fine (the goal is discharged by the
  formal statement, not a text ritual). When present, give ONLY `text`.

## Reductio (proof-by-contradiction) frames — the `frame` overlay

Many ProofNet proofs are by contradiction ("suppose for purposes of contradiction …"). A reductio has
THREE text-signalled moves. Mark each with an optional `frame` object ON TOP OF its normal role (these
segments are still `assume`/`deduction`s — they carry real content: a supposition, `False`, a negation).
The map stage uses them to stamp the nested contradiction block, so the map agent never hand-builds the
frame.

- **reductio_open** — "Suppose for purposes of contradiction that …", "For if not …", "Assume $X$." —
  the sentence that SUPPOSES the negation of the goal. Record the supposed fact in `supposition`.
  ```json
  { "role": "assume", "text": "suppose for purposes of contradiction that $U_1 \\cup U_2$ is a subspace and neither is contained in the other.",
    "frame": { "kind": "reductio_open", "supposition": "$U_1 \\cup U_2$ is a subspace and neither is contained in the other" },
    "spans": [ … ] }
  ```
- **contradiction** — "This is clearly a contradiction", "The very thing is impossible", "which is
  absurd" (`assertion`: "contradiction"). The map stage pre-sets its claim to `False`.
  ```json
  { "role": "deduction", "text": "This is clearly a contradiction, as each element was defined to not be in these subspaces.",
    "assertion": "contradiction", "frame": { "kind": "contradiction" }, "spans": [ … ] }
  ```
- **reductio_close** — "Thus our initial assumption must have been wrong, and …" — the sentence that
  DISCHARGES the reductio (establishes the negation of the supposition). `closes` is a **VERBATIM COPY of
  the matching open's `supposition`** — the two are linked by TEXT, not by index.
  ```json
  { "role": "deduction", "text": "Thus our initial assumption must have been wrong, and $U_1 \\subseteq U_2$ or $U_2 \\subseteq U_1$",
    "assertion": "one subspace is contained in the other",
    "frame": { "kind": "reductio_close", "closes": "$U_1 \\cup U_2$ is a subspace and neither is contained in the other" }, "spans": [ … ] }
  ```

A proof with two directions or two cases (e.g. an "if and only if") may have two independent reductio
triples, or one direction by contradiction and one direct — split each on its own merits.

---

## When to mark an assumption span

An `assumption` span is a substring that names a PRIOR FACT consumed by this step's reasoning:

**DO mark:**
- "since $p(x) \in (2)$" — cites a previously-established membership
- "because $x g(x)$ is a polynomial" — cites a known property
- "$g(0) \neq 0$" at the end of a "since …" clause citing a prior step's result

**DO NOT mark:**
- The assertion itself (what THIS segment newly claims)
- "Similarly" / "for the same reason" — too vague, skip (leave as glue)
- A named citation ("by Jensen's equality") — that goes in `cite`, not an assumption span

---

## Output format

Write a JSON array to `<corpus>/<id>/split.json`, entries **IN ORDER** (intro first, then the proof
segments, conclusion last if present). **Do NOT write an `index` field — it is auto-assigned from array
position.**

Intro (the NL statement, verbatim):
```json
{ "role": "intro", "text": "<verbatim nl_statement>" }
```

Assume / object introduction:
```json
{ "role": "assume", "text": "Let $f(x) \\in (2x)$.", "objects_introduced": ["$f(x)$"], "spans": [ … ] }
```

Deduction (`spans` per RULE 6 + a 1-line `assertion` paraphrase + `cite` if a result is named):
```json
{ "role": "deduction",
  "text": "But this means that $f(x) \\in (2)$ (because $x g(x)$ is a polynomial),",
  "assertion": "f(x) is in the ideal (2)",
  "spans": [
    { "label": "glue",       "text": "But this means that " },
    { "label": "assertion",  "text": "$f(x) \\in (2)$" },
    { "label": "glue",       "text": " (" },
    { "label": "assumption", "text": "because $x g(x)$ is a polynomial" },
    { "label": "glue",       "text": ")," } ],
  "cite": null }
```
The span texts joined with NOTHING must equal `text` character-for-character.

When a result IS named, `cite` is an object holding only the verbatim phrase:
```json
{ "role": "deduction",
  "text": "By the Corollary of Jensen's equality we get $S_N \\leq \\int_0^1 n(r) \\frac{dr}{r}$.",
  "assertion": "S_N is bounded by the Jensen integral",
  "spans": [ … ],
  "cite": { "text": "the Corollary of Jensen's equality" } }
```

Omit fields not relevant to a role. Use `null` for `cite` when nothing is cited; otherwise a
`{ "text": ... }` object (text-only — no Lean name at this stage).

---

## How the two fields tile

The coverage check reconstructs the source as: **`nl_statement`** then a single space then **`nl_proof`**
(with the statement being exactly the intro segment's text, and the remaining segments tiling `nl_proof`).
Concretely: intro segment text == `nl_statement` verbatim; the concatenation of every NON-intro segment
(joined by one space, in order) == `nl_proof` verbatim. The gate checks both halves.

---

## Procedure

1. Read the problem's `data/proofnet-<id>.json` (the ONLY file you read).
2. Set index 0 = `intro` = `nl_statement` verbatim.
3. Split `nl_proof` into ordered atomic segments (`assume` / `deduction` / `wts`), marking spans and any
   reductio frames.
4. Add a `conclusion` segment ONLY if `nl_proof` ends with an explicit closing restatement; otherwise omit.
5. Write the JSON array to `<corpus>/<id>/split.json`.
6. VERIFY — MACHINE GATE (mandatory; run it, do NOT just eyeball). Run
   `python3 scripts/check_split.py <corpus>/<id>` (e.g. `python3 scripts/check_split.py proofnet-verified/8`).
   It joins your slices and compares BYTE-FOR-BYTE to the source (`nl_statement` vs the intro segment,
   `nl_proof` vs the joined non-intro segments). On FAIL it names the exact divergence:
   - a **whitespace/newline** miss → add the missing space(s)/newline INSIDE the adjacent slice per RULE 2.
   - a **word/LaTeX** divergence / missing tail / overrun → fix the slice text (verbatim, contiguous).
   **Loop until it prints PASS.** Do NOT stop or hand off while it still FAILs — a split that doesn't tile
   poisons every downstream stage.
7. Report a summary table (index, role, first ~60 chars of text) and STOP for human review.

---

## Example (abbreviated — proofnet-8, the ideal-intersection $\mathbb{Z}[x]$ proof)

`nl_statement`: "Prove that in the ring $\mathbb{Z}[x],(2) \cap(x)=(2 x)$."
`nl_proof`: "Let $f(x) \in(2 x)$. Then there exists some polynomial $g(x) \in \mathbb{Z}$ such that … Finally, (2) $\cap(x)=(2 x)$, as required."

Output (abbreviated):
```json
[
  { "role": "intro", "text": "Prove that in the ring $\\mathbb{Z}[x],(2) \\cap(x)=(2 x)$." },
  { "role": "assume", "text": "Let $f(x) \\in(2 x)$.", "objects_introduced": ["$f(x)$"], "spans": [ … ] },
  { "role": "deduction", "text": "Then there exists some polynomial $g(x) \\in \\mathbb{Z}$ such that\n$$\nf(x)=2 x g(x)\n$$",
    "assertion": "f(x) = 2 x g(x) for some polynomial g", "spans": [ … ], "cite": null },
  { "role": "deduction", "text": "But this means that $f(x) \\in(2)$ (because $x g(x)$ is a polynomial),",
    "assertion": "f(x) is in the ideal (2)", "spans": [ … ], "cite": null },
  "… (the rest of the ⊆ argument, then the ⊇ argument) …",
  { "role": "conclusion", "text": "Finally,\n(2) $\\cap(x)=(2 x)$,\nas required." }
]
```
Note the display-math block `$$ … $$` and its surrounding `\n`s stay INSIDE the segment whose equation
they state, tiled verbatim.
