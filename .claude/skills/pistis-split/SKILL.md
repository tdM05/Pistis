---
name: pistis-split
description: >
  Split a natural-language proof into ATOMIC segments (a compound sentence becomes MULTIPLE entries —
  one per idea) and mark each segment's assumptions set + single assertion. TEXT-focused: you read the
  NL statement + NL proof and produce an ordered JSON array; you do NOT translate to Lean and do NOT open
  the formal statement. Outputs `<corpus>/item<N>/split.json`, verified to tile the source verbatim.
  Invoked with an item path, e.g. `/pistis-split proofnet_verified/item8`.
---

# Split an NL proof into atomic segments (TEXT-ONLY)

Your ONLY job: take the natural-language statement and proof of a problem and split them into atomic
**segments**. You produce a JSON file. You do NOT translate to Lean, you do NOT open the `.lean` formal
statement, you do NOT prove anything. This is pure English/LaTeX text analysis.

This realizes the paper's segmentation: the proof `Π` is partitioned into segments `s̄ = {s₁,…,sₙ}`, and
each segment `sᵢ` gets `assumptions(sᵢ)` (a SET of substrings — the consumed prior facts) and
`assert(sᵢ)` (a SINGLE substring — the one new claim). The paper's example: *"since P and Q, therefore
R"* → assumptions = {P, Q}, assert = R.
The whole point is **coverage**: concatenating the segments must recover the source text
character-for-character.

---

## Input / output

- **Input (the ONLY files you read):** the item's `<corpus>/item<N>/data/nl_statement.txt` and
  `<corpus>/item<N>/data/nl_proof.txt` — you are given the item as a path like
  `proofnet_verified/item8`, so read `proofnet_verified/item8/data/nl_statement.txt` and
  `proofnet_verified/item8/data/nl_proof.txt`. Each file's bytes ARE the text you must tile: plain
  UTF-8, no JSON escaping, no trailing newline. Read them DIRECTLY with the Read tool — do NOT
  search for them, do NOT open the item's `data/statement.lean` formal statement, do NOT open any baseline.
- **Output:** an ordered JSON array at `<corpus>/item<N>/split.json`, e.g.
  `proofnet_verified/item8/split.json` (written in the item folder, alongside `data/`).

You tile **the whole thing**: the NL statement is the `intro` segment (index 0), then the proof is split
into ordered segments, then an optional `conclusion` at the end.

---

## HARD RULES

**RULE 1 — TEXT ONLY.** You read EXACTLY TWO input files: the item's `data/nl_statement.txt` and
`data/nl_proof.txt`. You may
NOT open the formal `.lean` statement, the baseline proof, Mathlib, or any other problem. If you feel the
urge to "check" the formalization — STOP. Everything you need is the NL statement + NL proof.

**RULE 2 — VERBATIM TILING (WHITESPACE INCLUDED).** Your output slices, joined by EXACTLY ONE space in
index order, must reproduce the source CHARACTER-FOR-CHARACTER. The source to reproduce is
`nl_statement.txt` (for the intro segment) followed by `nl_proof.txt` (for the proof segments) — see "How the two
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
its substring goes into that segment's `assumptions` set. A "by <named theorem>" clause (e.g. "by
Jensen's equality", "by the corollary of Jensen's inequality") is a citation of a prior result: it stays
in the segment and its verbatim phrase is recorded in `cite` — it does NOT become its own segment just
because it is cited.

**RULE 6 — EACH SEGMENT HAS A SET OF ASSUMPTIONS AND A SINGLE ASSERTION.** This is the paper's core
structure (§4): each segment `sᵢ` gets `assumptions(sᵢ)` = a **SET of substrings** (the consumed prior
facts) and `assert(sᵢ)` = a **SINGLE substring** (the one new fact this segment claims). For "since $P$
and $Q$, therefore $R$": `assumptions = [P, Q]`, `assert = R`.
  - **Every entry of `assumptions` and the `assert` value must be an EXACT substring of the segment's
    `text`** (copy the bytes — `$…$`, backslashes and all). They are pointers INTO the text, used later to
    map each assumption/assertion to a formal step. They do NOT need to tile or cover the text (unlike the
    segment `text` itself, which DOES tile — RULE 2); connectives/punctuation simply belong to neither set.
  - **A SEGMENT HAS EXACTLY ONE `assert`.** If a sentence makes several independent claims ("$g=a^ib^j$
    and $h=a^kb^l$"... two facts), SPLIT it into separate segments — one `assert` each — UNLESS the claims
    are interleaved and cannot be sliced into contiguous tiling segments, in which case keep one segment
    and let `assert` be the whole compound substring.
  - `assumptions` is `[]` when the segment consumes no prior fact (a fresh object introduction or an
    unconditioned claim).

---

## Segments and roles

The unit is the **segment** (the paper's `sᵢ`). By default a segment is a plain reasoning step: it has an
`assumptions` set + a single `assert` (RULE 6) and an optional `cite`. It carries **no `role` field** —
the blank/default role IS "a normal segment", the bulk of the proof. The map stage stamps every default
segment as `pistis_segment`.

`role` is an **OPTIONAL, SPECIAL-CASE** field. Set it ONLY for the three structural segments that are NOT
normal reasoning steps (they carry no `assumptions`/`assert` and get a non-`pistis_segment` tactic):

- **`intro`** — ALWAYS index 0. The **NL statement**, verbatim (`nl_statement`), as one segment. It states
  what the problem asserts (the paper's proposition `P`); the goal is carried by the formal statement, not
  proved here. Give ONLY `text`. → `pistis_intro`.

- **`wts`** ("what to show") — a MID-PROOF announcement of a sub-goal: "We claim that …", "We will show
  that …", "It suffices to show …", "To prove this one way, …". It states what the FOLLOWING segments
  prove — it is NOT itself a proven fact. Give ONLY `text` (no `assumptions`, no `assert`, no `cite`). →
  `pistis_wts`.

- **`conclusion`** — the last segment, when the proof has an explicit closing restatement ("Thus,
  $(2)\cap(x) = (2x)$, as required.", "QED", "The series converges."). If the proof has NO closing
  restatement, **omit it entirely** (the goal is discharged by the formal statement, not a text ritual).
  Give ONLY `text`. → `pistis_conclude`.

### Fields of a default (plain) segment

- `assumptions`: the paper's `assumptions(sᵢ)` — a SET (JSON array) of the prior-fact substrings this
  step consumes ("since X", "because Y"). Each entry is an EXACT substring of `text`. `[]` if none.
- `assert`: the paper's `assert(sᵢ)` — the SINGLE substring naming the ONE new fact this segment claims.
  An EXACT substring of `text` (NOT a paraphrase).
- `cite`: `{ "text": "<the verbatim NL phrase naming the prior result>" }` when the step invokes a
  named prior result ("by Jensen's equality", "the corollary above"), or `null`. **Record ONLY the
  verbatim phrase — this stage is TEXT-ONLY.** Do NOT resolve it to a Lean name: mapping that phrase to a
  fully-qualified identifier (Mathlib lemma / prior corpus theorem / a helper you must formalize first) is
  a later, Lean-aware step that adds a `ref` field. Omit / `null` when nothing is cited.
- `objects_introduced` (optional): when the segment introduces new objects ("Let $f(x) \in (2x)$", "Fix
  $N$", "Let $m = 2r$"), the labels of those objects (`["$f(x)$"]`, `["$m$", "$n$"]`). A pure
  object-introduction still has an `assert` (the introduction itself) and usually empty `assumptions`.
- `frame` (optional): the reductio overlay, see below.

## Reductio (proof-by-contradiction) frames — the `frame` overlay

Many ProofNet proofs are by contradiction ("suppose for purposes of contradiction …"). A reductio has
THREE text-signalled moves. Mark each with an optional `frame` object on a normal (default-role) segment
— these are still plain segments carrying real content (a supposition, `False`, a negation), NOT special
roles. The map stage uses `frame` to stamp the nested contradiction block, so the map agent never
hand-builds the frame.

- **reductio_open** — "Suppose for purposes of contradiction that …", "For if not …", "Assume $X$." —
  the sentence that SUPPOSES the negation of the goal. Record the supposed fact in `supposition`.
  ```json
  { "text": "suppose for purposes of contradiction that $U_1 \\cup U_2$ is a subspace and neither is contained in the other.",
    "assumptions": [], "assert": "$U_1 \\cup U_2$ is a subspace and neither is contained in the other",
    "frame": { "kind": "reductio_open", "supposition": "$U_1 \\cup U_2$ is a subspace and neither is contained in the other" } }
  ```
- **contradiction** — "This is clearly a contradiction", "The very thing is impossible", "which is
  absurd". The map stage pre-sets its claim to `False`.
  ```json
  { "text": "This is clearly a contradiction, as each element was defined to not be in these subspaces.",
    "assumptions": ["each element was defined to not be in these subspaces"], "assert": "This is clearly a contradiction",
    "frame": { "kind": "contradiction" } }
  ```
- **reductio_close** — "Thus our initial assumption must have been wrong, and …" — the sentence that
  DISCHARGES the reductio (establishes the negation of the supposition). `closes` is a **VERBATIM COPY of
  the matching open's `supposition`** — the two are linked by TEXT, not by index.
  ```json
  { "text": "Thus our initial assumption must have been wrong, and $U_1 \\subseteq U_2$ or $U_2 \\subseteq U_1$",
    "assumptions": [], "assert": "$U_1 \\subseteq U_2$ or $U_2 \\subseteq U_1$",
    "frame": { "kind": "reductio_close", "closes": "$U_1 \\cup U_2$ is a subspace and neither is contained in the other" } }
  ```

A proof with two directions or two cases (e.g. an "if and only if") may have two independent reductio
triples, or one direction by contradiction and one direct — split each on its own merits.

---

## What goes in `assumptions`

Each entry of `assumptions` is a substring that names a PRIOR FACT consumed by this step's reasoning:

**DO include:**
- "since $p(x) \in (2)$" → `"$p(x) \\in (2)$"` — a previously-established membership
- "because $x g(x)$ is a polynomial" → `"$x g(x)$ is a polynomial"` — a known property
- "$g(0) \neq 0$" at the end of a "since …" clause citing a prior step's result

**DO NOT include:**
- The `assert` itself (what THIS segment newly claims)
- "Similarly" / "for the same reason" — too vague, skip
- A named citation ("by Jensen's equality") — that goes in `cite`, not `assumptions`

---

## Output format

Write a JSON array to `<corpus>/item<N>/split.json`, entries **IN ORDER** (intro first, then the proof
segments, conclusion last if present). **Do NOT write an `index` field — it is auto-assigned from array
position.**

Intro (the NL statement, verbatim — the one special segment at index 0):
```json
{ "role": "intro", "text": "<verbatim nl_statement>" }
```

A default segment (NO `role` field; the paper's `assumptions` set + single `assert`, each an EXACT
substring of `text`; + `cite` if a result is named). Add `objects_introduced` when it introduces objects:
```json
{ "text": "But this means that $f(x) \\in(2)$ (because $x g(x)$ is a polynomial),",
  "assumptions": ["$x g(x)$ is a polynomial"],
  "assert": "$f(x) \\in(2)$",
  "cite": null }
```
Both the `assert` value and every `assumptions` entry must appear VERBATIM inside `text` (they are
pointers into it). They need not cover the text — connectives/punctuation belong to neither.

When a result IS named, `cite` is an object holding only the verbatim phrase:
```json
{ "text": "By the Corollary of Jensen's equality we get $S_N \\leq \\int_0^1 n(r) \\frac{dr}{r}$.",
  "assumptions": [],
  "assert": "$S_N \\leq \\int_0^1 n(r) \\frac{dr}{r}$",
  "cite": { "text": "the Corollary of Jensen's equality" } }
```

Omit fields not relevant to a segment. A default segment has no `role`; only `intro`/`wts`/`conclusion`
carry one. Use `null` for `cite` when nothing is cited; otherwise a `{ "text": ... }` object (text-only —
no Lean name at this stage).

---

## How the two fields tile

The coverage gate checks TWO halves INDEPENDENTLY (no artificial join-space is inserted between the
statement and the proof):
- the `intro` segment's text == `nl_statement` verbatim; and
- the concatenation of every NON-intro segment (joined by exactly one space, in order) == `nl_proof`
  verbatim.

---

## Procedure

1. Read the item's `<corpus>/item<N>/data/nl_statement.txt` and `data/nl_proof.txt` (the ONLY files
   you read).
2. Set index 0 = a `role: intro` segment = `nl_statement.txt` verbatim.
3. Split `nl_proof.txt` into ordered atomic segments. Most are DEFAULT segments (no `role`) with an
   `assumptions` set + single `assert`; use `role: wts` for a mid-proof "we claim/it suffices"
   announcement, and mark reductio `frame`s where a contradiction argument opens/closes.
4. Add a `role: conclusion` segment ONLY if `nl_proof.txt` ends with an explicit closing restatement; else omit.
5. Write the JSON array to `<corpus>/item<N>/split.json`.
6. VERIFY — MACHINE GATE (mandatory; run it, do NOT just eyeball). Run
   `python3 scripts/check_split.py <corpus>/item<N>` (e.g. `python3 scripts/check_split.py proofnet_verified/item8`).
   It compares BYTE-FOR-BYTE (`nl_statement` vs the intro segment, `nl_proof` vs the joined non-intro
   segments). On FAIL it names the exact divergence:
   - a **whitespace/newline** miss → add the missing space(s)/newline INSIDE the adjacent slice per RULE 2.
   - a **word/LaTeX** divergence / missing tail / overrun → fix the slice text (verbatim, contiguous).
   **Loop until it prints PASS.** Do NOT stop or hand off while it still FAILs — a split that doesn't tile
   poisons every downstream stage.
7. Report a summary table (index, role-or-"segment", first ~60 chars of text) and STOP for human review.

---

## Example (abbreviated — proofnet-8, the ideal-intersection $\mathbb{Z}[x]$ proof)

`nl_statement`: "Prove that in the ring $\mathbb{Z}[x],(2) \cap(x)=(2 x)$."
`nl_proof`: "Let $f(x) \in(2 x)$. Then there exists some polynomial $g(x) \in \mathbb{Z}$ such that … Finally, (2) $\cap(x)=(2 x)$, as required."

Output (abbreviated — note only intro/conclusion carry a `role`; the middle segments are default):
```json
[
  { "role": "intro", "text": "Prove that in the ring $\\mathbb{Z}[x],(2) \\cap(x)=(2 x)$." },
  { "text": "Let $f(x) \\in(2 x)$.", "objects_introduced": ["$f(x)$"], "assumptions": [], "assert": "$f(x) \\in(2 x)$", "cite": null },
  { "text": "Then there exists some polynomial $g(x) \\in \\mathbb{Z}$ such that\n$$\nf(x)=2 x g(x)\n$$",
    "assumptions": [], "assert": "$$\nf(x)=2 x g(x)\n$$", "cite": null },
  { "text": "But this means that $f(x) \\in(2)$ (because $x g(x)$ is a polynomial),",
    "assumptions": ["$x g(x)$ is a polynomial"], "assert": "$f(x) \\in(2)$", "cite": null },
  "… (the rest of the ⊆ argument, then the ⊇ argument) …",
  { "role": "conclusion", "text": "Finally,\n(2) $\\cap(x)=(2 x)$,\nas required." }
]
```
Note the display-math block `$$ … $$` and its surrounding `\n`s stay INSIDE the segment whose equation
they state, tiled verbatim.
