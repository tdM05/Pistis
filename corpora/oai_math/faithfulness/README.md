# align-then-label for the openai/math corpus

The [faithfulness-dataset](../../../../faithfulness-dataset) labeler, vendored into this corpus and
driven by Pistis's proof decomposition. Isolated here on purpose: nothing outside
`corpora/oai_math/` is touched, so this can be exercised on one corpus before being promoted.

```
cd corpora/oai_math
python3 faithfulness/gen_datapoints.py items/item1    # derive the datapoints from the proof
python3 faithfulness/check_targets.py                 # every T_F is exactly the claim it says it is
python3 faithfulness/check_citations.py               # every Main.lean:LINE citation points at it too
python3 faithfulness/check_verbatim.py                # every string shown is in the source it cites
python3 faithfulness/check_coverage.py                # the finishing gate
python3 faithfulness/ui/serve.py                      # then open http://localhost:8000
```

One page, **two panels**:

* **left — `Main.lean` itself**, the entire file, verbatim and complete, syntax highlighted, with
  line numbers. Nothing is summarized or cut: the signature, the tactics, the claims and the comments
  are all there, because the NL text being judged *is* the string literals in that file.
* **right — the align-then-label view** of whichever unit you clicked: the `T_F`/`T_N` span strip,
  then the `F` and `N` columns (`S_F`, `C_F` / `S_N`, `C_N`, `I`) with the edges and their verdicts.

The proof is the index, so there is no file tree: you click a claim where it is written. **Drag the
divider** to give either side more room (double-click it to go back to the default); the width is
remembered. The proof **soft wraps** by default — `alt+Z` toggles it, as in VSCode, and wrapped rows
hang under their line's own indentation. With wrapping off, long lines scroll sideways and the line
numbers stay pinned.

| clickable region | opens |
| --- | --- |
| `pistis_intro "1.0" r"…"` | the `statement` unit |
| `pistis_segment "1.k" r"…"` (keyword, loc and NL literal) | that segment's unit |

It also works the other way. A `C_F` item cites the line it was read off
(`items/item1/Main.lean:46`), and that citation is a **clickable chip** on the card: it jumps the
proof panel to that line and marks it — same tab, no navigation, because this panel already holds the
whole file. **alt+←** (or the pane's `← back` button) returns to where you were, restoring both the
scroll position and the unit that was open. A citation is only drawn as a link when it resolves: a
file that is shown but has no such line is struck through, and provenance that is not on the page at
all (`Mathlib/…`) stays plain text.

**`check_citations.py` is the same check offline**, and it is not decoration. It immediately found
that all six of item1's citations were off by one: `pistis_proof` numbered lines from
`tf_norm.strip_comments`, which drops the newlines *inside* a block comment, so everything below the
`/-- … -/` at line 9 shifted up — the `obtain`'s record cited a comment and the `set`'s cited the
`obtain` above it. `_code_lines` now blanks comments while keeping every line, and the gate checks
the cited line against the **raw** file (not a comment, and it does say the stored text) before
asking `_ambient` anything, precisely so a numbering bug in the reader cannot agree with the
citations it wrote.

## Is it a quote?

The right panel is read as a quotation of the proof, so **`check_verbatim.py` holds every string it
shows to being text the cited source contains.** `T_N` must be a byte-for-byte substring of
`data/nl_{statement,proof}.txt`; a segment's `T_F` must be its claim as written in `Main.lean` (whitespace collapse is
the one liberty, and it is forced — `parse_main` collapses it); the statement's `T_F` must be its
lines, in source order, with `sorry` the only inserted token; `S_F`/`S_N` are slices, so they are
checked for being inside their target. The file is read through `_code_lines`, so nothing can be
"quoted" out of a comment.

The interesting column is `C_F`, where a seeder can paraphrase. The rule there is one rule with no
exceptions: **the string shown must occur, contiguously, in the lines it cites.** Nothing may be
stitched together, re-ordered, or inferred from what Lean would elaborate.

That rule is why a `C_F` item is now a **quote of the clause** — `obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ ≠ 0`,
`set Dτ : Matrix I J ℝ := D + τ • Matrix.single s j (1 : ℝ) with hDτ` — and carries no `name` field.
Three earlier shapes are all gone, and each was a string that existed only in the datapoint:

* `hsuppose1 : x j * y s ≠ 0`. The name is on line 38 (`intro hsuppose1`), the proposition on line 37
  (`have habsurd1 : ¬(x j * y s ≠ 0)`), the `:` on neither. An earlier version of this gate let it
  through as *framed* — name and type each found on the cited lines — and widening the citation to
  `37-38` did not make the string any more present. Both halves being in the file is exactly the
  argument for letting a reconstruction through, so the gate names that shape (`!stitched`) and
  rejects it.
* `hτ : τ ≠ 0`, split out of the `obtain` above. True, and not in the file.
* `hDτ : Dτ = D + τ • Matrix.single s j (1 : ℝ)`, which the file does not write because `set` writes
  `:=`. This used to be permitted as a *declared derivation* (`"derived": "set-equation"`). There is
  no such escape hatch now: what the proof says is the `set` clause, so that is what is shown.

Dropping the name costs nothing — the clause already says which names it binds — and removes the only
field that invited a reconstruction. `pistis_proof._quote` enforces the same rule from the writing
side: the text is the SEARCH KEY for its own citation, so a record that is not a quote of the file
cannot acquire a citation at all; it comes back `None` and is never emitted.

The gate deliberately does **not** go through `pistis_proof._ambient`: that is the reader that wrote
these signatures, and a gate routed through the thing it audits can only show that the thing agrees
with itself — which is exactly how the off-by-one below survived its first check. It is validated by
mutation instead, against a scratch copy. Sixteen edits, all caught: the `hsuppose1` stitch citing
`:38` and citing `:37-38`, the framed `hτ`, the `set`-derived `hDτ` both bare and still tagged
`derived`, a real clause on the wrong line, a type pinned to a name the line never binds, a
signature quoted out of a docstring, a wholly invented item, a paraphrased `T_N`, a macro quietly
expanded, a restated claim, shuffled statement lines, a `sorry` swapped for a real tactic, an
out-of-range span and an unsourced `C_N`.

Everything else in the file is just the proof, shown so nothing is hidden. Status is deliberately
*not* drawn into the source — a badge after every region broke up the text it was annotating. Hover a
region instead and its title gives the unit and its current verdict; the pane's toolbar carries the
overall `done` count, and saving re-reads it. The
open unit is outlined in the proof, and `?path=` names it, so a unit's view is linkable (ctrl-click a
region to open it in its own tab).

Those regions come from `pistis_proof.source_anchors`, as UTF-16 offsets into the *raw* source. The
panel therefore never reformats what it renders: Shiki's tokens are flattened to coloured runs and
then checked against the source character-for-character, and the colours are dropped if they don't
reconstruct it — a misplaced click target is worse than a monochrome proof.

The file is laid out as one grid row per source line, the number in its own gutter cell, so that
wrapping cannot drift the numbers out of step with the text. The cost is that a region crossing a
line break is emitted as one `<a>` per line (10 regions, 36 fragments in item1); they share a
`data-u`, so they highlight together and any of them opens the same unit.

## The unit model

The faithfulness-dataset model is per-statement: one datapoint is one `(T_F, T_N)` pair. A Pistis
item is a whole proof, so `pistis_proof.proof_outline` cuts it into units — one per alignment the
formalization asserts:

| unit id     | `T_N`                       | `T_F`                                      | coverage |
| ----------- | --------------------------- | ------------------------------------------ | -------- |
| `statement` | the item's `nl_statement`   | header + theorem signature                 | complete |
| `seg-<loc>` | one `pistis_segment`'s text | its claim — the type inside `(stepK : …)`  | complete |

Units are **derived, never hand-maintained** — they come out of `Main.lean`, `split.json`,
`meta.json` and `data/nl_{statement,proof}.txt` on every request, so editing the proof moves them with it. They land
on disk as `items/item<N>/align/<unit>/artifacts/`, which is what `find_datapoints()` discovers.

Two deliberate choices:

* **A segment's `T_F` is its claim and *only* its claim** — the type inside `(stepK : …)`, with the
  binder name dropped and whitespace collapsed. Not the tactic around it, not the `:= by` body, not a
  synthetic `theorem` with the binders restated, and not the lines above it. A segment asserts its
  claim and nothing else, so that proposition is the whole of what its sentence is judged against;
  padding the target is the one way to make an alignment look complete while the sentence is not
  really being checked. **`check_targets.py` fails if a stored `T_F` is anything else** — it re-reads
  the claims from `Main.lean` with the same parser the Pistis gates use, so it catches both a stale
  datapoint and a change of mind in the generator.
* **`C_F` is what the sentence introduces, and nothing else.** "For a nonzero real τ, the matrix
  `D_τ = D + τ e_s e_jᵀ` is still supported on T" has the claim `SupportedOn T Dτ`, while τ and `D_τ`
  are brought into being by the `obtain` / `set` lines above the tactic — and "Suppose instead
  that …" is opened by the `have h : ¬P := by intro hp` the segment sits inside. Those clauses would
  otherwise have nothing to align against, so `C_F` carries exactly the records between a segment's
  tactic and the previous one.

  It is *not* "whatever the claim needs in order to be read". That rule has no floor: `x : J → ℝ`
  needs `ℝ`, which needs the field axioms, which need ⋯, and stopping at the names that happen to be
  written in `Main.lean` is an artefact of which file the seeder reads. Writing a name is also not
  saying what its binder says — "$x_jy_s\ne0$" writes `x` and `j` and says nothing about where they
  live. The theorem's binders are therefore the `statement` unit's business, judged there once
  against the prose that introduces them rather than nine times over against prose that merely uses
  the name. In item1 that leaves four `C_F` items in two segments, each linked to the prose that
  introduces it, no ⊥ `C_F` edges anywhere, and seven of the nine segments with no context at all.

  The unit of context is the **clause**, not the name, and each item is that clause quoted: `obtain
  ⟨τ, hτ⟩ : ∃ τ : ℝ, τ ≠ 0` is one thing the proof does and "For a nonzero real τ" is one thing the
  prose says, so they are one edge. Splitting it into `τ : ℝ` and `hτ : τ ≠ 0` was two strings that
  appear nowhere in the file, aligned against prose that says it once. See *Is it a quote?* above.

## Seeded vs. authored

`gen_datapoints.py` seeds only what is already **derived** from text the Pistis gates hold verbatim:

* both targets (`T_N` is byte-identical to its slice of `data/nl_{statement,proof}.txt`; `T_F` is the Lean claim,
  gated by `check_targets.py`);
* `S_N[0]`, the unit's focus substring — `split.json`'s `assert`, already gated as an exact
  substring of the segment's text;
* `S_F[0]`, one region over the whole target;
* `C_F.items`, whatever this segment itself introduces — each one the clause verbatim, with the
  `Main.lean:LINE` it is written on.

Not seeded, because it is the judgment a human is here to make: **`R`** (which region corresponds to
which) and **`lambda`** (whether each correspondence holds, and why). They start empty, so `label.txt`
stays `NaN` until someone labels. `check_coverage.py` therefore reports errors on a fresh datapoint —
that is a draft failing the finishing gate, not a bug.

The statement unit gets **no** span seed on either side: a theorem is not atomic, and how to cut it
into regions is the labeler's call.

item1's annotation is authored, and it lives in **`annotate_item1.py`** rather than only in
`align/*/artifacts/`. Two reasons: `--force` resets spans and edges whenever a target changes, and
spans are UTF-16 offsets, which rot the moment a target is re-indented. In that script every region
is named by the text it covers and the offsets are computed, so a target that moves fails loudly
("needle not found") instead of silently mislabelling. Run it with `--check` to validate without
writing. It reads as the annotation it is: one block per unit, one line per edge saying which formal
region matches which NL fragment and why.

Human work is never clobbered. Re-running the generator leaves a datapoint whose seeds still match
(`[ok  ]`) and only *reports* one that has drifted (`[STALE]`, naming which of `T_F` / `T_N` /
`C_F.items` moved) — its spans index into the old text, so rewriting needs an explicit `--force`.
`C_F.items` is compared too, which is what catches a change in how a clause is *read*: when
`_ambient` stopped reconstructing `τ : ℝ` and `hτ : τ ≠ 0` and started quoting the `obtain` they came
out of, the two affected datapoints went stale rather than keeping signatures the proof does not
say. The price is that `C_F` items added by hand in the UI also read
as drift; `--force` would lose them, which is recoverable, where silent disagreement is not.

## Files

| file                | role |
| ------------------- | ---- |
| `pistis_proof.py`   | the proof → units decomposition, plus `source_anchors` (where each unit is written in `Main.lean`). Single source of truth for both panels and the datapoints, so they cannot drift. Has a CLI: `python3 faithfulness/pistis_proof.py items/item1`. |
| `gen_datapoints.py` | units → `artifacts/` trees. `--all`, `--force`. |
| `annotate_item1.py` | item1's authored annotation (spans, edges, verdicts and their reasons), re-runnable. `--check`. Refuses to run on a target `check_targets.py` rejects. |
| `check_targets.py`  | new gate: every stored `T_F` is exactly the claim inside `(stepK : …)` (or, for `statement`, the theorem signature). Re-reads `Main.lean` itself. |
| `check_citations.py`| new gate: every `C_F` item's `Main.lean:LINE` citation points at line(s) that are not a comment, do say the stored text, and are where `_ambient` reads that clause off. |
| `check_verbatim.py` | new gate: every string the right panel shows is a contiguous substring of the source it cites — no stitching, no framing, no declared derivations. Reads the file with `splitlines()`, never through `_ambient`. |
| `alignment_data.py` | **vendored.** Dataset IO + UTF-16 region validation. |
| `check_coverage.py` | **vendored, verbatim.** The finishing gate. |
| `tf_norm.py`        | **vendored, verbatim.** Flattens `T_F` to one line per declaration. |
| `ui/serve.py`       | **vendored + adapted.** The JSON API and the page. |
| `ui/index.html`     | **vendored + adapted.** The align-then-label labeler (the right panel) and the shell. |
| `ui/proof_pane.js`  | new. The left panel: `Main.lean` verbatim, with the unit regions clickable. |

`REPO` in both `alignment_data.py` and `ui/serve.py` resolves to `corpora/oai_math/` with no path
surgery, because the corpus root is also the Lake package root — so the version pin reads the real
`lean-toolchain` / `lake-manifest.json`.

## Differences from upstream

All three follow from this corpus having no `cf_extract` binary and no `proof-read` CLI:

* `C_F.available` (upstream: the depth-1 Lean constants of `T_F`, a read-only convenience list) stays
  empty. The hand-authored `C_F.items`, which is what actually gets linked, is unaffected.
* `/api/expand` and `/api/generate` (auto-draft) are gone, along with their buttons.
* `/api/overview` is new: the proof the left panel renders.

Three further UI changes, because the proof itself now does the navigating: the folder tree is gone
(a datapoint is reached by clicking the claim it is about), so `+ new` went with it — an ad-hoc
datapoint outside `align/` would be unreachable — and presentation mode is gone too.

Two smaller additions: `_SKIP_DIRS` gains `_gt`, so the datapoint walk can never descend into an
item's ground-truth proof (reading it is disqualifying contamination); and the labeler defines the
`\im` / `\rank` / `\R` macros, whose `\newcommand`s live in a paper preamble the excerpted `.tex` does
not carry. That is a rendering aid only — the stored `T_N` and the `S_N` offsets remain the verbatim
source. The proof panel renders no math at all: it shows the `.tex` as the proof quotes it.

A formula that an `S_N` span **cuts** is split at the span boundaries and each fragment typeset on its
own, so `$D_\tau=D+\tau e_s e_j^{\mathsf T}$` shows `D_\tau=` in one span's colour and the definition
in the other's. Upstream shades a formula only when a span *contains* it, which here hid a real label
in five of item1's nine segments — seg-1.3 and seg-1.5 are almost entirely a displayed equation, so
they showed nothing at all — and those cuts are the point: the prose puts the name on the left of the
`=` and the definition on the right. Selection stays atomic at fragment resolution, so the boundaries
you can drag to are exactly the ones already labelled; a fragment that will not parse on its own
sends the whole formula back to a single atomic node.

The **`S_N` cards typeset their text the same way**, and for the same reason: a card reading
`\in\im D_\tau,` or `the matrix\n$D_\tau=` is the hardest part of the page to read, and it is the part
you are reading to decide whether the edge beside it holds. The test is the span itself — a piece of
it lying inside a `$…$`, `$$…$$`, `\[…\]` or `\(…\)` **body** is typeset, prose is rendered as before,
and both are decided per *piece*, because item1's spans routinely straddle the boundary. Everything
degrades: a fragment KaTeX cannot parse falls back to its own source (shown monospaced), and
`__noKatex` skips the path entirely, so the worst case is exactly what the cards showed before. Two
consequences are deliberate — a typeset piece does not show the `$` / `\[` it replaced (the card's
hover title still carries the raw string, and `T_N` / `S_N` on disk are untouched: this is a rendering
choice, like the macros above), and display math is typeset inline rather than as a centred block,
because a card is one row in a column. A span that touches a formula without containing any of its
body — seg-1.5's `['\[', '\]']`, a real label on the presentation of a displayed equation — shows
those delimiters as themselves; it used to be joined into `\[ … \]` and handed to the markdown+math
renderer, which read the two delimiters as a formula and typeset the ellipsis between them.
