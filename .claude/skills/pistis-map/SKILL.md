---
name: pistis-map
description: >
  The MAP STAGE: turn an item's `split.json` into `Main.lean`'s claim types — one Lean claim per
  segment, a faithful restatement of what THAT segment asserts. ONE segment at a time, INTERACTIVELY,
  building + checking as you go, then STOP for human review. Prerequisite: `/pistis-split` produced a
  `split.json` that passes `check_split.py`. This is TRANSLATION, not proving (every body stays
  `:= by sorry`; proving is a later stage). Invoked with an item path, e.g. `/pistis-map proofnet_verified/item8`.
---

# Map stage — map each NL segment to a Lean claim type (TRANSLATION, not proving)

Your job: fill `<corpus>/item<N>/Main.lean` with a Lean claim type per segment — a faithful restatement
of what THAT segment asserts. You do this **one segment at a time**, building and checking as you go,
then **STOP for human review**. You do NOT prove (every body stays `:= by sorry`; proving is a later
stage).

**Prerequisite:** `/pistis-split` already ran → `<corpus>/item<N>/split.json` exists and passes
`python3 scripts/check_split.py <corpus>/item<N>`. If it doesn't, stop and run split first.

## STEP 0 — stamp the placeholder scaffold (deterministic; do this first)
```
python3 scripts/scaffold_main.py <corpus>/item<N>
```
This writes `Main.lean` reusing the item's `data/statement.lean` header + theorem signature VERBATIM,
then one `pistis_segment "<loc>" r"<text>" (stepN : True) := by sorry` per reasoning segment, the
`pistis_intro`/`pistis_conclude` structural markers, `pistis_assumption "<loc>" r"<substring>" (asmN
: True) := by sorry` tactics (seeded from each segment's `assumptions` set, sharing that segment's
`loc`), and a marked trailing `sorry -- @pistis_closer`. **The TEXT is copied from `split.json`, so
tiling is already byte-perfect — you must NEVER edit the segment text, locators, or ordering.** Your
whole job is to replace each `True` with a real claim — including each `pistis_assumption`'s own
`True` placeholder, with the real type of that premise — and the `@pistis_closer` line with the
real closing.

⛔ **The NL is a Lean RAW literal — `r"…"` (or `r#"…"#`). Leave the `r` and the delimiters alone.**
A raw literal has no escapes, so the file's bytes are the paper's bytes and `grep`/Ctrl-F for a
sentence of the proof finds it. Rewriting it as an ordinary `"…"` forces you to double every LaTeX
backslash (`\in` -> `\\in`); the decoded VALUE would still be right, so the coverage check would still
report "reproduces source exactly" while the file says something the paper never did. `check_main.py`
check 4 compares the BYTES and will fail you for it. Do not "fix" the quoting.

**Structural markers are ALREADY STAMPED for you** — you fill, you don't build the frame:
- A **`wts`** segment ("We claim / it suffices to show …") comes out as `pistis_wts "<loc>" r"<text>"` —
  no `True` slot, nothing to fill.
- A **reductio** (split's `reductio_open` / `contradiction` / `reductio_close` frames) comes out as a
  nested `have habsurd<k> : ¬(sorry) := by / intro hsuppose<k> / … / exact <False-step>` block, already
  indented, with the contradiction step's claim pre-set to `False`. **Fill the `¬(sorry)` with the real
  negated supposition and make the trailing reductio_close claim match it.** The script does NOT stamp
  `by_cases`/`rcases`/`wlog` — if the case structure needs one, you add it around the stamped block.

## ⛔ THE HARD RULES

**RULE 1 — ONE SEGMENT AT A TIME. NEVER one-shot the whole map.** Fill segments in order, one at a
time: write THIS segment's claim → BUILD / check → then the next. Batching all claims in one pass is what
produces the claim + dependency mistakes that surface late.

**RULE 2 — EVERY CLAIM IS NON-VACUOUS AND CONTAINS ONLY WHAT THE SEGMENT ASSERTS.**
- **No `True` / vacuous claim.** `True`, `x = x`, or any tautology is vacuous. Every reasoning segment
  asserts something — state THAT. (This guards the CLAIM slot `(stepN : …)` only. A trivially-true fact
  is fine as a `pistis_assumption`'s type — just not literally `True`, the scaffold's unfilled
  placeholder; see that section.)
- **⛔ NEVER RESTATE A GIVEN.** If your claim equals one of the theorem's hypotheses, it is VACUOUS: you
  have confused the segment's JUSTIFICATION for its ASSERTION. The claim is the NEW fact the segment
  states; the consumed given is a `pistis_assumption`. (This is the #1 real-world failure.)
- The `assumptions` set and the single `assert` in `split.json` already draw the assertion-vs-assumption
  line for you — the claim realizes the `assert`; each `assumptions` entry becomes a `pistis_assumption`.

**RULE 3 — FAITHFULNESS IS THE ONLY PRIORITY; DO NOT OPTIMIZE.**
- **Never collapse a claim** to a logically-equivalent shorter / cleaner / more-provable form. State
  literally what the segment says, even if redundant or verbose. Do NOT simplify to make proving easier —
  that is the prove stage's problem, not yours.
- **Assertion vs assumption.** The claim IS the segment's `assert`; a consumed premise is a
  `pistis_assumption`, never a conjunct of the claim, and the assertion is never hidden inside an
  assumption.
- **Negation placement (De Morgan).** For "X and Y do NOT …", the `∧` stays BETWEEN the parts and each
  `¬` sits on its OWN part — NEVER wrap a single `¬` around the whole conjunction (that flips `∧`→`∨`).
- **Comments are ONE line.** If a claim seems to need a multi-line comment, that is the signal to re-split
  the segment into atomic ones — not to write a long comment.

## VOCABULARY — anchor on the formal statement; read Mathlib as needed
There is no fixed vocabulary table (the target is all of Mathlib, not a small closed theory). Instead:
- **The formal statement (`data/statement.lean`) fixes this problem's idiom.** It already names the
  Mathlib concepts in play (`Ideal.span`, `Submodule`, `Polynomial ℤ`, `DifferentiableOn`, …). Write
  every intermediate claim in that SAME idiom, with the same types and notation.
- **Read Mathlib freely to find the right names/notation** — you may open Mathlib source, use
  `exact?` / `apply?` / `#check` / loogle / LeanSearchClient. The claim is a *type* (a `Prop`); you are
  choosing how to spell the segment's assertion in Mathlib, not proving it.
- **⛔ NEVER open the ground-truth proof** (`_source/*_gt.zip` / any baseline). The map must reflect the
  NL argument, not a pre-existing formal proof — reading it is contamination and defeats the point.
- If a segment's assertion genuinely cannot be expressed in the statement's types, that is a signal the
  split was too coarse (re-split) or a real modelling gap (STOP and report) — not license to invent.

## STRUCTURAL FRAMES — you EDIT Main's SHAPE, not just fill `True` slots
Filling a claim is usually a one-liner, but some proofs require RESTRUCTURING `Main.lean`. That is your
job, done faithfully.

### ⚠ UNDERSTAND THE ARGUMENT FIRST — frames are consequences, not keyword triggers
Before choosing ANY Lean structure (`by_contra`, `have … := by intro h`, `rcases`, `by_cases`, `wlog`,
`pistis_wts`), READ THE WHOLE PROOF and understand what it is SEMANTICALLY doing. The Lean structure is a
CONSEQUENCE of that understanding, not triggered by spotting a phrase. "Suppose for contradiction" is not
a mechanical signal — ask what the argument's overall shape is, where each hypothesis is in scope, and
what is asserted after a sub-argument closes.

- **Reductio / `by_contra`** — the scaffold stamps the `have habsurd : ¬(sorry) := by intro hsuppose …`
  frame from split's reductio frames; fill the `¬(…)` with the real negated supposition and make the
  `reductio_close` claim match. When the GOAL ITSELF is a negation, you may instead `intro` it and drive
  to `False` directly. A "… is not …" segment is STILL A REAL ASSERTION — give it a `¬(…)` claim, do not
  drop it to `pistis_wts`.
- **Case-split** — `rcases`/`by_cases`/`wlog`, one branch per case; a symmetric case via `wlog` or a
  mirrored structure. Add it around the relevant segments.
- **Mid-proof "we claim / it suffices to show …"** — the goal-announcement segment is already stamped
  `pistis_wts "loc" r"text"` (structural, no claim, no node, legal mid-proof). It ANNOUNCES the goal; it is
  not an assertion that the goal is already proven. The goal is established by the segments that FOLLOW it
  and assembled by the closing. ⛔ Do NOT re-map a `wts` as a `pistis_segment` carrying the goal body.

## Closing the goal — the ONLY places a `sorry` may appear
A `sorry` is allowed in EXACTLY two slots: a `pistis_segment "…" r"…" (stepN : …) := by sorry` body, or a
`have <n> : <claim> := by sorry`. **A `sorry` ANYWHERE ELSE is a STRAY sorry and is a hard error** — in
particular the scaffold's trailing `sorry -- @pistis_closer` line is a PLACEHOLDER you MUST replace: a
finished map has NO stray sorry.
- Replace `@pistis_closer` with the real closing that discharges the goal from the step claims —
  `exact <laststep>` when the last claim IS the goal, or `refine ⟨…⟩` / `exact ⟨…⟩` assembling the goal's
  components from named steps. If a goal component is a side-condition asserted by no segment, discharge it
  as its OWN `have <n> : <side-cond> := by sorry` (a legal body-sorry), then reference it — NEVER inline
  `by sorry` inside a tail `exact ⟨…, by sorry, …⟩`.
- Every `have … := by sorry` you add for a bridging/side fact is a legal deferred node (proved in the
  prove stage), NOT a stray sorry.

## `pistis_assumption` (INPUTS-ONLY)
Each `pistis_assumption "<loc>" r"<substring>" (asmN : True) := by sorry` tactic the scaffold seeded
(sharing its segment's `<loc>`) marks a prior fact this segment CONSUMES (from split's `assumptions`
set). Replace the `True` placeholder with the Lean type of that fact — the exact form of the
hypothesis it becomes; leave the body `:= by sorry` (proving is a later stage, same as a segment's
own claim). These types are LOAD-BEARING (a later fill stage proves each `pistis_assumption`'s body,
materializing it as a `have`, and a checker HARD-FAILS if one is dropped or retyped), so get the
type right.
- **INPUTS-ONLY:** a `pistis_assumption` is a fact the step consumes — NOT a conjunct of the step's
  own claim. If a seeded substring is actually the assertion, delete that tactic. When in doubt, drop it.
- **Trivially-true inputs are OK here** (unlike claims): a definitional / trivially-true consumed input is
  allowed and is often the faithful choice (it makes explicit that a hypothesis was consumed) — just
  not literally `True`, which is the unfilled-placeholder sentinel.

## ⛔ OUTSIDE-SOURCE BUG → STOP AND REPORT (do NOT silently "fix" it)
A discrepancy while mapping is one of two things:
- **OUR bug → fix it, quietly.** The map is unfaithful: an invented fact, a claim that restates a given,
  a mis-modelled object. Re-derive from the segment.
- **A genuine OUTSIDE-SOURCE bug → STOP + REPORT.** A real error in the NL proof or its formal statement
  (the argument asserts something false or inconsistent, the statement is mis-formalized). Do NOT paper
  over it: never edit the segment text, never weaken the claim to go green, never invent a workaround.
  Tell the human with the evidence and let THEM decide.

## PROCEDURE (one segment at a time)
1. STEP 0 (stamp the scaffold). Read `split.json` (the `assumptions`/`assert` of each segment) and
   `data/statement.lean` (the formal statement — the vocabulary anchor).
2. For each segment IN ORDER:
   a. Replace its `(stepN : True)` with the real claim (RULE 2/3; write it in the statement's Mathlib
      idiom). For a segment needing a **frame** (reductio / case-split), add the frame; bodies stay
      `:= by sorry`.
   b. Fill any `pistis_assumption`'s `True` placeholder on that segment (INPUTS-ONLY).
   c. Keep going — do NOT one-shot. When a small batch is filled, BUILD (see gate).
3. **HARD GATE — you may NOT finish until ALL of these pass. Loop: fix → re-run → repeat.**
   - `lake env lean <corpus>/item<N>/Main.lean` → **must succeed** (Main ELABORATES — which now also
     typechecks every `pistis_assumption`'s type immediately; only expected `declaration uses 'sorry'`
     warnings from the `:= by sorry` bodies remain — and the `@pistis_closer` line must be GONE,
     replaced by the real closing).
   - `python3 scripts/check_main.py <corpus>/item<N>` → **must exit 0** — perfect tiling, **ZERO
     `True`** on any segment OR assumption, no stray sorry, and check 5: every `assumptions` entry in
     `split.json` is still a `pistis_assumption` on its segment, none deleted and none invented.
   - `python3 scripts/check_signatures.py <corpus>/item<N>` → **must exit 0** — Main's theorem signature
     still equals the frozen `data/statement.lean` (you did NOT weaken the statement).
4. Run the SELF-REVIEW (below); fix anything; re-run the gate (still all green).
5. **STOP for human review — only once the gate passes.** The human confirms each claim honestly captures
   its segment, then runs `python3 scripts/check_steps.py --save <corpus>/item<N>` to freeze the approved
   claim + assumption types. Proving is the next stage.

## SELF-REVIEW (before you stop)
  □ No `True` and no vacuous/tautological claim on any reasoning segment; only intro/wts/conclusion carry
    none. Reductio contradiction → `False`; a negation → `¬ …`.
  □ **No claim RESTATES A GIVEN** — that is the assertion-vs-justification confusion; the given belongs in
    `pistis_assumption`.
  □ Every `pistis_assumption`: substring is verbatim from the segment, type is a genuine consumed INPUT
    (not a conjunct of this step's own claim); no `True` placeholder left, body is `:= by sorry`.
  □ ⛔ **You DELETED no `pistis_assumption`.** Deleting one and making its premise an extra
    conjunct of the claim is the one Atomicity break the older checks could not see — the text still
    tiles, the claim is not `True` — and `oai_math/item1` segment 1.7 shipped that way (before
    `pistis_assumption` was a tactic). "A claim carrying only the conclusion leaves the premises with
    nothing to align against" is NOT a reason: an assumption's formalization is its own TYPE, which
    is where it gets judged. Check 5 now fails you for it. Delete a `pistis_assumption` ONLY if the
    seeded substring is the segment's ASSERT, and then `split.json` is what is wrong — stop and
    report it, do not edit around it.
  □ Claims are written in the formal statement's Mathlib idiom (same types/notation).
  □ **NO stray sorry** — the `@pistis_closer` line is replaced; every remaining `sorry` sits in a
    `pistis_segment` body or a `have := by sorry`; none in a tail `exact`/term.
  □ You did NOT edit any segment's text / locator / ordering (Step-0 scaffold owns tiling), and every
    NL literal is still a RAW `r"…"` / `r#"…"#` (never re-quoted as `"…"` with doubled backslashes).
  □ You did NOT touch the theorem signature (it must still equal `data/statement.lean`).
  □ You did NOT read the ground-truth / baseline proof.

## WHAT YOU DO NOT DO
- Do NOT prove (leave `:= by sorry`; no real tactic bodies).
- Do NOT touch the theorem signature, or any segment's text / locator / ordering.
- Do NOT open the ground-truth / baseline proof (contamination).
- Do NOT invent facts a segment didn't state, or collapse a claim to a cleaner/easier form.
- Do NOT leave a stray `by sorry` in a tail term — the only sorry slots are a `pistis_segment` body or a
  `have := by sorry`.
