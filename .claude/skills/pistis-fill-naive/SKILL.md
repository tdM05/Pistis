---
name: pistis-fill-naive
description: >
  NAIVE fill stage: fill every `:= by sorry` in a mapped `Main.lean` so it builds with ZERO sorry,
  in a REQUIRED per-segment backing-file structure — one lemma file per `pistis_segment`, Main
  delegating to it and supplying every hypothesis via `pistis_assumption`. No search strategy, no
  decomposition heuristics: just the fixed structure + prove each lemma. Invoked with an item path,
  e.g. `/pistis-fill-naive proofnet_verified/item8`.
---

# Naive fill stage — fill every sorry in the required backing-file structure

Fill every `:= by sorry` in `<corpus>/item<N>/Main.lean` so the file builds with **ZERO sorry**.

## ⛔ DO NOT CHANGE (the map stage's frozen output)
- Do NOT change the theorem statement/signature.
- Do NOT change any `(stepN : CLAIM)` claim type.
- Do NOT change any `-- @pistis_assumption ("TEXT", TYPE)` line, or any segment's text/locator/order.
- Do NOT read the ground-truth / baseline proof (`_source/*_gt.zip`) — contamination, disqualifying.
Anything the source proof cites, cite in Lean too (import the Mathlib lemma or a prior item's theorem).

## REQUIRED STRUCTURE (this is CHECKED — do NOT prove any segment inline)
For each `pistis_segment "…" "…" (stepK : CLAIM) := by sorry` in `Main.lean`:

1. **Create a new file `<corpus>/item<N>/stepK.lean`** holding ONE lemma that proves that step,
   taking whatever facts it needs as hypotheses:
   ```
   import Mathlib
   import Pistis

   theorem helper_<itemname>_stepK (o1 o2 … : …) (h1 : TYPE1) (h2 : TYPE2) … : CLAIM := by
     <proof>
   ```
   `<itemname>` is the item's theorem name (from `data/statement.lean` / `meta.json`), e.g.
   `Artin_exercise_2_2_9`, so the helper is `helper_Artin_exercise_2_2_9_step1`. The proof may use any
   Mathlib tactic (`simp`, `linarith`, `nlinarith`, `omega`, `aesop`, `decide`, `exact?`-found lemmas,
   term mode, …); a helper may itself decompose with further `have`s if needed, but the top-level
   per-segment file is REQUIRED.

2. **Add `import <corpus-module>.item<N>.stepK`** at the top of `Main.lean` (the module path for the
   corpus lean_lib; alongside the existing `import Mathlib` / `import Pistis`).

3. **Make Main's body delegate**, supplying EVERY hypothesis via `pistis_assumption` with its type
   shown — EXACTLY `(by pistis_assumption "TEXT" (show TYPE; assumption))`, NEVER a bare
   `(by assumption)`:
   - If a hypothesis corresponds to a `-- @pistis_assumption ("NL-TEXT", TYPE)` line above the segment,
     use that **NL-TEXT verbatim** as the string (so it is clear WHERE that cited fact is used).
   - For every other (plumbing) hypothesis, use the empty string `""`.

   Schematic — in `Main.lean`:
   ```
   -- @pistis_assumption ("the cited NL fact", TYPE1)
   pistis_segment "…" "…"
     (stepK : CLAIM) := by
       exact helper_<itemname>_stepK o1 o2
         (by pistis_assumption "the cited NL fact" (show TYPE1; assumption))
         (by pistis_assumption "" (show TYPE2; assumption))
   ```
   and in `stepK.lean`:
   ```
   theorem helper_<itemname>_stepK (o1 … : …) (h1 : TYPE1) (h2 : TYPE2) : CLAIM := by <proof>
   ```
   (Use `exact` or `apply`/`refine` — whatever delivers the helper's conclusion to `stepK`'s claim.
   If a coercion mismatch arises, `exact_mod_cast` is fine.)

## THE CLOSER AND OTHER SORRY SLOTS
- Replace the scaffold's `sorry -- @pistis_closer …` line with the real closing that discharges the
  goal from the step results (`exact <laststep>`, or `refine ⟨…⟩` assembling components).
- A structural `pistis_intro` / `pistis_wts` / `pistis_conclude` has no body to fill.
- After filling, there must be **NO `sorry` anywhere** — not in Main, not in any `stepK.lean`. (A
  `have … := by sorry` left behind is a failure here; this is the fill stage, everything closes.)

## PROCEDURE
1. Read `Main.lean`. For each `pistis_segment … (stepK : CLAIM) := by sorry`, in order:
   a. Create `stepK.lean` with `helper_<itemname>_stepK`, binders = the objects + every hypothesis the
      proof consumes (each `@pistis_assumption` fact is a hypothesis binder), conclusion = `CLAIM`.
   b. Prove the lemma (any Mathlib tactics). Build the ONE file to check it:
      `lake env lean <corpus>/item<N>/stepK.lean`.
   c. Add the `import …stepK` to Main and rewrite the segment body to delegate per (3) above.
2. Replace the `@pistis_closer` line with the real closing.
3. **HARD GATE — you may NOT finish until BOTH pass:**
   - `lake env lean <corpus>/item<N>/Main.lean` → builds with ZERO sorry (no sorry warnings).
   - `python3 scripts/check_backing.py <corpus>/item<N>` → exit 0 (every segment delegates to its own
     `stepK.lean`; every hypothesis is a `pistis_assumption "…" (show TYPE; …)`, never bare
     `(by assumption)`; every `@pistis_assumption` NL-TEXT consumed verbatim).
   Also confirm the map-stage guards still hold: `python3 scripts/check_main.py <corpus>/item<N>`
   (tiling + claims unchanged) and `python3 scripts/check_signatures.py <corpus>/item<N>` (statement
   unchanged).
   Loop: fix → re-run → repeat until all green.

## WHAT YOU DO NOT DO
- Do NOT prove a segment inline in `Main.lean` — every segment delegates to its own `stepK.lean`.
- Do NOT use a bare `(by assumption)` — always `(by pistis_assumption "TEXT" (show TYPE; assumption))`.
- Do NOT change the statement, any claim type, or any `@pistis_assumption` line.
- Do NOT leave any `sorry`. Do NOT read the baseline/GT proof. Do NOT use git.
