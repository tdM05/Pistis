# Paper plan — leveled faithfulness detector

Notes from the Nov 27 discussion. Companion to `../llm_baseline_levels.md`.

## The one axis that matters: precision vs level
- NUM (count of unfaithfulness found) **already rises with level** — observed, not a question.
- So the whole study reduces to **precision(level)**. Everything hinges on how precision moves as we go deeper.
- "Optimal N" is therefore **the deepest level whose precision is still acceptable** — not a precision-maximizing N. Deeper = more true bugs found, as long as precision holds; the cost is human-review effort (~10^(l-1)·2).

## Two outcomes, two papers (decide later, same experiments)
- **Precision stays acceptable → TOOL paper.** The leveled detector works. Eval + artifact are the contribution. Levels is a small-but-real generalization of faithalign (whole-paper vs single-claim); conceptual delta is modest and that's fine for a tool paper — value is "works at scale, finds real bugs, beats naive LLM."
- **Precision too low → REGULAR paper.** This pipeline becomes the baseline/diagnostic; the contribution is the new method layered on top to fix precision (headline = the insight).
- Same experiments decide which. Don't commit now — read the precision curve first.

## Evaluation stance
- **Precision only, via human eval.** Recall needs full ground-truth error sets = infeasible for new results. That's a deliberate, defensible choice for a *detector* (fuzzers / static analyzers / test-gen report precision + bug count, not recall).
- **NUM = relative-recall proxy.** "Deeper finds strictly more real errors" = lower bound / relative recall. Never claim absolute recall.
- **Terminology:** do NOT call precision "soundness" (reserved in FM). Say **high-precision detector / low false-discovery / no crying wolf**.
- Pre-empt the two reviewer questions up front: (1) ground truth → human eval for precision; (2) false negatives → relative-recall-via-NUM, positioned as triage not a verifier.

## Likely Case-B mechanism (if precision drops at depth)
- The `mustMap` rule (formal leaf with empty Lean map ⇒ notok) probably over-fires at depth: tiny fragments legitimately don't map to their own decl (scaffolding, clause folded into a binder type) → spurious notok → precision falls.
- This is a labeling artifact, not "the idea is bad." Relaxing / adding a confirmation pass is the obvious "method on top" for the regular-paper branch.

## RQ simplifications (what we decided NOT to build)
- **Per-call thinking budget cap: not needed.** Capping per call doesn't isolate anything (deeper levels have *smaller* context per call; the extra compute is in # calls = the method itself). The real "is it just more compute?" control is giving the flat baseline a **matched total budget** → that's the agentic harness, already built.
- **RQ4 (more rounds) + RQ5 (less context/round) collapse** into one question: *does forced decomposition (levels) beat a free agent that stops when it thinks it's done?* Agentic mode operationalizes the free agent. So: agentic ≈ level N → structure adds nothing; level N > agentic → forced tiling matters.
- Drop the dedicated subagent/free-split and budget-knob variants.

## State of implementation
- Built: levels 0/1/2 (split → categorize → judge), errors as a one-sentence list, per-level error count, `--mode headless|agentic` (+ `--lean-build`), transcript/manifest metadata, viewer.
- Remaining work is **not code**: (1) run on **several papers** (one item can't carry either paper — this is the gating task), (2) **human eval** for precision.
