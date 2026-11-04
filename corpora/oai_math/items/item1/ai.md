# Notes on `_gt/MaxSupportKernel.lean`

Used only as a reference while filling `Main.lean`; two faithfulness gaps noticed in the GT proof
relative to the NL text (split.json), neither of which blocked the naive fill — both are silently
patched the same way in `Main.lean`'s own helpers.

1. **Segment 1.2 claims generality over τ that GT never formalizes.** The NL text says "for a
   nonzero real τ, the matrix D_τ = D + τ e_s e_j^T is still supported on T." GT skips the general-τ
   claim entirely: `range_lt_range_add_single` hard-codes the perturbation as
   `D + Matrix.single s j 1` (coefficient fixed to `1`), never introducing a τ variable. It proves
   only the τ = 1 instance, which is mathematically sufficient downstream but is not a formalization
   of the universally-quantified statement segment 1.2 actually asserts. (Our `Main.lean` keeps the
   general τ from the map stage and threads an arbitrary `τ ≠ 0` through steps 2–6, so it does not
   inherit this narrowing.)

2. **x_j ≠ 0 is used but never asserted as a step or assumption anywhere in split.json.** Segment
   1.4 ("Thus e_s ∈ im D_τ") implicitly needs x_j ≠ 0 to divide by τ·x_j and recover e_s from
   D_τ x = τ x_j e_s — but the only companion nonvanishing fact split.json records is y_s ≠ 0
   (wired as a `pistis_assumption` on segment 1.7). GT derives x_j ≠ 0 by contrapositive from the
   reductio hypothesis up front, outside any segment, i.e. it is not attached to the segment that
   actually needs it. This looks like a genuine small gap in the NL proof's own rigor (not a GT
   defect specifically), so we did the same derivation locally inside `step4.lean`'s helper rather
   than inventing a `pistis_assumption` the split stage didn't record.

No other discrepancies found; GT's overall rank/kernel argument matches the NL proof and all its
Mathlib lemma names resolve against this corpus's pinned mathlib commit.
