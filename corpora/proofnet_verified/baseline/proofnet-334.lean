import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Prove that no order can be defined in the complex field that turns it into an ordered field.
-/

/-Informal Proof

By Part (a) of Proposition $1.18$, either $i$ or $-i$ must be positive. Hence $-1=i^2=(-i)^2$ must be positive. But then $1=(-1)^2$, must also be positive, and this contradicts Part $(a)$ of Proposition 1.18, since 1 and $-1$ cannot both be positive.
-/

theorem Rudin_exercise_1_8 : ¬ ∃ (r : ℂ → ℂ → Prop), IsLinearOrder ℂ r := by
  sorry

/-
Explanation of falsity:
The informal claim fails because we can order `ℂ` lexicographically:
declare `z ≤ w` when `z.re < w.re` or when the real parts agree and `z.im ≤ w.im`.
This relation is a linear order since it is exactly the pullback of the standard
lexicographic order on `ℝ × ℝ`, so the original `¬ ∃` statement is false.
-/

/-- Lexicographic (pullback) relation on `ℂ`. -/
def complexLexRel (z w : ℂ) : Prop :=
  toLex (z.re, z.im) ≤ toLex (w.re, w.im)

/--
The inclusion map from `ℂ` into `ℝ ×ₗ ℝ` is a relation embedding for `complexLexRel`.
-/
def complexLexEmbedding : complexLexRel ↪r (fun x y : ℝ ×ₗ ℝ => x ≤ y) := by
  -- Step 1: Package the map `z ↦ toLex (z.re, z.im)` as an embedding.
  refine
    { toEmbedding :=
        { toFun := fun z => toLex (z.re, z.im)
          inj' := ?_ }
      map_rel_iff' := ?_ }
  · -- Step 2: Show injectivity by comparing the underlying real/imaginary pairs.
    -- Step 2.1: Assume the lex-coded pairs coincide.
    intro z w h
    -- Step 2.2: Convert equality in `ℝ ×ₗ ℝ` to equality of ordered pairs in `ℝ × ℝ`.
    have hpair : (z.re, z.im) = (w.re, w.im) := by
      simpa using (toLex_inj.mp h)
    -- Step 2.3: Extract the two coordinate equalities and finish by `Complex.ext`.
    have hre : z.re = w.re := congrArg Prod.fst hpair
    have him : z.im = w.im := congrArg Prod.snd hpair
    exact Complex.ext hre him
  · -- Step 3: Identify the relation on `ℂ` with the pulled-back order relation.
    -- Step 3.1: The relation equality holds definitionally.
    intro z w
    rfl

/--
There does exist a linear order on `ℂ`; the lexicographic one witnesses the negation
of the original (false) statement.
-/
theorem Rudin_exercise_1_8_neg : ∃ (r : ℂ → ℂ → Prop), IsLinearOrder ℂ r := by
  -- Step 1: Choose the lexicographic relation as the candidate order.
  refine ⟨complexLexRel, ?_⟩
  -- Step 2: Transfer the known linear order on `ℝ ×ₗ ℝ` via the embedding.
  exact (complexLexEmbedding).isLinearOrder

/--
There is no way to make `ℂ` into a strict ordered ring (and therefore no ordered field).
-/
theorem Rudin_exercise_1_8_corrected :
    ¬ (∃ inst : LinearOrder ℂ, by
      let _ : LinearOrder ℂ := inst
      exact IsStrictOrderedRing ℂ) := by
  -- Step 1: Assume there is a compatible linear order and strict ordered ring structure.
  rintro ⟨instLO, hStrict⟩
  classical
  -- Step 2: Activate the assumed structures so we can use the usual ordered-ring lemmas.
  letI : LinearOrder ℂ := instLO
  haveI : IsStrictOrderedRing ℂ := hStrict
  -- Step 3: Show that `I²` is strictly positive by splitting on the sign of `I`.
  have hIne : Complex.I ≠ 0 := Complex.I_ne_zero
  have hpos : (0 : ℂ) < Complex.I * Complex.I := by
    -- Step 3.1: Either `I` is negative or positive, and both give a positive square.
    have hcases : Complex.I < 0 ∨ 0 < Complex.I := lt_or_gt_of_ne hIne
    -- Step 3.2: Dispatch the two sign cases.
    cases hcases with
    | inl hlt =>
        -- Step 3.2.1: If `I < 0`, then `-I > 0` and its square equals `I²`.
        have hneg : (0 : ℂ) < -Complex.I := neg_pos.mpr hlt
        have hmul : (0 : ℂ) < (-Complex.I) * (-Complex.I) := mul_pos hneg hneg
        simpa [neg_mul_neg] using hmul
    | inr hgt =>
        -- Step 3.2.2: If `0 < I`, its square is directly positive.
        have hmul : (0 : ℂ) < Complex.I * Complex.I := mul_pos hgt hgt
        simpa using hmul
  -- Step 4: Translate `I² = -1` into an inequality about `-1`.
  have hlt : (0 : ℂ) < -1 := by
    simpa [Complex.I_mul_I] using hpos
  -- Step 5: Translate `0 < 1` into `-1 < 0` by adding `-1` to both sides.
  have hneg : -1 < (0 : ℂ) := by
    -- Step 5.1: `0 < 1` holds in any strict ordered ring.
    have h1 : (0 : ℂ) < 1 := zero_lt_one
    -- Step 5.2: Derive `-1 < 0` by linear arithmetic.
    linarith
  -- Step 6: Combine the inequalities to reach the contradiction `0 < 0`.
  exact (lt_irrefl (0 : ℂ)) (hlt.trans hneg)
