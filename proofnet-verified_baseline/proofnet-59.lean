import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that if $R$ is an integral domain and $x^{2}=1$ for some $x \in R$ then $x=\pm 1$.
-/

/-Informal Proof

Solution: If $x^2=1$, then $x^2-1=0$. Evidently, then,
$$
(x-1)(x+1)=0 .
$$
Since $R$ is an integral domain, we must have $x-1=0$ or $x+1=0$; thus $x=1$ or $x=-1$.
-/

theorem Dummit_Foote_exercise_7_1_11 {R : Type*} [CommRing R] [IsDomain R]
  {x : R} (hx : x^2 = 1) : x = 1 ∨ x = -1 := by
  -- Step 1: Turn the equation `x^2 = 1` into a factored product that equals zero.
  --         The classical identity `(x - 1) * (x + 1) = x^2 - 1` lets us connect
  --         our hypothesis with a product of two simpler factors.
  have hfactor : (x - 1) * (x + 1) = 0 := by
    -- Step 1.1: Rewrite the product into the difference of squares.
    --           The `ring` tactic carries out the algebraic expansion and simplification.
    calc
      (x - 1) * (x + 1) = x^2 - 1 := by ring
      -- Step 1.2: Replace `x^2` with `1` using `hx`, then simplify the arithmetic.
      _ = 0 := by simp [hx]
  -- Step 2: Use the integral-domain property (no zero divisors) to split the zero product.
  have hzero : x - 1 = 0 ∨ x + 1 = 0 := by
    -- In a domain, a product is zero only if one factor is zero.
    exact mul_eq_zero.mp hfactor
  -- Step 3: Translate each zero-factor case into the desired equalities for `x`.
  cases hzero with
  | inl h =>
      -- Step 3.1: From `x - 1 = 0`, deduce directly that `x = 1`.
      left
      exact sub_eq_zero.mp h
  | inr h =>
      -- Step 3.2: From `x + 1 = 0`, deduce that `x = -1`.
      right
      exact eq_neg_of_add_eq_zero_left h
