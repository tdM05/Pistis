import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

If $r$ is rational $(r \neq 0)$ and $x$ is irrational, prove that $rx$ is irrational.
-/

/-Informal Proof

If $r x$ were rational, then $x=\frac{r x}{r}$ would also be rational.
-/

theorem Rudin_exercise_1_1b
(x : ℝ)
(y : ℚ)
(h : y ≠ 0)
: ( Irrational x ) -> Irrational ( x * y ) := by
  -- Step 1: Introduce the hypothesis `hx : Irrational x` because we are proving an implication.
  intro hx
  -- Step 2: Record separately that the rational multiplier `y` is nonzero; this matches the input
  -- Step 2.1: The Mathlib lemma `Irrational.mul_ratCast` needs a named proof that the factor ≠ 0.
  -- Step 2.2: We reuse the assumption `h` but store it in `hy` to emphasize its later use.
  have hy : y ≠ 0 := h
  -- Step 3: Apply `Irrational.mul_ratCast`, which states that scaling an irrational real number by a
  -- Step 3.1: nonzero rational keeps it irrational; here `hx` provides the irrational number.
  -- Step 3.2: Feeding the nonzero witness `hy` yields precisely the target `Irrational (x * y)`.
  exact hx.mul_ratCast hy
