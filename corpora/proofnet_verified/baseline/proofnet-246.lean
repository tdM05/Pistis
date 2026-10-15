import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Let $R$ be a commutative ring with $1 \neq 0$. Prove that if $a$ is a nilpotent element of $R$ then $1-a b$ is a unit for all $b \in R$.
-/

/-Informal Proof

$\mathfrak{N}(R)$ is an ideal of $R$. Thus for all $b \in R,-a b$ is nilpotent. Hence $1-a b$ is a unit in $R$.
-/

theorem Dummit_Foote_exercise_7_4_27 {R : Type*} [CommRing R] (hR : (0 : R) ≠ 1)
  {a : R} (ha : IsNilpotent a) (b : R) :
  IsUnit (1-a*b) := by
  -- Step 1: Turn the nilpotency hypothesis on `a` into concrete data `n` with `a ^ n = 0`.
  obtain ⟨n, hn⟩ := ha
  -- Step 1.1: Handle the edge case where the witness `n` could be zero by using the nontriviality hypothesis.
  by_cases hzero : n = 0
  · -- Step 1.1.1: In the degenerate case, the equation `a ^ n = 0` becomes `1 = 0`, contradicting `hR`.
    have hcontr : (1 : R) = 0 := by simpa [hzero] using hn
    -- Step 1.1.2: Close the impossible branch by deriving false from `hR`.
    exact (hR hcontr.symm).elim
  · -- Step 2: Work with the meaningful exponent `n` (which is now known to be nonzero).
    have hnil : IsNilpotent (a * b) := by
      -- Step 2.1: Exhibit the power `n` of `a * b` and prove it is zero.
      refine ⟨n, ?_⟩
      -- Step 2.1.1: Expand `(a * b) ^ n` into `a ^ n * b ^ n` using the multiplicative power rule.
      -- Step 2.1.2: Substitute the equality `a ^ n = 0` from `hn` so the product collapses to zero.
      simp [mul_pow, hn]
    -- Step 3: Apply the lemma stating that `1 - x` is a unit whenever `x` is nilpotent.
    -- Step 3.1: Directly invoke `IsNilpotent.isUnit_one_sub` with `x = a * b`.
    simpa using hnil.isUnit_one_sub
