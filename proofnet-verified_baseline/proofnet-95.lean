import Mathlib

open Real
open scoped BigOperators



/-Informal Statement

Show that 2 is divisible by $(1+i)^{2}$ in $\mathbb{Z}[i]$.
-/

/-Informal Proof

We have $(1+i)^2=1+2 i-1=2 i$, so $2=-i(1+i)^2$.
-/

theorem Ireland_Rosen_exercise_1_31  : (⟨1, 1⟩ : GaussianInt) ^ 2 ∣ 2 := by
  -- Step 1: Choose the prospective quotient witnessing the divisibility; we take -i = ⟨0, -1⟩.
  refine ⟨⟨0, -1⟩, ?_⟩
  -- Step 2: Show that ((1 + i)^2) * (-i) equals 2 by comparing real and imaginary parts.
  -- Step 2.1: Expand (1 + i)^2 into (1 + i) * (1 + i) to make the product explicit.
  -- Step 2.2: Multiply the resulting Gaussian integer ⟨0, 2⟩ by ⟨0, -1⟩ and simplify the coordinates.
  -- Step 2.3: Verify that the real and imaginary parts match those of 2 using the `ext` principle.
  ext <;> simp [pow_two]
