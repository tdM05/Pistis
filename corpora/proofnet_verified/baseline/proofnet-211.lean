import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove the the operation $\star$ on $\mathbb{Z}$ defined by $a\star b=a-b$ is not commutative.
-/

/-Informal Proof

Not commutative since
$$
1 \star(-1)=1-(-1)=2
$$
$$
(-1) \star 1=-1-1=-2 .
$$
-/

theorem Dummit_Foote_exercise_1_1_2a : ∃ a b : ℤ, a - b ≠ b - a := by
  -- Step 1: Exhibit explicit integers witnessing the failure of commutativity.
  refine ⟨1, -1, ?_⟩
  -- Step 2: Compute `1 - (-1)` to understand the left-to-right operation order.
  have h_left : (1 : ℤ) - (-1) = 2 := by
    -- Step 2.1: Simplify the subtraction by converting to addition.
    simp
  -- Step 3: Compute `(-1) - 1` to understand the right-to-left order.
  have h_right : (-1 : ℤ) - 1 = -2 := by
    -- Step 3.1: Simplify again, now in the reversed order.
    simp
  -- Step 4: Use the computed values to rule out equality between the two orders.
  have h_goal : (1 : ℤ) - (-1) ≠ (-1 : ℤ) - 1 := by
    -- Step 4.1: Assume equality for contradiction.
    intro h
    -- Step 4.2: Translate the assumed equality into the simpler numeral equation `2 = -2`.
    have : (2 : ℤ) = -2 := by
      -- Step 4.2.1: Chain the equalities `2 = 1 - (-1) = (-1) - 1 = -2`.
      calc
        (2 : ℤ)
            = (1 : ℤ) - (-1) := by simp
        _ = (-1 : ℤ) - 1 := h
        _ = -2 := by simp
    -- Step 4.3: Contradict the impossible equality `2 = -2`.
    exact (by decide : (2 : ℤ) ≠ -2) this
  -- Step 5: The derived inequality matches the witness requirement, finishing the proof.
  exact h_goal
