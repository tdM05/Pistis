import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

If $x, y$ are complex, prove that $||x|-|y|| \leq |x-y|$.
-/

/-Informal Proof

Since $x=x-y+y$, the triangle inequality gives
$$
|x| \leq|x-y|+|y|
$$
so that $|x|-|y| \leq|x-y|$. Similarly $|y|-|x| \leq|x-y|$. Since $|x|-|y|$ is a real number we have either ||$x|-| y||=|x|-|y|$ or ||$x|-| y||=|y|-|x|$. In either case, we have shown that ||$x|-| y|| \leq|x-y|$.
-/

theorem Rudin_exercise_1_13 (x y : ℂ) :
  |‖x‖ - ‖y‖| ≤ ‖x-y‖ := by
  -- Step 1: Use the triangle inequality on the decomposition x = (x - y) + y to bound ‖x‖.
  have h₁ : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    -- Step 1.1: Apply ‖a + b‖ ≤ ‖a‖ + ‖b‖ with a = x - y and b = y, rewriting algebraically.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      norm_add_le (x - y) y
  -- Step 2: Repeat the triangle inequality for y = (y - x) + x to relate ‖y‖ to ‖x - y‖.
  have h₂ : ‖y‖ ≤ ‖x - y‖ + ‖x‖ := by
    -- Step 2.1: Apply ‖a + b‖ ≤ ‖a‖ + ‖b‖ with a = y - x and b = x.
    have h₂base : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
      -- Step 2.1.1: This is another direct application of the triangle inequality after rewriting y.
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        norm_add_le (y - x) x
    -- Step 2.2: Use ‖y - x‖ = ‖x - y‖ to express everything in terms of ‖x - y‖.
    simpa [norm_sub_rev, add_comm] using h₂base
  -- Step 3: Convert the upper bound on ‖x‖ into the desired inequality ‖x‖ - ‖y‖ ≤ ‖x - y‖.
  have h₁' : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := (sub_le_iff_le_add).2 h₁
  -- Step 4: Convert the symmetric bound on ‖y‖ into the lower bound −‖x - y‖ ≤ ‖x‖ - ‖y‖.
  have h₂' : -‖x - y‖ ≤ ‖x‖ - ‖y‖ := by
    -- Step 4.1: Apply neg_le_neg to the inequality obtained from h₂ and simplify the resulting expression.
    have : ‖y‖ - ‖x‖ ≤ ‖x - y‖ := (sub_le_iff_le_add).2 h₂
    -- Step 4.2: Negate both sides and rewrite to express the bound in terms of ‖x‖ - ‖y‖.
    simpa [sub_eq_add_neg, add_comm, add_left_comm] using neg_le_neg this
  -- Step 5: Combine the two-sided bounds to conclude |‖x‖ - ‖y‖| ≤ ‖x - y‖ via the characterization of absolute value.
  exact abs_le.mpr ⟨h₂', h₁'⟩
