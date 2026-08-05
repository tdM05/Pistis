import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Let $x$ be an element of $G$. Prove that if $|x|=n$ for some positive integer $n$ then $x^{-1}=x^{n-1}$.
-/

/-Informal Proof

We have $x \cdot x^{n-1}=x^n=1$, so by the uniqueness of inverses $x^{-1}=x^{n-1}$.
-/

theorem Dummit_Foote_exercise_1_1_17 {G : Type*} [Group G] {x : G} {n : ℕ+}
  (hxn: orderOf x = n) :
  x⁻¹ = x ^ (n - 1 : ℕ) := by
  -- Step 1: Translate the order information into a concrete power identity.
  have hxpow : x ^ (n : ℕ) = (1 : G) := by
    -- Step 1.1: The definition of `orderOf` ensures `x ^ orderOf x = 1`.
    --          Rewrite the exponent using the hypothesis.
    simpa [hxn] using (pow_orderOf_eq_one x)
  -- Step 2: Record the arithmetic fact that `(n - 1) + 1 = n` for positive `n`.
  have hsucc : (n - 1 : ℕ) + 1 = (n : ℕ) := by
    -- Step 2.1: Use `Nat.succ_pred_eq_of_pos` and the positivity of `n`.
    --          Convert `Nat.pred` and `Nat.succ` to subtraction/addition form.
    simpa [Nat.succ_eq_add_one, Nat.pred_eq_sub_one] using
      (Nat.succ_pred_eq_of_pos (show 0 < (n : ℕ) from n.pos))
  -- Step 3: Show that `x ^ (n - 1)` is a right inverse of `x`.
  have hxleft : x ^ (n - 1 : ℕ) * x = (1 : G) := by
    -- Step 3.1: Rewrite the target exponent using the numerical identity from Step 2.
    have hxcalc : x ^ ((n - 1 : ℕ) + 1) = (1 : G) := by
      -- Step 3.1.1: Substitute the equality `(n - 1) + 1 = n` into `hxpow`.
      simpa [hsucc] using hxpow
    -- Step 3.2: Convert `x ^ ((n - 1) + 1)` into `x ^ (n - 1) * x` with `pow_succ`.
    simpa [pow_succ] using hxcalc
  -- Step 4: Convert the right-inverse property into the desired explicit inverse.
  have hxinv : x ^ (n - 1 : ℕ) = x⁻¹ := by
    -- Step 4.1: Multiply the identity from Step 3 on the right by `x⁻¹` and simplify.
    calc
      x ^ (n - 1 : ℕ)
          = x ^ (n - 1 : ℕ) * 1 := by
            -- Step 4.1.1: Insert the neutral element.
            simp
      _ = x ^ (n - 1 : ℕ) * (x * x⁻¹) := by
            -- Step 4.1.2: Replace `1` with `x * x⁻¹`.
            simp
      _ = (x ^ (n - 1 : ℕ) * x) * x⁻¹ := by
            -- Step 4.1.3: Reassociate the product to expose `x ^ (n - 1) * x`.
            simp [mul_assoc]
      _ = 1 * x⁻¹ := by
            -- Step 4.1.4: Substitute the right-inverse identity from Step 3.
            simp [hxleft]
      _ = x⁻¹ := by
            -- Step 4.1.5: Remove the neutral element on the left.
            simp
  -- Step 5: Symmetrize the equality to match the statement.
  exact hxinv.symm
