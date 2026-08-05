import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Prove that if $x^{2}=1$ for all $x \in G$ then $G$ is abelian.
-/

/-Informal Proof

Solution: Note that since $x^2=1$ for all $x \in G$, we have $x^{-1}=x$. Now let $a, b \in G$. We have
$$
a b=(a b)^{-1}=b^{-1} a^{-1}=b a .
$$
Thus $G$ is abelian.
-/

theorem Dummit_Foote_exercise_1_1_25 {G : Type*} [Group G]
  (h : ∀ x : G, x ^ 2 = 1) : ∀ a b : G, a*b = b*a := by
  -- Step 1: Introduce arbitrary elements `a` and `b` of the group.
  intro a b
  -- Step 2: Prove that every element is its own inverse under the given hypothesis.
  have h_inv_general : ∀ x : G, x⁻¹ = x := by
    -- Step 2.1: Fix an arbitrary element `x`.
    intro x
    -- Step 2.2: Rewrite the square condition `x ^ 2 = 1` as a product equality.
    have hx_sq : x * x = (1 : G) := by
      -- Step 2.2.1: Expand the square using `pow_two` and apply the assumption.
      simpa [pow_two] using h x
    -- Step 2.3: Multiply the equation on the left by `x⁻¹` to isolate the inverse.
    calc
      x⁻¹ = x⁻¹ * 1 := by
        -- Step 2.3.1: Introduce the neutral element on the right.
        simp
      _ = x⁻¹ * (x * x) := by
        -- Step 2.3.2: Substitute `1` with `x * x` using the square relation.
        simp [hx_sq.symm]
      _ = (x⁻¹ * x) * x := by
        -- Step 2.3.3: Reassociate the triple product.
        simp
      _ = 1 * x := by
        -- Step 2.3.4: Collapse the inverse pair `x⁻¹ * x` to `1`.
        simp
      _ = x := by
        -- Step 2.3.5: Remove the left neutral element.
        simp
  -- Step 3: Record the specific square relations for `a` and `b`.
  have ha_sq : a * a = (1 : G) := by
    -- Step 3.1: Apply the hypothesis to `a`.
    simpa [pow_two] using h a
  have hb_sq : b * b = (1 : G) := by
    -- Step 3.2: Apply the hypothesis to `b`.
    simpa [pow_two] using h b
  -- Step 4: Translate the helper result to the product `a * b`.
  have hab_inv : a * b = (a * b)⁻¹ := by
    -- Step 4.1: Specialize the general inversion property to `a * b`.
    exact (h_inv_general (a * b)).symm
  -- Step 5: Establish that `b * a` acts as an inverse of `a * b`.
  have h_right : (a * b) * (b * a) = (1 : G) := by
    -- Step 5.1: Expand and reorganize the product to expose repeated factors.
    calc
      (a * b) * (b * a)
          = ((a * b) * b) * a := by
            -- Step 5.1.1: Reassociate the factors.
            simp [mul_assoc]
      _ = (a * (b * b)) * a := by
            -- Step 5.1.2: Shift parentheses to group the repeated element `b`.
            simp [mul_assoc]
      _ = (a * 1) * a := by
            -- Step 5.1.3: Replace `b * b` with `1` using `hb_sq`.
            simp [hb_sq]
      _ = a * a := by
            -- Step 5.1.4: Remove the neutral element.
            simp
      _ = 1 := by
            -- Step 5.1.5: Substitute `a * a` with `1` using `ha_sq`.
            simp [ha_sq]
  have h_ba_inv : b * a = (a * b)⁻¹ := by
    -- Step 5.2: Multiply the previous equality on the left by `(a * b)⁻¹` to solve for `b * a`.
    have := congrArg (fun t => (a * b)⁻¹ * t) h_right
    -- Step 5.2.1: Simplify both sides to isolate `b * a`.
    simpa [mul_assoc]
  -- Step 6: Combine the two inverse descriptions to obtain commutativity.
  calc
    a * b = (a * b)⁻¹ := hab_inv
    _ = b * a := by
      -- Step 6.1: Substitute the alternative expression for `(a * b)⁻¹`.
      simpa using h_ba_inv.symm
