import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Deduce that $|a b|=|b a|$ for all $a, b \in G$.
-/

/-Informal Proof

Let $a$ and $b$ be arbitrary group elements. Letting $x=a b$ and $g=a$, we see that
$$
|a b|=\left|a^{-1} a b a\right|=|b a| .
$$
-/

theorem Dummit_Foote_exercise_1_1_22b {G: Type*} [Group G] (a b : G) :
  orderOf (a * b) = orderOf (b * a) := by
  -- Step 1: Exhibit that `a * b` and `b * a` are related by conjugation through `a⁻¹`.
  -- Step 1.1: Translate the definition of `SemiconjBy` into the required equality between products,
  --           namely `a⁻¹ * (a * b) = (b * a) * a⁻¹`.
  have hSemiconj : SemiconjBy (a⁻¹) (a * b) (b * a) := by
    -- Step 1.1.1: Expand `SemiconjBy` so that we can work directly with the product equality.
    change a⁻¹ * (a * b) = (b * a) * a⁻¹
    -- Step 1.1.2: Reassociate the left-hand side so the inverse `a⁻¹` cancels with `a`.
    calc
      a⁻¹ * (a * b)
          = (a⁻¹ * a) * b := by
            -- Step 1.1.2.1: Use associativity to move parentheses.
            simp
      _ = b := by
            -- Step 1.1.2.2: Cancel `a⁻¹ * a` to `1` and drop the neutral element.
            simp
      _ = (b * a) * a⁻¹ := by
            -- Step 1.1.2.3: Reinsert `a` and `a⁻¹` on the right so the expression matches the target.
            --               Another associativity rewrite shows `(b * a) * a⁻¹ = b`.
            simp [mul_assoc]
  -- Step 2: Apply the lemma ensuring semiconjugate elements have the same order.
  -- Step 2.1: Use `SemiconjBy.orderOf_eq` with the witness from Step 1 to finish the argument.
  simpa using
    (SemiconjBy.orderOf_eq (a := a⁻¹) (x := a * b) (y := b * a) hSemiconj)
