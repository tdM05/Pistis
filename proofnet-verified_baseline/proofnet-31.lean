import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators



/-Informal Statement

Let $x$ and $y$ be elements of $G$. Prove that $xy=yx$ if and only if $y^{-1}xy=x$ if and only if $x^{-1}y^{-1}xy=1$.
-/

/-Informal Proof

If $x y=y x$, then $y^{-1} x y=y^{-1} y x=1 x=x$. Multiplying by $x^{-1}$ then gives $x^{-1} y^{-1} x y=1$.

On the other hand, if $x^{-1} y^{-1} x y=1$, then we may multiply on the left by $x$ to get $y^{-1} x y=x$. Then multiplying on the left by $y$ gives $x y=y x$ as desired.
-/

theorem Dummit_Foote_exercise_1_1_18 {G : Type*} [Group G]
  (x y : G) : (x * y = y * x ↔ y⁻¹ * x * y = x) ∧ (y⁻¹ * x * y = x ↔ x⁻¹ * y⁻¹ * x * y = 1) := by
  -- Step 1: Break the overall target into the conjunction of two equivalences.
  constructor
  · -- Step 1.1: Show `x * y = y * x` if and only if `y⁻¹ * x * y = x`.
    constructor
    · -- Step 1.1.1: Assume the commutativity relation and derive the conjugation equality.
      intro h_comm
      -- Step 1.1.1.1: Multiply both sides of the commutativity equation on the left by `y⁻¹`.
      have h_helper := congrArg (fun z => y⁻¹ * z) h_comm
      -- Step 1.1.1.2: Simplify to obtain `y⁻¹ * x * y = x`.
      simpa [mul_assoc] using h_helper
    · -- Step 1.1.2: Assume the conjugation equality and conclude commutativity.
      intro h_conj
      -- Step 1.1.2.1: Multiply both sides of the given equality on the left by `y`.
      have h_helper := congrArg (fun z => y * z) h_conj
      -- Step 1.1.2.2: Simplify to reach `x * y = y * x`.
      simpa [mul_assoc] using h_helper
  · -- Step 2: Show `y⁻¹ * x * y = x` if and only if `x⁻¹ * y⁻¹ * x * y = 1`.
    constructor
    · -- Step 2.1: Assume the conjugation equality and obtain the identity after multiplying by `x⁻¹`.
      intro h_conj
      -- Step 2.1.1: Multiply both sides on the left by `x⁻¹`.
      have h_helper := congrArg (fun z => x⁻¹ * z) h_conj
      -- Step 2.1.2: Simplify to deduce `x⁻¹ * y⁻¹ * x * y = 1`.
      simpa [mul_assoc] using h_helper
    · -- Step 2.2: Assume the identity statement and recover the conjugation equality.
      intro h_id
      -- Step 2.2.1: Multiply both sides on the left by `x`.
      have h_helper := congrArg (fun z => x * z) h_id
      -- Step 2.2.2: Simplify to conclude `y⁻¹ * x * y = x`.
      simpa [mul_assoc] using h_helper
