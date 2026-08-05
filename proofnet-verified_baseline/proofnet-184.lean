import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators



/-Informal Statement

Prove that the products $a b$ and $b a$ are conjugate elements in a group.
-/

/-Informal Proof

We have that $(a^{-1})ab(a^{-1})^{-1} = ba$.
-/

theorem Artin_exercise_2_3_2 {G : Type*} [Group G] (a b : G) :
  ∃ g : G, b* a = g * a * b * g⁻¹ := by
  -- Step 1: We explicitly exhibit the conjugating element by choosing `g = b`.
  refine ⟨b, ?_⟩
  -- Step 2: Compute `g * a * b * g⁻¹` for this choice and show it equals `b * a`.
  -- Step 2.1: Associate the product to isolate the adjacent factors `b * b⁻¹`.
  -- Step 2.2: Simplify using the inverse law `b * b⁻¹ = 1` and the identity law.
  -- Step 2.3: After simplification both sides coincide, so the equality holds.
  simp [mul_assoc]
