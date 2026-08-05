import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd RingHom
open scoped BigOperators



/-Informal Statement

Prove that every homomorphism of fields is injective.
-/

/-Informal Proof

Suppose $f(a)=f(b)$, then $f(a-b)=0=f(0)$. If $u=(a-b) \neq 0$, then $f(u) f\left(u^{-1}\right)=f(1)=1$, but that means that $0 f\left(u^{-1}\right)=1$, which is impossible. Hence $a-b=0$ and $a=b$.
-/

theorem Artin_exercise_3_2_7 {F : Type*} [Field F] {G : Type*} [Field G]
  (φ : F →+* G) : Injective φ := by
  classical
  -- Step 1: Introduce arbitrary elements in `F` and the equality of their images.
  intro a b hab
  -- Step 1.1: Rewrite `φ (a - b)` using `map_sub` so that the assumption `φ a = φ b` forces the image to vanish.
  have hker : φ (a - b) = 0 := by
    -- Step 1.2: Expand the image of the subtraction and use `φ a = φ b` to see the result is zero.
    have hsub := map_sub φ a b
    have hzero : φ a - φ b = 0 := sub_eq_zero.mpr hab
    exact hsub.trans hzero
  -- Step 2: Prove that `a - b = 0` by deriving a contradiction from assuming the opposite.
  have hdiff_zero : a - b = 0 := by
    -- Step 2.1: Assume `a - b ≠ 0` and work toward a contradiction.
    by_contra hne
    -- Step 2.2: Map the identity `(a - b) * (a - b)⁻¹ = 1` through `φ` to obtain an equation in `G`.
    have hmul_eq_one : φ (a - b) * φ ((a - b)⁻¹) = (1 : G) := by
      -- Step 2.2.1: Use the field inverse law to get `(a - b) * (a - b)⁻¹ = 1` in `F`.
      have hne' : a - b ≠ 0 := hne
      have hx : (a - b) * (a - b)⁻¹ = (1 : F) := by
        simpa using (mul_inv_cancel₀ (a := a - b) hne')
      -- Step 2.2.2: Apply `φ` to the identity and simplify with the homomorphism properties.
      have hxmap := congrArg φ hx
      simpa [map_mul, map_one] using hxmap
    -- Step 2.3: The previous equation together with `φ (a - b) = 0` forces `0 = 1` in `G`.
    have hzero_eq_one : (0 : G) = 1 := by
      -- Step 2.3.1: Replace the first factor in the product by zero using `hker`.
      -- Step 2.3.2: Collapse using the kernel and zero multiplication facts.
      simp [hker] at hmul_eq_one
    -- Step 2.4: Contradict the basic field fact `0 ≠ 1`, eliminating the assumption `a - b ≠ 0`.
    exact zero_ne_one hzero_eq_one
  -- Step 3: Convert the vanishing difference back into the desired equality `a = b`.
  exact sub_eq_zero.mp hdiff_zero
