import Mathlib

open Real
open Polynomial
open scoped BigOperators



/-Informal Statement

Show that $\sin (\pi / 12)$ is an algebraic number.
-/

/-Informal Proof

$$
\begin{aligned}
    \sin \pi/12=\sin \left(\pi/4-\pi/6\right) & =\sin \pi/4 \cos \pi/6-\cos \pi/4 \sin \pi/6 \\
& =\frac{\sqrt{3}}{2 \sqrt{2}}-\frac{1}{2 \sqrt{2}} \\
& =\frac{\sqrt{3}-1}{2 \sqrt{2}}
\end{aligned}
$$
-/

theorem Ireland_Rosen_exercise_12_12 : IsAlgebraic ℚ (sin (Real.pi/12)) := by
  classical
  -- Step 1: Introduce a short name `s` for `sin (π / 12)` so that later algebra is easier to read.
  set s := Real.sin (Real.pi / 12) with hs
  -- Step 2: Choose an explicit polynomial with rational coefficients that will vanish at `s`.
  --         The candidate below is obtained by clearing denominators from the squared triple-angle identity.
  let p : ℚ[X] :=
    Polynomial.C (32 : ℚ) * Polynomial.X ^ 6
      - Polynomial.C (48 : ℚ) * Polynomial.X ^ 4
      + Polynomial.C (18 : ℚ) * Polynomial.X ^ 2
      - 1
  -- Step 2.1: Show that this polynomial is not identically zero by looking at its value at `0`.
  have h_eval0 : Polynomial.eval (0 : ℚ) p = (-1 : ℚ) := by
    -- The constant term is `-1`, so evaluating at zero gives `-1`.
    simp [p]
  -- Step 2.2: Convert that evaluation into the required non-vanishing fact.
  have hp_ne : p ≠ 0 := by
    intro hp
    have hzero : Polynomial.eval (0 : ℚ) p = 0 := by simp [hp]
    have : (-1 : ℚ) = 0 := by simp [h_eval0] at hzero
    exact (by norm_num : (-1 : ℚ) ≠ 0) this
  -- Step 3: Use the triple-angle identity to relate `s` to the known value `sin (π / 4)`.
  have h_three : 3 * (Real.pi / 12) = Real.pi / 4 := by
    -- Step 3.1: First write `3 * (π / 12)` as `π * (3 / 12)` and simplify `3 / 12 = 1 / 4`.
    have h_ratio : (3 : ℝ) / 12 = (1 : ℝ) / 4 := by norm_num
    have h1 : 3 * (Real.pi / 12) = Real.pi * ((3 : ℝ) / 12) := by
      simp [div_eq_mul_inv, mul_left_comm]
    have h2 : Real.pi * ((3 : ℝ) / 12) = Real.pi * (1 / 4) := by simp [h_ratio]
    have h3 : Real.pi * (1 / 4) = Real.pi / 4 := by
      simp [div_eq_mul_inv]
    exact h1.trans <| h2.trans h3
  -- Step 3.2: Apply the triple-angle identity `sin (3x) = 3 sin x - 4 sin^3 x` at `x = π / 12`.
  have h_triple : Real.sin (Real.pi / 4) = 3 * s - 4 * s ^ 3 := by
    simpa [hs, h_three] using Real.sin_three_mul (Real.pi / 12)
  -- Step 3.3: Record the exact square of `sin (π / 4)` for future substitutions.
  have h_sin_sq : (Real.sqrt 2 / 2 : ℝ) ^ 2 = (1 / 2 : ℝ) := by
    have hpos : 0 ≤ (2 : ℝ) := by norm_num
    simp [pow_two, div_eq_mul_inv, Real.mul_self_sqrt hpos, mul_comm, mul_left_comm]
  -- Step 4: Square both sides to remove the square root appearing in `sin (π / 4)`.
  have h_sq :
      (3 * s - 4 * s ^ 3) ^ 2 = (1 / 2 : ℝ) := by
    -- Step 4.1: After squaring, simplify with the known exact value of `sin (π / 4)`.
    have h := congrArg (fun t : ℝ => t ^ 2) h_triple.symm
    simpa [h_sin_sq] using h
  -- Step 4.2: Expand the square so that only even powers of `s` remain.
  have h_sq_exp :
      16 * s ^ 6 - 24 * s ^ 4 + 9 * s ^ 2 = (1 / 2 : ℝ) := by
    have h_expand : (3 * s - 4 * s ^ 3) ^ 2 = 16 * s ^ 6 - 24 * s ^ 4 + 9 * s ^ 2 := by
      ring
    simpa [h_expand] using h_sq
  -- Step 4.3: Clear the denominator by multiplying both sides by `2`.
  have h_mul2 :
      32 * s ^ 6 - 48 * s ^ 4 + 18 * s ^ 2 = (1 : ℝ) := by
    have h_expand2 :
        (2 : ℝ) * (16 * s ^ 6 - 24 * s ^ 4 + 9 * s ^ 2)
          = 32 * s ^ 6 - 48 * s ^ 4 + 18 * s ^ 2 := by
      ring
    have := congrArg (fun t : ℝ => (2 : ℝ) * t) h_sq_exp
    simpa [h_expand2] using this
  -- Step 4.4: Move the right-hand side to zero; this is exactly the relation encoded by `p`.
  have h_poly :
      (32 : ℝ) * s ^ 6 - 48 * s ^ 4 + 18 * s ^ 2 - 1 = 0 := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (sub_eq_zero.mpr h_mul2)
  -- Step 5: Evaluate `p` at `s` (seen inside `ℝ`) via the algebra map `ℚ → ℝ`.
  have h_aeval :
      aeval s p = (32 : ℝ) * s ^ 6 - (48 : ℝ) * s ^ 4 + (18 : ℝ) * s ^ 2 - 1 := by
    simp [p, hs]
  -- Step 5.1: Combine the explicit evaluation with the polynomial relation to conclude that the evaluation is zero.
  have h_aeval_zero : aeval s p = 0 := by
    simpa [h_poly] using h_aeval
  -- Step 6: Package everything into the definition of `IsAlgebraic`.
  refine ⟨p, hp_ne, ?_⟩
  simpa using h_aeval_zero
