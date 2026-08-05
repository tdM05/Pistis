import Mathlib

open Filter Real Function
open scoped Topology



/-Informal Statement

Prove that the real function $\sqrt{n+1}-\sqrt{n} \rightarrow 0$ as $n \rightarrow \infty$.
-/

/-Informal Proof

$$
\sqrt{n+1}-\sqrt{n}=\frac{(\sqrt{n+1}-\sqrt{n})(\sqrt{n+1}+\sqrt{n})}{\sqrt{n+1}+\sqrt{n}}=\frac{1}{\sqrt{n+1}+\sqrt{n}}<\frac{1}{2 \sqrt{n}}
$$
-/

theorem Pugh_exercise_3_4 :
  Tendsto (fun n : ℝ => sqrt (n + 1) - sqrt n) atTop (𝓝 0) := by
  -- Step 1: Show that `√(x + 1)` is positive whenever `x ≥ 0`.
  have h_sqrt_pos :
      ∀ {x : ℝ}, 0 ≤ x → 0 < sqrt (x + 1) := by
    intro x hx
    -- Step 1.1: Since `x ≥ 0`, we have `0 < x + 1`, so its square root is positive.
    have hx_pos : 0 < x + 1 := add_pos_of_nonneg_of_pos hx zero_lt_one
    exact Real.sqrt_pos.2 hx_pos
  -- Step 2: Deduce that the denominator `√(x + 1) + √x` stays positive for `x ≥ 0`.
  have h_pos_denom :
      ∀ {x : ℝ}, 0 ≤ x → 0 < sqrt (x + 1) + sqrt x := by
    intro x hx
    -- Step 2.1: Combine the strict positivity of `√(x + 1)` with the nonnegativity of `√x`.
    exact add_pos_of_pos_of_nonneg (h_sqrt_pos hx) (Real.sqrt_nonneg x)
  -- Step 3: Rationalize the difference to `1 / (√(x + 1) + √x)` under the same assumption.
  have h_diff_eq :
      ∀ {x : ℝ}, 0 ≤ x →
        sqrt (x + 1) - sqrt x = (1 : ℝ) / (sqrt (x + 1) + sqrt x) := by
    intro x hx
    -- Step 3.1: Name the denominator and note that it never vanishes.
    set denom := sqrt (x + 1) + sqrt x
    have h_denom_pos : 0 < denom := h_pos_denom hx
    have h_denom_ne : denom ≠ 0 := ne_of_gt h_denom_pos
    -- Step 3.2: Compute the product `(√(x + 1) - √x) * denom`.
    have h_prod :
        (sqrt (x + 1) - sqrt x) * denom = 1 := by
      -- Step 3.2.1: Apply the difference-of-squares identity.
      have h_prod' :
          (sqrt (x + 1) - sqrt x) * denom
              = (sqrt (x + 1)) ^ 2 - (sqrt x) ^ 2 := by
        have h :=
          (by
            ring
          :
            (sqrt (x + 1) - sqrt x) * (sqrt (x + 1) + sqrt x)
                = (sqrt (x + 1)) ^ 2 - (sqrt x) ^ 2)
        simpa [denom] using h
      -- Step 3.2.2: Replace squares of square roots by the original nonnegative numbers.
      have hx1 : 0 ≤ x + 1 := add_nonneg hx zero_le_one
      have hx2 : 0 ≤ x := hx
      have h_sq₁ :
          (sqrt (x + 1)) ^ 2 = x + 1 := by
        simpa [pow_two] using Real.mul_self_sqrt hx1
      have h_sq₂ :
          (sqrt x) ^ 2 = x := by
        simpa [pow_two] using Real.mul_self_sqrt hx2
      simpa [h_sq₁, h_sq₂] using h_prod'
    -- Step 3.3: Divide the product identity by the nonzero denominator.
    have h_res :=
      congrArg (fun t : ℝ => t / denom) h_prod
    simpa [denom, h_denom_ne] using h_res
  -- Step 4: The sequence is monotone in the sense that each difference is nonnegative.
  have h_nonneg :
      ∀ {x : ℝ}, 0 ≤ x → 0 ≤ sqrt (x + 1) - sqrt x := by
    intro x hx
    -- Step 4.1: Use the reciprocal expression together with the positivity of the denominator.
    have h_pos : 0 < sqrt (x + 1) + sqrt x := h_pos_denom hx
    have h_rec_nonneg :
        0 ≤ (1 : ℝ) / (sqrt (x + 1) + sqrt x) :=
      (one_div_pos.mpr h_pos).le
    simpa [h_diff_eq hx] using h_rec_nonneg
  -- Step 5: Switch to the ε–X formulation of convergence for real-valued functions.
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε_pos
  -- Step 5.1: Collect reusable bounds involving ε.
  have hε_ne : ε ≠ 0 := ne_of_gt hε_pos
  have hhalf_lt : ε / 2 < ε := half_lt_self hε_pos
  have h_two_div_pos : 0 < (2 / ε : ℝ) := by
    have h_inv_pos : 0 < (1 / ε : ℝ) := one_div_pos.2 hε_pos
    simpa [div_eq_mul_inv] using mul_pos (show (0 : ℝ) < 2 by norm_num) h_inv_pos
  -- Step 5.2: Choose a concrete threshold that enforces both `x ≥ 0` and `x ≥ (2 / ε)^2`.
  let X : ℝ := max 0 ((2 / ε : ℝ) ^ 2)
  have hX_nonneg : 0 ≤ X := le_max_left _ _
  have hX_threshold : (2 / ε : ℝ) ^ 2 ≤ X := le_max_right _ _
  refine ⟨X, ?_⟩
  intro x hx
  -- Step 5.3: Extract that `x` is large and nonnegative from `x ≥ X`.
  have hx_nonneg : 0 ≤ x := hX_nonneg.trans hx
  have h_threshold :
      (2 / ε : ℝ) ^ 2 ≤ x := hX_threshold.trans hx
  have h_threshold_succ :
      (2 / ε : ℝ) ^ 2 ≤ x + 1 := by
    have : x ≤ x + 1 := by linarith
    exact h_threshold.trans this
  -- Step 5.4: Deduce that `√(x + 1)` dominates `2 / ε`.
  have h_sqrt_lower :
      (2 / ε : ℝ) ≤ sqrt (x + 1) := by
    have h := Real.sqrt_le_sqrt h_threshold_succ
    have h_left :
        sqrt ((2 / ε : ℝ) ^ 2) = 2 / ε := by
      have h_abs : |2 / ε| = 2 / ε := abs_of_pos h_two_div_pos
      simp [Real.sqrt_sq_eq_abs, h_abs]
    simpa [h_left] using h
  -- Step 5.5: Convert the reciprocal representation into a convenient upper bound.
  have h_le_one_over_sqrt :
      sqrt (x + 1) - sqrt x ≤ (1 : ℝ) / sqrt (x + 1) := by
    have hineq :=
      one_div_le_one_div_of_le (h_sqrt_pos hx_nonneg)
        (show sqrt (x + 1) ≤ sqrt (x + 1) + sqrt x from
          le_add_of_nonneg_right (Real.sqrt_nonneg x))
    simpa [h_diff_eq hx_nonneg] using hineq
  -- Step 5.6: Now force `1 / √(x + 1)` below ε/2 using the previous lower bound.
  have h_inv_bound :
      (1 : ℝ) / sqrt (x + 1) ≤ ε / 2 := by
    have h_inv :=
      one_div_le_one_div_of_le h_two_div_pos h_sqrt_lower
    have h_val : (1 : ℝ) / (2 / ε) = ε / 2 := by
      field_simp [div_eq_mul_inv, hε_ne]
    simpa [h_val] using h_inv
  -- Step 5.7: Combine the two inequalities and translate back to the metric language.
  have h_final_bound :
      sqrt (x + 1) - sqrt x ≤ ε / 2 :=
    h_le_one_over_sqrt.trans h_inv_bound
  have h_lt : sqrt (x + 1) - sqrt x < ε :=
    lt_of_le_of_lt h_final_bound hhalf_lt
  have hx_diff_nonneg : 0 ≤ sqrt (x + 1) - sqrt x := h_nonneg hx_nonneg
  have hx_sqrt_le : sqrt x ≤ sqrt (x + 1) := sub_nonneg.mp hx_diff_nonneg
  have h_abs :
      |sqrt (x + 1) - sqrt x| = sqrt (x + 1) - sqrt x :=
    abs_of_nonneg hx_diff_nonneg
  have h_dist :
      dist (sqrt (x + 1) - sqrt x) 0
        = sqrt (x + 1) - sqrt x := by
    simpa [Real.dist_eq, sub_eq_add_neg, h_abs]
  simpa [h_dist] using h_lt
