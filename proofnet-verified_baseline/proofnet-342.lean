import Mathlib

open Topology Filter Real TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Prove that $\lim_{n \rightarrow \infty}\sqrt{n^2 + n} - n = 1/2$ for the real function $f(n) = \sqrt{n^2+n} - n$.
-/

/-Informal Proof

Multiplying and dividing by $\sqrt{n^2+n}+n$ yields
$$
\sqrt{n^2+n}-n=\frac{n}{\sqrt{n^2+n}+n}=\frac{1}{\sqrt{1+\frac{1}{n}}+1} .
$$
It follows that the limit is $\frac{1}{2}$.
-/

theorem Rudin_exercise_3_2a
  : Tendsto (λ (n : ℝ) => (sqrt (n^2 + n) - n)) atTop (𝓝 (1/2)) := by
  -- Step 1: Introduce the simplified helper function `g x = 1 / (√(1 + x) + 1)`
  -- so that the original sequence is expected to be eventually equal to `g (1/n)`.
  let g : ℝ → ℝ := fun x => 1 / (sqrt (1 + x) + 1)

  -- Step 2: Prove that for all sufficiently large (hence positive) `n`,
  -- the original term `√(n^2 + n) - n` coincides with `g (1/n)`.
  have h_eq :
      (fun n : ℝ => sqrt (n^2 + n) - n) =ᶠ[atTop] fun n => g (1 / n) := by
    -- Step 2.1: Along `atTop` we eventually have `n > 0`, which grants all needed divisions.
    have hpos : ∀ᶠ n : ℝ in atTop, 0 < n := Ioi_mem_atTop 0
    -- Step 2.2: On that event we perform the algebraic rewriting.
    refine hpos.mono ?_
    intro n hn
    -- Step 2.3: Record the non-zeroness and nonnegativity facts that will be reused.
    have hn0 : n ≠ 0 := ne_of_gt hn
    have hnonneg_arg : 0 ≤ n^2 + n := by nlinarith
    -- Step 2.4: Rationalize once to remove the subtraction in the numerator.
    have hden_pos : 0 < sqrt (n^2 + n) + n := by
      have hpos_arg : 0 < n^2 + n := by nlinarith
      have hpos_sqrt : 0 < sqrt (n^2 + n) := Real.sqrt_pos.2 hpos_arg
      linarith
    have hden_ne : sqrt (n^2 + n) + n ≠ 0 := ne_of_gt hden_pos
    have h_rational :
        sqrt (n^2 + n) - n = n / (sqrt (n^2 + n) + n) := by
      -- Difference of squares: (a - b)(a + b) = a² - b².
      have hprod :
          (sqrt (n^2 + n) - n) * (sqrt (n^2 + n) + n) = n := by
        calc
          (sqrt (n^2 + n) - n) * (sqrt (n^2 + n) + n)
              = (sqrt (n^2 + n))^2 - n^2 := by ring
          _ = n^2 + n - n^2 := by
                have hsq := Real.sq_sqrt hnonneg_arg
                simp [hsq]
          _ = n := by ring
      exact (eq_div_iff hden_ne).2 hprod

    -- Step 2.5: Relate `√(n^2 + n) / n` to `√(1 + 1/n)` using `sqrt_div`.
    have hfrac :
        sqrt (n^2 + n) / n = sqrt (1 + 1 / n) := by
      -- Rewrite the denominator via `sqrt (n^2) = n` for positive `n`.
      have hsqrt_sq : sqrt (n^2) = n := by
        have habs : sqrt (n^2) = |n| := by
          -- `sqrt_sq_eq_abs` expresses `√(n^2)` as `|n|`.
          simpa [sq] using Real.sqrt_sq_eq_abs n
        simpa [abs_of_pos hn] using habs
      calc
        sqrt (n^2 + n) / n = sqrt (n^2 + n) / sqrt (n^2) := by simp [hsqrt_sq]
        _ = sqrt ((n^2 + n) / n^2) := by
              -- Apply the `sqrt_div` lemma (and flip the equality to match the goal).
              simpa using (sqrt_div hnonneg_arg (n^2)).symm
        _ = sqrt (1 + 1 / n) := by
              -- Simplify the inner fraction `(n^2 + n) / n^2` to `1 + 1/n`.
              have hn0' : n ≠ 0 := hn0
              field_simp [hn0']

    -- Step 2.6: Divide numerator and denominator by `n` to reach `g (1/n)`.
    calc
      sqrt (n^2 + n) - n
          = n / (sqrt (n^2 + n) + n) := h_rational
      _ = (n / n) / (sqrt (n^2 + n) / n + 1) := by
            have hn0 : n ≠ 0 := hn0
            field_simp [hn0]
      _ = 1 / (sqrt (n^2 + n) / n + 1) := by
            have hn0 : n ≠ 0 := hn0
            simp [hn0]
      _ = 1 / (sqrt (1 + 1 / n) + 1) := by simp [hfrac]
      _ = g (1 / n) := by rfl

  -- Step 3: Show that the simplified function `n ↦ g (1/n)` tends to `1/2`.
  -- Step 3.1: `g` is continuous at `0` because it is built from continuous pieces and the denominator is nonzero there.
  have h_cont_g : ContinuousAt g 0 := by
    -- Step 3.1.1: Continuity of `x ↦ √(1 + x) + 1` at `0`.
    have h_inner :
        ContinuousAt (fun x : ℝ => sqrt (1 + x) + 1) 0 :=
      (Real.continuous_sqrt.comp (continuous_const.add continuous_id)).continuousAt.add
        continuousAt_const
    -- Step 3.1.2: At `x = 0` the denominator equals `2`, so inversion is continuous.
    have h_ne : (sqrt (1 + 0) + 1) ≠ (0 : ℝ) := by norm_num
    -- Step 3.1.3: Combine the previous two bullets with `inv₀`.
    have h_inv :
        ContinuousAt (fun x : ℝ => (sqrt (1 + x) + 1)⁻¹) 0 :=
      h_inner.inv₀ h_ne
    -- Step 3.1.4: Translate to the original `g` notation.
    simpa [g, one_div] using h_inv

  -- Step 3.2: Evaluate the limit of `g` at `0`, namely `g 0 = 1/2`.
  have h_tendsto_g : Tendsto g (𝓝 0) (𝓝 (1 / 2 : ℝ)) := by
    have hbase := h_cont_g.tendsto
    -- `hbase` states convergence to `g 0`; compute `g 0` explicitly.
    have hg0 : g 0 = (1 / 2 : ℝ) := by norm_num [g]
    simpa [hg0] using hbase

  -- Step 3.3: The map `n ↦ 1/n` tends to `0` as `n → ∞`.
  have h_inv_zero : Tendsto (fun n : ℝ => 1 / n) atTop (𝓝 (0 : ℝ)) := by
    -- This is the standard real-analysis fact about reciprocals.
    simpa [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun n : ℝ => n⁻¹) atTop (𝓝 0))

  -- Step 3.4: Compose the two limits to obtain the limit of the simplified sequence.
  have h_comp : Tendsto (fun n : ℝ => g (1 / n)) atTop (𝓝 (1 / 2 : ℝ)) :=
    h_tendsto_g.comp h_inv_zero

  -- Step 3.5: Transfer the limit back to the original sequence via the eventual equality `h_eq`.
  exact (tendsto_congr' h_eq).2 h_comp
