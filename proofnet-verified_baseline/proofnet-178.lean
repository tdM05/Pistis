import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology



/-Informal Statement

Prove that the power series $\sum z^n/n^2$ converges at every point of the unit circle.
-/

/-Informal Proof

Since $\left|z^n / n^2\right|=1 / n^2$ for all $|z|=1$, then $\sum z^n / n^2$ converges at every point in the unit circle as $\sum 1 / n^2$ does ( $p$-series $p=2$.)
-/

theorem Shakarchi_exercise_1_19b (z : ℂ) (hz : ‖z‖ = 1) (s : ℕ → ℂ)
    (h : s = (λ n => ∑ i ∈ (range n), z ^ (i + 1) / (i + 1) ^ 2)) :
    ∃ y, Tendsto s atTop (𝓝 y) := by
  -- Step 1: Introduce the function `f` capturing the summand of our series.
  classical
  set f : ℕ → ℂ := fun n => z ^ (n + 1) / (n + 1 : ℂ) ^ 2 with hfdef
  -- Step 2: Describe the norm of each summand explicitly using the hypothesis ‖z‖ = 1.
  have h_norm :
      (fun n : ℕ => ‖f n‖) =
        fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ) ^ 2 := by
    -- Step 2.1: Expand `f` and simplify via `‖z‖ = 1`.
    funext n
    -- Step 2.2: Use explicit computations for the numerator and denominator norms.
    have hzpow : ‖z ^ (n + 1)‖ = 1 := by
      simp [hz, Complex.norm_pow z (n + 1)]
    -- Step 2.3: Identify the norm of the denominator `(n + 1 : ℂ)^2`.
    have hdenpow :
        ‖(n + 1 : ℂ) ^ 2‖ = (n + 1 : ℝ) ^ 2 := by
      have hden : ‖(n + 1 : ℂ)‖ = (n + 1 : ℝ) := by
        simpa [Nat.cast_add, Nat.cast_one] using (Complex.norm_natCast (n + 1))
      simp [pow_two, hden]
    -- Step 2.4: Combine the two calculations to obtain the desired equality.
    calc
      ‖f n‖ = ‖z ^ (n + 1)‖ / ‖(n + 1 : ℂ) ^ 2‖ := by
        simp [f]
      _ = 1 / ‖(n + 1 : ℂ) ^ 2‖ := by
        simp [hzpow]
      _ = (1 : ℝ) / (n + 1 : ℝ) ^ 2 := by
        simp [hdenpow]
  -- Step 3: Apply the classical p-series summability lemma to the norm sequence.
  have h_pSeries :
      Summable fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ) ^ 2 := by
    -- Step 3.1: Produce the classical `p`-series with exponent `p = 2`.
    have h_base :
        Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 :=
      (Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two
    -- Step 3.2: Shift the index by one to match the exact numerator in `f`.
    simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 h_base
  -- Step 3.3: Transfer summability across the function equality `h_norm`.
  have h_norm_summable :
      Summable fun n : ℕ => ‖f n‖ := by
    simpa [h_norm] using h_pSeries
  -- Step 4: Absolute convergence yields convergence of the complex series itself.
  have hfSummable : Summable f :=
    Summable.of_norm h_norm_summable
  -- Step 5: Extract the limit supplied by `HasSum` for the partial sums of `f`.
  refine ⟨∑' n, f n, ?_⟩
  have hy : HasSum f (∑' n, f n) := hfSummable.hasSum
  -- Step 6: Rewrite the target sequence `s` in terms of the partial sums of `f`.
  -- Step 6.1: Use the supplied equality `h` alongside `hy`.
  -- Step 6.2: Conclude by the convergence of partial sums furnished by `HasSum`.
  simpa [h, f] using hy.tendsto_sum_nat
