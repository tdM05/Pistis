import Mathlib
open Topology Filter Real TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Prove that the convergence of $\Sigma a_{n}$ implies the convergence of $\sum \frac{\sqrt{a_{n}}}{n}$ if $a_n\geq 0$.
-/

/-Informal Proof

Since $\left(\sqrt{a_n}-\frac{1}{n}\right)^2 \geq 0$, it follows that
$$
\frac{\sqrt{a_n}}{n} \leq \frac{1}{2}\left(a_n^2+\frac{1}{n^2}\right) .
$$
Now $\Sigma a_n^2$ converges by comparison with $\Sigma a_n$ (since $\Sigma a_n$ converges, we have $a_n<1$ for large $n$, and hence $\left.a_n^2<a_n\right)$. Since $\Sigma \frac{1}{n^2}$ also converges ($p$ series, $p=2$ ), it follows that $\Sigma \frac{\sqrt{a_n}}{n}$ converges.
-/

theorem Rudin_exercise_3_7
  (a : ℕ → ℝ)
  (hnneg : ∀ n, a n ≥ 0)
  (h : ∃ y, (Tendsto (λ n => (∑ i ∈ (range n), a i)) atTop (𝓝 y))) :
  ∃ y, Tendsto (λ n => (∑ i ∈ (range n), sqrt (a i) / (i + 1))) atTop (𝓝 y) := by
  classical
  obtain ⟨y₀, hy₀⟩ := h
  -- Step 1: reinterpret the hypothesis `h` as the summability of the original series `∑ a n`.
  have hSummable : Summable a := by
    -- Step 1.1: use the characterization of `HasSum` for nonnegative series to upgrade `hy₀`.
    exact ⟨y₀, (hasSum_iff_tendsto_nat_of_nonneg hnneg _).2 hy₀⟩
  -- Step 2: record the classical `p`-series convergence `∑ 1 / n^2` and shift it to `(n + 1)`.
  have hPSeries : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := by
    -- Step 2.1: specialize the real `p`-series test with exponent `2`.
    have hTwo : 1 < (2 : ℕ) := by decide
    exact (Real.summable_one_div_nat_pow (p := 2)).2 hTwo
  -- Step 2.2: shift the index so that the denominator becomes `(n + 1)` everywhere.
  have hPSeriesShift :
      Summable (fun n : ℕ => 1 / (n + 1 : ℝ) ^ 2) := by
    -- Step 2.2.1: reindex via the `summable_nat_add_iff` lemma with shift `1`.
    simpa using
      ((summable_nat_add_iff 1 (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) (G := ℝ)).2 hPSeries)
  -- Step 3: build the dominating summable sequence `(a n + 1/(n+1)^2)/2`.
  have hDom :
      Summable fun n : ℕ => (a n + 1 / (n + 1 : ℝ) ^ 2) / 2 := by
    -- Step 3.1: the sum of the two summable sequences is still summable.
    have hAdd :
        Summable fun n : ℕ => a n + 1 / (n + 1 : ℝ) ^ 2 :=
      hSummable.add hPSeriesShift
    -- Step 3.2: multiplying a summable series by the constant `1/2` keeps it summable.
    simpa [div_eq_mul_inv, add_comm, add_left_comm, add_assoc] using
      hAdd.mul_right (1 / 2 : ℝ)
  -- Step 4: note that every term of the target series is nonnegative.
  have hNonneg :
      ∀ n : ℕ, 0 ≤ sqrt (a n) / (n + 1 : ℝ) := by
    -- Step 4.1: positivity is immediate because `sqrt (a n) ≥ 0` and `n + 1 > 0`.
    intro n
    have hden : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
    exact div_nonneg (Real.sqrt_nonneg _) hden.le
  -- Step 5: compare every term with the dominating term using `(√a - 1/(n+1))^2 ≥ 0`.
  have hCompare :
      ∀ n : ℕ,
        sqrt (a n) / (n + 1 : ℝ) ≤ (a n + 1 / (n + 1 : ℝ) ^ 2) / 2 := by
    intro n
    -- Step 5.1: apply `2ab ≤ a^2 + b^2` with `a = √(a n)` and `b = 1/(n+1)`.
    have hineq :=
      two_mul_le_add_sq (Real.sqrt (a n)) (1 / (n + 1 : ℝ))
    have hineq' :=
      (mul_le_mul_of_nonneg_right hineq (by norm_num : (0 : ℝ) ≤ 1 / 2))
    -- Step 5.2: rewrite both squares so that they match the statement of the comparison.
    have hrewrite :
        sqrt (a n) / (n + 1 : ℝ) ≤
          ((Real.sqrt (a n)) ^ 2 + (1 / (n + 1 : ℝ)) ^ 2) / 2 := by
      simpa [pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, add_comm,
        add_left_comm, add_assoc] using hineq'
    have hsq :
        (Real.sqrt (a n)) ^ 2 = a n := by
      simpa [pow_two] using (Real.mul_self_sqrt (hnneg n))
    have hdivpow :
        (1 / (n + 1 : ℝ)) ^ 2 = 1 / (n + 1 : ℝ) ^ 2 := by
      simp [one_div, pow_two]
    -- Step 5.3: substitute the rewritten squares to obtain the desired inequality.
    simpa [hsq, hdivpow, add_comm, add_left_comm, add_assoc] using hrewrite
  -- Step 6: apply the comparison test for nonnegative real series.
  have hSummableSqrt :
      Summable fun n : ℕ => sqrt (a n) / (n + 1 : ℝ) :=
    Summable.of_nonneg_of_le hNonneg hCompare hDom
  -- Step 7: unpack the summability statement back into the convergence of partial sums.
  have hy := hSummableSqrt.hasSum
  -- Step 7.1: translate `HasSum` back to the requested limit of partial sums.
  refine ⟨∑' n, sqrt (a n) / (n + 1 : ℝ), ?_⟩
  exact (hasSum_iff_tendsto_nat_of_nonneg hNonneg _).1 hy
