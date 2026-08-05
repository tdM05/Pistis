import Mathlib

open Filter Real Function
open scoped Topology



/-Informal Statement

Prove that $\sum 1/k(\log(k))^p$ converges when $p > 1$.
-/

/-Informal Proof

Using the integral test, for a set $a$, we see
$$
\lim _{b \rightarrow \infty} \int_a^b \frac{1}{x \log (x)^c} d x=\lim _{b \rightarrow \infty}\left(\frac{\log (b)^{1-c}}{1-c}-\frac{\log (a)^{1-c}}{1-c}\right)
$$
which goes to infinity if $c \leq 1$ and converges if $c>1$. Thus,
$$
\sum_{n=2}^{\infty} \frac{1}{n \log (n)^c}
$$
converges if and only if $c>1$.
-/

theorem Pugh_exercise_3_63a (p : ℝ) (f : ℕ → ℝ) (hp : p > 1)
  (h : f = λ (k : ℕ) => (1 : ℝ) / (k * (log k) ^ p)) :
  ∃ l, Tendsto f atTop (𝓝 l) := by
  -- Step 1: Fix the candidate limit to be `0` and translate the goal using the definition of `f`.
  refine ⟨0, ?_⟩
  -- Step 1.1: It suffices to show that the explicit reciprocal sequence tends to `0`.
  have hgoal :
      Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) * (Real.log k) ^ p)) atTop (𝓝 (0 : ℝ)) := by
    -- Step 2: Introduce the positive constant `C = (log 2)^p`, which bounds the logarithmic term from below.
    set C : ℝ := (Real.log 2) ^ p with hC_def
    -- Step 2.1: Record positivity data for `log 2`, the exponent `p`, and `C`.
    have hlog2_pos : 0 < Real.log 2 := by
      -- Step 2.1.1: `log` is positive on numbers larger than `1`, so apply it to `2`.
      simpa using Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    have hp_pos : 0 < p := lt_trans zero_lt_one hp
    have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
    have hC_pos : 0 < C := by
      -- Step 2.1.2: A positive base raised to any real exponent remains positive.
      simpa [hC_def] using Real.rpow_pos_of_pos hlog2_pos p
    have hC_ne_zero : C ≠ 0 := ne_of_gt hC_pos
    -- Step 3: Register that the auxiliary sequence `1 / k` tends to `0`.
    have hone_div :
        Tendsto (fun k : ℕ => (1 : ℝ) / k) atTop (𝓝 (0 : ℝ)) := by
      -- Step 3.1: Compose `tendsto_inv_atTop_zero` with the natural inclusion `ℕ → ℝ`.
      have h_inv := (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 (0 : ℝ)))
      have hcast : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop
      -- Step 3.1.1: Simplify the composition to obtain the desired statement about `1 / k`.
      simpa [Function.comp, one_div] using h_inv.comp hcast
    -- Step 4: Define the upper comparison function `g k = (1 / C) * (1 / k)` and record its limit.
    let g : ℕ → ℝ := fun k => (1 / C) * ((1 : ℝ) / k)
    have hg_limit : Tendsto g atTop (𝓝 (0 : ℝ)) := by
      -- Step 4.1: Multiply the previous limit by the constant `1 / C`.
      simpa [g, zero_mul] using (Filter.Tendsto.const_mul (1 / C) hone_div)
    -- Step 5: Show that the target sequence is eventually squeezed between `0` and `g`.
    have h_nonneg :
        ∀ᶠ k : ℕ in atTop, 0 ≤ (1 : ℝ) / ((k : ℝ) * (Real.log k) ^ p) := by
      -- Step 5.1: Restrict attention to `k ≥ 2`, where every factor is positive.
      refine (eventually_ge_atTop (2 : ℕ)).mono ?_
      intro k hk
      -- Step 5.1.1: Translate `k ≥ 2` into the positivity of `k` and `log k`.
      have hk_pos_nat : 0 < k := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk
      have hk_gt_one_nat : 1 < k := lt_of_lt_of_le one_lt_two hk
      have hk_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr hk_pos_nat
      have hk_gt_one : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk_gt_one_nat
      have hlog_pos : 0 < Real.log k := Real.log_pos hk_gt_one
      -- Step 5.1.2: The denominator is positive, so the whole fraction is nonnegative.
      have hden_pos : 0 < (k : ℝ) * (Real.log k) ^ p :=
        mul_pos hk_pos (Real.rpow_pos_of_pos hlog_pos p)
      exact (div_pos zero_lt_one hden_pos).le
    have h_upper :
        ∀ᶠ k : ℕ in atTop,
          (1 : ℝ) / ((k : ℝ) * (Real.log k) ^ p) ≤ g k := by
      -- Step 5.2: Again work on the tail `k ≥ 2` to compare logarithmic factors.
      refine (eventually_ge_atTop (2 : ℕ)).mono ?_
      intro k hk
      have hk_pos_nat : 0 < k := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk
      have hk_nonneg : 0 ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
      have hk_real_ge_two : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      -- Step 5.2.1: Use the monotonicity of `log` to bound `(log k)` below by `(log 2)`.
      have hlog_mono : Real.log 2 ≤ Real.log k :=
        Real.log_le_log (show 0 < (2 : ℝ) by norm_num) hk_real_ge_two
      have hpow_le : C ≤ (Real.log k) ^ p :=
        Real.rpow_le_rpow (le_of_lt hlog2_pos) hlog_mono hp_nonneg
      have h_inv_le : 1 / (Real.log k) ^ p ≤ 1 / C :=
        one_div_le_one_div_of_le hC_pos hpow_le
      have h_mul :=
        mul_le_mul_of_nonneg_right h_inv_le
          (one_div_nonneg.mpr hk_nonneg)
      -- Step 5.2.2: Rewrite the inequality to match the desired expressions.
      have hk_bound :
          (1 : ℝ) / ((k : ℝ) * (Real.log k) ^ p)
              ≤ (1 / C) * ((1 : ℝ) / k) := by
        simpa [g, one_div, mul_comm, mul_left_comm, mul_assoc]
          using h_mul
      exact hk_bound
    -- Step 6: Combine the bounds through the squeeze theorem to obtain the desired limit.
    have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le' hzero hg_limit h_nonneg h_upper
  -- Step 1.2: Translate the proven limit back to `f` using the defining equation.
  simpa [h] using hgoal

/-
The original formalization is not faithful to the informal statement.

The informal statement asserts convergence of the **series** ∑ 1/(k (log k)^p) for p > 1,
i.e., the partial sums have a finite limit. The Lean formalization instead asserts that the
**sequence of terms** f(k) = 1/(k (log k)^p) tends to some limit l. These are completely
different claims: the terms tend to 0 trivially (even when p ≤ 1 and the series diverges),
so the Lean statement is much weaker and does not capture series convergence at all.

The correction uses `Summable` to properly express that the series converges. We shift the
index by 2 (summing over k+2) to avoid the singularity at k=0 (where log 0 is undefined)
and k=1 (where log 1 = 0 makes the denominator zero). This gives the sum
1/(2 log²2) + 1/(3 log³3) + ... which is exactly ∑_{k=2}^∞ 1/(k (log k)^p).
-/


theorem Pugh_exercise_3_63a_corrected (p : ℝ) (hp : p > 1) :
  Summable (fun (k : ℕ) => (1 : ℝ) / ((k + 2) * (Real.log (k + 2)) ^ p)) := by
  have hp_pos : (0 : ℝ) < p := by linarith
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  -- Step 1: reduce to summability of g(n) = 1/(n*(log n)^p) via index shift.
  -- Our function is g ∘ (· + 2); by summable_nat_add_iff, shifting preserves summability.
  suffices key : Summable (fun n : ℕ => (1 : ℝ) / ((↑n : ℝ) * (Real.log (↑n : ℝ)) ^ p)) by
    -- Step 1.1: show our function equals g composed with the shift (· + 2).
    have heq : (fun k : ℕ => (1 : ℝ) / ((↑k + 2) * (Real.log (↑k + 2)) ^ p)) =
      (fun n : ℕ => (1 : ℝ) / ((↑n : ℝ) * (Real.log (↑n : ℝ)) ^ p)) ∘ (· + 2) := by
      ext k; simp [Function.comp]
    -- Step 1.2: apply the shift equivalence.
    rw [heq]; exact (summable_nat_add_iff (G := ℝ) 2).mpr key
  -- Step 2: apply the Cauchy condensation test to g.
  -- The test says: for eventually nonneg and eventually antitone f,
  -- Summable (fun k => 2^k * f(2^k)) ↔ Summable f.
  rw [← summable_condensed_iff_of_eventually_nonneg]
  · -- Step 3: show the condensed series is summable.
    -- The condensed series is k ↦ 2^k * g(2^k) = 2^k / (2^k * (k*log2)^p) = 1/(k*log2)^p
    -- = (log2)^(-p) * k^(-p), a constant multiple of the convergent p-series ∑ k^(-p).
    -- Step 3.1: Start from the standard p-series theorem.
    have hpseries : Summable (fun k : ℕ => (1 : ℝ) / (k : ℝ) ^ p) :=
      Real.summable_one_div_nat_rpow.mpr hp
    -- Step 3.2: Multiplying a summable series by a fixed real constant preserves summability.
    have hscaled :
        Summable (fun k : ℕ => (Real.log 2) ^ (-p) * ((1 : ℝ) / (k : ℝ) ^ p)) :=
      hpseries.mul_left ((Real.log 2) ^ (-p))
    -- Step 3.3: It remains to identify the condensed series with this scaled p-series on the
    -- tail `k ≥ 1`.  The term `k = 0` is irrelevant for summability.
    exact hscaled.congr_atTop <| by
      filter_upwards [eventually_ge_atTop 1] with k hk
      -- Step 3.3.1: Convert the tail condition into positivity of `k` as a real number.
      have hk_pos_nat : 0 < k := by omega
      have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk_pos_nat
      -- Step 3.3.2: Record the nonzero facts needed for the field simplification.
      have h2pow_ne : ((2 : ℝ) ^ k) ≠ 0 := pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0)
      have hk_rpow_ne : ((k : ℝ) ^ p) ≠ 0 :=
        ne_of_gt (Real.rpow_pos_of_pos hk_pos p)
      have hlog2_rpow_ne : (Real.log 2) ^ p ≠ 0 :=
        ne_of_gt (Real.rpow_pos_of_pos hlog2_pos p)
      -- Step 3.3.3: Rewrite `log (2^k)` as `k * log 2`.
      have hlog_pow : Real.log (((2 : ℕ) ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log 2 := by
        simp [Nat.cast_pow, Real.log_pow]
      -- Step 3.3.4: Rewrite `(k * log 2)^p` as `k^p * (log 2)^p`.
      have hmul_rpow : ((k : ℝ) * Real.log 2) ^ p =
          (k : ℝ) ^ p * (Real.log 2) ^ p := by
        exact Real.mul_rpow (le_of_lt hk_pos) (le_of_lt hlog2_pos)
      -- Step 3.3.5: Complete the algebraic identification of the condensed term.
      have hmain :
          (Real.log 2) ^ (-p) * ((1 : ℝ) / (k : ℝ) ^ p) =
            (2 : ℝ) ^ k *
              ((1 : ℝ) / ((2 : ℝ) ^ k * (((k : ℝ) * Real.log 2) ^ p))) := by
        rw [Real.rpow_neg (le_of_lt hlog2_pos), hmul_rpow]
        field_simp [h2pow_ne, hk_rpow_ne, hlog2_rpow_ne]
      simpa [Nat.cast_pow, hlog_pow] using hmain
  · -- Step 4: g is eventually nonneg (for n ≥ 2, all factors in the denominator are positive).
    filter_upwards [eventually_ge_atTop 2] with n hn
    apply div_nonneg one_pos.le
    apply mul_nonneg (Nat.cast_nonneg' n)
    exact rpow_nonneg (Real.log_nonneg (show (1:ℝ) ≤ (n:ℝ) from by
      exact_mod_cast (show 1 ≤ n from by omega))) p
  · -- Step 5: g is eventually antitone (for n ≥ 2, increasing n increases the denominator).
    filter_upwards [eventually_ge_atTop 2] with k hk
    -- Step 5.1: establish positivity of k and log k.
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
    have hlogk_pos : 0 < Real.log (k : ℝ) :=
      Real.log_pos (show (1 : ℝ) < (k : ℝ) from by exact_mod_cast (show 1 < k from by omega))
    -- Step 5.2: since the numerator is constant (= 1) and positive, it suffices to show
    -- the denominator is nondecreasing: k*(log k)^p ≤ (k+1)*(log(k+1))^p.
    apply div_le_div_of_nonneg_left one_pos.le (mul_pos hk_pos (rpow_pos_of_pos hlogk_pos p))
    -- Step 5.3: the product k*(log k)^p is nondecreasing because both factors are.
    exact mul_le_mul (by exact_mod_cast Nat.le_succ k)
      (rpow_le_rpow hlogk_pos.le
        (Real.log_le_log hk_pos (by exact_mod_cast Nat.le_succ k)) (by linarith))
      (rpow_nonneg hlogk_pos.le p) (by exact_mod_cast (show 0 ≤ k + 1 from Nat.zero_le _))
