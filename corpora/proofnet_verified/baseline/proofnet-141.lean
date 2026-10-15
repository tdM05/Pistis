import Mathlib

open Filter Real Function
open scoped Topology



/-Informal Statement

Prove that $\sum 1/k(\log(k))^p$ diverges when $p \leq 1$.
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

theorem Pugh_exercise_3_63b (p : ℝ) (f : ℕ → ℝ) (hp : p ≤ 1)
  (h : f = λ (k : ℕ) => (1 : ℝ) / (k * (log k) ^ p)) :
  ¬ ∃ l, Tendsto f atTop (𝓝 l) := by
  sorry

/-
The previous formalization is **false**.

Step 1. The original statement encodes a limit for the raw sequence
        `k ↦ 1 / (k * (log k) ^ p)` instead of for its sequence of
        partial sums.
Step 2. A basic counterexample already occurs at `p = 1`.  A direct
        limit computation shows that `lim_{k → ∞} f k = 0`, so a limit
        exists and equals `0`.
Step 3. Therefore the Lean statement contradicts the intended
        divergence claim for the series, and we must keep it unsolved,
        prove its negation, and state a corrected convergent version.
-/

lemma tendsto_log_pow_div_sqrt (p : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ (-p) / x ^ ((1 : ℝ) / 2)) atTop (𝓝 0) := by
  -- Step 1: Convert the analytic fact “log grows slower than any power” into a little-o statement.
  have hLittle :
      (fun x : ℝ => (Real.log x) ^ (-p)) =o[atTop] fun x : ℝ => x ^ ((1 : ℝ) / 2) := by
    -- Step 1.1: Use the dedicated mathlib lemma with `r = -p` and `s = 1/2`.
    simpa using
      (isLittleO_log_rpow_rpow_atTop (r := -p) (s := (1 : ℝ) / 2)
        (by norm_num : 0 < (1 : ℝ) / 2))
  -- Step 2: Translate the little-o statement into the desired limit of the corresponding quotient.
  -- Step 2.1: `IsLittleO.tendsto_div_nhds_zero` exactly states that the quotient tends to `0`.
  simpa using hLittle.tendsto_div_nhds_zero

lemma tendsto_inv_sqrt :
    Tendsto (fun x : ℝ => 1 / x ^ ((1 : ℝ) / 2)) atTop (𝓝 0) := by
  -- Step 1: Express the function via a negative power to apply standard power limits.
  have h_neg :
      Tendsto (fun x : ℝ => x ^ ( -((1 : ℝ) / 2))) atTop (𝓝 0) :=
    -- Step 1.1: Invoke `tendsto_rpow_neg_atTop` with exponent `1/2`.
    tendsto_rpow_neg_atTop (by norm_num : 0 < (1 : ℝ) / 2)
  -- Step 2: Show both expressions agree eventually (for large positive inputs).
  have h_eq :
      (fun x : ℝ => 1 / x ^ ((1 : ℝ) / 2)) =ᶠ[atTop] fun x : ℝ => x ^ ( -((1 : ℝ) / 2)) := by
    -- Step 2.1: For sufficiently large `x` (say `x ≥ 1`) we can rewrite using `Real.rpow_neg`.
    refine (eventually_ge_atTop (1 : ℝ)).mono ?_
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    -- Step 2.2: Apply `Real.rpow_neg` to trade the negative exponent for reciprocals.
    simp [one_div, Real.rpow_neg hx_pos.le]
  -- Step 3: Transport the limit through eventual equality.
  exact (h_neg.congr' h_eq.symm)

lemma tendsto_one_div_mul_log_pow_Real (p : ℝ) :
    Tendsto (fun x : ℝ => 1 / (x * (Real.log x) ^ p)) atTop (𝓝 0) := by
  -- Step 1: Build the product of the two auxiliary limits from the previous lemmas.
  have h1 := tendsto_log_pow_div_sqrt p
  have h2 := tendsto_inv_sqrt
  have h_temp :
      Tendsto
          (fun x : ℝ =>
            ((Real.log x) ^ (-p) / x ^ ((1 : ℝ) / 2)) * (1 / x ^ ((1 : ℝ) / 2)))
          atTop (𝓝 0) := by
    simpa [zero_mul] using Tendsto.mul h1 h2
  -- Step 2: Simplify the auxiliary expression step by step using eventual equalities.
  have h_to_ratio :
      (fun x : ℝ =>
          ((Real.log x) ^ (-p) / x ^ ((1 : ℝ) / 2)) * (1 / x ^ ((1 : ℝ) / 2)))
        =ᶠ[atTop] fun x : ℝ => ((Real.log x) ^ (-p)) / x := by
    refine (eventually_ge_atTop (1 : ℝ)).mono ?_
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hx_half_pos : 0 < x ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hx_pos _
    have hx_half_ne : x ^ ((1 : ℝ) / 2) ≠ 0 := (ne_of_gt hx_half_pos)
    have hx_sum : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = (1 : ℝ) := by norm_num
    have hx_pow :
        x ^ (2 : ℝ)⁻¹ * x ^ (2 : ℝ)⁻¹ = x := by
      have := (Real.rpow_add hx_pos ((1 : ℝ) / 2) ((1 : ℝ) / 2)).symm
      simpa [hx_sum, Real.rpow_one, mul_comm, mul_left_comm] using this
    have hx_step :
        ((Real.log x) ^ (-p) / x ^ ((1 : ℝ) / 2)) * (1 / x ^ ((1 : ℝ) / 2))
          = ((Real.log x) ^ (-p)) / (x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2)) := by
      field_simp [hx_half_ne, div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc]
    have hx_eq :
        ((Real.log x) ^ (-p) / x ^ ((1 : ℝ) / 2)) * (1 / x ^ ((1 : ℝ) / 2))
          = ((Real.log x) ^ (-p)) / x := by
      simpa [hx_pow] using hx_step
    simpa using hx_eq
  have h_ratio :
      Tendsto (fun x : ℝ => ((Real.log x) ^ (-p)) / x) atTop (𝓝 0) :=
    h_temp.congr' h_to_ratio
  have h_final_eq :
      (fun x : ℝ => ((Real.log x) ^ (-p)) / x)
        =ᶠ[atTop] fun x : ℝ => 1 / (x * (Real.log x) ^ p) := by
    refine (eventually_ge_atTop (2 : ℝ)).mono ?_
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_two hx
    have hx_gt_one : 1 < x := lt_of_lt_of_le one_lt_two hx
    have hlog_pos : 0 < Real.log x := Real.log_pos hx_gt_one
    have hx_ne : x ≠ 0 := hx_pos.ne'
    have hlog_ne : Real.log x ≠ 0 := hlog_pos.ne'
    calc
      ((Real.log x) ^ (-p)) / x
          = (Real.log x ^ p)⁻¹ * x⁻¹ := by
              simp [div_eq_mul_inv, Real.rpow_neg hlog_pos.le]
      _ = 1 / (x * (Real.log x) ^ p) := by
              simp [div_eq_mul_inv]
  exact (h_ratio.congr' h_final_eq)

lemma tendsto_one_div_mul_log_pow_nat (p : ℝ) :
    Tendsto (fun k : ℕ => 1 / (k * (Real.log k) ^ p)) atTop (𝓝 0) := by
  -- Step 1: Use the real-variable limit and compose with the embedding `ℕ → ℝ`.
  have hReal := tendsto_one_div_mul_log_pow_Real p
  -- Step 2: The composition with `Nat.cast` keeps the limit unchanged.
  simpa using hReal.comp tendsto_natCast_atTop_atTop

theorem Pugh_exercise_3_63b_neg (p : ℝ) (f : ℕ → ℝ) (_hp : p ≤ 1)
    (h : f = fun k : ℕ => 1 / (k * (Real.log k) ^ p)) :
    ∃ l, Tendsto f atTop (𝓝 l) := by
  -- Step 1: Identify the concrete limit (it is zero for all real `p`, so `hp` is unused).
  have hLimit := tendsto_one_div_mul_log_pow_nat p
  -- Step 2: Transfer the limit to `f` via the provided identity.
  refine ⟨0, ?_⟩
  -- Step 3: Rewrite the sequence with the supplied definition.
  simpa [h] using hLimit

/-
Corrected formulation (faithful):

Pugh's claim is that the **series** `∑ 1/(k · (log k)^p)` diverges when
`p ≤ 1`, not that the *terms* tend to zero. (For `p ≤ 1` the terms in fact
do tend to zero — that is exactly why the original Lean statement, which
asserts existence of a sequence-limit, fails to capture divergence.) The
faithful translation of "diverges" is `¬ Summable f`.

Proof sketch (not formalized here):

* Apply the Cauchy condensation test (`Real.summable_condensed_iff_of_eventually_nonneg`)
  to `f`, which is eventually nonnegative and eventually antitone.
* The condensed sequence simplifies to `(log 2)^{-p} · n^{-p}`, i.e. a
  positive multiple of the `p`-series with exponent `p`.
* For `p ≤ 1`, the `p`-series diverges by `Real.summable_one_div_nat_rpow`,
  hence so does the original series.
-/

theorem Pugh_exercise_3_63b_corrected (p : ℝ) (f : ℕ → ℝ) (hp : p ≤ 1)
    (h : f = fun k : ℕ => 1 / (k * (Real.log k) ^ p)) :
    ¬ Summable f := by
  classical
  subst h
  -- Helper: `log 3 > 1`, since `e < 3`.
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    have hexp : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    have hlt := Real.log_lt_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at hlt
  -- Step 1: Prove the boundary `p = 1` case (Bertrand series) via Cauchy condensation.
  have hbertrand : ¬ Summable (fun k : ℕ => 1 / ((k : ℝ) * Real.log k)) := by
    intro hb
    -- Step 1.1: The summand is eventually nonneg (for `k ≥ 2`).
    have hnn : 0 ≤ᶠ[atTop] (fun k : ℕ => 1 / ((k : ℝ) * Real.log k)) := by
      filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with k hk
      have hkR_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
      have hlog_pos : 0 < Real.log k :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < k))
      positivity
    -- Step 1.2: It is also eventually antitone (for `k ≥ 2`).
    have hmono : ∀ᶠ k in (atTop : Filter ℕ),
        1 / (((k + 1 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ))
          ≤ 1 / ((k : ℝ) * Real.log k) := by
      filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with k hk
      have hkR_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
      have hk1R_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) :=
        by exact_mod_cast (by omega : 0 < k + 1)
      have hlogk_pos : 0 < Real.log k :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < k))
      have hlogk1_pos : 0 < Real.log ((k + 1 : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < k + 1))
      have hk_le : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
      have hlog_le : Real.log k ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
        Real.log_le_log hkR_pos hk_le
      have hmul_le :
          (k : ℝ) * Real.log k ≤ ((k + 1 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ) :=
        mul_le_mul hk_le hlog_le hlogk_pos.le hk1R_pos.le
      exact one_div_le_one_div_of_le (mul_pos hkR_pos hlogk_pos) hmul_le
    -- Step 1.3: Apply Cauchy condensation: now `hb` is on the condensed sequence.
    rw [← summable_condensed_iff_of_eventually_nonneg hnn hmono] at hb
    -- Step 1.4: For `k ≥ 1`, `2^k · (1 / (2^k · log 2^k)) = 1 / (k · log 2)`.
    rw [← summable_nat_add_iff 1] at hb
    have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hsimp :
        (fun k : ℕ =>
            (2 : ℝ) ^ (k + 1) *
              (1 / (((2 ^ (k + 1) : ℕ) : ℝ) * Real.log ((2 ^ (k + 1) : ℕ) : ℝ))))
          = fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) * Real.log 2) := by
      funext k
      have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
      have h2k_ne : ((2 : ℝ) ^ (k + 1)) ≠ 0 := h2k_pos.ne'
      have hcast : ((2 ^ (k + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (k + 1) := by push_cast; rfl
      have hlog : Real.log ((2 : ℝ) ^ (k + 1)) = ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
        rw [Real.log_pow]
      rw [hcast, hlog]
      have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) :=
        by exact_mod_cast (Nat.succ_pos k)
      field_simp
    rw [hsimp] at hb
    -- Step 1.5: Multiplying by `log 2` reduces to the harmonic series.
    have hb' : Summable (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ))) := by
      have hmul := hb.mul_left (Real.log 2)
      have heq :
          (fun k : ℕ => Real.log 2 * (1 / (((k + 1 : ℕ) : ℝ) * Real.log 2)))
            = fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ)) := by
        funext k
        have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) :=
          by exact_mod_cast (Nat.succ_pos k)
        field_simp
      rwa [heq] at hmul
    exact not_summable_one_div_natCast
      ((summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / n) 1).mp hb')
  -- Step 2: For arbitrary `p ≤ 1`, compare with the Bertrand series at `p = 1`.
  intro hsum
  apply hbertrand
  -- Step 2.1: Shift past `k < 3` to apply the comparison cleanly.
  rw [← summable_nat_add_iff 3]
  refine ((summable_nat_add_iff 3).mpr hsum).of_nonneg_of_le ?nn ?bound
  -- Step 2.2: Each `1/((k+3) · log(k+3))` is nonneg for `k ≥ 0`.
  · intro n
    have hk_one : (1 : ℝ) < ((n + 3 : ℕ) : ℝ) :=
      by exact_mod_cast (by omega : 1 < n + 3)
    have hlog_pos : 0 < Real.log ((n + 3 : ℕ) : ℝ) := Real.log_pos hk_one
    have hk_pos : (0 : ℝ) < ((n + 3 : ℕ) : ℝ) :=
      by exact_mod_cast (by omega : 0 < n + 3)
    positivity
  -- Step 2.3: For `k ≥ 3` and `p ≤ 1`, `(log k)^p ≤ log k`, hence the desired inequality.
  · intro n
    have hk3 : (3 : ℝ) ≤ ((n + 3 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_add_left 3 n)
    have hk_one : (1 : ℝ) < ((n + 3 : ℕ) : ℝ) :=
      by exact_mod_cast (by omega : 1 < n + 3)
    have hk_pos : (0 : ℝ) < ((n + 3 : ℕ) : ℝ) :=
      by exact_mod_cast (by omega : 0 < n + 3)
    have hlog_pos : 0 < Real.log ((n + 3 : ℕ) : ℝ) := Real.log_pos hk_one
    have hlog_ge_one : (1 : ℝ) ≤ Real.log ((n + 3 : ℕ) : ℝ) := by
      have hle := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hk3
      linarith
    have hpow_le :
        Real.log ((n + 3 : ℕ) : ℝ) ^ p ≤ Real.log ((n + 3 : ℕ) : ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_le hlog_ge_one hp
      simpa [Real.rpow_one] using h
    have hpow_pos : 0 < Real.log ((n + 3 : ℕ) : ℝ) ^ p :=
      Real.rpow_pos_of_pos hlog_pos p
    have hmul_le :
        ((n + 3 : ℕ) : ℝ) * Real.log ((n + 3 : ℕ) : ℝ) ^ p
          ≤ ((n + 3 : ℕ) : ℝ) * Real.log ((n + 3 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hpow_le hk_pos.le
    exact one_div_le_one_div_of_le (mul_pos hk_pos hpow_pos) hmul_le
