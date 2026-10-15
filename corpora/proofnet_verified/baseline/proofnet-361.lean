import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology



/-Informal Statement

Prove that the power series $\sum nz^n$ does not converge on any point of the unit circle.
-/

/-Informal Proof

For $z \in S:=\{z \in \mathbb{C}:|z|=1\}$ it also holds $z^n \in S$ for all $n \in \mathbb{N}$ (since in this case $\left.\left|z^n\right|=|z|^n=1^n=1\right)$
Thus, the sequence $\left(a_n\right)_{n \in \mathbb{N}}$ with $a_n=n z^n$ does not converge to zero which is necessary for the corresponding sum $\sum_{n \in \mathbb{N}} a_n$ to be convergent. Hence this sum does not converge.
-/

theorem Shakarchi_exercise_1_19a (z : ℂ) (hz : ‖z‖ = 1) (s : ℕ → ℂ)
    (h : s = (λ n => ∑ i ∈ (range n), i * z ^ i)) :
    ¬ ∃ y, Tendsto s atTop (𝓝 y) := by
  -- Step 1: Assume, for contradiction, that the sequence `s` converges to some limit.
  intro hconv
  -- Step 1.1: Unpack the hypothetical limit and record it as `ℓ`.
  rcases hconv with ⟨ℓ, hℓ⟩
  -- Step 2: Describe the difference of two consecutive partial sums explicitly.
  have hdiff : ∀ n, s (n + 1) - s n = (n : ℂ) * z ^ n := by
    -- Step 2.1: Express both `s (n + 1)` and `s n` via the given closed form.
    intro n
    have hsucc : s (n + 1) = ∑ i ∈ range (n + 1), i * z ^ i := by
      simpa using congrArg (fun f => f (n + 1)) h
    have hbase : s n = ∑ i ∈ range n, i * z ^ i := by
      simpa using congrArg (fun f => f n) h
    -- Step 2.2: Peel off the last term of the range sum to identify the increment.
    have : s (n + 1) = s n + (n : ℂ) * z ^ n := by
      simp [hsucc, hbase, sum_range_succ]
    -- Step 2.3: Turn the increment identity into our desired difference formula.
    calc
      s (n + 1) - s n
          = (s n + (n : ℂ) * z ^ n) - s n := by simp [this]
      _ = (n : ℂ) * z ^ n := by simp
  -- Step 3: Use convergence to `ℓ` to find a uniform ball eventually containing the sequence.
  have half_pos : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
  have h_close_set :
      ∀ᶠ n in atTop, s n ∈ Metric.ball ℓ ((1 : ℝ) / 2) :=
    hℓ.eventually (Metric.ball_mem_nhds _ half_pos)
  -- Step 3.1: Rewrite the ball condition as a norm inequality around the limit.
  have h_close : ∀ᶠ n in atTop, ‖s n - ℓ‖ < (1 : ℝ) / 2 := by
    refine h_close_set.mono ?_
    intro n hn
    simpa [Metric.ball, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hn
  -- Step 3.2: Convert the eventual condition into an explicit integer threshold `N`.
  obtain ⟨N, hN⟩ := eventually_atTop.1 h_close
  -- Step 4: Choose `n₀` past both `N` and `1` so that successive terms are simultaneously close.
  set n₀ := max N 1 with hn₀_def
  have hN_le : N ≤ n₀ := by
    -- Step 4.1: `n₀` dominates `N` by construction.
    simp [hn₀_def]
  have hone_le : 1 ≤ n₀ := by
    -- Step 4.2: `n₀` is also at least `1`, again by construction.
    simp [hn₀_def]
  have h_bound_n₀ : ‖s n₀ - ℓ‖ < (1 : ℝ) / 2 := hN _ hN_le
  have h_bound_succ : ‖s (n₀ + 1) - ℓ‖ < (1 : ℝ) / 2 :=
    hN _ (le_trans hN_le (Nat.le_succ _))
  -- Step 4.3: Deduce that the difference between consecutive terms eventually has norm < 1.
  have h_sum_lt : ‖s (n₀ + 1) - ℓ‖ + ‖s n₀ - ℓ‖ < 1 := by
    have htmp := add_lt_add h_bound_succ h_bound_n₀
    calc
      ‖s (n₀ + 1) - ℓ‖ + ‖s n₀ - ℓ‖
          < (1 : ℝ) / 2 + (1 : ℝ) / 2 := htmp
      _ = 1 := by norm_num
  have h_diff_lt_one : ‖s (n₀ + 1) - s n₀‖ < 1 := by
    have h_le : ‖s (n₀ + 1) - s n₀‖ ≤ ‖s (n₀ + 1) - ℓ‖ + ‖s n₀ - ℓ‖ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (norm_sub_le (s (n₀ + 1) - ℓ) (s n₀ - ℓ))
    exact lt_of_le_of_lt h_le h_sum_lt
  -- Step 5: Translate the difference estimate into the behavior of the term `(n₀ : ℂ) * z ^ n₀`.
  have h_term_lt_one : ‖(n₀ : ℂ) * z ^ n₀‖ < 1 := by
    simpa [hdiff n₀] using h_diff_lt_one
  -- Step 5.1: Compute the norm of the term using `|z| = 1`.
  have hz_pow : ‖z ^ n₀‖ = (1 : ℝ) := by
    simp [hz, one_pow]
  have hnorm_nat : ‖(n₀ : ℂ)‖ = (n₀ : ℝ) := by
    simp
  have h_norm_term : ‖(n₀ : ℂ) * z ^ n₀‖ = (n₀ : ℝ) := by
    simp [hz_pow]
  -- Step 6: Conclude the contradiction: `(n₀ : ℝ)` is simultaneously ≥ 1 and < 1.
  have hlt : (n₀ : ℝ) < 1 := by
    exact (h_norm_term ▸ h_term_lt_one)
  have hge : (1 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hone_le
  have : (1 : ℝ) < (1 : ℝ) := lt_of_le_of_lt hge hlt
  exact (lt_irrefl _ this).elim
