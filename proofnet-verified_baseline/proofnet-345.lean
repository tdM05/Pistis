import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Prove that the Cauchy product of two absolutely convergent series converges absolutely.
-/

/-Informal Proof

Since both the hypothesis and conclusion refer to absolute convergence, we may assume both series consist of nonnegative terms. We let $S_n=\sum_{k=0}^n a_n, T_n=\sum_{k=0}^n b_n$, and $U_n=\sum_{k=0}^n \sum_{l=0}^k a_l b_{k-l}$. We need to show that $U_n$ remains bounded, given that $S_n$ and $T_n$ are bounded. To do this we make the convention that $a_{-1}=T_{-1}=0$, in order to save ourselves from having to separate off the first and last terms when we sum by parts. We then have
$$
\begin{aligned}
U_n &=\sum_{k=0}^n \sum_{l=0}^k a_l b_{k-l} \\
&=\sum_{k=0}^n \sum_{l=0}^k a_l\left(T_{k-l}-T_{k-l-1}\right) \\
&=\sum_{k=0}^n \sum_{j=0}^k a_{k-j}\left(T_j-T_{j-1}\right) \\
&=\sum_{k=0}^n \sum_{j=0}^k\left(a_{k-j}-a_{k-j-1}\right) T_j \\
&=\sum_{j=0}^n \sum_{k=j}^n\left(a_{k-j}-a_{k-j-1}\right) T_j
&=\sum_{j=0}^n a_{n-j} T_j \\
&\leq T \sum_{m=0}^n a_m \\
&=T S_n \\
&\leq S T .
\end{aligned}
$$
Thus $U_n$ is bounded, and hence approaches a finite limit.
-/

theorem Rudin_exercise_3_13
  (a b : ℕ → ℝ)
  (ha : ∃ y, (Tendsto (λ n => (∑ i ∈ (range n), |a i|)) atTop (𝓝 y)))
  (hb : ∃ y, (Tendsto (λ n => (∑ i ∈ (range n), |b i|)) atTop (𝓝 y))) :
  ∃ y, (Tendsto (λ n => (∑ i ∈ (range n),
  |λ i => (∑ j ∈ range (i + 1), a j * b (i - j))|)) atTop (𝓝 y)) := by
  sorry

/-
Step 0: Explain why `Rudin_exercise_3_13` is false.
Step 0.1: The absolute value in the conclusion wraps the constant function `λ i => …`.
Step 0.2: Summing this function over `range n` produces the same function repeated `n` times, so
the resulting term takes values `k ↦ n • |∑ j a j * b (k - j)|`.
Step 0.3: Unless the Cauchy product is identically zero, the value at `k = 0` grows linearly with
`n`, hence the sequence inside the limit can never converge in `(ℕ → ℝ)`.
Step 0.4: Choosing sequences with `a 0 = b 0 = 1` and everything else zero provides a concrete
counterexample that meets the hypotheses but makes the conclusion fail.
-/

section Counterexample

open scoped BigOperators

/-- Step 1: define the spike sequence that is `1` at `0` and vanishes elsewhere. -/
def spike : ℕ → ℝ :=
  fun n => if n = 0 then 1 else 0

@[simp] lemma spike_zero : spike 0 = 1 := by
  -- Step 1.1: unfold the definition at zero.
  simp [spike]

@[simp] lemma spike_succ (n : ℕ) : spike (n + 1) = 0 := by
  -- Step 1.2: for positive indices the conditional takes the `else` branch.
  simp [spike]

@[simp] lemma abs_spike (n : ℕ) : |spike n| = spike n := by
  -- Step 2: `spike` only takes the values `0` and `1`, so its absolute value is itself.
  by_cases h : n = 0
  · -- Step 2.1: evaluate the zero case.
    subst h
    simp
  · -- Step 2.2: evaluate the positive case.
    simp [spike, h]

lemma sum_spike_succ (n : ℕ) :
    (∑ i ∈ range (n + 1), spike i) = 1 := by
  -- Step 3: the plain spike sequence sums to `1` on every nonempty range.
  classical
  have hmem : (0 : ℕ) ∈ range (n + 1) := by
    simp
  refine Finset.sum_eq_single 0 ?_ ?_
  · intro b hb hb0
    simp [spike, hb0]
  · intro hnot
    exact (hnot hmem).elim

lemma sum_abs_spike (n : ℕ) :
    (∑ i ∈ range n, |spike i|) = if n = 0 then 0 else 1 := by
  -- Step 3: show the partial sums of `|spike|` are `0` at `n = 0` and `1` afterwards.
  classical
  cases n with
  | zero =>
      simp
  | succ m =>
      have hsum := sum_spike_succ m
      simp [abs_spike, hsum]

lemma tendsto_sum_abs_spike :
    Tendsto (fun n => ∑ i ∈ range n, |spike i|) atTop (𝓝 (1 : ℝ)) := by
  -- Step 4: after the first step the partial sums stay constant.
  have hEvent :
      (fun n : ℕ => ∑ i ∈ range n, |spike i|) =ᶠ[atTop]
        fun _ => (1 : ℝ) := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨1, ?_⟩
    intro n hn
    cases n with
    | zero =>
        cases (lt_irrefl _ (lt_of_lt_of_le (show 0 < (1 : ℕ) by decide) hn))
    | succ m =>
        simp [sum_spike_succ, abs_spike]
  exact (tendsto_congr' hEvent).mpr tendsto_const_nhds

lemma spike_convolution (n : ℕ) :
    (∑ j ∈ range (n + 1), spike j * spike (n - j)) = spike n := by
  -- Step 5: compute the Cauchy product term-by-term.
  classical
  cases n with
  | zero =>
      -- Step 5.1: only `j = 0` appears.
      simp
  | succ n =>
      -- Step 5.2: every summand is zero when `n ≥ 0`.
      have hterm :
          ∀ j ∈ range (Nat.succ n + 1),
            spike j * spike (Nat.succ n - j) = 0 := by
        intro j hj
        by_cases hj0 : j = 0
        · -- Step 5.2.1: `j = 0` makes the second factor vanish.
          subst hj0
          simp
        · -- Step 5.2.2: otherwise the first factor vanishes.
          simp [spike, hj0]
      have :
          (∑ j ∈ range (Nat.succ n + 1), spike j * spike (Nat.succ n - j)) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro j hj
        simpa using hterm j hj
      simp [this]

lemma conv_sum_eval (n : ℕ) :
    ((∑ _i ∈ range n,
        |(fun k : ℕ =>
            ∑ j ∈ range (k + 1), spike j * spike (k - j))|) 0) = (n : ℝ) := by
  -- Step 6: evaluate the pathological sum at `0`.
  classical
  set g := fun k : ℕ => ∑ j ∈ range (k + 1), spike j * spike (k - j)
  have hfun :
      (∑ i ∈ range n, fun k : ℕ => |g k|) 0 =
        ∑ i ∈ range n, |g 0| := by
    simp [Finset.sum_apply]
  have hg0 : |g 0| = (1 : ℝ) := by
    simp [g, spike_convolution]
  have hconst :
      ∑ i ∈ range n, |g 0| = (n : ℝ) := by
    simp [Finset.card_range, nsmul_eq_mul, hg0]
  -- Step 6.2: combine the equalities.
  simp [hconst]

lemma not_tendsto_nat (c : ℝ) :
    ¬ Tendsto (fun n : ℕ => (n : ℝ)) atTop (𝓝 c) := by
  -- Step 7: prove the natural numbers diverge away from any finite limit.
  intro h
  -- Step 7.1: specialize the definition with `ε = 1`.
  have hball :
      (fun n : ℕ => (n : ℝ)) ⁻¹' Metric.ball c 1 ∈ atTop := by
    exact h (Metric.ball_mem_nhds c (by norm_num))
  -- Step 7.2: translate membership in `atTop` into an index bound.
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hball
  -- Step 7.3: pick an index beyond both `N` and `c + 2`.
  let M := max N (Nat.ceil (c + 2))
  have hM_ge_N : N ≤ M := le_max_left _ _
  have hdist := hN M hM_ge_N
  have hceil : (c + 2 : ℝ) ≤ (Nat.ceil (c + 2) : ℝ) := Nat.le_ceil _
  have hM_ge_ceil_nat : Nat.ceil (c + 2) ≤ M := le_max_right _ _
  have hM_ge_ceil : (Nat.ceil (c + 2) : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast hM_ge_ceil_nat
  have hMge : (M : ℝ) ≥ c + 2 := hceil.trans hM_ge_ceil
  have hpos : 0 ≤ (M : ℝ) - c := by
    linarith
  have hineq : |(M : ℝ) - c| ≥ 2 := by
    have hlarge : (M : ℝ) - c ≥ 2 := by
      linarith
    have : |(M : ℝ) - c| = (M : ℝ) - c := abs_of_nonneg hpos
    simpa [this] using hlarge
  -- Step 7.4: contradiction with `|(M : ℝ) - c| < 1`.
  have : |(M : ℝ) - c| < 1 := by
    simpa [Metric.mem_ball, Real.dist_eq] using hdist
  linarith

lemma no_limit_for_pathological_sum :
    ¬ ∃ y,
        Tendsto
          (fun n =>
            (∑ _i ∈ range n,
              |(fun k : ℕ =>
                ∑ j ∈ range (k + 1), spike j * spike (k - j))|))
          atTop (𝓝 y) := by
  -- Step 8: show the main conclusion fails for the spike sequences.
  intro h
  obtain ⟨y, hy⟩ := h
  -- Step 8.1: evaluate the convergent sequence at `0` via the evaluation map.
  have h_eval :
      Tendsto
          (fun n =>
            (∑ i ∈ range n,
              |(fun k : ℕ =>
                ∑ j ∈ range (k + 1), spike j * spike (k - j))|) 0)
          atTop (𝓝 (y 0)) := by
    have hcont :
        Tendsto (fun f : ℕ → ℝ => f 0) (𝓝 y) (𝓝 (y 0)) :=
      (continuous_apply (0 : ℕ)).tendsto y
    exact hcont.comp hy
  -- Step 8.2: rewrite the evaluation using `conv_sum_eval`.
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop (𝓝 (y 0)) := by
    simpa [conv_sum_eval] using h_eval
  -- Step 8.3: contradiction with `not_tendsto_nat`.
  exact (not_tendsto_nat (y 0)) hnat

lemma exercise_3_13_counterexample :
    ∃ (a b : ℕ → ℝ),
      (∃ y, Tendsto (fun n => ∑ i ∈ range n, |a i|) atTop (𝓝 y)) ∧
        (∃ y, Tendsto (fun n => ∑ i ∈ range n, |b i|) atTop (𝓝 y)) ∧
          ¬ ∃ y,
              Tendsto
                (fun n =>
                  (∑ _i ∈ range n,
                    |(fun k : ℕ =>
                      ∑ j ∈ range (k + 1), a j * b (k - j))|))
                atTop (𝓝 y) := by
  -- Step 9: package the spike sequences with the three required properties.
  refine ⟨spike, spike, ?_, ?_, ?_⟩
  · -- Step 9.1: partial sums of `|spike|` converge to `1`.
    exact ⟨1, tendsto_sum_abs_spike⟩
  · -- Step 9.2: same for `b`.
    exact ⟨1, tendsto_sum_abs_spike⟩
  · -- Step 9.3: the conclusion fails.
    convert no_limit_for_pathological_sum using 3

theorem Rudin_exercise_3_13_neg :
    ¬ (∀ (a b : ℕ → ℝ),
        (∃ y, Tendsto (fun n => ∑ i ∈ range n, |a i|) atTop (𝓝 y)) →
          (∃ y, Tendsto (fun n => ∑ i ∈ range n, |b i|) atTop (𝓝 y)) →
            ∃ y,
              Tendsto
                (fun n =>
                  (∑ _i ∈ range n,
                    |(fun k : ℕ =>
                      ∑ j ∈ range (k + 1), a j * b (k - j))|))
                atTop (𝓝 y)) := by
  -- Step 10: use the counterexample to negate the original universally quantified claim.
  intro h
  rcases exercise_3_13_counterexample with ⟨a, b, ha, hb, hfail⟩
  have := h a b ha hb
  exact hfail this

end Counterexample

/-
Corrected statement:
Step 0: Clarify that the absolute value inside the final sum must be applied to the scalar term
`∑ j ∈ range (i + 1), a j * b (i - j)` instead of the whole constant function.
Step 0.1: With that change the conclusion states that the sequence of partial sums of absolute
values of the Cauchy product is convergent, i.e. that the Cauchy product is absolutely convergent.
Step 0.2: The following section proves this corrected statement directly from the hypotheses that
the series of `|a|` and `|b|` converge.
-/

section CorrectedStatement

open scoped BigOperators

lemma convolution_abs_le (a b : ℕ → ℝ) (n : ℕ) :
    |∑ j ∈ range (n + 1), a j * b (n - j)|
      ≤ ∑ j ∈ range (n + 1), |a j| * |b (n - j)| := by
  -- Step 1: use the triangle inequality on each partial Cauchy product.
  simpa [abs_mul] using
    Finset.abs_sum_le_sum_abs (fun j => a j * b (n - j)) (range (n + 1))

theorem Rudin_exercise_3_13_corrected
   (a b : ℕ → ℝ)
   (ha : ∃ y, Tendsto (fun n => ∑ i ∈ range n, |a i|) atTop (𝓝 y))
   (hb : ∃ y, Tendsto (fun n => ∑ i ∈ range n, |b i|) atTop (𝓝 y)) :
   ∃ y,
     Tendsto
       (fun n =>
         ∑ i ∈ range n,
           |∑ j ∈ range (i + 1), a j * b (i - j)|)
       atTop (𝓝 y) := by
  -- Step 2: reduce the problem to the absolute Cauchy product of nonnegative sequences.
  classical
  have hSummAbsA : Summable fun n => |a n| :=
    summable_of_absolute_convergence_real (by simpa using ha)
  have hSummAbsB : Summable fun n => |b n| :=
    summable_of_absolute_convergence_real (by simpa using hb)
  -- Step 2.1: the convolution of the absolute values is summable.
  have hSummConv :
      Summable fun n =>
        ∑ k ∈ range (n + 1), |a k| * |b (n - k)| := by
    have hSummNorm :=
      summable_norm_sum_mul_range_of_summable_norm
        (f := fun n => |a n|) (g := fun n => |b n|)
        (hf := by simpa [Real.norm_eq_abs] using hSummAbsA)
        (hg := by simpa [Real.norm_eq_abs] using hSummAbsB)
    simpa using
      (Summable.of_norm hSummNorm :
        Summable fun n => ∑ k ∈ range (n + 1), |a k| * |b (n - k)|)
  -- Step 2.2: dominate the absolute values of the actual Cauchy product.
  have hSummAbs :
      Summable fun n =>
        |∑ k ∈ range (n + 1), a k * b (n - k)| := by
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun n => convolution_abs_le a b n) ?_
    exact hSummConv
  -- Step 2.3: convert summability into the desired limit statement.
  refine ⟨∑' n, |∑ k ∈ range (n + 1), a k * b (n - k)|, ?_⟩
  have hlimit := hSummAbs.hasSum.tendsto_sum_nat
  simpa using hlimit

end CorrectedStatement
