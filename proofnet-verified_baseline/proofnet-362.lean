import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology



/-Informal Statement

Prove that the power series $\sum z^n/n$ converges at every point of the unit circle except $z = 1$.
-/

/-Informal Proof

If $z=1$ then $\sum z^n / n=\sum 1 / n$ is divergent (harmonic series). If $|z|=1$ and $z \neq 1$, write $z=e^{2 \pi i t}$ with $t \in(0,1)$ and apply Dirichlet's test: if $\left\{a_n\right\}$ is a sequence of real numbers and $\left\{b_n\right\}$ a sequence of complex numbers satisfying
- $a_{n+1} \leq a_n$
- $\lim _{n \rightarrow \infty} a_n=0$
- $\left|\sum_{n=1}^N b_n\right| \leq M$ for every positive integer $N$ and some $M>0$,
then $\sum a_n b_n$ converges. Let $a_n=1 / n$, so $a_n$ satisfies $a_{n+1} \leq a_n$ and $\lim _{n \rightarrow \infty} a_n=0$. Let $b_n=e^{2 \pi i n t}$, then
$$
\left|\sum_{n=1}^N b_n\right|=\left|\sum_{n=1}^N e^{2 \pi i n t}\right|=\left|\frac{e^{2 \pi i t}-e^{2 \pi i(N+1) t}}{1-e^{2 \pi i t}}\right| \leq \frac{2}{\left|1-e^{2 \pi i t}\right|}=M \text { for all } N
$$
Thus $\sum a_n b_n=\sum z^n / n$ converges for every point in the unit circle except $z=1$.
-/

theorem Shakarchi_exercise_1_19c (z : ℂ) (hz : ‖z‖ = 1) (s : ℕ → ℂ)
    (h : s = (λ n => ∑ i ∈ (range n), z ^ (i + 1) / (i + 1))) :
    (∃ z₀, Tendsto s atTop (𝓝 z₀)) ↔ z ≠ 1 := by
  classical
  -- Step 1: Record the closed form for every partial sum so that we can reuse it repeatedly.
  have hs_eval : ∀ n, s n = ∑ i ∈ range n, z ^ (i + 1) / (i + 1) := by
    intro n
    simpa using congrArg (fun f => f n) h
  -- Step 1.1: Extract the recursion satisfied by the sequence of partial sums.
  have hs_succ : ∀ n, s (n + 1) = s n + z ^ (n + 1) / (n + 1) := by
    intro n
    have hsn1 := hs_eval (n + 1)
    have hsn := hs_eval n
    have hsum :
        ∑ i ∈ range (n + 1), z ^ (i + 1) / (i + 1) =
          (∑ i ∈ range n, z ^ (i + 1) / (i + 1)) + z ^ (n + 1) / (n + 1) := by
      simpa [Nat.succ_eq_add_one] using
        (sum_range_succ fun i => z ^ (i + 1) / (i + 1)) n
    simp [hsn1, hsn, hsum, add_comm]
  constructor
  · -- Step 2: Prove that convergence forces `z ≠ 1` by contradiction.
    intro hconv
    by_cases hz1 : z = 1
    · -- Step 2.1: Translate the sequence into real harmonic sums and obtain a contradiction.
      exfalso
      obtain ⟨ℓ, hℓ⟩ := hconv
      -- Step 2.1.1: Define the real harmonic partial sums that will control the norms.
      set H : ℕ → ℝ := fun n => ∑ i ∈ range n, (1 : ℝ) / (i + 1)
      have hH_succ : ∀ n, H (n + 1) = H n + 1 / (n + 1) := by
        intro n
        simp [H, Finset.sum_range_succ, add_comm]
      have hH_nonneg : ∀ n, 0 ≤ H n := by
        intro n
        refine sum_nonneg fun i hi => ?_
        have : 0 < (i + 1 : ℝ) := by exact_mod_cast Nat.succ_pos i
        exact one_div_nonneg.mpr this.le
      -- Step 2.1.2: Show that the complex sequence coincides with the coerced real sequence.
      have hs_real : ∀ n, s n = (H n : ℂ) := by
        intro n
        induction' n with n ih
        · simp [hs_eval, H]
        · have hsn := hs_succ n
          have hHn := hH_succ n
          simp [hsn, hHn, hz1, ih, add_comm]
      -- Step 2.1.3: Convert the previous equality into a norm identity.
      have hnorm_eq : ∀ n, ‖s n‖ = H n := by
        intro n
        have hpos : 0 ≤ H n := hH_nonneg n
        calc
          ‖s n‖ = ‖(H n : ℂ)‖ := by simp [hs_real n]
          _ = |H n| := by
            simp
          _ = H n := by simp [hpos]
      -- Step 2.1.4: Obtain eventually-small deviations from the candidate limit.
      have hone_pos : (0 : ℝ) < 1 := by norm_num
      have hclose' :=
        hℓ.eventually (Metric.ball_mem_nhds _ hone_pos)
      have hclose :
          ∀ᶠ n in atTop, ‖s n - ℓ‖ < 1 := hclose'.mono fun n hn => by
            simpa [Metric.ball, dist_eq_norm, sub_eq_add_neg] using hn
      obtain ⟨Nclose, hNclose⟩ := eventually_atTop.1 hclose
      -- Step 2.1.5: Use divergence of the harmonic series to force the norms to grow.
      have hdiv : Tendsto H atTop atTop :=
        Real.tendsto_sum_range_one_div_nat_succ_atTop
      have hlarge :
          ∀ᶠ n in atTop, ‖ℓ‖ + 2 ≤ H n :=
        (tendsto_atTop.1 hdiv) (‖ℓ‖ + 2)
      obtain ⟨Ndiv, hNdiv⟩ := eventually_atTop.1 hlarge
      -- Step 2.1.6: Choose an index beyond both thresholds.
      set n₀ := max Nclose Ndiv
      have hclose_n₀ : ‖s n₀ - ℓ‖ < 1 :=
        hNclose _ (le_max_left _ _)
      have hlarge_n₀ : ‖ℓ‖ + 2 ≤ H n₀ :=
        hNdiv _ (le_max_right _ _)
      -- Step 2.1.7: Turn the closeness estimate into an upper bound on the norms.
      have hnorm_le :
          ‖s n₀‖ ≤ ‖s n₀ - ℓ‖ + ‖ℓ‖ := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (norm_add_le (s n₀ - ℓ) ℓ)
      have hsum_lt : ‖s n₀ - ℓ‖ + ‖ℓ‖ < ‖ℓ‖ + 1 := by
        have := add_lt_add_right hclose_n₀ ‖ℓ‖
        simpa [add_comm, add_left_comm, add_assoc] using this
      have hnorm_lt : ‖s n₀‖ < ‖ℓ‖ + 1 :=
        lt_of_le_of_lt hnorm_le hsum_lt
      -- Step 2.1.8: Combine both bounds and extract the final contradiction.
      have hlarge_norm : (‖ℓ‖ + 2 : ℝ) ≤ ‖s n₀‖ := by
        simpa [hnorm_eq n₀] using hlarge_n₀
      have hcontr : (‖ℓ‖ + 2 : ℝ) < ‖ℓ‖ + 1 :=
        lt_of_le_of_lt hlarge_norm hnorm_lt
      have htwo_lt_one : (2 : ℝ) < 1 := by
        simpa using (lt_of_add_lt_add_left hcontr)
      exact (by norm_num : ¬((2 : ℝ) < 1)) htwo_lt_one
    · -- Step 2.2: If `z ≠ 1`, we immediately finish this implication.
      exact hz1
  · -- Step 3: Assuming `z ≠ 1`, construct the limit via Dirichlet's test.
    intro hz_ne_one
    -- Step 3.1: Set up the ingredients used by Dirichlet's convergence criterion.
    let f : ℕ → ℝ := fun n => (1 : ℝ) / (n + 1)
    let zseq : ℕ → ℂ := fun n => z ^ (n + 1)
    have hf_antitone : Antitone f := by
      intro m n hmn
      have hle : (n + 1 : ℝ) ≥ m + 1 := by norm_cast; omega
      have hpos : 0 < (m + 1 : ℝ) := by exact_mod_cast Nat.succ_pos m
      have := one_div_le_one_div_of_le hpos hle
      simpa [f, add_comm] using this
    have hf_tendsto : Tendsto f atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    -- Step 3.2: Bound geometric partial sums uniformly.
    have hz_pow_bound :
        ∀ n, ‖∑ i ∈ range n, zseq i‖ ≤ 2 / ‖1 - z‖ := by
      intro n
      have hgeom :
          ∑ i ∈ range n, zseq i = z * (1 - z ^ n) / (1 - z) := by
        have hfac :
            ∑ i ∈ range n, zseq i =
              (∑ i ∈ range n, z ^ i) * z := by
          classical
          simpa [zseq, pow_succ, sum_mul, mul_comm, mul_left_comm, mul_assoc] using
            (sum_mul (s := range n) (f := fun i => z ^ i) z).symm
        have hfac' :
            ∑ i ∈ range n, zseq i =
              z * ∑ i ∈ range n, z ^ i := by
          simpa [mul_comm] using hfac
        have hz' : (1 - z) ≠ 0 := sub_ne_zero.mpr (ne_comm.mp hz_ne_one)
        have hgeom' :
            ∑ i ∈ range n, z ^ i = (1 - z ^ n) / (1 - z) := by
          have hbase := geom_sum_mul_neg (x := z) (n := n)
          have := congrArg (fun t : ℂ => t * (1 - z)⁻¹) hbase
          simp [hz'] at this
          simpa [div_eq_mul_inv, hz'] using this
        calc
          ∑ i ∈ range n, zseq i
              = z * ∑ i ∈ range n, z ^ i := hfac'
          _ = z * ((1 - z ^ n) / (1 - z)) := by simp [hgeom']
          _ = z * (1 - z ^ n) / (1 - z) := by
            simp [div_eq_mul_inv, mul_assoc]
      have hzpow_norm : ‖z ^ n‖ = (1 : ℝ) := by
        simp [hz]
      have hnum_le : ‖1 - z ^ n‖ ≤ 2 := by
        have htemp : ‖1 - z ^ n‖ ≤ 1 + 1 := by
          simpa [hzpow_norm] using (norm_sub_le (1 : ℂ) (z ^ n))
        have htwo : (1 : ℝ) + 1 = 2 := by norm_num
        simpa [htwo] using htemp
      have hden_pos : 0 < ‖1 - z‖ :=
        (norm_pos_iff.mpr (sub_ne_zero.mpr (by simpa [eq_comm] using hz_ne_one)))
      have hbound :
          ‖z * (1 - z ^ n)‖ / ‖1 - z‖ ≤ 2 / ‖1 - z‖ := by
        have hinv_nonneg : 0 ≤ ‖1 - z‖⁻¹ :=
          inv_nonneg.mpr hden_pos.le
        have hmul :
            ‖z‖ * ‖1 - z ^ n‖ ≤ ‖z‖ * 2 :=
          mul_le_mul_of_nonneg_left hnum_le (norm_nonneg z)
        have :=
          mul_le_mul_of_nonneg_right hmul hinv_nonneg
        simpa [div_eq_mul_inv, norm_mul, hz] using this
      have hbound' :
          ‖z * (1 - z ^ n) / (1 - z)‖ ≤ 2 / ‖1 - z‖ := by
        calc
          ‖z * (1 - z ^ n) / (1 - z)‖ = ‖z * (1 - z ^ n)‖ / ‖1 - z‖ := by
            simp
          _ ≤ 2 / ‖1 - z‖ := hbound
      simpa [hgeom] using hbound'
    -- Step 3.3: Apply Dirichlet's test to conclude that the sequence is Cauchy.
    have hs_series_fun :
        (fun n => ∑ i ∈ range n, (↑(f i) : ℂ) * zseq i) = s := by
      funext n
      have hs := hs_eval n
      have hterm :
          ∀ i, (↑(f i) : ℂ) * zseq i = z ^ (i + 1) / (i + 1) := by
        intro i
        simp [f, zseq, div_eq_mul_inv, mul_comm]
      have hsum :
          ∑ i ∈ range n, (↑(f i) : ℂ) * zseq i =
              ∑ i ∈ range n, z ^ (i + 1) / (i + 1) := by
        refine sum_congr rfl ?_
        intro i hi; simpa using hterm i
      simp [hs, hsum]
    have hCauchy_s : CauchySeq s := by
      simpa [hs_series_fun] using
        hf_antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf_tendsto hz_pow_bound
    -- Step 3.4: Use completeness of `ℂ` to extract the limit.
    exact cauchySeq_tendsto_of_complete hCauchy_s
