import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Show that the rationals $\mathbb{Q}$ are not locally compact.
-/

/-Informal Proof

First, we prove that each set $\mathbb{Q} \cap[a, b]$, where $a, b$ are irrational numbers, is not compact. Indeed, since $\mathbb{Q} \cap[a, b]$ is countable, we can write $\mathbb{Q} \cap[a, b]=\left\{q_1, q_2, \ldots\right\}$. Then $\left\{U_i\right\}_{i \in \mathbb{Z}_{+}}$, where $U_i=\mathbb{Q} \cap\left[a, q_i\right)$ for each $i$, is an open covering of $\mathbb{Q} \cap[a, b]$ with no finite subcovering. Now let $x \in \mathbb{Q}$ and suppose that $\mathbb{Q}$ is locally compact at $x$. Then there exists a compact set $C$ containing a neighbourhood $U$ of $x$. Then $U$ contains a set $\mathbb{Q} \cap[a, b]$ where $a, b$ are irrational numbers. Since this set is closed and contained in the compact $C$, it follows $\mathbb{Q} \cap[a, b]$ is compact, a contradiction. Therefore, $\mathbb{Q}$ is not locally compact.
-/

theorem Munkres_exercise_29_1 : ¬ LocallyCompactSpace ℚ := by
  classical
  -- Step 1: Assume for contradiction that ℚ carries a locally compact structure.
  intro hLC
  -- Step 2: Specialize the definition at the rational point x = 0 with the unit open ball.
  let x : ℚ := 0
  let n : Set ℚ := Metric.ball x (1 : ℝ)
  -- Step 2.1: Record that the unit ball is a neighbourhood of x.
  have hn : n ∈ 𝓝 x := by
    -- Step 2.1.1: Use the standard metric fact that open balls with positive radius are neighbourhoods.
    simpa [x, n] using Metric.ball_mem_nhds x (show (0 : ℝ) < (1 : ℝ) by exact zero_lt_one)
  -- Step 3: Extract the purported compact neighbourhood guaranteed by local compactness.
  obtain ⟨s, hs_mem, hs_subset, hs_compact⟩ := hLC.local_compact_nhds x n hn
  -- Step 3.1: Because s is a neighbourhood, shrink to some ε-ball contained in s.
  obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.mem_nhds_iff.mp hs_mem
  -- Step 4: Choose an irrational number a lying strictly between -ε/2 and 0 so that it sits inside the ball.
  have hneg : - (ε / 2) < (0 : ℝ) := by
    -- Step 4.1: Translate the positivity of ε/2 into the desired inequality.
    exact neg_lt_zero.mpr (half_pos hε_pos)
  obtain ⟨a, ha_irr, ha_left, ha_right⟩ := exists_irrational_btwn hneg
  -- Step 4.2: Record that |a| is strictly smaller than ε/2.
  have ha_abs : |a| < ε / 2 := by
    -- Step 4.2.1: Use abs bounds coming from the interval (−ε/2, ε/2).
    refine abs_lt.mpr ?_
    refine ⟨ha_left, lt_of_lt_of_le ha_right (half_pos hε_pos).le⟩
  -- Step 5: Construct a decreasing sequence of rationals converging to a from above.
  obtain ⟨u, hu_strictAnti, hu_gt, hu_tendsto⟩ := Real.exists_seq_rat_strictAnti_tendsto a
  -- Step 5.1: Quantify how close the sequence eventually gets to a.
  obtain ⟨N₁, hN₁⟩ :=
    (Metric.tendsto_atTop.1 hu_tendsto) (ε / 2) (half_pos hε_pos)
  -- Step 5.2: From now on, drop finitely many terms so every term lies deep inside the ε-ball.
  let N := N₁
  let seq : ℕ → ℚ := fun n => u (n + N)
  -- Step 5.4: Every element of the tail sequence is within ε/2 of a and thus close to x.
  have h_seq_close :
      ∀ n, |((seq n : ℝ) - a)| < ε / 2 := by
    -- Step 5.4.1: Unpack the eventual estimate provided by hN₁.
    intro n
    have h_le : N₁ ≤ n + N := by
      simp [N, Nat.add_comm]
    have hdist := hN₁ (n + N) h_le
    -- Step 5.4.2: Translate the inequality into the absolute-value form.
    simpa [seq, Real.dist_eq, sub_eq_add_neg] using hdist
  -- Step 5.6: Deduce that the entire tail sequence lives inside the ε-ball around x and thus inside s.
  have h_seq_mem_s : ∀ n, seq n ∈ s := by
    intro n
    -- Step 5.6.1: Bound |seq n| by the triangle inequality via the intermediate point a.
    have hsmall : |(seq n : ℝ)| < ε := by
      have h_close : |(seq n : ℝ) - a| < ε / 2 := h_seq_close n
      have hsum : |(seq n : ℝ)| ≤ |(seq n : ℝ) - a| + |a| := by
        -- Step 5.6.1.1: Rewrite seq n as (seq n − a) + a and apply the triangle inequality.
        simpa [seq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          using abs_add_le ((u (n + N) : ℝ) - a) a
      -- Step 5.6.1.2: Combine the two < ε/2 bounds to finish.
      have hsum_lt : |(seq n : ℝ) - a| + |a| < ε := by
        have ht : |(seq n : ℝ) - a| + |a| < ε / 2 + ε / 2 :=
          add_lt_add h_close ha_abs
        simpa [add_halves] using ht
      exact lt_of_le_of_lt hsum hsum_lt
    -- Step 5.6.2: Convert the inequality on absolute values to a metric statement.
    have hball :
        seq n ∈ Metric.ball x ε := by
      simpa [Metric.mem_ball, Rat.dist_eq, seq, x, sub_eq_add_neg]
        using hsmall
    -- Step 5.6.3: Chain the inclusions ball ⊆ s ⊆ n.
    exact hε_ball hball
  -- Step 6: Observe that the shifted sequence still converges to a in ℝ.
  have h_seq_tendsto :
      Tendsto (fun n => (seq n : ℝ)) atTop (𝓝 a) :=
    hu_tendsto.comp (tendsto_add_atTop_nat N)
  -- Step 7: Use compactness to extract a convergent subsequence inside s.
  obtain ⟨q, hq_in, φ, hφ_mono, hφ_tendsto⟩ :=
    hs_compact.tendsto_subseq (x := seq) h_seq_mem_s
  -- Step 7.1: Push the subsequence through the inclusion ℚ → ℝ to get convergence in ℝ.
  have hφ_real :
      Tendsto (fun n => (seq (φ n) : ℝ)) atTop (𝓝 (q : ℝ)) :=
    (Rat.continuous_coe_real.tendsto (x := q)).comp hφ_tendsto
  -- Step 7.2: The same subsequence also converges to a because the original sequence does.
  have hφ_to_a :
      Tendsto (fun n => (seq (φ n) : ℝ)) atTop (𝓝 a) :=
    h_seq_tendsto.comp (StrictMono.tendsto_atTop hφ_mono)
  -- Step 7.3: Limits in ℝ are unique, hence the two limits must coincide.
  have hq_eq : (q : ℝ) = a :=
    tendsto_nhds_unique hφ_real hφ_to_a
  -- Step 8: Reach the contradiction: a cannot equal any rational number.
  exact ha_irr.ne_rat q hq_eq.symm
