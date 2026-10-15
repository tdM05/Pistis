import Mathlib

open Filter Set TopologicalSpace
open scoped Topology BoundedContinuousFunction

abbrev I : Set ℝ := Icc 0 1

/-Informal Statement

Show that $[0, 1]^\omega$ is not locally compact in the uniform topology.
-/

/-Informal Proof

Consider $\mathbf{0} \in[0,1]^\omega$ and suppose that $[0,1]^\omega$ is locally compact at $\mathbf{0}$. Then there exists a compact $C$ containing an open ball $B=B_\rho(\mathbf{0}, \varepsilon) \subset[0,1]^\omega$. Note that $\bar{B}=[0, \varepsilon]^\omega$. Then $[0, \varepsilon]^\omega$ is closed and contained in the compact $C$, so it is compact. But $[0, \varepsilon]^\omega$ is homeomorphic to $[0,1]^\omega$, which is not compact by Exercise 28.1. This contradiction proves that $[0,1]^\omega$ is not locally compact in the uniform topology.
-/

theorem Munkres_exercise_29_4 [TopologicalSpace (ℕ → I)] :
  ¬ LocallyCompactSpace (ℕ → I) := by
  sorry

/-
Step 1: The Lean statement above equips `(ℕ → I)` with the canonical product topology rather
than the uniform (sup) topology mentioned in the informal text.  Under this topology each factor
`I = [0,1]` is compact, and Tychonoff's theorem (available in Mathlib as an instance) shows that
the whole product is compact, hence locally compact.  Therefore the formal statement is false.
-/

/-- Step-by-step proof of the negation:
`(ℕ → I)` *is* a locally compact space with its product topology. -/
theorem Munkres_exercise_29_4_neg :
    LocallyCompactSpace (ℕ → I) := by
  classical
  -- Step 1: note that the closed interval `I` inherits compactness from `ℝ`.
  have hI : CompactSpace I := inferInstance
  -- Step 2: products of compact spaces are compact, so `(ℕ → I)` is compact.
  have h_compact : CompactSpace (ℕ → I) := by infer_instance
  -- Step 3: every compact space is automatically locally compact.
  exact inferInstance

/-
Corrected version (uniform topology): if we give `[0,1]^ω` the uniform topology coming from the
sup metric (Lean model: bounded continuous functions `ℕ →ᵇ I`, which coincide with all sequences
because ℕ is discrete and values are bounded), then the space fails to be locally compact.  The
following formalization works with the type `ℕ →ᵇ I`, whose uniform structure is induced by the
sup metric.
-/


/-! ### Preparing the spikes used in the counterexample -/

-- Step 0: work noncomputably since we use real numbers without worrying about effectivity.
noncomputable section

-- Step 1: define the amplitude of our spike functions in terms of a chosen radius `ε`.
def spikeValue (ε : ℝ) : ℝ :=
  min (ε / 2) (1 / 2)

lemma spikeValue_pos {ε : ℝ} (hε : 0 < ε) : 0 < spikeValue ε := by
  have h_half : 0 < ε / 2 := half_pos hε
  have h_const : 0 < (1 / 2 : ℝ) := by norm_num
  simpa [spikeValue] using lt_min h_half h_const

lemma spikeValue_nonneg {ε : ℝ} (hε : 0 < ε) : 0 ≤ spikeValue ε :=
  (spikeValue_pos (ε := ε) hε).le

lemma spikeValue_le_half (ε : ℝ) : spikeValue ε ≤ (1 / 2 : ℝ) := by
  simp [spikeValue]

lemma spikeValue_le_one (ε : ℝ) : spikeValue ε ≤ (1 : ℝ) := by
  have hle : spikeValue ε ≤ (1 / 2 : ℝ) := spikeValue_le_half ε
  have h_half_le : (1 / 2 : ℝ) ≤ 1 := by norm_num
  exact le_trans hle h_half_le

lemma spikeValue_lt {ε : ℝ} (hε : 0 < ε) : spikeValue ε < ε := by
  have hle : spikeValue ε ≤ ε / 2 := by
    simp [spikeValue]
  have h_small : ε / 2 < ε := half_lt_self hε
  exact lt_of_le_of_lt hle h_small

-- Step 2: turn this amplitude into a value of the interval type `I = [0,1]`.
def spikePoint (ε : ℝ) (hε : 0 < ε) : I :=
  ⟨spikeValue ε,
    ⟨spikeValue_nonneg (ε := ε) hε, spikeValue_le_one ε⟩⟩

@[simp]
lemma spikePoint_coe (ε : ℝ) (hε : 0 < ε) :
    ((spikePoint ε hε : I) : ℝ) = spikeValue ε := rfl

-- Step 3: define the spike functions as bounded continuous maps (uniform topology).
lemma dist_le_one_I (a b : I) : dist a b ≤ (1 : ℝ) := by
  -- Step A: control the absolute difference between two points of `[0,1]`.
  have ha : (a : ℝ) ∈ Icc (0 : ℝ) 1 := a.property
  have hb : (b : ℝ) ∈ Icc (0 : ℝ) 1 := b.property
  have ha₀ : 0 ≤ (a : ℝ) := ha.1
  have hb₀ : 0 ≤ (b : ℝ) := hb.1
  have ha₁ : (a : ℝ) ≤ 1 := ha.2
  have hb₁ : (b : ℝ) ≤ 1 := hb.2
  have h_upper : (a : ℝ) - (b : ℝ) ≤ (1 : ℝ) := by
    have : (a : ℝ) - (b : ℝ) ≤ (a : ℝ) := sub_le_self _ hb₀
    exact this.trans ha₁
  have h_lower : -(1 : ℝ) ≤ (a : ℝ) - (b : ℝ) := by
    have : (b : ℝ) - (a : ℝ) ≤ (b : ℝ) := sub_le_self _ ha₀
    have : (b : ℝ) - (a : ℝ) ≤ (1 : ℝ) := this.trans hb₁
    have := neg_le_neg_iff.mpr this
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have h_abs : |(a : ℝ) - (b : ℝ)| ≤ (1 : ℝ) :=
    (abs_le.mpr ⟨h_lower, h_upper⟩)
  simpa [Real.dist_eq] using h_abs

def spike (ε : ℝ) (hε : 0 < ε) (n : ℕ) : ℕ →ᵇ I :=
  BoundedContinuousFunction.mkOfDiscrete
    (fun k => if k = n then spikePoint ε hε else (0 : I))
    1
    (by
      intro x y
      -- Step 3.1: every value lies in `[0,1]`, so their distance is bounded by `1`.
      simpa [spikePoint, spikePoint_coe]
        using dist_le_one_I
          (a := if x = n then spikePoint ε hε else (0 : I))
          (b := if y = n then spikePoint ε hε else (0 : I)))

@[simp]
lemma spike_apply (ε : ℝ) (hε : 0 < ε) (n k : ℕ) :
    spike ε hε n k = if k = n then spikePoint ε hε else (0 : I) :=
  rfl

@[simp]
lemma dist_spikePoint_zero (ε : ℝ) (hε : 0 < ε) :
    dist (spikePoint ε hε) (0 : I) = spikeValue ε := by
  have h_nonneg : 0 ≤ spikeValue ε := spikeValue_nonneg (ε := ε) hε
  change dist (spikeValue ε : ℝ) 0 = spikeValue ε
  simp [abs_of_nonneg h_nonneg]

@[simp]
lemma dist_zero_spikePoint (ε : ℝ) (hε : 0 < ε) :
    dist (0 : I) (spikePoint ε hε) = spikeValue ε := by
  simp [dist_comm]

lemma spike_coord_dist_zero_le (ε : ℝ) (hε : 0 < ε) (n k : ℕ) :
    dist (spike ε hε n k) 0 ≤ spikeValue ε := by
  by_cases hk : k = n
  · subst hk
    have := (dist_spikePoint_zero (ε := ε) hε).le
    simp [spike_apply]
  · have h_nonneg : (0 : ℝ) ≤ spikeValue ε := spikeValue_nonneg (ε := ε) hε
    simp [spike_apply, hk, h_nonneg]

lemma spike_coord_dist_le (ε : ℝ) (hε : 0 < ε) (m n k : ℕ) :
    dist (spike ε hε m k) (spike ε hε n k) ≤ spikeValue ε := by
  have h_nonneg : (0 : ℝ) ≤ spikeValue ε := spikeValue_nonneg (ε := ε) hε
  by_cases hm : k = m
  · by_cases hn : k = n
    · subst hm; subst hn
      simp [spike_apply, h_nonneg]
    · subst hm
      simp [spike_apply, hn, dist_spikePoint_zero]
  · by_cases hn : k = n
    · subst hn
      simp [spike_apply, hm, dist_zero_spikePoint]
    · simp [spike_apply, hm, hn, h_nonneg]

-- Step 4: estimate the distances between spikes.
lemma dist_spike_to_zero (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    dist (spike ε hε n) (0 : ℕ →ᵇ I) = spikeValue ε := by
  -- Step 4.1: upper bound using the uniform bound on pointwise differences.
  have h_le :
      dist (spike ε hε n) (0 : ℕ →ᵇ I) ≤ spikeValue ε := by
    have h_nonneg : (0 : ℝ) ≤ spikeValue ε :=
      spikeValue_nonneg (ε := ε) hε
    refine (BoundedContinuousFunction.dist_le (f := spike ε hε n)
        (g := (0 : ℕ →ᵇ I)) h_nonneg).mpr ?_
    intro k
    simpa using spike_coord_dist_zero_le (ε := ε) hε n k
  -- Step 4.2: lower bound from evaluating the distance at the key coordinate.
  have h_ge :
      spikeValue ε ≤ dist (spike ε hε n) (0 : ℕ →ᵇ I) := by
    have h_point :
        dist ((spike ε hε n) n) ((0 : ℕ →ᵇ I) n) = spikeValue ε := by
      simp [spike_apply, dist_spikePoint_zero]
    have := BoundedContinuousFunction.dist_coe_le_dist
      (f := spike ε hε n) (g := (0 : ℕ →ᵇ I)) n
    exact le_trans (by simp) this
  exact le_antisymm h_le h_ge

lemma dist_spike_pair {ε : ℝ} (hε : 0 < ε) {m n : ℕ} (hne : m ≠ n) :
    dist (spike ε hε m) (spike ε hε n) = spikeValue ε := by
  -- Step 5.1: the uniform upper bound.
  have h_nonneg : (0 : ℝ) ≤ spikeValue ε :=
    spikeValue_nonneg (ε := ε) hε
  have h_le :
      dist (spike ε hε m) (spike ε hε n) ≤ spikeValue ε := by
    refine (BoundedContinuousFunction.dist_le (f := spike ε hε m)
        (g := spike ε hε n) h_nonneg).mpr ?_
    intro k
    simpa using spike_coord_dist_le (ε := ε) hε m n k
  -- Step 5.2: the lower bound from the `m`-th coordinate.
  have h_point :
      dist ((spike ε hε m) m) ((spike ε hε n) m) = spikeValue ε := by
    simp [spike_apply, hne, dist_spikePoint_zero]
  have h_ge :
      spikeValue ε ≤ dist (spike ε hε m) (spike ε hε n) := by
    have h_point_le :
        spikeValue ε ≤
          dist ((spike ε hε m) m) ((spike ε hε n) m) := by
      exact le_of_eq h_point.symm
    exact le_trans h_point_le
      (BoundedContinuousFunction.dist_coe_le_dist
        (f := spike ε hε m) (g := spike ε hε n) m)
  exact le_antisymm h_le h_ge

lemma spike_mem_ball {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    spike ε hε n ∈ Metric.ball (0 : ℕ →ᵇ I) ε := by
  -- Step 6: combine the previous distance computation with the amplitude bound.
  have h_dist := dist_spike_to_zero (ε := ε) hε n
  have h_small : spikeValue ε < ε := spikeValue_lt (ε := ε) hε
  simpa [Metric.mem_ball, h_dist] using h_small

/-! ### The corrected theorem: the uniform space is not locally compact -/

theorem Munkres_exercise_29_4_corrected :
    ¬ LocallyCompactSpace (ℕ →ᵇ I) := by
  classical
  -- Step 1: assume, for contradiction, that the space is locally compact.
  intro h_loc
  -- Step 2: apply local compactness at the zero function with the neighbourhood `univ`.
  have h_univ : (Set.univ : Set (ℕ →ᵇ I)) ∈ 𝓝 (0 : ℕ →ᵇ I) := by simp
  obtain ⟨s, hs_mem, hs_subset, hs_compact⟩ :=
    LocallyCompactSpace.local_compact_nhds
      (X := ℕ →ᵇ I) 0 (Set.univ : Set (ℕ →ᵇ I)) h_univ
  -- Step 3: use the metric structure to find a uniform ball inside `s`.
  obtain ⟨ε, ε_pos, h_ball_subset⟩ := Metric.mem_nhds_iff.mp hs_mem
  -- Step 4: consider the sequence of spikes of height `min (ε/2) (1/2)`.
  let seq : ℕ → ℕ →ᵇ I := fun n => spike ε ε_pos n
  have h_seq_mem : ∀ n, seq n ∈ s := by
    intro n
    exact h_ball_subset (spike_mem_ball (ε := ε) ε_pos n)
  -- Step 5: compactness of `s` supplies a convergent subsequence of the spikes.
  have h_seqcompact : IsSeqCompact s := hs_compact.isSeqCompact
  obtain ⟨y, hy_in, hφ⟩ := h_seqcompact (x := seq) h_seq_mem
  obtain ⟨φ, hφ_mono, hφ_tendsto⟩ := hφ
  -- Step 6: extract a small control parameter from convergence.
  set δ := spikeValue ε
  have hδ_pos : 0 < δ := spikeValue_pos (ε := ε) ε_pos
  have h_tendsto :=
    Metric.tendsto_atTop.1 hφ_tendsto (δ / 4)
      (by
        have hδ_quarter : 0 < δ / 4 := div_pos hδ_pos (by norm_num)
        simpa using hδ_quarter)
  obtain ⟨N, hN⟩ := h_tendsto
  have h_close_N : dist (seq (φ N)) y < δ / 4 := hN N le_rfl
  have h_close_succ :
      dist (seq (φ (N + 1))) y < δ / 4 :=
    hN (N + 1) (Nat.le_succ _)
  have h_sum_lt :
      dist (seq (φ N)) y + dist y (seq (φ (N + 1))) < δ / 2 := by
    have h_comm : dist y (seq (φ (N + 1))) = dist (seq (φ (N + 1))) y :=
      dist_comm _ _
    have h₂ : dist y (seq (φ (N + 1))) < δ / 4 := by
      simpa [h_comm] using h_close_succ
    have h_add :
        dist (seq (φ N)) y + dist y (seq (φ (N + 1))) <
          δ / 4 + δ / 4 := add_lt_add h_close_N h₂
    have h₃ :
        δ / 4 + δ / 4 = δ * ((1 / 4 : ℝ) + 1 / 4) := by
      simp [div_eq_mul_inv, mul_add]
    have h₄ :
        δ * ((1 / 4 : ℝ) + 1 / 4) = δ / 2 := by
      have : (1 / 4 : ℝ) + 1 / 4 = 1 / 2 := by norm_num
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        congrArg (fun t : ℝ => δ * t) this
    have h_eq : δ / 4 + δ / 4 = δ / 2 := by simpa [h₃] using h₄
    simpa [h_eq] using h_add
  have h_dist_small :
      dist (seq (φ N)) (seq (φ (N + 1))) < δ / 2 :=
    lt_of_le_of_lt
      (dist_triangle _ _ _)
      h_sum_lt
  -- Step 7: but spikes remain a fixed distance `δ` apart, contradiction.
  have h_pair :
      dist (seq (φ N)) (seq (φ (N + 1))) = δ := by
    have h_ne : φ N ≠ φ (N + 1) :=
      (hφ_mono (Nat.lt_succ_self N)).ne
    simpa [seq, δ] using dist_spike_pair
      (ε := ε) ε_pos h_ne
  have hδ_half_lt : δ / 2 < δ := half_lt_self hδ_pos
  have h_goal : dist (seq (φ N)) (seq (φ (N + 1))) < δ :=
    lt_of_lt_of_le h_dist_small (le_of_lt hδ_half_lt)
  have h_contra : δ < δ := by
    simp [h_pair] at h_goal
  exact (lt_irrefl _ h_contra).elim

end
