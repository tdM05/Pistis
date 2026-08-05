import Mathlib

open Filter Real Function Set
open scoped Topology



/-Informal Statement

A continuous, strictly increasing function $\mu \colon (0, \infty) \rightarrow (0, \infty)$ is a modulus of continuity if $\mu(s) \rightarrow 0$ as $s \rightarrow 0$. A function $f \colon [a, b] \rightarrow \mathbb{R}$ has modulus of continuity $\mu$ if $|f(s) - f(t)| \leq \mu(|s - t|)$ for all $s, t \in [a, b]$. Prove that a function is uniformly continuous if and only if it has a modulus of continuity.
-/

/-Informal Proof

Suppose there exists a modulus of continuity $w$ for $f$, then fix $\varepsilon>0$, since $\lim _{s \rightarrow 0} w(s)=0$, there exists $\delta>0$ such that for any $|s|<\delta$, we have $w(s)<\varepsilon$, then we have for any $x, z \in X$ such that $d_X(x, z)<\delta$, we have $d_Y(f(x), f(z)) \leq w\left(d_X(x, z)\right)<\varepsilon$, which means $f$ is uniformly continuous.

Suppose $f:\left(X, d_X\right) \rightarrow\left(Y, d_Y\right)$ is uniformly continuous.
Let $\delta_1>0$ be such that $d_X(a, b)<\delta_1$ implies $d_Y(f(a), f(b))<1$.
Define $w:[0, \infty) \rightarrow[0, \infty]$ by
$$
w(s)= \begin{cases}\left.\sup \left\{d_Y(f(a), f(b))\right\} \mid d_X(a, b) \leq s\right\} & \text { if } s \leq \delta_1 \\ \infty & \text { if } s>\delta_1\end{cases}
$$
We'll show that $w$ is a modulus of continuity for $f \ldots$
By definition of $w$, it's immediate that $w(0)=0$ and it's clear that
$$
d_Y(f(a), f(b)) \leq w\left(d_X(a, b)\right)
$$
for all $a, b \in X$.
It remains to show $\lim _{s \rightarrow 0^{+}} w(s)=0$.
It's easily seen that $w$ is nonnegative and non-decreasing, hence $\lim _{s \rightarrow 0^{+}}=L$ for some $L \geq 0$, where $L=\inf w((0, \infty))$
Let $\epsilon>0$.
By uniform continuity of $f$, there exists $\delta>0$ such that $d_X(a, b)<\delta$ implies $d_Y(f(a), f(b))<\epsilon$, hence by definition of $w$, we get $w(\delta) \leq \epsilon$.
Thus $L \leq \epsilon$ for all $\epsilon>0$, hence $L=0$.
This completes the proof.
-/

theorem Pugh_exercise_4_15a (a b : ℝ) (hab : a ≤ b) (f : Icc a b → ℝ) :
  UniformContinuous f ↔ ∃ (μ : ℝ → ℝ), ∀ (x : ℝ), (x > 0 → μ x > 0) ∧
  StrictMonoOn μ (Ioi 0) ∧ Tendsto μ (𝓝 0) (𝓝 0) ∧
  (∀ s t : Icc a b, |f s - f t| ≤ μ (|s - t|)) := by
  classical
  constructor
  · intro hUC
    -- Step 1: Upgrade uniform continuity to continuity so we can use compactness of the interval.
    have hcont : Continuous f := hUC.continuous
    -- Step 2: Bound the image of `f` on the compact domain using the extreme value theorem.
    have hcont_abs : Continuous fun x : Icc a b => |f x| := hcont.abs
    have hcompact : IsCompact (Set.univ : Set (Icc a b)) := isCompact_univ
    have hnonempty : (Set.univ : Set (Icc a b)).Nonempty := by
      refine ⟨⟨a, ⟨le_rfl, hab⟩⟩, ?_⟩
      simp
    obtain ⟨x₀, -, hx₀_bound⟩ :=
      hcompact.exists_isMaxOn hnonempty hcont_abs.continuousOn
    set C : ℝ := |f x₀|
    -- Step 2.1: Record the explicit numeric bound `C` for all values of `f`.
    have hbound : ∀ x : Icc a b, |f x| ≤ C := by
      intro x
      have := hx₀_bound (by simp : (x : Icc a b) ∈ (Set.univ : Set (Icc a b)))
      simpa [C] using this
    -- Step 3: Define the oscillation sets capturing maximal variation within radius `r`.
    let oscSet : ℝ → Set ℝ :=
      fun r => {δ : ℝ | ∃ s t : Icc a b, |(s : ℝ) - (t : ℝ)| ≤ r ∧ δ = |f s - f t|}
    -- Step 3.1: Ensure the zero value always belongs to each oscillation set for nonnegative radii.
    have hzero_mem : ∀ {r : ℝ}, 0 ≤ r → (0 : ℝ) ∈ oscSet r := by
      intro r hr
      have ha_mem : a ∈ Icc a b := ⟨le_rfl, hab⟩
      refine ⟨⟨a, ha_mem⟩, ⟨a, ha_mem⟩, ?_, by simp⟩
      have : |((⟨a, ha_mem⟩ : Icc a b) : ℝ) - ((⟨a, ha_mem⟩ : Icc a b) : ℝ)| = 0 := by simp
      simpa [this]
    -- Step 3.2: Record non-emptiness and boundedness of the oscillation sets.
    have hosc_nonempty : ∀ r : ℝ, 0 ≤ r → (oscSet r).Nonempty := by
      intro r hr
      exact ⟨0, hzero_mem hr⟩
    have hosc_bdd : ∀ {r : ℝ}, 0 ≤ r → BddAbove (oscSet r) := by
      intro r hr
      refine ⟨2 * C, ?_⟩
      intro y hy
      rcases hy with ⟨s, t, -, rfl⟩
      have hs : |f s| ≤ C := hbound s
      have ht : |f t| ≤ C := hbound t
      have htriangle : |f s - f t| ≤ |f s| + |f t| := by
        simpa using abs_sub_le (f s) 0 (f t)
      have hsum : |f s| + |f t| ≤ C + C := add_le_add hs ht
      have : |f s - f t| ≤ 2 * C := by
        have := htriangle.trans hsum
        simpa [two_mul] using this
      exact this
    -- Step 4: Introduce the raw oscillation function as the supremum of each oscillation set.
    let rawOsc : ℝ → ℝ := fun r => sSup (oscSet r)
    -- Step 4.1: Note that raw oscillation is nonnegative on nonnegative radii and vanishes at zero.
    have hraw_nonneg : ∀ {r : ℝ}, 0 ≤ r → 0 ≤ rawOsc r := by
      intro r hr
      exact le_csSup (hosc_bdd hr) (hzero_mem hr)
    have hraw_zero : rawOsc 0 = 0 := by
      refine le_antisymm ?_ (hraw_nonneg (show 0 ≤ (0 : ℝ) from le_rfl))
      refine csSup_le (hosc_nonempty 0 (show 0 ≤ (0 : ℝ) from le_rfl)) ?_
      intro y hy
      rcases hy with ⟨s, t, hst, rfl⟩
      have hzeroabs : |(s : ℝ) - (t : ℝ)| = 0 :=
        le_antisymm hst (abs_nonneg _)
      have hst' : (s : ℝ) = (t : ℝ) := by
        simpa using sub_eq_zero.mp (abs_eq_zero.mp hzeroabs)
      have hst_eq : s = t := Subtype.ext (by simpa using hst')
      simp [hst_eq]
    -- Step 4.2: Establish monotonicity of the raw oscillation as the radius grows.
    have hraw_mono : ∀ {r₁ r₂ : ℝ}, 0 ≤ r₁ → r₁ ≤ r₂ → rawOsc r₁ ≤ rawOsc r₂ := by
      intro r₁ r₂ hr₁ hle
      have hr₂ : 0 ≤ r₂ := hr₁.trans hle
      have hsubset : oscSet r₁ ⊆ oscSet r₂ := by
        intro y hy
        rcases hy with ⟨s, t, hst, rfl⟩
        exact ⟨s, t, hst.trans hle, rfl⟩
      refine csSup_le (hosc_nonempty r₁ hr₁) ?_
      intro y hy
      have hy' : y ∈ oscSet r₂ := hsubset hy
      exact le_csSup (hosc_bdd hr₂) hy'
    -- Step 4.3: Any concrete oscillation is controlled by `rawOsc`.
    have hraw_upper : ∀ {r : ℝ} {s t : Icc a b},
        0 ≤ r → |(s : ℝ) - (t : ℝ)| ≤ r → |f s - f t| ≤ rawOsc r := by
      intro r s t hr hst
      exact le_csSup (hosc_bdd hr) ⟨s, t, hst, rfl⟩
    -- Step 5: Control the decay of raw oscillation via uniform continuity.
    have hmetric := (Metric.uniformContinuous_iff).1 hUC
    -- Step 6: Define the desired modulus by adding a strictly increasing linear term.
    let μ : ℝ → ℝ := fun x => rawOsc (max x 0) + max x 0
    -- Step 6.1: Collect the positivity information into a reusable lemma.
    have hpos_all : ∀ x : ℝ, x > 0 → μ x > 0 := by
      intro x hx
      have hx_nonneg : 0 ≤ x := le_of_lt hx
      have := hraw_nonneg hx_nonneg
      have hμsimp : μ x = rawOsc x + x := by
        simp [μ, max_eq_left hx_nonneg]
      have hpos := add_pos_of_nonneg_of_pos this hx
      simpa [hμsimp]
    -- Step 6.2: Package strict monotonicity.
    have hmono_all : StrictMonoOn μ (Ioi 0) := by
      intro x hx y hy hxy
      have hx_nonneg : 0 ≤ x := le_of_lt hx
      have hy_nonneg : 0 ≤ y := le_of_lt hy
      have hx_le_y : x ≤ y := hxy.le
      have hosc_le := hraw_mono hx_nonneg hx_le_y
      have hμx : μ x = rawOsc x + x := by simp [μ, max_eq_left hx_nonneg]
      have hμy : μ y = rawOsc y + y := by simp [μ, max_eq_left hy_nonneg]
      have hstep1 : rawOsc x + x ≤ rawOsc y + x := by linarith
      have hstep2 : rawOsc y + x < rawOsc y + y := by linarith
      have hlt := lt_of_le_of_lt hstep1 hstep2
      simpa [hμx, hμy]
    -- Step 6.3: Capture the limit behavior of `μ`.
    have htendsto : Tendsto μ (𝓝 0) (𝓝 0) := by
      refine Metric.tendsto_nhds.2 ?_
      intro ε hε
      obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hmetric (ε / 2) (half_pos hε)
      have hosc_small' : ∀ {r : ℝ}, 0 ≤ r → r < δ₁ → rawOsc r ≤ ε / 2 := by
        intro r hr hlt
        refine csSup_le (hosc_nonempty r hr) ?_
        intro y hy
        rcases hy with ⟨s, t, hst, rfl⟩
        have hdist : dist s t < δ₁ := by
          have hlt' : |(s : ℝ) - (t : ℝ)| < δ₁ := lt_of_le_of_lt hst hlt
          simpa [Real.dist_eq] using hlt'
        have hlt' := hδ₁ hdist
        exact (le_of_lt (by simpa [Real.dist_eq] using hlt'))
      let δ := min δ₁ (ε / 2)
      have hδpos : 0 < δ := lt_min hδ₁pos (half_pos hε)
      have hprop : ∀ x : ℝ, dist x 0 < δ → dist (μ x) 0 < ε := by
        intro x hx
        have habs : |x| < δ := by simpa [Real.dist_eq] using hx
        by_cases hx_nonpos : x ≤ 0
        · have hmax : max x 0 = 0 := max_eq_right hx_nonpos
          have hxμ : μ x = 0 := by simp [μ, hmax, hraw_zero]
          have hdist : dist (μ x) 0 = 0 := by simp [hxμ]
          simpa [hdist] using hε
        · have hx_pos : 0 < x := lt_of_not_ge hx_nonpos
          have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
          have hx_abs : |x| = x := abs_of_nonneg hx_nonneg
          have hxδ : x < δ := by simpa [hx_abs] using habs
          have hltδ : x < δ₁ :=
            lt_of_lt_of_le hxδ (by simp [δ])
          have hltε : x < ε / 2 :=
            lt_of_lt_of_le hxδ (by simp [δ])
          have hosc := hosc_small' hx_nonneg hltδ
          have hμsimp : μ x = rawOsc x + x := by simp [μ, max_eq_left hx_nonneg]
          have hμ_le : μ x ≤ ε / 2 + x := by
            have := add_le_add_right hosc x
            simpa [hμsimp]
          have htarget : ε / 2 + x < ε := by
            have := add_lt_add_left hltε (ε / 2)
            simpa [add_comm, add_left_comm, two_mul] using this
          have hμ_lt : μ x < ε := lt_of_le_of_lt hμ_le htarget
          have hμ_nonneg : 0 ≤ μ x := by
            have := hraw_nonneg hx_nonneg
            simpa [μ, max_eq_left hx_nonneg] using add_nonneg this hx_nonneg
          have hμ_abs : |rawOsc x + x| = rawOsc x + x := by
            have := hμ_nonneg
            simpa [hμsimp] using this
          simpa [Real.dist_eq, hμsimp, hμ_abs] using hμ_lt
      have hball : Metric.ball (0 : ℝ) δ ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hδpos
      refine Filter.mem_of_superset hball ?_
      intro x hx
      have hx' : dist x 0 < δ := by simpa [Metric.mem_ball] using hx
      exact hprop x hx'
    -- Step 6.4: Record the oscillation bound.
    have hcontrol_all : ∀ s t : Icc a b, |f s - f t| ≤ μ (|(s : ℝ) - (t : ℝ)|) := by
      intro s t
      have hge : 0 ≤ |(s : ℝ) - (t : ℝ)| := abs_nonneg _
      have hbase := hraw_upper hge (le_of_eq rfl)
      have hμsimp :
          μ (|(s : ℝ) - (t : ℝ)|) =
            rawOsc (|(s : ℝ) - (t : ℝ)|) + |(s : ℝ) - (t : ℝ)| := by
        simp [μ]
      have hle : |f s - f t| ≤ rawOsc (|(s : ℝ) - (t : ℝ)|) := hbase
      have hfin : rawOsc (|(s : ℝ) - (t : ℝ)|) ≤
          rawOsc (|(s : ℝ) - (t : ℝ)|) + |(s : ℝ) - (t : ℝ)| :=
        le_add_of_nonneg_right hge
      have : |f s - f t| ≤
          rawOsc (|(s : ℝ) - (t : ℝ)|) + |(s : ℝ) - (t : ℝ)| :=
        hle.trans hfin
      simpa [hμsimp] using this
    -- Step 6.5: Assemble the conjunction demanded by the goal.
    refine ⟨μ, fun x => ?_⟩
    refine ⟨hpos_all x, ?_⟩
    exact ⟨hmono_all, ⟨htendsto, hcontrol_all⟩⟩
  · intro hmod
    -- Step 1: Unpack the provided modulus data.
    rcases hmod with ⟨μ, hμ⟩
    have hlim : Tendsto μ (𝓝 0) (𝓝 0) := (hμ 0).2.2.1
    have hcontrol : ∀ s t : Icc a b, |f s - f t| ≤ μ (|(s : ℝ) - (t : ℝ)|) :=
      (hμ 0).2.2.2
    -- Step 2: Use the `ε-δ` criterion with the supplied modulus to prove uniform continuity.
    refine (Metric.uniformContinuous_iff).2 ?_
    intro ε hε
    have hset := (Metric.tendsto_nhds.1 hlim) ε hε
    obtain ⟨δ, hδpos, hsubset⟩ := Metric.mem_nhds_iff.1 hset
    refine ⟨δ, hδpos, ?_⟩
    intro s t hdist
    have hlt : |(s : ℝ) - (t : ℝ)| < δ := by
      simpa [Real.dist_eq] using hdist
    have hμlt : |μ (|(s : ℝ) - (t : ℝ)|)| < ε := by
      have hball : dist (|(s : ℝ) - (t : ℝ)|) 0 < δ := by
        simpa [Real.dist_eq, abs_of_nonneg (abs_nonneg _)] using hlt
      have hmem : (|(s : ℝ) - (t : ℝ)|) ∈ Metric.ball (0 : ℝ) δ := by
        simpa [Metric.mem_ball] using hball
      have := hsubset hmem
      simpa [Real.dist_eq] using this
    have hbound := hcontrol s t
    have hμ_nonneg : 0 ≤ μ (|(s : ℝ) - (t : ℝ)|) :=
      (abs_nonneg _).trans hbound
    have hμ_val : μ (|(s : ℝ) - (t : ℝ)|) < ε :=
      by simpa [abs_of_nonneg hμ_nonneg] using hμlt
    have hfinal : |f s - f t| < ε := lt_of_le_of_lt hbound hμ_val
    simpa [Real.dist_eq] using hfinal


/-
## Why the Original Formalization is Not Faithful

The informal statement defines a "modulus of continuity" as a **continuous**, strictly
increasing function μ : (0,∞) → (0,∞) with μ(s) → 0 as s → 0. The Lean formalization
encodes strict monotonicity, positivity, and Tendsto at 0, but **omits the continuity
requirement** on μ over (0,∞). Since strict monotonicity does not imply continuity
(consider a strictly increasing function with jump discontinuities), the existential
quantifier ranges over a larger class of functions than intended.

This makes:
- The forward direction (UC → ∃μ) **weaker** than the informal claim (easier to satisfy
  the existential without the continuity constraint).
- The backward direction (∃μ → UC) **stronger** than the informal claim (the hypothesis
  on μ is weaker, so concluding UC is a stronger result).

Since one direction is weaker and the other stronger, the Lean iff is logically
incomparable to the informal statement.

## Correction

Add `ContinuousOn μ (Ioi 0)` to the properties required of μ. This faithfully captures
the informal definition that μ is continuous on (0,∞).
-/

theorem Pugh_exercise_4_15a_corrected (a b : ℝ) (hab : a ≤ b) (f : Icc a b → ℝ) :
  UniformContinuous f ↔ ∃ (μ : ℝ → ℝ), (∀ x : ℝ, x > 0 → μ x > 0) ∧
  ContinuousOn μ (Ioi 0) ∧ StrictMonoOn μ (Ioi 0) ∧ Tendsto μ (𝓝[>] 0) (𝓝 0) ∧
  (∀ s t : Icc a b, |f s - f t| ≤ μ (|s - t|)) := by
  classical
  constructor
  · -- Step 1: Prove the forward implication.
    -- Assume `f` is uniformly continuous on the compact interval subtype, and construct a
    -- continuous strictly increasing modulus of continuity.
    intro hUC
    -- Step 1.1: Upgrade uniform continuity to ordinary continuity.
    have hcont : Continuous f := hUC.continuous
    -- Step 1.2: The absolute value of `f` is continuous on the compact subtype.
    have hcont_abs : Continuous fun x : Icc a b => |f x| := hcont.abs
    -- Step 1.3: The whole subtype interval is compact.
    have hcompact : IsCompact (Set.univ : Set (Icc a b)) := isCompact_univ
    -- Step 1.4: The interval subtype is nonempty, using the given hypothesis `a ≤ b`.
    have hnonempty : (Set.univ : Set (Icc a b)).Nonempty := by
      refine ⟨⟨a, ⟨le_rfl, hab⟩⟩, ?_⟩
      simp
    -- Step 1.5: Choose a point where `|f|` attains its maximum.
    obtain ⟨x₀, -, hx₀_bound⟩ :=
      hcompact.exists_isMaxOn hnonempty hcont_abs.continuousOn
    -- Step 1.6: Let `C` be that maximum value.
    set C : ℝ := |f x₀|
    -- Step 1.7: Record the resulting pointwise bound `|f x| ≤ C`.
    have hbound : ∀ x : Icc a b, |f x| ≤ C := by
      intro x
      have := hx₀_bound (by simp : (x : Icc a b) ∈ (Set.univ : Set (Icc a b)))
      simpa [C] using this
    -- Step 1.8: Define a strictly positive global oscillation bound `K`.
    let K : ℝ := 2 * C + 1
    -- Step 1.9: `C` is nonnegative because it is an absolute value.
    have hC_nonneg : 0 ≤ C := by
      simp [C]
    -- Step 1.10: `K` is positive; this will make the affine majorants well behaved.
    have hK_pos : 0 < K := by
      dsimp [K]
      nlinarith
    -- Step 1.11: Also record the weaker nonnegativity of `K`.
    have hK_nonneg : 0 ≤ K := le_of_lt hK_pos
    -- Step 1.12: Every oscillation of `f` is bounded by `K`.
    have hdiff_bound : ∀ s t : Icc a b, |f s - f t| ≤ K := by
      intro s t
      -- Step 1.12.1: Bound `|f s - f t|` by `|f s| + |f t|`.
      have htriangle : |f s - f t| ≤ |f s| + |f t| := by
        simpa using abs_sub_le (f s) 0 (f t)
      -- Step 1.12.2: Bound both terms by the compact maximum `C`.
      have hs : |f s| ≤ C := hbound s
      have ht : |f t| ≤ C := hbound t
      -- Step 1.12.3: Combine the estimates and absorb them into `K = 2*C + 1`.
      have hsum : |f s| + |f t| ≤ 2 * C := by
        have := add_le_add hs ht
        nlinarith
      exact htriangle.trans (hsum.trans (by dsimp [K]; linarith))
    -- Step 2: Extract an `ε`-`δ` modulus from uniform continuity at every positive rational
    -- accuracy.  Positive rationals give a countable cofinal family of target errors.
    let ℚpos := {q : ℚ // 0 < q}
    -- Step 2.1: Use the metric form of uniform continuity.
    have hmetric := (Metric.uniformContinuous_iff).1 hUC
    -- Step 2.2: For every positive rational `q`, choose a positive radius `δ q` ensuring
    -- oscillation less than `q`.
    have hdelta_exists : ∀ q : ℚpos,
        ∃ δ > 0, ∀ s t : Icc a b, dist s t < δ → dist (f s) (f t) < (q : ℝ) := by
      intro q
      have hq_real : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.2
      obtain ⟨δ, hδpos, hδ⟩ := hmetric (q : ℝ) hq_real
      exact ⟨δ, hδpos, fun s t hst => hδ hst⟩
    -- Step 2.3: Name the chosen radius.
    let δ : ℚpos → ℝ := fun q => Classical.choose (hdelta_exists q)
    -- Step 2.4: Record positivity of the chosen radius.
    have hδ_pos : ∀ q : ℚpos, 0 < δ q := by
      intro q
      exact (Classical.choose_spec (hdelta_exists q)).1
    -- Step 2.5: Record the uniform-continuity estimate attached to the chosen radius.
    have hδ_spec : ∀ q : ℚpos, ∀ s t : Icc a b,
        dist s t < δ q → dist (f s) (f t) < (q : ℝ) := by
      intro q
      exact (Classical.choose_spec (hdelta_exists q)).2
    -- Step 3: Define affine upper bounds and take their pointwise infimum.
    -- The term for `q` is `q + K*x/δq`; it dominates every oscillation at distance `x`.
    let φ : ℚpos → ℝ → ℝ := fun q x => (q : ℝ) + K * x / δ q
    let ν : ℝ → ℝ := fun x => ⨅ q : ℚpos, φ q x
    -- Step 3.1: The affine terms are nonnegative on the nonnegative half-line.
    have hφ_nonneg : ∀ {x : ℝ}, 0 ≤ x → ∀ q : ℚpos, 0 ≤ φ q x := by
      intro x hx q
      have hq_real : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.2
      have hterm_nonneg : 0 ≤ K * x / δ q := by
        exact div_nonneg (mul_nonneg hK_nonneg hx) (le_of_lt (hδ_pos q))
      dsimp [φ]
      linarith
    -- Step 3.2: Hence the family of affine terms is bounded below whenever `x ≥ 0`.
    have hφ_bddBelow : ∀ {x : ℝ}, 0 ≤ x → BddBelow (Set.range fun q : ℚpos => φ q x) := by
      intro x hx
      refine ⟨0, ?_⟩
      intro y hy
      rcases hy with ⟨q, rfl⟩
      exact hφ_nonneg hx q
    -- Step 3.3: The infimum `ν x` is nonnegative for `x ≥ 0`.
    have hν_nonneg : ∀ {x : ℝ}, 0 ≤ x → 0 ≤ ν x := by
      intro x hx
      dsimp [ν]
      exact le_ciInf (hφ_nonneg hx)
    -- Step 3.4: The infimum lies below every affine term for `x ≥ 0`.
    have hν_le_φ : ∀ {x : ℝ}, 0 ≤ x → ∀ q : ℚpos, ν x ≤ φ q x := by
      intro x hx q
      dsimp [ν]
      exact ciInf_le (hφ_bddBelow hx) q
    -- Step 3.5: The infimum `ν` is monotone on the nonnegative half-line.
    have hν_mono_nonneg : ∀ {x y : ℝ}, 0 ≤ x → x ≤ y → ν x ≤ ν y := by
      intro x y hx hxy
      -- Step 3.5.1: It suffices to show `ν x` is a lower bound for every affine term at `y`.
      dsimp [ν]
      apply le_ciInf
      intro q
      -- Step 3.5.2: `ν x ≤ φ q x` by the infimum property.
      have hx_le : (⨅ q : ℚpos, φ q x) ≤ φ q x :=
        ciInf_le (hφ_bddBelow hx) q
      -- Step 3.5.3: Each affine term is monotone because `K/δq ≥ 0`.
      have hφxy : φ q x ≤ φ q y := by
        have hmul : K * x ≤ K * y := mul_le_mul_of_nonneg_left hxy hK_nonneg
        have hdiv : K * x / δ q ≤ K * y / δ q :=
          div_le_div_of_nonneg_right hmul (le_of_lt (hδ_pos q))
        dsimp [φ]
        linarith
      exact hx_le.trans hφxy
    -- Step 4: Prove `ν` is concave on `(0,∞)`, since it is an infimum of affine functions.
    have hν_concave : ConcaveOn ℝ (Ioi 0) ν := by
      -- Step 4.1: The domain `(0,∞)` is convex.
      refine ⟨convex_Ioi (𝕜 := ℝ) (0 : ℝ), ?_⟩
      -- Step 4.2: Take two positive points and convex weights.
      intro x hx y hy A B hA hB hAB
      -- Step 4.3: Name the convex combination.
      set z : ℝ := A • x + B • y
      -- Step 4.4: The convex combination stays in `(0,∞)`.
      have hz : z ∈ Ioi (0 : ℝ) := by
        dsimp [z]
        exact ((convex_Ioi (𝕜 := ℝ) (0 : ℝ) : Convex ℝ (Ioi (0 : ℝ))) hx hy hA hB hAB)
      -- Step 4.5: Convert membership facts into nonnegativity facts used for infimum bounds.
      have hx_nonneg : 0 ≤ x := le_of_lt hx
      have hy_nonneg : 0 ≤ y := le_of_lt hy
      have hz_nonneg : 0 ≤ z := le_of_lt hz
      -- Step 4.6: Show the desired concavity inequality by proving it is below every affine
      -- term at the convex combination.
      dsimp [ν]
      apply le_ciInf
      intro q
      -- Step 4.7: Bound each `ν` value by the corresponding affine term.
      have hx_inf : (⨅ q : ℚpos, φ q x) ≤ φ q x :=
        ciInf_le (hφ_bddBelow hx_nonneg) q
      have hy_inf : (⨅ q : ℚpos, φ q y) ≤ φ q y :=
        ciInf_le (hφ_bddBelow hy_nonneg) q
      -- Step 4.8: Nonnegative weights preserve these two inequalities.
      have hweighted :
          A * (⨅ q : ℚpos, φ q x) + B * (⨅ q : ℚpos, φ q y) ≤
            A * φ q x + B * φ q y := by
        exact add_le_add (mul_le_mul_of_nonneg_left hx_inf hA)
          (mul_le_mul_of_nonneg_left hy_inf hB)
      -- Step 4.9: The affine term commutes with convex combinations.
      have haffine : A * φ q x + B * φ q y = φ q z := by
        have hδne : δ q ≠ 0 := ne_of_gt (hδ_pos q)
        calc
          A * φ q x + B * φ q y =
              (A + B) * (q : ℝ) + K * (A * x + B * y) / δ q := by
            dsimp [φ]
            field_simp [hδne]
            ring
          _ = φ q z := by
            dsimp [φ, z]
            rw [hAB]
            ring
      -- Step 4.10: Combine the weighted bound with the affine identity.
      simpa [smul_eq_mul, haffine] using hweighted
    -- Step 4.11: A real-valued concave function on an open convex set is continuous there.
    have hν_cont : ContinuousOn ν (Ioi 0) := hν_concave.continuousOn isOpen_Ioi
    -- Step 5: Define the final modulus by adding `x`; this forces strict increase.
    let μ : ℝ → ℝ := fun x => ν x + x
    -- Step 5.1: Prove positivity on `(0,∞)`.
    have hμ_pos : ∀ x : ℝ, x > 0 → μ x > 0 := by
      intro x hx
      have hx_nonneg : 0 ≤ x := le_of_lt hx
      have hνx : 0 ≤ ν x := hν_nonneg hx_nonneg
      dsimp [μ]
      exact add_pos_of_nonneg_of_pos hνx hx
    -- Step 5.2: Prove continuity on `(0,∞)` from continuity of `ν` and of the identity.
    have hμ_cont : ContinuousOn μ (Ioi 0) := by
      dsimp [μ]
      exact hν_cont.add continuousOn_id
    -- Step 5.3: Prove strict monotonicity on `(0,∞)`.
    have hμ_strict : StrictMonoOn μ (Ioi 0) := by
      intro x hx y hy hxy
      -- Step 5.3.1: `ν x ≤ ν y` by monotonicity of `ν`.
      have hνxy : ν x ≤ ν y := hν_mono_nonneg (le_of_lt hx) hxy.le
      -- Step 5.3.2: Adding the strictly increasing identity term makes the sum strict.
      dsimp [μ]
      linarith
    -- Step 6: Prove that `μ(x) → 0` as `x → 0+`.
    have hμ_tendsto : Tendsto μ (𝓝[>] 0) (𝓝 0) := by
      -- Step 6.1: Use the metric right-neighborhood criterion.
      rw [Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      -- Step 6.2: Pick a positive rational `q < ε/3`.
      have hthird_pos : (0 : ℝ) < ε / 3 := by positivity
      obtain ⟨qrat, hqrat_pos, hqrat_lt⟩ := exists_rat_btwn hthird_pos
      let q : ℚpos := ⟨qrat, by exact_mod_cast hqrat_pos⟩
      have hq_pos_real : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.2
      have hq_lt : (q : ℝ) < ε / 3 := by
        simpa [q] using hqrat_lt
      -- Step 6.3: Choose a positive input radius making both `x` and `K*x/δq` less than `ε/3`.
      let η : ℝ := min (ε / 3) ((ε / 3) * δ q / K)
      have hη_pos : 0 < η := by
        have hpart : 0 < (ε / 3) * δ q / K := by
          exact div_pos (mul_pos hthird_pos (hδ_pos q)) hK_pos
        exact lt_min hthird_pos hpart
      refine ⟨η, hη_pos, ?_⟩
      intro x hx_pos hx_dist
      -- Step 6.4: Since `x > 0`, `dist x 0 < η` is just `x < η`.
      have hx_abs : |x| = x := abs_of_nonneg (le_of_lt hx_pos)
      have hx_lt_eta : x < η := by
        simpa [Real.dist_eq, hx_abs] using hx_dist
      -- Step 6.5: Extract the two smallness inequalities from `x < min ...`.
      have hx_lt_eps3 : x < ε / 3 := lt_of_lt_of_le hx_lt_eta (min_le_left _ _)
      have hx_lt_scaled : x < (ε / 3) * δ q / K :=
        lt_of_lt_of_le hx_lt_eta (min_le_right _ _)
      -- Step 6.6: Convert the scaled inequality into `K*x/δq < ε/3`.
      have hKx_lt : K * x / δ q < ε / 3 := by
        have hmul : x * K < (ε / 3) * δ q := by
          rwa [lt_div_iff₀ hK_pos] at hx_lt_scaled
        rw [div_lt_iff₀ (hδ_pos q)]
        nlinarith
      -- Step 6.7: Bound `ν x` by the selected affine term.
      have hν_upper : ν x ≤ φ q x := hν_le_φ (le_of_lt hx_pos) q
      -- Step 6.8: Therefore `μ x ≤ q + K*x/δq + x`.
      have hμ_upper : μ x ≤ (q : ℝ) + K * x / δ q + x := by
        dsimp [μ, φ] at hν_upper ⊢
        linarith
      -- Step 6.9: The right-hand side is less than `ε`.
      have hμ_lt : μ x < ε := by
        have : (q : ℝ) + K * x / δ q + x < ε := by
          linarith
        exact hμ_upper.trans_lt this
      -- Step 6.10: `μ x` is nonnegative, so its distance to zero is just itself.
      have hμ_nonneg : 0 ≤ μ x := by
        dsimp [μ]
        exact add_nonneg (hν_nonneg (le_of_lt hx_pos)) (le_of_lt hx_pos)
      simpa [Real.dist_eq, abs_of_nonneg hμ_nonneg] using hμ_lt
    -- Step 7: Prove the modulus inequality.
    have hμ_control : ∀ s t : Icc a b, |f s - f t| ≤ μ (|(s : ℝ) - (t : ℝ)|) := by
      intro s t
      -- Step 7.1: Name the distance between `s` and `t` in the ambient real interval.
      set d : ℝ := |(s : ℝ) - (t : ℝ)|
      have hd_nonneg : 0 ≤ d := by
        dsimp [d]
        exact abs_nonneg _
      -- Step 7.2: Show `|f s - f t|` is below every affine upper bound `φ q d`.
      have hdiff_le_all : ∀ q : ℚpos, |f s - f t| ≤ φ q d := by
        intro q
        -- Step 7.2.1: Split according to whether `d < δ q`.
        by_cases hdlt : d < δ q
        · -- Step 7.2.2: If `d < δ q`, uniform continuity gives oscillation less than `q`.
          have hdist_st : dist s t < δ q := by
            have : |(s : ℝ) - (t : ℝ)| < δ q := by simpa [d] using hdlt
            simpa [Real.dist_eq] using this
          have hf_lt : |f s - f t| < (q : ℝ) := by
            have := hδ_spec q s t hdist_st
            simpa [Real.dist_eq] using this
          have hterm_nonneg : 0 ≤ K * d / δ q := by
            exact div_nonneg (mul_nonneg hK_nonneg hd_nonneg) (le_of_lt (hδ_pos q))
          dsimp [φ]
          linarith
        · -- Step 7.2.3: If `δ q ≤ d`, the global bound `K` is dominated by `K*d/δq`.
          have hδ_le_d : δ q ≤ d := le_of_not_gt hdlt
          have hratio : 1 ≤ d / δ q := by
            rw [le_div_iff₀ (hδ_pos q)]
            simpa using hδ_le_d
          have hK_le : K ≤ K * d / δ q := by
            calc
              K = K * 1 := by ring
              _ ≤ K * (d / δ q) := mul_le_mul_of_nonneg_left hratio hK_nonneg
              _ = K * d / δ q := by ring
          have hq_nonneg : (0 : ℝ) ≤ (q : ℝ) := le_of_lt (by exact_mod_cast q.2)
          have hdiffK : |f s - f t| ≤ K := hdiff_bound s t
          dsimp [φ]
          linarith
      -- Step 7.3: Taking the infimum preserves the bound because the left side is a lower
      -- bound for all affine upper bounds.
      have hdiff_le_ν : |f s - f t| ≤ ν d := by
        dsimp [ν]
        exact le_ciInf hdiff_le_all
      -- Step 7.4: Finally, `μ d = ν d + d`, and `d ≥ 0`.
      have hν_le_μ : ν d ≤ μ d := by
        dsimp [μ]
        exact le_add_of_nonneg_right hd_nonneg
      exact hdiff_le_ν.trans hν_le_μ
    -- Step 8: Assemble the required witness and all its properties.
    refine ⟨μ, hμ_pos, hμ_cont, hμ_strict, hμ_tendsto, ?_⟩
    -- Step 8.1: Rewrite the ambient-subtraction form to match the theorem statement.
    intro s t
    simpa using hμ_control s t
  · -- Step 9: Prove the reverse implication.
    -- A function controlled by a modulus tending to zero on the right is uniformly continuous.
    intro hmod
    -- Step 9.1: Unpack the modulus and its properties.
    rcases hmod with ⟨μ, hμ_pos, hμ_cont, hμ_mono, hμ_tendsto, hcontrol⟩
    -- Step 9.2: Use the metric uniform-continuity criterion.
    refine (Metric.uniformContinuous_iff).2 ?_
    intro ε hε
    -- Step 9.3: Convert the right-hand limit of `μ` into an explicit positive radius.
    obtain ⟨δ, hδpos, hδ⟩ := (Metric.tendsto_nhdsWithin_nhds).1 hμ_tendsto ε hε
    refine ⟨δ, hδpos, ?_⟩
    intro s t hst
    -- Step 9.4: Name the ambient distance between `s` and `t`.
    set d : ℝ := |(s : ℝ) - (t : ℝ)|
    have hd_nonneg : 0 ≤ d := by
      dsimp [d]
      exact abs_nonneg _
    have hd_lt : d < δ := by
      have : |(s : ℝ) - (t : ℝ)| < δ := by
        simpa [Real.dist_eq] using hst
      simpa [d] using this
    -- Step 9.5: If the input distance is zero, then the points are equal and the conclusion is
    -- immediate.
    by_cases hd_zero : d = 0
    · have hsub_zero : (s : ℝ) - (t : ℝ) = 0 := by
        exact abs_eq_zero.mp (by simpa [d] using hd_zero)
      have hst_eq_real : (s : ℝ) = (t : ℝ) := sub_eq_zero.mp hsub_zero
      have hst_eq : s = t := Subtype.ext hst_eq_real
      simp [hst_eq, hε]
    · -- Step 9.6: Otherwise `d` is a positive right-neighborhood input.
      have hd_pos : 0 < d := lt_of_le_of_ne hd_nonneg (Ne.symm hd_zero)
      have hμ_small : dist (μ d) 0 < ε := hδ (by simpa [d] using hd_pos) (by
        simpa [Real.dist_eq, abs_of_nonneg hd_nonneg] using hd_lt)
      -- Step 9.7: The control inequality forces `μ d` to be nonnegative.
      have hbound : |f s - f t| ≤ μ d := by
        simpa [d] using hcontrol s t
      have hμ_nonneg : 0 ≤ μ d := (abs_nonneg _).trans hbound
      -- Step 9.8: Therefore `μ d < ε`.
      have hμ_lt : μ d < ε := by
        simpa [Real.dist_eq, abs_of_nonneg hμ_nonneg] using hμ_small
      -- Step 9.9: Combine the control bound with `μ d < ε`.
      have hfinal : |f s - f t| < ε := hbound.trans_lt hμ_lt
      simpa [Real.dist_eq] using hfinal
