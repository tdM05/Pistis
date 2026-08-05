import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

noncomputable section


/-Informal Statement

Suppose $f$ is a real function with domain $R^{1}$ which has the intermediate value property: if $f(a) < c < f(b)$, then $f(x)=c$ for some $x$ between $a$ and $b$. Suppose also, for every rational $r$, that the set of all $x$ with $f(x)=r$ is closed. Prove that $f$ is continuous.
-/

/-Informal Proof

The contradiction is evidently that $x_0$ is a limit point of the set of $t$ such that $f(t)=r$, yet, $x_0$ does not belong to this set. This contradicts the hypothesis that the set is closed.
-/

theorem Rudin_exercise_4_19
  {f : ℝ → ℝ} (hf : ∀ a b c, a < b → f a < c → c < f b → ∃ x, a < x ∧ x < b ∧ f x = c)
  (hg : ∀ r : ℚ, IsClosed {x | f x = r}) : Continuous f := by
  sorry

/-
Step-by-step disproof, explanation, and repair of the formal statement.

The informal text intends the full intermediate value property.  The formal
version only handles the case `f a < c < f b` when `a < b`; it says nothing
when `f a > f b`, so any *strictly decreasing* function satisfies `hf`
vacuously.  We exploit this gap to build a discontinuous counterexample whose
every rational level set is still closed.
-/

/-- Counterexample function: strictly decreasing with a jump at `0`. -/
def fCounter : ℝ → ℝ := fun x => if x ≤ 0 then -x else -x - 1

lemma fCounter_strictAnti : StrictAnti fCounter := by
  -- Step 1: unfold the definition and split into the three positional cases.
  -- Step 1.1: `a < b ≤ 0`, both inputs on the left branch.
  -- Step 1.2: `a < 0 < b`, inputs on different branches (the jump).
  -- Step 1.3: `0 ≤ a < b`, both inputs on the right branch.
  intro a b hlt
  by_cases hb : b ≤ 0
  · -- Step 1.1: Both `a` and `b` are nonpositive.
    have ha : a ≤ 0 := le_trans (le_of_lt hlt) hb
    -- On this branch `fCounter x = -x`, which is strictly decreasing.
    have hfa : fCounter a = -a := by simp [fCounter, ha]
    have hfb : fCounter b = -b := by simp [fCounter, hb]
    -- The inequality `a < b` becomes `-a > -b`.
    have hneg : -a > -b := by linarith
    simpa [hfa, hfb] using hneg
  · -- Step 1.2 or 1.3: `b > 0`.
    have hbpos : 0 < b := lt_of_not_ge hb
    by_cases ha : a ≤ 0
    · -- Step 1.2: `a ≤ 0 < b`, across the jump.
      have hfa : fCounter a = -a := by simp [fCounter, ha]
      have hfb : fCounter b = -b - 1 := by
        have : ¬ b ≤ 0 := not_le_of_gt hbpos
        simp [fCounter, this]
      -- Here `-a ≥ 0` while `-b - 1 < -1`, so the inequality is automatic.
      have hpos : 0 ≤ -a := by linarith
      have hneg : -b - 1 < -1 := by linarith
      -- Combining gives `fCounter a > fCounter b`.
      have hgt : fCounter a > fCounter b := by
        -- `-a ≥ 0` and `-b - 1 < -1`, so `-a > -b - 1`.
        have : (-a) - (-b - 1) ≥ 1 := by linarith
        linarith
      simpa [hfa, hfb] using hgt
    · -- Step 1.3: `0 < a < b`, right branch only.
      have hapos : 0 < a := lt_of_not_ge ha
      have hfa : fCounter a = -a - 1 := by
        have : ¬ a ≤ 0 := not_le_of_gt hapos
        simp [fCounter, this]
      have hfb : fCounter b = -b - 1 := by
        have : ¬ b ≤ 0 := not_le_of_gt hbpos
        simp [fCounter, this]
      -- Both sides are `-x - 1`, still strictly decreasing.
      have hneg : -a - 1 > -b - 1 := by linarith
      simpa [hfa, hfb] using hneg

lemma hf_counterexample :
    ∀ a b c, a < b → fCounter a < c → c < fCounter b →
      ∃ x, a < x ∧ x < b ∧ fCounter x = c := by
  -- Step 2: show the original hypothesis `hf` holds *vacuously* for `fCounter`.
  intro a b c hlt hfa hcb
  -- Since `fCounter` is strictly decreasing, `fCounter a < fCounter b` is impossible.
  have hgt : fCounter a > fCounter b := fCounter_strictAnti hlt
  -- The assumptions `fCounter a < c < fCounter b` contradict strict decrease.
  have hcontr : False := not_lt_of_gt hgt (lt_trans hfa hcb)
  -- From contradiction, anything follows; provide an arbitrary witness.
  exact False.elim hcontr

lemma hg_counterexample : ∀ r : ℚ, IsClosed {x : ℝ | fCounter x = r} := by
  -- Step 3: each fiber is a singleton or empty because `fCounter` is injective.
  have h_inj : Function.Injective fCounter := fCounter_strictAnti.injective
  intro r
  classical
  -- Step 3.1: either `r` is attained once or not attained at all.
  by_cases h : ∃ x, fCounter x = r
  · -- Step 3.2: the fiber is a singleton `{x0}`.
    rcases h with ⟨x0, hx0⟩
    have hset : {x : ℝ | fCounter x = r} = {x0} := by
      -- Step 3.2.1: extensionality of the equality set.
      ext x
      constructor
      · intro hx
        have : fCounter x = fCounter x0 := by simpa [hx0] using hx
        -- Injectivity forces `x = x0`.
        exact h_inj this
      · intro hx
        -- Using `hx : x = x0`, rewrite and finish.
        subst hx
        simp [hx0]
    -- Singletons are closed in `ℝ`.
    simp [hset]
  · -- Step 3.3: the fiber is empty, hence closed.
    have hset : {x : ℝ | fCounter x = r} = (∅ : Set ℝ) := by
      ext x
      constructor
      · intro hx; exact False.elim (h ⟨x, hx⟩)
      · intro hx; cases hx
    simp [hset]

lemma not_continuous_counterexample : ¬ Continuous fCounter := by
  -- Step 4: prove discontinuity at `0` via a sequence approaching from the right.
  -- Step 4.1: compute the explicit form of the sequence values.
  have hSeqEq :
      (fun n : ℕ => fCounter ((n + 1 : ℝ)⁻¹)) =
        fun n : ℕ => -((n + 1 : ℝ)⁻¹) - 1 := by
    funext n
    -- Each term `1/(n+1)` is positive, so we are in the right branch.
    have hpos : (0 : ℝ) < (n + 1 : ℝ)⁻¹ := by
      have hden : (0 : ℝ) < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
      exact inv_pos.mpr hden
    have hle : ¬ (n + 1 : ℝ)⁻¹ ≤ 0 := not_le_of_gt hpos
    simp [fCounter, hle]
  -- Step 4.2: the sequence tends to `-1`.
  have hSeqLimit :
      Tendsto (fun n : ℕ => fCounter ((n + 1 : ℝ)⁻¹)) atTop (𝓝 (-1)) := by
    -- Rewrite with the explicit expression.
    have hAux : Tendsto (fun n : ℕ => -((n + 1 : ℝ)⁻¹) - 1) atTop (𝓝 (-1)) := by
      -- The inner sequence `1/(n+1)` tends to `0`.
      have h0 : Tendsto (fun n : ℕ => (n + 1 : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) := by
        simpa [one_div] using
          (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 (0 : ℝ)))
      -- Negation preserves the limit.
      have h0' : Tendsto (fun n : ℕ => -((n + 1 : ℝ)⁻¹)) atTop (𝓝 0) := by
        simpa using h0.neg
      -- Subtracting `1` shifts the limit to `-1`.
      have h0'' :
          Tendsto (fun n : ℕ => -((n + 1 : ℝ)⁻¹) - 1) atTop (𝓝 (0 - 1)) :=
        h0'.sub tendsto_const_nhds
      simpa using h0''
    simpa [hSeqEq] using hAux
  -- Step 4.3: continuity at `0` would force the same sequence to converge to `0`.
  intro hcont
  have hcont0 : ContinuousAt fCounter 0 := hcont.continuousAt
  -- Compose with the sequence `n ↦ (n+1)⁻¹`.
  have hbase : Tendsto (fun n : ℕ => (n + 1 : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 (0 : ℝ)))
  have hcomp :
      Tendsto (fun n : ℕ => fCounter ((n + 1 : ℝ)⁻¹)) atTop (𝓝 (fCounter 0)) :=
    hcont0.tendsto.comp hbase
  -- Evaluate `fCounter 0 = 0`.
  have hf0 : fCounter 0 = 0 := by simp [fCounter]
  have hcomp' : Tendsto (fun n : ℕ => fCounter ((n + 1 : ℝ)⁻¹)) atTop (𝓝 0) := by
    simpa [hf0] using hcomp
  -- Uniqueness of limits in a Hausdorff space yields a contradiction.
  have hEq : (-1 : ℝ) = 0 := tendsto_nhds_unique hSeqLimit hcomp'
  have hNe : (-1 : ℝ) ≠ 0 := by norm_num
  exact hNe hEq

/-- The formal statement is therefore false. -/
theorem Rudin_exercise_4_19_neg :
    ∃ f : ℝ → ℝ,
      (∀ a b c, a < b → f a < c → c < f b → ∃ x, a < x ∧ x < b ∧ f x = c) ∧
      (∀ r : ℚ, IsClosed {x | f x = r}) ∧ ¬ Continuous f := by
  -- Step 5: package the counterexample function and collected properties.
  refine ⟨fCounter, ?_, ?_, ?_⟩
  · exact hf_counterexample
  · exact hg_counterexample
  · exact not_continuous_counterexample

/-
Corrected version:
To recover the intended result, the intermediate value property must work in
both directions.  We add the symmetric hypothesis

`hf_symm : ∀ a b c, a < b →
    ((f a < c ∧ c < f b) ∨ (f b < c ∧ c < f a)) →
    ∃ x, a < x ∧ x < b ∧ f x = c`.

With this genuine Darboux property, the closure of every rational level set
forces continuity.
-/

theorem Rudin_exercise_4_19_corrected
  {f : ℝ → ℝ}
  (hf : ∀ a b c, a < b →
      ((f a < c ∧ c < f b) ∨ (f b < c ∧ c < f a)) →
      ∃ x, a < x ∧ x < b ∧ f x = c)
  (hg : ∀ r : ℚ, IsClosed {x | f x = r}) : Continuous f := by
  -- Step 1: reduce global continuity to continuity at each point.
  refine continuous_iff_continuousAt.2 ?_
  intro x0
  -- Step 2: assume (for contradiction) that `f` is not continuous at `x0`.
  by_contra hcont
  -- Step 2.1: restate non-continuity as failure of the `Tendsto` criterion.
  have hcont' : ¬ Tendsto f (𝓝 x0) (𝓝 (f x0)) := by
    simpa [ContinuousAt] using hcont
  -- Step 2.2: use the sequential characterization to pick a convergent sequence with bad images.
  have hseq :=
    (tendsto_nhds_iff_seq_tendsto (X := ℝ) (Y := ℝ)).not.mp hcont'
  classical
  rcases not_forall.mp hseq with ⟨xn, hx⟩
  rcases Classical.not_imp.mp hx with ⟨hxn_tendsto, hxn_bad⟩
  -- Step 3: from non-convergence of `(f ∘ xn)` obtain a positive gap seen infinitely often.
  have hgap : ∃ ε > (0 : ℝ), ∃ᶠ n in atTop, |f (xn n) - f x0| ≥ ε := by
    classical
    -- Step 3.1: pick a neighborhood where the convergence of `f ∘ xn` fails.
    obtain ⟨s, hs_mem, hs_freq⟩ :=
      (Filter.not_tendsto_iff_exists_frequently_notMem).mp hxn_bad
    rcases Metric.mem_nhds_iff.1 hs_mem with ⟨ε, εpos, hball⟩
    -- Step 3.2: shrinking to a ball gives a concrete gap `ε`.
    have hfreq_ball : ∃ᶠ n in atTop, f (xn n) ∉ Metric.ball (f x0) ε := by
      refine hs_freq.mono ?_
      intro n hn hmem
      exact hn (hball hmem)
    have hfreq_abs : ∃ᶠ n in atTop, |f (xn n) - f x0| ≥ ε := by
      refine hfreq_ball.mono ?_
      intro n hn
      have hnotlt : ¬ dist (f (xn n)) (f x0) < ε := by
        intro hlt
        exact hn (by simpa [Metric.mem_ball] using hlt)
      have hdist : ε ≤ dist (f (xn n)) (f x0) := not_lt.mp hnotlt
      -- Rewrite the distance on `ℝ` as an absolute value.
      simpa [Real.dist_eq, abs_sub_comm] using hdist
    exact ⟨ε, εpos, hfreq_abs⟩
  rcases hgap with ⟨ε, εpos, hfreq_gap⟩
  -- Step 4: split the large deviations into the two one-sided inequalities.
  let p : ℕ → Prop := fun n => f (xn n) ≥ f x0 + ε
  let q : ℕ → Prop := fun n => f (xn n) ≤ f x0 - ε
  have hfreq_or : ∃ᶠ n in atTop, p n ∨ q n := by
    -- Each deviation contributes to one of the two cases.
    refine hfreq_gap.mono ?_
    intro n hlarge
    by_cases hsign : f (xn n) - f x0 ≥ 0
    · -- If the difference is nonnegative, the absolute value drops.
      have habs : |f (xn n) - f x0| = f (xn n) - f x0 := abs_of_nonneg hsign
      have hdiff : f (xn n) - f x0 ≥ ε := by linarith [hlarge, habs]
      have : p n := by linarith [hdiff]
      exact Or.inl this
    · -- If the difference is negative, flip the inequality using the absolute value.
      have hneg : f (xn n) - f x0 < 0 := lt_of_not_ge hsign
      have habs : |f (xn n) - f x0| = -(f (xn n) - f x0) := abs_of_neg hneg
      have hdiff : f x0 - f (xn n) ≥ ε := by linarith [hlarge, habs]
      have : q n := by linarith [hdiff]
      exact Or.inr this
  rcases frequently_or_distrib.mp hfreq_or with hfreq_high | hfreq_low
  · -- Step 4.1: Case 1 — infinitely many `xn n` sit above `f x0 + ε`.
    -- Step 4.1.1: choose a rational level strictly between `f x0` and those high values.
    rcases exists_rat_btwn (by linarith : f x0 < f x0 + ε) with ⟨r, hr_low, hr_high⟩
    -- Step 4.1.2: extract a monotone subsequence where the high inequality always holds.
    rcases extraction_of_frequently_atTop hfreq_high with ⟨φ, hφ_mono, hφ_high⟩
    let yn : ℕ → ℝ := fun n => xn (φ n)
    have hyn_tendsto : Tendsto yn atTop (𝓝 x0) := hxn_tendsto.comp hφ_mono.tendsto_atTop
    -- Step 4.1.3: for each `n`, apply the Darboux property to produce `z` with `f z = r`.
    have hmid : ∀ n, ∃ z, min x0 (yn n) < z ∧ z < max x0 (yn n) ∧ f z = r := by
      intro n
      have hval : f (yn n) ≥ f x0 + ε := by simpa [p, yn] using hφ_high n
      -- Step 4.1.3.1: set the interval endpoints and show they are distinct.
      set a := min x0 (yn n)
      set b := max x0 (yn n)
      have hxneq : x0 ≠ yn n := by
        have hgt : f (yn n) > f x0 := by linarith
        intro hEq
        have : f (yn n) = f x0 := by simp [hEq]
        linarith
      have hlt_ab : a < b := by
        rcases lt_or_gt_of_ne hxneq with hlt | hgt
        · have ha : a = x0 := by simp [a, hlt.le]
          have hb : b = yn n := by simp [b, hlt.le]
          simpa [ha, hb] using hlt
        · have ha : a = yn n := by simp [a, (le_of_lt hgt)]
          have hb : b = x0 := by simp [b, (le_of_lt hgt)]
          simpa [ha, hb] using hgt
      -- Step 4.1.3.2: arrange the inequalities so `r` lies between `f a` and `f b`.
      have hbetween : ((f a < r ∧ r < f b) ∨ (f b < r ∧ r < f a)) := by
        by_cases horder : x0 ≤ yn n
        · have ha : a = x0 := by simp [a, horder]
          have hb : b = yn n := by simp [b, horder]
          have hr_lt_fb : r < f b := by
            have : (r : ℝ) < f x0 + ε := hr_high
            have : (r : ℝ) < f (yn n) := by linarith
            simpa [hb] using this
          have hfa_lt_r : f a < r := by
            have : f x0 < (r : ℝ) := hr_low
            simpa [ha] using this
          exact Or.inl ⟨hfa_lt_r, hr_lt_fb⟩
        · have horder' : yn n ≤ x0 := le_of_not_ge horder
          have ha : a = yn n := by simp [a, horder']
          have hb : b = x0 := by simp [b, horder']
          have hfb_lt_r : f b < r := by
            have : f x0 < (r : ℝ) := hr_low
            simpa [hb] using this
          have hr_lt_fa : r < f a := by
            have : f (yn n) ≥ f x0 + ε := hval
            have : (r : ℝ) < f (yn n) := by linarith
            simpa [ha] using this
          exact Or.inr ⟨hfb_lt_r, hr_lt_fa⟩
      rcases hf a b r hlt_ab hbetween with ⟨z, hz1, hz2, hzval⟩
      exact ⟨z, hz1, hz2, hzval⟩
    -- Step 4.1.4: assemble the sequence `z n` hitting the rational `r`.
    classical
    choose z hz1 hz2 hzval using hmid
    -- Step 4.1.5: show `|z n - x0|` is bounded by `|yn n - x0|`.
    have hbound : ∀ n, |z n - x0| ≤ |yn n - x0| := by
      intro n
      by_cases horder : x0 ≤ yn n
      · have hz_between : x0 ≤ z n ∧ z n ≤ yn n := by
          have hz1' : min x0 (yn n) < z n := hz1 n
          have hz2' : z n < max x0 (yn n) := hz2 n
          have ha : min x0 (yn n) = x0 := by simp [min_eq_left horder]
          have hb : max x0 (yn n) = yn n := by simp [max_eq_right horder]
          have hz1'' : x0 < z n := by simpa [ha] using hz1'
          have hz2'' : z n < yn n := by simpa [hb] using hz2'
          exact ⟨hz1''.le, hz2''.le⟩
        have hz_nonneg : z n - x0 ≥ 0 := by linarith
        have hyn_nonneg : yn n - x0 ≥ 0 := by linarith
        have hz_abs : |z n - x0| = z n - x0 := abs_of_nonneg hz_nonneg
        have hyn_abs : |yn n - x0| = yn n - x0 := abs_of_nonneg hyn_nonneg
        linarith
      · have horder' : yn n ≤ x0 := le_of_not_ge horder
        have hz_between : yn n ≤ z n ∧ z n ≤ x0 := by
          have hz1' : min x0 (yn n) < z n := hz1 n
          have hz2' : z n < max x0 (yn n) := hz2 n
          have ha : min x0 (yn n) = yn n := by simp [min_eq_right horder']
          have hb : max x0 (yn n) = x0 := by simp [max_eq_left horder']
          have hz1'' : yn n < z n := by simpa [ha] using hz1'
          have hz2'' : z n < x0 := by simpa [hb] using hz2'
          exact ⟨hz1''.le, hz2''.le⟩
        have hz_nonpos : z n - x0 ≤ 0 := by linarith
        have hyn_nonpos : yn n - x0 ≤ 0 := by linarith
        have hz_abs : |z n - x0| = -(z n - x0) := abs_of_nonpos hz_nonpos
        have hyn_abs : |yn n - x0| = -(yn n - x0) := abs_of_nonpos hyn_nonpos
        linarith
    -- Step 4.1.6: squeeze the distances to deduce `z n → x0`.
    have hz_tendsto : Tendsto z atTop (𝓝 x0) := by
      refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
      have hnorm_bound : ∀ n, ‖z n - x0‖ ≤ ‖yn n - x0‖ := by
        intro n; simpa [Real.norm_eq_abs] using hbound n
      have hnonneg : ∀ᶠ n in atTop, 0 ≤ ‖z n - x0‖ :=
        Filter.eventually_atTop.mpr ⟨0, by intro n hn; exact norm_nonneg _⟩
      have hbound_ev : ∀ᶠ n in atTop, ‖z n - x0‖ ≤ ‖yn n - x0‖ :=
        Filter.eventually_atTop.mpr ⟨0, by intro n hn; exact hnorm_bound n⟩
      have hlim : Tendsto (fun n => ‖yn n - x0‖) atTop (𝓝 0) := by
        simpa [tendsto_iff_norm_sub_tendsto_zero] using hyn_tendsto
      exact squeeze_zero' hnonneg hbound_ev hlim
    -- Step 4.1.7: closedness of the fiber forces `x0` itself to satisfy `f x0 = r`.
    have hclosed := hg r
    have hz_in : ∀ᶠ n in atTop, z n ∈ {x : ℝ | f x = r} := by
      refine Filter.eventually_atTop.mpr ?_
      refine ⟨0, ?_⟩
      intro n hn
      simpa using hzval n
    have hx0_in : x0 ∈ {x : ℝ | f x = r} :=
      hclosed.mem_of_tendsto hz_tendsto hz_in
    have hx0_val : f x0 = r := hx0_in
    linarith
  · -- Step 4.2: Case 2 — infinitely many `xn n` sit below `f x0 - ε` (mirror argument).
    -- Step 4.2.1: choose a rational level strictly between the low values and `f x0`.
    rcases exists_rat_btwn (by linarith : f x0 - ε < f x0) with ⟨r, hr_low, hr_high⟩
    -- Step 4.2.2: extract a monotone subsequence satisfying the low inequality.
    rcases extraction_of_frequently_atTop hfreq_low with ⟨φ, hφ_mono, hφ_low⟩
    let yn : ℕ → ℝ := fun n => xn (φ n)
    have hyn_tendsto : Tendsto yn atTop (𝓝 x0) := hxn_tendsto.comp hφ_mono.tendsto_atTop
    -- Step 4.2.3: for each `n`, use the intermediate value property to hit the rational `r`.
    have hmid : ∀ n, ∃ z, min x0 (yn n) < z ∧ z < max x0 (yn n) ∧ f z = r := by
      intro n
      have hval : f (yn n) ≤ f x0 - ε := by simpa [q, yn] using hφ_low n
      set a := min x0 (yn n)
      set b := max x0 (yn n)
      have hxneq : x0 ≠ yn n := by
        have hlt : f (yn n) < f x0 := by linarith
        intro hEq
        have : f (yn n) = f x0 := by simp [hEq]
        linarith
      have hlt_ab : a < b := by
        rcases lt_or_gt_of_ne hxneq with hlt | hgt
        · have ha : a = x0 := by simp [a, hlt.le]
          have hb : b = yn n := by simp [b, hlt.le]
          simpa [ha, hb] using hlt
        · have ha : a = yn n := by simp [a, (le_of_lt hgt)]
          have hb : b = x0 := by simp [b, (le_of_lt hgt)]
          simpa [ha, hb] using hgt
      -- Step 4.2.3.1: position `r` between the endpoint values.
      have hbetween : ((f a < r ∧ r < f b) ∨ (f b < r ∧ r < f a)) := by
        by_cases horder : x0 ≤ yn n
        · have ha : a = x0 := by simp [a, horder]
          have hb : b = yn n := by simp [b, horder]
          have hfb_lt_r : f b < r := by
            have : f (yn n) ≤ f x0 - ε := hval
            have : f b ≤ f x0 - ε := by simpa [hb] using this
            linarith [hr_low]
          have hr_lt_fa : r < f a := by
            have : (r : ℝ) < f x0 := hr_high
            simpa [ha] using this
          exact Or.inr ⟨hfb_lt_r, hr_lt_fa⟩
        · have horder' : yn n ≤ x0 := le_of_not_ge horder
          have ha : a = yn n := by simp [a, horder']
          have hb : b = x0 := by simp [b, horder']
          have hfa_lt_r : f a < r := by
            have : f (yn n) ≤ f x0 - ε := hval
            have : f a ≤ f x0 - ε := by simpa [ha] using this
            linarith [hr_low]
          have hr_lt_fb : r < f b := by
            have : (r : ℝ) < f x0 := hr_high
            simpa [hb] using this
          exact Or.inl ⟨hfa_lt_r, hr_lt_fb⟩
      rcases hf a b r hlt_ab hbetween with ⟨z, hz1, hz2, hzval⟩
      exact ⟨z, hz1, hz2, hzval⟩
    classical
    choose z hz1 hz2 hzval using hmid
    -- Step 4.2.4: compare the distances of `z n` and `yn n` to `x0`.
    have hbound : ∀ n, |z n - x0| ≤ |yn n - x0| := by
      intro n
      by_cases horder : x0 ≤ yn n
      · have hz_between : x0 ≤ z n ∧ z n ≤ yn n := by
          have ha : min x0 (yn n) = x0 := by simp [min_eq_left horder]
          have hb : max x0 (yn n) = yn n := by simp [max_eq_right horder]
          have hz1' : x0 < z n := by simpa [ha] using hz1 n
          have hz2' : z n < yn n := by simpa [hb] using hz2 n
          exact ⟨hz1'.le, hz2'.le⟩
        have hz_nonneg : z n - x0 ≥ 0 := by linarith
        have hyn_nonneg : yn n - x0 ≥ 0 := by linarith
        have hz_abs : |z n - x0| = z n - x0 := abs_of_nonneg hz_nonneg
        have hyn_abs : |yn n - x0| = yn n - x0 := abs_of_nonneg hyn_nonneg
        linarith
      · have horder' : yn n ≤ x0 := le_of_not_ge horder
        have hz_between : yn n ≤ z n ∧ z n ≤ x0 := by
          have ha : min x0 (yn n) = yn n := by simp [min_eq_right horder']
          have hb : max x0 (yn n) = x0 := by simp [max_eq_left horder']
          have hz1' : yn n < z n := by simpa [ha] using hz1 n
          have hz2' : z n < x0 := by simpa [hb] using hz2 n
          exact ⟨hz1'.le, hz2'.le⟩
        have hz_nonpos : z n - x0 ≤ 0 := by linarith
        have hyn_nonpos : yn n - x0 ≤ 0 := by linarith
        have hz_abs : |z n - x0| = -(z n - x0) := abs_of_nonpos hz_nonpos
        have hyn_abs : |yn n - x0| = -(yn n - x0) := abs_of_nonpos hyn_nonpos
        linarith
    -- Step 4.2.5: deduce `z n → x0` from the bound and `yn n → x0`.
    have hz_tendsto : Tendsto z atTop (𝓝 x0) := by
      refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
      have hnorm_bound : ∀ n, ‖z n - x0‖ ≤ ‖yn n - x0‖ := by
        intro n; simpa [Real.norm_eq_abs] using hbound n
      have hnonneg : ∀ᶠ n in atTop, 0 ≤ ‖z n - x0‖ :=
        Filter.eventually_atTop.mpr ⟨0, by intro n hn; exact norm_nonneg _⟩
      have hbound_ev : ∀ᶠ n in atTop, ‖z n - x0‖ ≤ ‖yn n - x0‖ :=
        Filter.eventually_atTop.mpr ⟨0, by intro n hn; exact hnorm_bound n⟩
      have hlim : Tendsto (fun n => ‖yn n - x0‖) atTop (𝓝 0) := by
        simpa [tendsto_iff_norm_sub_tendsto_zero] using hyn_tendsto
      exact squeeze_zero' hnonneg hbound_ev hlim
    -- Step 4.2.6: closed fiber forces `f x0 = r`, contradicting the inequalities.
    have hclosed := hg r
    have hz_in : ∀ᶠ n in atTop, z n ∈ {x : ℝ | f x = r} := by
      refine Filter.eventually_atTop.mpr ?_
      refine ⟨0, ?_⟩
      intro n hn
      simpa using hzval n
    have hx0_in : x0 ∈ {x : ℝ | f x = r} :=
      hclosed.mem_of_tendsto hz_tendsto hz_in
    have hx0_val : f x0 = r := hx0_in
    linarith
