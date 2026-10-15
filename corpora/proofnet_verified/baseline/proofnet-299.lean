import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

abbrev I : Set ℝ := Icc 0 1

/-Informal Statement

Define $f_{n}:[0,1] \rightarrow \mathbb{R}$ by the equation $f_{n}(x)=x^{n}$. Show that the sequence $\left(f_{n}\right)$ does not converge uniformly.
-/

/-Informal Proof

The sequence $\left(f_n\right)_n$ does not converge uniformly, since given $0<\varepsilon<1$ and $N \in \mathbb{Z}_{+}$, for $x=\varepsilon^{1 / N}$ we have $d\left(f_N(x), f(x)\right)=\varepsilon$. We can also apply Theorem 21.6: the convergence is not uniform since $f$ is not continuous.
-/

theorem Munkres_exercise_21_6b
  (f : ℕ → I → ℝ)
  (h : ∀ x n, f n x = ↑x ^ n) :
  ¬ ∃ f₀, TendstoUniformly f f₀ atTop := by
  classical
  -- Step 1: Argue by contradiction and assume a uniformly convergent limit exists.
  intro hUniform
  rcases hUniform with ⟨f₀, hh⟩
  -- Step 1.1: Record that each function `f n` is continuous by identifying it with a polynomial map.
  have hf_cont : ∀ n, Continuous (f n) := by
    intro n
    have hPow : (fun x : I => f n x) = fun x : I => (x : ℝ) ^ n := by
      funext x; simp [h]
    -- Step 1.1.1: Compose the continuous inclusion `I ↪ ℝ` with the continuous power map on `ℝ`.
    simpa [hPow] using ((continuous_pow n).comp continuous_subtype_val)
  -- Step 1.2: Convert continuity of each `f n` into continuity of the candidate limit `f₀`.
  have hf₀_continuous : Continuous f₀ := by
    have h_eventually : ∀ᶠ n in atTop, Continuous (f n) :=
      Filter.eventually_atTop.2 <| by
        refine ⟨0, ?_⟩
        intro n _; exact hf_cont n
    exact hh.continuous h_eventually.frequently
  -- Step 2: Describe the pointwise limit explicitly using the known power-limit behavior on `[0, 1]`.
  have hx_bounds : ∀ x : I, 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ 1 := by
    intro x
    have hx_mem : (x : ℝ) ∈ I := by simp [I]
    exact Set.mem_Icc.mp hx_mem
  -- Step 2.1: Show that every point strictly inside the interval is mapped to `0` by `f₀`.
  have h_lt_one_value : ∀ ⦃x : I⦄, (x : ℝ) < 1 → f₀ x = 0 := by
    intro x hxlt1
    have hx_pow : Tendsto (fun n : ℕ => f n x) atTop (𝓝 (0 : ℝ)) := by
      have hx0 : (0 : ℝ) ≤ (x : ℝ) := (hx_bounds x).1
      have hxabs : |(x : ℝ)| < 1 := by
        simpa [abs_of_nonneg hx0] using hxlt1
      have hpow_lim :=
        (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hxabs :
          Tendsto (fun n : ℕ => (x : ℝ) ^ n) atTop (𝓝 (0 : ℝ)))
      have hfunext : (fun n => f n x) = fun n : ℕ => (x : ℝ) ^ n := by
        funext n; simp [h]
      simpa [hfunext]
    have hx_uni : Tendsto (fun n : ℕ => f n x) atTop (𝓝 (f₀ x)) := hh.tendsto_at x
    -- Step 2.1.1: Uniqueness of limits in Hausdorff spaces identifies `f₀ x` with `0`.
    simpa using (tendsto_nhds_unique hx_uni hx_pow)
  -- Step 2.2: Identify the boundary value `f₀ 1 = 1` using the constant subsequence.
  let xOne : I := ⟨1, by
    refine ⟨by norm_num, le_rfl⟩
  ⟩
  have hxOne_value : f₀ xOne = 1 := by
    have hconst : (fun n : ℕ => f n xOne) = fun _ : ℕ => (1 : ℝ) := by
      funext n; simp [xOne, h]
    have hconst_tendsto : Tendsto (fun n : ℕ => f n xOne) atTop (𝓝 (1 : ℝ)) := by
      simp [hconst]
    have hx_uni : Tendsto (fun n : ℕ => f n xOne) atTop (𝓝 (f₀ xOne)) := hh.tendsto_at xOne
    -- Step 2.2.1: Again use uniqueness of limits to show that `f₀ xOne = 1`.
    simpa using (tendsto_nhds_unique hx_uni hconst_tendsto)
  -- Step 3: Apply continuity of `f₀` at the endpoint to derive the final contradiction.
  have hf₀_cont_at : ContinuousAt f₀ xOne := hf₀_continuous.continuousAt
  -- Step 3.1: Use the ε-δ definition with `ε = 1/2`.
  have h_half_pos : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨δ, δ_pos, hδ⟩ := (Metric.continuousAt_iff).mp hf₀_cont_at (1 / 2) h_half_pos
  -- Step 3.2: Pick an explicit point `y` slightly to the left of `1` but still in `I`.
  set t : ℝ := min (δ / 2) (1 / 2)
  have ht_pos : 0 < t := by
    have hδ2 : 0 < δ / 2 := by simpa [one_div] using half_pos δ_pos
    have hhalf : 0 < (1 : ℝ) / 2 := by norm_num
    simpa [t] using lt_min hδ2 hhalf
  have ht_le_delta_half : t ≤ δ / 2 := by
    have := min_le_left (δ / 2) (1 / 2)
    simp [t]
  have ht_le_half : t ≤ 1 / 2 := by
    have := min_le_right (δ / 2) (1 / 2)
    simp [t]
  have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
  set yVal : ℝ := 1 - t
  have hy_nonneg : 0 ≤ yVal := by
    have ht_le_one : t ≤ 1 := le_trans ht_le_half (by norm_num)
    exact sub_nonneg.mpr ht_le_one
  have hy_le_one : yVal ≤ 1 := by
    simpa [yVal] using sub_le_self (1 : ℝ) ht_nonneg
  have hy_lt_one : yVal < 1 := by
    simpa [yVal] using sub_lt_self (1 : ℝ) ht_pos
  let y : I := ⟨yVal, ⟨hy_nonneg, hy_le_one⟩⟩
  -- Step 3.3: Verify that `y` lies in the δ-ball around `xOne`.
  have hy_dist_eq : dist y xOne = t := by
    simp [Subtype.dist_eq, y, yVal, xOne, abs_of_nonneg ht_nonneg,
      sub_eq_add_neg]
  have hy_dist_lt : dist y xOne < δ := by
    have hle : dist y xOne ≤ δ / 2 := by
      simpa [hy_dist_eq] using ht_le_delta_half
    have hhalf_lt : δ / 2 < δ := half_lt_self δ_pos
    exact lt_of_le_of_lt hle hhalf_lt
  -- Step 3.4: Evaluate `f₀` at `y` using the interior-limit description.
  have hy_value : f₀ y = 0 := h_lt_one_value (by simpa [y, yVal] using hy_lt_one)
  have hdist_values := hδ hy_dist_lt
  -- Step 3.5: Translate the continuity inequality into the contradiction `1 < 1/2`.
  have : (1 : ℝ) < 1 / 2 := by
    simpa [hy_value, hxOne_value, Real.dist_eq] using hdist_values
  exact (not_lt.mpr (by norm_num : (1 / 2 : ℝ) ≤ 1)) this
