import Mathlib

open Complex Filter Function Metric Finset MeasureTheory
open scoped BigOperators Topology Polynomial



/-Informal Statement

Prove that all entire functions that are also injective take the form $f(z) = az + b$, $a, b \in \mathbb{C}$ and $a \neq 0$.
-/

/-Informal Proof

Look at $f(1 / z)$. If it has an essential singularity at 0 , then pick any $z_0 \neq 0$. Now we know that the range of $f$ is dense as $z \rightarrow 0$. We also know that the image of $f$ in some small ball around $z_0$ contains a ball around $f\left(z_0\right)$. But this means that the image of $f$ around this ball intersects the image of $f$ in any arbitrarily small ball around 0 (because of the denseness). Thus, $f$ cannot be injective. So the singularity at 0 is not essential, so $f(1 / z)$ is some polynomial of $1 / z$, so $f$ is some polynomial of $z$. If its degree is more than 1 it is not injective (fundamental theorem of algebra), so the degree of $f$ is 1 .
-/

theorem Shakarchi_exercise_3_14 {f : ℂ → ℂ} (hf : Differentiable ℂ f)
   (hf_inj : Function.Injective f) :
   ∃ (a b : ℂ), f = (λ z => a * z + b) ∧ a ≠ 0 := by
  classical

  /-
  We follow the informal strategy, but we make every implicit step explicit.

  High-level roadmap (with formal content):

  Step 1: Define `g(z) = f(z⁻¹)` and observe that `g` is injective.

  Step 2: Prove `MeromorphicAt g 0`.
    Step 2.A: Prove a “density” lemma: if `g` is not meromorphic at `0`, then its image on every
              punctured neighborhood of `0` meets every open ball in `ℂ`.
              (Formal proof: contrapositive via the removable singularity theorem applied to
               `φ(z) = (g z - w)⁻¹`.)
    Step 2.B: Apply the local open mapping theorem to `g` at the point `1`, to get that
              `g '' ball 1 (1/4)` is a neighborhood of `g 1`. Combine with Step 2.A to contradict
              injectivity of `g`.

  Step 3: From `MeromorphicAt g 0`, deduce a polynomial growth bound for `f` at infinity.

  Step 4: Use Cauchy estimates (via `norm_cauchyPowerSeries_le`) and the growth bound to prove that
          all coefficients of the Cauchy power series beyond some `N` are zero. Hence `f` is a
          polynomial function.

  Step 5: Show an injective complex polynomial has degree ≤ 1, so `f(z) = a*z + b` with `a ≠ 0`.
  -/

  /-
  Step 1: Define `g(z) = f(z⁻¹)` and record injectivity.
  -/

  -- Step 1.1: Define the auxiliary map.
  -- Note: `0⁻¹ = 0`, but meromorphicity ignores the value at the point anyway.
  set g : ℂ → ℂ := fun z => f z⁻¹

  -- Step 1.2: `g` is injective (composition of injective maps).
  have hg_inj : Function.Injective g := by
    intro z₁ z₂ hz
    -- Step 1.2.1: Use injectivity of `f`.
    have hInv : z₁⁻¹ = z₂⁻¹ := hf_inj (by simpa [g] using hz)
    -- Step 1.2.2: Conclude by injectivity of inversion.
    exact inv_injective hInv

  /-
  Step 2.A: Density near `0` if `g` is not meromorphic at `0`.

  We prove the following contrapositive statement:

  If there exist `w, ε, r` with `ε > 0` and `r > 0` such that `g` avoids `ball w ε` on the punctured
  ball `ball 0 r \ {0}`, then `g` must be meromorphic at `0`.

  Formal idea:
  - Define `φ(z) = (g z - w)⁻¹`.
  - On `ball 0 r \ {0}`, the denominator never vanishes (since otherwise `g z = w ∈ ball w ε`).
  - Therefore `φ` is holomorphic on the punctured ball.
  - Moreover, `‖φ z‖ ≤ 1/ε` on that punctured ball.
  - By the removable singularity theorem, `φ` extends holomorphically across `0`.
  - Then `g = w + (φ)⁻¹` is meromorphic at `0`.
  - Contradiction.
  -/

  have hg_hits_ball_near_zero_of_not_meromorphic :
      (¬ MeromorphicAt g 0) →
        ∀ (w : ℂ) (ε r : ℝ), 0 < ε → 0 < r →
          ∃ z : ℂ, z ≠ 0 ∧ z ∈ ball (0 : ℂ) r ∧ g z ∈ ball w ε := by
    intro hnot w ε r hε hr

    -- Step 2.A.1: Work by contradiction: assume there is no such `z`.
    by_contra hno
    have hAvoid : ∀ z : ℂ, z ≠ 0 → z ∈ ball (0 : ℂ) r → g z ∉ ball w ε := by
      intro z hz0 hzball hzmem
      exact hno ⟨z, hz0, hzball, hzmem⟩

    -- Step 2.A.2: Define `φ(z) = (g z - w)⁻¹`.
    let φ : ℂ → ℂ := fun z => (g z - w)⁻¹

    -- Step 2.A.3: Show `φ` is differentiable on `ball 0 r \ {0}`.
    have hφ_diff : DifferentiableOn ℂ φ (ball (0 : ℂ) r \ ({0} : Set ℂ)) := by
      -- Step 2.A.3.1: First show `g` is differentiable on that punctured ball.
      have hg_diff : DifferentiableOn ℂ g (ball (0 : ℂ) r \ ({0} : Set ℂ)) := by
        -- `g = f ∘ inv`, where `f` is differentiable on `univ` and `inv` is differentiable on `{z ≠ 0}`.
        have hfOn : DifferentiableOn ℂ f Set.univ := hf.differentiableOn
        have hinvOn : DifferentiableOn ℂ (fun z : ℂ => z⁻¹) {z : ℂ | z ≠ 0} :=
          (differentiableOn_inv : DifferentiableOn ℂ (fun z : ℂ => z⁻¹) {z : ℂ | z ≠ 0})
        have hinvOn' : DifferentiableOn ℂ (fun z : ℂ => z⁻¹) (ball (0 : ℂ) r \ ({0} : Set ℂ)) := by
          refine hinvOn.mono ?_
          intro z hz
          exact hz.2
        have hcomp := hfOn.comp hinvOn' (by
          intro z hz
          trivial)
        simpa [g, Function.comp] using hcomp

      -- Step 2.A.3.2: `z ↦ g z - w` is differentiable on the punctured ball.
      have hgw_diff : DifferentiableOn ℂ (fun z => g z - w) (ball (0 : ℂ) r \ ({0} : Set ℂ)) := by
        simpa using hg_diff.sub (differentiableOn_const (c := w) :
          DifferentiableOn ℂ (fun _ : ℂ => w) (ball (0 : ℂ) r \ ({0} : Set ℂ)))

      -- Step 2.A.3.3: On the punctured ball, `g z - w ≠ 0`.
      have hne : ∀ z ∈ ball (0 : ℂ) r \ ({0} : Set ℂ), g z - w ≠ 0 := by
        intro z hz
        have hz0 : z ≠ 0 := hz.2
        have hgz : g z ∉ ball w ε := hAvoid z hz0 hz.1
        intro hzw
        have : g z = w := by simpa [sub_eq_zero] using hzw
        have hwmem : w ∈ ball w ε := by
          -- the center is always in its own ball when the radius is positive
          simpa [Metric.mem_ball, Complex.dist_eq] using hε
        exact hgz (this ▸ hwmem)

      -- Step 2.A.3.4: Now invert the differentiable function.
      simpa [φ] using hgw_diff.inv hne

    -- Step 2.A.4: Show `φ` is bounded on the punctured ball.
    have hφ_bdd : BddAbove (norm ∘ φ '' (ball (0 : ℂ) r \ ({0} : Set ℂ))) := by
      refine ⟨(1 / ε : ℝ), ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      have hz0 : z ≠ 0 := hz.2
      have hgz : g z ∉ ball w ε := hAvoid z hz0 hz.1

      -- Step 2.A.4.1: From `g z ∉ ball w ε`, get `ε ≤ ‖g z - w‖`.
      have hdist : ε ≤ ‖g z - w‖ := by
        have : ¬ dist (g z) w < ε := by
          simpa [Metric.mem_ball] using hgz
        have : ¬ ‖g z - w‖ < ε := by
          simpa [Complex.dist_eq] using this
        exact le_of_not_gt this

      -- Step 2.A.4.2: Invert the inequality and rewrite via `norm_inv`.
      have : ‖(g z - w)⁻¹‖ ≤ (1 / ε : ℝ) := by
        have : (1 / ‖g z - w‖ : ℝ) ≤ 1 / ε := one_div_le_one_div_of_le hε hdist
        simpa [norm_inv, one_div] using this
      simpa [φ] using this

    -- Step 2.A.5: Apply removable singularity theorem to extend `φ` across `0`.
    have hball_nhds : ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := ball_mem_nhds _ hr
    have hφ_update_diff :
        DifferentiableOn ℂ (Function.update φ 0 (limUnder (𝓝[≠] 0) φ)) (ball (0 : ℂ) r) := by
      simpa using
        (Complex.differentiableOn_update_limUnder_of_bddAbove (f := φ) (s := ball (0 : ℂ) r)
          (c := (0 : ℂ)) hball_nhds hφ_diff hφ_bdd)

    -- Step 2.A.6: Turn this into meromorphicity of `φ` at `0` (value at the point is irrelevant).
    have hφ_mer : MeromorphicAt φ (0 : ℂ) := by
      have hφ_update_an : AnalyticAt ℂ (Function.update φ 0 (limUnder (𝓝[≠] 0) φ)) (0 : ℂ) :=
        hφ_update_diff.analyticAt hball_nhds
      have hφ_update_mer : MeromorphicAt (Function.update φ 0 (limUnder (𝓝[≠] 0) φ)) (0 : ℂ) :=
        hφ_update_an.meromorphicAt
      -- Remove the `update` using `MeromorphicAt.update_iff`.
      simpa using (MeromorphicAt.update_iff (f := φ) (z := (0 : ℂ)) (w := (0 : ℂ))
        (e := limUnder (𝓝[≠] 0) φ)).1 hφ_update_mer

    -- Step 2.A.7: From meromorphicity of `φ`, deduce meromorphicity of `g = w + (φ)⁻¹`.
    have hg_mer : MeromorphicAt g (0 : ℂ) := by
      have hw_mer : MeromorphicAt (fun _ : ℂ => w) (0 : ℂ) := MeromorphicAt.const w 0
      have hφinv_mer : MeromorphicAt (fun z => (φ z)⁻¹) (0 : ℂ) := hφ_mer.inv
      have hsum_mer : MeromorphicAt (fun z => w + (φ z)⁻¹) (0 : ℂ) := hw_mer.add hφinv_mer
      -- These agree on `𝓝[≠] 0`.
      refine hsum_mer.congr ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp [φ, g, sub_eq_add_neg]

    -- Step 2.A.8: Contradiction.
    exact hnot hg_mer

  /-
  Step 2.B: Prove `MeromorphicAt g 0` using density + open mapping + injectivity.
  -/

  have hg_meromorphic : MeromorphicAt g (0 : ℂ) := by
    by_contra hnot

    -- Step 2.B.1: Get the density property near 0.
    have hDense := hg_hits_ball_near_zero_of_not_meromorphic hnot

    -- Step 2.B.2: `g` is analytic at `1` because it is differentiable on `{z ≠ 0}`, a neighborhood of `1`.
    have hg_an1 : AnalyticAt ℂ g (1 : ℂ) := by
      have hgDiff : DifferentiableOn ℂ g {z : ℂ | z ≠ 0} := by
        have hfOn : DifferentiableOn ℂ f Set.univ := hf.differentiableOn
        have hinvOn : DifferentiableOn ℂ (fun z : ℂ => z⁻¹) {z : ℂ | z ≠ 0} :=
          (differentiableOn_inv : DifferentiableOn ℂ (fun z : ℂ => z⁻¹) {z : ℂ | z ≠ 0})
        have hcomp := hfOn.comp hinvOn (by
          intro z hz
          trivial)
        simpa [g, Function.comp] using hcomp
      have hnhds : ({z : ℂ | z ≠ 0} : Set ℂ) ∈ 𝓝 (1 : ℂ) :=
        (isOpen_ne).mem_nhds (by simp)
      exact hgDiff.analyticAt hnhds

    -- Step 2.B.3: Use open mapping theorem locally at 1.
    have h_open : 𝓝 (g (1 : ℂ)) ≤ Filter.map g (𝓝 (1 : ℂ)) := by
      rcases hg_an1.eventually_constant_or_nhds_le_map_nhds with hconst | hnhds
      · -- If `g` were locally constant at `1`, injectivity would fail.
        rcases (Metric.eventually_nhds_iff.1 hconst) with ⟨δ, hδpos, hδ⟩
        let y : ℂ := (1 : ℂ) + (δ / 2 : ℝ)
        have hy_dist : dist y (1 : ℂ) < δ := by
          have hdist : dist y (1 : ℂ) = |δ| / 2 := by
            simp [y]
          have hlt : |δ| / 2 < δ := by
            simpa [abs_of_pos hδpos] using (half_lt_self hδpos)
          simpa [hdist] using hlt
        have hgy : g y = g (1 : ℂ) := hδ hy_dist
        have hy_ne : y ≠ (1 : ℂ) := by
          intro hEq
          -- Step 2.B.3.1: If `y = 1`, then (subtracting `1`) we get `(δ/2) = 0`.
          have hδhalf_eq : (δ / 2 : ℝ) = 0 := by
            have := congrArg (fun z : ℂ => z - 1) hEq
            simpa [y] using this
          -- Step 2.B.3.2: But `δ/2 > 0` since `δ > 0`.
          have hδhalf_pos : (0 : ℝ) < δ / 2 := by nlinarith [hδpos]
          -- Step 2.B.3.3: Contradiction.
          exact (ne_of_gt hδhalf_pos) hδhalf_eq
        exact (hy_ne (hg_inj hgy)).elim
      · exact hnhds

    -- Step 2.B.4: `g '' ball 1 (1/4)` is a neighborhood of `g 1`.
    have himage_nhds : g '' ball (1 : ℂ) (1 / 4 : ℝ) ∈ 𝓝 (g (1 : ℂ)) := by
      have hU : ball (1 : ℂ) (1 / 4 : ℝ) ∈ 𝓝 (1 : ℂ) := ball_mem_nhds _ (by norm_num)
      have : g '' ball (1 : ℂ) (1 / 4 : ℝ) ∈ Filter.map g (𝓝 (1 : ℂ)) :=
        Filter.image_mem_map hU
      exact h_open this

    -- Step 2.B.5: Extract `δ > 0` with `ball (g 1) δ ⊆ g '' ball 1 (1/4)`.
    rcases Metric.mem_nhds_iff.1 himage_nhds with ⟨δ, hδpos, hδsubset⟩

    -- Step 2.B.6: Use Step 2.A with `w = g 1`, `ε = δ`, `r = 1/4`.
    obtain ⟨z, hz0, hzball0, hgz⟩ :=
      hDense (g (1 : ℂ)) δ (1 / 4 : ℝ) (by simpa using hδpos) (by norm_num)

    -- Step 2.B.7: `g z ∈ ball (g 1) δ ⊆ g '' ball 1 (1/4)` so pick `y` with `g y = g z`.
    have hz_image : g z ∈ g '' ball (1 : ℂ) (1 / 4 : ℝ) := hδsubset hgz
    rcases hz_image with ⟨y, hyball1, hyEq⟩
    have hgyEq : g y = g z := by simpa using hyEq

    -- Step 2.B.8: Show `y ≠ z` because the two balls are disjoint.
    have hy_ne_z : y ≠ z := by
      have hdisj : Disjoint (ball (0 : ℂ) (1 / 4 : ℝ)) (ball (1 : ℂ) (1 / 4 : ℝ)) := by
        refine Metric.ball_disjoint_ball ?_
        have : (1 / 4 : ℝ) + (1 / 4 : ℝ) ≤ (1 : ℝ) := by norm_num
        simpa [Complex.dist_eq] using this
      intro hEq
      have : y ∈ ball (0 : ℂ) (1 / 4 : ℝ) := by simpa [hEq] using hzball0
      exact hdisj.le_bot ⟨this, hyball1⟩

    -- Step 2.B.9: Contradict injectivity.
    exact hy_ne_z (hg_inj hgyEq)

  -- Keep the result for later.
  have hg_mer : MeromorphicAt g (0 : ℂ) := hg_meromorphic

  /-
  Step 3: From `MeromorphicAt g 0` to a polynomial growth bound for `f`.
  -/

  -- Step 3.1: Unpack the definition of meromorphicity.
  rcases hg_mer with ⟨N, hN_an⟩

  -- Step 3.2: Define `h(z) = z^N * g z`, which is analytic at `0`.
  let h : ℂ → ℂ := fun z => z ^ N * g z
  have h_an : AnalyticAt ℂ h (0 : ℂ) := by
    -- `MeromorphicAt` gives analyticity of `(z - 0)^N • g z`; simplify.
    simpa [h, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hN_an
  have h_cont : ContinuousAt h (0 : ℂ) := h_an.continuousAt

  -- Step 3.3: Local boundedness of `h` near `0`.
  obtain ⟨r, hrpos, C, hCball⟩ :
      ∃ r > (0 : ℝ), ∃ C : ℝ, ∀ z ∈ ball (0 : ℂ) r, ‖h z‖ ≤ C := by
    have hnorm_cont : ContinuousAt (fun z : ℂ => ‖h z‖) (0 : ℂ) := by
      -- Step 3.3.1: `z ↦ ‖z‖` is continuous, so composing with the continuous-at map `h` stays continuous-at.
      simpa [Function.comp] using
        (ContinuousAt.comp (f := h) (x := (0 : ℂ)) (g := fun z : ℂ => ‖z‖)
          (continuous_norm.continuousAt) h_cont)
    have hnhds : Set.Iio (‖h (0 : ℂ)‖ + 1) ∈ 𝓝 (‖h (0 : ℂ)‖) :=
      Iio_mem_nhds (by linarith)
    have : {z : ℂ | ‖h z‖ < ‖h (0 : ℂ)‖ + 1} ∈ 𝓝 (0 : ℂ) :=
      (hnorm_cont.tendsto) hnhds
    rcases Metric.mem_nhds_iff.1 this with ⟨r, hrpos, hrball⟩
    refine ⟨r, hrpos, ‖h (0 : ℂ)‖ + 1, ?_⟩
    intro z hz
    exact le_of_lt (hrball hz)

  -- Step 3.4: Translate local boundedness of `h` into polynomial growth of `f`.
  let R0 : ℝ := 2 / r
  have h_growth : ∀ w : ℂ, R0 ≤ ‖w‖ → ‖f w‖ ≤ C * ‖w‖ ^ N := by
    intro w hw
    -- Step 3.4.1: `w ≠ 0` since `R0 > 0`.
    have hR0pos : 0 < R0 := by
      exact div_pos (by norm_num) hrpos
    have hw0 : w ≠ 0 := by
      intro hw0
      have : 0 < ‖w‖ := lt_of_lt_of_le hR0pos hw
      simpa [hw0] using this.ne'

    -- Step 3.4.2: Show `w⁻¹ ∈ ball 0 r` by the estimate `‖w⁻¹‖ = 1/‖w‖`.
    have hw_inv : w⁻¹ ∈ ball (0 : ℂ) r := by
      have hR0pos' : 0 < (2 / r : ℝ) := div_pos (by norm_num) hrpos
      have hInv : (1 / ‖w‖ : ℝ) ≤ 1 / (2 / r : ℝ) :=
        one_div_le_one_div_of_le hR0pos' hw
      have hInv' : (1 / ‖w‖ : ℝ) ≤ r / 2 := by
        have : (1 / (2 / r : ℝ)) = r / 2 := by
          field_simp [hrpos.ne']
        simpa [this] using hInv
      have : (1 / ‖w‖ : ℝ) < r := lt_of_le_of_lt hInv' (by nlinarith)
      have hnorm_inv : ‖w⁻¹‖ < r := by
        simpa [norm_inv, one_div] using this
      simpa [Metric.mem_ball, Complex.dist_eq] using hnorm_inv

    -- Step 3.4.3: Apply the local bound to `h (w⁻¹)`.
    have hbound : ‖h (w⁻¹)‖ ≤ C := hCball (w⁻¹) hw_inv

    -- Step 3.4.4: Rewrite `h(w⁻¹) = (w⁻¹)^N * f w`.
    have hbound' : ‖(w⁻¹) ^ N * f w‖ ≤ C := by
      -- `h(w⁻¹) = (w⁻¹)^N * g(w⁻¹) = (w⁻¹)^N * f w`.
      simpa [h, g] using hbound

    -- Step 3.4.5: Convert to `‖f w‖ ≤ C * ‖w‖^N`.
    have hmul : (‖w‖ ^ N) * ‖(w⁻¹) ^ N * f w‖ ≤ (‖w‖ ^ N) * C :=
      mul_le_mul_of_nonneg_left hbound' (by positivity)
    have hw_norm_ne : ‖w‖ ≠ 0 := by
      simpa [norm_eq_zero] using hw0
    have hw_pow_ne : ‖w‖ ^ N ≠ 0 := pow_ne_zero N hw_norm_ne
    have hleft : (‖w‖ ^ N) * ‖(w⁻¹) ^ N * f w‖ = ‖f w‖ := by
      calc
        (‖w‖ ^ N) * ‖(w⁻¹) ^ N * f w‖
            = (‖w‖ ^ N) * ((‖w‖ ^ N)⁻¹ * ‖f w‖) := by
                simp [norm_pow, norm_inv, hw0, mul_comm]
        _ = ((‖w‖ ^ N) * (‖w‖ ^ N)⁻¹) * ‖f w‖ := by ring
        _ = ‖f w‖ := by simp [hw_pow_ne]
    calc
      ‖f w‖ = (‖w‖ ^ N) * ‖(w⁻¹) ^ N * f w‖ := by simpa using hleft.symm
      _ ≤ (‖w‖ ^ N) * C := hmul
      _ = C * ‖w‖ ^ N := by ring

  /-
  Step 4: Use polynomial growth to prove `f` is a polynomial.
  -/

  -- Step 4.1: Fix a base radius `1` and define the Cauchy power series at `0`.
  let Rbase : NNReal := 1
  have hRbase : (0 : NNReal) < Rbase := by
    simp [Rbase]
  let pSeries : FormalMultilinearSeries ℂ ℂ ℂ := cauchyPowerSeries f (0 : ℂ) (↑Rbase : ℝ)

  -- Step 4.2: This series represents `f` globally (radius `⊤`).
  have hps_base_ball : HasFPowerSeriesOnBall f pSeries (0 : ℂ) (⊤ : ENNReal) := by
    simpa [pSeries] using (hf.hasFPowerSeriesOnBall (0 : ℂ) (R := Rbase) hRbase)
  have hps_base_at : HasFPowerSeriesAt f pSeries (0 : ℂ) := hps_base_ball.hasFPowerSeriesAt

  -- Step 4.3: Prove coefficients beyond `N` are zero.
  have hcoeff_zero : ∀ n : ℕ, N < n → pSeries n = 0 := by
    intro n hn
    -- We show `‖pSeries n‖ = 0`.
    apply norm_eq_zero.mp
    apply le_antisymm
    · -- Show `‖pSeries n‖ ≤ 0` using `le_of_forall_pos_le_add`.
      have hnorm_le_eps : ∀ ε : ℝ, 0 < ε → ‖pSeries n‖ ≤ ε := by
        intro ε hε

        -- Step 4.3.1: Let `m = n - N` (positive).
        let m : ℕ := n - N
        have hmpos : 0 < m := Nat.sub_pos_of_lt hn
        have hm_ne : m ≠ 0 := Nat.ne_of_gt hmpos

        -- Step 4.3.2: `C / R^m → 0` as `R → ∞`.
        have htendsto : Tendsto (fun R : ℝ => C / R ^ m) atTop (𝓝 (0 : ℝ)) := by
          have hpow : Tendsto (fun R : ℝ => R ^ m) atTop atTop :=
            Filter.tendsto_pow_atTop hm_ne
          have hinv : Tendsto (fun R : ℝ => (R ^ m)⁻¹) atTop (𝓝 (0 : ℝ)) :=
            tendsto_inv_atTop_zero.comp hpow
          simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinv)

        -- Step 4.3.3: Choose `R₁` such that for all `R ≥ R₁`, `C / R^m < ε`.
        have hEvent : ∀ᶠ R : ℝ in atTop, C / R ^ m < ε :=
          htendsto.eventually (Iio_mem_nhds hε)
        rcases (Filter.eventually_atTop.1 hEvent) with ⟨R₁, hR₁⟩

        -- Step 4.3.4: Pick `R = max R₁ (max R0 1)`.
        let R : ℝ := max R₁ (max R0 1)
        have hR_ge_R0 : R0 ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
        have hRpos : 0 < R :=
          lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
            (le_trans (le_max_right _ _) (le_max_right _ _))
        have hR_lt : C / R ^ m < ε := hR₁ R (le_max_left _ _)

        -- Step 4.3.5: Compare `pSeries` with `cauchyPowerSeries f 0 R` using uniqueness.
        let Rnn : NNReal := ⟨R, le_of_lt hRpos⟩
        have hRnn_pos : (0 : NNReal) < Rnn := by simpa [Rnn] using hRpos
        have hpsR_at : HasFPowerSeriesAt f (cauchyPowerSeries f (0 : ℂ) (↑Rnn : ℝ)) (0 : ℂ) :=
          (hf.hasFPowerSeriesOnBall (0 : ℂ) (R := Rnn) hRnn_pos).hasFPowerSeriesAt
        have hp_eq : pSeries = cauchyPowerSeries f (0 : ℂ) (↑Rnn : ℝ) :=
          HasFPowerSeriesAt.eq_formalMultilinearSeries hps_base_at hpsR_at

        -- Step 4.3.6: Rewrite the coefficient at index `n`.
        have hCoeffEq : pSeries n = cauchyPowerSeries f (0 : ℂ) R n := by
          -- `↑Rnn = R` by definition.
          simpa [Rnn] using congrArg (fun p => p n) hp_eq
        have hCoeffEq_norm : ‖pSeries n‖ = ‖cauchyPowerSeries f (0 : ℂ) R n‖ := by
          simp [hCoeffEq]

        -- Step 4.3.7: Apply the Cauchy coefficient bound.
        have hCauchy :
            ‖cauchyPowerSeries f (0 : ℂ) R n‖ ≤
              ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap (0 : ℂ) R θ)‖) *
                |R|⁻¹ ^ n :=
          norm_cauchyPowerSeries_le (f := f) (c := (0 : ℂ)) (R := R) (n := n)

        -- Step 4.3.8: Bound the average integral using the growth bound.
        have hCircleBound : ∀ θ : ℝ, ‖f (circleMap (0 : ℂ) R θ)‖ ≤ C * |R| ^ N := by
          intro θ
          have hnorm : ‖circleMap (0 : ℂ) R θ‖ = |R| := by
            simp
          have : R0 ≤ ‖circleMap (0 : ℂ) R θ‖ := by
            have : R0 ≤ |R| := by
              simpa [abs_of_pos hRpos] using hR_ge_R0
            simpa [hnorm] using this
          simpa [hnorm] using (h_growth (circleMap (0 : ℂ) R θ) this)

        have hAvg :
            ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap (0 : ℂ) R θ)‖) ≤
              C * |R| ^ N := by
          have hab : (0 : ℝ) ≤ 2 * Real.pi := by
            have : (0 : ℝ) ≤ Real.pi := by positivity
            linarith
          have hInt1 : IntervalIntegrable (fun θ : ℝ => ‖f (circleMap (0 : ℂ) R θ)‖) volume (0 : ℝ)
              (2 * Real.pi) := by
            have hcont : Continuous fun θ : ℝ => ‖f (circleMap (0 : ℂ) R θ)‖ :=
              continuous_norm.comp (hf.continuous.comp (continuous_circleMap (0 : ℂ) R))
            exact hcont.intervalIntegrable _ _
          have hInt2 : IntervalIntegrable (fun _θ : ℝ => C * |R| ^ N) volume (0 : ℝ) (2 * Real.pi) := by
            simp
          have hInt :
              (∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap (0 : ℂ) R θ)‖)
                ≤ ∫ θ in (0 : ℝ)..2 * Real.pi, C * |R| ^ N := by
            exact intervalIntegral.integral_mono (μ := volume) hab hInt1 hInt2
              (by intro θ; exact hCircleBound θ)
          have hpos : 0 ≤ (2 * Real.pi)⁻¹ := by
            have : 0 ≤ (2 * Real.pi : ℝ) := by
              have : (0 : ℝ) ≤ Real.pi := by positivity
              linarith
            exact inv_nonneg.2 this
          have hMul := mul_le_mul_of_nonneg_left hInt hpos
          have hInt_const :
              (∫ _θ in (0 : ℝ)..2 * Real.pi, C * |R| ^ N) = (2 * Real.pi) * (C * |R| ^ N) := by
            -- Step 4.3.8.1: Interval integral of a constant is `(b - a) * c`; here `a = 0`.
            -- The remaining goal is a commutativity/associativity rearrangement.
            simp [intervalIntegral.integral_const, mul_assoc, mul_left_comm, mul_comm]
          have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
          calc
            (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap (0 : ℂ) R θ)‖)
                ≤ (2 * Real.pi)⁻¹ * (∫ _θ in (0 : ℝ)..2 * Real.pi, C * |R| ^ N) := hMul
            _ = (2 * Real.pi)⁻¹ * ((2 * Real.pi) * (C * |R| ^ N)) := by simp [hInt_const]
            _ = C * |R| ^ N := by field_simp [hpi]

        -- Step 4.3.9: Combine bounds.
        have hCoeff1 :
            ‖cauchyPowerSeries f (0 : ℂ) R n‖ ≤ (C * |R| ^ N) * |R|⁻¹ ^ n := by
          exact le_trans hCauchy (by gcongr)

        -- Step 4.3.10: Rewrite the RHS as `C / R^(n-N)` (using `R > 0`).
        have hR0 : R ≠ 0 := ne_of_gt hRpos
        have hNle : N ≤ n := le_of_lt hn
        have habs : |R| = R := abs_of_pos hRpos
        have hAlg : (C * R ^ N) * (R⁻¹) ^ n = C / R ^ (n - N) := by
          have hn' : N + (n - N) = n := Nat.add_sub_of_le hNle
          calc
            C * R ^ N * (R⁻¹) ^ n
                = C * R ^ N * ((R⁻¹) ^ (N + (n - N))) := by simp [hn']
            _ = C * R ^ N * ((R⁻¹) ^ N * (R⁻¹) ^ (n - N)) := by
                  simp [pow_add, mul_assoc]
            _ = C * (R ^ N * (R⁻¹) ^ N) * (R⁻¹) ^ (n - N) := by
                  ring_nf
            _ = C * ((R * R⁻¹) ^ N) * (R⁻¹) ^ (n - N) := by
                  simp [mul_pow]
            _ = C * (1 ^ N) * (R⁻¹) ^ (n - N) := by
                  simp [mul_inv_cancel₀ hR0]
            _ = C * (R⁻¹) ^ (n - N) := by simp
            _ = C * (R ^ (n - N))⁻¹ := by simp [inv_pow]
            _ = C / R ^ (n - N) := by simp [div_eq_mul_inv]

        have hCoeff2 : ‖cauchyPowerSeries f (0 : ℂ) R n‖ ≤ C / R ^ (n - N) := by
          -- Replace `|R|` by `R` and then use `hAlg`.
          have : (C * |R| ^ N) * |R|⁻¹ ^ n = C / R ^ (n - N) := by
            simpa [habs] using hAlg
          -- Step 4.3.10.1: Use `≤`-transitivity and view the equality as an inequality.
          exact le_trans hCoeff1 (le_of_eq this)

        -- Step 4.3.11: Convert back to `‖pSeries n‖`.
        have hCoeff3 : ‖pSeries n‖ ≤ C / R ^ m := by
          -- `m = n - N` by definition.
          have hm : m = n - N := by rfl
          simpa [hCoeffEq_norm, hm] using hCoeff2

        -- Step 4.3.12: Now use the chosen `R` making `C / R^m < ε`.
        have hm : m = n - N := by rfl
        have : C / R ^ m < ε := by simpa [hm, R] using hR_lt
        exact le_of_lt (lt_of_le_of_lt hCoeff3 this)

      have : ∀ ε : ℝ, 0 < ε → ‖pSeries n‖ ≤ 0 + ε := by
        intro ε hε
        simpa using (hnorm_le_eps ε hε)
      exact le_of_forall_pos_le_add this
    · exact norm_nonneg _

  -- Step 4.4: Build an explicit polynomial from the coefficients.

  -- Step 4.4.1: Define scalar coefficients `aCoeff k`.
  let aCoeff : ℕ → ℂ := fun k => pSeries k (fun _ : Fin k => (1 : ℂ))

  -- Step 4.4.2: In one variable, `pSeries k (z,z,...,z) = z^k * aCoeff k`.
  have hterm : ∀ k : ℕ, ∀ z : ℂ, pSeries k (fun _ : Fin k => z) = (z ^ k) * aCoeff k := by
    intro k z
    have h1 := (pSeries k).map_smul_univ (c := fun _ : Fin k => z) (m := fun _ : Fin k => (1 : ℂ))
    simp [aCoeff]

  -- Step 4.4.3: Define the polynomial `P(z) = ∑_{k=0}^N aCoeff k * z^k`.
  let P : ℂ[X] :=
    ∑ k ∈ Finset.range (N + 1), Polynomial.C (aCoeff k) * Polynomial.X ^ k

  -- Step 4.4.4: Prove `f z = P.eval z` for all `z`.
  have hP_eval : ∀ z : ℂ, f z = P.eval z := by
    intro z

    -- Step 4.4.4.1: Use the global power series representation.
    have hzBall : z ∈ Metric.eball (0 : ℂ) (⊤ : ENNReal) := edist_lt_top z 0
    have hSum : HasSum (fun n : ℕ => pSeries n (fun _ : Fin n => z)) (f z) := by
      simpa [zero_add] using hps_base_ball.hasSum (y := z) hzBall
    have htsum : (∑' n : ℕ, pSeries n (fun _ : Fin n => z)) = f z := hSum.tsum_eq

    -- Step 4.4.4.2: Reduce the infinite sum to a finite sum using `hcoeff_zero`.
    have hzero : ∀ n : ℕ, N < n → (pSeries n) (fun _ : Fin n => z) = 0 := by
      intro n hn
      simpa using congrArg (fun T => T (fun _ : Fin n => z)) (hcoeff_zero n hn)
    have hzero' : ∀ n ∉ Finset.range (N + 1), (pSeries n) (fun _ : Fin n => z) = 0 := by
      intro n hnmem
      have hn' : N < n := by
        have hle : N + 1 ≤ n :=
          Nat.le_of_not_gt (by
            intro hlt
            exact hnmem (Finset.mem_range.2 hlt))
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self N) hle
      exact hzero n hn'
    have htsum2 :
        (∑' n : ℕ, pSeries n (fun _ : Fin n => z)) =
          ∑ n ∈ Finset.range (N + 1), pSeries n (fun _ : Fin n => z) := by
      simpa using (tsum_eq_sum (s := Finset.range (N + 1)) hzero')

    have hFinite : f z = ∑ n ∈ Finset.range (N + 1), pSeries n (fun _ : Fin n => z) := by
      calc
        f z = ∑' n : ℕ, pSeries n (fun _ : Fin n => z) := by simpa using htsum.symm
        _ = ∑ n ∈ Finset.range (N + 1), pSeries n (fun _ : Fin n => z) := htsum2

    -- Step 4.4.4.3: Rewrite each term using `hterm`.
    have hFinite' : f z = ∑ n ∈ Finset.range (N + 1), (z ^ n) * aCoeff n := by
      simpa [hterm] using hFinite
    have hFinite'' : f z = ∑ n ∈ Finset.range (N + 1), aCoeff n * z ^ n := by
      -- commute each term
      refine hFinite'.trans ?_
      refine Finset.sum_congr rfl ?_
      intro n hn
      ring

    -- Step 4.4.4.4: Evaluate the polynomial and match the finite sum.
    have hPz : P.eval z = ∑ n ∈ Finset.range (N + 1), aCoeff n * z ^ n := by
      simp [P, Polynomial.eval_finset_sum]
    simpa [hPz] using hFinite''

  -- Step 4.5: Turn pointwise equality into a function equality.
  have hf_poly : f = fun z : ℂ => P.eval z := by
    funext z
    exact hP_eval z

  /-
  Step 5: An injective complex polynomial has degree ≤ 1.
  -/

  -- Step 5.1: Transfer injectivity from `f` to `P.eval`.
  have hP_inj : Function.Injective (fun z : ℂ => P.eval z) := by
    intro z₁ z₂ hz
    apply hf_inj
    simpa [hf_poly] using hz

  -- Step 5.2: Prove `P.natDegree ≤ 1` by contradiction.
  have hdeg : P.natDegree ≤ 1 := by
    by_contra hdeg'
    have hdeg2 : 2 ≤ P.natDegree := by
      have : 1 < P.natDegree := Nat.lt_of_not_ge hdeg'
      simpa using (Nat.succ_le_iff.2 this)

    -- Step 5.2.1: Define `D = P - C (P.eval 0)`.
    let D : ℂ[X] := P - Polynomial.C (P.eval 0)
    have hD0 : D.eval (0 : ℂ) = 0 := by simp [D]

    -- Step 5.2.2: Show `D ≠ 0`.
    have hD_ne : D ≠ 0 := by
      intro hD
      have hPconst0 : P = Polynomial.C (P.eval 0) := sub_eq_zero.mp hD
      -- Introduce a fresh constant to avoid rewriting loops.
      let c : ℂ := P.eval 0
      have hPconst : P = Polynomial.C c := by simpa [c] using hPconst0
      have hEq : P.eval (0 : ℂ) = P.eval (1 : ℂ) := by
        calc
          P.eval (0 : ℂ) = (Polynomial.C c).eval (0 : ℂ) := by simp [hPconst]
          _ = c := by simp
          _ = (Polynomial.C c).eval (1 : ℂ) := by simp
          _ = P.eval (1 : ℂ) := by simp [hPconst]
      have : (0 : ℂ) = 1 := hP_inj hEq
      simp at this

    -- Step 5.2.3: Factor `D` at the root `0` using `rootMultiplicity`.
    obtain ⟨Q, hDQ, hXnot⟩ := D.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hD_ne (0 : ℂ)
    have hDQ' : D = Polynomial.X ^ D.rootMultiplicity (0 : ℂ) * Q := by
      -- Step 5.2.3.1: The factorization lemma uses `(X - C 0)`; simplify it to `X`.
      simpa using hDQ
    have hXnot' : ¬ (Polynomial.X : ℂ[X]) ∣ Q := by
      simpa using hXnot

    -- Step 5.2.4: Split into `Q` constant vs nonconstant.
    by_cases hQdeg : Q.degree ≤ 0
    · -- Case 1: `Q` is constant.
      have hQconst : Q = Polynomial.C (Q.coeff 0) := (Polynomial.degree_le_zero_iff).1 hQdeg
      have hDmono : D = Polynomial.C (Q.coeff 0) * Polynomial.X ^ D.rootMultiplicity (0 : ℂ) := by
        -- Step 5.2.4.0: Rewrite `D` using the factorization and the fact that `Q` is constant.
        calc
          D = Polynomial.X ^ D.rootMultiplicity (0 : ℂ) * Q := hDQ'
          _ = Polynomial.X ^ D.rootMultiplicity (0 : ℂ) * Polynomial.C (Q.coeff 0) := by
                -- Step 5.2.4.0.1: Replace `Q` by the corresponding constant polynomial.
                -- We use `congrArg` to rewrite *only* the right factor `Q` (and not the `Q` hidden
                -- inside `Q.coeff 0`, which would create definitional mismatches).
                simpa using
                  congrArg (fun T : ℂ[X] => (Polynomial.X : ℂ[X]) ^ D.rootMultiplicity (0 : ℂ) * T) hQconst
          _ = Polynomial.C (Q.coeff 0) * Polynomial.X ^ D.rootMultiplicity (0 : ℂ) := by
                -- Step 5.2.4.0.2: Commute the two factors once (avoid `simp [mul_comm]`, which loops).
                simp

      -- Step 5.2.4.1: The scalar coefficient is nonzero.
      have hCoeff_ne : Q.coeff 0 ≠ 0 := by
        intro h0
        -- Step 5.2.4.1.1: If the scalar were `0`, then the whole monomial polynomial would be `0`.
        have hD_zero : D = 0 := by
          calc
            D = Polynomial.C (Q.coeff 0) * Polynomial.X ^ D.rootMultiplicity (0 : ℂ) := hDmono
            _ = 0 := by simp [h0]
        -- Step 5.2.4.1.2: Contradiction with `D ≠ 0`.
        exact hD_ne hD_zero

      -- Step 5.2.4.2: `D.natDegree = k` where `k = rootMultiplicity 0 D`.
      have hD_nat : D.natDegree = D.rootMultiplicity (0 : ℂ) := by
        -- `natDegree (C a * X^k) = k` when `a ≠ 0`.
        -- IMPORTANT: we *freeze* the exponent `k = rootMultiplicity 0 D` into a separate name, so that
        -- rewriting `D` does not accidentally rewrite inside `D.rootMultiplicity`.
        let k : ℕ := D.rootMultiplicity (0 : ℂ)
        have hk : D.rootMultiplicity (0 : ℂ) = k := by rfl
        have hDmono' : D = Polynomial.C (Q.coeff 0) * Polynomial.X ^ k := by
          simpa [k] using hDmono

        -- Step 5.2.4.2.1: Compute `D.natDegree` from the monomial form.
        have hNat : D.natDegree = k := by
          rw [hDmono']
          simpa using (Polynomial.natDegree_C_mul_X_pow (R := ℂ) k (Q.coeff 0) hCoeff_ne)

        -- Step 5.2.4.2.2: Replace `k` back by its definition.
        calc
          D.natDegree = k := hNat
          _ = D.rootMultiplicity (0 : ℂ) := hk.symm

      -- Step 5.2.4.3: Show `D.natDegree = P.natDegree` (subtracting a constant does not change natDegree).
      have hD_eq : D.natDegree = P.natDegree := by
        have hlt : (-Polynomial.C (P.eval 0) : ℂ[X]).natDegree < P.natDegree := by
          have : (0 : ℕ) < P.natDegree := lt_of_lt_of_le (by norm_num) hdeg2
          simpa using this
        simpa [D, sub_eq_add_neg] using
          (Polynomial.natDegree_add_eq_left_of_natDegree_lt (p := P) (q := -Polynomial.C (P.eval 0)) hlt)

      -- Therefore `k ≥ 2`.
      have hk_ge2 : 2 ≤ D.rootMultiplicity (0 : ℂ) := by
        have : 2 ≤ D.natDegree := by
          simpa [hD_eq] using hdeg2
        simpa [hD_nat] using this
      have hk_gt1 : 1 < D.rootMultiplicity (0 : ℂ) :=
        Nat.lt_of_lt_of_le (by decide : 1 < 2) hk_ge2

      -- Step 5.2.4.4: Choose a nontrivial `k`-th root of unity.
      obtain ⟨ζ, hζpow, hζne⟩ : ∃ ζ : ℂ, ζ ^ D.rootMultiplicity (0 : ℂ) = 1 ∧ ζ ≠ 1 := by
        let ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * I / (D.rootMultiplicity (0 : ℂ) : ℂ))
        have hk0 : D.rootMultiplicity (0 : ℂ) ≠ 0 :=
          Nat.ne_of_gt (lt_trans (by decide : 0 < 1) hk_gt1)
        have hprim : IsPrimitiveRoot ζ (D.rootMultiplicity (0 : ℂ)) := by
          simpa [ζ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
            (Complex.isPrimitiveRoot_exp (D.rootMultiplicity (0 : ℂ)) hk0)
        refine ⟨ζ, hprim.pow_eq_one, hprim.ne_one hk_gt1⟩

      -- Step 5.2.4.5: Show `P.eval ζ = P.eval 1`.
      have hP_eq_from_D : ∀ z : ℂ, P.eval z = D.eval z + P.eval 0 := by
        intro z
        simp [D, sub_eq_add_neg, add_left_comm, add_comm]
      have hD_eval : ∀ z : ℂ, D.eval z = (Q.coeff 0) * z ^ D.rootMultiplicity (0 : ℂ) := by
        intro z
        -- Step 5.2.4.5.1: Freeze `k = rootMultiplicity 0 D` to avoid rewriting inside it.
        let k : ℕ := D.rootMultiplicity (0 : ℂ)
        have hk : D.rootMultiplicity (0 : ℂ) = k := by rfl
        have hDmono' : D = Polynomial.C (Q.coeff 0) * Polynomial.X ^ k := by
          simpa [k] using hDmono

        -- Step 5.2.4.5.2: Evaluate the monomial polynomial.
        calc
          D.eval z = (Polynomial.C (Q.coeff 0) * Polynomial.X ^ k).eval z := by
                simp [hDmono']
          _ = (Q.coeff 0) * z ^ k := by
                simp [Polynomial.eval_mul, Polynomial.eval_pow]
          _ = (Q.coeff 0) * z ^ D.rootMultiplicity (0 : ℂ) := by
                -- Step 5.2.4.5.3: Unfreeze the exponent.
                rw [hk]
      have hEq : P.eval ζ = P.eval (1 : ℂ) := by
        calc
          P.eval ζ = D.eval ζ + P.eval 0 := hP_eq_from_D ζ
          _ = (Q.coeff 0) * ζ ^ D.rootMultiplicity (0 : ℂ) + P.eval 0 := by simp [hD_eval]
          _ = (Q.coeff 0) * (1 : ℂ) + P.eval 0 := by simp [hζpow]
          _ = (Q.coeff 0) * (1 : ℂ) ^ D.rootMultiplicity (0 : ℂ) + P.eval 0 := by simp
          _ = D.eval (1 : ℂ) + P.eval 0 := by simp [hD_eval]
          _ = P.eval (1 : ℂ) := (hP_eq_from_D (1 : ℂ)).symm

      -- Step 5.2.4.6: Contradict injectivity.
      have : ζ = (1 : ℂ) := hP_inj hEq
      exact hζne this

    · -- Case 2: `Q` is nonconstant, hence it has a (nonzero) root.
      have hQpos : 0 < Q.degree := lt_of_not_ge hQdeg
      obtain ⟨z, hz⟩ := Complex.exists_root hQpos
      have hz_eval : Q.eval z = 0 := hz

      -- `z ≠ 0` because `X ∤ Q`.
      have hz_ne0 : z ≠ (0 : ℂ) := by
        intro hz0
        have hroot0 : Q.IsRoot (0 : ℂ) := by
          simpa [hz0] using hz_eval
        have hX : (Polynomial.X : ℂ[X]) ∣ Q := by
          -- `X ∣ Q` iff `IsRoot Q 0`.
          simpa [Polynomial.dvd_iff_isRoot] using
            (show (Polynomial.X - Polynomial.C (0 : ℂ)) ∣ Q from (Polynomial.dvd_iff_isRoot).2 hroot0)
        exact hXnot' hX

      -- From the factorization, `D.eval z = 0`.
      have hDz : D.eval z = 0 := by
        -- Step 5.2.4.6.1: Rewrite `D` using the factorization, then evaluate.
        rw [hDQ']
        simp [hz_eval, Polynomial.eval_mul, Polynomial.eval_pow]

      -- Therefore `P.eval z = P.eval 0`.
      have hPz : P.eval z = P.eval 0 := by
        have : D.eval z = P.eval z - P.eval 0 := by simp [D]
        have : P.eval z - P.eval 0 = 0 := by simpa [this] using hDz
        exact sub_eq_zero.mp this

      -- Injectivity gives `z = 0`, contradiction.
      exact hz_ne0 (hP_inj hPz)

  /-
  Step 6: Extract `a, b` from the degree ≤ 1 polynomial and conclude.
  -/

  rcases P.exists_eq_X_add_C_of_natDegree_le_one hdeg with ⟨a, b, hPform⟩
  refine ⟨a, b, ?_, ?_⟩
  · -- Step 6.1: Show `f(z) = a*z + b`.
    have hf_aff : ∀ z : ℂ, f z = a * z + b := by
      intro z
      calc
        f z = P.eval z := hP_eval z
        _ = (Polynomial.C a * Polynomial.X + Polynomial.C b).eval z := by
              simp [hPform]
        _ = a * z + b := by
              simp
    -- Turn pointwise equality into a function equality.
    funext z
    exact hf_aff z
  · -- Step 6.2: Show `a ≠ 0` (otherwise `f` would be constant).
    intro ha0
    have hf_aff : f = fun z : ℂ => a * z + b := by
      -- Reuse the computation from the previous step.
      funext z
      calc
        f z = P.eval z := hP_eval z
        _ = (Polynomial.C a * Polynomial.X + Polynomial.C b).eval z := by
              simp [hPform]
        _ = a * z + b := by
              simp
    have : f 0 = f 1 := by
      simp [hf_aff, ha0]
    have : (0 : ℂ) = 1 := hf_inj this
    simp at this
