import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset Set
open scoped BigOperators



/-Informal Statement

Suppose $f$ is defined and differentiable for every $x>0$, and $f^{\prime}(x) \rightarrow 0$ as $x \rightarrow+\infty$. Put $g(x)=f(x+1)-f(x)$. Prove that $g(x) \rightarrow 0$ as $x \rightarrow+\infty$.
-/

/-Informal Proof

Let $\varepsilon>0$. Choose $x_0$ such that $\left|f^{\prime}(x)\right|<\varepsilon$ if $x>x_0$. Then for any $x \geq x_0$ there exists $x_1 \in(x, x+1)$ such that
$$
f(x+1)-f(x)=f^{\prime}\left(x_1\right) .
$$
Since $\left|f^{\prime}\left(x_1\right)\right|<\varepsilon$, it follows that $|f(x+1)-f(x)|<\varepsilon$, as required.
-/

theorem Rudin_exercise_5_5
  {f : ℝ → ℝ}
  (hfd : DifferentiableOn ℝ f (Ioi 0))
  (hf : Tendsto (deriv f) atTop (𝓝 0)) :
  Tendsto (λ x => f (x + 1) - f x) atTop (𝓝 0) := by
  -- Step 1: turn the limit of `deriv f` at `+∞` into an eventual bound using the metric definition.
  refine Metric.tendsto_atTop.2 ?_
  intro ε εpos
  -- Step 1.1: extract `δ` so that beyond some threshold the derivative stays in the ball of radius `ε`.
  have hderiv_small : ∀ᶠ x : ℝ in atTop, |deriv f x| < ε := by
    -- Step 1.1.1: apply `hf` to the metric ball `Metric.ball 0 ε` and rewrite it as an absolute-value inequality.
    have hball := hf.eventually (Metric.ball_mem_nhds (0 : ℝ) εpos)
    refine hball.mono ?_
    intro x hx
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub, sub_zero] using hx
  -- Step 1.2: translate the eventual statement into an explicit lower bound `N`.
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hderiv_small
  -- Step 2: prove the desired estimate once `x` is no smaller than `max N 1`.
  refine ⟨max N 1, ?_⟩
  intro x hx
  -- Step 2.1: record the basic inequalities coming from the choice `x ≥ max N 1`.
  have hxN : N ≤ x := by exact (le_of_max_le_left hx)
  have hx1 : (1 : ℝ) ≤ x := by exact (le_of_max_le_right hx)
  have hxpos : 0 < x := lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) hx1
  -- Step 2.2: restrict differentiability/continuity to `[x, x + 1] ⊆ (0, +∞)`.
  have hsubset_cc : Icc x (x + 1) ⊆ Ioi (0 : ℝ) := by
    intro y hy
    exact lt_of_lt_of_le hxpos hy.1
  have hsubset_oo : Ioo x (x + 1) ⊆ Ioi (0 : ℝ) := by
    intro y hy
    exact lt_trans hxpos hy.1
  have hcont_restrict : ContinuousOn f (Icc x (x + 1)) :=
    (hfd.continuousOn).mono hsubset_cc
  have hdiff_restrict : DifferentiableOn ℝ f (Ioo x (x + 1)) :=
    hfd.mono hsubset_oo
  -- Step 2.3: apply the mean value theorem to get a point whose derivative equals the increment.
  have hxlt : x < x + 1 := lt_add_of_pos_right x one_pos
  obtain ⟨c, hc_mem, hc_deriv⟩ :=
    exists_deriv_eq_slope (f := f) (a := x) (b := x + 1)
      (hab := hxlt) (hfc := hcont_restrict) (hfd := hdiff_restrict)
  have hdiff_eq : deriv f c = f (x + 1) - f x := by
    have hxden : (x + 1) - x = (1 : ℝ) := by ring
    simpa [hxden] using hc_deriv
  -- Step 2.4: bound the increment by bounding the derivative at the point `c ∈ (x, x + 1)`.
  have hc_ge : N ≤ c := le_trans hxN (le_of_lt hc_mem.1)
  have hbound : |deriv f c| < ε := hN c hc_ge
  have hgoal : |f (x + 1) - f x| < ε := by simpa [hdiff_eq]
    using hbound
  -- Step 2.5: rewrite the absolute value bound as a metric bound against `0`.
  simpa [Real.dist_eq, sub_zero] using hgoal
