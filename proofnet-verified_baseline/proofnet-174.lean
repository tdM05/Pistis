import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators



/-Informal Statement

Suppose (a) $f$ is continuous for $x \geq 0$, (b) $f^{\prime}(x)$ exists for $x>0$, (c) $f(0)=0$, (d) $f^{\prime}$ is monotonically increasing. Put $g(x)=\frac{f(x)}{x} \quad(x>0)$ and prove that $g$ is monotonically increasing.
-/

/-Informal Proof

Put
$$
g(x)=\frac{f(x)}{x} \quad(x>0)
$$
and prove that $g$ is monotonically increasing.
By the mean-value theorem
$$
f(x)=f(x)-f(0)=f^{\prime}(c) x
$$
for some $c \in(0, x)$. Since $f^{\prime}$ is monotonically increasing, this result implies that $f(x)<x f^{\prime}(x)$. It therefore follows that
$$
g^{\prime}(x)=\frac{x f^{\prime}(x)-f(x)}{x^2}>0,
$$
so that $g$ is also monotonically increasing.
-/

theorem Rudin_exercise_5_6
  {f : ℝ → ℝ}
  (hf1 : ContinuousOn f (Set.Ici 0))
  (hf2 : DifferentiableOn ℝ f (Set.Ioi 0))
  (hf3 : f 0 = 0)
  (hf4 : MonotoneOn (deriv f) (Set.Ioi 0)) :
  MonotoneOn (λ x => f x / x) (Set.Ioi 0) := by
  -- Step 1: Use the monotonicity of `f'` to deduce that `f` is convex on `[0, ∞)`.
  have hfconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) f := by
    -- Step 1.1: Rewrite the differentiability assumption on `(0, ∞)` as an interior statement.
    have hdiff : DifferentiableOn ℝ f (interior (Set.Ici (0 : ℝ))) := by
      simpa [interior_Ici] using hf2
    -- Step 1.2: Rewrite the monotonicity assumption on `(0, ∞)` as an interior statement.
    have hmono : MonotoneOn (deriv f) (interior (Set.Ici (0 : ℝ))) := by
      simpa [interior_Ici] using hf4
    -- Step 1.3: Apply the mean-value theorem based convexity criterion.
    exact hmono.convexOn_of_deriv (convex_Ici (0 : ℝ)) hf1 hdiff
  -- Step 2: Compare `g x = f x / x` and `g y` for arbitrary `0 < x ≤ y`.
  refine fun x hx y hy hxy => ?_
  -- Step 2.1: Record positivity and membership facts for `x`, `y`, and `0`.
  have hx_pos : 0 < x := hx
  have hy_pos : 0 < y := hy
  have hy_mem : y ∈ Set.Ici (0 : ℝ) := hy_pos.le
  have hzero_mem : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := by simp
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  -- Step 2.2: Introduce the ratio θ = x / y and collect its basic bounds.
  set θ := x / y with hθdef
  have hθ_nonneg : 0 ≤ θ := by
    -- Step 2.2.1: Both numerator and denominator are nonnegative.
    simpa [θ] using div_nonneg hx_pos.le hy_pos.le
  have hθ_le_one : θ ≤ (1 : ℝ) := by
    -- Step 2.2.2: Use `x ≤ y` to bound θ from above by 1.
    have hy_nonneg : 0 ≤ y := hy_pos.le
    simpa [θ] using div_le_one_of_le₀ hxy hy_nonneg
  have hone_minus_nonneg : 0 ≤ 1 - θ := sub_nonneg.mpr hθ_le_one
  -- Step 2.3: Apply convexity to the chord joining `y` and `0` with weights `θ` and `1 - θ`.
  have hfxle : f x ≤ θ * f y := by
    have hconv_app := hfconv.2 hy_mem hzero_mem hθ_nonneg hone_minus_nonneg (by simp)
    -- Step 2.3.1: Simplify the convex combination using `f 0 = 0` and the definition of θ.
    simpa [θ, hy_ne, hf3, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, add_right_comm] using
      hconv_app
  -- Step 2.4: Rewrite the inequality to express it in terms of `f x / x` and `f y / y`.
  have hx_goal : f x ≤ (f y / y) * x := by
    simpa [θ, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hfxle
  -- Step 2.5: Divide by the positive number `x` to obtain the desired monotonicity.
  exact (div_le_iff₀ hx_pos).2 hx_goal
