import Mathlib

open Filter Set TopologicalSpace
open scoped Topology



/-Informal Statement

Let $f: S^{1} \rightarrow \mathbb{R}$ be a continuous map. Show there exists a point $x$ of $S^{1}$ such that $f(x)=f(-x)$.
-/

/-Informal Proof

Let $f: S^1 \rightarrow \mathbb{R}$ be continuous. Let $x \in S^1$. If $f(x)=f(-x)$ we are done, so assume $f(x) \neq f(-x)$. Define $g: S^1 \rightarrow \mathbb{R}$ by setting $g(x)=f(x)-f(-x)$. Then $g$ is continuous. Suppose $f(x)>f(-x)$, so that $g(x)>0$. Then $-x \in S^1$ and $g(-x)<0$. By the intermediate value theorem, since $S^1$ is connected and $g(-x)<0<g(x)$, there exists $y \in S^1$ such that $g(y)=0$. i.e, $f(y)=f(-y)$. Similarly, if $f(x)<f(-x)$, then $g(x)<0<g(-x)$ and again the intermediate value theorem gives the result.
-/

theorem Munkres_exercise_24_2 {f : (Metric.sphere 0 1 : Set ℝ) → ℝ}
  (hf : Continuous f) : ∃ x, f x = f (-x) := by
  sorry

/-
Explanation: The formalized domain `Metric.sphere 0 1 : Set ℝ` contains only the two antipodal
points `1` and `-1`. A continuous function on this discrete two-point space can separate the values
at these points, so the claimed equality need not hold.
-/

noncomputable section

open scoped Real

/-- Step 1: Define the counterexample function `x ↦ x` on the 0-sphere `{±1}`. -/
def exercise_24_2_counterexample :
    (Metric.sphere (0 : ℝ) 1 : Set ℝ) → ℝ :=
  fun x => (x : ℝ)

/-- Step 2: Prove the counterexample function is continuous (the subtype projection is continuous). -/
lemma exercise_24_2_counterexample_cont :
    Continuous exercise_24_2_counterexample := by
  -- Step 2.1: Rewrite goal via the definition to use `continuous_subtype_val`.
  simpa [exercise_24_2_counterexample] using
    (continuous_subtype_val :
      Continuous fun x : (Metric.sphere (0 : ℝ) 1 : Set ℝ) => (x : ℝ))

/-- Step 3: Show no point on the 0-sphere satisfies the symmetry equality for the counterexample. -/
lemma exercise_24_2_counterexample_no_sym :
    ¬ ∃ x, exercise_24_2_counterexample x = exercise_24_2_counterexample (-x) := by
  -- Step 3.1: Argue by contradiction assuming some `x` equalizes the values.
  intro hx
  obtain ⟨x, hx⟩ := hx
  -- Step 3.2: Translate the equality into a statement about real numbers.
  have hx' : (x : ℝ) = -((x : ℝ)) := by
    simpa [exercise_24_2_counterexample]
  -- Step 3.3: Add `(x : ℝ)` to both sides to deduce `2 * (x : ℝ) = 0`.
  have hx_double :
      (2 : ℝ) * (x : ℝ) = 0 := by
    -- Step 3.3.1: First show `(x : ℝ) + (x : ℝ) = 0`.
    have hx_sum :
        (x : ℝ) + (x : ℝ) = 0 := by
      -- Step 3.3.1.1: Apply congruence after adding `(x : ℝ)` to both sides.
      have := congrArg (fun t : ℝ => t + (x : ℝ)) hx'
      -- Step 3.3.1.2: Simplify and finish the equality.
      simpa [add_comm, add_left_comm, add_assoc] using this
    -- Step 3.3.2: Convert the sum equality into a product equality.
    simpa [two_mul] using hx_sum
  -- Step 3.4: Use that `2 ≠ 0` to deduce `(x : ℝ) = 0`.
  have hx_zero : (x : ℝ) = 0 := by
    -- Step 3.4.1: Apply the zero-product property.
    exact
      (mul_eq_zero.mp hx_double).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
  -- Step 3.5: Evaluate the defining distance using `x = 0`.
  have hdist_zero : dist (x : ℝ) 0 = 0 := by
    -- Step 3.5.1: `(x : ℝ) = 0` implies the distance to the origin is zero.
    simp [hx_zero]
  -- Step 3.6: Combine with the sphere condition to reach a contradiction.
  have hx_dist : dist (x : ℝ) 0 = 1 := x.property
  have : (1 : ℝ) = 0 := by
    -- Step 3.6.1: Substitute the computed distance into the defining equality.
    simpa [hdist_zero] using hx_dist.symm
  -- Step 3.7: Contradiction with `1 ≠ 0`.
  exact one_ne_zero this

/-- Step 4: Package the negation: the universal claim fails thanks to the counterexample. -/
theorem Munkres_exercise_24_2_neg :
    ¬ (∀ (f : (Metric.sphere (0 : ℝ) 1 : Set ℝ) → ℝ),
        Continuous f → ∃ x, f x = f (-x)) := by
  -- Step 4.1: Expand the negation using the explicit counterexample.
  intro h
  -- Step 4.2: Apply the assumed statement to our counterexample function.
  have hx := h exercise_24_2_counterexample exercise_24_2_counterexample_cont
  -- Step 4.3: Contradict the previous lemma showing the absence of symmetric points.
  exact exercise_24_2_counterexample_no_sym hx

/-
Corrected Statement:
If we interpret the circle as the unit sphere in the complex plane, every continuous function
`f : Metric.sphere (0 : ℂ) 1 → ℝ` admits an antipodal pair with equal values.
-/

/-- Step 5: Parameterize the sphere via the exponential map on the circle. -/
def circleParam (t : ℝ) :
    (Metric.sphere (0 : ℂ) 1 : Set ℂ) :=
  ⟨(Circle.exp t : ℂ), by
    -- Step 5.1: Restate the sphere membership as a norm equality.
    change ‖(Circle.exp t : ℂ) - 0‖ = 1
    -- Step 5.2: Simplify to the known unit-norm property of `Circle.exp`.
    simp⟩

/-- Step 6: The parametrization is continuous. -/
lemma circleParam_continuous : Continuous circleParam := by
  -- Step 6.1: The map `t ↦ (Circle.exp t : ℂ)` is continuous.
  have hval :
      Continuous fun t : ℝ => (Circle.exp t : ℂ) :=
    (continuous_subtype_val : Continuous fun z : Circle => (z : ℂ)).comp Circle.exp.continuous
  -- Step 6.2: Upgrade the continuity result to the subtype.
  exact Continuous.subtype_mk
    (by simpa [circleParam] using hval)
    (by
      intro t
      change ‖(Circle.exp t : ℂ) - 0‖ = 1
      simp)

/-- Step 7: Rotating the parameter by `π` gives the antipodal point. -/
lemma circleParam_add_pi (t : ℝ) :
    circleParam (t + Real.pi) = -circleParam t := by
  -- Step 7.1: Compare underlying complex numbers.
  apply Subtype.ext
  -- Step 7.2: Rewrite via complex exponentials.
  change (Circle.exp (t + Real.pi) : ℂ) = -(Circle.exp t : ℂ)
  simp [Circle.coe_exp, Complex.exp_pi_mul_I]

/-- Step 8: State and prove the corrected version on the complex unit circle. -/
theorem Munkres_exercise_24_2_corrected
    {f : (Metric.sphere (0 : ℂ) 1 : Set ℂ) → ℝ}
    (hf : Continuous f) : ∃ x, f x = f (-x) := by
  -- Step 9.1: Work classically for convenience.
  classical
  -- Step 9.2: Define the asymmetry function on the sphere.
  let g : (Metric.sphere (0 : ℂ) 1 : Set ℂ) → ℝ := fun z => f z - f (-z)
  -- Step 9.3: Establish continuity of `g`.
  have hg : Continuous g := by
    -- Step 9.3.1: Combine continuity of `f` with the negation map.
    refine hf.sub ?_
    exact hf.comp continuous_neg
  -- Step 9.4: Pull back along the parameterization.
  let φ : ℝ → ℝ := fun t => g (circleParam t)
  -- Step 9.5: Record continuity of `φ`.
  have hφ : Continuous φ := hg.comp circleParam_continuous
  -- Step 9.6: Evaluate the endpoints at `0` and `π`.
  have hφ_zero :
      φ 0 = f (circleParam 0) - f (-circleParam 0) := by
    -- Step 9.6.1: Unfold definitions.
    simp [φ, g]
  have hφ_pi :
      φ Real.pi = f (circleParam Real.pi) - f (-circleParam Real.pi) := by
    -- Step 9.6.2: Similar expansion at `π`.
    simp [φ, g]
  -- Step 9.7: Relate the two endpoints using the antipodal identity.
  have hflip : circleParam Real.pi = -circleParam 0 := by
    simpa [zero_add] using circleParam_add_pi (0 : ℝ)
  have hφ_pi' :
      φ Real.pi = -φ 0 := by
    -- Step 9.7.1: Substitute the identity from Step 9.7.
    simp [φ, g, hflip, sub_eq_add_neg, add_comm]
  -- Step 9.8: Prepare data for the intermediate value theorem.
  have hcont_on : ContinuousOn φ (Set.Icc (0 : ℝ) Real.pi) := hφ.continuousOn
  have hpi_nonneg : (0 : ℝ) ≤ Real.pi := Real.pi_nonneg
  -- Step 9.9: Case split on whether `φ 0` already vanishes.
  by_cases hzero : φ 0 = 0
  · -- Step 9.9.1: Immediate solution when the difference at `t = 0` vanishes.
    refine ⟨circleParam 0, ?_⟩
    -- Step 9.9.1.1: Read the equality off from the definition of `φ`.
    have hzero' : φ 0 = 0 := hzero
    have : f (circleParam 0) - f (-circleParam 0) = 0 := by
      simpa [φ, g] using hzero'
    exact sub_eq_zero.mp this
  · -- Step 9.9.2: Otherwise, apply the intermediate value theorem.
    have hφ_ne : φ 0 ≠ 0 := hzero
    -- Step 9.9.2.1: Distinguish the sign of `φ 0`.
    have hcases := lt_or_gt_of_ne hφ_ne
    rcases hcases with hneg | hpos
    · -- Step 9.9.2.1(a): If `φ 0 < 0`, then `φ π > 0`.
      have hpos' : 0 ≤ φ Real.pi := by
        simpa [hφ_pi'] using neg_nonneg.mpr (le_of_lt hneg)
      have hsubset :=
        intermediate_value_Icc (a := (0 : ℝ)) (b := Real.pi)
          (f := φ) hpi_nonneg hcont_on
      have hzero_mem : (0 : ℝ) ∈ Set.Icc (φ 0) (φ Real.pi) :=
        ⟨le_of_lt hneg, hpos'⟩
      obtain ⟨t, ht_mem, ht_val⟩ := hsubset hzero_mem
      refine ⟨circleParam t, ?_⟩
      -- Step 9.9.2.1(a.i): Translate the vanishing of `φ t` back to the original function.
      simpa [φ, g, sub_eq_zero] using ht_val
    · -- Step 9.9.2.1(b): If `φ 0 > 0`, then `φ π < 0`.
      have hneg' : φ Real.pi ≤ 0 := by
        simpa [hφ_pi'] using neg_nonpos.mpr (le_of_lt hpos)
      have hsubset :=
        intermediate_value_Icc' (a := (0 : ℝ)) (b := Real.pi)
          (f := φ) hpi_nonneg hcont_on
      have hzero_mem : (0 : ℝ) ∈ Set.Icc (φ Real.pi) (φ 0) :=
        ⟨hneg', le_of_lt hpos⟩
      obtain ⟨t, ht_mem, ht_val⟩ := hsubset hzero_mem
      refine ⟨circleParam t, ?_⟩
      -- Step 9.9.2.1(b.i): Conclude as in the previous branch.
      simpa [φ, g, sub_eq_zero] using ht_val
