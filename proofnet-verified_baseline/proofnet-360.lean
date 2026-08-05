import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology



/-Informal Statement

Suppose that $f$ is holomorphic in an open set $\Omega$. Prove that if $\text{Im}(f)$ is constant, then $f$ is constant.
-/

/-Informal Proof

Let $f(z)=f(x, y)=u(x, y)+i v(x, y)$, where $z=x+i y$.
Since $\operatorname{Im}(f)=$ constant,
$$
\frac{\partial v}{\partial x}=0, \frac{\partial v}{\partial y}=0 .
$$
By the Cauchy-Riemann equations,
$$
\frac{\partial u}{\partial x}=\frac{\partial v}{\partial y}=0 .
$$
Thus in $\Omega$,
$$
f^{\prime}(z)=\frac{\partial f}{\partial x}=\frac{\partial u}{\partial x}+i \frac{\partial v}{\partial x}=0+0=0 .
$$
Thus $f$ is constant.
-/

theorem Shakarchi_exercise_1_13b {f : ℂ → ℂ} (Ω : Set ℂ) (a b : Ω) (h : IsOpen Ω)
  (hf : DifferentiableOn ℂ f Ω) (hc : ∃ (c : ℝ), ∀ z ∈ Ω, (f z).im = c) :
  f a = f b := by
  sorry

/-!
Counterexample discussion and fixed statements for Shakarchi_exercise_1_13b.
-/

namespace Proofnet360

def ex113bLeft : Set ℂ := {z : ℂ | z.re < 0}

def ex113bRight : Set ℂ := {z : ℂ | 0 < z.re}

def ex113bΩ : Set ℂ := ex113bLeft ∪ ex113bRight

noncomputable def ex113bF (z : ℂ) : ℂ := if z.re < 0 then 0 else 1

noncomputable def ex113bPointNeg : ex113bΩ :=
  ⟨-1, Or.inl <|
    by
      -- Step 0: Simplify the membership condition to `(-1 : ℝ) < 0`.
      simp [ex113bLeft, show (-1 : ℝ) < 0 from neg_one_lt_zero]⟩

noncomputable def ex113bPointPos : ex113bΩ :=
  ⟨1, Or.inr <|
    by
      -- Step 0: Reduce the membership goal to `0 < (1 : ℝ)`.
      simp [ex113bRight, show 0 < (1 : ℝ) from zero_lt_one]⟩

lemma ex113b_isOpen_left : IsOpen ex113bLeft := by
  -- Step 1: Reinterpret the left half-plane as `{z | (fun z ↦ z.re) z < (fun _ ↦ 0) z}`.
  -- Step 2: Apply the standard lemma `isOpen_lt` using the continuity of `Complex.re`.
  simpa [ex113bLeft] using (isOpen_lt Complex.continuous_re continuous_const)

lemma ex113b_isOpen_right : IsOpen ex113bRight := by
  -- Step 1: Express the right half-plane as `{z | (fun _ ↦ 0) z < (fun z ↦ z.re) z}`.
  -- Step 2: Invoke `isOpen_lt` once more, now swapping the two continuous maps.
  simpa [ex113bRight] using (isOpen_lt continuous_const Complex.continuous_re)

lemma ex113b_isOpen_Ω : IsOpen ex113bΩ := by
  -- Step 1: Observe that `ex113bΩ` is the union of the two open half-planes.
  -- Step 2: Conclude using `IsOpen.union`.
  simpa [ex113bΩ] using ex113b_isOpen_left.union ex113b_isOpen_right

lemma ex113bF_differentiable :
    DifferentiableOn ℂ ex113bF ex113bΩ := by
  classical
  -- Step 1: Show differentiability on the left component by comparing with the constant zero map.
  have hLeft :
      DifferentiableOn ℂ ex113bF ex113bLeft := by
    have hconst' :
        Differentiable ℂ fun _ : ℂ => (0 : ℂ) := by
      exact differentiable_const (0 : ℂ)
    have hconst :
        DifferentiableOn ℂ (fun _ : ℂ => (0 : ℂ)) ex113bLeft :=
      hconst'.differentiableOn
    -- Step 1.1: Use `DifferentiableOn.congr` because on the left half-plane the function equals `0`.
    refine hconst.congr ?_
    intro z hz
    -- Step 1.2: `simp` unfolds the `if` since `hz : z.re < 0`.
    have hzlt : z.re < 0 := hz
    simp [ex113bF, hzlt]
  -- Step 2: Show differentiability on the right component via the constant one map.
  have hRight :
      DifferentiableOn ℂ ex113bF ex113bRight := by
    have hconst' :
        Differentiable ℂ fun _ : ℂ => (1 : ℂ) := by
      exact differentiable_const (1 : ℂ)
    have hconst :
        DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) ex113bRight :=
      hconst'.differentiableOn
    -- Step 2.1: Again rely on `DifferentiableOn.congr`, now using that `z.re < 0` is false on the right.
    refine hconst.congr ?_
    intro z hz
    -- Step 2.2: Record that `¬ z.re < 0` because `hz : 0 < z.re`.
    have hpos : 0 < z.re := hz
    have hnot : ¬ z.re < 0 := not_lt.mpr (le_of_lt hpos)
    -- Step 2.3: Simplify the `if` decision using `hnot`.
    simp [ex113bF, hnot]
  -- Step 3: Combine the two pieces using the union lemma for differentiability on open sets.
  simpa [ex113bΩ] using
    (DifferentiableOn.union_of_isOpen hLeft hRight ex113b_isOpen_left ex113b_isOpen_right)

lemma ex113bF_im_constant :
    ∃ c : ℝ, ∀ z ∈ ex113bΩ, (ex113bF z).im = c := by
  -- Step 1: Choose the constant `c = 0` because both branch values are real.
  refine ⟨0, ?_⟩
  intro z hz
  -- Step 2: Split according to which connected component contains `z`.
  rcases hz with hz | hz
  · -- Step 2.1: On the left component the value is `0`, so the imaginary part is automatically `0`.
    have hzlt : z.re < 0 := hz
    simp [ex113bF, hzlt]
  · -- Step 2.2: On the right component the value is `1`, whose imaginary part also vanishes.
    have hpos : 0 < z.re := hz
    have hnot : ¬ z.re < 0 := not_lt.mpr (le_of_lt hpos)
    simp [ex113bF, hnot]

lemma ex113bF_neg_value : ex113bF ex113bPointNeg = 0 := by
  -- Step 1: Unfold the definition of the special point and of the function.
  -- Step 2: Simplify using that `(-1).re < 0`.
  simp [ex113bF, ex113bPointNeg]

lemma ex113bF_pos_value : ex113bF ex113bPointPos = 1 := by
  -- Step 1: Expand the definitions.
  -- Step 2: Use that `(1).re > 0`, so we fall in the second branch of the `if`.
  simp [ex113bF, ex113bPointPos]

lemma ex113bF_values_ne :
    ex113bF ex113bPointNeg ≠ ex113bF ex113bPointPos := by
  -- Step 1: Reduce to `0 ≠ 1` via the previous two evaluation lemmas.
  -- Step 2: Finish with the obvious inequality.
  simp [ex113bF_neg_value, ex113bF_pos_value]

end Proofnet360

open Proofnet360

theorem Shakarchi_exercise_1_13b_neg :
    ∃ (f : ℂ → ℂ) (Ω : Set ℂ) (a b : Ω)
      (_h : IsOpen Ω) (_hf : DifferentiableOn ℂ f Ω)
      (_hc : ∃ c : ℝ, ∀ z ∈ Ω, (f z).im = c), f a ≠ f b := by
  classical
  -- Step 1: Select the explicit counterexample data prepared above.
  refine ⟨ex113bF, ex113bΩ, ex113bPointNeg, ex113bPointPos,
    ex113b_isOpen_Ω, ex113bF_differentiable, ex113bF_im_constant, ?_⟩
  -- Step 2: Apply the computed inequality `ex113bF ex113bPointNeg ≠ ex113bF ex113bPointPos`.
  simpa using ex113bF_values_ne

/-- A helper lemma for the corrected version: no nonempty subset of a horizontal or vertical line
is open in the complex plane. -/
lemma subset_verticalLine_not_isOpen {c : ℝ} {s : Set ℂ}
    (hs : s ⊆ {z : ℂ | z.im = c}) (hne : s.Nonempty) :
    ¬ IsOpen s := by
  classical
  -- Step 1: Fix a point `w ∈ s` and remember its imaginary part.
  obtain ⟨w, hw⟩ := hne
  have hw_im : w.im = c := by
    have := hs hw
    simpa [Set.mem_setOf_eq] using this
  -- Step 2: Assume `s` is open so that it contains a ball around `w`.
  intro hOpen
  rcases Metric.mem_nhds_iff.1 (hOpen.mem_nhds hw) with ⟨r, hr_pos, hr_ball⟩
  -- Step 3: Move vertically by `r / 2` to obtain a new point inside that ball.
  set w' := w + ((r / 2 : ℝ) : ℂ) * Complex.I
  have hw'_mem : w' ∈ Metric.ball w r := by
    -- Step 3.1: Compute the distance to `w`.
    have hdist : dist w' w = r / 2 := by
      simp [w', dist_eq_norm, Complex.norm_real, Complex.norm_I,
        Real.norm_eq_abs, abs_of_pos hr_pos]
    -- Step 3.2: Compare this distance with `r`.
    have : dist w' w < r := by
      simpa [hdist] using (half_lt_self hr_pos)
    exact Metric.mem_ball.2 this
  have hw'_in_s : w' ∈ s := hr_ball hw'_mem
  -- Step 4: Evaluate the imaginary part of `w'`.
  have hw'_im : w'.im = c + r / 2 := by
    simp [w', hw_im]
  -- Step 5: The equality above contradicts the constraint `hs`.
  have hpos : r / 2 > 0 := half_pos hr_pos
  have hw'_not_mem : w' ∉ {z : ℂ | z.im = c} := by
    -- Step 5.1: `c + r / 2` is strictly larger than `c`.
    have hneq : c + r / 2 ≠ c := by
      have hgt : c + r / 2 > c := by
        have := lt_add_of_pos_right c hpos
        simpa [add_comm] using this
      exact ne_of_gt hgt
    -- Step 5.2: Conclude that `w'.im` cannot equal `c`.
    intro hw'
    have : c + r / 2 = c := by
      simpa [Set.mem_setOf_eq, hw'_im] using hw'
    exact hneq this
  exact hw'_not_mem (hs hw'_in_s)

/-- Corrected statement: on a preconnected open domain, a holomorphic function with constant
imaginary part is globally constant. -/
theorem Shakarchi_exercise_1_13b_corrected {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hConn : IsPreconnected Ω)
    (hf : DifferentiableOn ℂ f Ω)
    (hc : ∃ c : ℝ, ∀ z ∈ Ω, (f z).im = c) :
    ∀ a b : Ω, f a = f b := by
  classical
  -- Step 1: Extract the constant imaginary value.
  obtain ⟨c, hcConst⟩ := hc
  -- Step 2: Promote the differentiability assumption to analyticity on a neighborhood.
  have hAnalytic : AnalyticOnNhd ℂ f Ω := hf.analyticOnNhd hΩ
  -- Step 3: Apply the open mapping theorem dichotomy.
  have hChoice := hAnalytic.is_constant_or_isOpen hConn
  -- Step 4: Prepare the auxiliary facts about the image of `f`.
  have hsubset : f '' Ω ⊆ {z : ℂ | z.im = c} := by
    -- Step 4.1: Directly unfold the definition of the image and use `hcConst`.
    intro w hw
    rcases hw with ⟨z, hzΩ, rfl⟩
    simpa [Set.mem_setOf_eq] using hcConst z hzΩ
  -- Step 4.2: We will also use that the image is nonempty once a point of `Ω` is chosen.
  intro a b
  have himage_ne : (f '' Ω).Nonempty := ⟨f a, ⟨a, a.property, rfl⟩⟩
  -- Step 5: Perform the case analysis.
  cases hChoice with
  | inl hconst =>
      -- Step 5.1: In the constant case, specialize the witness to both `a` and `b`.
      obtain ⟨w, hw⟩ := hconst
      have ha := hw a a.property
      have hb := hw b b.property
      -- Step 5.2: Combine the two equalities.
      simp [ha, hb]
  | inr hopen =>
      -- Step 6: Show that the \"open image\" option contradicts the geometric constraint.
      have hopenImage : IsOpen (f '' Ω) := hopen Ω subset_rfl hΩ
      have hnoopen := subset_verticalLine_not_isOpen (c := c) hsubset himage_ne
      exact (hnoopen hopenImage).elim
/-
Explanation (plain language):
Step 1. The original statement forgets to ask that `Ω` be connected. The open mapping theorem
(or the standard fact that holomorphic functions are locally constant when the derivative vanishes)
only ensures constancy on each connected component.
Step 2. Take the open set consisting of the left and right open half-planes. On each component we
declare a different real constant value; the imaginary part stays at `0`, but the function is not
constant across the two components.
Step 3. Therefore the Lean statement is false as written, and we must prove its negation and also
record a corrected version that assumes `Ω` is preconnected (hence connected in the classical sense).
-/
