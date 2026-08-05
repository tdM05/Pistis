import Mathlib
import Mathlib.Analysis.Complex.OpenMapping

open Complex Filter Function Metric Finset
open scoped BigOperators Topology



/-Informal Statement

Suppose that $f$ is holomorphic in an open set $\Omega$. Prove that if $\text{Re}(f)$ is constant, then $f$ is constant.
-/

/-Informal Proof

Let $f(z)=f(x, y)=u(x, y)+i v(x, y)$, where $z=x+i y$.
Since $\operatorname{Re}(f)=$ constant,
$$
\frac{\partial u}{\partial x}=0, \frac{\partial u}{\partial y}=0 .
$$
By the Cauchy-Riemann equations,
$$
\frac{\partial v}{\partial x}=-\frac{\partial u}{\partial y}=0 .
$$
Thus, in $\Omega$,
$$
f^{\prime}(z)=\frac{\partial f}{\partial x}=\frac{\partial u}{\partial x}+i \frac{\partial v}{\partial x}=0+0=0 .
$$
3
Thus $f(z)$ is constant.
-/

theorem Shakarchi_exercise_1_13a {f : ℂ → ℂ} (Ω : Set ℂ) (a b : Ω) (h : IsOpen Ω)
  (hf : DifferentiableOn ℂ f Ω) (hc : ∃ (c : ℝ), ∀ z ∈ Ω, (f z).re = c) :
  f a = f b := by
  sorry

/-
Step-by-step diagnosis of the informal argument:
Step 1: The textbook proof silently assumes that the open set `Ω` is connected (a “domain”).
Step 2: If `Ω` is disconnected, one may define a holomorphic function that is constant on every
        connected component but takes different constants on different components.
Step 3: Such a function still has constant real part, so the hypotheses of the Lean statement hold,
        yet the conclusion fails for points chosen in distinct components.
Step 4: The correct statement must therefore add a connectivity hypothesis (for instance
        `IsPreconnected Ω`), after which the open mapping theorem implies that `f` is constant.
-/

namespace Exercise_1_13a

open Set Metric

noncomputable section

def badΩ : Set ℂ := {z : ℂ | z.im ≠ 0}

def badf (z : ℂ) : ℂ := if z.im ≤ 0 then (2 : ℂ) * Complex.I else Complex.I

lemma isOpen_badΩ : IsOpen badΩ := by
  classical
  -- Step 1: Decompose `badΩ` into the union of the open upper and lower half-planes.
  have hpos : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hneg : IsOpen {z : ℂ | z.im < 0} :=
    isOpen_lt Complex.continuous_im continuous_const
  have hrepr :
      {z : ℂ | z.im < 0} ∪ {z : ℂ | 0 < z.im} = {z : ℂ | z.im ≠ 0} := by
    ext z; constructor <;> intro hz
    · -- Step 1.1: A nonzero imaginary part is either negative or positive.
      rcases hz with hlt | hgt
      · exact ne_of_lt hlt
      · exact ne_of_gt hgt
    · -- Step 1.2: Either inequality implies the imaginary part is nonzero.
      have hz' : z.im ≠ 0 := hz
      have := lt_or_gt_of_ne hz'
      exact this
  -- Step 2: Conclude openness via stability under finite unions.
  have hUnion : IsOpen ({z : ℂ | z.im < 0} ∪ {z : ℂ | 0 < z.im}) := hneg.union hpos
  simpa [badΩ, hrepr] using hUnion

lemma mem_badΩ_iff {z : ℂ} : z ∈ badΩ ↔ z.im ≠ 0 := Iff.rfl

lemma badf_differentiable : DifferentiableOn ℂ badf badΩ := by
  classical
  -- Step 1: Fix an arbitrary point `z` inside `badΩ` and unfold the goal.
  intro z hz
  -- Step 2: Split the point into the two possible sign cases for `z.im`.
  have hcases := lt_or_gt_of_ne (by simpa [mem_badΩ_iff] using hz)
  -- Step 3: Treat the case `z.im < 0`, showing that `badf` agrees near `z` with the constant map
  --         equal to `(2 : ℂ) * Complex.I`.
  cases hcases with
  | inl hneg =>
      -- Step 3.1: Record openness of the lower half-plane to obtain an eventual equality.
      have hopen_neg : IsOpen {w : ℂ | w.im < 0} :=
        isOpen_lt Complex.continuous_im continuous_const
      have hz_mem : z ∈ {w : ℂ | w.im < 0} := hneg
      have hnhds : {w : ℂ | w.im < 0} ∈ 𝓝 z := hopen_neg.mem_nhds hz_mem
      -- Step 3.2: Use `DifferentiableAt.congr_of_eventuallyEq` with the constant function.
      have hconst : DifferentiableAt ℂ (fun _ : ℂ => (2 : ℂ) * Complex.I) z := by
        -- Step 3.2.1: Constant maps are differentiable at every point.
        exact differentiableAt_const _
      have hEq :
          badf =ᶠ[𝓝 z] fun _ : ℂ => (2 : ℂ) * Complex.I := by
        -- Step 3.2.2: Near `z`, the imaginary part stays negative, so `badf` equals the constant.
        refine (Filter.eventually_of_mem hnhds ?_)
        intro w hw
        have hwle : w.im ≤ 0 := le_of_lt hw
        -- Step 3.2.3: Rewrite the `if` using the nonpositivity evidence.
        simp [badf, hwle]
      -- Step 3.3: Transfer differentiability along the eventual equality.
      exact
        (DifferentiableAt.congr_of_eventuallyEq hconst hEq).differentiableWithinAt
  | inr hpos =>
      -- Step 4: Treat the case `0 < z.im`, reducing to the constant map `fun _ => Complex.I`.
      have hopen_pos : IsOpen {w : ℂ | 0 < w.im} :=
        isOpen_lt continuous_const Complex.continuous_im
      have hz_mem : z ∈ {w : ℂ | 0 < w.im} := hpos
      have hnhds : {w : ℂ | 0 < w.im} ∈ 𝓝 z := hopen_pos.mem_nhds hz_mem
      -- Step 4.1: As before, constant maps are differentiable.
      have hconst : DifferentiableAt ℂ (fun _ : ℂ => Complex.I) z := by
        exact differentiableAt_const _
      -- Step 4.2: Show that `badf` equals that constant near `z`.
      have hEq :
          badf =ᶠ[𝓝 z] fun _ : ℂ => Complex.I := by
        refine (Filter.eventually_of_mem hnhds ?_)
        intro w hw
        have : ¬ w.im ≤ 0 := not_le.mpr hw
        simp [badf, this]
      -- Step 4.3: Conclude differentiability on this branch.
      exact
        (DifferentiableAt.congr_of_eventuallyEq hconst hEq).differentiableWithinAt

lemma badf_real_part_const :
    ∀ ⦃z : ℂ⦄, z ∈ badΩ → (badf z).re = 0 := by
  classical
  -- Step 1: Fix `z` in `badΩ` and split into the same sign cases as above.
  intro z hz
  have hcases := lt_or_gt_of_ne (by simpa [mem_badΩ_iff] using hz)
  cases hcases with
  | inl hneg =>
      -- Step 1.1: When `z.im < 0`, we are in the first branch of the definition.
      have hzle : z.im ≤ 0 := le_of_lt hneg
      -- Step 1.2: Evaluate the real part explicitly.
      simp [badf, hzle]
  | inr hpos =>
      -- Step 1.3: When `0 < z.im`, the second branch gives the result immediately.
      have : ¬ z.im ≤ 0 := not_le.mpr hpos
      simp [badf, this]

def badA : badΩ :=
  ⟨Complex.I, by
    -- Step 1: Show that `Complex.I` has imaginary part `1`, hence belongs to `badΩ`.
    simp [badΩ]⟩

def badB : badΩ :=
  ⟨-Complex.I, by
    -- Step 1: The point `-I` has imaginary part `-1`, which is nonzero.
    simp [badΩ]⟩

lemma badf_badA : badf badA = Complex.I := by
  -- Step 1: `badA` lies in the upper half-plane, so the “else” branch is selected.
  have : ¬ (Complex.I).im ≤ 0 := by
    -- Step 1.1: `Complex.I` has positive imaginary part.
    simp
  -- Step 1.2: Evaluate the definition.
  simp [badf, badA]

lemma badf_badB : badf badB = (2 : ℂ) * Complex.I := by
  -- Step 1: `badB` lies in the lower half-plane, so we use the first branch.
  have : (-Complex.I).im ≤ 0 := by
    -- Step 1.1: The imaginary part equals `-1`.
    simp
  -- Step 1.2: Evaluate the definition.
  simp [badf, badB]

lemma complexI_ne_two_complexI : (Complex.I : ℂ) ≠ (2 : ℂ) * Complex.I := by
  -- Step 1: Suppose equality holds and derive `Complex.I = 0`, contradicting `Complex.I_ne_zero`.
  intro h
  have hzero : (Complex.I : ℂ) = 0 := by
    -- Step 1.1: Subtract `Complex.I` from both sides and simplify.
    have := congrArg (fun z : ℂ => z - Complex.I) h
    simpa [two_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this.symm
  -- Step 1.2: Use the known fact that `I ≠ 0`.
  exact Complex.I_ne_zero hzero

theorem exercise_1_13a_counterexample :
    ¬ (∀ {f : ℂ → ℂ} {Ω : Set ℂ} {a b : Ω},
        IsOpen Ω →
        DifferentiableOn ℂ f Ω →
        (∃ c : ℝ, ∀ z ∈ Ω, (f z).re = c) →
        f a = f b) := by
  classical
  -- Step 1: Witness the negation by instantiating all arguments with the explicit counterexample.
  refine fun h => ?_
  -- Step 2: Package the data required by the original claim.
  set Ω := badΩ
  set f := badf
  have hΩ : IsOpen Ω := isOpen_badΩ
  -- Step 3: Produce the necessary analytic data.
  have hf : DifferentiableOn ℂ f Ω := badf_differentiable
  have hc : ∃ c : ℝ, ∀ z ∈ Ω, (f z).re = c := ⟨0, fun z hz => badf_real_part_const hz⟩
  -- Step 4: Apply the universally quantified hypothesis.
  have hval := h (f := f) (Ω := Ω) (a := badA) (b := badB) hΩ hf hc
  -- Step 5: Evaluate both sides of the equality obtained from the hypothesis.
  have hcontra : Complex.I = (2 : ℂ) * Complex.I := by
    simp [f, badf_badA, badf_badB] at hval
  -- Step 6: Reach the contradiction promised by the explicit inequality.
  exact complexI_ne_two_complexI hcontra

lemma open_subset_verticalLine_eq_empty {s : Set ℂ} {c : ℝ}
    (hs : IsOpen s) (hsub : s ⊆ {w : ℂ | w.re = c}) : s = ∅ := by
  classical
  -- Step 1: Prove emptiness by contradiction; assume there exists `z ∈ s`.
  apply by_contra fun hne =>
  have hnonempty : (Set.Nonempty s) := Set.nonempty_iff_ne_empty.mpr hne
  let z : ℂ := hnonempty.choose
  have hz : z ∈ s := by
    simpa [z] using hnonempty.choose_spec
  -- Step 2: Use openness to find a radius `r` with `ball z r ⊆ s`.
  have hposball : ∃ r, 0 < r ∧ ball z r ⊆ s := (Metric.isOpen_iff.mp hs) z hz
  let r : ℝ := hposball.choose
  have hrpos : 0 < r := by
    simpa [r] using (hposball.choose_spec).1
  have hrsubset : ball z r ⊆ s := by
    simpa [r, z] using (hposball.choose_spec).2
  -- Step 3: Consider the point obtained by shifting `z` along the real axis.
  let w : ℂ := z + (r / 2 : ℝ)
  have hw_ball : w ∈ ball z r := by
    -- Step 3.1: The displacement has norm `r / 2`, which is strictly smaller than `r`.
    have hdiff : w - z = (r / 2 : ℝ) := by
      simp [w, sub_eq_add_neg, add_comm, add_left_comm]
    have hdist : dist w z = r / 2 := by
      have hnorm : dist w z = ‖((r / 2 : ℝ) : ℂ)‖ := by
        simp [dist_eq, hdiff]
      have hnormReal :
          ‖((r / 2 : ℝ) : ℂ)‖ = r / 2 := by
        have h₁ : ‖((r / 2 : ℝ) : ℂ)‖ = ‖r / 2‖ := by
          simp [Complex.norm_real]
        have h₂ : ‖r / 2‖ = |r / 2| := Real.norm_eq_abs _
        have h₃ : |r / 2| = r / 2 := abs_of_nonneg (half_pos hrpos).le
        exact h₁.trans (h₂.trans h₃)
      exact hnorm.trans hnormReal
    -- Step 3.2: Turn the distance computation into ball membership.
    have : dist w z < r := by
      simpa [hdist] using (half_lt_self hrpos)
    simpa [Metric.mem_ball] using this
  -- Step 4: Both `z` and `w` belong to `s`, so their real parts equal `c`.
  have hz_line : z.re = c := by
    simpa using hsub hz
  have hw_mem : w ∈ s := hrsubset hw_ball
  have hw_line : w.re = c := by
    simpa using hsub hw_mem
  -- Step 5: Compute `w.re` explicitly to see that it differs from `c`.
  have hw_re : w.re = z.re + r / 2 := by
    simp [w]
  have hsum : c = c + r / 2 := by
    calc
      c = w.re := hw_line.symm
      _ = z.re + r / 2 := hw_re
      _ = c + r / 2 := by simp [hz_line]
  -- Step 6: Deduce the impossible inequality `r / 2 = 0`.
  have hr_half_zero : (r / 2 : ℝ) = 0 := by
    have := congrArg (fun t : ℝ => t - c) hsum
    simpa using this.symm
  -- Step 7: Conclude by contradicting the positivity of `r / 2`.
  (half_pos hrpos).ne' (by simpa using hr_half_zero)

/-
Corrected formal statement:
If `Ω` is open *and preconnected* and `f` is holomorphic on `Ω` with constant real part, then
`f` is constant on `Ω`.
-/

theorem Shakarchi_exercise_1_13a_corrected {f : ℂ → ℂ} (Ω : Set ℂ) (a b : Ω) (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) (hf : DifferentiableOn ℂ f Ω)
    (hc : ∃ c : ℝ, ∀ z ∈ Ω, (f z).re = c) : f a = f b := by
  classical
  -- Step 1: Extract the real constant and restate the image constraint.
  rcases hc with ⟨c, hc⟩
  -- Step 2: Upgrade differentiability to analyticity on the open set.
  have hAnalytic : AnalyticOnNhd ℂ f Ω := hf.analyticOnNhd hΩ
  -- Step 3: Apply the open mapping dichotomy on preconnected sets.
  have hDichotomy := AnalyticOnNhd.is_constant_or_isOpen (g := f) (U := Ω) hAnalytic hconn
  rcases hDichotomy with hconst | hopen
  · -- Step 3.1: In the constant case, evaluate both points directly.
    rcases hconst with ⟨w, hw⟩
    -- Step 3.1.1: Use the provided equalities `f z = w` for the relevant points.
    have ha : f a = w := hw a a.property
    have hb : f b = w := hw b b.property
    -- Step 3.1.2: Combine both equalities to reach the desired equality.
    exact ha.trans hb.symm
  · -- Step 3.2: In the "open image" case, we derive a contradiction.
    have hOpenImage : IsOpen (f '' Ω) := hopen Ω (Subset.rfl) hΩ
    -- Step 3.2.1: Every value of `f` on `Ω` has real part `c`, so the image sits inside a line.
    have hsubset : f '' Ω ⊆ {w : ℂ | w.re = c} := by
      intro w hw
      rcases hw with ⟨z, hz, rfl⟩
      simpa using hc z hz
    -- Step 3.2.2: Invoke the geometric lemma to deduce that the image must be empty.
    have hEmpty : f '' Ω = ∅ := open_subset_verticalLine_eq_empty hOpenImage hsubset
    -- Step 3.2.3: Produce an explicit element of the image, contradicting emptiness.
    have hmem : f a ∈ f '' Ω := ⟨a, a.property, rfl⟩
    simp [hEmpty] at hmem
end

end Exercise_1_13a
