import Mathlib

open scoped BigOperators



/-Informal Statement

Let $f$ be a real function on the real line with continuous third derivative. Prove that there exists a point $a$ such that $f(a) \cdot f^{\prime}(a) \cdot f^{\prime \prime}(a) \cdot f^{\prime \prime \prime}(a) \geq 0$.
-/

/-Informal Proof

If at least one of $f(a)$, $f'(a)$, $f''(a)$, or $f'''(a)$ vanishes
at some point $a$, then we are done.  Hence we may assume each of
$f(x)$, $f'(x)$, $f''(x)$, and $f'''(x)$ is either strictly positive
or strictly negative on the real line.  By replacing $f(x)$ by $-f(x)$
if necessary, we may assume $f''(x)>0$; by replacing $f(x)$
by $f(-x)$ if necessary, we may assume $f'''(x)>0$.  (Notice that these
substitutions do not change the sign of $f(x) f'(x) f''(x) f'''(x)$.)
Now $f''(x)>0$ implies that $f'(x)$ is increasing, and $f'''(x)>0$
implies that $f'(x)$ is convex, so that $f'(x+a)>f'(x)+a f''(x)$
for all $x$ and $a$.  By
letting $a$ increase in the latter inequality, we see that $f'(x+a)$
must be positive for sufficiently large $a$; it follows that
$f'(x)>0$
for all $x$.  Similarly, $f'(x)>0$ and $f''(x)>0$ imply
that $f(x)>0$ for all $x$.  Therefore $f(x) f'(x) f''(x) f'''(x)>0$ for
all $x$, and we are done.
-/

/-
================================================================================
AUXILIARY LEMMAS: Tangent Line Inequalities for Convex/Concave Functions
================================================================================

These lemmas establish the fundamental tangent line inequalities:
- For convex functions: f(y) >= f(x) + f'(x)(y - x)  (graph lies above tangent)
- For concave functions: f(y) <= f(x) + f'(x)(y - x) (graph lies below tangent)

These are derived from the slope monotonicity properties of convex/concave functions.
-/

/--
Tangent Line Lower Bound for Convex Functions:
For a convex function f on Set.univ, at any point x where f is differentiable,
the function value f(y) at any other point y lies above the tangent line at x.
-/
lemma convexOn_tangent_line_lower_bound {x y : ℝ} {f : ℝ → ℝ} (hconv : ConvexOn ℝ Set.univ f)
    (hdiff : DifferentiableAt ℝ f x) : f y ≥ f x + deriv f x * (y - x) := by
  -- Step 1: Handle the trivial case where x = y
  by_cases hxy : x = y
  · -- Step 1.1: If x = y, both sides are equal to f(x), so the inequality holds trivially
    simp [hxy]
  · -- Step 2: Split into cases based on whether x < y or x > y
    by_cases hlt : x < y
    · -- Step 2.1: Case x < y
      -- Step 2.1.1: Use the convexity slope inequality: deriv f x ≤ slope f x y
      have h := hconv.deriv_le_slope (Set.mem_univ x) (Set.mem_univ y) hlt hdiff
      -- Step 2.1.2: Expand slope f x y = (y - x)⁻¹ * (f y - f x)
      simp only [slope, vsub_eq_sub, smul_eq_mul] at h
      -- Step 2.1.3: Since y - x > 0, we can multiply both sides
      have hpos : y - x > 0 := sub_pos.mpr hlt
      have h2 : deriv f x * (y - x) ≤ (y - x)⁻¹ * (f y - f x) * (y - x) := by
        exact mul_le_mul_of_nonneg_right h (le_of_lt hpos)
      -- Step 2.1.4: Simplify the right side: (y - x)⁻¹ * (f y - f x) * (y - x) = f y - f x
      have h3 : (y - x)⁻¹ * (f y - f x) * (y - x) = f y - f x := by field_simp
      -- Step 2.1.5: Conclude by linear arithmetic
      linarith
    · -- Step 2.2: Case y < x (since x ≠ y and ¬(x < y))
      push_neg at hlt
      have hgt : y < x := lt_of_le_of_ne hlt (Ne.symm hxy)
      -- Step 2.2.1: Use the slope inequality: slope f y x ≤ deriv f x
      have h := hconv.slope_le_deriv (Set.mem_univ y) (Set.mem_univ x) hgt hdiff
      -- Step 2.2.2: Expand slope f y x = (x - y)⁻¹ * (f x - f y)
      simp only [slope, vsub_eq_sub, smul_eq_mul] at h
      -- Step 2.2.3: Since x - y > 0, multiply both sides by (x - y)
      have hpos : x - y > 0 := sub_pos.mpr hgt
      have h2 : (x - y)⁻¹ * (f x - f y) * (x - y) ≤ deriv f x * (x - y) := by
        exact mul_le_mul_of_nonneg_right h (le_of_lt hpos)
      -- Step 2.2.4: Simplify: (x - y)⁻¹ * (f x - f y) * (x - y) = f x - f y
      have h3 : (x - y)⁻¹ * (f x - f y) * (x - y) = f x - f y := by field_simp
      have h4 : f x - f y ≤ deriv f x * (x - y) := by linarith
      -- Step 2.2.5: Convert (x - y) to -(y - x) and conclude
      have h5 : deriv f x * (y - x) = -(deriv f x * (x - y)) := by ring
      linarith

/--
Tangent Line Upper Bound for Concave Functions:
For a concave function f on Set.univ, at any point x where f is differentiable,
the function value f(y) at any other point y lies below the tangent line at x.
-/
lemma concaveOn_tangent_line_upper_bound {x y : ℝ} {f : ℝ → ℝ} (hconc : ConcaveOn ℝ Set.univ f)
    (hdiff : DifferentiableAt ℝ f x) : f y ≤ f x + deriv f x * (y - x) := by
  -- Step 1: Use the fact that f is concave iff -f is convex
  have hconv : ConvexOn ℝ Set.univ (-f) := hconc.neg
  -- Step 2: -f is differentiable at x since f is
  have hdiff_neg : DifferentiableAt ℝ (-f) x := hdiff.neg
  -- Step 3: Apply the convex tangent inequality to -f
  have h := @convexOn_tangent_line_lower_bound x y (-f) hconv hdiff_neg
  -- Step 4: Simplify: -f(y) ≥ -f(x) + (-f'(x))(y - x) becomes f(y) ≤ f(x) + f'(x)(y - x)
  simp only [Pi.neg_apply, deriv.neg] at h
  linarith


/-
================================================================================
MAIN THEOREM: Putnam 1998 A3
================================================================================

**Problem Statement:**
Let f be a real function on the real line with continuous third derivative.
Prove that there exists a point a such that f(a) * f'(a) * f''(a) * f'''(a) >= 0.

**Proof Strategy:**
We use a case analysis approach. The product of four real numbers is >= 0 if:
1. At least one factor is zero, OR
2. An even number of factors are negative (0, 2, or 4 negative factors)

The proof proceeds as follows:
- Case 1-4: If any of f, f', f'', f''' has a zero, we're done (product = 0)
- Case 5: If none have zeros, each maintains constant sign by IVT
  - We show f and f'' must have the same sign (both + or both -)
  - We show f' and f''' must have the same sign (both + or both -)
  - This gives 0 or 4 negative factors, making the product >= 0
-/

theorem Putnam_exercise_1998_a3 (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) :
  ∃ a : ℝ, (f a) * (deriv f a) * (iteratedDeriv 2 f a) * (iteratedDeriv 3 f a) ≥ 0 := by

  /-
  ============================================================================
  STEP 1: ESTABLISH CONTINUITY AND DIFFERENTIABILITY OF ALL DERIVATIVES
  ============================================================================
  Since f is C³, we have:
  - f, f', f'', f''' are all continuous
  - f, f', f'' are all differentiable
  -/

  -- Step 1.1: f is continuous (immediate from C³)
  have hf_cont : Continuous f := hf.continuous

  -- Step 1.2: f' = deriv f is continuous (f is C³ implies deriv f is C², hence continuous)
  have hf'_cont : Continuous (deriv f) := by
    exact hf.continuous_deriv (by native_decide : (1 : WithTop ℕ∞) ≤ 3)

  -- Step 1.3: f'' = iteratedDeriv 2 f is continuous
  -- We use iteratedDeriv_succ to rewrite f'' = deriv(deriv f)
  -- Since deriv f is C², its derivative is continuous
  have hf''_cont : Continuous (iteratedDeriv 2 f) := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
    have h_df_C2 : ContDiff ℝ 2 (deriv f) := (contDiff_succ_iff_deriv.mp hf).2.2
    exact h_df_C2.continuous_deriv (by native_decide : (1 : WithTop ℕ∞) ≤ 2)

  -- Step 1.4: f''' = iteratedDeriv 3 f is continuous
  -- We use iteratedDeriv_succ repeatedly: f''' = deriv(deriv(deriv f))
  -- Since deriv(deriv f) is C¹, its derivative is continuous
  have hf'''_cont : Continuous (iteratedDeriv 3 f) := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
    have h_df_C2 : ContDiff ℝ 2 (deriv f) := (contDiff_succ_iff_deriv.mp hf).2.2
    have h_ddf_C1 : ContDiff ℝ 1 (deriv (deriv f)) := (contDiff_succ_iff_deriv.mp h_df_C2).2.2
    exact h_ddf_C1.continuous_deriv (by native_decide : (1 : WithTop ℕ∞) ≤ 1)

  -- Step 1.5: f is differentiable (needed for tangent line inequalities)
  have hf_diff : Differentiable ℝ f := hf.differentiable (by native_decide : (3 : WithTop ℕ∞) ≠ 0)

  -- Step 1.6: f' = deriv f is differentiable (f is C³ implies deriv f is C², hence differentiable)
  have h_df_C2 : ContDiff ℝ 2 (deriv f) := (contDiff_succ_iff_deriv.mp hf).2.2
  have hf'_diff : Differentiable ℝ (deriv f) := h_df_C2.differentiable (by native_decide : (2 : WithTop ℕ∞) ≠ 0)

  /-
  ============================================================================
  STEP 2: HANDLE CASES WHERE ONE OF THE FACTORS IS ZERO
  ============================================================================
  If any of f, f', f'', f''' has a zero somewhere, we're done because
  the product at that point will be 0 >= 0.
  -/

  -- Step 2.1: Check if f has a zero anywhere
  by_cases h_f_zero : ∃ a, f a = 0
  · -- Step 2.1.1: f has a zero at some point a
    obtain ⟨a, ha⟩ := h_f_zero
    use a
    -- Step 2.1.2: The product is 0 * ... = 0 >= 0
    simp [ha]

  · -- Step 2.2: Check if f' has a zero anywhere
    by_cases h_f'_zero : ∃ a, deriv f a = 0
    · -- Step 2.2.1: f' has a zero at some point a
      obtain ⟨a, ha⟩ := h_f'_zero
      use a
      -- Step 2.2.2: The product is ... * 0 * ... = 0 >= 0
      simp [ha]

    · -- Step 2.3: Check if f'' has a zero anywhere
      by_cases h_f''_zero : ∃ a, iteratedDeriv 2 f a = 0
      · -- Step 2.3.1: f'' has a zero at some point a
        obtain ⟨a, ha⟩ := h_f''_zero
        use a
        -- Step 2.3.2: The product is ... * 0 * ... = 0 >= 0
        simp [ha]

      · -- Step 2.4: Check if f''' has a zero anywhere
        by_cases h_f'''_zero : ∃ a, iteratedDeriv 3 f a = 0
        · -- Step 2.4.1: f''' has a zero at some point a
          obtain ⟨a, ha⟩ := h_f'''_zero
          use a
          -- Step 2.4.2: The product is ... * 0 = 0 >= 0
          simp [ha]

        /-
        ======================================================================
        STEP 3: MAIN CASE - NONE OF f, f', f'', f''' HAVE ANY ZEROS
        ======================================================================
        In this case, we need to show that f, f'' have the same sign and
        f', f''' have the same sign, which ensures the product is positive.
        -/
        · -- Step 3.1: Convert existential negations to universal statements
          push_neg at h_f_zero h_f'_zero h_f''_zero h_f'''_zero

          -- Step 3.2: Name the universal statements for clarity
          have f_ne_zero : ∀ x, f x ≠ 0 := h_f_zero
          have f'_ne_zero : ∀ x, deriv f x ≠ 0 := h_f'_zero
          have f''_ne_zero : ∀ x, iteratedDeriv 2 f x ≠ 0 := h_f''_zero
          have f'''_ne_zero : ∀ x, iteratedDeriv 3 f x ≠ 0 := h_f'''_zero

          /-
          ------------------------------------------------------------------
          STEP 3.3: IVT LEMMA FOR CONSTANT SIGN
          ------------------------------------------------------------------
          Key insight: A continuous function that never equals zero must have
          constant sign (always positive or always negative) by the Intermediate
          Value Theorem.
          -/
          have ivt_const_sign : ∀ (g : ℝ → ℝ), Continuous g → (∀ x, g x ≠ 0) →
              (∀ x, g x > 0) ∨ (∀ x, g x < 0) := by
            intro g hg_cont hg_ne
            -- Step 3.3.1: Check the sign at x = 0 to determine which case we're in
            by_cases hg0 : g 0 > 0
            · -- Step 3.3.2: g(0) > 0 case - show g is always positive
              left
              intro x
              by_contra hx
              push_neg at hx
              -- Step 3.3.2.1: g(x) ≤ 0 and g(x) ≠ 0 implies g(x) < 0
              have hx_lt : g x < 0 := lt_of_le_of_ne hx (hg_ne x)
              -- Step 3.3.2.2: Use IVT to find a zero between x and 0
              rcases le_or_gt x 0 with hx_le | hx_gt
              · -- Step 3.3.2.2.1: x ≤ 0 case
                have hcont : ContinuousOn g (Set.Icc x 0) := hg_cont.continuousOn
                have h_in : (0 : ℝ) ∈ Set.Icc (g x) (g 0) := ⟨le_of_lt hx_lt, le_of_lt hg0⟩
                have hsub := intermediate_value_Icc hx_le hcont
                obtain ⟨c, _, hc_eq⟩ := hsub h_in
                -- Step 3.3.2.2.1.1: Found c with g(c) = 0, contradiction
                exact hg_ne c hc_eq
              · -- Step 3.3.2.2.2: 0 < x case
                have hcont : ContinuousOn g (Set.Icc 0 x) := hg_cont.continuousOn
                have h_in : (0 : ℝ) ∈ Set.Icc (g x) (g 0) := ⟨le_of_lt hx_lt, le_of_lt hg0⟩
                have hsub := intermediate_value_Icc' (le_of_lt hx_gt) hcont
                obtain ⟨c, _, hc_eq⟩ := hsub h_in
                -- Step 3.3.2.2.2.1: Found c with g(c) = 0, contradiction
                exact hg_ne c hc_eq
            · -- Step 3.3.3: g(0) ≤ 0 case - show g is always negative
              push_neg at hg0
              have hg0_neg : g 0 < 0 := lt_of_le_of_ne hg0 (hg_ne 0)
              right
              intro x
              by_contra hx
              push_neg at hx
              -- Step 3.3.3.1: ¬(g x < 0) and g(x) ≠ 0 implies g(x) > 0
              have hx_pos : g x > 0 := lt_of_le_of_ne' hx (hg_ne x)
              -- Step 3.3.3.2: Use IVT to find a zero between x and 0
              rcases le_or_gt x 0 with hx_le | hx_gt
              · -- Step 3.3.3.2.1: x ≤ 0 case
                have hcont : ContinuousOn g (Set.Icc x 0) := hg_cont.continuousOn
                have h_in : (0 : ℝ) ∈ Set.Icc (g 0) (g x) := ⟨le_of_lt hg0_neg, le_of_lt hx_pos⟩
                have hsub := intermediate_value_Icc' hx_le hcont
                obtain ⟨c, _, hc_eq⟩ := hsub h_in
                exact hg_ne c hc_eq
              · -- Step 3.3.3.2.2: 0 < x case
                have hcont : ContinuousOn g (Set.Icc 0 x) := hg_cont.continuousOn
                have h_in : (0 : ℝ) ∈ Set.Icc (g 0) (g x) := ⟨le_of_lt hg0_neg, le_of_lt hx_pos⟩
                have hsub := intermediate_value_Icc (le_of_lt hx_gt) hcont
                obtain ⟨c, _, hc_eq⟩ := hsub h_in
                exact hg_ne c hc_eq

          /-
          ------------------------------------------------------------------
          STEP 3.4: APPLY IVT LEMMA TO DETERMINE SIGN PATTERNS
          ------------------------------------------------------------------
          -/
          -- Step 3.4.1: Each of f'', f''', f, f' has constant sign
          have f''_const_sign := ivt_const_sign (iteratedDeriv 2 f) hf''_cont f''_ne_zero
          have f'''_const_sign := ivt_const_sign (iteratedDeriv 3 f) hf'''_cont f'''_ne_zero
          have f_const_sign := ivt_const_sign f hf_cont f_ne_zero
          have f'_const_sign := ivt_const_sign (deriv f) hf'_cont f'_ne_zero

          /-
          ------------------------------------------------------------------
          STEP 3.5: PROVE f AND f'' HAVE THE SAME SIGN
          ------------------------------------------------------------------
          Key insight: If f > 0 everywhere and f'' < 0 everywhere (concave),
          then by the tangent line inequality, f must go to -∞ as x → ±∞,
          contradicting f > 0. Similar argument for other mismatched cases.
          -/
          have f_f''_same_sign : (∀ x, f x > 0 ∧ iteratedDeriv 2 f x > 0) ∨
                                  (∀ x, f x < 0 ∧ iteratedDeriv 2 f x < 0) := by
            cases f_const_sign with
            | inl hf_pos =>
              -- Step 3.5.1: f > 0 everywhere
              cases f''_const_sign with
              | inl hf''_pos =>
                -- Step 3.5.1.1: f'' > 0 everywhere - same sign (both positive)
                left; intro x; exact ⟨hf_pos x, hf''_pos x⟩
              | inr hf''_neg =>
                -- Step 3.5.1.2: f > 0 and f'' < 0 everywhere - contradiction
                exfalso
                -- Step 3.5.1.2.1: f'' < 0 everywhere means f is strictly concave
                have hconc : ConcaveOn ℝ Set.univ f := by
                  apply concaveOn_of_deriv2_nonpos convex_univ
                  · exact hf_cont.continuousOn
                  · exact hf_diff.differentiableOn
                  · exact hf'_diff.differentiableOn
                  · intro x _
                    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply]
                    have h := hf''_neg x
                    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero] at h
                    exact le_of_lt h

                -- Step 3.5.1.2.2: For concave f: f(y) ≤ f(x) + f'(x)(y - x)
                have h_tangent : ∀ a x, f x ≤ f a + deriv f a * (x - a) := fun a x =>
                  concaveOn_tangent_line_upper_bound hconc (hf_diff a)

                -- Step 3.5.1.2.3: Find a point where f must be negative
                cases f'_const_sign with
                | inl hf'_pos =>
                  -- f' > 0: tangent at 0 has positive slope
                  -- For x << 0: f(x) ≤ f(0) + f'(0)*x → -∞
                  have hf'0 : deriv f 0 > 0 := hf'_pos 0
                  have hf0 : f 0 > 0 := hf_pos 0
                  have hne : deriv f 0 ≠ 0 := ne_of_gt hf'0
                  set x0 := -(f 0 / deriv f 0) - 1
                  have h1 : f 0 + deriv f 0 * x0 < 0 := by simp only [x0]; field_simp; linarith
                  linarith [h_tangent 0 x0, hf_pos x0]
                | inr hf'_neg =>
                  -- f' < 0: tangent at 0 has negative slope
                  -- For x >> 0: f(x) ≤ f(0) + f'(0)*x → -∞
                  have hf'0 : deriv f 0 < 0 := hf'_neg 0
                  have hf0 : f 0 > 0 := hf_pos 0
                  have hne : deriv f 0 ≠ 0 := ne_of_lt hf'0
                  have hpos : -deriv f 0 > 0 := by linarith
                  set x0 := f 0 / (-deriv f 0) + 1
                  have h1 : f 0 + deriv f 0 * x0 < 0 := by
                    simp only [x0]
                    have h2 : deriv f 0 * (f 0 / (-deriv f 0) + 1) = -f 0 + deriv f 0 := by field_simp
                    linarith
                  linarith [h_tangent 0 x0, hf_pos x0]

            | inr hf_neg =>
              -- Step 3.5.2: f < 0 everywhere
              cases f''_const_sign with
              | inl hf''_pos =>
                -- Step 3.5.2.1: f < 0 and f'' > 0 everywhere - contradiction
                exfalso
                -- Step 3.5.2.1.1: f'' > 0 everywhere means f is strictly convex
                have hconv : ConvexOn ℝ Set.univ f := by
                  apply convexOn_of_deriv2_nonneg convex_univ
                  · exact hf_cont.continuousOn
                  · exact hf_diff.differentiableOn
                  · exact hf'_diff.differentiableOn
                  · intro x _
                    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply]
                    have h := hf''_pos x
                    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero] at h
                    exact le_of_lt h

                -- Step 3.5.2.1.2: For convex f: f(y) ≥ f(x) + f'(x)(y - x)
                have h_tangent : ∀ a x, f x ≥ f a + deriv f a * (x - a) := fun a x =>
                  convexOn_tangent_line_lower_bound hconv (hf_diff a)

                -- Step 3.5.2.1.3: Find a point where f must be positive
                cases f'_const_sign with
                | inl hf'_pos =>
                  -- f' > 0: tangent at 0 has positive slope
                  -- For x >> 0: f(x) ≥ f(0) + f'(0)*x → +∞
                  have hf'0 : deriv f 0 > 0 := hf'_pos 0
                  have hf0 : f 0 < 0 := hf_neg 0
                  have hne : deriv f 0 ≠ 0 := ne_of_gt hf'0
                  set x0 := (1 - f 0) / deriv f 0
                  have h1 : f 0 + deriv f 0 * x0 = 1 := by simp only [x0]; field_simp; ring
                  linarith [h_tangent 0 x0, hf_neg x0]
                | inr hf'_neg =>
                  -- f' < 0: tangent at 0 has negative slope
                  -- For x << 0: f(x) ≥ f(0) + f'(0)*x → +∞
                  have hf'0 : deriv f 0 < 0 := hf'_neg 0
                  have hf0 : f 0 < 0 := hf_neg 0
                  have hne : deriv f 0 ≠ 0 := ne_of_lt hf'0
                  set x0 := (1 - f 0) / deriv f 0
                  have h1 : f 0 + deriv f 0 * x0 = 1 := by simp only [x0]; field_simp; ring
                  linarith [h_tangent 0 x0, hf_neg x0]

              | inr hf''_neg =>
                -- Step 3.5.2.2: f'' < 0 everywhere - same sign (both negative)
                right; intro x; exact ⟨hf_neg x, hf''_neg x⟩

          /-
          ------------------------------------------------------------------
          STEP 3.6: PROVE f' AND f''' HAVE THE SAME SIGN
          ------------------------------------------------------------------
          Key insight: f''' is the second derivative of f', so the same
          convexity/concavity argument applies to f'.
          -/
          -- Step 3.6.1: Set up differentiability for deriv(deriv f)
          have h_ddf_C1 : ContDiff ℝ 1 (deriv (deriv f)) := (contDiff_succ_iff_deriv.mp h_df_C2).2.2
          have hf''_diff : Differentiable ℝ (deriv (deriv f)) := h_ddf_C1.differentiable (by native_decide : (1 : WithTop ℕ∞) ≠ 0)

          have f'_f'''_same_sign : (∀ x, deriv f x > 0 ∧ iteratedDeriv 3 f x > 0) ∨
                                   (∀ x, deriv f x < 0 ∧ iteratedDeriv 3 f x < 0) := by
            -- Step 3.6.2: Note that f''' = (f')'' (second derivative of f')
            have h_f'''_eq : iteratedDeriv 3 f = iteratedDeriv 2 (deriv f) := by
              ext x
              rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
              rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]

            cases f'_const_sign with
            | inl hf'_pos =>
              -- Step 3.6.3: f' > 0 everywhere
              cases f'''_const_sign with
              | inl hf'''_pos =>
                -- Step 3.6.3.1: f''' > 0 everywhere - same sign (both positive)
                left; intro x; exact ⟨hf'_pos x, hf'''_pos x⟩
              | inr hf'''_neg =>
                -- Step 3.6.3.2: f' > 0 and f''' < 0 everywhere - contradiction
                exfalso
                -- Step 3.6.3.2.1: f''' < 0 means f' is strictly concave
                have hf'_conc : ConcaveOn ℝ Set.univ (deriv f) := by
                  apply concaveOn_of_deriv2_nonpos convex_univ
                  · exact hf'_cont.continuousOn
                  · exact hf'_diff.differentiableOn
                  · exact hf''_diff.differentiableOn
                  · intro x _
                    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply]
                    have h := hf'''_neg x
                    rw [h_f'''_eq, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero] at h
                    exact le_of_lt h

                -- Step 3.6.3.2.2: For concave f': f'(y) ≤ f'(x) + f''(x)(y - x)
                have h_tangent' : ∀ a x, deriv f x ≤ deriv f a + iteratedDeriv 2 f a * (x - a) := by
                  intro a x
                  have hderiv_eq : deriv (deriv f) a = iteratedDeriv 2 f a := by
                    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
                  rw [← hderiv_eq]
                  exact concaveOn_tangent_line_upper_bound hf'_conc (hf'_diff a)

                have hf'0 : deriv f 0 > 0 := hf'_pos 0

                -- Step 3.6.3.2.3: Find a point where f' must be negative
                cases f''_const_sign with
                | inl hf''_pos =>
                  -- f'' > 0: tangent to f' at 0 has positive slope in f'' direction
                  have hf''0 : iteratedDeriv 2 f 0 > 0 := hf''_pos 0
                  have hne : iteratedDeriv 2 f 0 ≠ 0 := ne_of_gt hf''0
                  set x0 := -(deriv f 0 + 1) / iteratedDeriv 2 f 0
                  have h_bound : deriv f 0 + iteratedDeriv 2 f 0 * x0 = -1 := by
                    simp only [x0]; field_simp; ring
                  linarith [h_tangent' 0 x0, hf'_pos x0]
                | inr hf''_neg =>
                  -- f'' < 0: tangent to f' at 0 has negative slope in f'' direction
                  have hf''0 : iteratedDeriv 2 f 0 < 0 := hf''_neg 0
                  have hne : iteratedDeriv 2 f 0 ≠ 0 := ne_of_lt hf''0
                  have hpos : -iteratedDeriv 2 f 0 > 0 := by linarith
                  set x0 := (deriv f 0 + 1) / (-iteratedDeriv 2 f 0)
                  have h_bound : deriv f 0 + iteratedDeriv 2 f 0 * x0 = -1 := by
                    simp only [x0]
                    have h1 : iteratedDeriv 2 f 0 * ((deriv f 0 + 1) / (-iteratedDeriv 2 f 0)) =
                              -(deriv f 0 + 1) := by field_simp
                    linarith
                  linarith [h_tangent' 0 x0, hf'_pos x0]

            | inr hf'_neg =>
              -- Step 3.6.4: f' < 0 everywhere
              cases f'''_const_sign with
              | inl hf'''_pos =>
                -- Step 3.6.4.1: f' < 0 and f''' > 0 everywhere - contradiction
                exfalso
                -- Step 3.6.4.1.1: f''' > 0 means f' is strictly convex
                have hf'_conv : ConvexOn ℝ Set.univ (deriv f) := by
                  apply convexOn_of_deriv2_nonneg convex_univ
                  · exact hf'_cont.continuousOn
                  · exact hf'_diff.differentiableOn
                  · exact hf''_diff.differentiableOn
                  · intro x _
                    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply]
                    have h := hf'''_pos x
                    rw [h_f'''_eq, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero] at h
                    exact le_of_lt h

                -- Step 3.6.4.1.2: For convex f': f'(y) ≥ f'(x) + f''(x)(y - x)
                have h_tangent' : ∀ a x, deriv f x ≥ deriv f a + iteratedDeriv 2 f a * (x - a) := by
                  intro a x
                  have hderiv_eq : deriv (deriv f) a = iteratedDeriv 2 f a := by
                    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
                  rw [← hderiv_eq]
                  exact convexOn_tangent_line_lower_bound hf'_conv (hf'_diff a)

                have hf'0 : deriv f 0 < 0 := hf'_neg 0

                -- Step 3.6.4.1.3: Find a point where f' must be positive
                cases f''_const_sign with
                | inl hf''_pos =>
                  have hf''0 : iteratedDeriv 2 f 0 > 0 := hf''_pos 0
                  have hne : iteratedDeriv 2 f 0 ≠ 0 := ne_of_gt hf''0
                  set x0 := (-deriv f 0 + 1) / iteratedDeriv 2 f 0
                  have h_bound : deriv f 0 + iteratedDeriv 2 f 0 * x0 = 1 := by
                    simp only [x0]; field_simp; ring
                  linarith [h_tangent' 0 x0, hf'_neg x0]
                | inr hf''_neg =>
                  have hf''0 : iteratedDeriv 2 f 0 < 0 := hf''_neg 0
                  have hne : iteratedDeriv 2 f 0 ≠ 0 := ne_of_lt hf''0
                  set x0 := (-deriv f 0 + 1) / iteratedDeriv 2 f 0
                  have h_bound : deriv f 0 + iteratedDeriv 2 f 0 * x0 = 1 := by
                    simp only [x0]; field_simp; ring
                  linarith [h_tangent' 0 x0, hf'_neg x0]

              | inr hf'''_neg =>
                -- Step 3.6.4.2: f''' < 0 everywhere - same sign (both negative)
                right; intro x; exact ⟨hf'_neg x, hf'''_neg x⟩

          /-
          ------------------------------------------------------------------
          STEP 3.7: CONCLUDE THE PROOF
          ------------------------------------------------------------------
          We have shown:
          - f and f'' have the same sign (both + or both -)
          - f' and f''' have the same sign (both + or both -)

          Therefore:
          - f * f'' > 0 (product of two numbers with same sign)
          - f' * f''' > 0 (product of two numbers with same sign)
          - The full product f * f' * f'' * f''' > 0
          -/
          use 0
          cases f_f''_same_sign with
          | inl h_both_pos =>
            -- Step 3.7.1: f > 0 and f'' > 0
            cases f'_f'''_same_sign with
            | inl h'_both_pos =>
              -- Step 3.7.1.1: f' > 0 and f''' > 0 - all four positive
              have hp1 : f 0 * iteratedDeriv 2 f 0 > 0 := mul_pos (h_both_pos 0).1 (h_both_pos 0).2
              have hp2 : deriv f 0 * iteratedDeriv 3 f 0 > 0 := mul_pos (h'_both_pos 0).1 (h'_both_pos 0).2
              have hp3 : f 0 * deriv f 0 > 0 := mul_pos (h_both_pos 0).1 (h'_both_pos 0).1
              nlinarith
            | inr h'_both_neg =>
              -- Step 3.7.1.2: f' < 0 and f''' < 0 - two positive, two negative
              have hp1 : f 0 * iteratedDeriv 2 f 0 > 0 := mul_pos (h_both_pos 0).1 (h_both_pos 0).2
              have hp2 : deriv f 0 * iteratedDeriv 3 f 0 > 0 := mul_pos_of_neg_of_neg (h'_both_neg 0).1 (h'_both_neg 0).2
              have hp3 : f 0 * deriv f 0 < 0 := mul_neg_of_pos_of_neg (h_both_pos 0).1 (h'_both_neg 0).1
              have hp4 : iteratedDeriv 2 f 0 * iteratedDeriv 3 f 0 < 0 := mul_neg_of_pos_of_neg (h_both_pos 0).2 (h'_both_neg 0).2
              nlinarith
          | inr h_both_neg =>
            -- Step 3.7.2: f < 0 and f'' < 0
            cases f'_f'''_same_sign with
            | inl h'_both_pos =>
              -- Step 3.7.2.1: f' > 0 and f''' > 0 - two positive, two negative
              have hp1 : f 0 * iteratedDeriv 2 f 0 > 0 := mul_pos_of_neg_of_neg (h_both_neg 0).1 (h_both_neg 0).2
              have hp2 : deriv f 0 * iteratedDeriv 3 f 0 > 0 := mul_pos (h'_both_pos 0).1 (h'_both_pos 0).2
              have hp3 : f 0 * deriv f 0 < 0 := mul_neg_of_neg_of_pos (h_both_neg 0).1 (h'_both_pos 0).1
              have hp4 : iteratedDeriv 2 f 0 * iteratedDeriv 3 f 0 < 0 := mul_neg_of_neg_of_pos (h_both_neg 0).2 (h'_both_pos 0).2
              nlinarith
            | inr h'_both_neg =>
              -- Step 3.7.2.2: f' < 0 and f''' < 0 - all four negative
              have hp1 : f 0 * iteratedDeriv 2 f 0 > 0 := mul_pos_of_neg_of_neg (h_both_neg 0).1 (h_both_neg 0).2
              have hp2 : deriv f 0 * iteratedDeriv 3 f 0 > 0 := mul_pos_of_neg_of_neg (h'_both_neg 0).1 (h'_both_neg 0).2
              have hp3 : f 0 * deriv f 0 > 0 := mul_pos_of_neg_of_neg (h_both_neg 0).1 (h'_both_neg 0).1
              nlinarith
